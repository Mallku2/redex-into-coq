Require Import 
        Lists.List
        Logic.Eqdep
        (* inj_pair2_eq_dec *)
        Logic.Eqdep_dec
        Program.Equality
        (* to deal with trans. closure of m_rel_noinp_cons *)
        Relations.Relation_Operators
        (* Some_inj *)
        ssr.ssrfun.

Require Export
        match_impl_lemmas
        wf_rel
        lib_ext.ListExt
        lib_ext.tactics.

(* lemmas about matching spec. *)
Module MatchSpecLemmas (pt : PatTermsSymb).
  Import pt.

  Module MatchImplLemmas := MatchImplLemmas pt.
  Import MatchImplLemmas.
  Import MatchingSpec.
  Import Matching.
  Import MatchTads.
  Import WfRel.
  Import GrammarLists.

  (* prepare the hints database *)
  #[local] Hint Constructors match_spec            : core.
  #[local] Hint Constructors decompose_spec        : core.
  #[local] Hint Constructors pat_grammar_evolution : core.
  #[local] Hint Constructors clos_trans_1n         : core.

  (* soundness of our manipulation of non-left-recursive grammars, during
     matching: it is sound to remove a production from the grammar, 
     during no input consumption *)
  Lemma non_left_g_rm_sound :
    forall (g1 g2 : GrammarLists.grammar) (t : term) (n : nonterm)
      (p : pat) (proof_in : GrammarLists.prod_in_g (n, p) g2) (b : bindings),
      non_left_recursive_grammar ->
      (g1 ⊢ t : p, GrammarLists.remove_prod (n, p) g2 proof_in | b
       <->
       g1 ⊢ t : p, g2 | b)
      /\
      (forall (C : contxt) (subt : term),
          g1 ⊢ t ⩦ C[subt] : p, GrammarLists.remove_prod (n, p) g2 proof_in | b
          <->
          g1 ⊢ t ⩦ C[subt] : p, g2 | b
      ).
  Proof.
    intros g1 g2 t n p Hproof_in b Hnon_lr.
    
    enough (IP: 
             forall  (ncons_tup : pat * GrammarLists.grammar),
               let (p', g2') := ncons_tup in
               forall (proof_mrel : pat_grammar_evolution_trans (p', g2') (p, g2))
                 (Hproof_in' : GrammarLists.prod_in_g (n, p) g2') (b : bindings),
                 (g1 ⊢ t : p', GrammarLists.remove_prod (n, p) g2' Hproof_in' | b
                  <->
                  g1 ⊢ t : p', g2' | b)
                 /\
                 (forall (C : contxt) (subt : term),
                     g1 ⊢ t ⩦ C [subt] : p',
                    GrammarLists.remove_prod (n, p) g2' Hproof_in' | b
                    <->
                    g1 ⊢ t ⩦ C [subt] : p', g2' | b)).
    - (* original goal *)
      split.
      + (* match *)
        destruct p as [lit |  | l | v p |n0 | p1 p2].
        * (* p = lit *)
          split;
            intro Hmatch;
            inversion Hmatch;
               eauto.
        * (* p = hole *)
          split;
            intro Hmatch;
            inversion Hmatch;
               eauto.
        * (* p = cons, contxt *)
          destruct l;
            split;
            intro Hmatch;
            inversion Hmatch;
               eauto.
        * (* p = name *)
          split.
          -- (* we can add a removed prod *)
             intro Hmatch.
             inversion Hmatch as [| |t' v' p'' bp b0'
                                        g_rem Hmatch_p
                                        Hb_union Heq_t Heq_v
                                        Heq_g_rem Heq_b0 |  | | | | | | ].
             
             assert(((g1 ⊢ t : p, GrammarLists.remove_prod (n, name v p) g2
                                               Hproof_in | bp)
                     <->
                     g1 ⊢ t : p, g2 | bp)
                    /\
                    (forall (C : contxt) (subt : term),
                        (g1 ⊢ t ⩦ C [subt]: p,
                                            GrammarLists.remove_prod (n, name v p) g2
                                                        Hproof_in | bp)
                        <->
                        g1 ⊢ t ⩦ C [subt]: p, g2 | bp))
               as Hinst_IH.
             {assert(pat_grammar_evolution_trans (p, g2) (name v p, g2))
                 as Hmrel.
              {apply t1n_step.
               auto.
              }
              apply (IP (p, g2) Hmrel Hproof_in bp).
             }
             
             intuition eauto.
          -- (* we can remove a used prod *)
             intro Hmatch.
             inversion Hmatch as [| |t' v' p'' bp b0'
                                        g_rem Hmatch_p
                                        Hb_union Heq_t Heq_v
                                        Heq_g_rem Heq_b0 |  | | | | | | ].

             assert(((g1 ⊢ t : p, GrammarLists.remove_prod (n, name v p) g2
                                               Hproof_in | bp)
                     <->
                     g1 ⊢ t : p, g2 | bp)
                    /\
                    (forall (C : contxt) (subt : term),
                        (g1 ⊢ t ⩦ C [subt]: p,
                                            GrammarLists.remove_prod (n, name v p) g2
                                                        Hproof_in | bp)
                        <->
                        g1 ⊢ t ⩦ C [subt]: p, g2 | bp))
               as Hinst_IH.
             {assert(pat_grammar_evolution_trans (p, g2) (name v p, g2))
                 as Hmrel.
              {apply t1n_step.
               auto.
              }
              apply (IP (p, g2) Hmrel Hproof_in bp).
             }
             
             intuition eauto.
        * (* p = nt *)
          split.
          -- (* we can add a removed prod *)
             intro Hmatch.
             inversion Hmatch as  [| | | n' p' t' b' g_rem Hprod_in_p'
                                            Hmatch_p' Heq_t' Heq_n'
                                            Heq_g_rem Heq_bind | | | | | |].

             assert(exists (proof_in_pr2' : GrammarLists.prod_in_g (n0, p') g2)
                      (proof_in_pr1' : GrammarLists.prod_in_g (n, nt n0)
                                                 (GrammarLists.remove_prod (n0, p') g2
                                                              proof_in_pr2')),
                       GrammarLists.remove_prod (n0, p') (GrammarLists.remove_prod (n, nt n0) g2
                                                         Hproof_in)
                                   Hprod_in_p'
                       = GrammarLists.remove_prod (n, nt n0) (GrammarLists.remove_prod (n0, p') g2
                                                             proof_in_pr2')
                                     proof_in_pr1')
               as Hremove_comm.
             {apply GrammarLists.remove_prod_comm.
             }
             inversion Hremove_comm as [Hproof_p'_g2
                                          (Hproof_p_g_rem, Hremove_comm')].
             clear Hremove_comm.

             rewrite Hremove_comm' in Hmatch_p'.
             clear Hremove_comm'.

             assert(((g1 ⊢ t : p', GrammarLists.remove_prod (n, nt n0)
                                     (GrammarLists.remove_prod (n0, p') g2 Hproof_p'_g2)
                                     Hproof_p_g_rem
                                   | b')
                     <->
                     g1 ⊢ t : p', GrammarLists.remove_prod (n0, p') g2
                                              Hproof_p'_g2 | b') /\
                    (forall (C : contxt) (subt : term),
                        (g1 ⊢ t ⩦ C [subt]: p',
                                            GrammarLists.remove_prod (n, nt n0)
                                                        (GrammarLists.remove_prod
                                                           (n0, p') g2
                                                           Hproof_p'_g2)
                                                        Hproof_p_g_rem | b')
                        <->
                        (g1 ⊢ t ⩦ C [subt]: p',
                                            GrammarLists.remove_prod (n0, p') g2
                                                        Hproof_p'_g2 | b')))
               as (Hinst_IH_match, Hinst_IH_decom).
             {assert(pat_grammar_evolution_trans 
                       (p', GrammarLists.remove_prod (n0, p') g2 Hproof_p'_g2)
                       (nt n0, g2))
                 as Hmrel.
              {apply t1n_step.
               auto.
              }
              apply (IP (p', GrammarLists.remove_prod (n0, p') g2 Hproof_p'_g2)
                        Hmrel Hproof_p_g_rem).
             }
             clear Hinst_IH_decom.
             rewrite Hinst_IH_match in Hmatch_p'.
             eauto.
             
          -- (* we can remove a used prod *)
             intro Hmatch.
             (* we can instantiate the IH since (n, nt n0) can be removed
                from g2 given that g <> g2 (non-left-recursive grammar
                hypothesis) *)
             inversion Hmatch as  [| | | n' p' t' b' g_rem Hprod_in_p'
                                            Hmatch_p' Heq_t' Heq_n'
                                            Heq_g_rem Heq_bind | | | | | |].

             assert(GrammarLists.prod_in_g (n, nt n0)
                              (GrammarLists.remove_prod (n0, p') g2 Hprod_in_p'))
               as Hrem.
             {(* we are assuming non-left recursive grammars *)
               assert((n, nt n0) <> (n0, p'))
                 as Hneq_pair.
               {assert(n <> n0)
                   as Hneq_n.
                {intro Heq_n.
                 rewrite <- Heq_n in Hproof_in.
                 assert(not (pat_grammar_evolution_trans 
                               (nt n, GrammarLists.remove_prod (n, nt n) g2 Hproof_in)
                               (nt n, g2)))
                   as Hnon_left_g2.
                 {auto.
                 }
                 assert(pat_grammar_evolution_trans 
                          (nt n, GrammarLists.remove_prod (n, nt n) g2 Hproof_in)
                          (nt n, g2))
                   as Hleft_g2.
                 {apply t1n_step.
                  eauto.
                 }
                 contradiction.
                }
                intros Heq_pair.
                inversion Heq_pair as [Heq_n].
                contradiction.
               }
               generalize remove_prod_in_g_neq; intro lemma.
               eauto.
             }
             
             assert(((g1 ⊢ t : p', GrammarLists.remove_prod (n, nt n0)
                                               (GrammarLists.remove_prod (n0, p') g2 Hprod_in_p')
                                               Hrem
                     | b')
                     <->
                     g1 ⊢ t : p', GrammarLists.remove_prod (n0, p') g2
                                              Hprod_in_p' | b')
                    /\
                    (forall (C : contxt) (subt : term),
                        (g1 ⊢ t ⩦ C [subt]: p',
                                            GrammarLists.remove_prod (n, nt n0)
                                                        (GrammarLists.remove_prod
                                                           (n0, p') g2
                                                           Hprod_in_p')
                                                        Hrem | b')
                        <->
                        g1 ⊢ t ⩦ C [subt]: p', GrammarLists.remove_prod
                                                 (n0, p') g2
                                                 Hprod_in_p' | b'))
               as [Hinst_IH_match Hinst_IH_decom].
             {assert(pat_grammar_evolution_trans 
                       (p', GrammarLists.remove_prod (n0, p') g2 Hprod_in_p')
                       (nt n0, g2))
                 as Hmrel.
              {apply t1n_step.
               eauto.
              }
              apply (IP (p', GrammarLists.remove_prod (n0, p') g2
                                         Hprod_in_p')
                        Hmrel
                        Hrem
                        b').
             }
             clear Hinst_IH_decom.

             rewrite <- Hinst_IH_match in Hmatch_p'.

             assert(exists (proof_in_pr2 : GrammarLists.prod_in_g (n, nt n0) g2)
                       (proof_in_pr1' : GrammarLists.prod_in_g (n0, p')
                                                 (GrammarLists.remove_prod (n, nt n0) g2
                                                              Hproof_in)),
                       GrammarLists.remove_prod (n, nt n0)
                                   (GrammarLists.remove_prod (n0, p') g2 Hprod_in_p')
                                   Hrem
                       =
                       GrammarLists.remove_prod (n0, p')
                                   (GrammarLists.remove_prod (n, nt n0) g2
                                                proof_in_pr2)
                                   proof_in_pr1')
               as [Hprod_in_n0_g2 (Hprod_in_p_g_rem, Hremove_comm)].
             {apply remove_prod_comm.
             }
             rewrite Hremove_comm in Hmatch_p'.
             clear Hremove_comm Hinst_IH_match.

             assert(GrammarLists.remove_prod (n, nt n0) g2 Hprod_in_n0_g2 =
                    GrammarLists.remove_prod (n, nt n0) g2 Hproof_in)
               as Hremove_eq.
             {apply remove_prod_prod_in_g_irrelevance.
             }
             revert Hmatch_p'.
             rewrite <- Hremove_eq.
             intro Hmatch_p'.

             eauto.
        * (* p = inhole *)
          split.
          -- (* we can add a removed prod *)
             intro Hmatch.
             inversion Hmatch as [ | | | | | | | 
                                   |t1 t2 C p1' p2' b1 b2 b0 g_rem Hdecom
                                       Hsubterm Hmatch_p2 Heq_bunion Heq_t
                                       Heq_p1 Heq_p2 Heq_g_rem |
                                   t' p1' p2' b1 b2 b0 g_rem Hdecom
                                      Hmatch_p2 Heq_bunion Heq_t
                                      Heq_p1 Heq_g_rem ].

             ++ (* sub-pattern pc consumes input *)
                assert(((g1 ⊢ t : p1, GrammarLists.remove_prod (n, inhole p1 p2) g2 Hproof_in
                        | b1)
                        <->
                        g1 ⊢ t : p1, g2 | b1) /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p1,
                                               GrammarLists.remove_prod (n, inhole p1 p2)
                                                           g2 Hproof_in
                           | b1)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p1, g2 | b1))
                 as [Hinst_IH_match Hinst_IH_decom].
                {assert(pat_grammar_evolution_trans (p1, g2) (inhole p1 p2, g2))
                    as Htrans.
                 {apply t1n_step.
                  eauto.
                 }
                 apply (IP (p1, g2) Htrans Hproof_in b1).
                }
                clear Hinst_IH_match.
                rewrite (Hinst_IH_decom C t2) in Hdecom.
                clear Hinst_IH_decom.
                eauto.
             ++ (* sub-pattern pc does not consume input *)
                assert(((g1 ⊢ t : p1, GrammarLists.remove_prod (n, inhole p1 p2) g2 Hproof_in
                        | b1)
                        <->
                        g1 ⊢ t : p1, g2 | b1) /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p1,
                               GrammarLists.remove_prod (n, inhole p1 p2) g2 Hproof_in
                           | b1)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p1, g2 | b1))
                 as [Hinst_IH_match Hinst_IH_decom].
                {assert(pat_grammar_evolution_trans (p1, g2) (inhole p1 p2, g2))
                    as Htrans.
                 {apply t1n_step.
                  auto.
                 }
                 apply (IP (p1, g2) Htrans Hproof_in b1).
                }
                clear Hinst_IH_match.
                rewrite (Hinst_IH_decom hole__t t) in Hdecom.
                clear Hinst_IH_decom.
                
                assert(((g1 ⊢ t : p2, GrammarLists.remove_prod (n, inhole p1 p2) g2 Hproof_in
                        | b2)
                        <->
                        g1 ⊢ t : p2, g2 | b2) /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p2,
                               GrammarLists.remove_prod (n, inhole p1 p2) g2 Hproof_in
                           | b2)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p2, g2 | b2))
                 as [Hinst_IH_match Hinst_IH_decom].
                {assert(pat_grammar_evolution_trans (p2, g2) (inhole p1 p2, g2))
                    as Htrans.
                 {apply t1n_step.
                  eauto.
                 }
                 apply (IP (p2, g2) Htrans Hproof_in b2).
                }
                clear Hinst_IH_decom.
                rewrite Hinst_IH_match in Hmatch_p2.
                clear Hinst_IH_match.
                eauto.
          -- (* we can remove a used prod *)
             intro Hmatch.
             inversion Hmatch as [ | | | | | | |
                                   |t1 t2 C p1' p2' b1 b2 b0 g_rem Hdecom
                                       Hsubterm Hmatch_p2 Heq_bunion Heq_t
                                       Heq_p1 Heq_p2 Heq_g_rem |
                                   t' p1' p2' b1 b2 b0 g_rem Hdecom
                                      Hmatch_p2 Heq_bunion Heq_t
                                      Heq_p1 Heq_g_rem].

             ++ (* sub-pattern pc consumes input *)
                assert(((g1 ⊢ t : p1, GrammarLists.remove_prod (n, inhole p1 p2) g2 Hproof_in
                        | b1)
                        <->
                        g1 ⊢ t : p1, g2 | b1) /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p1,
                               GrammarLists.remove_prod (n, inhole p1 p2) g2 Hproof_in
                           | b1)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p1, g2 | b1))
                 as [Hinst_IH_match Hinst_IH_decom].
                {assert(pat_grammar_evolution_trans (p1, g2) (inhole p1 p2, g2))
                    as Htrans.
                 {apply t1n_step.
                  eauto.
                 }
                 apply (IP (p1, g2) Htrans Hproof_in b1).
                }
                clear Hinst_IH_match.
                rewrite <- (Hinst_IH_decom C t2) in Hdecom.
                clear Hinst_IH_decom.
                eauto.
             ++ (* sub-pattern pc does not consume input *)
                assert(((g1 ⊢ t : p1, GrammarLists.remove_prod (n, inhole p1 p2) g2 Hproof_in
                        | b1)
                        <->
                        g1 ⊢ t : p1, g2 | b1) /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p1,
                               GrammarLists.remove_prod (n, inhole p1 p2) g2 Hproof_in
                           | b1)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p1, g2 | b1))
                 as [Hinst_IH_match Hinst_IH_decom].
                {assert(pat_grammar_evolution_trans (p1, g2) (inhole p1 p2, g2))
                    as Htrans.
                 {apply t1n_step.
                  eauto.
                 }
                 apply (IP (p1, g2) Htrans Hproof_in b1).
                }
                clear Hinst_IH_match.
                rewrite <- (Hinst_IH_decom hole__t t) in Hdecom.
                clear Hinst_IH_decom.
                
                assert(((g1 ⊢ t : p2, GrammarLists.remove_prod (n, inhole p1 p2) g2 Hproof_in
                        | b2)
                        <->
                        g1 ⊢ t : p2, g2 | b2) /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p2,
                               GrammarLists.remove_prod (n, inhole p1 p2) g2 Hproof_in
                           | b2)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p2, g2 | b2))
                 as [Hinst_IH_match Hinst_IH_decom].
                {assert(pat_grammar_evolution_trans (p2, g2) (inhole p1 p2, g2))
                    as Htrans.
                 {apply t1n_step.
                  eauto.
                 }
                 apply (IP (p2, g2) Htrans Hproof_in b2).
                }
                clear Hinst_IH_decom.
                rewrite <- Hinst_IH_match in Hmatch_p2.
                clear Hinst_IH_match.
                eauto.
      + (* decom *)
        intros C subt.
        destruct p as [lit |  | p1 | v p |n0 | p1 p2].
        * (* p = lit *)
          split;
            intro Hdecom;
            inversion Hdecom.
        * (* p = hole *)
          split;
            intro Hdecom;
            inversion Hdecom;
            eauto.
        * (* p, t = cons, ctxt *)
          destruct p1;
            split;
            intro Hdecom;
            inversion Hdecom;
            eauto.
        * (* p = name *)
          split.
          -- (* we can add a removed prod *)
             intro Hdecom.
             inversion Hdecom.

             (* TODO: not every introduced variable can be named *)
             inversion Hdecom as [ | | | | | | | | |
                                   |t1' C' t2' x' p'
                                        b1' b' g2'
                                        Hdecom_p Heqb_union Heq_t
                                        Heq_C Heq_subt
                                        Heq_x Heq_p Heq_g2'].
             assert(((g1 ⊢ t : p, GrammarLists.remove_prod (n, name v p) g2 Hproof_in
                     | b1')
                      <->
                      g1 ⊢ t : p, g2 | b1') /\
                     (forall (C : contxt) (subt : term),
                         (g1 ⊢ t ⩦ C [subt] : p,
                                              GrammarLists.remove_prod (n, name v p) g2
                                                          Hproof_in | b1')
                         <->
                         g1 ⊢ t ⩦ C [subt] : p, g2 | b1'))
                as [Hinst_IH_match Hinst_IH_decom].
             {assert(pat_grammar_evolution_trans (p, g2) (name v p, g2))
                 as Htrans.
              {apply t1n_step.
               eauto.
              }
              apply (IP (p, g2) Htrans Hproof_in b1').
              }
              clear Hinst_IH_match.
              rewrite Hinst_IH_decom in Hdecom_p.
              
              eauto.
          -- (* we can remove a used prod *)
             intro Hdecom.
             (* TODO: not every introduced variable can be named *)
             inversion Hdecom as [ | | | | | | | | |
                                   |t1' C' t2' x' p'
                                        b1' b' g2'
                                        Hdecom_p Heqb_union Heq_t
                                        Heq_C Heq_subt
                                        Heq_x Heq_p Heq_g2'].
             assert(((g1 ⊢ t : p, GrammarLists.remove_prod (n, name v p) g2 Hproof_in | b1')
                      <->
                      g1 ⊢ t : p, g2 | b1') /\
                     (forall (C : contxt) (subt : term),
                         (g1 ⊢ t ⩦ C [subt] : p,
                                              GrammarLists.remove_prod (n, name v p) g2
                                                          Hproof_in | b1')
                         <->
                         g1 ⊢ t ⩦ C [subt] : p, g2 | b1'))
                as [Hinst_IH_match Hinst_IH_decom].
             {assert(pat_grammar_evolution_trans (p, g2) (name v p, g2))
                 as Htrans.
              {apply t1n_step.
               eauto.
              }
              apply (IP (p, g2) Htrans Hproof_in b1').
              }
              clear Hinst_IH_match.
              rewrite <- Hinst_IH_decom in Hdecom_p.
              
              eauto.
        * (* p = nt *)
          split.
          -- (* we can add a removed prod *)
             intro Hdecom.
             inversion Hdecom as  [| | | | | | |
                                   n' p' t' C' subt' b'
                                      g_rem Hprod_in_g_rem Hdecom_p
                                      Heq_t Heq_C Heq_subt
                                      Heq_n Heq_g_rem Heq_b| | |].

             assert(exists (proof_in_pr2' : GrammarLists.prod_in_g (n0, p') g2)
                      (proof_in_pr1' : GrammarLists.prod_in_g (n, nt n0)
                                                 (GrammarLists.remove_prod (n0, p') g2
                                                              proof_in_pr2')),
                       GrammarLists.remove_prod (n0, p') (GrammarLists.remove_prod (n, nt n0) g2
                                                         Hproof_in)
                                   Hprod_in_g_rem
                       =
                       GrammarLists.remove_prod (n, nt n0) (GrammarLists.remove_prod (n0, p') g2
                                                       proof_in_pr2')
                                   proof_in_pr1')
               as Hremove_comm.
             {apply remove_prod_comm.
             }
             inversion Hremove_comm as [Hproof_p'_g2 (Hproof_p_g_rem, Hremove_comm')].
             clear Hremove_comm.

             rewrite Hremove_comm' in Hdecom_p.
             clear Hremove_comm'.

             assert((g1 ⊢ t ⩦ C [subt] : p',
                                        remove_prod (n, nt n0)
                                                    (remove_prod (n0, p')
                                                                 g2
                                                                 Hproof_p'_g2)
                                                    Hproof_p_g_rem | b')
             <->
             g1 ⊢ t ⩦ C [subt] : p', remove_prod (n0, p') g2
                                                 Hproof_p'_g2 | b')
               as Hdecom_eq.
             {assert(pat_grammar_evolution_trans 
                       (p', remove_prod (n0, p') g2 Hproof_p'_g2)
                                      (nt n0, g2))
                 as Htrans.
              {apply t1n_step.
               eauto.
              }
              apply (IP (p', remove_prod (n0, p') g2 Hproof_p'_g2)
                        Htrans
                        Hproof_p_g_rem
                        b').
             }
             rewrite Hdecom_eq in Hdecom_p.

             eauto.
          -- (* we can remove a used prod *)
             intro Hdecom.
             inversion Hdecom as  [| | | | | | |
                                   n' p' t' C' subt' b'
                                      g_rem Hprod_in_g_rem Hdecom_p
                                      Heq_t Heq_C Heq_subt
                                      Heq_n Heq_g_rem Heq_b| | |].

             (* we use the assumption that every grammar is 
                 non-left-recursive *)
               assert((n, nt n0) <> (n0, p'))
                 as Hneq_pair.
               {intro Heq_pair.
                inversion Heq_pair as [Heq_n0].

              
                assert(pat_grammar_evolution_trans 
                         (nt n0, remove_prod (n, nt n0) g2 Hproof_in)
                         (nt n, g2))
                as Htrans.
                {apply t1n_step.
                 eauto.
                }

                revert Htrans.
                revert Hproof_in.
                rewrite Heq_n0.
                intros Hproof_in Htrans.

                assert(not (pat_grammar_evolution_trans 
                              (nt n0, remove_prod (n0, nt n0) g2 Hproof_in)
                              (nt n0, g2)))
                  as Hnot_trans.
                {apply Hnon_lr.
                }
                contradiction.
               }
               
             assert(GrammarLists.prod_in_g (n, nt n0) (remove_prod (n0, p') g2
                                                      Hprod_in_g_rem))
               as Hprod_in_n0_g2.
             {apply remove_prod_in_g_neq.
              exact Hneq_pair.
              exact Hproof_in.
             }

             assert(GrammarLists.prod_in_g (n0, p') (remove_prod (n, nt n0) g2
                                                    Hproof_in))
               as Hprod_in_p'_g2.
             {apply remove_prod_in_g_neq.
              intro Heq_pair.
              apply eq_sym in Heq_pair.
              contradiction.
              exact Hprod_in_g_rem.
             }
             
             assert(forall (C : contxt) (subt : term),
                       (g1 ⊢ t ⩦ C [subt]: p',
                           remove_prod (n, nt n0)
                             (remove_prod (n0, p') g2 Hprod_in_g_rem)
                             Hprod_in_n0_g2
                       | b')
                       <->
                       g1 ⊢ t ⩦ C [subt]: p', remove_prod (n0, p') g2
                                                       Hprod_in_g_rem | b')
               as Heq_decom.
             {assert(pat_grammar_evolution_trans 
                       (p', remove_prod (n0, p') g2 Hprod_in_g_rem)
                       (nt n0, g2))
                 as Htrans.
              {apply t1n_step.
               auto.
              }
              apply (IP (p', remove_prod (n0, p') g2 Hprod_in_g_rem)
                        Htrans
                        Hprod_in_n0_g2
                        b').
             }
             rewrite <- (Heq_decom C subt) in Hdecom_p.
             clear Heq_decom.

             assert(exists (proof_in_pr2' : GrammarLists.prod_in_g (n, nt n0) g2)
                      (proof_in_pr1' : GrammarLists.prod_in_g (n0, p')
                                                 (remove_prod
                                                    (n, nt n0)
                                                    g2
                                                    proof_in_pr2')),
                       remove_prod (n, nt n0)
                                   (remove_prod (n0, p')
                                                      g2
                                                      Hprod_in_g_rem)
                                   Hprod_in_n0_g2
                       =
                       remove_prod (n0, p')
                                   (remove_prod (n, nt n0)
                                                      g2
                                                      proof_in_pr2')
                                   proof_in_pr1')
               as [Hproof_in_n''_g2
                     (Hproof_in_n0_g_rem, Hremove_comm)].
             {apply remove_prod_comm.
             }

             rewrite Hremove_comm in Hdecom_p.
             eauto.
        * (* p = inhole *)
          split.
          -- (* we can add a removed prod *)
             intro Hdecom.
             inversion Hdecom as [| | | | | | |
                                  |t' C1 subt' p1' b1 C2
                                      subt'' p2' b2 b0
                                      g_rem Hdecom_p1 Hsubterm
                                      Hdecom_p2 Heq_bunion Heq_t Heq_C
                                      Heq_subt Heq_p1 Heq_p2
                                      Heq_g_rem
                                  | t' p1' b1 C2
                                       subt'' p2' b2 b0
                                       g_rem Hdecom_p1
                                       Hdecom_p2 Heq_bunion Heq_t Heq_C
                                       Heq_subt Heq_p1 Heq_g_rem
                                  |].
             ++ (* sub-pattern pc consumes input *)
                assert(((g1 ⊢ t : p1, remove_prod (n, inhole p1 p2) g2 Hproof_in
                        | b1)
                        <->
                        g1 ⊢ t : p1, g2 | b1)
                       /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p1,
                                               remove_prod (n, inhole p1 p2)
                                                           g2 Hproof_in
                           | b1)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p1, g2 | b1))
                 as [_ Heq_decom].
                {assert(pat_grammar_evolution_trans (p1, g2) (inhole p1 p2, g2))
                    as Htrans.
                 {apply t1n_step.
                  auto.
                 }
                 apply (IP (p1, g2)
                           Htrans
                           Hproof_in
                           b1).
                }
                rewrite (Heq_decom C1 subt') in Hdecom_p1.
                clear Heq_decom.

                eauto.
             ++ (* sub-pattern pc does not consume input *)
                assert(((g1 ⊢ t : p1, remove_prod (n, inhole p1 p2)
                                                  g2 Hproof_in
                        | b1)
                        <->
                        g1 ⊢ t : p1, g2 | b1)
                       /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p1,
                                               remove_prod (n, inhole p1 p2)
                                                           g2 Hproof_in
                           | b1)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p1, g2 | b1))
                 as [_ Heq_decom].
                {assert(pat_grammar_evolution_trans (p1, g2) (inhole p1 p2, g2))
                    as Htrans.
                 {apply t1n_step.
                  auto.
                 }
                 apply (IP (p1, g2)
                           Htrans
                           Hproof_in
                           b1).
                }
                rewrite (Heq_decom hole__t t) in Hdecom_p1.
                clear Heq_decom.

                assert(((g1 ⊢ t : p2, remove_prod (n, inhole p1 p2)
                                                  g2 Hproof_in
                        | b2)
                        <->
                        g1 ⊢ t : p2, g2 | b2)
                       /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p2,
                                               remove_prod (n, inhole p1 p2)
                                                           g2 Hproof_in
                           | b2)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p2, g2 | b2))
                 as [_ Heq_decom].
                {assert(pat_grammar_evolution_trans (p2, g2) (inhole p1 p2, g2))
                    as Htrans.
                 {apply t1n_step.
                  auto.
                 }
                 apply (IP (p2, g2)
                           Htrans
                           Hproof_in
                           b2).
                }
                rewrite (Heq_decom C2 subt) in Hdecom_p2.
                clear Heq_decom.

                rewrite <- Heq_C.
                
                eauto.
          -- (* we can remove a used prod *)
             intro Hdecom.
             inversion Hdecom as [| | | | | | |
                                  |t' C1 subt' p1' b1 C2
                                      subt'' p2' b2 b0
                                      g_rem 
                                      Hdecom_p1 Hsubterm
                                      Hdecom_p2 Heq_bunion Heq_t Heq_C
                                      Heq_subt Heq_p1 Heq_p2
                                      Heq_g_rem
                                  | t' p1' b1 C2
                                       subt'' p2' b2 b0
                                       g_rem 
                                       Hdecom_p1
                                       Hdecom_p2 Heq_bunion Heq_t Heq_C
                                       Heq_subt Heq_p1 Heq_g_rem
                                  |].
             ++ (* sub-pattern pc consumes input *)
                assert(((g1 ⊢ t : p1, remove_prod (n, inhole p1 p2)
                                                  g2 Hproof_in
                        | b1)
                        <->
                        g1 ⊢ t : p1, g2 | b1)
                       /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p1,
                                               remove_prod (n, inhole p1 p2)
                                                           g2 Hproof_in
                           | b1)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p1, g2 | b1))
                 as [_ Heq_decom].
                {assert(pat_grammar_evolution_trans (p1, g2) (inhole p1 p2, g2))
                    as Htrans.
                 {apply t1n_step.
                  auto.
                 }
                 apply (IP (p1, g2)
                           Htrans
                           Hproof_in
                           b1).
                }
                rewrite <- (Heq_decom C1 subt') in Hdecom_p1.
                clear Heq_decom.

                eauto.
             ++ (* sub-pattern pc does not consume input *)
                assert(((g1 ⊢ t : p1, remove_prod (n, inhole p1 p2)
                                                  g2 Hproof_in
                        | b1)
                        <->
                        g1 ⊢ t : p1, g2 | b1)
                       /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p1,
                                               remove_prod (n, inhole p1 p2)
                                                           g2 Hproof_in
                           | b1)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p1, g2 | b1))
                 as [_ Heq_decom].
                {assert(pat_grammar_evolution_trans (p1, g2) (inhole p1 p2, g2))
                    as Htrans.
                 {apply t1n_step.
                  auto.
                 }
                 apply (IP (p1, g2)
                           Htrans
                           Hproof_in
                           b1).
                }
                rewrite <- (Heq_decom hole__t t) in Hdecom_p1.
                clear Heq_decom.

                assert(((g1 ⊢ t : p2, remove_prod (n, inhole p1 p2)
                                                  g2 Hproof_in
                        | b2)
                        <->
                        g1 ⊢ t : p2, g2 | b2)
                       /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p2,
                                               remove_prod (n, inhole p1 p2)
                                                           g2 Hproof_in
                           | b2)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p2, g2 | b2))
                 as [_ Heq_decom].
                {assert(pat_grammar_evolution_trans (p2, g2) (inhole p1 p2, g2))
                    as Htrans.
                 {apply t1n_step.
                  auto.
                 }
                 apply (IP (p2, g2)
                           Htrans
                           Hproof_in
                           b2).
                }
                rewrite <- (Heq_decom C2 subt) in Hdecom_p2.
                clear Heq_decom.

                rewrite <- Heq_C.
                
                eauto.
    - (* actual proof of the lemma *)
      apply (well_founded_ind
             pat_grammar_evolution_well_founded
              (fun tup : pat * grammar =>
                 match tup with
                 | (p', g2') =>
                   pat_grammar_evolution_trans (p', g2') (p, g2) ->
                   forall (proof_in : prod_in_g (n, p) g2') (b : bindings),
                     (g1 ⊢ t : p', remove_prod (n, p) g2' proof_in | b
                      <->
                      g1 ⊢ t : p', g2' | b) /\
                     (forall (C : contxt) (subt : term),
                         g1 ⊢ t ⩦ C [subt] : p',
                        remove_prod (n, p) g2' proof_in | b
                        <->
                        g1 ⊢ t ⩦ C [subt] : p', g2' | b)
                 end)).

      intros (p', g2') IH Hproof_in_p' b0.
      split.
      ++ (* matching *)
         split.
         + (* when using a production, we could just left it in the 
              grammar *)
           intro Hmatch.
           destruct p'.
           * (* p' = lit pat *)
             inversion Hmatch;
               eauto.
           * (* p' = hole *)
             inversion Hmatch;
               eauto.
           * (* p = cons *)
             inversion Hmatch;
               eauto.
           * (* p = name *)
             inversion Hmatch as [| |t' v' p'' bp b0'
                                        g_rem Hmatch_p
                                        Hb_union Heq_t Heq_v
                                        Heq_g_rem Heq_b0 |  | | | | | |].
             assert(g1 ⊢ t : p', g2' | bp)
               as Hmatch_name.
             {assert(pat_grammar_evolution (p', g2') (name v p', g2'))
                 as Hmrel.
              {auto.
              }

              assert(pat_grammar_evolution_trans (p', g2') (p, g2))
                as Htrans.
              {assert(pat_grammar_evolution_trans (p', g2') (name v p', g2'))
                  as Htrans_step.
               {apply t1n_step.
                eauto.
               }
               eapply (t1n_trans _ _ _ _).
               apply Hmrel.
               exact Hproof_in_p'.
              }

              assert(((g1 ⊢ t : p', remove_prod (n, p) g2' b0 | bp)
                      <->
                      g1 ⊢ t : p', g2' | bp) /\
                     (forall (C : contxt) (subt : term),
                         (g1 ⊢ t ⩦ (C) [(subt)] : p',
                                                  remove_prod (n, p) g2'
                                                              b0 | bp)
                         <->
                         g1 ⊢ t ⩦ (C) [(subt)] : p', g2' | bp))
                as [Hinst_IH_match Hinst_IH_decom].
              {apply (IH (p', g2') Hmrel Htrans b0 bp).
              }
              rewrite Hinst_IH_match in Hmatch_p.
              exact Hmatch_p.
             } 
             eauto.
             
           * (* p = nt *)
             inversion Hmatch as  [| | | n' p' t' b' g_rem Hprod_in_p'
                                            Hmatch_p' Heq_t' Heq_n'
                                            Heq_g_rem Heq_bind | | | | | |].

             assert(exists (proof_in_pr2' : prod_in_g (n0, p') g2')
                      (proof_in_pr1' : prod_in_g (n, p)
                                                 (remove_prod (n0, p') g2'
                                                              proof_in_pr2')),
                       remove_prod (n0, p') (remove_prod (n, p) g2'
                                                         b0)
                                   Hprod_in_p'
                       = remove_prod (n, p) (remove_prod (n0, p') g2'
                                                         proof_in_pr2')
                                     proof_in_pr1')
               as Hremove_comm.
             {apply remove_prod_comm.
             }
             inversion Hremove_comm as [Hproof_p'_g2 (Hproof_p_g_rem, Hremove_comm')].
             clear Hremove_comm.

             rewrite Hremove_comm' in Hmatch_p'.
             clear Hremove_comm'.

             assert((g1 ⊢ t : p', remove_prod (n, p)
                                              (remove_prod (n0, p') g2'
                                                           Hproof_p'_g2)
                                              Hproof_p_g_rem | b')
                    <->
                    g1 ⊢ t : p', (remove_prod (n0, p') g2'
                                              Hproof_p'_g2) | b')
               as Hmatch_eq.
             {assert(pat_grammar_evolution_trans 
                       (p', remove_prod (n0, p') g2' Hproof_p'_g2)
                       (p, g2))
                 as Htrans.
              {eapply t1n_trans.
               eauto using pat_grammar_evolution.
               exact Hproof_in_p'.
              }
              apply (IH (p', remove_prod (n0, p') g2' Hproof_p'_g2)
                        (pat_grammar_evolution_nt _ _ _ _)
                        Htrans
                        Hproof_p_g_rem
                        b').
             }
             
             rewrite Hmatch_eq in Hmatch_p'.

             apply (nt_match_spec g1 n0 p' t b' g2' Hproof_p'_g2).
             exact Hmatch_p'.
           * (* p = inhole *)
             inversion Hmatch as [ | | | | | | |
                                  | t' subt C p1 p2 b1' b2 b0' g_rem
                                       Hdecom Hsubterm Hmatch_p2
                                       Heq_bunion Heq_t Heq_p1 Heq_g_rem
                                       Heq_b0 | ].
             -- (* decomposing with p1 produces consumption of input *)
                (* instantiate IH *)
                assert((g1 ⊢ t ⩦ C [subt] : p'1,
                           remove_prod (n, p) g2' b0 | b1')
                       <->
                       g1 ⊢ t ⩦ C [subt] : p'1, g2' | b1')
                 as Hinst_IH.
                {assert(pat_grammar_evolution (p'1, g2') (inhole p'1 p'2, g2'))
                    as Hmrel.
                 {auto.
                 }

                 assert(pat_grammar_evolution_trans (p'1, g2') (p, g2))
                   as Htrans.
                 {eapply t1n_trans.
                  exact Hmrel.
                  exact Hproof_in_p'.
                 }
                 
                 apply (IH (p'1, g2') Hmrel Htrans b0 b1').
                }
                rewrite Hinst_IH in Hdecom.
                eauto.
             -- (* decomposing with p1 does not produce consumption of 
                  input *)
                assert((g1 ⊢ t ⩦ hole__t [t] : p'1,
                                             remove_prod (n, p) g2'
                                                         b0 | b2)
                      <->
                      g1 ⊢ t ⩦ hole__t [t] : p'1, g2' | b2)
                 as Hinst_IH.
               {assert(pat_grammar_evolution (p'1, g2') (inhole p'1 p'2, g2'))
                   as Hmrel.
                {auto.
                }
                assert(pat_grammar_evolution_trans (p'1, g2') (p, g2))
                  as Htrans.
                {eapply t1n_trans.
                 exact Hmrel.
                 exact Hproof_in_p'.
                }
                apply (IH (p'1, g2') Hmrel Htrans b0 b2).
               }
               rewrite Hinst_IH in H.
               clear Hinst_IH.

               assert((g1 ⊢ t : p'2, remove_prod (n, p) g2'
                                                 b0 | b3)
                      <->
                      g1 ⊢ t : p'2, g2' | b3)
                 as Hinst_IH.
               {assert(pat_grammar_evolution (p'2, g2') (inhole p'1 p'2, g2'))
                   as Hmrel.
                {auto.
                }

                assert(pat_grammar_evolution_trans (p'2, g2') (p, g2))
                  as Htrans.
                {eapply t1n_trans.
                 exact Hmrel.
                 exact Hproof_in_p'.
                }
                apply (IH (p'2, g2') Hmrel Htrans b0 b3).
               }
               rewrite Hinst_IH in H0.
               clear Hinst_IH.
               eauto.
               
         + (* when can remove a production that we've just used *)
           intro Hmatch.
           destruct p'.
           * (* p' = lit *)
             inversion Hmatch.
             auto.
           * (* p' = hole *)
             inversion Hmatch.
             auto.
           * (* p' = cons, contxt *)
             (* simple application of constructors of match_spec *)
             inversion Hmatch;
               eauto. 
           * (* p' = name *)
             inversion Hmatch as [| |t' v' p'' bp b0'
                                        g_rem Hmatch_p
                                        Hb_union Heq_t Heq_v
                                        Heq_g_rem Heq_b0 |  | | | | | |].
             assert((g1 ⊢ t : p', remove_prod (n, p) g2' b0 | bp)
                    <->
                    g1 ⊢ t : p', g2' | bp)
               as Hinst_IH.
             {assert(pat_grammar_evolution (p', g2') (name v p', g2'))
                 as Hmrel.
              {auto.
              }

              assert(((g1 ⊢ t : p', remove_prod (n, p) g2' b0 | bp)
                      <->
                      g1 ⊢ t : p', g2' | bp) /\
                     (forall (C : contxt) (subt : term),
                         (g1 ⊢ t ⩦ C [subt]: p', remove_prod (n, p) g2' b0 | bp)
                         <->
                         g1 ⊢ t ⩦ C [subt]: p', g2' | bp))
                as Hinst_IH'.
              {assert(pat_grammar_evolution_trans (p', g2') (p, g2))
                  as Htrans.
               {eapply t1n_trans.
                exact Hmrel.
                exact Hproof_in_p'.
               }
               apply (IH (p', g2') Hmrel Htrans b0 bp).
              }
              intuition eauto.
             }

             rewrite <- Hinst_IH in Hmatch_p.
             eauto.
           * (* p' = nt *)
             inversion Hmatch as  [| | | n' p' t' b' g_rem Hprod_in_p'
                                            Hmatch_p' Heq_t' Heq_n'
                                            Heq_g_rem Heq_bind | | | | | |].

             (* we use the assumption that every grammar is 
                non-left-recursive *)
             assert((n, p) <> (n0, p'))
               as Hneq_pair.
             {intro Heq_pair.
              inversion Heq_pair as [Heq_n].

              
              assert(pat_grammar_evolution_trans 
                       (nt n0, remove_prod (n, p) g2' b0)
                       (p, remove_prod (n, p) g2 Hproof_in))
                as Htrans.
              {clear IH Hmatch n' p' t' b' Hprod_in_p' Hmatch_p'
                     Heq_t' Heq_n' Heq_pair H Heq_g_rem Heq_bind Heq_n
                     g1 t b b1 g_rem.

               (* unfold trans_clos_noinp in Hproof_in_p'. *)
               (* unfold trans_clos_noinp. *)
               revert Hproof_in_p'.
               generalize (nt n0).
               intros p0 Hproof_in_p'.

               assert(forall (p1 p2 : pat)
                        (g1 g2 : grammar)
                        (proof_in_g1 : prod_in_g (n, p) g1)
                        (proof_in_g2 : prod_in_g (n, p) g2),
                         pat_grammar_evolution (p1, g1) (p2, g2) ->
                         pat_grammar_evolution
                           (p1, remove_prod (n, p) g1
                                            proof_in_g1)
                           (p2, remove_prod (n, p) g2
                                            proof_in_g2))
                 as Hbase_case.
               {intros p1 p2 g0 g1 proof_in_g0 proof_in_g1 Hmrel.
                inversion Hmrel as [g2'' pc ph Heq_ph Heq_p |
                                    g2'' pc ph Heq_pc Heq_p |
                                    g2'' nt' x Heq_nt Heq_p |
                                    g2'' nt' n'' Hproof_n0_in_g2 Heq_nt
                                         Heq_p].
                 + (* p = inhole, right sub-pattern *)
                   revert b0.
                   revert Hproof_in.
                   revert proof_in_g0.
                   rewrite H0.
                   intros Hproof_in b0 proof_in_g0.
                   rewrite (remove_prod_prod_in_g_irrelevance
                              g1
                              (n, p)
                              proof_in_g1
                              Hproof_in).
                   eauto.
                 + (* p = inhole, left sub-pattern *)
                   revert b0.
                   revert Hproof_in.
                   revert proof_in_g0.
                   rewrite H0.
                   intros proof_in_g0 Hproof_in b0.
                   rewrite (remove_prod_prod_in_g_irrelevance
                              g1
                              (n, p)
                              proof_in_g0
                              proof_in_g1).
                   eauto.
                 + (* p = name *)
                   revert b0.
                   revert Hproof_in.
                   revert proof_in_g0.
                   rewrite H0.
                   intros proof_in_g0 Hproof_in b0.
                   rewrite (remove_prod_prod_in_g_irrelevance
                              g1
                              (n, p)
                              proof_in_g0
                              proof_in_g1).
                   eauto.
                 + (* p = nt *)
                   revert b0.
                   revert Hproof_in.
                   revert proof_in_g1.
                   revert H.
                   revert Hproof_n0_in_g2.
                   rewrite H0.
                   intros Hproof_n0_in_g2 H proof_in_g1 Hproof_in b0.

                   revert proof_in_g0.
                   rewrite <- H.
                   intro proof_in_g0.
                   
                   assert(exists (proof_in_pr2' : prod_in_g (n, p) g1)
                            (proof_in_pr1' : prod_in_g (n'', p1)
                                                       (remove_prod
                                                          (n, p)
                                                          g1
                                                          proof_in_pr2')),
                             remove_prod (n, p)
                                         (remove_prod (n'', p1)
                                                            g1
                                                            Hproof_n0_in_g2)
                                         proof_in_g0
                             =
                             remove_prod (n'', p1)
                                         (remove_prod (n, p)
                                                            g1
                                                            proof_in_pr2')
                                         proof_in_pr1')
                     as [Hproof_in_n''_g2
                           (Hproof_in_n0_g_rem, Hremove_comm)].
                   {apply remove_prod_comm.
                   }

                   rewrite Hremove_comm.
                   clear Hremove_comm.
                   revert Hproof_in_n0_g_rem.
                   rewrite (remove_prod_prod_in_g_irrelevance
                              g1
                              (n, p)
                              Hproof_in_n''_g2
                              proof_in_g1).
                   intro Hproof_in_n0_g_rem.
                   eauto.
               }
               
               dependent induction Hproof_in_p'.
               - (* is a m_rel_noinp_cons step *)
                 apply t1n_step.
                 apply Hbase_case.
                 exact H.
               - (* is a trans step *)
                 destruct y as [p' g2''].

                 (* instantiate IH *)
                 assert(prod_in_g (n, p) g2'')
                     as Hprod_in_g2''.
                 {generalize pat_grammar_evolution_no_prod_added.
                  intro lemma.
                  eauto.
                 }
                 
                 assert(pat_grammar_evolution_trans
                                      (p', remove_prod (n, p) g2''
                                                       Hprod_in_g2'')
                                      (p, remove_prod (n, p) g2
                                                      Hproof_in))
                   as Hinst_IH_r.
                 {apply IHHproof_in_p'.
                  reflexivity.
                  reflexivity.
                  exact Hbase_case.
                 }
                 
                 assert(pat_grammar_evolution
                          (p0, remove_prod (n, p) g2' b0)
                          (p', remove_prod (n, p) g2'' Hprod_in_g2''))
                    as Hbase_inst.
                 {eauto.
                 }

                 eapply t1n_trans.
                 exact Hbase_inst.
                 exact Hinst_IH_r.
              }

              assert(pat_grammar_evolution_trans 
                       (p, remove_prod (n, p) g2 Hproof_in)
                       (nt n, g2))
                as Htrans_p_n.
              {apply t1n_step.
               eauto.
              }

              assert(pat_grammar_evolution_trans 
                       (nt n, remove_prod (n, p) g2' b0)
                       (nt n, g2))
                as Htrans_n_n.
              {revert Htrans.
               revert b0.
               revert Htrans_p_n.
               revert Hproof_in.
               rewrite Heq_n.
               intros Hproof_in Htrans_p_n b0 Htrans.

               clear Hmatch Hmatch_p' Heq_t' Heq_n' Heq_g_rem Heq_bind
                     Heq_pair H IH Hnon_lr t b Hproof_in_p'
                     b1 n' t' b' g_rem Hprod_in_p' Heq_n p' n.
               
               induction Htrans.
               - (* one m_rel_noinp_cons step *)
                 (* unfold trans_clos_noinp in Htrans_p_n. *)
                 (* unfold trans_clos_noinp. *)
                 eapply t1n_trans.
                 + (* m_rel_noinp_cons step *)
                   exact H.
                 + (* trans step *)
                   exact Htrans_p_n.
               - (* one m_rel_noinp_cons step and one trans step *)
                 assert(pat_grammar_evolution_trans y (nt n0, g2))
                   as Htrans_y_n0.
                 {apply IHHtrans.
                  exact Htrans_p_n.
                 }
                 eapply t1n_trans.
                 + (* m_rel_noinp_cons step *)
                   exact H.
                 + (* trans step *)
                   exact Htrans_y_n0.
              }
              
              assert(not (pat_grammar_evolution_trans 
                            (nt n, remove_prod (n, p) g2' b0)
                            (nt n, g2)))
                as Hinst_non_left.
              {apply Hnon_lr.
              }

              contradiction.
             }

             assert(prod_in_g (n, p) (remove_prod (n0, p') g2' Hprod_in_p'))
               as Hn_p_in_g2'_rem.
             {apply remove_prod_in_g_neq.
              exact Hneq_pair.
              exact b0.
             }

             assert((g1 ⊢ t : p', remove_prod (n, p)
                                              (remove_prod (n0, p') g2'
                                                           Hprod_in_p')
                                              Hn_p_in_g2'_rem | b')
                    <->
                    g1 ⊢ t : p', (remove_prod (n0, p') g2' Hprod_in_p') |
                    b')
               as Hinst_IH.
             {assert(pat_grammar_evolution_trans 
                       (p', remove_prod (n0, p') g2'
                              Hprod_in_p') (p, g2))
                 as Htrans.
              {eapply t1n_trans.
               eauto.
               exact Hproof_in_p'.
              }

              assert(pat_grammar_evolution 
                       (p', remove_prod (n0, p') g2' Hprod_in_p')
                       (nt n0, g2'))
                as Hmrel_step.
              {auto.
              }
              
              apply (IH (p', remove_prod (n0, p') g2' Hprod_in_p')
                        Hmrel_step
                        Htrans
                        Hn_p_in_g2'_rem
                        b').
             }
             rewrite <- Hinst_IH in Hmatch_p'.
             clear Hinst_IH.

             assert(exists (proof_in_pr2' : prod_in_g (n, p) g2')
                      (proof_in_pr1' : prod_in_g (n0, p')
                                                 (remove_prod
                                                    (n, p)
                                                    g2'
                                                    proof_in_pr2')),
                       remove_prod (n, p)
                                   (remove_prod (n0, p')
                                                      g2'
                                                      Hprod_in_p')
                                   Hn_p_in_g2'_rem
                       =
                       remove_prod (n0, p')
                                   (remove_prod (n, p)
                                                      g2'
                                                      proof_in_pr2')
                                   proof_in_pr1')
               as [Hproof_in_n''_g2
                     (Hproof_in_n0_g_rem, Hremove_comm)].
             {apply remove_prod_comm.
             }

             rewrite Hremove_comm in Hmatch_p'.
             eauto.
           * (* p' = inhole *)
             inversion Hmatch as [ | | | | | | |
                                   |t1 t2 C p1' p2' b1' b2 b0' g_rem Hdecom
                                       Hsubterm Hmatch_p2 Heq_bunion Heq_t
                                       Heq_p1 Heq_p2 Heq_g_rem |
                                   t' p1' p2' b1' b2 b0' g_rem Hdecom
                                      Hmatch_p2 Heq_bunion Heq_t
                                      Heq_p1 Heq_g_rem].

             -- (* sub-pattern pc consumes input *)
                assert(((g1 ⊢ t : p'1, remove_prod (n, p) g2' b0 | b1')
                        <->
                        g1 ⊢ t : p'1, g2' | b1') /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p'1,
                                               remove_prod (n, p)
                                                           g2' b0
                           | b1')
                           <->
                           g1 ⊢ t ⩦ C [subt]: p'1, g2' | b1'))
                 as [Hinst_IH_match Hinst_IH_decom].
                {assert(pat_grammar_evolution_trans (p'1, g2') (p, g2))
                    as Htrans.
                 {eapply t1n_trans.
                  apply pat_grammar_evolution_inhole_left.
                  exact Hproof_in_p'.
                 }

                 assert(pat_grammar_evolution (p'1, g2') (inhole p'1 p'2, g2'))
                   as Hmrel_step.
                 {auto.
                 }
                 
                 apply (IH (p'1, g2') Hmrel_step Htrans b0 b1').
                }
                clear Hinst_IH_match.
                rewrite <- (Hinst_IH_decom C t2) in Hdecom.
                clear Hinst_IH_decom.
                eauto.
             -- (* sub-pattern pc does not consume input *)
                assert(((g1 ⊢ t : p'1, remove_prod (n, p) g2' b0 | b1')
                        <->
                        g1 ⊢ t : p'1, g2' | b1') /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p'1,
                               remove_prod (n, p) g2' b0
                           | b1')
                           <->
                           g1 ⊢ t ⩦ C [subt]: p'1, g2' | b1'))
                 as [_ Hinst_IH_decom].
                {assert(pat_grammar_evolution_trans (p'1, g2') (p, g2))
                    as Htrans.
                 {eapply t1n_trans.
                  apply pat_grammar_evolution_inhole_left.
                  exact Hproof_in_p'.
                 }

                 assert(pat_grammar_evolution (p'1, g2') (inhole p'1 p'2, g2'))
                   as Hmrel_step.
                 {auto.
                 }
                 
                 apply (IH (p'1, g2') Hmrel_step Htrans b0 b1').
                }
                rewrite <- (Hinst_IH_decom hole__t t) in Hdecom.
                clear Hinst_IH_decom.
                
                assert(((g1 ⊢ t : p'2, remove_prod (n, p) g2' b0
                        | b2)
                        <->
                        g1 ⊢ t : p'2, g2' | b2) /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p'2,
                               remove_prod (n, p) g2' b0
                           | b2)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p'2, g2' | b2))
                 as [Hinst_IH_match _].
                {assert(pat_grammar_evolution_trans (p'2, g2') (p, g2))
                    as Htrans.
                 {eapply t1n_trans.
                  apply pat_grammar_evolution_inhole_right.
                  exact Hproof_in_p'.
                 }

                 assert(pat_grammar_evolution (p'2, g2') (inhole p'1 p'2, g2'))
                   as Hmrel_step.
                 {auto.
                 }
                 apply (IH (p'2, g2') Hmrel_step Htrans b0 b2).
                }
                rewrite <- Hinst_IH_match in Hmatch_p2.
                clear Hinst_IH_match.
                eauto.
     ++ (* decomposition *)
        intros C subt.
        destruct p' as [lit |  | p1 | v p'' |n0 | p1 p2].
        * (* p = lit *)
          split;
            intro Hdecom;
            inversion Hdecom.
        * (* p = hole *)
          split;
            intro Hdecom;
            inversion Hdecom;
            eauto.
        * (* p, t = cons, ctxt *)
          split;
            intro Hdecom;
            inversion Hdecom;
            eauto.
        * (* p = name *)
          split.
          -- (* we can add a removed prod *)
             intro Hdecom.
             inversion Hdecom.

             (* TODO: not every introduced variable can be named *)
             inversion Hdecom as [ | | | | | | | | |
                                   |t1' C' t2' x' p'
                                        b1' b' g2''
                                        Hdecom_p Heqb_union Heq_t
                                        Heq_C Heq_subt
                                        Heq_x Heq_p Heq_g2'].
             assert(((g1 ⊢ t : p'', remove_prod (n, p) g2' b0
                     | b1')
                      <->
                      g1 ⊢ t : p'', g2' | b1') /\
                     (forall (C : contxt) (subt : term),
                         (g1 ⊢ t ⩦ C [subt] : p'',
                                              remove_prod (n, p) g2'
                                                          b0 | b1')
                         <->
                         g1 ⊢ t ⩦ C [subt] : p'', g2' | b1'))
               as [Hinst_IH_match Hinst_IH_decom].
             {assert(pat_grammar_evolution_trans (p'', g2') (p, g2))
                 as Htrans.
              {eapply t1n_trans.
               eauto.
               exact Hproof_in_p'.
              }

              assert(pat_grammar_evolution (p'', g2') (name v p'', g2'))
                as Hmrel_step.
              {auto.
              }
              
              apply (IH (p'', g2') Hmrel_step Htrans b0 b1').
              }
              clear Hinst_IH_match.
              rewrite Hinst_IH_decom in Hdecom_p.
              
              eauto.
          -- (* we can remove a used prod *)
             intro Hdecom.
             (* TODO: not every introduced variable can be named *)
             inversion Hdecom as [ | | | | | | | | |
                                   |t1' C' t2' x' p'
                                        b1' b' g2''
                                        Hdecom_p Heqb_union Heq_t
                                        Heq_C Heq_subt
                                        Heq_x Heq_p Heq_g2'].
             assert(((g1 ⊢ t : p'', remove_prod (n, p) g2' b0
                     | b1')
                      <->
                      g1 ⊢ t : p'', g2' | b1') /\
                     (forall (C : contxt) (subt : term),
                         (g1 ⊢ t ⩦ C [subt] : p'',
                                              remove_prod (n, p) g2'
                                                          b0 | b1')
                         <->
                         g1 ⊢ t ⩦ C [subt] : p'', g2' | b1'))
                as [Hinst_IH_match Hinst_IH_decom].
             {assert(pat_grammar_evolution_trans (p'', g2') (p, g2))
                 as Htrans.
              {eapply t1n_trans.
               eauto.
               exact Hproof_in_p'.
              }

              assert(pat_grammar_evolution (p'', g2') (name v p'', g2'))
                as Hmrel_step.
              {auto.
              }
              
              apply (IH (p'', g2') Hmrel_step Htrans b0 b1').
              }
              clear Hinst_IH_match.
              rewrite <- Hinst_IH_decom in Hdecom_p.
              
              eauto.
        * (* p = nt *)
          split.
          -- (* we can add a removed prod *)
             intro Hdecom.
             inversion Hdecom as  [| | | | | | |
                                   n' p' t' C' subt' b'
                                      g_rem Hprod_in_g_rem Hdecom_p
                                      Heq_t Heq_C Heq_subt
                                      Heq_n Heq_g_rem Heq_b| | |].

             assert(exists (proof_in_pr2' : prod_in_g (n0, p') g2')
                      (proof_in_pr1' : prod_in_g (n, p)
                                                 (remove_prod (n0, p') g2'
                                                              proof_in_pr2')),
                       remove_prod (n0, p') (remove_prod (n, p) g2'
                                                         b0)
                                   Hprod_in_g_rem
                       =
                       remove_prod (n, p) (remove_prod (n0, p') g2'
                                                       proof_in_pr2')
                                   proof_in_pr1')
               as Hremove_comm.
             {apply remove_prod_comm.
             }
             inversion Hremove_comm as [Hproof_p'_g2 (Hproof_p_g_rem, Hremove_comm')].
             clear Hremove_comm.

             rewrite Hremove_comm' in Hdecom_p.
             clear Hremove_comm'.

             assert((g1 ⊢ t ⩦ C [subt] : p',
                                        remove_prod (n, p)
                                                    (remove_prod (n0, p')
                                                                 g2'
                                                                 Hproof_p'_g2)
                                                    Hproof_p_g_rem | b')
             <->
             g1 ⊢ t ⩦ C [subt] : p', remove_prod (n0, p') g2'
                                                 Hproof_p'_g2 | b')
               as Hdecom_eq.
             {assert(pat_grammar_evolution_trans 
                       (p', remove_prod (n0, p') g2' Hproof_p'_g2)
                       (p, g2))
                 as Htrans.
              {eapply t1n_trans.
               eauto.
               exact Hproof_in_p'.
              }

              assert(pat_grammar_evolution 
                       (p', remove_prod (n0, p') g2' Hproof_p'_g2)
                       (nt n0, g2'))
                as Hmrel_step.
              {auto.
              }
              
              apply (IH (p', remove_prod (n0, p') g2' Hproof_p'_g2)
                        Hmrel_step
                        Htrans
                        Hproof_p_g_rem
                        b').
             }
             rewrite Hdecom_eq in Hdecom_p.

             eauto.
          -- (* we can remove a used prod *)
             intro Hdecom.
             inversion Hdecom as  [| | | | | | |
                                   n' p' t' C' subt' b'
                                      g_rem Hprod_in_g_rem Hdecom_p
                                      Heq_t Heq_C Heq_subt
                                      Heq_n Heq_g_rem Heq_b| | |].

             (* we use the assumption that every grammar is 
                non-left-recursive *)
             assert((n, p) <> (n0, p'))
               as Hneq_pair.
             {intro Heq_pair.
              inversion Heq_pair as [Heq_n0].

              
              assert(pat_grammar_evolution_trans 
                       (nt n0, remove_prod (n, p) g2' b0)
                       (p, remove_prod (n, p) g2 Hproof_in))
                as Htrans.
              {clear IH Hdecom n' t' b' Hdecom_p
                     Heq_t Heq_C Heq_pair H Heq_g_rem Heq_b Heq_n
                     g1 t b b1 g_rem C C' Heq_subt subt subt' Heq_n0
                     Hprod_in_g_rem p'.

               revert Hproof_in_p'.
               generalize (nt n0).
               intros p0 Hproof_in_p'.

               assert(forall (p1 p2 : pat)
                        (g1 g2 : grammar)
                        (proof_in_g1 : prod_in_g (n, p) g1)
                        (proof_in_g2 : prod_in_g (n, p) g2),
                         pat_grammar_evolution (p1, g1) (p2, g2) ->
                         pat_grammar_evolution
                           (p1, remove_prod (n, p) g1
                                            proof_in_g1)
                           (p2, remove_prod (n, p) g2
                                            proof_in_g2))
                 as Hbase_case.
               {intros p1 p2 g0 g1 proof_in_g0 proof_in_g1 Hmrel.
                inversion Hmrel as [g2'' pc ph Heq_ph Heq_p |
                                    g2'' pc ph Heq_pc Heq_p |
                                    g2'' nt' x Heq_nt Heq_p |
                                    g2'' nt' n'' Hproof_n0_in_g2 Heq_nt
                                         Heq_p].
                 + (* p = inhole, right sub-pattern *)
                   revert b0.
                   revert Hproof_in.
                   revert proof_in_g0.
                   rewrite H0.
                   intros Hproof_in b0 proof_in_g0.
                   rewrite (remove_prod_prod_in_g_irrelevance
                              g1
                              (n, p)
                              proof_in_g1
                              Hproof_in).
                   eauto.
                 + (* p = inhole, left sub-pattern *)
                   revert b0.
                   revert Hproof_in.
                   revert proof_in_g0.
                   rewrite H0.
                   intros proof_in_g0 Hproof_in b0.
                   rewrite (remove_prod_prod_in_g_irrelevance
                              g1
                              (n, p)
                              proof_in_g0
                              proof_in_g1).
                   eauto.
                 + (* p = name *)
                   revert b0.
                   revert Hproof_in.
                   revert proof_in_g0.
                   rewrite H0.
                   intros proof_in_g0 Hproof_in b0.
                   rewrite (remove_prod_prod_in_g_irrelevance
                              g1
                              (n, p)
                              proof_in_g0
                              proof_in_g1).
                   eauto.
                 + (* p = nt *)
                   revert b0.
                   revert Hproof_in.
                   revert proof_in_g1.
                   revert H.
                   revert Hproof_n0_in_g2.
                   rewrite H0.
                   intros Hproof_n0_in_g2 H proof_in_g1 Hproof_in b0.

                   revert proof_in_g0.
                   rewrite <- H.
                   intro proof_in_g0.
                   
                   assert(exists (proof_in_pr2' : prod_in_g (n, p) g1)
                            (proof_in_pr1' : prod_in_g (n'', p1)
                                                       (remove_prod
                                                          (n, p)
                                                          g1
                                                          proof_in_pr2')),
                             remove_prod (n, p)
                                         (remove_prod (n'', p1)
                                                            g1
                                                            Hproof_n0_in_g2)
                                         proof_in_g0
                             =
                             remove_prod (n'', p1)
                                         (remove_prod (n, p)
                                                            g1
                                                            proof_in_pr2')
                                         proof_in_pr1')
                     as [Hproof_in_n''_g2
                           (Hproof_in_n0_g_rem, Hremove_comm)].
                   {apply remove_prod_comm.
                   }

                   rewrite Hremove_comm.
                   clear Hremove_comm.
                   revert Hproof_in_n0_g_rem.
                   rewrite (remove_prod_prod_in_g_irrelevance
                              g1
                              (n, p)
                              Hproof_in_n''_g2
                              proof_in_g1).
                   intro Hproof_in_n0_g_rem.
                   eauto.
               }
               
               dependent induction Hproof_in_p'.
               - (* is a m_rel_noinp_cons step *)
                 apply t1n_step.
                 apply Hbase_case.
                 exact H.
               - (* is a trans step *)
                 destruct y as [p' g2''].

                 (* instantiate IH *)
                 assert(prod_in_g (n, p) g2'')
                     as Hprod_in_g2''.
                 {generalize pat_grammar_evolution_no_prod_added.
                  intro lemma.
                  eauto.
                 }
                 assert(pat_grammar_evolution_trans
                          (p', remove_prod (n, p) g2'' Hprod_in_g2'')
                          (p, remove_prod (n, p) g2 Hproof_in))
                   as Hinst_IH_r.
                 {apply IHHproof_in_p'.
                  reflexivity.
                  reflexivity.
                  exact Hbase_case.
                 }
                 
                 assert(pat_grammar_evolution
                          (p0, remove_prod (n, p) g2' b0)
                          (p', remove_prod (n, p) g2'' Hprod_in_g2''))
                    as Hbase_inst.
                 {eauto.
                 }

                 eapply t1n_trans.
                 exact Hbase_inst.
                 exact Hinst_IH_r.
              }

              assert(pat_grammar_evolution_trans 
                       (p, remove_prod (n, p) g2 Hproof_in)
                       (nt n, g2))
                as Htrans_p_n.
              {apply t1n_step.
               eauto.
              }

              assert(pat_grammar_evolution_trans  
                       (nt n, remove_prod (n, p) g2' b0)
                       (nt n, g2))
                as Htrans_n_n.
              {revert Htrans.
               revert b0.
               revert Htrans_p_n.
               revert Hproof_in.
               rewrite Heq_n0.
               intros Hproof_in Htrans_p_n b0 Htrans.

               clear Hdecom_p Heq_t Heq_n Heq_g_rem Heq_b
                     Heq_pair H IH Hnon_lr b Hproof_in_p'
                     n' t' b' g_rem Heq_n.

               induction Htrans.
               - (* one m_rel_noinp_cons step *)
                 eapply t1n_trans.
                 + (* m_rel_noinp_cons step *)
                   exact H.
                 + (* trans step *)
                   exact Htrans_p_n.
               - (* one m_rel_noinp_cons step and one trans step *)
                 assert(pat_grammar_evolution_trans y (nt n0, g2))
                   as Htrans_y_n0.
                 {apply IHHtrans.
                  exact Htrans_p_n.
                 }
                 eapply t1n_trans.
                 + (* m_rel_noinp_cons step *)
                   exact H.
                 + (* trans step *)
                   exact Htrans_y_n0.
              }
              
              assert(not (pat_grammar_evolution_trans 
                            (nt n, remove_prod (n, p) g2' b0)
                            (nt n, g2)))
                as Hinst_non_left.
              {apply Hnon_lr.
              }

              contradiction.
             }

             assert(prod_in_g (n, p) (remove_prod (n0, p') g2'
                                                  Hprod_in_g_rem))
               as Hn_p_in_g2'_rem.
             {apply remove_prod_in_g_neq.
              exact Hneq_pair.
              exact b0.
             }

             assert((g1 ⊢ t  ⩦ (C) [(subt)] : p',
                                              remove_prod (n, p)
                                                          (remove_prod
                                                             (n0, p') g2'
                                                             Hprod_in_g_rem)
                                                          Hn_p_in_g2'_rem | b')
                    <->
                    g1 ⊢ t  ⩦ (C) [(subt)] : p',
                                             remove_prod (n0, p') g2'
                                                         Hprod_in_g_rem |
                    b')
               as Hinst_IH.
             {assert(pat_grammar_evolution_trans  
                       (p', remove_prod (n0, p') g2' Hprod_in_g_rem)
                       (p, g2))
                 as Htrans.
              {eapply t1n_trans.
               eauto.
               exact Hproof_in_p'.
              }

              assert(pat_grammar_evolution 
                       (p', remove_prod (n0, p') g2' Hprod_in_g_rem)
                       (nt n0, g2'))
                as Hmrel_step.
              {auto.
              }
              
              apply (IH (p', remove_prod (n0, p') g2' Hprod_in_g_rem)
                         Hmrel_step
                         Htrans
                         Hn_p_in_g2'_rem
                         b').
             }
             rewrite <- Hinst_IH in Hdecom_p.
             clear Hinst_IH.

             assert(exists (proof_in_pr2' : prod_in_g (n, p) g2')
                      (proof_in_pr1' : prod_in_g (n0, p')
                                                 (remove_prod
                                                    (n, p)
                                                    g2'
                                                    proof_in_pr2')),
                       remove_prod (n, p)
                                   (remove_prod (n0, p')
                                                      g2'
                                                      Hprod_in_g_rem)
                                   Hn_p_in_g2'_rem
                       =
                       remove_prod (n0, p')
                                   (remove_prod (n, p)
                                                      g2'
                                                      proof_in_pr2')
                                   proof_in_pr1')
               as [Hproof_in_n''_g2
                     (Hproof_in_n0_g_rem, Hremove_comm)].
             {apply remove_prod_comm.
             }

             rewrite Hremove_comm in Hdecom_p.
             eauto.
        * (* p = inhole *)
          split.
          -- (* we can add a removed prod *)
             intro Hdecom.
             inversion Hdecom as [| | | | | | |
                                  |t' C1 subt' p1' b1' C2
                                      subt'' p2' b2 b0'
                                      g_rem 
                                      Hdecom_p1 Hsubterm
                                      Hdecom_p2 Heq_bunion Heq_t Heq_C
                                      Heq_subt Heq_p1 Heq_p2
                                      Heq_g_rem
                                  | t' p1' b1' C2
                                       subt'' p2' b2 b0'
                                       g_rem 
                                       Hdecom_p1
                                       Hdecom_p2 Heq_bunion Heq_t Heq_C
                                       Heq_subt Heq_p1 Heq_g_rem
                                  |].
             ** (* sub-pattern pc consumes input *)
                assert(((g1 ⊢ t : p1, remove_prod (n, p)
                                                  g2' b0
                        | b1')
                        <->
                        g1 ⊢ t : p1, g2' | b1')
                       /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p1,
                                               remove_prod (n, p)
                                                           g2' b0
                           | b1')
                           <->
                           g1 ⊢ t ⩦ C [subt]: p1, g2' | b1'))
                 as [_ Heq_decom].
                {assert(pat_grammar_evolution_trans (p1, g2') (p, g2))
                    as Htrans.
                 {eapply t1n_trans.
                  apply pat_grammar_evolution_inhole_left.
                  exact Hproof_in_p'.
                 }

                 assert(pat_grammar_evolution (p1, g2') (inhole p1 p2, g2'))
                   as Hmrel_step.
                 {auto.
                 }
                 
                 apply (IH (p1, g2')
                           Hmrel_step
                           Htrans
                           b0
                           b1').
                }
                rewrite (Heq_decom C1 subt') in Hdecom_p1.
                clear Heq_decom.

                eauto.
             ** (* sub-pattern pc does not consume input *)
                assert(((g1 ⊢ t : p1, remove_prod (n, p)
                                                  g2' b0
                        | b1')
                        <->
                        g1 ⊢ t : p1, g2' | b1')
                       /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p1,
                                               remove_prod (n, p)
                                                           g2' b0
                           | b1')
                           <->
                           g1 ⊢ t ⩦ C [subt]: p1, g2' | b1'))
                 as [_ Heq_decom].
                {assert(pat_grammar_evolution_trans (p1, g2') (p, g2))
                    as Htrans.
                 {eapply t1n_trans.
                  apply pat_grammar_evolution_inhole_left.
                  exact Hproof_in_p'.
                 }

                 assert(pat_grammar_evolution (p1, g2') (inhole p1 p2, g2'))
                   as Hmrel_step.
                 {auto.
                 }
                 apply (IH (p1, g2')
                           Hmrel_step
                           Htrans
                           b0
                           b1').
                }
                rewrite (Heq_decom hole__t t) in Hdecom_p1.
                clear Heq_decom.

                assert(((g1 ⊢ t : p2, remove_prod (n, p)
                                                  g2' b0
                        | b2)
                        <->
                        g1 ⊢ t : p2, g2' | b2)
                       /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p2,
                                               remove_prod (n, p)
                                                           g2' b0
                           | b2)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p2, g2' | b2))
                 as [_ Heq_decom].
                {assert(pat_grammar_evolution_trans (p2, g2') (p, g2))
                    as Htrans.
                 {eapply t1n_trans.
                  apply pat_grammar_evolution_inhole_right.
                  exact Hproof_in_p'.
                 }

                 assert(pat_grammar_evolution (p2, g2') (inhole p1 p2, g2'))
                   as Hmrel_step.
                 {auto.
                 }
                 
                 apply (IH (p2, g2')
                           Hmrel_step
                           Htrans
                           b0
                           b2).
                }
                rewrite (Heq_decom C2 subt) in Hdecom_p2.
                clear Heq_decom.

                rewrite <- Heq_C.
                
                eauto.
          -- (* we can remove a used prod *)
             intro Hdecom.
             inversion Hdecom as [| | | | | | |
                                  |t' C1 subt' p1' b1' C2
                                      subt'' p2' b2 b0'
                                      g_rem 
                                      Hdecom_p1 Hsubterm
                                      Hdecom_p2 Heq_bunion Heq_t Heq_C
                                      Heq_subt Heq_p1 Heq_p2
                                      Heq_g_rem
                                  | t' p1' b1' C2
                                       subt'' p2' b2 b0'
                                       g_rem 
                                       Hdecom_p1
                                       Hdecom_p2 Heq_bunion Heq_t Heq_C
                                       Heq_subt Heq_p1 Heq_g_rem
                                  |].
             ** (* sub-pattern pc consumes input *)
                assert(((g1 ⊢ t : p1, remove_prod (n, p)
                                                  g2' b0
                        | b1')
                        <->
                        g1 ⊢ t : p1, g2' | b1')
                       /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p1,
                                               remove_prod (n, p)
                                                           g2'
                                                           b0
                           | b1')
                           <->
                           g1 ⊢ t ⩦ C [subt]: p1, g2' | b1'))
                 as [_ Heq_decom].
                {assert(pat_grammar_evolution_trans (p1, g2') (p, g2))
                    as Htrans.
                 {eapply t1n_trans.
                  apply pat_grammar_evolution_inhole_left.
                  exact Hproof_in_p'.
                 }

                 assert(pat_grammar_evolution (p1, g2') (inhole p1 p2, g2'))
                   as Hmrel_step.
                 {auto.
                 }
                 
                 apply (IH (p1, g2')
                           Hmrel_step
                           Htrans
                           b0
                           b1').
                }
                rewrite <- (Heq_decom C1 subt') in Hdecom_p1.
                clear Heq_decom.

                eauto.
             ** (* sub-pattern pc does not consume input *)
                assert(((g1 ⊢ t : p1, remove_prod (n, p)
                                                  g2' b0
                        | b1')
                        <->
                        g1 ⊢ t : p1, g2' | b1')
                       /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p1,
                                               remove_prod (n, p)
                                                           g2' b0
                           | b1')
                           <->
                           g1 ⊢ t ⩦ C [subt]: p1, g2' | b1'))
                 as [_ Heq_decom].
                {assert(pat_grammar_evolution_trans (p1, g2') (p, g2))
                    as Htrans.
                 {eapply t1n_trans.
                  apply pat_grammar_evolution_inhole_left.
                  exact Hproof_in_p'.
                 }

                 assert(pat_grammar_evolution (p1, g2') (inhole p1 p2, g2'))
                   as Hmrel_step.
                 {auto.
                 }
                 apply (IH (p1, g2')
                           Hmrel_step
                           Htrans
                           b0
                           b1').
                }
                rewrite <- (Heq_decom hole__t t) in Hdecom_p1.
                clear Heq_decom.

                assert(((g1 ⊢ t : p2, remove_prod (n, p)
                                                  g2' b0
                        | b2)
                        <->
                        g1 ⊢ t : p2, g2' | b2)
                       /\
                       (forall (C : contxt) (subt : term),
                           (g1 ⊢ t ⩦ C [subt]: p2,
                                               remove_prod (n, p)
                                                           g2' b0
                           | b2)
                           <->
                           g1 ⊢ t ⩦ C [subt]: p2, g2' | b2))
                 as [_ Heq_decom].
                {assert(pat_grammar_evolution_trans (p2, g2') (p, g2))
                    as Htrans.
                 {eapply t1n_trans.
                  apply pat_grammar_evolution_inhole_right.
                  exact Hproof_in_p'.
                 }

                 assert(pat_grammar_evolution (p2, g2') (inhole p1 p2, g2'))
                   as Hmrel_step.
                 {auto.
                 }
                 apply (IH (p2, g2')
                           Hmrel_step
                           Htrans
                           b0
                           b2).
                }
                rewrite <- (Heq_decom C2 subt) in Hdecom_p2.
                clear Heq_decom.

                rewrite <- Heq_C.
                
                eauto.
  Qed.

  Lemma subterm_rel_characterization : forall G p G' t C t' b,
      G ⊢ t ⩦ C [t'] : p, G' | b ->
      pt.subterm_rel t' t \/ (t = t' /\ C = hole__t).
  Proof.
    intros G p G' t C t' b H.
    induction H.
    - (* C = hole *)
      auto.
    - (* ct t1 t2 ⩦ (left__t C t2) *)
      inversion IHdecompose_spec as [Hsub | [Heq_t1 Heq_C] ].
      + (* pt.subterm_rel t1' t1 *)
        assert(Hsub_t1 : subterm_rel t1 (ct t1 t2)).
        {eauto using subterm_rel.
        }
        
        assert(Hsubt_trans : subterm_rel t1' (ct t1 t2)).
        {eauto using subterm_trans.
        }

        left.
        exact Hsubt_trans.
      + (* t1 = t1' /\ C = hole__t *)
        subst.
        left.
        eauto using subterm_rel.
    - (* left__t C t2 ⩦ (left__t C' t2) *)
      inversion IHdecompose_spec as [Hsub | [Heq_C Heq_C'] ].
      + (* subterm_rel sub_C (ctxt C) *)
        assert(Hsub_ctxt : subterm_rel (ctxt C) (ctxt hd_c C t2)).
        {eauto using subterm_rel.
        }

        left.
        eauto using subterm_trans.
      + (* ctxt C = sub_C /\ C' = hole__t *)
        subst.
        left.
        eauto using subterm_rel.
    - (* right__t t1 C ⩦ (hd_c C' (cons_term_c C nil_term_c)) *)
      inversion IHdecompose_spec as [Hsub | [Heq_t1 Heq_C'] ].
      + (* pt.subterm_rel t1' t1 *)
        left.
        assert(subterm_rel t1 (ctxt tail_c t1 C)).
        {eauto using subterm_rel.
        }
        eauto using subterm_trans.
      + (* t1 = t1' /\ C' = hole__t *)
        subst.
        left.
        eauto using subterm_rel.
    - (* ct t1 t2 ⩦ (tail_c t1 C) *)
      inversion IHdecompose_spec as [Hsub | [Heq_t2 Heq_C'] ].
      + (* pt.subterm_rel t2' t2 *)
        left.
        assert(subterm_rel t2 (ct t1 t2)).
        {eauto using subterm_rel.
        }
        eauto using subterm_trans.
      + (* t2 = t2' /\ C = hole__t *)
        subst.
        left.
        eauto using subterm_rel.
    - (* hd_c C t2 ⩦ (tail_c C C') *)
      inversion IHdecompose_spec as [Hsub | [Heq_t2 Heq_C'] ].
      + (* pt.subterm_rel t2' t2 *)
        left.
        assert(subterm_rel t2 (ctxt hd_c C t2)).
        {eauto using subterm_rel.
        }
        eauto using subterm_trans.
      + (* t2 = t2' /\ C' = hole__t *)
        subst.
        left.
        eauto using subterm_rel.
    - (* tail_c t1 C ⩦ (tail_c t1 C') *)
      inversion IHdecompose_spec as [Hsub | [Heq_C Heq_C'] ].
      + (* pt.subterm_rel sub_C C *)
        left.
        assert(subterm_rel (ctxt C) (ctxt tail_c t1 C)).
        {eauto using subterm_rel.
        }
        eauto using subterm_trans.
      + (* ctxt C = sub_C /\ C' = hole__t *)
        subst.
        left.
        eauto using subterm_rel.
    - (* nt *)
      inversion IHdecompose_spec as [Hsub | [Heq_t1 Heq_C] ].
      + (* pt.subterm_rel t2 t1 *)
        left.
        auto.
      + (* t1 = t2 /\ C = hole__t *)
        subst.
        auto.
    - (* t ⩦ (context_com C1 C2) *)
      inversion IHdecompose_spec1 as [Hsub_t1 | [Heq_t1 Heq_C1] ].
      + (* pt.subterm_rel t1 t *)
        inversion IHdecompose_spec2 as [Hsub_t2 | [Heq_t2 Heq_C2] ].
        * (* pt.subterm_rel t2 t1 *)
          eauto using subterm_trans.
        * (* t1 = t2 /\ C2 = hole__t *)
          subst.
          left.
          auto.
      + (* t = t1 /\ C1 = hole__t *)
        inversion IHdecompose_spec2 as [Hsub_t2 | [Heq_t2 Heq_C2] ].
        * (* pt.subterm_rel t2 t1 *)
          eauto using subterm_trans.
        * (* t1 = t2 /\ C2 = hole__t *)
          subst.
          left.
          auto.
    - (* t ⩦ (context_com hole__t C2) *)
      inversion IHdecompose_spec1 as [Hsub_t | [Heq_t Heq_hole] ].
      + (* pt.subterm_rel t t *)
        assert(not (subterm_rel t t)).
        {apply subterm_rel_non_reflex.
        }
        contradiction.
      + (* t = t /\ hole__t = hole__t *)
        inversion IHdecompose_spec2 as [Hsub_t2 | [Heq_t2 Heq_C2] ].
        * (* pt.subterm_rel t2 t1 *)
          auto.
        * (* t1 = t2 /\ C2 = hole__t *)
          subst.
          auto.
    - (* name *)
      inversion IHdecompose_spec as [Hsub_t1 | [Heq_t1 Heq_C] ].
      + (* subterm_rel t2 t1 *)
        auto.
      + (* t1 = t2 /\ C = hole__t *)
        auto.
  Qed.

End MatchSpecLemmas.
