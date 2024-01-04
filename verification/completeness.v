Require Import
        Lists.List
        Logic.Eqdep
        (* inj_pair2_eq_dec *)
        Logic.Eqdep_dec
        Program.Equality
        (* Some_inj *)
        ssreflect
        ssr.ssrfun.

Require Export
        patterns_terms_dec
        match_spec_lemmas
        lib_ext.ListExt.

(* completeness of M_ev *)
Module Completeness (pt : PatTermsSymb).
  Import pt.

  Module MatchSpecLemmas := MatchSpecLemmas pt.
  Import MatchSpecLemmas.
  Import MatchImplLemmas.
  Import MatchingSpec.
  Import Matching.
  Import MatchTads.
  Import WfRel.
  Import GrammarLists.
  Import PatTermsDec.

  (* lemmas that capture each case of the proof of completeness *)
  Section Lemmas.

    (* case G |- t : name x p | b’  *)
    Lemma match_name_case :
      forall {p0 : pt.pat}
        (sub_t sub_t' : pt.term)
        (C : contxt)
        {t0 : pt.term}
        {bp b0 : bindings}
        {g g' : grammar}
        {x : pt.var}
        (Hmatch : match_spec g t0 p0 g' bp)
        (H1 : ((x, t0) :: ∅) ⊔ bp = Some b0)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (t0, (name x p0, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t' C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                    (M_ev g (t', (p', G2'))))
            end),
        In (mtch_pair t0 (empty_d_ev t0) b0)
           (M_ev g (t0, (name x p0, g'))).
    Proof.
      intros p0 sub_t sub_t' C t0 bp b0 g g' x Hmatch H1 H.
      (* we show that
            In (mtch_pair t0 (empty_d_ev t0) bp)
               (M_ev (m_rel_e (g, t0) (p0, g'))*)
      rewrite (M_ev_rew_name_case g g' t0 p0 x).

      assert(In (mtch_pair t0 (empty_d_ev t0) bp)
                   (M_ev g (t0, (p0, g'))))
        as Hinpair_inst.
      {assert(matching_tuple_order g
                (t0, (p0, g'))
                (t0, (name x p0, g')))
          as Hname_pat_rel.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t0 p0 g' bp ->
               In (mtch_pair t0 (empty_d_ev t0) bp)
                  (M_ev g (t0, (p0, g')))) /\
              (decompose_spec g t0  C sub_t p0 g' bp ->
               exists ev_decom : {sub_t = t0 /\ C = hole_contxt_c} + {subterm_rel sub_t t0},
                 In
                   (mtch_pair t0 (nonempty_d_ev t0 C sub_t ev_decom) bp)
                   (M_ev g (t0, (p0, g')))))
         as Happ.
       {apply (H (t0, (p0, g'))
                 Hname_pat_rel
                 sub_t bp C).
       }
       inversion Happ as [Hmatch_spec Hdecom].
       apply (Hmatch_spec Hmatch).
      }

      (* now we show the effect of name_case over
            (mtch_pair t0 (empty_d_ev t0) bp) *)

      assert(exists l1 l2, M_ev g (t0, (p0, g')) = l1 ++ (mtch_pair t0 (empty_d_ev t0) bp) :: l2)
        as Hrec_set_split.
      {apply in_split.
       
       exact Hinpair_inst.
      }
      inversion Hrec_set_split as [l1 Hrec_set_split'].
      clear Hrec_set_split.
      inversion Hrec_set_split' as [l2 Hrec_set_split''].
      clear Hrec_set_split'.

      assert(name_case t0 (l1 ++ mtch_pair t0 (empty_d_ev t0) bp :: l2) x
             = (name_case t0 l1 x) ++
                 (name_case t0 (mtch_pair t0 (empty_d_ev t0) bp :: l2) x))
        as Hname_case_eq.
      {apply (name_case_concat t0 l1
                               (mtch_pair t0 (empty_d_ev t0) bp :: l2)
                               x).
      }

      rewrite <- Hrec_set_split'' in Hname_case_eq.
      clear Hrec_set_split''.
      rewrite Hname_case_eq.
      clear Hname_case_eq.
      remember (name_case t0 l1 x) as l1'.
      remember (name_case t0 (mtch_pair t0 (empty_d_ev t0) bp :: l2) x)
        as l2'.
      remember (mtch_pair t0 (empty_d_ev t0) b0) as elem.
      rewrite in_app_iff.
      right.
      clear Heql1' l1 l1'.
      simpl in Heql2'.
      simpl in H1.

      remember (bindings_app (rem_rep bp) x) as bind_app_bp_x.
      destruct bind_app_bp_x as [t' |].
      - (* (bindings_app (rem_rep bp) x) = Some t *)
        remember (MatchTads.PatTermsDec.term_eq_dec t0 t')
          as term_eq_dec_t0_t' eqn: Heq_term_eq_dec_t0_t'.
        destruct term_eq_dec_t0_t' as [Heq_t0_t' | Hneq_t0_t'].
        + (* t0 = t' *)
          rewrite Heql2'.
          rewrite Heqelem.
          inversion H1.
          rewrite H2.
          apply in_eq.
        + (* t0 <> t' *)
          inversion H1.
      - (* (bindings_app (rem_rep bp) x) <> Some t *)
        rewrite Heql2'.
        rewrite Heqelem.
        inversion H1.
        rewrite H2.
        apply in_eq.
    Qed.


    Lemma match_nt_case :
      forall (p0 : pt.pat)
        (t0 sub_t sub_t' : pt.term)
        (b0 : bindings)
        (C C' : pt.contxt)
        (g g' : grammar)
        (n : pt.nonterm)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (t0, (nt n, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t' C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                    (M_ev g (t', (p', G2'))))
            end)
        (proof : prod_in_g (n, p0) g')
        (Hmatch : match_spec g t0 p0 (remove_prod (n, p0) g' proof) b0),
        In (mtch_pair t0 (empty_d_ev t0) ∅)
           (M_ev g (t0, (nt n, g'))).
    Proof.
      intros p0 t0 sub_t sub_t' b0 C C' g g' n H proof Hmatch.

      (* inspect content of the recursive call *)
      assert(matching_tuple_order g
               (t0, (p0, remove_prod (n, p0) g' proof))
               (t0, (nt n, g')))
        as Hnt_rel.
      {matching_tuple_order_build_ev.
      }

      assert(In (mtch_pair t0 (empty_d_ev t0) b0)
                (M_ev g (t0, (p0, remove_prod (n, p0) g' proof))))
        as IH.
      {assert((match_spec g t0 p0 (remove_prod (n, p0) g' proof) b0 ->
               In (mtch_pair t0 (empty_d_ev t0) b0)
                  (M_ev g (t0, (p0, (remove_prod (n, p0) g' proof))))) /\
              (decompose_spec g t0 C sub_t p0 (remove_prod (n, p0) g' proof) b0 ->
               exists ev_decom : {sub_t = t0 /\ C = hole_contxt_c} + {subterm_rel sub_t t0},
                 In
                   (mtch_pair t0 (nonempty_d_ev t0 C sub_t ev_decom) b0)
                   (M_ev g (t0, (p0, (remove_prod (n, p0) g' proof))))))
          as Happ.
       {apply (H (t0, (p0, remove_prod (n, p0) g' proof))
                 Hnt_rel
                 sub_t b0 C).
       }
       inversion Happ as [Hmatch_spec Hdecom].

       apply (Hmatch_spec Hmatch).
      }

      (* rewrite call to M_ev nt n *)
      rewrite (M_ev_rew_nt_case g g' t0 n).
      unfold nt_case.
      assert(exists (proof' : prod_in_g (n, p0) g') G1' G1'',
                get_rhs g' n = G1' ++ ((exist (fun pa =>
                                                 prod_in_g (n, pa) g')
                                              p0
                                              proof') :: nil) ++ G1'')
        as lemma_get_rhs.
      {apply (get_rhs_split g' p0 n proof).
      }
      inversion lemma_get_rhs as [proof' Hget'].
      inversion Hget' as [G1' Hget''].
      inversion Hget'' as [G1'' Hget'''].
      rewrite Hget'''.
      rewrite map_app.
      rewrite map_app.
      rewrite fold_left_app.
      rewrite fold_left_fapp.
      rewrite in_app_iff.
      right.
      simpl.
      rewrite fold_left_fapp.
      rewrite in_app_iff.
      left.

      assert(exists l1 l2, M_ev g (t0, (p0, remove_prod (n, p0) g' proof'))
                      =
                      l1 ++ (mtch_pair t0 (empty_d_ev t0) b0) :: l2)
        as Hin.
      {apply in_split.
       exact IH.
      }
      inversion Hin as [l1 Hin'].
      clear Hin.
      clear IH.
      inversion Hin' as [l2 Hin''].
      clear Hin'.
      rewrite Hin''.
      rewrite map_app.
      rewrite in_app_iff.
      right.
      rewrite map_cons.
      apply in_eq.
    Qed.

    (* case G |- ct t1 t2 : cp p1 p2  | b *)
    Lemma match_cons_case :
      forall (p1 : pt.pat)
        (p2 : list_pat)
        (sub_t sub_t' : pt.term)
        (b1 b2 b0 : bindings)
        (C C' : pt.contxt)
        (g g' : grammar)
        (t1 : pt.term)
        (t2 : list_term)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (ct t1 t2, (cp p1 p2, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t' C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                    (M_ev g (t', (p', G2'))))
            end)
        (Hmatch1 : match_spec g t1 p1 g b1)
        (Hmatch2 : match_spec g t2 p2 g b2)
        (H2 : b_union b1 b2 = Some b0),
        In (mtch_pair (ct t1 t2) (empty_d_ev (ct t1 t2)) b0)
           (M_ev g (ct t1 t2, (cp p1 p2, g'))).
    Proof.
      intros p1 p2 sub_t sub_t' b1 b2 b0 C C' g g' t1 t2 H
             Hmatch1 Hmatch2 H2.

      (* express M_ev in terms of function cons_case *)
      assert(M_ev g (ct t1 t2, (cp p1 p2, g'))
             =
               cons_case (ct t1 t2) t1 t2 (build_subterm_proof t1 t2)
                 (M_ev g (t1, (p1, g)))
                 (M_ev g (list_term_c t2, (list_pat_c p2, g))))
        as Hrec_call.
      {apply M_ev_rew_cons_case.
      }

      (* inspect content of recursive calls *)
      assert(In (mtch_pair t1 (empty_d_ev t1) b1)
                (M_ev g (t1, (p1, g))))
        as Hin_t1.
      {assert(matching_tuple_order g
                (t1, (p1, g))
                (ct t1 t2, (cp p1 p2, g')))
          as Hmrel_t1.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t1 p1 g b1 ->
               In (mtch_pair t1 (empty_d_ev t1) b1)
                  (M_ev g (t1, (p1, g)))) /\
              (decompose_spec g t1 C sub_t p1 g b1 ->
               exists ev_decom : {sub_t = t1 /\ C = hole_contxt_c} + {subterm_rel sub_t t1},
                 In
                   (mtch_pair t1 (nonempty_d_ev t1 C sub_t ev_decom) b1)
                   (M_ev g (t1, (p1, g)))))
         as Happ.
       {
        apply (H (t1, (p1, g))
                 Hmrel_t1
                 sub_t b1 C).
       }
       inversion Happ as [Hmatch_spec Hdecom].

       apply (Hmatch_spec Hmatch1).
      }
      assert(exists l1_t1 l2_t1,
                M_ev g (t1, (p1, g)) =
                l1_t1 ++ (mtch_pair t1 (empty_d_ev t1) b1) :: l2_t1)
        as Hsplit_t1.
      {apply (in_split _ _ Hin_t1).
      }
      inversion Hsplit_t1 as [l1_t1 Hsplit_t1'].
      clear Hsplit_t1.
      inversion Hsplit_t1' as [l2_t1 Hsplit_t1''].
      clear Hsplit_t1'.
      clear Hin_t1.

      assert(In (mtch_pair t2 (empty_d_ev t2) b2)
                (M_ev g (list_term_c t2, (list_pat_c p2, g))))
        as Hin_t2.
      {assert(matching_tuple_order g
                (list_term_c t2, (list_pat_c p2, g))
                (ct t1 t2, (cp p1 p2, g')))
          as Hmrel_t2.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t2 p2 g b2 ->
               In (mtch_pair t2 (empty_d_ev t2) b2)
                  (M_ev g (list_term_c t2, (list_pat_c p2, g)))) /\
              (decompose_spec g t2 C sub_t p2 g b2 ->
               exists ev_decom : {sub_t = t2 /\ C = hole_contxt_c} + {subterm_rel sub_t t2},
                 In
                   (mtch_pair t2 (nonempty_d_ev t2 C sub_t ev_decom) b2)
                   (M_ev g (list_term_c t2, (list_pat_c p2, g)))))
         as Happ.
       {apply (H (list_term_c t2, (list_pat_c p2, g))
                 Hmrel_t2
                 sub_t b2 C).
       }
       inversion Happ as [Hmatch_spec Hdecom].


       apply (Hmatch_spec Hmatch2).
      }

      assert(exists l1_t2 l2_t2,
                M_ev g (list_term_c t2, (list_pat_c p2, g)) =
                l1_t2 ++ (mtch_pair t2 (empty_d_ev t2) b2) :: l2_t2)
        as Hsplit_t2.
      {apply (in_split _ _ Hin_t2).
      }

      inversion Hsplit_t2 as [l1_t2 Hsplit_t2'].
      clear Hsplit_t2.
      inversion Hsplit_t2' as [l2_t2 Hsplit_t2''].
      clear Hsplit_t2'.
      clear Hin_t2.

      rewrite Hsplit_t1'' in Hrec_call.
      clear Hsplit_t1''.
      rewrite Hsplit_t2'' in Hrec_call.
      clear Hsplit_t2''.

      (* compute with cons_case over the mtch_pairs of interest *)
      rewrite cons_case_dist in Hrec_call.

      assert(exists res : mtch_powset_ev (ct t1 t2),
                cons_case (ct t1 t2) t1 t2 (build_subterm_proof t1 t2)
                          (mtch_pair t1 (empty_d_ev t1) b1 :: l2_t1)
                          (l1_t2 ++ mtch_pair t2 (empty_d_ev t2) b2 :: l2_t2)
                =
                res ++
                    cons_case_aux (ct t1 t2) t1 t2 (build_subterm_proof t1 t2)
                    (mtch_pair t1 (empty_d_ev t1) b1)
                    (mtch_pair t2 (empty_d_ev t2) b2 :: l2_t2) ++
                    cons_case (ct t1 t2) t1 t2 (build_subterm_proof t1 t2) l2_t1
                    (l1_t2 ++ mtch_pair t2 (empty_d_ev t2)
                           b2 :: l2_t2))
        as Hcons_case_dist_unfold.
      {apply cons_case_dist_unfold.
      }

      inversion Hcons_case_dist_unfold as [res Hcons_case_dist_unfold'].
      clear Hcons_case_dist_unfold.
      rewrite Hcons_case_dist_unfold' in Hrec_call.
      clear Hcons_case_dist_unfold'.

      rewrite Hrec_call.
      rewrite in_app_iff.
      right.
      rewrite in_app_iff.
      right.
      rewrite in_app_iff.
      left.

      simpl.
      rewrite H2.
      apply in_eq.
    Qed.

    (* case G |- ctxt (lc C0 t2) : cp p1 p2  | b *)
    Lemma match_hd_contxt_case :
      forall (p1 : pt.pat)
        (p2 : list_pat)
        (sub_t sub_t' : pt.term)
        (t2 : list_term)
        (b0 b1 b2 : bindings)
        (C C0 C' : pt.contxt)
        (g g' : grammar)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (ctxt (hd_contxt C0 t2), (cp p1 p2, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                 (M_ev g (t', (p', G2')))) /\
                (decompose_spec g t' C' sub_t' p' G2' b' ->
                 exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                   In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                     (M_ev g (t', (p', G2'))))
            end)
        (Hmatch1 : match_spec g (ctxt C0) p1 g b1)
        (Hmatch2 : match_spec g t2 p2 g b2)
        (H2 : b_union b1 b2 = Some b0),
        In (mtch_pair (ctxt (hd_contxt C0 t2)) (empty_d_ev (ctxt (hd_contxt C0 t2))) b0)
          (M_ev g (ctxt (hd_contxt C0 t2), (cp p1 p2, g'))).
    Proof.
      intros p1 p2 sub_t sub_t' t2 b0 b1 b2 C C0 C' g g' H
        Hmatch1 Hmatch2 H2.

      (* express M_ev in terms of function cons_case *)
      assert(exists (proof_subt : subterms (ctxt (hd_contxt C0 t2))
                                           (ctxt C0)
                                           t2),
                M_ev g (ctxt (hd_contxt C0 t2), (cp p1 p2, g'))
                =
                (cons_case (ctxt (hd_contxt C0 t2)) (ctxt C0) t2 proof_subt
                           (M_ev g (ctxt C0, (p1, g)))
                           (M_ev g (list_term_c t2, (list_pat_c p2, g)))))
        as Hrec_call.
      {apply M_ev_rew_cons_case_hd_ctxt.
      }
      inversion Hrec_call as [proof_subt Hrec_call'].
      clear Hrec_call.

      (* inspect content of recursive calls *)
      assert(In (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b1)
                (M_ev g (ctxt C0, (p1, g))))
        as Hin_ctxt_C0.
      {assert(matching_tuple_order g
                (ctxt C0, (p1, g))
                (ctxt (hd_contxt C0 t2), (cp p1 p2, g')))
          as Hmrel_ctxt_C0.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g (ctxt C0) p1 g b1 ->
               In (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b1)
                  (M_ev g (ctxt C0, (p1, g)))) /\
              (decompose_spec g (ctxt C0) C sub_t p1 g b1 ->
               exists ev_decom : {sub_t = (ctxt C0) /\ C = hole_contxt_c} + {subterm_rel sub_t (ctxt C0)},
                 In
                   (mtch_pair (ctxt C0) (nonempty_d_ev (ctxt C0) C sub_t ev_decom) b1)
                   (M_ev g (ctxt C0, (p1, g)))))
         as Happ.
       {apply (H (ctxt C0, (p1, g))
                 Hmrel_ctxt_C0
                 sub_t b1 C).
       }
       inversion Happ as [Hmatch_spec Hdecom].

       apply (Hmatch_spec Hmatch1).
      }
      assert(exists l1_t1' l2_t1',
                M_ev g (ctxt C0, (p1, g)) =
                l1_t1'
                  ++
                  (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b1) :: l2_t1')
        as Hsplit_ctxt_C0.
      {apply (in_split _ _ Hin_ctxt_C0).
      }
      inversion Hsplit_ctxt_C0 as [l1_t1' Hsplit_ctxt_C0'].
      clear Hsplit_ctxt_C0.
      inversion Hsplit_ctxt_C0' as [l2_t1' Hsplit_ctxt_C0''].
      clear Hsplit_ctxt_C0'.
      clear Hin_ctxt_C0.

      assert(In (mtch_pair t2 (empty_d_ev t2) b2)
                (M_ev g (list_term_c t2, (list_pat_c p2, g))))
        as Hin_t2.
      {assert(matching_tuple_order g
                (list_term_c t2, (list_pat_c p2, g))
                (ctxt (hd_contxt C0 t2), (cp p1 p2, g')))
          as Hmrel_t2.
       {matching_tuple_order_build_ev.
       }


       assert((match_spec g t2 p2 g b2 ->
               In (mtch_pair t2 (empty_d_ev t2) b2)
                  (M_ev g (list_term_c t2, (list_pat_c p2, g)))) /\
              (decompose_spec g t2 C sub_t p2 g b2 ->
               exists ev_decom : {sub_t = t2 /\ C = hole_contxt_c} + {subterm_rel sub_t t2},
                 In
                   (mtch_pair t2 (nonempty_d_ev t2 C sub_t ev_decom) b2)
                   (M_ev g (list_term_c t2, (list_pat_c p2, g)))))
         as Happ.
       {apply (H (list_term_c t2, (list_pat_c p2, g))
                 Hmrel_t2
                 sub_t b2 C).
       }
       inversion Happ as [Hmatch_spec Hdecom].


       apply (Hmatch_spec Hmatch2).
      }
      
      assert(exists l1_t2 l2_t2,
                M_ev g (list_term_c t2, (list_pat_c p2, g)) =
                l1_t2 ++ (mtch_pair t2 (empty_d_ev t2) b2) :: l2_t2)
        as Hsplit_t2.
      {apply (in_split _ _ Hin_t2).
      }
      inversion Hsplit_t2 as [l1_t2 Hsplit_t2'].
      clear Hsplit_t2.
      inversion Hsplit_t2' as [l2_t2 Hsplit_t2''].
      clear Hsplit_t2'.
      clear Hin_t2.

      rewrite Hsplit_ctxt_C0'' in Hrec_call'.
      clear Hsplit_ctxt_C0''.
      rewrite Hsplit_t2'' in Hrec_call'.
      clear Hsplit_t2''.

      (* compute with cons_case over the mtch_pairs of interest *)
      rewrite cons_case_dist in Hrec_call'.

      assert(exists res : mtch_powset_ev (ctxt (hd_contxt C0 t2)),
                cons_case (ctxt (hd_contxt C0 t2)) (ctxt C0) t2 proof_subt
                          (mtch_pair (ctxt C0)
                                     (empty_d_ev (ctxt C0)) b1 :: l2_t1')
                          (l1_t2 ++ mtch_pair t2 (empty_d_ev t2) b2 :: l2_t2)
                =
                res ++
                    cons_case_aux (ctxt (hd_contxt C0 t2)) (ctxt C0) t2 proof_subt
                    (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b1)
                    (mtch_pair t2 (empty_d_ev t2) b2 :: l2_t2) ++
                    cons_case (ctxt (hd_contxt C0 t2)) (ctxt C0) t2 proof_subt l2_t1'
                    (l1_t2 ++ mtch_pair t2 (empty_d_ev t2)
                           b2 :: l2_t2))
        as Hcons_case_dist_unfold.
      {apply cons_case_dist_unfold.
      }
      inversion Hcons_case_dist_unfold as [res Hcons_case_dist_unfold'].
      clear Hcons_case_dist_unfold.
      rewrite Hcons_case_dist_unfold' in Hrec_call'.
      clear Hcons_case_dist_unfold'.

      rewrite Hrec_call'.
      rewrite in_app_iff.
      right.
      rewrite in_app_iff.
      right.
      rewrite in_app_iff.
      left.

      simpl.
      rewrite H2.
      apply in_eq.
    Qed.

    (* case G |- ctxt (rc t2 C0) : cp p1 p2  | b *)
    Lemma match_tail_contxt_case :
      forall (p1 : pt.pat)
        (p2 : list_pat)
        (sub_t t1 sub_t' : pt.term)
        (b0 b1 b2 : bindings)
        (C C' : pt.contxt)
        (C0 : list_contxt)
        (g g' : grammar)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (ctxt (tail_contxt t1 C0), (cp p1 p2, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t' C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                    (M_ev g (t', (p', G2'))))
            end)
        (Hmatch1 : match_spec g t1 p1 g b1)
        (Hmatch2 : match_spec g (ctxt C0) p2 g b2)
        (H2 : b_union b1 b2 = Some b0),
        In (mtch_pair (ctxt (tail_contxt t1 C0)) (empty_d_ev (ctxt (tail_contxt t1 C0))) b0)
           (M_ev g (ctxt (tail_contxt t1 C0), (cp p1 p2, g'))).
    Proof.
      intros p1 p2 sub_t t1 sub_t' b0 b1 b2 C C' C0 g g' H
          Hmatch1 Hmatch2 H2.

      (* express M_ev in terms of function cons_case *)
      assert(exists (proof_subt : subterms (ctxt (tail_contxt t1 C0)) t1 (ctxt C0)),
                M_ev g (ctxt (tail_contxt t1 C0), (cp p1 p2, g'))
                =
                (cons_case (ctxt (tail_contxt t1 C0)) t1 (ctxt C0) proof_subt
                           (M_ev g (t1, (p1, g)))
                           (M_ev g (ctxt C0, (list_pat_c p2, g)))))
        as Hrec_call.
      {apply M_ev_rew_cons_case_tail_ctxt.
      }
      inversion Hrec_call as [proof_subt Hrec_call'].
      clear Hrec_call.

      (* inspect content of recursive calls *)
      assert(In (mtch_pair t1 (empty_d_ev t1) b1)
                (M_ev g (t1, (p1, g))))
        as Hin_t1.
      {assert(matching_tuple_order g
                (t1, (p1, g))
                (ctxt (tail_contxt t1 C0), (cp p1 p2, g')))
          as Hmrel_t1.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t1 p1 g b1 ->
               In (mtch_pair t1 (empty_d_ev t1) b1)
                  (M_ev g (t1, (p1, g)))) /\
              (decompose_spec g t1 C sub_t p1 g b1 ->
               exists ev_decom : {sub_t = t1 /\ C = hole_contxt_c} + {subterm_rel sub_t t1},
                 In
                   (mtch_pair t1 (nonempty_d_ev t1 C sub_t ev_decom) b1)
                   (M_ev g (t1, (p1, g)))))
         as Happ.
       {apply (H (t1, (p1, g))
                 Hmrel_t1
                 sub_t b1 C).
       }
       inversion Happ as [Hmatch_spec Hdecom].

       apply (Hmatch_spec Hmatch1).
      }

      assert(exists l1_t1' l2_t1',
                M_ev g (t1, (p1, g)) =
                l1_t1'
                  ++
                  (mtch_pair t1 (empty_d_ev t1) b1) :: l2_t1')
        as Hsplit_t1.
      {apply (in_split _ _ Hin_t1).
      }
      inversion Hsplit_t1 as [l1_t1' Hsplit_t1'].
      clear Hsplit_t1.
      inversion Hsplit_t1' as [l2_t1' Hsplit_t1''].
      clear Hsplit_t1'.
      clear Hin_t1.

      assert(In (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b2)
                (M_ev g (ctxt C0, (list_pat_c p2, g))))
        as Hin_ctxt_C0.
      {assert(matching_tuple_order g
                (ctxt C0, (list_pat_c p2, g))
                (ctxt (tail_contxt t1 C0), (cp p1 p2, g')))
          as Hmrel_ctxt_C0.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g (ctxt C0) p2 g b2 ->
               In (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b2)
                  (M_ev g (ctxt C0, (list_pat_c p2, g)))) /\
              (decompose_spec g (ctxt C0) C sub_t p2 g b2 ->
               exists ev_decom : {sub_t = ctxt C0 /\ C = hole_contxt_c} + {subterm_rel sub_t (ctxt C0)},
                 In
                   (mtch_pair (ctxt C0)
                              (nonempty_d_ev (ctxt C0) C sub_t ev_decom) b2)
                   (M_ev g (ctxt C0, (list_pat_c p2, g)))))
         as Happ.
       {apply (H (ctxt C0, (list_pat_c p2, g))
                 Hmrel_ctxt_C0
                 sub_t b2 C).
       }
       inversion Happ as [Hmatch_spec Hdecom].

       apply (Hmatch_spec Hmatch2).
      }
      assert(exists l1_t2 l2_t2,
                M_ev g (ctxt C0, (list_pat_c p2, g)) =
                l1_t2 ++ (mtch_pair (ctxt C0)
                                    (empty_d_ev (ctxt C0)) b2) :: l2_t2)
        as Hsplit_ctxt_C0.
      {apply (in_split _ _ Hin_ctxt_C0).
      }
      inversion Hsplit_ctxt_C0 as [l1_t2 Hsplit_ctxt_C0'].
      clear Hsplit_ctxt_C0.
      inversion Hsplit_ctxt_C0' as [l2_t2 Hsplit_ctxt_C0''].
      clear Hsplit_ctxt_C0'.
      clear Hin_ctxt_C0.

      rewrite Hsplit_t1'' in Hrec_call'.
      clear Hsplit_t1''.
      rewrite Hsplit_ctxt_C0'' in Hrec_call'.
      clear Hsplit_ctxt_C0''.

      (* compute with cons_case over the mtch_pairs of interest *)
      rewrite cons_case_dist in Hrec_call'.

      assert(exists res : mtch_powset_ev (ctxt (tail_contxt t1 C0)),
                cons_case (ctxt (tail_contxt t1 C0)) t1 (ctxt C0) proof_subt
                          (mtch_pair t1
                                     (empty_d_ev t1) b1 :: l2_t1')
                          (l1_t2 ++ mtch_pair (ctxt C0)
                                 (empty_d_ev (ctxt C0)) b2 :: l2_t2)
                =
                res ++
                    cons_case_aux (ctxt (tail_contxt t1 C0)) t1 (ctxt C0) proof_subt
                    (mtch_pair t1 (empty_d_ev t1) b1)
                    (mtch_pair (ctxt C0)
                               (empty_d_ev (ctxt C0)) b2 :: l2_t2) ++
                    cons_case (ctxt (tail_contxt t1 C0)) t1 (ctxt C0) proof_subt l2_t1'
                    (l1_t2
                       ++ mtch_pair (ctxt C0) (empty_d_ev (ctxt C0))
                       b2 :: l2_t2))
        as Hcons_case_dist_unfold.
      {apply cons_case_dist_unfold.
      }
      inversion Hcons_case_dist_unfold as [res Hcons_case_dist_unfold'].
      clear Hcons_case_dist_unfold.
      rewrite Hcons_case_dist_unfold' in Hrec_call'.
      clear Hcons_case_dist_unfold'.

      rewrite Hrec_call'.
      rewrite in_app_iff.
      right.
      rewrite in_app_iff.
      right.
      rewrite in_app_iff.
      left.

      simpl.
      rewrite H2.
      apply in_eq.
    Qed.

    (* case G |- t : in-hole p1 p2  | b *)
    Lemma match_inhole_case_inp_cons :
      forall (p1 p2 : pt.pat)
        (sub_t t1 sub_t' t2 : pt.term)
        (b0 b1 b2 : bindings)
        (C C' C0 : pt.contxt)
        (g g' : grammar)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (t1, (inhole_pat p1 p2, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t' C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                    (M_ev g (t', (p', G2'))))
            end)
        (H1 : decompose_spec g t1 C0 t2 p1 g' b1)
        (H2 : pt.subterm_rel t2 t1)
        (Hmatch : match_spec g t2 p2 g b2)
        (H3 : b_union b1 b2 = Some b0),
        In (mtch_pair t1 (empty_d_ev t1) b0)
           (M_ev g (t1, (inhole_pat p1 p2, g'))).
    Proof.
      intros p1 p2 sub_t t1 sub_t' t2 b0 b1 b2 C C' C0 g g' H H1
             H2 Hmatch H3.
      (* unfold and simplify call *)
      assert(M_ev g (t1, (inhole_pat p1 p2, g'))
             =
             inhole_case t1 p1 p2 g g'
               (fun (tpg2 : matching_tuple)
                  (_ : matching_tuple_order g tpg2 (t1, (inhole_pat p1 p2, g')))
                => M_ev g tpg2))
        as Hcall.
      {apply M_ev_rew_inhole_case.
      }
      rewrite Hcall.


      (* inspect content of rec. call *)
      assert(exists ev_decom : {t2 = t1 /\ C0 = hole_contxt_c} + {subterm_rel t2 t1},
                In (mtch_pair t1 (nonempty_d_ev t1 C0 t2 ev_decom) b1)
                   (M_ev g (t1, (p1, g'))))
        as Hrec_call.
      {assert(matching_tuple_order g
                (t1, (p1, g'))
                (t1, (inhole_pat p1 p2, g')))
          as Hmrel_p1.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t1 p1 g' b1 ->
               In (mtch_pair t1 (empty_d_ev t1) b1)
                  (M_ev g (t1, (p1, g')))) /\
              (decompose_spec g t1 C0 t2 p1 g' b1 ->
               exists ev_decom : {t2 = t1 /\ C0 = hole_contxt_c} + {subterm_rel t2 t1},
                 In
                   (mtch_pair t1 (nonempty_d_ev t1 C0 t2 ev_decom) b1)
                   (M_ev g (t1, (p1, g')))))
         as Happ.
       {apply (H (t1, (p1, g'))
                 Hmrel_p1
                 t2 b1 C0).
       }
       inversion Happ as [Hmatch_spec Hdecom].

       apply (Hdecom H1).
      }

      inversion Hrec_call as [ev_decom Hrec_call'].
      clear Hrec_call.

      assert(exists mp1 mp2 : mtch_powset_ev t1,
                M_ev g (t1, (p1, g'))
                =
                mp1 ++ (mtch_pair t1 (nonempty_d_ev t1 C0 t2 ev_decom) b1) :: mp2)
        as Hsplit_rec_call.
      {apply (in_split (mtch_pair t1 (nonempty_d_ev t1 C0 t2 ev_decom) b1)
                       (M_ev g (t1, (p1, g')))
                       Hrec_call').
      }

      inversion Hsplit_rec_call as [mp1 Hsplit_rec_call'].
      clear Hsplit_rec_call.
      inversion Hsplit_rec_call' as [mp2 Hsplit_rec_call''].
      clear Hsplit_rec_call'.

      unfold inhole_case.
      rewrite Hsplit_rec_call''.
      clear Hsplit_rec_call''.

      (* distribute map application *)
      rewrite map_app.
      rewrite map_cons.
      simpl.
      rewrite fold_left_app.
      rewrite fold_left_fapp.
      rewrite in_app_iff.
      right.
      destruct ev_decom as [ [Heq Heq_c] | Hsubterm].
      ++ (* ev_decom = refl, no decomposition or hole context in first rec  *)
         (*                call; contradiction *)
         rewrite Heq in H2.
         assert(not (subterm_rel t1 t1))
           as Hnot_refl.
         {apply subterm_rel_non_reflex.
         }
         contradiction.
        
      ++ (* ev_decom = subterm t2 t1 *)
         simpl.

         (* inspect content of right rec. call *)
         assert(In (mtch_pair t2 (empty_d_ev t2) b2)
                   (M_ev g (t2, (p2, g))))
           as Hin_p2.
         {assert(matching_tuple_order g
                   (t2, (p2, g))
                   (t1, (inhole_pat p1 p2, g')))
             as Hmrel_p2.
           {matching_tuple_order_build_ev.
           }

           assert((match_spec g t2 p2 g b2 ->
                   In (mtch_pair t2 (empty_d_ev t2) b2)
                      (M_ev g (t2, (p2, g)))) /\
                  (decompose_spec g t2 C0 t2 p2 g b2 ->
                   exists ev_decom : {t2 = t2 /\ C0 = hole_contxt_c} + {subterm_rel t2 t2},
                     In
                       (mtch_pair t2
                                  (nonempty_d_ev t2 C0 t2 ev_decom) b2)
                       (M_ev g (t2, (p2, g)))))
             as Happ.
           {apply (H (t2, (p2, g))
                     Hmrel_p2
                     t2 b2 C0).
           }
           inversion Happ as [Hmatch_spec Hdecom].
           apply (Hmatch_spec Hmatch).
          }

          assert(exists mp1' mp2' : mtch_powset_ev t2,
                    M_ev g (t2, (p2, g))
                    =
                    mp1' ++ (mtch_pair t2 (empty_d_ev t2) b2) :: mp2')
            as Hsplit_p2.
          {apply (in_split (mtch_pair t2 (empty_d_ev t2) b2)
                           (M_ev g (t2, (p2, g)))
                           Hin_p2).
          }
          inversion Hsplit_p2 as [mp1' Hsplit_p2'].
          clear Hsplit_p2.
          inversion Hsplit_p2' as [mp2' Hsplit_p2''].
          
          rewrite Hsplit_p2''.
          clear Hsplit_p2'.
          clear Hsplit_p2''.

          rewrite map_app.
          rewrite fold_left_app.
          rewrite fold_left_fapp.
          simpl.
          rewrite H3.
          rewrite fold_left_fapp.
          rewrite <- app_assoc.
          rewrite in_app_iff.
          left.
          rewrite in_app_iff.
          right.
          apply in_eq.
    Qed.

    Lemma match_inhole_case_noinp_cons :
      forall (p1 p2 : pt.pat)
        (t1 : pt.term)
        (b0 b1 b2 : bindings)
        (g g' : grammar)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (t1, (inhole_pat p1 p2, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t' C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                    (M_ev g (t', (p', G2'))))
            end)
        (H1 : decompose_spec g t1 hole_contxt_c t1 p1 g' b1)
        (Hmatch : match_spec g t1 p2 g' b2)
        (H3 : b_union b1 b2 = Some b0),
        In (mtch_pair t1 (empty_d_ev t1) b0)
           (M_ev g (t1, (inhole_pat p1 p2, g'))).
    Proof.
      intros p1 p2 t1 b0 b1 b2 g g' H H1 Hmatch H3.
      (* unfold and simplify call *)
      assert(M_ev g (t1, (inhole_pat p1 p2, g'))
             =
             inhole_case t1 p1 p2 g g'
                         (fun (tpg2 : matching_tuple)
                              (_ : matching_tuple_order g
                                     tpg2 (t1, (inhole_pat p1 p2, g')))
                          => M_ev g tpg2))
        as Hcall.
      {apply M_ev_rew_inhole_case.
      }
      rewrite Hcall.


      (* inspect content of rec. call *)
      assert(exists ev_decom : {t1 = t1 /\ hole_contxt_c = hole_contxt_c} + {subterm_rel t1 t1},
                In (mtch_pair t1 (nonempty_d_ev t1 hole_contxt_c t1 ev_decom)
                              b1)
                   (M_ev g (t1, (p1, g'))))
        as Hrec_call.
      {assert(matching_tuple_order g
                (t1, (p1, g'))
                (t1, (inhole_pat p1 p2, g')))
          as Hmrel_p1.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t1 p1 g' b1 ->
               In (mtch_pair t1 (empty_d_ev t1) b1)
                  (M_ev g (t1, (p1, g')))) /\
              (decompose_spec g t1 hole_contxt_c t1 p1 g' b1 ->
               exists ev_decom : {t1 = t1 /\ hole_contxt_c = hole_contxt_c} + {subterm_rel t1 t1},
                 In
                   (mtch_pair t1 (nonempty_d_ev t1 hole_contxt_c t1 ev_decom) b1)
                   (M_ev g (t1, (p1, g')))))
         as Happ.
       {apply (H (t1, (p1, g'))
                 Hmrel_p1
                 t1 b1 hole_contxt_c).
       }
       inversion Happ as [Hmatch_spec Hdecom].

       apply (Hdecom H1).
      }

      inversion Hrec_call as [ev_decom Hrec_call'].
      clear Hrec_call.

      assert(exists mp1 mp2 : mtch_powset_ev t1,
                M_ev g (t1, (p1, g'))
                =
                mp1
                  ++
                  (mtch_pair t1 (nonempty_d_ev t1 hole__t t1 ev_decom) b1) ::
                  mp2)
        as Hsplit_rec_call.
      {apply (in_split (mtch_pair t1 (nonempty_d_ev t1 hole__t t1 ev_decom) b1)
                       (M_ev g (t1, (p1, g')))
                       Hrec_call').
      }

      inversion Hsplit_rec_call as [mp1 Hsplit_rec_call'].
      clear Hsplit_rec_call.
      inversion Hsplit_rec_call' as [mp2 Hsplit_rec_call''].
      clear Hsplit_rec_call'.

      unfold inhole_case.
      rewrite Hsplit_rec_call''.
      clear Hsplit_rec_call''.

      (* distribute map application *)
      rewrite map_app.
      rewrite map_cons.
      simpl.
      rewrite fold_left_app.
      rewrite fold_left_fapp.
      rewrite in_app_iff.
      right.
      destruct ev_decom as [ [Heq Heq_C] | Hsubterm].
      ++ (* ev_decom = refl, no decomposition or hole context in first rec  *)
        (*                call *)
        simpl.

        (* inspect content of right rec. call *)
        assert(In (mtch_pair t1 (empty_d_ev t1) b2)
                  (M_ev g (t1, (p2, g'))))
          as Hin_p2.
        {assert(matching_tuple_order g
                  (t1, (p2, g'))
                  (t1, (inhole_pat p1 p2, g')))
            as Hmrel_p2.
         {matching_tuple_order_build_ev.
         }

         assert((match_spec g t1 p2 g' b2 ->
                 In (mtch_pair t1 (empty_d_ev t1) b2)
                    (M_ev g (t1, (p2, g')))) /\
                (decompose_spec g t1 hole__t t1 p2 g' b2 ->
                 exists ev_decom : {t1 = t1 /\ hole_contxt_c = hole_contxt_c} + {subterm_rel t1 t1},
                   In
                     (mtch_pair t1 (nonempty_d_ev t1 hole__t t1 ev_decom) b2)
                     (M_ev g (t1, (p2, g')))))
           as Happ.
         {apply (H (t1, (p2, g'))
                   Hmrel_p2
                   t1 b2 hole__t).
         }
         inversion Happ as [Hmatch_spec Hdecom].

         apply (Hmatch_spec Hmatch).
        }

        assert(exists mp1' mp2' : mtch_powset_ev t1,
                  (M_ev g (t1, (p2, g')))
                  =
                  mp1' ++ (mtch_pair t1 (empty_d_ev t1) b2) :: mp2')
          as Hsplit_p2.
        {apply (in_split (mtch_pair t1 (empty_d_ev t1) b2)
                         (M_ev g (t1, (p2, g')))
                         Hin_p2).
        }
        inversion Hsplit_p2 as [mp1' Hsplit_p2'].
        clear Hsplit_p2.
        inversion Hsplit_p2' as [mp2' Hsplit_p2''].
        rewrite Hsplit_p2''.
        clear Hsplit_p2'.
        clear Hsplit_p2''.

        (* reduce rec. call to completion *)
        rewrite map_app.
        rewrite map_cons.
        simpl.
        rewrite H3.
        rewrite fold_left_fapp.

        remember (fun mtch2 : mtch_ev t1 =>
                    match
                      mtch2 in (mtch_ev t''')
                      return (t1 = t''' -> mtch_powset_ev t1)
                    with
                    | mtch_pair t''' dh bh =>
                      fun eqp''' : t1 = t''' =>
                        match b_union b1 bh with
                        | Some b3 =>
                          mtch_pair
                            t1
                            (combine t1 hole__t t'''
                                     (inhole_eq1 t1 t''' hole_contxt_c eqp''' Heq_C)
                                     dh)
                            b3 :: nil
                        | None => nil
                        end
                    end (erefl t1)) as map_f2 eqn : Heq_map_f2.

        rewrite in_app_iff.
        left.
        destruct (map map_f2 mp1') as [ | hdmap tlmap].
      -- (* map map_f2 mp1' = nil *)
         simpl.
         rewrite fold_left_fapp.
         rewrite in_app_iff.
         left.
         apply in_eq.
      -- (* map map_f2 mp1' = hdmap tlmap *)
         simpl.
         rewrite fold_left_app.
         rewrite fold_left_fapp.
         rewrite in_app_iff.
         right.
         simpl.
         rewrite fold_left_fapp.
         rewrite in_app_iff.
         left.
         apply in_eq.
   ++ (* ev_decom = subterm t1 t1; contradiction *)
      assert(not (subterm_rel t1 t1))
       as Hnot_refl.
      {apply subterm_rel_non_reflex.
      }
      contradiction.
    Qed.

    (* case G |- t = hole [t] : hole | ∅ *)
    Lemma decom_hole_context :
      forall (sub_t : pt.term)
        (g g' : grammar)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (sub_t, ([ ], g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t' C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                    (M_ev g (t', (p', G2'))))
            end),
      exists ev_decom : {sub_t = sub_t /\ hole_contxt_c = hole_contxt_c} + {subterm_rel sub_t sub_t},
        In
          (mtch_pair sub_t
                     (nonempty_d_ev sub_t pt.hole_contxt_c sub_t ev_decom)
                     ∅) (M_ev g (sub_t, ([ ], g'))).
    Proof.
      intros sub_t' g g' H.
      generalize (M_ev_rew_hole_case g g' sub_t').
      intro Hrew_call.
      inversion Hrew_call as [ev_decom Hrew_call'].
      clear Hrew_call.
      inversion Hrew_call' as [Hsub_t'_hole Hsub_t'_nhole].
      clear Hrew_call'.

      assert(sub_t' = hole \/ sub_t' <> hole)
        as Hdisj_sub_t'.
      {destruct sub_t'.
       - (* sub_t' = a *)
         right.
         intro Hlter.
         inversion Hlter.
       - (* sub_t' = ct t0_1 t0_2 *)
         right.
         intro Hlter.
         inversion Hlter.
       - (* sub_t' = ctxt c *)
         destruct c as [ | l].
         + (* c = hole *)
           left.
           reflexivity.
         + (* c = list_contxt *)
           destruct l as [lco tr | tl lco].
           * (* l = hd_contxt lco tr *)
             right.
             intro Hctxt.
             inversion Hctxt.
           *  (* l = tail_contxt tl lco *)
           right.
           intro Hctxt.
           inversion Hctxt.
      }
      inversion Hdisj_sub_t' as [Hsub_t'_eq_hole | Hsub_t'_neq_hole].
      ++ (* sub_t' = hole *)
        rewrite (Hsub_t'_hole Hsub_t'_eq_hole).
        exists ev_decom.
        apply in_eq.
      ++ (* sub_t' <> hole *)
        rewrite (Hsub_t'_nhole Hsub_t'_neq_hole).
        exists ev_decom.
        apply in_eq.
    Qed.

    (* case G |- hd_contxt C t2 = (hd_contxt C' t2) [sub_t'] : cons p1 p2 | b1 U b2  *)
    Lemma decom_left_left_contexts :
      forall (p1 : pt.pat)
        (p2 : list_pat)
        (sub_t sub_t' : pt.term)
        (t2 : list_term)
        (b0 b1 b2 : bindings)
        (C C0 C'0 : pt.contxt)
        (g g' : grammar)
        (H0 : b_union b1 b2 = Some b0)
        (Hdecom : decompose_spec g (ctxt C0)  C'0 sub_t' p1 g b1)
        (H1 : match_spec g t2 p2 g b2)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (ctxt (hd_contxt C0 t2), (cp p1 p2, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t' C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                    (M_ev g (t', (p', G2'))))
            end),
      exists ev_decom : {sub_t' = ctxt (hd_contxt C0 t2) /\ 
                   (hd_c C'0 t2) = hole_contxt_c} + {subterm_rel sub_t' (ctxt (hd_contxt C0 t2))},
        In
          (mtch_pair (ctxt (hd_contxt C0 t2))
                     (nonempty_d_ev (ctxt (hd_contxt C0 t2)) (hd_contxt C'0 t2) sub_t'
                                    ev_decom) b0)
          (M_ev g (ctxt (hd_contxt C0 t2), (cp p1 p2, g'))).
    Proof.
      intros p1 p2 sub_t sub_t' t2 b0 b1 b2 C C0 C'0 g g' H0
             Hdecom H1 H.

      (* inspect content of recursive calls *)
      assert(exists ev_decom : {sub_t' = (ctxt C0) /\ C'0 = hole_contxt_c}
                               +
                          {subterm_rel sub_t' (ctxt C0)},
                In (mtch_pair (ctxt C0)
                              (nonempty_d_ev (ctxt C0) C'0
                                             sub_t' ev_decom)
                              b1)
                   (M_ev g (ctxt C0, (p1, g))))
        as Hdecom_in.
      {assert(matching_tuple_order g 
                (ctxt C0, (p1, g)) 
                (ctxt (hd_contxt C0 t2), (cp p1 p2, g')))
          as Hmrel.
       {matching_tuple_order_build_ev.
       }
       
       assert((match_spec g (ctxt C0) p1 g b1 ->
               In (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b1)
                  (M_ev g (ctxt C0, (p1, g)))) /\
              (decompose_spec g (ctxt C0)  C'0 sub_t' p1 g b1 ->
               exists ev_decom : {sub_t' = ctxt C0 /\ C'0 = hole_contxt_c}
                                 + {subterm_rel sub_t' (ctxt C0)},
                 In (mtch_pair (ctxt C0)
                               (nonempty_d_ev (ctxt C0) C'0 sub_t' ev_decom)
                               b1)
                    (M_ev g (ctxt C0, (p1, g)))))
         as Hmatch_decom.
       {apply (H (ctxt C0, (p1, g)) Hmrel sub_t' b1 C'0).
       }

       inversion Hmatch_decom as [Hmatch He_decom].

       apply (He_decom Hdecom).
      }
      inversion Hdecom_in as [ev_decom Hdecom_in'].
      clear Hdecom_in.
      assert(exists mp1 mp2 : mtch_powset_ev (ctxt C0),
                M_ev g (ctxt C0, (p1, g)) =
                mp1
                  ++
                  (mtch_pair (ctxt C0)
                             (nonempty_d_ev (ctxt C0) C'0 sub_t' ev_decom) b1)
                  :: mp2)
        as Hsplit_ctxtC.
      {apply in_split.
       exact Hdecom_in'.
      }
      clear Hdecom_in'.
      inversion Hsplit_ctxtC as [mp1 Hsplit_ctxtC'].
      clear Hsplit_ctxtC.
      inversion Hsplit_ctxtC' as [mp2 Hsplit_ctxtC''].
      clear Hsplit_ctxtC'.

      assert(In (mtch_pair t2 (empty_d_ev t2) b2)
                (M_ev g (list_term_c t2, (list_pat_c p2, g))))
        as Hmatch_in.
      {assert(matching_tuple_order g (list_term_c t2, (list_pat_c p2, g)) (ctxt (hd_contxt C0 t2), (cp p1 p2, g')))
          as Hmrel.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t2 p2 g b2 ->
               In (mtch_pair t2 (empty_d_ev t2) b2)
                  (M_ev g (list_term_c t2, (list_pat_c p2, g)))) /\
              (decompose_spec g t2 C'0 sub_t' p2 g b2 ->
               exists ev_decom : {sub_t' = t2 /\ C'0 = hole_contxt_c} + {subterm_rel sub_t' t2},
                 In (mtch_pair t2 (nonempty_d_ev t2 C'0 sub_t' ev_decom)
                               b2)
                    (M_ev g (list_term_c t2, (list_pat_c p2, g)))))
         as Hmatch_decom.
       {apply (H (list_term_c t2, (list_pat_c p2, g)) Hmrel sub_t' 
                    b2 C'0).
       }

       inversion Hmatch_decom as [Hmatch He_decom].

       apply (Hmatch H1).
      }

      assert(exists mp1' mp2' : mtch_powset_ev t2,
                M_ev g (list_term_c t2, (list_pat_c p2, g)) =
                mp1'
                  ++
                  (mtch_pair t2 (empty_d_ev t2) b2)
                  :: mp2')
        as Hsplit_t2.
      {apply in_split.
       exact Hmatch_in.
      }
      clear Hmatch_in.
      inversion Hsplit_t2 as [mp1' Hsplit_t2'].
      clear Hsplit_t2.
      inversion Hsplit_t2' as [mp2' Hsplit_t2''].
      clear Hsplit_t2'.

      (* rewrite call and rec. calls *)
      assert(exists proof_subt : subterms (ctxt (hd_contxt C0 t2)) (ctxt C0) t2,
                M_ev g (ctxt (hd_contxt C0 t2), (cp p1 p2, g')) =
                cons_case (ctxt (hd_contxt C0 t2)) (ctxt C0) t2 proof_subt
                          (M_ev g (ctxt C0, (p1, g)))
                          (M_ev g (list_term_c t2, (list_pat_c p2, g))))
        as Heq_call.
      {apply (M_ev_rew_cons_case_hd_ctxt g g' C0 t2 p1 p2).
      }
      inversion Heq_call as [proof_subt Heq_call'].
      clear Heq_call.
      rewrite Heq_call'.
      clear Heq_call'.
      rewrite Hsplit_ctxtC''.
      clear Hsplit_ctxtC''.
      rewrite Hsplit_t2''.
      clear Hsplit_t2''.

      (* reduce function call *)
      remember (nonempty_d_ev (ctxt C0) C'0 sub_t' ev_decom)
        as C0_decom.
      rewrite cons_case_dist.
      remember (cons_case  (ctxt (hd_contxt C0 t2)) (ctxt C0) t2 proof_subt
                           (mtch_pair (ctxt C0) C0_decom b1 :: mp2)
                           (mp1'
                              ++ mtch_pair t2 (empty_d_ev t2) b2 :: mp2'))
        as lelem eqn:Heq_lelem.

      assert(exists (res : mtch_powset_ev (ctxt (hd_contxt C0 t2))),
                lelem =
                res
                  ++
                  (cons_case_aux (ctxt (hd_contxt C0 t2)) (ctxt C0) t2
                                 proof_subt
                                 (mtch_pair (ctxt C0) C0_decom b1)
                                 (mtch_pair t2 (empty_d_ev t2) b2 :: mp2'))
                  ++
                  cons_case (ctxt (hd_contxt C0 t2)) (ctxt C0) t2
                  proof_subt mp2
                  (mp1' ++ mtch_pair t2 (empty_d_ev t2) b2 :: mp2'))
        as Hcons_dist.
      {rewrite Heq_lelem.
       apply cons_case_dist_unfold.
      }
      inversion Hcons_dist as [res Hcons_dist'].
      clear Hcons_dist.

      simpl in Hcons_dist'.
      rewrite HeqC0_decom in Hcons_dist'.
      remember (select (ctxt C0)
                       (nonempty_d_ev (ctxt C0) C'0 sub_t' ev_decom) t2
                       (empty_d_ev t2) (ctxt (hd_contxt C0 t2)) proof_subt)
        as sel eqn:Heq_sel.
      simpl in Heq_sel.
      rewrite Heq_sel in Hcons_dist'.
      simpl in Hcons_dist'.
      rewrite H0 in Hcons_dist'.

      exists (subterm2 proof_subt (erefl (ctxt C0)) ev_decom).
      rewrite in_app_iff.

      right.
      rewrite Hcons_dist'.
      rewrite in_app_iff.
      right.

      rewrite <- app_comm_cons.
      apply in_eq.
    Qed.

    (* case G |- hd_contxt C t2 = (tail_contxt C C') [sub_t'] : cons p1 p2 | b1 U b2  *)
    Lemma decom_left_right_contexts :
      forall (p1 : pt.pat)
        (p2 : list_pat)
        (sub_t sub_t' : pt.term)
        (t2 : list_term)
        (b0 b1 b2 : bindings)
        (C C0 : pt.contxt)
        (C'0 : list_contxt)
        (g g' : grammar)
        (H0 : b_union b1 b2 = Some b0)
        (H1 : match_spec g (ctxt C0) p1 g b1)
        (Hdecom : decompose_spec g t2 C'0 sub_t' p2 g b2)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (ctxt (hd_contxt C0 t2), (cp p1 p2, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t'  C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                    (M_ev g (t', (p', G2'))))
            end),
      exists ev_decom : {sub_t' = ctxt (hd_contxt C0 t2) /\ 
                      (tail_c (ctxt C0) C'0) = hole_contxt_c} +
                   {subterm_rel sub_t' (ctxt (hd_contxt C0 t2))},
        In
          (mtch_pair (ctxt (hd_contxt C0 t2))
                     (nonempty_d_ev (ctxt (hd_contxt C0 t2)) (tail_contxt (ctxt C0) C'0) sub_t'
                                    ev_decom) b0)
          (M_ev g (ctxt (hd_contxt C0 t2), (cp p1 p2, g'))).
    Proof.
      intros p1 p2 sub_t sub_t' t2 b0 b1 b2 C C0 C'0 g g' H0 H1 Hdecom H.

      (* inspect content of recursive calls *)
      assert(In (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b1)
                (M_ev g (ctxt C0, (p1, g))))
        as Hmatch_in.
      {assert(matching_tuple_order g (ctxt C0, (p1, g)) (ctxt (hd_contxt C0 t2), (cp p1 p2, g')))
          as Hmrel.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g (ctxt C0) p1 g b1 ->
               In (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b1)
                  (M_ev g (ctxt C0, (p1, g)))) /\
              (decompose_spec g (ctxt C0) C0 sub_t' p1 g b1 ->
               exists ev_decom : {sub_t' = ctxt C0 /\ C0 = hole_contxt_c} + {subterm_rel sub_t' (ctxt C0)},
                 In (mtch_pair (ctxt C0)
                               (nonempty_d_ev (ctxt C0) C0 sub_t' ev_decom)
                               b1)
                    (M_ev g (ctxt C0, (p1, g)))))
         as Hmatch_decom.
       {apply (H (ctxt C0, (p1, g)) Hmrel sub_t' b1 C0).
       }

       inversion Hmatch_decom as [Hmatch He_decom].

       apply (Hmatch H1).
      }
      assert(exists mp1 mp2 : mtch_powset_ev (ctxt C0),
                M_ev g (ctxt C0, (p1, g)) =
                mp1
                  ++
                  (mtch_pair (ctxt C0)
                             (empty_d_ev (ctxt C0)) b1)
                  :: mp2)
        as Hsplit_C0.
      {apply in_split.
       exact Hmatch_in.
      }
      clear Hmatch_in.
      inversion Hsplit_C0 as [mp1 Hsplit_C0'].
      clear Hsplit_C0.
      inversion Hsplit_C0' as [mp2 Hsplit_C0''].
      clear Hsplit_C0'.

      assert(exists ev_decom : {sub_t' = t2 /\ (list_contxt_c C'0) = hole_contxt_c} + {subterm_rel sub_t' t2},
                In (mtch_pair t2
                              (nonempty_d_ev t2 C'0
                                             sub_t' ev_decom)
                              b2)
                   (M_ev g (list_term_c t2, (list_pat_c p2, g))))
        as Hdecom_in.
      {assert(matching_tuple_order g (list_term_c t2, (list_pat_c p2, g)) (ctxt (hd_contxt C0 t2), (cp p1 p2, g')))
          as Hmrel.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t2 p2 g b2 ->
               In (mtch_pair t2 (empty_d_ev t2) b2)
                  (M_ev g (list_term_c t2, (list_pat_c p2, g)))) /\
              (decompose_spec g t2 C'0 sub_t' p2 g b2 ->
               exists ev_decom : {sub_t' = t2 /\ (list_contxt_c C'0) = hole_contxt_c} + {subterm_rel sub_t' t2},
                 In (mtch_pair t2
                               (nonempty_d_ev t2 C'0 sub_t' ev_decom)
                               b2)
                    (M_ev g (list_term_c t2, (list_pat_c p2, g)))))
         as Hmatch_decom.
       {apply (H (list_term_c t2, (list_pat_c p2, g)) Hmrel sub_t' b2 C'0).
       }

       inversion Hmatch_decom as [Hmatch He_decom].

       apply (He_decom Hdecom).
      }

      inversion Hdecom_in as [ev_decom Hdecom_in'].
      clear Hdecom_in.

      assert(exists mp1' mp2' : mtch_powset_ev t2,
                M_ev g (list_term_c t2, (list_pat_c p2, g)) =
                mp1'
                  ++
                  (mtch_pair t2 (nonempty_d_ev t2 C'0 sub_t' ev_decom) b2)
                  :: mp2')
        as Hsplit_t2.
      {apply in_split.
       exact Hdecom_in'.
      }
      clear Hdecom_in'.
      inversion Hsplit_t2 as [mp1' Hsplit_t2'].
      clear Hsplit_t2.
      inversion Hsplit_t2' as [mp2' Hsplit_t2''].
      clear Hsplit_t2'.

      (* rewrite call and rec. calls *)
      assert(exists proof_subt : subterms (ctxt (hd_contxt C0 t2)) (ctxt C0) t2,
                M_ev g (ctxt (hd_contxt C0 t2), (cp p1 p2, g')) =
                cons_case (ctxt (hd_contxt C0 t2)) (ctxt C0) t2 proof_subt
                          (M_ev g (ctxt C0, (p1, g)))
                          (M_ev g (list_term_c t2, (list_pat_c p2, g))))
        as Heq_call.
      {apply (M_ev_rew_cons_case_hd_ctxt g g' C0 t2 p1 p2).
      }
      inversion Heq_call as [proof_subt Heq_call'].
      clear Heq_call.
      rewrite Heq_call'.
      clear Heq_call'.
      rewrite Hsplit_C0''.
      clear Hsplit_C0''.
      rewrite Hsplit_t2''.
      clear Hsplit_t2''.

      (* reduce function call *)
      remember (nonempty_d_ev t2 C'0 sub_t' ev_decom)
        as t2_decom.
      rewrite cons_case_dist.
      remember (cons_case (ctxt (hd_contxt C0 t2)) (ctxt C0) t2 proof_subt
                          (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b1 :: mp2)
                          (mp1'
                             ++
                             mtch_pair t2 t2_decom b2 :: mp2'))
        as lelem eqn:Heq_lelem.

      assert(exists (res : mtch_powset_ev (ctxt (hd_contxt C0 t2))),
                lelem =
                res
                  ++
                  (cons_case_aux (ctxt (hd_contxt C0 t2)) (ctxt C0) t2
                                 proof_subt
                                 (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b1)
                                 (mtch_pair t2 t2_decom b2 :: mp2'))
                  ++
                  cons_case (ctxt (hd_contxt C0 t2)) (ctxt C0) t2
                  proof_subt mp2
                  (mp1' ++ mtch_pair t2 t2_decom b2 :: mp2'))
        as Hcons_dist.
      {rewrite Heq_lelem.
       apply cons_case_dist_unfold.
      }
      inversion Hcons_dist as [res Hcons_dist'].
      clear Hcons_dist.

      simpl in Hcons_dist'.
      rewrite Heqt2_decom in Hcons_dist'.
      rewrite H0 in Hcons_dist'.

      exists (subterm1 proof_subt ev_decom (erefl (list_term_c t2))).
      rewrite in_app_iff.

      right.
      rewrite Hcons_dist'.
      rewrite in_app_iff.
      right.

      rewrite <- app_comm_cons.
      apply in_eq.
    Qed.

    (* case G |- tail_contxt t1 C = (hd_contxt C' C) [sub_t'] : cons p1 p2 | b1 U b2  *)
    Lemma decom_right_left_contexts :
      forall (p1 : pt.pat)
        (p2 : list_pat)
        (t1 sub_t' : pt.term)
        (b0 b1 b2 : bindings)
        (C'0 : pt.contxt)
        (C0 : list_contxt)
        (g g' : grammar)
        (H0 : b_union b1 b2 = Some b0)
        (Hdecom : decompose_spec g t1  C'0 sub_t' p1 g b1)
        (H1 : match_spec g (ctxt C0) p2 g b2)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (ctxt (tail_contxt t1 C0), (cp p1 p2, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t'  C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                    (M_ev g (t', (p', G2'))))
            end),
      exists ev_decom : {sub_t' = ctxt (tail_contxt t1 C0) /\ 
                      (hd_c C'0 (list_contxt_2_list_term C0)) = hole_contxt_c} +
                   {subterm_rel sub_t' (ctxt (tail_contxt t1 C0))},
        In
          (mtch_pair (ctxt (tail_contxt t1 C0))
                     (nonempty_d_ev (ctxt (tail_contxt t1 C0)) 
                        (hd_contxt C'0 (list_contxt_2_list_term C0)) sub_t'
                                    ev_decom) b0)
          (M_ev g (ctxt (tail_contxt t1 C0), (cp p1 p2, g'))).
    Proof.
      intros p1 p2 t1 sub_t' b0 b1 b2 C'0 C0 g g' H0 Hdecom H1
             H.

      (* inspect content of recursive calls *)
      assert(exists ev_decom : {sub_t' = t1 /\ C'0 = hole_contxt_c} + {subterm_rel sub_t' t1},
                In (mtch_pair t1
                              (nonempty_d_ev t1 C'0
                                             sub_t' ev_decom)
                              b1)
                   (M_ev g (t1, (p1, g))))
        as Hdecom_in.
      {assert(matching_tuple_order g (t1, (p1, g)) (ctxt (tail_contxt t1 C0), (cp p1 p2, g')))
          as Hmrel.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t1 p1 g b1 ->
               In (mtch_pair t1 (empty_d_ev t1) b1)
                  (M_ev g (t1, (p1, g)))) /\
              (decompose_spec g t1  C'0 sub_t' p1 g b1 ->
               exists ev_decom : {sub_t' = t1 /\ C'0 = hole_contxt_c}
                                 + {subterm_rel sub_t' t1},
                 In (mtch_pair t1
                               (nonempty_d_ev t1 C'0 sub_t' ev_decom)
                               b1)
                    (M_ev g (t1, (p1, g)))))
         as Hmatch_decom.
       {apply (H (t1, (p1, g)) Hmrel sub_t' b1 C'0).
       }

       inversion Hmatch_decom as [Hmatch He_decom].

       apply (He_decom Hdecom).
      }
      inversion Hdecom_in as [ev_decom Hdecom_in'].
      clear Hdecom_in.
      assert(exists mp1 mp2 : mtch_powset_ev t1,
                M_ev g (t1, (p1, g)) =
                mp1
                  ++
                  (mtch_pair t1
                             (nonempty_d_ev t1 C'0 sub_t' ev_decom) b1)
                  :: mp2)
        as Hsplit_t1.
      {apply in_split.
       exact Hdecom_in'.
      }
      clear Hdecom_in'.
      inversion Hsplit_t1 as [mp1 Hsplit_t1'].
      clear Hsplit_t1.
      inversion Hsplit_t1' as [mp2 Hsplit_t1''].
      clear Hsplit_t1'.

      assert(In (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b2)
                (M_ev g (ctxt C0, (list_pat_c p2, g))))
        as Hmatch_in.
      {assert(matching_tuple_order g (ctxt C0, (list_pat_c p2, g)) (ctxt (tail_contxt t1 C0), (cp p1 p2, g')))
          as Hmrel.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g (ctxt C0) p2 g b2 ->
               In (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b2)
                  (M_ev g (ctxt C0, (list_pat_c p2, g)))) /\
              (decompose_spec g (ctxt C0) C'0 sub_t' p2 g b2 ->
               exists ev_decom : {sub_t' = ctxt C0 /\ C'0 = hole_contxt_c} + {subterm_rel sub_t' (ctxt C0)},
                 In (mtch_pair (ctxt C0)
                               (nonempty_d_ev (ctxt C0) C'0 sub_t' ev_decom)
                               b2)
                    (M_ev g (ctxt C0, (list_pat_c p2, g)))))
         as Hmatch_decom.
       {apply (H (ctxt C0, (list_pat_c p2, g)) Hmrel sub_t' b2 C'0).
       }

       inversion Hmatch_decom as [Hmatch He_decom].

       apply (Hmatch H1).
      }

      assert(exists mp1' mp2' : mtch_powset_ev (ctxt C0),
                M_ev g (ctxt C0, (list_pat_c p2, g)) =
                mp1'
                  ++
                  (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b2)
                  :: mp2')
        as Hsplit_C0.
      {apply in_split.
       exact Hmatch_in.
      }
      clear Hmatch_in.
      inversion Hsplit_C0 as [mp1' Hsplit_C0'].
      clear Hsplit_C0.
      inversion Hsplit_C0' as [mp2' Hsplit_C0''].
      clear Hsplit_C0'.

      (* rewrite call and rec. calls *)
      assert(exists proof_subt : subterms (ctxt (tail_contxt t1 C0)) t1 (ctxt C0),
                M_ev g (ctxt (tail_contxt t1 C0), (cp p1 p2, g')) =
                cons_case (ctxt (tail_contxt t1 C0)) t1 (ctxt C0) proof_subt
                          (M_ev g (t1, (p1, g)))
                          (M_ev g (ctxt C0, (list_pat_c p2, g))))
        as Heq_call.
      {apply (M_ev_rew_cons_case_tail_ctxt g g' t1 C0 p1 p2).
      }
      inversion Heq_call as [proof_subt Heq_call'].
      clear Heq_call.
      rewrite Heq_call'.
      clear Heq_call'.
      rewrite Hsplit_t1''.
      clear Hsplit_t1''.
      rewrite Hsplit_C0''.
      clear Hsplit_C0''.

      (* reduce function call *)
      remember (nonempty_d_ev t1 C'0 sub_t' ev_decom)
        as t1_decom.
      rewrite cons_case_dist.
      remember (cons_case (ctxt (tail_contxt t1 C0)) t1 (ctxt C0) proof_subt
                          (mtch_pair t1 t1_decom b1 :: mp2)
                          (mp1'
                             ++
                             mtch_pair (ctxt C0)
                             (empty_d_ev (ctxt C0)) b2 :: mp2'))
        as lelem eqn:Heq_lelem.

      assert(exists (res : mtch_powset_ev (ctxt (tail_contxt t1 C0))),
                lelem =
                res
                  ++
                  (cons_case_aux (ctxt (tail_contxt t1 C0)) t1 (ctxt C0)
                                 proof_subt
                                 (mtch_pair t1 t1_decom b1)
                                 (mtch_pair (ctxt C0)
                                            (empty_d_ev (ctxt C0)) b2 :: mp2'))
                  ++
                  cons_case (ctxt (tail_contxt t1 C0)) t1 (ctxt C0)
                  proof_subt mp2
                  (mp1' ++ mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b2 :: mp2'))
        as Hcons_dist.
      {rewrite Heq_lelem.
       apply cons_case_dist_unfold.
      }
      inversion Hcons_dist as [res Hcons_dist'].
      clear Hcons_dist.

      simpl in Hcons_dist'.
      rewrite Heqt1_decom in Hcons_dist'.
      remember (select t1
                       (nonempty_d_ev t1 C'0 sub_t' ev_decom)
                       (ctxt C0)
                       (empty_d_ev (ctxt C0))
                       (ctxt (tail_contxt t1 C0)) proof_subt)
        as sel eqn:Heq_sel.
      simpl in Heq_sel.
      rewrite Heq_sel in Hcons_dist'.
      simpl in Hcons_dist'.
      rewrite H0 in Hcons_dist'.

      exists (subterm2 proof_subt (erefl t1) ev_decom).
      rewrite in_app_iff.

      right.
      rewrite Hcons_dist'.
      rewrite in_app_iff.
      right.

      rewrite <- app_comm_cons.
      apply in_eq.
    Qed.

    (* case G |- cons t1 t2 = (tail_contxt t1 C) [sub_t'] : cons p1 p2 | b1 U b2  *)
    Lemma decom_cons_right_contexts :
      forall (p1 : pt.pat)
        (p2 : list_pat)
        (sub_t t1 sub_t' : pt.term)
        (t2 : list_term)
        (b0 b1 b2 : bindings)
        (C : pt.contxt)
        (C0 : list_contxt)
        (g g' : grammar)
        (H0 : b_union b1 b2 = Some b0)
        (H1 : match_spec g t1 p1 g b1)
        (Hdecom : decompose_spec g t2 C0 sub_t' p2 g b2)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (ct t1 t2, (cp p1 p2, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t' C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                    (M_ev g (t', (p', G2'))))
            end),
      exists ev_decom : {sub_t' = ct t1 t2 /\ (tail_c t1 C0) = hole_contxt_c} + {subterm_rel sub_t' (ct t1 t2)},
        In (mtch_pair (ct t1 t2)
                      (nonempty_d_ev (ct t1 t2) (tail_contxt t1 C0) sub_t' ev_decom)
                      b0)
           (M_ev g (ct t1 t2, (cp p1 p2, g'))).
    Proof.
      intros p1 p2 sub_t t1 sub_t' t2 b0 b1 b2 C C0 g g' H0 H1
             Hdecom H.

      (* inspect content of recursive calls *)
      assert(In (mtch_pair t1 (empty_d_ev t1) b1)
                (M_ev g (t1, (p1, g))))
        as Hmatch_in.
      {assert(matching_tuple_order g (t1, (p1, g)) (ct t1 t2, (cp p1 p2, g')))
          as Hmrel.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t1 p1 g b1 ->
               In (mtch_pair t1 (empty_d_ev t1) b1)
                  (M_ev g (t1, (p1, g)))) /\
              (decompose_spec g t1  C0 sub_t' p1 g b1 ->
               exists ev_decom : {sub_t' = t1 /\ (list_contxt_c C0) = hole_contxt_c}
                                 + {subterm_rel sub_t' t1},
                 In (mtch_pair t1
                               (nonempty_d_ev t1 C0 sub_t' ev_decom)
                               b1)
                    (M_ev g (t1, (p1, g)))))
         as Hmatch_decom.
       {apply (H (t1, (p1, g)) Hmrel sub_t' b1 C0).
       }

       inversion Hmatch_decom as [Hmatch He_decom].

       apply (Hmatch H1).
      }
      assert(exists mp1 mp2 : mtch_powset_ev t1,
                M_ev g (t1, (p1, g)) =
                mp1
                  ++
                  (mtch_pair t1
                             (empty_d_ev t1) b1)
                  :: mp2)
        as Hsplit_t1.
      {apply in_split.
       exact Hmatch_in.
      }
      clear Hmatch_in.
      inversion Hsplit_t1 as [mp1 Hsplit_t1'].
      clear Hsplit_t1.
      inversion Hsplit_t1' as [mp2 Hsplit_t1''].
      clear Hsplit_t1'.

      assert(exists ev_decom : {sub_t' = t2 /\ (list_contxt_c C0) = hole_contxt_c} + {subterm_rel sub_t' t2},
                In (mtch_pair t2
                              (nonempty_d_ev t2 C0
                                             sub_t' ev_decom)
                              b2)
                   (M_ev g (list_term_c t2, (list_pat_c p2, g))))
        as Hdecom_in.
      {assert(matching_tuple_order g (list_term_c t2, (list_pat_c p2, g)) (ct t1 t2, (cp p1 p2, g')))
          as Hmrel.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t2 p2 g b2 ->
               In (mtch_pair t2 (empty_d_ev t2) b2)
                  (M_ev g (list_term_c t2, (list_pat_c p2, g)))) /\
              (decompose_spec g t2  C0 sub_t' p2 g b2 ->
               exists ev_decom : {sub_t' = t2 /\ (list_contxt_c C0) = hole_contxt_c}
                                 + {subterm_rel sub_t' t2},
                 In (mtch_pair t2
                               (nonempty_d_ev t2 C0 sub_t' ev_decom)
                               b2)
                    (M_ev g (list_term_c t2, (list_pat_c p2, g)))))
         as Hmatch_decom.
       {apply (H (list_term_c t2, (list_pat_c p2, g)) Hmrel sub_t' b2 C0).
       }

       inversion Hmatch_decom as [Hmatch He_decom].

       apply (He_decom Hdecom).
      }

      inversion Hdecom_in as [ev_decom Hdecom_in'].
      clear Hdecom_in.

      assert(exists mp1' mp2' : mtch_powset_ev t2,
                M_ev g (list_term_c t2, (list_pat_c p2, g)) =
                mp1'
                  ++
                  (mtch_pair t2 (nonempty_d_ev t2 C0 sub_t' ev_decom) b2)
                  :: mp2')
        as Hsplit_t2.
      {apply in_split.
       exact Hdecom_in'.
      }
      clear Hdecom_in'.
      inversion Hsplit_t2 as [mp1' Hsplit_t2'].
      clear Hsplit_t2.
      inversion Hsplit_t2' as [mp2' Hsplit_t2''].
      clear Hsplit_t2'.

      (* rewrite call and rec. calls *)
      assert(M_ev g (ct t1 t2, (cp p1 p2, g')) =
               cons_case (ct t1 t2) t1 t2 (build_subterm_proof t1 t2)
                 (M_ev g (t1, (p1, g)))
                 (M_ev g (list_term_c t2, (list_pat_c p2, g))))
        as Heq_call.
      {apply (M_ev_rew_cons_case g g' t1 t2 p1 p2).
      }
      rewrite Heq_call.
      clear Heq_call.
      rewrite Hsplit_t1''.
      clear Hsplit_t1''.
      rewrite Hsplit_t2''.
      clear Hsplit_t2''.

      (* reduce function call *)
      remember (nonempty_d_ev t2 C0 sub_t' ev_decom)
        as t2_decom.
      rewrite cons_case_dist.
      remember (cons_case (ct t1 t2) t1 t2 (build_subterm_proof t1 t2)
                          (mtch_pair t1 (empty_d_ev t1) b1 :: mp2)
                          (mp1'
                             ++
                             mtch_pair t2 t2_decom b2 :: mp2'))
        as lelem eqn:Heq_lelem.

      assert(exists (res : mtch_powset_ev (ct t1 t2)),
                lelem =
                res
                  ++
                  (cons_case_aux (ct t1 t2) t1 t2
                                 (build_subterm_proof t1 t2)
                                 (mtch_pair t1 (empty_d_ev t1) b1)
                                 (mtch_pair t2 t2_decom b2 :: mp2'))
                  ++
                  cons_case (ct t1 t2) t1 t2
                  (build_subterm_proof t1 t2) mp2
                  (mp1' ++ mtch_pair t2 t2_decom b2 :: mp2'))
        as Hcons_dist.
      {rewrite Heq_lelem.
       apply cons_case_dist_unfold.
      }
      inversion Hcons_dist as [res Hcons_dist'].
      clear Hcons_dist.

      simpl in Hcons_dist'.
      rewrite Heqt2_decom in Hcons_dist'.
      rewrite H0 in Hcons_dist'.

      exists (subterm1 (build_subterm_proof t1 t2) ev_decom (erefl (list_term_c t2))).
      rewrite in_app_iff.

      right.
      rewrite Hcons_dist'.
      rewrite in_app_iff.
      right.

      rewrite <- app_comm_cons.
      apply in_eq.
    Qed.

    Lemma decom_cons_left_contexts :
      forall (p1 : pt.pat)
        (p2 : list_pat)
        (sub_t t1 sub_t' : pt.term)
        (t2 : list_term)
        (b0 b1 b2 : bindings)
        (C C0 : pt.contxt)
        (g g' : grammar)
        (H0 : b_union b1 b2 = Some b0)
        (Hdecom : decompose_spec g t1 C0 sub_t' p1 g b1)
        (H1 : match_spec g t2 p2 g b2)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (ct t1 t2, (cp p1 p2, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t' C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                    (M_ev g (t', (p', G2'))))
            end),
      exists ev_decom : {sub_t' = ct t1 t2 /\ (hd_c C0 t2) = hole_contxt_c} + {subterm_rel sub_t' (ct t1 t2)},
        In
          (mtch_pair (ct t1 t2)
                     (nonempty_d_ev (ct t1 t2) (hd_contxt C0 t2) sub_t' ev_decom) b0)
          (M_ev g (ct t1 t2, (cp p1 p2, g'))).
    Proof.
      intros p1 p2 sub_t t1 sub_t' t2 b0 b1 b2 C C0 g g' H0 Hdecom
             H1 H.

      (* inspect content of recursive calls *)
      assert(exists ev_decom : {sub_t' = t1 /\ C0 = hole_contxt_c} + {subterm_rel sub_t' t1},
                In (mtch_pair t1 (nonempty_d_ev t1 C0 sub_t' ev_decom)
                              b1)
                   (M_ev g (t1, (p1, g))))
        as Hdecom_in.
      {assert(matching_tuple_order g (t1, (p1, g)) (ct t1 t2, (cp p1 p2, g')))
          as Hmrel.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t1 p1 g b1 ->
               In (mtch_pair t1 (empty_d_ev t1) b1)
                  (M_ev g (t1, (p1, g)))) /\
              (decompose_spec g t1 C0 sub_t' p1 g b1 ->
               exists ev_decom : {sub_t' = t1 /\ C0 = hole_contxt_c} + {subterm_rel sub_t' t1},
                 In (mtch_pair t1 (nonempty_d_ev t1 C0 sub_t' ev_decom)
                               b1)
                    (M_ev g (t1, (p1, g)))))
         as Hmatch_decom.
       {apply (H (t1, (p1, g)) Hmrel sub_t' b1 C0).
       }

       inversion Hmatch_decom as [Hmatch He_decom].

       apply (He_decom Hdecom).
      }
      inversion Hdecom_in as [ev_decom Hdecom_in'].
      clear Hdecom_in.
      assert(exists mp1 mp2 : mtch_powset_ev t1,
                M_ev g (t1, (p1, g)) =
                mp1 ++ (mtch_pair t1 (nonempty_d_ev t1 C0 sub_t' ev_decom) b1)
                  :: mp2)
        as Hsplit_t1.
      {apply in_split.
       exact Hdecom_in'.
      }
      clear Hdecom_in'.
      inversion Hsplit_t1 as [mp1 Hsplit_t1'].
      clear Hsplit_t1.
      inversion Hsplit_t1' as [mp2 Hsplit_t1''].
      clear Hsplit_t1'.

      assert(In (mtch_pair t2 (empty_d_ev t2) b2)
                (M_ev g (list_term_c t2, (list_pat_c p2, g))))
        as Hmatch_in.
      {assert(matching_tuple_order g (list_term_c t2, (list_pat_c p2, g)) (ct t1 t2, (cp p1 p2, g')))
          as Hmrel.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t2 p2 g b2 ->
               In (mtch_pair t2 (empty_d_ev t2) b2)
                  (M_ev g (list_term_c t2, (list_pat_c p2, g)))) /\
              (decompose_spec g t2 C0 sub_t' p2 g b2 ->
               exists ev_decom : {sub_t' = t2 /\ C0 = hole_contxt_c} + {subterm_rel sub_t' t2},
                 In (mtch_pair t2 (nonempty_d_ev t2 C0 sub_t' ev_decom)
                               b2)
                    (M_ev g (list_term_c t2, (list_pat_c p2, g)))))
         as Hmatch_decom.
       {apply (H (list_term_c t2, (list_pat_c p2, g)) Hmrel sub_t' b2 C0).
       }

       inversion Hmatch_decom as [Hmatch He_decom].

       apply (Hmatch H1).
      }
      assert(exists mp1' mp2' : mtch_powset_ev t2,
                M_ev g (list_term_c t2, (list_pat_c p2, g)) =
                mp1'
                  ++
                  (mtch_pair t2 (empty_d_ev t2) b2)
                  :: mp2')
        as Hsplit_t2.
      {apply in_split.
       exact Hmatch_in.
      }
      clear Hmatch_in.
      inversion Hsplit_t2 as [mp1' Hsplit_t2'].
      clear Hsplit_t2.
      inversion Hsplit_t2' as [mp2' Hsplit_t2''].
      clear Hsplit_t2'.

      (* rewrite call and rec. calls *)
      assert(M_ev g (ct t1 t2, (cp p1 p2, g')) =
               cons_case (ct t1 t2) t1 t2 (build_subterm_proof t1 t2)
                 (M_ev g (t1, (p1, g)))
                 (M_ev g (list_term_c t2, (list_pat_c p2, g))))
        as Heq_call.
      {apply M_ev_rew_cons_case.
      }
      rewrite Heq_call.
      clear Heq_call.
      rewrite Hsplit_t1''.
      rewrite Hsplit_t2''.

      (* reduce function call *)
      remember (nonempty_d_ev t1 C0 sub_t' ev_decom)
        as t1_decom.
      rewrite cons_case_dist.
      remember (cons_case (ct t1 t2) t1 t2 (build_subterm_proof t1 t2)
                          (mtch_pair t1 t1_decom b1 :: mp2)
                          (mp1'
                             ++ mtch_pair t2 (empty_d_ev t2) b2 :: mp2'))
        as lelem eqn:Heq_lelem.

      assert(exists (res : mtch_powset_ev (ct t1 t2)),
                cons_case (ct t1 t2) t1 t2 (build_subterm_proof t1 t2)
                          (mtch_pair t1 t1_decom b1 :: mp2)
                          (mp1'
                             ++ mtch_pair t2 (empty_d_ev t2) b2 :: mp2') =
                res
                  ++
                  (cons_case_aux (ct t1 t2) t1 t2
                                 (build_subterm_proof t1 t2)
                                 (mtch_pair t1 t1_decom b1)
                                 (mtch_pair t2 (empty_d_ev t2) b2 :: mp2'))
                  ++
                  cons_case (ct t1 t2) t1 t2
                  (build_subterm_proof t1 t2) mp2
                  (mp1' ++ mtch_pair t2 (empty_d_ev t2) b2 :: mp2'))
        as Hcons_dist.
      {apply cons_case_dist_unfold.
      }
      inversion Hcons_dist as [res Hcons_dist'].
      clear Hcons_dist.

      simpl in Hcons_dist'.
      rewrite Heqt1_decom in Hcons_dist'.
      simpl in Hcons_dist'.
      rewrite H0 in Hcons_dist'.

      simpl in Heq_lelem.
      rewrite Heqt1_decom in Heq_lelem.
      rewrite <- Heq_lelem in Hcons_dist'.

      exists (subterm2 (build_subterm_proof t1 t2) (erefl t1) ev_decom).
      rewrite in_app_iff.

      right.
      rewrite Hcons_dist'.
      rewrite in_app_iff.
      right.
      apply in_eq.
    Qed.

    (* case G |- tail_contxt t1 C = (tail_contxt C C') [sub_C] : cons p1 p2 | b1 U b2  *)
    Lemma decom_right_right_contexts :
      forall (p1 : pt.pat)
        (p2 : list_pat)
        (sub_t t1 sub_t' : pt.term)
        (b0 b1 b2 : bindings)
        (C : pt.contxt)
        (C0 C'0 : list_contxt)
        (g g' : grammar)
        (H0 : b_union b1 b2 = Some b0)
        (H1 : match_spec g t1 p1 g b1)
        (Hdecom : decompose_spec g (ctxt C0) C'0 sub_t' p2 g b2)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (ctxt (tail_contxt t1 C0), (cp p1 p2, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t' C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                    (M_ev g (t', (p', G2'))))
            end),
      exists ev_decom : {sub_t' = ctxt (tail_contxt t1 C0) /\ 
                      (tail_c t1 C'0) = hole_contxt_c} +
                   {subterm_rel sub_t' (ctxt (tail_contxt t1 C0))},
        In
          (mtch_pair (ctxt (tail_contxt t1 C0))
                     (nonempty_d_ev (ctxt (tail_contxt t1 C0)) (tail_contxt t1 C'0) sub_t'
                                    ev_decom) b0)
          (M_ev g (ctxt (tail_contxt t1 C0), (cp p1 p2, g'))).
    Proof.
      intros p1 p2 sub_t t1 sub_t' b0 b1 b2 C C0 C'0 g g' H0 H1 Hdecom
             H.

      (* inspect content of recursive calls *)
      assert(In (mtch_pair t1 (empty_d_ev t1) b1)
                (M_ev g (t1, (p1, g))))
        as Hmatch_in.
      {assert(matching_tuple_order g (t1, (p1, g)) (ctxt (tail_contxt t1 C0), (cp p1 p2, g')))
          as Hmrel.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t1 p1 g b1 ->
               In (mtch_pair t1 (empty_d_ev t1) b1)
                  (M_ev g (t1, (p1, g)))) /\
              (decompose_spec g t1 C'0 sub_t' p1 g b1 ->
               exists ev_decom : {sub_t' = t1 /\ (list_contxt_c C'0) = hole_contxt_c}
                                 + {subterm_rel sub_t' t1},
                 In (mtch_pair t1
                               (nonempty_d_ev t1 C'0 sub_t' ev_decom)
                               b1)
                    (M_ev g (t1, (p1, g)))))
         as Hmatch_decom.
       {apply (H (t1, (p1, g)) Hmrel sub_t' b1 C'0).
       }

       inversion Hmatch_decom as [Hmatch He_decom].

       apply (Hmatch H1).
      }
      assert(exists mp1 mp2 : mtch_powset_ev t1,
                M_ev g (t1, (p1, g)) =
                mp1
                  ++
                  (mtch_pair t1
                             (empty_d_ev t1) b1)
                  :: mp2)
        as Hsplit_t1.
      {apply in_split.
       exact Hmatch_in.
      }
      clear Hmatch_in.
      inversion Hsplit_t1 as [mp1 Hsplit_t1'].
      clear Hsplit_t1.
      inversion Hsplit_t1' as [mp2 Hsplit_t1''].
      clear Hsplit_t1'.

      assert(exists ev_decom : {sub_t' = ctxt C0 /\ (list_contxt_c C'0) = hole_contxt_c}
                               +
                               {subterm_rel sub_t' (ctxt C0)},
                In (mtch_pair (ctxt C0)
                              (nonempty_d_ev (ctxt C0) C'0
                                             sub_t' ev_decom)
                              b2)
                   (M_ev g (ctxt C0, (list_pat_c p2, g))))
        as Hdecom_in.
      {assert(matching_tuple_order g (ctxt C0, (list_pat_c p2, g)) (ctxt (tail_contxt t1 C0), (cp p1 p2, g')))
          as Hmrel.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g (ctxt C0) p2 g b2 ->
               In (mtch_pair (ctxt C0) (empty_d_ev (ctxt C0)) b2)
                  (M_ev g (ctxt C0, (list_pat_c p2, g)))) /\
              (decompose_spec g (ctxt C0) C'0 sub_t' p2 g b2 ->
               exists ev_decom : {sub_t' = ctxt C0 /\ (list_contxt_c C'0) = hole_contxt_c}
                            + {subterm_rel sub_t' (ctxt C0)},
                 In (mtch_pair (ctxt C0)
                               (nonempty_d_ev (ctxt C0) C'0 sub_t' ev_decom)
                               b2)
                    (M_ev g (ctxt C0, (list_pat_c p2, g)))))
         as Hmatch_decom.
       {apply (H (ctxt C0, (list_pat_c p2, g)) Hmrel sub_t' b2 C'0).
       }

       inversion Hmatch_decom as [Hmatch He_decom].

       apply (He_decom Hdecom).
      }

      inversion Hdecom_in as [ev_decom Hdecom_in'].
      clear Hdecom_in.

      assert(exists mp1' mp2' : mtch_powset_ev (ctxt C0),
                M_ev g (ctxt C0, (list_pat_c p2, g)) =
                mp1'
                  ++
                  (mtch_pair (ctxt C0)
                             (nonempty_d_ev (ctxt C0) C'0 sub_t'
                                            ev_decom) b2)
                  :: mp2')
        as Hsplit_C0.
      {apply in_split.
       exact Hdecom_in'.
      }
      clear Hdecom_in'.
      inversion Hsplit_C0 as [mp1' Hsplit_C0'].
      clear Hsplit_C0.
      inversion Hsplit_C0' as [mp2' Hsplit_C0''].
      clear Hsplit_C0'.

      (* rewrite call and rec. calls *)
      assert(exists proof_subt : subterms (ctxt (tail_contxt t1 C0)) t1 (ctxt C0),
                M_ev g (ctxt (tail_contxt t1 C0), (cp p1 p2, g')) =
                cons_case (ctxt (tail_contxt t1 C0)) t1 (ctxt C0) proof_subt
                          (M_ev g (t1, (p1, g)))
                          (M_ev g (ctxt C0, (list_pat_c p2, g))))
        as Heq_call.
      {apply (M_ev_rew_cons_case_tail_ctxt g g' t1 C0 p1 p2).
      }
      inversion Heq_call as [proof_subt Heq_call'].
      clear Heq_call.
      rewrite Heq_call'.
      clear Heq_call'.
      rewrite Hsplit_C0''.
      clear Hsplit_C0''.
      rewrite Hsplit_t1''.
      clear Hsplit_t1''.

      (* reduce function call *)
      remember (nonempty_d_ev (ctxt C0) C'0 sub_t' ev_decom)
        as C0_decom.
      rewrite cons_case_dist.
      remember (cons_case (ctxt (tail_contxt t1 C0)) t1 (ctxt C0) proof_subt
                          (mtch_pair t1 (empty_d_ev t1) b1 :: mp2)
                          (mp1'
                             ++
                             mtch_pair (ctxt C0) C0_decom b2 :: mp2'))
        as lelem eqn:Heq_lelem.

      assert(exists (res : mtch_powset_ev (ctxt (tail_contxt t1 C0))),
                lelem =
                res
                  ++
                  (cons_case_aux (ctxt (tail_contxt t1 C0)) t1 (ctxt C0)
                                 proof_subt
                                 (mtch_pair t1 (empty_d_ev t1) b1)
                                 (mtch_pair (ctxt C0) C0_decom b2 :: mp2'))
                  ++
                  cons_case (ctxt (tail_contxt t1 C0)) t1 (ctxt C0)
                  proof_subt mp2
                  (mp1' ++ mtch_pair (ctxt C0) C0_decom b2 :: mp2'))
        as Hcons_dist.
      {rewrite Heq_lelem.
       apply cons_case_dist_unfold.
      }
      inversion Hcons_dist as [res Hcons_dist'].
      clear Hcons_dist.

      simpl in Hcons_dist'.
      rewrite HeqC0_decom in Hcons_dist'.
      rewrite H0 in Hcons_dist'.

      exists (subterm1 proof_subt ev_decom (erefl (ctxt C0))).
      rewrite in_app_iff.

      right.
      rewrite Hcons_dist'.
      rewrite in_app_iff.
      right.

      rewrite <- app_comm_cons.
      apply in_eq.
    Qed.

    (* case G |- t1 = C [t2] : nt n | ∅  *)
    Lemma decom_nt_case :
      forall (p0 : pt.pat)
        (sub_t t1 sub_t' : pt.term)
        (b0 : bindings)
        (C C' : pt.contxt)
        (g g' : grammar)
        (n : pt.nonterm)
        (proof : prod_in_g (n, p0) g')
        (Hdecom : decompose_spec g t1 C' sub_t' p0
                                 (remove_prod (n, p0) g' proof) b0)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (t1, (nt n, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t' C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                    (M_ev g (t', (p', G2'))))
            end),
      exists ev_decom : {sub_t' = t1 /\ C' = hole_contxt_c} + {subterm_rel sub_t' t1},
        In (mtch_pair t1 (nonempty_d_ev t1 C' sub_t' ev_decom) ∅)
           (M_ev g (t1, (nt n, g'))).
    Proof.
      intros p0 sub_t t1 sub_t' b0 C C' g g' n proof Hdecom H.

      (* inspect content of recursive call *)
      assert(matching_tuple_order g
               (t1, (p0, remove_prod (n, p0) g' proof))
               (t1, (nt n, g')))
        as Hnt_rel.
      {matching_tuple_order_build_ev.
      }
      assert(exists ev_decom : {sub_t' = t1 /\ C' = hole_contxt_c} + {subterm_rel sub_t' t1},
                In (mtch_pair t1 (nonempty_d_ev t1 C' sub_t' ev_decom) b0)
                   (M_ev g (t1, (p0, remove_prod (n, p0) g' proof))))
        as IH.
      {assert((match_spec g t1 p0 (remove_prod (n, p0) g' proof) b0 ->
               In (mtch_pair t1 (empty_d_ev t1) b0)
                  (M_ev g (t1, (p0, (remove_prod (n, p0) g' proof)))))
              /\
              (decompose_spec g t1 C' sub_t' p0
                              (remove_prod (n, p0) g' proof) b0 ->
               exists ev_decom : {sub_t' = t1 /\ C' = hole_contxt_c} + {subterm_rel sub_t' t1},
                 In
                   (mtch_pair t1 (nonempty_d_ev t1 C' sub_t' ev_decom) b0)
                   (M_ev g (t1, (p0, (remove_prod (n, p0) g' proof))))))
          as Happ.
       {apply (H (t1, (p0, remove_prod (n, p0) g' proof))
                 Hnt_rel
                 sub_t' b0 C').
       }
       inversion Happ as [Hmatch_spec Hev_decom].

       apply (Hev_decom Hdecom).
      }

      (* reduce call M_ev nt n *)
      rewrite (M_ev_rew_nt_case g g' t1 n).
      unfold nt_case.
      assert(exists (proof' : prod_in_g (n, p0) g') G1' G1'',
                get_rhs g' n = G1' ++ ((exist (fun pa =>
                                                 prod_in_g (n, pa) g')
                                              p0
                                              proof') :: nil) ++ G1'') as lemma_get_rhs.
      {apply (get_rhs_split g' p0 n proof).
      }
      inversion lemma_get_rhs as [proof' Hget'].
      clear lemma_get_rhs.
      inversion Hget' as [G1' Hget''].
      clear Hget'.
      inversion Hget'' as [G1'' Hget'''].
      clear Hget''.

      rewrite Hget'''.
      rewrite map_app.
      rewrite map_app.
      rewrite fold_left_app.
      rewrite fold_left_fapp.

      inversion IH as [ev_decom IH'].
      clear IH.
      exists ev_decom.

      rewrite in_app_iff.
      right.
      simpl.
      rewrite fold_left_fapp.
      rewrite in_app_iff.
      left.
      assert(exists l1 l2,
                M_ev g (t1, (p0, remove_prod (n, p0) g' proof'))
                =
                l1 ++ (mtch_pair t1 (nonempty_d_ev t1 C' sub_t' ev_decom) b0) :: l2)
        as Hin.
      {apply in_split.
       exact IH'.
      }
      inversion Hin as [l1 Hin'].
      clear Hin.
      inversion Hin' as [l2 Hin''].
      clear Hin'.
      rewrite Hin''.
      rewrite map_app.
      rewrite in_app_iff.
      right.
      rewrite map_cons.
      apply in_eq.
    Qed.

    (* case G |- t1 = C1 ++ C2 [t2] : in_hole p1 p2 | b1 U b2  *)
    Lemma decom_inhole_case_inp_cons :
      forall (p1 p2 : pt.pat)
        (sub_t t0 t1 sub_t' : pt.term)
        (b0 b1 b2 : bindings)
        (C C1 C2 : pt.contxt)
        (g g' : grammar)
        (H0 : b_union b1 b2 = Some b0)
        (H1 : pt.subterm_rel t1 t0)
        (Hdecom1 : decompose_spec g t0 C1 t1 p1 g' b1)
        (Hdecom2 : decompose_spec g t1 C2 sub_t' p2 g b2)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (t0, (inhole_pat p1 p2, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings)
              (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t' C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In
                   (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom)
                              b') (M_ev g (t', (p', G2'))))
            end),
      exists ev_decom : {sub_t' = t0 /\ (context_com C1 C2) = hole_contxt_c} + {subterm_rel sub_t' t0},
        In
          (mtch_pair t0
                     (nonempty_d_ev t0 (context_com C1 C2) sub_t' ev_decom)
                     b0) (M_ev g (t0, (inhole_pat p1 p2, g'))).
    Proof.
      intros p1 p2 sub_t t0 t1 sub_t' b0 b1 b2 C C1 C2 g g' H0 H1
             Hdecom1 Hdecom2 H.

      (* unfold and simplify call *)
      assert(M_ev g (t0, (inhole_pat p1 p2, g'))
             =
             inhole_case t0 p1 p2 g g'
                         (fun (tpg2 : matching_tuple)
                              (_ : matching_tuple_order g tpg2
                                     (t0, (inhole_pat p1 p2, g')))
                          => M_ev g tpg2))
        as Hcall.
      {apply M_ev_rew_inhole_case.
      }
      rewrite Hcall.


      (* inspect content of rec. call *)
      assert(exists ev_decom : {t1 = t0 /\ C1 = hole_contxt_c} + {subterm_rel t1 t0},
                In (mtch_pair t0 (nonempty_d_ev t0 C1 t1 ev_decom) b1)
                   (M_ev g (t0, (p1, g'))))
        as Hrec_call.
      {assert(matching_tuple_order g (t0, (p1, g')) (t0, (inhole_pat p1 p2, g')))
          as Hmrel_p1.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t0 p1 g' b1 ->
               In (mtch_pair t0 (empty_d_ev t0) b1)
                  (M_ev g (t0, (p1, g')))) /\
              (decompose_spec g t0 C1 t1 p1 g' b1 ->
               exists ev_decom : {t1 = t0 /\ C1 = hole_contxt_c} + {subterm_rel t1 t0},
                 In
                   (mtch_pair t0
                              (nonempty_d_ev t0 C1 t1 ev_decom) b1)
                   (M_ev g (t0, (p1, g')))))
         as Happ.
       {apply (H (t0, (p1, g'))
                 Hmrel_p1
                 t1 b1 C1).
       }
       inversion Happ as [Hmatch_spec Hdecom].

       apply (Hdecom Hdecom1).
      }

      inversion Hrec_call as [ev_decom Hrec_call'].
      clear Hrec_call.

      assert(exists mp1 mp2 : mtch_powset_ev t0,
                M_ev g (t0, (p1, g'))
                =
                mp1
                  ++
                  (mtch_pair t0 (nonempty_d_ev t0 C1 t1 ev_decom) b1) :: mp2)
        as Hsplit_rec_call.
      {apply (in_split (mtch_pair t0 (nonempty_d_ev t0 C1 t1 ev_decom) b1)
                       (M_ev g (t0, (p1, g')))
                       Hrec_call').
      }
      clear Hrec_call'.
      inversion Hsplit_rec_call as [mp1 Hsplit_rec_call'].
      clear Hsplit_rec_call.
      inversion Hsplit_rec_call' as [mp2 Hsplit_rec_call''].
      clear Hsplit_rec_call'.

      unfold inhole_case.
      rewrite Hsplit_rec_call''.
      clear Hsplit_rec_call''.

      (* distribute map application *)
      rewrite map_app.
      rewrite map_cons.
      simpl.
      rewrite fold_left_app.
      rewrite fold_left_fapp.

      destruct ev_decom as [ [Ht1_eq Heq_c] | Ht1_subterm].
      ++ (* ev_decom = (t1 = t0) *)
         (* contradiction *)
         assert(not (subterm_rel t1 t1))
          as Hnot_refl.
         {apply subterm_rel_non_reflex.
         }
         rewrite <- Ht1_eq in H1.
         contradiction.
      ++ (* ev_decom = (subterm t1 t0) *)
         (* inspect content of right rec. call *)
         intros.
         assert(exists ev_decom : {sub_t' = t1 /\ C2 = hole_contxt_c} + {subterm_rel sub_t' t1},
                   In (mtch_pair t1 (nonempty_d_ev t1 C2 sub_t' ev_decom) b2)
                      (M_ev g (t1, (p2, g))))
           as Hrec_call.
         {assert(matching_tuple_order g (t1, (p2, g)) (t0, (inhole_pat p1 p2, g')))
             as Hmrel_p2.
          {matching_tuple_order_build_ev.
          }
          
          assert((match_spec g t1 p2 g b2 ->
                  In (mtch_pair t1 (empty_d_ev t1) b2)
                     (M_ev g (t1, (p2, g)))) /\
                 (decompose_spec g t1 C2 sub_t' p2 g b2 ->
                  exists ev_decom : {sub_t' = t1 /\ C2 = hole_contxt_c} + {subterm_rel sub_t' t1},
                    In
                      (mtch_pair t1
                                 (nonempty_d_ev t1 C2 sub_t' ev_decom) b2)
                      (M_ev g (t1, (p2, g)))))
            as Happ.
          {apply (H (t1, (p2, g))
                    Hmrel_p2
                    sub_t' b2 C2).
          }
          inversion Happ as [Hmatch_spec Hdecom].

          apply (Hdecom Hdecom2).
         }
         inversion Hrec_call as [ev_decom_sub_t' Hrec_call'].
         clear Hrec_call.

         assert(exists mp1 mp2 : mtch_powset_ev t1,
                   M_ev g (t1, (p2, g))
                   =
                   mp1
                     ++
                     (mtch_pair t1 (nonempty_d_ev t1 C2 sub_t'
                                                  ev_decom_sub_t') b2) :: mp2)
           as Hsplit_rec_call.
         {apply (in_split (mtch_pair t1 (nonempty_d_ev t1 C2 sub_t'
                                                       ev_decom_sub_t') b2)
                          (M_ev g (t1, (p2, g)))
                          Hrec_call').
         }
         clear Hrec_call'.
         inversion Hsplit_rec_call as [mp1' Hsplit_rec_call'].
         clear Hsplit_rec_call.
         inversion Hsplit_rec_call' as [mp2' Hsplit_rec_call''].
         clear Hsplit_rec_call'.
         rewrite Hsplit_rec_call''.
         clear Hsplit_rec_call''.

         (* simplify applications of fold_left and map  *)
         assert({sub_t' = t0 /\ C2 = hole_contxt_c} + {subterm_rel sub_t' t0})
           as Hsub_t'.
         {destruct ev_decom_sub_t' as [ [Hsub_t'_eq Heq_C] | Hsub_t'_subterm].
          - (* Hsub_t'_eq = sub_t' = t1 *)
            rewrite <- Hsub_t'_eq in Ht1_subterm.
            right.
            exact Ht1_subterm.
          - (* Hsub_t'_eq = subterm_rel *)
            right.
            apply (subterm_trans sub_t' t1 t0 Hsub_t'_subterm
                                 Ht1_subterm).
         }

         rewrite map_app.
         rewrite fold_left_app.
         simpl.
         rewrite H0.
         rewrite fold_left_fapp.
         rewrite fold_left_fapp.
         destruct ev_decom_sub_t' as [Heq_sub_t' | Hsubterm_sub_t'].
         -- (* ev_decom_sub_t' = sub_t' = t1 *)
            unfold combine_proof.
            simpl.
            destruct Heq_sub_t'.
            unfold eq_rec_r.
            repeat (rewrite <- eq_rec_eq).
            remember (eq_rec t1
                     (fun y : pt.term =>
                      {y = t1 /\ C2 = hole__t} + {pt.subterm_rel y t1} ->
                      {y = t0 /\ context_com C1 C2 = hole__t} + {pt.subterm_rel y t0})
                     [eta eq_rec hole__t
                            (fun y : pt.contxt =>
                             {t1 = t1 /\ y = hole__t} + {pt.subterm_rel t1 t1} ->
                             {t1 = t0 /\ context_com C1 y = hole__t} +
                             {pt.subterm_rel t1 t0})
                            (fun=> right
                                     (eq_ind_r [eta pt.subterm_rel t1] Ht1_subterm
                                        (erefl t0))) C2 (eq_sym e0)] sub_t' 
                     (eq_sym e) (left (conj e e0)))
                       as Proof_sub_t'_t0.
            exists Proof_sub_t'_t0.
            rewrite in_app_iff.
            right.
            rewrite fold_left_fapp.
            rewrite fold_left_fapp.
            rewrite in_app_iff.
            left.
            rewrite in_app_iff.
            left.
            rewrite in_app_iff.
            right.
            rewrite HeqProof_sub_t'_t0.
            unfold eq_rec_r.
            repeat (rewrite <- eq_rec_eq).
            apply in_eq.
         -- (* ev_decom_sub_t' = subterm sub_t' t0 *)
            unfold combine_proof.
            simpl.
            exists (right (pt.subterm_trans sub_t' t1 t0 Hsubterm_sub_t' Ht1_subterm)).
            rewrite in_app_iff.
            right.
            rewrite fold_left_fapp.
            rewrite fold_left_fapp.
            rewrite in_app_iff.
            left.
            rewrite in_app_iff.
            left.
            rewrite in_app_iff.
            right.
            unfold eq_rec_r.
            unfold eq_ind_r.
            repeat (rewrite <- eq_rec_eq).
            apply in_eq.
    Qed.

    Lemma decom_inhole_case_noinp_cons :
      forall (p1 p2 : pt.pat)
        (t sub_t : pt.term)
        (b0 b1 b2 : bindings)
        (C : pt.contxt)
        (g g' : grammar)
        (H0 : b_union b1 b2 = Some b0)
        (Hdecom1 : decompose_spec g t hole__t t p1 g' b1)
        (Hdecom2 : decompose_spec g t C sub_t p2 g' b2)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (t, (inhole_pat p1 p2, g')) ->
            match tup with
            | (t', (p', G2')) =>
            forall (sub_t' : pt.term) (b' : bindings)
              (C' : pt.contxt),
              (match_spec g t' p' G2' b' ->
               In (mtch_pair t' (empty_d_ev t') b')
                  (M_ev g (t', (p', G2')))) /\
              (decompose_spec g t' C' sub_t' p' G2' b' ->
               exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                 In
                   (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom)
                              b') (M_ev g (t', (p', G2'))))
            end),
      exists ev_decom : {sub_t = t /\ (context_com hole__t C) = hole_contxt_c} + {subterm_rel sub_t t},
        In
          (mtch_pair t
                     (nonempty_d_ev t (context_com hole__t C) sub_t ev_decom)
                     b0) (M_ev g (t, (inhole_pat p1 p2, g'))).
    Proof.
      intros p1 p2 t0 sub_t b0 b1 b2 C g g' H0
             Hdecom1 Hdecom2 H.

      (* unfold and simplify call *)
      assert(M_ev g (t0, (inhole_pat p1 p2, g'))
             =
             inhole_case t0 p1 p2 g g'
                         (fun (tpg2 : matching_tuple)
                              (_ : matching_tuple_order g tpg2
                                      (t0, (inhole_pat p1 p2, g')))
                          => M_ev g tpg2))
        as Hcall.
      {apply M_ev_rew_inhole_case.
      }
      rewrite Hcall.


      (* inspect content of rec. call *)
      assert(exists ev_decom : {t0 = t0 /\ hole__t = hole_contxt_c} + {subterm_rel t0 t0},
                In (mtch_pair t0 (nonempty_d_ev t0 hole__t t0 ev_decom) b1)
                   (M_ev g (t0, (p1, g'))))
        as Hrec_call.
      {assert(matching_tuple_order g (t0, (p1, g')) (t0, (inhole_pat p1 p2, g')))
          as Hmrel_p1.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t0 p1 g' b1 ->
               In (mtch_pair t0 (empty_d_ev t0) b1)
                  (M_ev g (t0, (p1, g')))) /\
              (decompose_spec g t0 hole__t t0 p1 g' b1 ->
               exists ev_decom : {t0 = t0 /\ hole__t = hole_contxt_c} + {subterm_rel t0 t0},
                 In
                   (mtch_pair t0
                              (nonempty_d_ev t0 hole__t t0 ev_decom) b1)
                   (M_ev g (t0, (p1, g')))))
         as Happ.
       {apply (H (t0, (p1, g'))
                 Hmrel_p1
                 t0 b1 hole__t).
       }
       inversion Happ as [Hmatch_spec Hdecom].

       apply (Hdecom Hdecom1).
      }

      inversion Hrec_call as [ev_decom Hrec_call'].
      clear Hrec_call.

      assert(exists mp1 mp2 : mtch_powset_ev t0,
                M_ev g (t0, (p1, g'))
                =
                mp1
                  ++
                  (mtch_pair t0 (nonempty_d_ev t0 hole__t t0 ev_decom) b1) :: mp2)
        as Hsplit_rec_call.
      {apply (in_split (mtch_pair t0 (nonempty_d_ev t0 hole__t t0 ev_decom) b1)
                       (M_ev g (t0, (p1, g')))
                       Hrec_call').
      }
      clear Hrec_call'.
      inversion Hsplit_rec_call as [mp1 Hsplit_rec_call'].
      clear Hsplit_rec_call.
      inversion Hsplit_rec_call' as [mp2 Hsplit_rec_call''].
      clear Hsplit_rec_call'.

      unfold inhole_case.
      rewrite Hsplit_rec_call''.
      clear Hsplit_rec_call''.

      (* distribute map application *)
      rewrite map_app.
      rewrite map_cons.
      simpl.
      rewrite fold_left_app.
      rewrite fold_left_fapp.

      destruct ev_decom as [ [Ht1_eq Heq_C ]| Ht1_subterm].
      ++ (* ev_decom = (t0 = t0) *)
         (* inspect content of right rec. call *)
         assert(exists ev_decom : {sub_t = t0 /\ C = hole_contxt_c} + {subterm_rel sub_t t0},
                   In (mtch_pair t0 (nonempty_d_ev t0 C sub_t ev_decom) b2)
                      (M_ev g (t0, (p2, g'))))
          as Hrec_call.
         {assert(matching_tuple_order g (t0, (p2, g')) (t0, (inhole_pat p1 p2, g')))
             as Hmrel_p2.
          {matching_tuple_order_build_ev.
          }

          assert((match_spec g t0 p2 g' b2 ->
                  In (mtch_pair t0 (empty_d_ev t0) b2)
                     (M_ev g (t0, (p2, g')))) /\
                 (decompose_spec g t0 C sub_t p2 g' b2 ->
                  exists ev_decom : {sub_t = t0 /\ C = hole_contxt_c} + {subterm_rel sub_t t0},
                    In
                      (mtch_pair t0
                                 (nonempty_d_ev t0 C sub_t ev_decom) b2)
                      (M_ev g (t0, (p2, g')))))
            as Happ.
          {apply (H (t0, (p2, g'))
                    Hmrel_p2
                    sub_t b2 C).
          }
          inversion Happ as [Hmatch_spec Hdecom].

          apply (Hdecom Hdecom2).
         }
         inversion Hrec_call as [ev_decom_sub_t' Hrec_call'].
         clear Hrec_call.

         exists ev_decom_sub_t'.
         assert(exists mp1 mp2 : mtch_powset_ev t0,
                   M_ev g (t0, (p2, g'))
                   =
                   mp1
                     ++
                     (mtch_pair t0 (nonempty_d_ev t0 C sub_t
                                                  ev_decom_sub_t') b2) :: mp2)
           as Hsplit_rec_call.
         {apply (in_split (mtch_pair t0 (nonempty_d_ev t0 C sub_t
                                                       ev_decom_sub_t') b2)
                          (M_ev g (t0, (p2, g')))
                          Hrec_call').
         }
         clear Hrec_call'.
         inversion Hsplit_rec_call as [mp1' Hsplit_rec_call'].
         clear Hsplit_rec_call.
         inversion Hsplit_rec_call' as [mp2' Hsplit_rec_call''].
         clear Hsplit_rec_call'.
         rewrite Hsplit_rec_call''.
         clear Hsplit_rec_call''.

         (* simplify applications of fold_left and map  *)
         rewrite in_app_iff.
         right.
         rewrite map_app.
         rewrite fold_left_app.
         simpl.
         rewrite H0.
         rewrite fold_left_fapp.
         rewrite fold_left_fapp.
         rewrite in_app_iff.
         left.
         rewrite in_app_iff.
         left.
         rewrite in_app_iff.
         right.
         destruct ev_decom_sub_t' as [ [Heq_sub_t' Heq_C'] | Hsubterm_sub_t'].
         -- (* ev_decom_sub_t' = sub_t' = t0 *)
            unfold combine_proof.
            simpl.
            unfold eq_rec_r.
            repeat (rewrite <- eq_rec_eq).
            left.
            unfold eq_rec.
            destruct (eq_sym Heq_sub_t').
            unfold eq_rect.
            repeat (rewrite <- eq_rect_eq).
            destruct (eq_sym Heq_C').
            unfold inhole_eq1.
            assert(Heq: Heq_sub_t' = eq_sym (erefl t0)).
            {assert(Heq_sub_t' = erefl t0).
             {apply UIP_refl.
             }
             auto.
            }
            rewrite Heq.
            assert(Heq_C = Heq_C').
            {assert(Heq_C = erefl hole__t).
             {apply UIP_refl.
             }
             assert(Heq_C' = erefl hole__t).
             {apply UIP_refl.
             }
             congruence.
            }
            congruence.
         -- (* ev_decom_sub_t' = subterm sub_t' t0 *)
            unfold combine_proof.
            simpl.
            left.
            unfold eq_rec_r.
            repeat (rewrite <- eq_rec_eq).
            reflexivity.
        ++ (* ev_decom = (subterm t0 t0) *)
           (* contradiction *)
           assert(not (subterm_rel t0 t0))
            as Hnot_refl.
           {apply subterm_rel_non_reflex.
           }
           contradiction.
    Qed.

    (* case G |- t1 = C [t2] : name_pat x p | {(x, C)} U b  *)
    Lemma decom_name_case :
      forall (p0 : pt.pat)
        (sub_t t1 sub_t' : pt.term)
        (b0 b1 : bindings)
        (C C' : pt.contxt)
        (g g' : grammar)
        (x : pt.var)
        (H0 : b_union ((x, ctxt C') :: ∅) b1 = Some b0)
        (Hdecom : decompose_spec g t1  C' sub_t' p0 g' b1)
        (H : forall tup : matching_tuple,
            matching_tuple_order g tup (t1, (name x p0, g')) ->
            match tup with
            | (t', (p', G2')) =>
                forall (sub_t' : pt.term) (b' : bindings) (C' : pt.contxt),
                  (match_spec g t' p' G2' b' ->
                   In (mtch_pair t' (empty_d_ev t') b')
                     (M_ev g (t', (p', G2')))) /\
                    (decompose_spec g t' C' sub_t' p' G2' b' ->
                     exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                       In (mtch_pair t' (nonempty_d_ev t' C' sub_t' ev_decom) b')
                         (M_ev g (t', (p', G2'))))
            end),
        exists ev_decom : {sub_t' = t1 /\ C' = hole_contxt_c} + {subterm_rel sub_t' t1},
          In (mtch_pair t1 (nonempty_d_ev t1 C' sub_t' ev_decom) b0)
             (M_ev g (t1, (name x p0, g'))).
    Proof.
      intros p0 sub_t t1 sub_t' b0 b1 C C' g g' x H0 Hdecom H.

      (* we show that
            In (mtch_pair t0 (empty_d_ev t0) bp)
               (M_ev (m_rel_e (g, t0) (p0, g')) *)
      rewrite (M_ev_rew_name_case g g' t1 p0 x).
      simpl.

      assert(exists ev_decom : {sub_t' = t1 /\ C' = hole_contxt_c} + {subterm_rel sub_t' t1},
                In (mtch_pair t1 (nonempty_d_ev t1 C' sub_t' ev_decom) b1)
                   (M_ev g (t1, (p0, g')))
            )
        as Hinpair_inst.
      {assert(matching_tuple_order g (t1, (p0, g')) (t1, (name x p0, g')))
          as Hname_pat_rel.
       {matching_tuple_order_build_ev.
       }

       assert((match_spec g t1 p0 g' b1 ->
               In (mtch_pair t1 (empty_d_ev t1) b1)
                  (M_ev g (t1, (p0, g')))) /\
              (decompose_spec g t1 C' sub_t' p0 g' b1 ->
               exists ev_decom : {sub_t' = t1 /\ C' = hole_contxt_c} + {subterm_rel sub_t' t1},
                 In
                   (mtch_pair t1 (nonempty_d_ev t1 C' sub_t' ev_decom) b1)
                   (M_ev g (t1, (p0, g')))))
         as Happ.
       {apply (H (t1, (p0, g'))
                 Hname_pat_rel
                 sub_t' b1 C').
       }
       inversion Happ as [Hmatch_spec Hexists_decom].

       assert(exists ev_decom : {sub_t' = t1 /\ C' = hole_contxt_c} + {subterm_rel sub_t' t1},
                 In (mtch_pair t1 (nonempty_d_ev t1 C' sub_t' ev_decom) b1)
                    (M_ev g (t1, (p0, g'))))
         as Hpair_Mev.
       {apply (Hexists_decom Hdecom).
       }
       inversion Hpair_Mev as [ev_decom Hpair_Mev'].
       clear Hpair_Mev.

       exists ev_decom.
       exact Hpair_Mev'.
      }
      (* now we show the effect of name_case over
            (mtch_pair t1 (nonempty_d_ev t1 C' sub_t' ev_decom) b1) *)

      inversion Hinpair_inst as [ev_decom Hinpair_inst'].
      clear Hinpair_inst.
      exists ev_decom.

      assert(exists l1 l2,
                M_ev g (t1, (p0, g')) = l1 ++
                             (mtch_pair t1
                                        (nonempty_d_ev t1 C' sub_t'
                                                       ev_decom) b1) :: l2)
        as Hrec_set_split.
      {apply in_split.
       exact Hinpair_inst'.
      }
      inversion Hrec_set_split as [l1 Hrec_set_split'].
      clear Hrec_set_split.
      inversion Hrec_set_split' as [l2 Hrec_set_split''].
      clear Hrec_set_split'.

      assert(name_case t1
                       (l1 ++ mtch_pair t1
                           (nonempty_d_ev t1 C' sub_t' ev_decom) b1 :: l2) x
             = (name_case t1 l1 x)
                 ++
                 (name_case t1
                            (mtch_pair t1
                                       (nonempty_d_ev t1 C' sub_t' ev_decom)
                                       b1 :: l2) x))
        as Hname_case_eq.
      {apply (name_case_concat t1 l1
                               (mtch_pair t1
                                          (nonempty_d_ev t1 C' sub_t'
                                                         ev_decom) b1 :: l2)
                               x).
      }

      rewrite <- Hrec_set_split'' in Hname_case_eq.
      clear Hrec_set_split''.
      rewrite Hname_case_eq.
      clear Hname_case_eq.
      remember (name_case t1 l1 x) as l1'.
      remember
        (name_case t1
                   (mtch_pair t1 (nonempty_d_ev t1 C' sub_t'
                                                ev_decom) b1 :: l2) x)
        as l2'.
      remember (mtch_pair t1 (nonempty_d_ev t1 C' sub_t' ev_decom) b1) as elem.
      rewrite in_app_iff.
      right.
      clear Heql1' l1 l1'.
      simpl in Heql2'.
      rewrite Heqelem in Heql2'.
      rewrite <- eq_rec_eq in Heql2'.

      unfold named in Heql2'.

      remember (bindings_app (rem_rep b1) x) as binding_app_b1_x.
      destruct binding_app_b1_x as [t' |].
      - (* bindings_app (rem_rep b1) x = Some t' *)
        remember (MatchTads.PatTermsDec.term_eq_dec (ctxt C') t') as term_eq_C_t.
        destruct term_eq_C_t as [Heq_C_t | Hneq_C_t].
        + (* C = t *)
          rewrite Heql2'.

          simpl in H0.
          rewrite <- Heqbinding_app_b1_x in H0.
          rewrite <- Heqterm_eq_C_t in H0.
          inversion H0.
          rewrite H2.
          apply in_eq.
        + (* C <> t *)
          simpl in H0.
          rewrite <- Heqbinding_app_b1_x in H0.
          rewrite <- Heqterm_eq_C_t in H0.
          inversion H0.
      - (* bindings_app (rem_rep b1) x = None *)
        simpl in H0.
        rewrite <- Heqbinding_app_b1_x in H0.
        inversion H0.
        rewrite H2 in Heql2'.
        rewrite Heql2'.
        rewrite H2.
        apply in_eq.
    Qed.

  End Lemmas.

  Ltac a_step := unfold M_ev;
                 rewrite Fix_eq;
                 [(* func. ext. of M_ev_body *)
                   apply fix_eq_fun_ext
                 | unfold M_ev_body; 
                   simpl].

  Theorem completeness_M : forall G1 G2 p t sub_t b C,
      (match_spec G1 t p G2 b ->
       In (mtch_pair t (empty_d_ev t) b)
          (M_ev G1 (t, (p, G2))))
      /\
      (decompose_spec G1 t  C sub_t p G2 b ->
       exists (ev_decom : {sub_t = t /\ C = hole_contxt_c} + {subterm_rel sub_t t}),
         In (mtch_pair t (nonempty_d_ev t C sub_t ev_decom) b)
            (M_ev G1 (t, (p, G2)))).
  Proof.
    intros G1 G2 p t sub_t b C.

    (* to apply the induction principle derived from the well-foundedness
       of m_rel, we rewrite the statement as a predicate over a
       match_rel_tup tuple *)
    enough (IP: 
             forall  (tup : matching_tuple),
               match tup with
               | (t', (p', G2')) =>
                   forall sub_t' b' C',
                     (match_spec G1 t' p' G2' b' ->
                      In (mtch_pair t' (empty_d_ev t') b')
                        (M_ev G1 (t', (p', G2')))) /\
                       (decompose_spec G1 t' C' sub_t' p' G2' b' ->
                        exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                          In (mtch_pair t' (nonempty_d_ev t' C'
                                              sub_t' ev_decom) b')
                            (M_ev G1 (t', (p', G2'))))
               end).
    * (* original goal *)
      apply (IP (t, (p, G2)) sub_t b C).
    * (* prove IP hypothesis *)
      apply (matching_tuple_ind
              (fun tup : matching_tuple =>
                 match tup with
                 | (t', (p', G2')) =>
                   forall sub_t' b' C',
                     (match_spec G1 t' p' G2' b' ->
                      In (mtch_pair t' (empty_d_ev t') b')
                         (M_ev G1 (t', (p', G2')))) /\
                     (decompose_spec G1 t' C' sub_t' p' G2' b' ->
                      exists ev_decom : {sub_t' = t' /\ C' = hole_contxt_c} + {subterm_rel sub_t' t'},
                        In (mtch_pair t' (nonempty_d_ev t' C'
                                                        sub_t' ev_decom) b')
                           (M_ev G1 (t', (p', G2'))))
                 end) G1).
      intros [ t1 [p1 G'] ] H sub_t' b' C'.
      split.
      + (* match_spec *)
        intros Hmatch.
        induction Hmatch as [a | | ? ? ? ? ? ? Hmatch_spec b_union_some ? | | | | | | |].

        - (* case G |- a : a | ∅ *)
          a_step.
          case (pt.lit_eq_dec a a).
          -- (* a = a *)
            intros _; simpl.
            left.
            reflexivity.
          -- (* a <> a *)
            assert (Ha : a = a).
            { reflexivity. }
            contradiction.
        - (* case G |- hole : hole | ∅ *)
          a_step.
          right.
          left.
          reflexivity.
        - (* case G |- t : name x p | b’  *)
          eapply match_name_case ; eauto.
        - (* case G |- t : nt n | ∅ *)
          eapply match_nt_case; eauto.
        - (* case G |- ct t1 t2 : cp p1 p2  | b *)
          eapply match_cons_case ; eauto.
        - (* case G |- ctxt (hd_contxt C0 t2) : cp p1 p2  | b *)
          eapply match_hd_contxt_case ; eauto.
        - (* case G |- ctxt (tail_contxt t2 C0) : cp p1 p2  | b *)
          eapply match_tail_contxt_case ; eauto.
        - (* case G |- nil : nil  | b *)
          a_step.
          left.
          reflexivity.
        - (* case G |- t : in-hole p1 p2  | b *)
          (* p1 consumes input *)
          eapply match_inhole_case_inp_cons ; eauto.
        - (* case G |- t : in-hole p1 p2  | b *)
          (* p1 does not consume input *)
          eapply match_inhole_case_noinp_cons; eauto.
    + (* decompose_spec *)
      intro Hdecom.
      dependent induction Hdecom.

      - (* case G |- t = hole [t] : hole | ∅ *)
        eapply (decom_hole_context t0 G1 G' _).

      - (* case G |- ct t1 t2 = (hd_contxt C0 t2) [sub_t'] : cons p1 p2 | b1 U b2 *)
        eapply decom_cons_left_contexts ; eauto.

      - (* case G |- hd_contxt C t2 = (hd_contxt C' t2) [sub_t'] : cons p1 p2 | b1 U b2  *)
        eapply decom_left_left_contexts ; eauto.


      - (* case G |- tail_contxt t1 C = (hd_contxt C' C) [sub_t'] : cons p1 p2 | b1 U b2  *)
        eapply decom_right_left_contexts; eauto.

      - (* case G |- cons t1 t2 = (tail_contxt t1 C) [sub_t'] : cons p1 p2 | b1 U b2  *)
        eapply decom_cons_right_contexts ; eauto.

      - (* case G |- hd_contxt C t2 = (tail_contxt C C') [sub_t'] : cons p1 p2 | b1 U b2  *)
        eapply decom_left_right_contexts ; eauto.

      - (* case G |- tail_contxt t1 C = (tail_contxt t1 C') [sub_C] : cons p1 p2 | b1 U b2  *)
        eapply decom_right_right_contexts ; eauto.

      - (* case G |- t1 = C [t1] : nt n | ∅  *)
        eapply decom_nt_case ; eauto.

      - (* case G |- t1 = C1 ++ C2 [t2] : in_hole p1 p2 | b1 U b2  *)
        (* p1 consumes input *)
        eapply decom_inhole_case_inp_cons ; eauto.
      - (* case G |- t1 = C1 ++ C2 [t2] : in_hole p1 p2 | b1 U b2  *)
        (* p1 does not consume input *)
        eapply decom_inhole_case_noinp_cons ; eauto.
      - (* case G |- t1 = C [t2] : name_pat x p | {(x, C)} U b  *)
        eapply decom_name_case ; eauto.
      Unshelve.
      apply H.
  Qed.

End Completeness.
