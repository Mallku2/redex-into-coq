Require Export
        match_spec_lemmas
        lib_ext.ListExt.

Require Import
        Lists.List
        Logic.Eqdep
        (* inj_pair2_eq_dec *)
        Logic.Eqdep_dec
        Program.Equality
        (* Some_inj *)
        ssreflect
        ssr.ssrfun.

Module Soundness (pt : PatTermsSymb).
  Import pt.

  Module MatchSpecLemmas := MatchSpecLemmas pt.
  Import MatchSpecLemmas.
  Import MatchImplLemmas.
  Import MatchingSpec.
  Import Matching.
  Import MatchTads.
  Import WfRel.
  Import GrammarLists.

  Theorem soundness_M : forall G1 G2 p t sub_t b C,
      (In (mtch_pair t (empty_d_ev t) b)
          (M_ev G1 (t, (p, G2))) ->
       G1 ⊢ t : p , G2 | b) /\
        (forall (ev_decom : {sub_t = t /\ C = hole_contxt_c} + {subterm_rel sub_t t}),
            In (mtch_pair t (nonempty_d_ev t C sub_t ev_decom) b)
               (M_ev G1 (t, (p , G2))) ->
            G1 ⊢ t ⩦ C[sub_t] : p,  G2 | b).
   Proof.
     intros G1 G2 p t sub_t b C.
     (* to apply the induction principle derived from the well-foundedness
       of matching_tuple_order, we rewrite the statement as a predicate over a
       matching_tuple *)
    enough (IP: forall  (tup : matching_tuple),
               match tup with
               | (t', (p', G2')) =>
                   forall sub_t b C,
                     (In (mtch_pair t' (empty_d_ev t') b)
                        (M_ev G1 (t', (p', G2'))) ->
                      match_spec G1 t' p' G2' b) /\
                       (forall (ev_decom : {sub_t = t' /\ C = hole_contxt_c} + 
                                        {subterm_rel sub_t t'}),
                           In (mtch_pair t' (nonempty_d_ev t' C sub_t ev_decom) b)
                             (M_ev G1 (t', (p' , G2'))) ->
                           decompose_spec G1 t' C sub_t p' G2' b)
               end).
     - apply (IP (t, (p, G2)) sub_t b C).
     - (* actual proof *)
       clear G2 p t sub_t b C.
       apply (matching_tuple_ind _ G1).
       intros [t [p G2] ] IH sub_t b C.
       split.
       * (* match *)
         destruct p.
         + (* lit *)
           M_ev_reduce.
           destruct t.
           -- (* t = lit *)
              simpl.
              intro Hin.
              destruct (pt.lit_eq_dec l l0) as [Heq | Hneq].
              ** inversion Hin as [Hin_hd | Hin_tl].
                 ++ inversion Hin_hd.
                     rewrite Heq.
                     eauto using match_spec.
                 ++ inversion Hin_tl.
              ** inversion Hin.
           -- (* t = list_term *)
              intro Hin.
              inversion Hin.
           -- (* t = contxt *)
              intro Hin.
              inversion Hin.
         + (* p = hole *)
           M_ev_reduce.
           destruct t.
           -- (* t = lit *)
              intro Hin.
              simpl in Hin.
              inversion Hin as [Heq | Hfalse].
              ** inversion Heq.
              ** inversion Hfalse.
           -- (* t = hole *)
              intro Hin.
              simpl in Hin.
              inversion Hin as [Heq | Hfalse].
              ** inversion Heq.
              ** inversion Hfalse.
           -- (* c = contxt *)
              destruct c.
              ** (* c = hole *)
                 intro Hin.
                 simpl in Hin.
                 inversion Hin as [Hfalse1 | [ Heq | Hfalse2] ].
                 ++ inversion Hfalse1.
                 ++ inversion Heq.
                    eauto using match_spec.
                 ++ inversion Hfalse2.
              ** (* c = list contxt *)
                 destruct l.
                 ++ (* l = hd contxt *)
                    simpl.
                    intro Hin.
                    inversion Hin as [Heq | Hfalse].
                    --- inversion Heq.
                    --- inversion Hfalse.
                 ++ (* l = tail contxt *)
                    simpl.
                    intro Hin.
                    inversion Hin as [Heq | Hfalse].
                    --- inversion Heq.
                    --- inversion Hfalse.
         + (* p = list pat *)
           match goal with
           | [l' : cons__p |-_] =>
               destruct l'
           end.
           -- (* p = nil *)
              destruct t.
              ** (* t = lit *)
                 M_ev_reduce.
                 simpl.
                 intuition.
              ** (* t = list term *)
                 M_ev_reduce.
                 match goal with
                 | [l' : cons__t |-_] =>
                     destruct l'
                 end.
                 ++ (* t = nil *)
                    intro Hin.
                    inversion Hin as [Heq | Hfalse].
                    --- inversion Heq.
                        eauto using match_spec.
                    --- inversion Hfalse.
                 ++ simpl.
                    intuition.
              ** (* t = contxt *)
                 M_ev_reduce.
                 simpl.
                 intuition.
           -- (* p = cons pat *)
              destruct t as [ | | c].
              ** (* t = lit *)
                 M_ev_reduce.
                 simpl.
                 intuition.
              ** (* t = list term *)
                 match goal with
                 | [l' : cons__t |-_] =>
                     destruct l'
                 end.
                 ++ (* t = nil *)
                    M_ev_reduce.
                    simpl.
                    intuition.
                 ++ (* t = cons *)
                    generalize (M_ev_rew_cons_case G1 G2 t l0 p l).
                    intros [Hsubt Heq].
                    rewrite Heq.
                    intro Hin_cons.
                    apply M_ev_cons_case_pair_in in Hin_cons.
                    
                    inversion Hin_cons as [bl [br [Hb [Hin_l Hin_r] ] ] ].
                    
                    assert(Hlt_l :
                            matching_tuple_order G1 (t, (p, G1)) (ct t l0, (cp p l, G2))).
                    {matching_tuple_order_build_ev.
                    }
                    generalize (IH _ Hlt_l t bl C).
                    intros [Hmtch_l _].
                    apply Hmtch_l in Hin_l.
                    clear Hmtch_l.

                    assert(Hlt_r :
                            matching_tuple_order G1 
                              (list_term_c l0, (list_pat_c l, G1)) 
                              (ct t l0, (cp p l, G2))).
                    {matching_tuple_order_build_ev.
                    }
                    generalize (IH _ Hlt_r t br C).
                    intros [Hmtch_r _].
                    apply Hmtch_r in Hin_r.
                    clear Hmtch_r.
                    eauto using match_spec.
              ** (* contxt *)
                 destruct c as [ | l'].
                 --- (* c = hole *)
                     M_ev_reduce.
                     intuition.
                 --- (* c = ctxt list *)
                     destruct l' as [c tl | hd c].
                     +++ (* hd_c c l0 *)
                         generalize (M_ev_rew_cons_case_hd_ctxt G1 G2 c tl p l).
                         intros [Hsubt Heq].
                         rewrite Heq.
                         intro Hin_cons.
                         apply M_ev_cons_case_hd_contxt_pair_in in Hin_cons.                      
                         inversion Hin_cons as [bl [br [Hb [Hin_l Hin_r] ] ] ].
                         
                         assert(Hlt_l :
                                 matching_tuple_order G1 
                                   (contxt_term c, (p, G1)) 
                                   (contxt_term (hd_c c tl), (cp p l, G2))).
                         {matching_tuple_order_build_ev.
                         }
                         generalize (IH _ Hlt_l (contxt_term c) bl C).
                         intros [Hmtch_l _].
                         apply Hmtch_l in Hin_l.
                         clear Hmtch_l.

                         assert(Hlt_r :
                                 matching_tuple_order G1 
                                   (list_term_c tl, (list_pat_c l, G1)) 
                                   (ctxt (hd_c c tl), (cp p l, G2))).
                         {matching_tuple_order_build_ev.
                         }
                         generalize (IH _ Hlt_r (contxt_term c) br C).
                         intros [Hmtch_r _].
                         apply Hmtch_r in Hin_r.
                         clear Hmtch_r.
                         eauto using match_spec.
                     +++ (* tail_c t tl *)
                         generalize (M_ev_rew_cons_case_tail_ctxt G1 G2 hd c p l).
                         intros [Hsubt Heq].
                         rewrite Heq.
                         intro Hin_cons.
                         apply M_ev_cons_case_tail_contxt_pair_in in Hin_cons.                      
                         inversion Hin_cons as [bl [br [Hb [Hin_l Hin_r] ] ] ].
                         
                         assert(Hlt_l :
                                 matching_tuple_order G1 
                                   (hd, (p, G1)) 
                                   (contxt_term (tail_c hd c), (cp p l, G2))).
                         {matching_tuple_order_build_ev.
                         }
                         generalize (IH _ Hlt_l hd bl C).
                         intros [Hmtch_l _].
                         apply Hmtch_l in Hin_l.
                         clear Hmtch_l.

                         assert(Hlt_r :
                                 matching_tuple_order G1 
                                   (contxt_term c, (list_pat_c l, G1)) 
                                   (ctxt (tail_c hd c), (cp p l, G2))).
                         {matching_tuple_order_build_ev.
                         }
                         generalize (IH _ Hlt_r (contxt_term c) br C).
                         intros [Hmtch_r _].
                         apply Hmtch_r in Hin_r.
                         clear Hmtch_r.
                         eauto using match_spec.
         + (* p = name p *)
           intro Hin.
           apply M_ev_name_case_in in Hin.
           inversion Hin as [b' [Hin' Hunion] ].
           clear Hin.
           assert(Hlt : matching_tuple_order G1 (t, (p, G2)) (t, (name v p, G2))).
           {matching_tuple_order_build_ev.
           }
           apply IH in Hlt.
           generalize (Hlt t b' hole_contxt_c).
           intros [Hmtch _].
           apply Hmtch in Hin'.
           eauto using match_spec.
         + (* p = nt *)
           intro Hin.
           apply M_ev_nt_case_in in Hin.
           inversion Hin as [p [proof [b' [Hin' Hb] ] ] ].
           clear Hin.
           assert(Hlt : matching_tuple_order G1 
                          (t, (p, remove_prod (n, p) G2 proof)) 
                          (t, (nt n, G2))).
           {matching_tuple_order_build_ev.
           }
           apply IH in Hlt.
           generalize (Hlt t b' hole_contxt_c).
           intros [Hmtch _].
           apply Hmtch in Hin'.
           subst.
           eauto using match_spec.
         + (* p = inhole *)
           intro H.
           apply M_ev_inhole_case_in in H.
           inversion H as [C' [subt [g3 [b1 [b2 [proof [Hin_left [Hin_right [Heq_t [Hsubt Hbunion] ] ] ] ] ] ] ] ] ].
           clear H.
           assert(Hlt_p1 : matching_tuple_order G1 
                          (t, (p1, G2)) 
                          (t, (inhole p1 p2, G2))).
           {matching_tuple_order_build_ev.
           }
           apply IH in Hlt_p1.
           generalize (Hlt_p1 subt b1 C').
           intros [_ Hdecom].
           apply Hdecom in Hin_left.
           clear Hlt_p1.

           destruct proof as [ [Heq Heq_C] | Hsubt'].
           -- (* subt = t *)
              assert(Hlt_p2 : matching_tuple_order G1 
                                (t, (p2, G2)) 
                                (t, (inhole p1 p2, G2))).
              {matching_tuple_order_build_ev.
              }
              clear Hdecom.
              apply IH in Hlt_p2.
              clear IH.
              generalize (Hlt_p2 subt b2 C').
              intros [Hmtch _].
              clear Hlt_p2.
              rewrite Heq_C in Hin_left.
              rewrite Heq in Hin_left.
              rewrite Heq in Hin_right.
              apply eq_sym in Heq.
              apply Heq_t in Heq.
              inversion Heq as [Heq_g _].
              rewrite Heq_g in Hin_right.
              apply Hmtch in Hin_right.
              eauto using match_spec.
           -- (* subterm subt t *)
              
              assert(Hlt_p2 : matching_tuple_order G1 
                                (subt, (p2, G1)) 
                                (t, (inhole p1 p2, G2))).
              {matching_tuple_order_build_ev.
              }
              clear Hdecom.
              apply IH in Hlt_p2.
              clear IH.
              generalize (Hlt_p2 subt b2 C').
              intros [Hmtch _].
              clear Hlt_p2.
              assert(Heq_g : g3 = G1).
              {auto.
              }
              rewrite Heq_g in Hin_right.
              apply Hmtch in Hin_right.
              eauto using match_spec.
       * (* decom *)
         Ltac solve_simple :=
           intros [Heq | Hfalse];
           [(* mtch = mtch *)
             inversion Heq;
             subst;
             eauto using decompose_spec
           | (* false *)
             solve[inversion Hfalse
                  | apply in_inv in Hfalse;
                    inversion Hfalse as [Heq | Hfalse'];
                    [(* mtch = mtch *)
                      inversion Heq
                    | (* In nil *)
                      inversion Hfalse']
               ]
           ].

         destruct p as [ l | | l | |  | ].
         + (* lit *)
           intros ev_decom.
           M_ev_reduce.
           destruct t as [ l' | |].
           -- (* lit *)
              simpl.
              destruct (pt.lit_eq_dec l l').
              ++ (* l = l' *)
                 simpl.
                 intros [Heq | Hfalse].
                 ** (* empty = non-empty *)
                    inversion Heq.
                 ** (* ⊥ *)
                    inversion Hfalse.
              ++ (* l <> l' *)
                 simpl.
                 intuition.
           -- (* list *)
              simpl.
              intuition.
           -- (* contxt *)
              simpl.
              intuition.
         + (* hole *)
           intros ev_decom.
           M_ev_reduce.
           destruct t as [ l' | | c ].
           -- (* lit *)
              simpl.
              solve_simple.
           -- (* list *)
              simpl.
              solve_simple.
           -- (* contxt *)
              destruct c as [ | l].
              ++ (* hole *)
                 solve_simple.
              ++ (* list contxt *)
                 destruct l.
                 ** (* hd context *)
                    solve_simple.
                 ** (* tail contxt *)
                    solve_simple.
         + (* list pat *)
           destruct l.
           -- (* nil *)
              intro ev_decom.
              M_ev_reduce.
              destruct t as [ | l | c].
              ++ (* lit *)
                 intro Hin.
                 inversion Hin.
              ++ (* list *)
                 destruct l.
                 ** (* nil *)
                    solve_simple.
                 ** (* list *)
                    intro Hin.
                    inversion Hin.
              ++ (* contxt *)
                 intro Hin.
                 inversion Hin.
           -- (* list *)
              intro ev_decom.
              destruct t as [ | l' | c].
              ++ (* lit *)
                 M_ev_reduce.
                 intuition.
              ++ (* list *)
                 destruct l'.
                 ** (* nil *)
                    M_ev_reduce.
                    intuition.
                 ** (* list *)
                    generalize (M_ev_rew_cons_case G1 G2 t l' p l).
                    intros [Hproof_subt Heq].
                    rewrite Heq.
                    intro Hin_cons.
                    apply M_ev_cons_case_nonempty_pair_in in Hin_cons.
                    
                    inversion Hin_cons as [bl [br [Hb [Hin_l | Hin_r] ] ] ].
                    --- (* empty dec on the left *)
                        inversion Hin_l as [Hin_left [c' [c'' [ev_subt [Hin [Heq_c' Heq_C] ] ] ] ] ].
                        
                        assert(Hlt_l :
                                matching_tuple_order G1 (t, (p, G1)) (ct t l', (cp p l, G2))).
                        {matching_tuple_order_build_ev.
                        }
                        generalize (IH _ Hlt_l t bl C).
                        intros [Hmtch_l _].
                        apply Hmtch_l in Hin_left.
                        clear Hmtch_l.

                        assert(Hlt_r :
                                matching_tuple_order G1 
                                  (list_term_c l', (list_pat_c l, G1)) 
                                  (ct t l', (cp p l, G2))).
                        {matching_tuple_order_build_ev.
                        }
                        generalize (IH _ Hlt_r sub_t br c').
                        intros [_ Hdecom_r].
                        apply (Hdecom_r ev_subt) in Hin.
                        clear Hdecom_r.
                        rewrite Heq_C.
                        rewrite Heq_c' in Hin.
                        eauto using decompose_spec.
                    --- (* non-empty dec on the left *)
                        inversion Hin_r as [c' [ev_subt [Hin_l [Hin_r' Heq_C] ] ] ].
                        
                        assert(Hlt_l :
                                matching_tuple_order G1 (t, (p, G1)) (ct t l', (cp p l, G2))).
                        {matching_tuple_order_build_ev.
                        }
                        generalize (IH _ Hlt_l sub_t bl c').
                        intros [_ Hdecom].
                        apply (Hdecom ev_subt) in Hin_l.
                        clear Hdecom.

                        assert(Hlt_r :
                                matching_tuple_order G1 
                                  (list_term_c l', (list_pat_c l, G1)) 
                                  (ct t l', (cp p l, G2))).
                        {matching_tuple_order_build_ev.
                        }
                        generalize (IH _ Hlt_r l' br c').
                        intros [Hmatch _].
                        apply (Hmatch) in Hin_r'.
                        clear Hmatch.
                        rewrite Heq_C.
                        eauto using decompose_spec.
              ++ (* contxt *)
                 destruct c as [ | l'].
                 ** (* c = hole *)
                    M_ev_reduce.
                    intuition.
                 ** (* c = list c *)
                    destruct l'.
                    --- (* l' = hd *)
                        generalize (M_ev_rew_cons_case_hd_ctxt G1 G2 c l0 p l).
                        intros [Hproof_subt Heq].
                        rewrite Heq.
                        intro Hin_cons.
                        apply M_ev_cons_case_hd_contxt_nonempty_pair_in in Hin_cons.
                        
                        inversion Hin_cons as [bl [br [Hb [Hin_l | Hin_r] ] ] ].
                        +++ (* empty dec on the left *)
                            inversion Hin_l as [Hin_left [c' [c'' [ev_subt [Hin [Heq_c' Heq_C] ] ] ] ] ].
                            
                            assert(Hlt_l :
                                    matching_tuple_order G1 (contxt_term c, (p, G1)) 
                                      (ctxt (hd_c c l0), (cp p l, G2))).
                            {matching_tuple_order_build_ev.
                            }
                            generalize (IH _ Hlt_l c bl C).
                            intros [Hmtch_l _].
                            apply Hmtch_l in Hin_left.
                            clear Hmtch_l.

                            assert(Hlt_r :
                                    matching_tuple_order G1 
                                      (list_term_c l0, (list_pat_c l, G1)) 
                                      (ctxt (hd_c c l0), (cp p l, G2))).
                            {matching_tuple_order_build_ev.
                            }
                            generalize (IH _ Hlt_r sub_t br c').
                            intros [_ Hdecom_r].
                            apply (Hdecom_r ev_subt) in Hin.
                            clear Hdecom_r.
                            rewrite Heq_C.
                            rewrite Heq_c' in Hin.
                            eauto using decompose_spec.
                        +++ (* non-empty dec on the left *)
                            inversion Hin_r as [c' [ev_subt [Hin_l [Hin_r' Heq_C] ] ] ].
                            
                            assert(Hlt_l :
                                    matching_tuple_order G1 
                                      (contxt_term c, (p, G1)) 
                                      (ctxt (hd_c c l0), (cp p l, G2))).
                            {matching_tuple_order_build_ev.
                            }
                            generalize (IH _ Hlt_l sub_t bl c').
                            intros [_ Hdecom].
                            apply (Hdecom ev_subt) in Hin_l.
                            clear Hdecom.

                            assert(Hlt_r :
                                    matching_tuple_order G1 
                                      (list_term_c l0, (list_pat_c l, G1)) 
                                      (ctxt (hd_c c l0), (cp p l, G2))).
                            {matching_tuple_order_build_ev.
                            }
                            generalize (IH _ Hlt_r l0 br c').
                            intros [Hmatch _].
                            apply (Hmatch) in Hin_r'.
                            clear Hmatch.
                            rewrite Heq_C.
                            eauto using decompose_spec.
                    --- (* l' = hd *)
                        generalize (M_ev_rew_cons_case_tail_ctxt G1 G2 t l' p l).
                        intros [Hproof_subt Heq].
                        rewrite Heq.
                        intro Hin_cons.
                        apply M_ev_cons_case_tail_contxt_nonempty_pair_in in Hin_cons.
                        
                        inversion Hin_cons as [bl [br [Hb [Hin_l | Hin_r] ] ] ].
                        +++ (* empty dec on the left *)
                            inversion Hin_l as [Hin_left [c' [c'' [ev_subt [Hin [Heq_c' Heq_C] ] ] ] ] ].
                            
                            assert(Hlt_l :
                                    matching_tuple_order G1 (t, (p, G1)) 
                                      (ctxt (tail_c t l'), (cp p l, G2))).
                            {matching_tuple_order_build_ev.
                            }
                            generalize (IH _ Hlt_l t bl C).
                            intros [Hmtch_l _].
                            apply Hmtch_l in Hin_left.
                            clear Hmtch_l.

                            assert(Hlt_r :
                                    matching_tuple_order G1 
                                      (contxt_term l', (list_pat_c l, G1)) 
                                      (ctxt (tail_c t l'), (cp p l, G2))).
                            {matching_tuple_order_build_ev.
                            }
                            generalize (IH _ Hlt_r sub_t br c').
                            intros [_ Hdecom_r].
                            apply (Hdecom_r ev_subt) in Hin.
                            clear Hdecom_r.
                            rewrite Heq_C.
                            rewrite Heq_c' in Hin.
                            eauto using decompose_spec.
                        +++ (* non-empty dec on the left *)
                            inversion Hin_r as [c' [ev_subt [Hin_l [Hin_r' Heq_C] ] ] ].
                            
                            assert(Hlt_l :
                                    matching_tuple_order G1 
                                      (t, (p, G1)) 
                                      (ctxt (tail_c t l'), (cp p l, G2))).
                            {matching_tuple_order_build_ev.
                            }
                            generalize (IH _ Hlt_l sub_t bl c').
                            intros [_ Hdecom].
                            apply (Hdecom ev_subt) in Hin_l.
                            clear Hdecom.

                            assert(Hlt_r :
                                    matching_tuple_order G1 
                                      (contxt_term l', (list_pat_c l, G1)) 
                                      (ctxt (tail_c t l'), (cp p l, G2))).
                            {matching_tuple_order_build_ev.
                            }
                            generalize (IH _ Hlt_r l' br c').
                            intros [Hmatch _].
                            apply (Hmatch) in Hin_r'.
                            clear Hmatch.
                            rewrite Heq_C.
                            eauto using decompose_spec.
         + (* name *)
           intros ev_decom Hin.
           apply M_ev_name_non_empty_case_in in Hin.
           inversion Hin as [b' [Hin' Hunion] ].
           clear Hin.
           assert(Hlt : matching_tuple_order G1 (t, (p, G2)) (t, (name v p, G2))).
           {matching_tuple_order_build_ev.
           }
           apply IH in Hlt.
           generalize (Hlt sub_t b' C).
           intros [_ Hdecom].
           apply (Hdecom ev_decom) in Hin'.
           eauto using decompose_spec.
         + (* nt *)
           intros ev_decom Hin.
           apply M_ev_nt_non_empty_case_in in Hin.
           inversion Hin as [p [proof [b' [Hin' Hb] ] ] ].
           clear Hin.
           assert(Hlt : matching_tuple_order G1 
                          (t, (p, remove_prod (n, p) G2 proof)) 
                          (t, (nt n, G2))).
           {matching_tuple_order_build_ev.
           }
           apply IH in Hlt.
           generalize (Hlt sub_t b' C).
           intros [_ Hdecom].
           apply (Hdecom ev_decom) in Hin'.
           subst.
           eauto using decompose_spec.
         + (* inhole *)
           intros ev_decom H.
           apply M_ev_inhole_non_empty_case_in in H.
           inversion H as [C' [subt [g3 [C'' [b1 [b2 [proof1 [proof2 [Hin_left [Hin_right [Heq_t [Hsubt [Hbunion Heq_C] ] ] ] ] ] ] ] ] ] ] ] ].
           clear H.
           assert(Hlt_p1 : matching_tuple_order G1 
                          (t, (p1, G2)) 
                          (t, (inhole p1 p2, G2))).
           {matching_tuple_order_build_ev.
           }
           apply IH in Hlt_p1.
           generalize (Hlt_p1 subt b1 C').
           intros [_ Hdecom].
           apply Hdecom in Hin_left.
           clear Hlt_p1.

           destruct proof1 as [ [Heq Heq_C'] | Hsubt'].
           -- (* subt = t *)
              assert(Hlt_p2 : matching_tuple_order G1 
                                (t, (p2, G2)) 
                                (t, (inhole p1 p2, G2))).
              {matching_tuple_order_build_ev.
              }
              clear Hdecom.
              apply IH in Hlt_p2.
              clear IH.
              generalize (Hlt_p2 sub_t b2 C'').
              intros [_ Hdecom].
              clear Hlt_p2.
              rewrite Heq_C' in Hin_left.
              rewrite Heq in Hin_left.
              revert proof2 Hin_right.
              rewrite Heq.
              intros proof2 Hin_right.
              apply eq_sym in Heq.
              apply Heq_t in Heq.
              inversion Heq as [Heq_g _].
              rewrite Heq_g in Hin_right.
              apply (Hdecom proof2) in Hin_right.
              rewrite Heq_C.
              rewrite Heq_C'.
              eauto using decompose_spec.
           -- (* subterm subt t *)
              assert(Hlt_p2 : matching_tuple_order G1 
                                (subt, (p2, G1)) 
                                (t, (inhole p1 p2, G2))).
              {matching_tuple_order_build_ev.
              }
              clear Hdecom.
              apply IH in Hlt_p2.
              clear IH.
              generalize (Hlt_p2 sub_t b2 C'').
              intros [_ Hdecom].
              clear Hlt_p2.
              assert(Heq_g : g3 = G1).
              {auto.
              }
              rewrite Heq_g in Hin_right.
              apply (Hdecom proof2) in Hin_right.
              rewrite Heq_C.
              eauto using decompose_spec.

Qed.

End Soundness.
