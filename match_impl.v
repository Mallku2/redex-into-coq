Require Import 
        Lists.List.

Require Export 
        patterns_terms
        grammar
        match_tads
        wf_rel.

(* Main component of the semantics for "reduction semantics": definition
   of the notion of matching and decomposition *)
Module Matching(pt : PatTermsSymb).
  Import pt.

  Module MatchTads := MatchTads(pt).
  Import MatchTads.

  Module WfRel := WfRel(pt).
  Import WfRel.
  Import WfRel.GrammarLists.

  Section MatchDecomAux.
    (* auxiliary functions from def. of M: select, combined, named  *)
    
    (* *********************************************************** *)
    (* select (fig. 10) for the case of pattern cons of function M *)
    (* *********************************************************** *)
    
    (* evidence for (subterm_rel subt t) for the third equation of select *)
    Lemma subterm1 : forall {t1 t2 t t2' subt : term} {C1 C2 : contxt}
      (eq_ev : subterms t t1 t2)
      (ev_subt : {subt = t2' /\ C1 = hole_contxt_c} + {subterm_rel subt t2'})
      (eqp : t2 = t2'),
      {subt = t /\ C2 = hole_contxt_c} + {subterm_rel subt t}.
    Proof.
      right.
      inversion eq_ev as [ [l [Heq_t2 Heq_ct] ] | 
                           [ [c [l [Heq_t1 [Heq_t2 Heq_t] ] ] ]|
                           [ c [Heq_t2 Heq_t] ] ] ].
      - (* t = ct *)
        inversion ev_subt as [ [H Hhole] | Hsubt].
        + (* subt = t2' *)
          subst.
          eauto using subterm_rel.
        + (* subterm_rel subt t2' *)
          subst.
          eauto using subterm_rel.
      - (* t = ctxt hd *)
        inversion ev_subt as [ [H Hhole] | Hsubt].
        + (* subt = t2' *)
          subst.
          eauto using subterm_rel.
        + (* subt < t2' *)
          subst.
          eauto using subterm_rel.
      - (* t = ctxt tail *)
        inversion ev_subt as [ [H Hhole] | Hsubt].
        + (* subt = t2' *)
          subst.
          eauto using subterm_rel.
        + (* subt < t2' *)
          subst.
          eauto using subterm_rel.
    Defined.
    
    (* evidence (subterm_rel subt t) for the second equation of select *)
    Lemma subterm2 : forall {t1 t2 t t1' subt : term} {C1 C2 : contxt}
      (eq_ev : subterms t t1 t2) (eqp0 : t1 = t1')
      (ev_subt : {subt = t1' /\ C1 = hole_contxt_c} + {subterm_rel subt t1'}),
      {subt = t /\ C2 = hole_contxt_c} + {subterm_rel subt t}.
    Proof.
      right.
      inversion eq_ev as [ [l [Heq_t2 Heq_ct] ] | 
                           [ [c [Heq_t1 Heq_t] ] |
                           [ c [Heq_t2 Heq_t] ] ] ];
        solve[inversion ev_subt as [ [H Hhole] | Hsubt];
              subst;
              eauto using subterm_rel
             | inversion ev_subt as [ [H Hhole] | Hsubt];
               inversion Heq_t as [a [b c'] ];
               subst;
               eauto using subterm_rel].
    Defined.

    (* implementation of select, together with evidence required to argue about 
       the soundness of the returned decomposition *)
    Definition select (t1 : term) (d1 : decom_ev t1) (t2 : term)
                      (d2 : decom_ev t2) (t : term)
                      (eq_ev : subterms t t1 t2) : option (decom_ev t) :=
      match d1 in decom_ev t1' return t1 = t1' -> option (decom_ev t) with
         | empty_d_ev t1' =>
             fun eqp : t1 = t1' =>
               (match d2 in decom_ev t2'
                      return t2 = t2' -> option (decom_ev t) with
                | empty_d_ev t2' =>
                    fun eqp : t2 = t2' =>
                      (* first equation of select *)
                      Some (empty_d_ev t)
                | nonempty_d_ev t2' c subt ev_subt =>
                    fun eqp : t2 = t2' =>
                      (* third equation *)
                      match c as c' return c = c' -> option (decom_ev t) with
                      | hole_contxt_c  =>
                          fun eqp_c : c = hole_contxt_c => 
                            (* impossible case: t2 will always refer to the tail
                               of a list of terms; if we decomposed there, 
                               c should be a list with a hole *)
                            None
                            (* Some (nonempty_d_ev t *)
                            (*         (tail_c t1 (hd_contxt hole_contxt_c nil_term_c)) *)
                            (*         subt *)
                            (*         (* evidence (subterm_rel subt t) for *) *)
                            (*         (* the third equation of select *) *)
                            (*         (subterm1 eq_ev ev_subt eqp) *)

                      | list_contxt_c l =>
                          fun eqp_c : c = list_contxt_c l =>
                            Some (nonempty_d_ev t
                                    (tail_c t1 l)
                                    subt
                                    (* evidence (subterm_rel subt t) for *)
                                    (* the third equation of select *)
                                    (subterm1 eq_ev ev_subt eqp))
                      end eq_refl
                          
                end eq_refl)
         | nonempty_d_ev t1' c subt ev_subt =>
             fun eqp : t1 = t1' =>
               (match d2 in (decom_ev t2') return
                      t2 = t2' -> option (decom_ev t) with
                | empty_d_ev t2' =>
                    fun eqp' : t2 = t2' =>
                      (* second equation *)
                      match t2' as t2'' return t2' = t2'' -> option (decom_ev t) with
                      | lit_term _       =>
                          (* impossible case *)
                          fun _ => Some (empty_d_ev t)

                      | list_term_c t2'' =>
                          fun eqp_t2'' : t2' = list_term_c t2'' =>
                            Some (nonempty_d_ev t
                                    (hd_c c t2'')
                                    subt
                                    (* evidence (subterm_rel subt t) for  *)
                                    (* the second equation of select *)
                                    (subterm2 eq_ev eqp ev_subt)
                              )
                      | contxt_term c'    =>
                          fun eqp_t2'' : t2' = contxt_term c' =>
                            match c' with
                            | hole_contxt_c   =>
                                Some (nonempty_d_ev t
                                        (hd_c c (cons_term_c t2 nil_term_c))
                                        subt
                                        (* evidence (subterm_rel subt t) for  *)
                                        (* the second equation of select *)
                                        (subterm2 eq_ev eqp ev_subt)
                                  )
                            | list_contxt_c l =>
                                Some (nonempty_d_ev t
                                        (hd_c c (list_contxt_2_list_term l))
                                        subt
                                        (* evidence (subterm_rel subt t) for  *)
                                        (* the second equation of Nselect *)
                                        (subterm2 eq_ev eqp ev_subt)
                                  )
                            end
                      end eq_refl
                          
                | _ =>
                    (* fourth equation *)
                    fun eqp' : _ => None
                                   
                end eq_refl)
         end eq_refl.
          
    
    (* ************************* *)
    (* combine (fig. 10) for the case of pattern in-hole of function M *)
    (* ************************* *)

    (* required evidence to argue about the soundness of the decomposition  *)
    (*    returned by combine *)
    Lemma combine_proof : forall {t tc tc' subt : term} {c c' : contxt}
                            (ev_decom_t : {tc = t /\ c = hole_contxt_c} + {subterm_rel tc t})
                            (ev_decom_tc : {subt = tc' /\ c' = hole_contxt_c} + {subterm_rel subt tc'})
                            (eqp : tc = tc'),
        {subt = t /\ context_com c c' = hole_contxt_c} + {subterm_rel subt t}.
    Proof.
      intros.
      inversion ev_decom_tc as [ [Heq Hhole] | Hsubt];
        inversion ev_decom_t as [ [Heq' Hhole'] | Hsubt'];
        subst; eauto using subterm_rel.
    Defined.

    (* implementation of combine, together with evidence required to argue about  *)
    (*    the soundness of the returned decomposition *)
    Definition combine (t : term) (c : contxt) (tc : term)
               (* TODO: abstract this predicate into a definition *)
               (ev_decom_t : {tc = t /\ c = hole_contxt_c} + {subterm_rel tc t})
               (dh : decom_ev tc) : decom_ev t :=
      match dh in (decom_ev tc') return tc = tc' -> (decom_ev t) with
       | empty_d_ev tc' =>
         (* first equation of combine *)
         fun eqp : tc = tc' => empty_d_ev t
       | nonempty_d_ev tc' c' subt ev_decom_tc =>
         (* second equation *)
         fun eqp : tc = tc' =>
           nonempty_d_ev t
             (* {(context_com c c') = c ++ c'} *)
             (context_com c c')
             subt
             (combine_proof ev_decom_t ev_decom_tc eqp)
       end eq_refl.

    (* *************************** *)
    (* named (fig. 10) for the case of pattern name of function M *)
    (* decides naming: if there isn't a decomposition, the name *)
    (*    should be bound with the term; if a decomposition is performed, *)
    (*    the name should be bound with the context. *)
    (* ************************* *)
    Definition named (t : term) (d : decom_ev t) : term :=
      match d with
      (* first equation of named *)
      | empty_d_ev _ => t
      (* second equation *)
      | nonempty_d_ev t' c subt ev_subterm => (contxt_term c)
      end.
    
  End MatchDecomAux.

  (* Performs matching and decomposition simultaneusly *)
  Section MatchDecom.
    
    (* ************************************************************ *)
    (* cons_case_aux:
       aux. function for cons_case (see below): helps to implement recursion over
       the mtch_powset_ev tr
     *)
    Fixpoint cons_case_aux
             (t tl tr : term)
             (eq_ev : subterms t tl tr)
             (mtch_pair_tl : mtch_ev tl)
             (mtch_powset_tr : mtch_powset_ev tr) : 
      mtch_powset_ev t :=
      match mtch_powset_tr  with
      | mtch_pair_tr :: mtch_powset_tr' =>
        (* TODO: cannot do annotated dependent pattern match on mtch_powset_ev *)
        (* values; forced to match against (mtch_ev t) values individually  *)
        (match mtch_pair_tl in (mtch_ev tl')
               return tl = tl' -> (mtch_powset_ev t) with
         | mtch_pair tl' dl bl =>
           fun eqp_tl : tl = tl' =>
             (match mtch_pair_tr in (mtch_ev tr')
                    return tr = tr' -> (mtch_powset_ev t) with
              | mtch_pair tr' dr br =>
                fun eqp_tr : tr = tr' =>
                  (* after the recursive calls for subterms pl and tr, call  *)
                  (* for select over the returned results and construct a proof *)
                  (* of subterms t tl' tr' from subterms t tl tr *)
                  let eq_ev0 : subterms t  tl' tr :=
                      eq_ind tl (fun tl0 : term => subterms t tl0 tr)
                             eq_ev tl' eqp_tl in
                  let eq_ev1 : subterms t  tl' tr' :=
                      eq_ind tr (fun tr0 : term => subterms t tl' tr0)
                             eq_ev0 tr' eqp_tr in
                  match select tl' dl tr' dr t eq_ev1 with
                  | Some d =>
                    (* returned mtch value: decomposition returned by select *)
                    (* plus the union of bindings from both recursive calls *)
                    let union := (b_union bl br) in
                    match union with
                    | None   => 
                        (* matching failed: continue with remaining cases *)
                        cons_case_aux t tl tr eq_ev mtch_pair_tl mtch_powset_tr'

                    | Some b => (mtch_pair t d b) :: cons_case_aux t tl tr eq_ev
                                                      mtch_pair_tl
                                                      mtch_powset_tr'
                    end
                    
                  (* if select does not return a decomposition we continue with 
                     remaining cases *)
                  | None => cons_case_aux t tl tr eq_ev mtch_pair_tl mtch_powset_tr'
                  end
              end eq_refl)
         end eq_refl)
      (* recursive calls returning empty mtch sets *)
      | _ => nil
      end.

    (* ******************************* *)
    (* cons_case:
       performs union of bindings and selection of match/decom for the case 
       of pattern cons, fourth equation of M
       PARAMS:
       t : original term, of the form (k tl tr), for which we are performing 
           matching/decomp
       tl tr : subterms of t 
       eq_ev : evidence showing tl and tr as subterms of t 
       mtch_powset1: result of the recursive call over tl 
       mtch_powset2: result of the recursive call over tr

       RETURNS:
       a (mtch_powset_ev t) with the results of the call to M, cons case
     *)
    Fixpoint cons_case
             (t tl tr : term)
             (eq_ev : subterms t tl tr)
             (mtch_powset1 : mtch_powset_ev tl)
             (mtch_powset2 : mtch_powset_ev tr) : 
      mtch_powset_ev t :=
      match mtch_powset1  with
      | mtch_pair_tl :: mtch_powset1' =>
        cons_case_aux t tl tr eq_ev mtch_pair_tl mtch_powset2 ++
        cons_case t tl tr eq_ev mtch_powset1' mtch_powset2
        
      | _                            => nil
      end.

    (* to be able to reason about cons_case using induction: 
       cons_case is "lineal" over the first set of mtch_decoms  *)
    Lemma cons_case_dist :
      forall (t tl tr : term)
        (eq_ev : subterms t tl tr)
        (mp11 mp12 : mtch_powset_ev tl)
        (mp2 : mtch_powset_ev tr),
        cons_case t tl tr eq_ev (mp11 ++ mp12) mp2 =
        (cons_case t tl tr eq_ev mp11 mp2) ++ (cons_case t tl tr eq_ev mp12 mp2).
    Proof.
      intros t tl tr eq_ev mp11 mp12 mp2.
      induction mp11 as [| hmp11 tlmp11 IHtlmp11].
      + (* mp11 = nil *)
        reflexivity.
      + (* mp1 = htlmp11 tltlmp11 *)
        destruct hmp11.
        simpl.
        rewrite IHtlmp11.
        rewrite app_assoc.
        reflexivity.
    Qed.

    (* cons_case_aux_dist is linear over the second set of match_decom results *)
    Lemma cons_case_aux_dist :
      forall (t tl tr : term)
        (eq_ev : subterms t tl tr)
        (mp1 mp2 : mtch_powset_ev tr)
        (elem1 : mtch_ev tl)
        (elem2 : mtch_ev tr),
        cons_case_aux t tl tr eq_ev elem1 (mp1 ++ elem2 :: mp2) =
        cons_case_aux t tl tr eq_ev elem1 mp1 ++
                      cons_case_aux t tl tr eq_ev elem1 (elem2 :: mp2).
    Proof.
      intros t tl tr eq_ev mp1 mp2 elem1 elem2.
      induction mp1 as [ | hdmp1 tlmp1 IH].
      - (* mp1 = nil *)
        reflexivity.
      - (* mp1 = hdmp1 tlmp1 *)
        destruct elem1 as [tl'].
        remember (mtch_pair tl' d b) as elem1 eqn : Heq_elem1.
        rewrite Heq_elem1.
        destruct elem2 as [tr' d0 b0].
        remember (mtch_pair tr' d0 b0) as elem2 eqn : Heq_elem2.
        rewrite Heq_elem2.
        destruct hdmp1 as [tr' d1 b1].
        remember (mtch_pair tr' d1 b1) as elem2' eqn : Heq_elem2'.
        rewrite Heq_elem2'.

        simpl.
        destruct (select tl' d tr' d1 t eq_ev) as [d2 | ].
        + (* select tl' d tr' d1 (ct tl' tr') eq_ev = Some d2 *)
          destruct (b_union b b1) as [b2 |].
          -- (* (b_union b b1) = some b2 *)
             remember (select tl' d tr' d0 t eq_ev)
              as select1 eqn : Heq_select1.
             destruct select1 as [d3 | ].
             ++ (* select1 = Some d3 *)
                remember (b_union b b0) as bunion1 eqn : Heq_bunion1.
                destruct bunion1 as [b3 | ].
                --- (* bunion1 = Some b3 *)
                    rewrite <- Heq_elem1.
                    rewrite <- Heq_elem2.
                    rewrite IH.
                    rewrite app_comm_cons.
                    
                    rewrite Heq_elem1.
                    rewrite Heq_elem2.
                    
                    simpl.
                    rewrite <- Heq_select1.
                    rewrite <- Heq_bunion1.
                    reflexivity.
                --- (* bunion1 = None *)
                    rewrite <- Heq_elem1.
                    rewrite <- Heq_elem2.
                    rewrite IH.
                    rewrite app_comm_cons.
                    
                    rewrite Heq_elem1.
                    rewrite Heq_elem2.
                    
                    simpl.
                    rewrite <- Heq_select1.
                    rewrite <- Heq_bunion1.

                    reflexivity.
             ++ (* select1 = None *)
                rewrite <- Heq_elem1.
                rewrite <- Heq_elem2.
                rewrite IH.
                rewrite app_comm_cons.
                
                rewrite Heq_elem1.
                rewrite Heq_elem2.
                
                simpl.
                rewrite <- Heq_select1.
                reflexivity.
          -- (* (b_union b b1) = None *)
             remember (select tl' d tr' d0 t eq_ev)
              as select1 eqn : Heq_select1.
             destruct select1 as [d3 | ].
             ++ (* select1 = Some d3*)
                remember (b_union b b0) as bunion1 eqn : Heq_bunion1.
                destruct bunion1 as [b3 | ].
                --- (* bunion1 = Some b3 *)
                    rewrite <- Heq_elem1.
                    rewrite <- Heq_elem2.
                    rewrite IH.
                    
                    rewrite Heq_elem1.
                    rewrite Heq_elem2.
                    
                    simpl.
                    rewrite <- Heq_select1.
                    rewrite <- Heq_bunion1.
                    reflexivity.
                --- (* bunion1 = None *)
                    rewrite <- Heq_elem1.
                    rewrite <- Heq_elem2.
                    rewrite IH.
                    
                    rewrite Heq_elem1.
                    rewrite Heq_elem2.
                    
                    simpl.
                    rewrite <- Heq_select1.
                    rewrite <- Heq_bunion1.
                    reflexivity.
             ++ (* select1 = None *)
                rewrite <- Heq_elem1.
                rewrite <- Heq_elem2.
                rewrite IH.
                    
                rewrite Heq_elem1.
                rewrite Heq_elem2.
                    
                simpl.
                rewrite <- Heq_select1.
                reflexivity.
        + (* select tl' d tr' d1 (ct tl' tr') eq_ev = None *)
          remember (select tl' d tr' d0 t eq_ev)
            as select1 eqn : Heq_select1.
          destruct select1 as [d2 | ].
          -- (* select1 = Some d2*)
             remember (b_union b b0) as bunion1 eqn : Heq_bunion1.
             destruct bunion1 as [b2 | ];
               rewrite <- Heq_elem1;
               rewrite <- Heq_elem2;
               rewrite IH;
             
               rewrite Heq_elem1;
               rewrite Heq_elem2;
               
               simpl;
               rewrite <- Heq_select1;
               rewrite <- Heq_bunion1;
               reflexivity.
          -- (* select1 = None *)
             rewrite <- Heq_elem1.
             rewrite <- Heq_elem2.
             rewrite IH.
             
             rewrite Heq_elem1.
             rewrite Heq_elem2.
                    
             simpl.
             rewrite <- Heq_select1.
             reflexivity.
    Qed.
    
    Lemma cons_case_dist_unfold:
      forall (t tl tr : term)
        (eq_ev : subterms t tl tr)
        (elem1 : mtch_ev tl)
        (elem2 : mtch_ev tr)
        (mp1 : mtch_powset_ev tl)
        (mp21 mp22 : mtch_powset_ev tr),
        
      exists (res : mtch_powset_ev t),
        cons_case t tl tr eq_ev (elem1 :: mp1) (mp21 ++ elem2 :: mp22) =
        res ++ cons_case_aux t tl tr eq_ev elem1 (elem2 :: mp22) ++
            cons_case t tl tr eq_ev mp1 (mp21 ++ elem2 :: mp22).
    Proof.
      intros t tl tr eq_ev elem1 elem2 mp1 mp21 mp22.

      destruct elem1 as [tl'].
      remember (mtch_pair tl' d b) as elem1 eqn : Heq_elem1.
      rewrite Heq_elem1.
      destruct elem2 as [tr'].
      remember (mtch_pair tr' d0 b0) as elem2 eqn : Heq_elem2.
      rewrite Heq_elem2.

      
      destruct mp21 as [ | hdmp21 tlmp21].
      + (* mp21 = nil *)
        remember (nil ++ mtch_pair tr' d0 b0 :: mp22) as mp22l eqn : Heq_mp22l.
        simpl in Heq_mp22l.
        rewrite Heq_mp22l.
        clear Heq_mp22l.
        unfold cons_case.
        fold cons_case.
        exists nil.
        reflexivity.
            
      + (* mp21 = hdmp21 tlmp21 *)
        destruct hdmp21 as [tr'' d1 b1].
        unfold cons_case.
        fold cons_case.
        rewrite (cons_case_aux_dist t tl' tr'' eq_ev
                                    (mtch_pair tr'' d1 b1 :: tlmp21)
                                    mp22
                                    (mtch_pair tl' d b)
                                    (mtch_pair tr'' d0 b0)).
        
        remember (cons_case_aux t tl' tr'' eq_ev (mtch_pair tl' d b)
                                (mtch_pair tr'' d1 b1 :: tlmp21)) as l1.

        remember (cons_case_aux t tl' tr'' eq_ev (mtch_pair tl' d b)
                                (mtch_pair tr'' d0 b0 :: mp22)) as l2.

        remember (cons_case t tl' tr'' eq_ev mp1
                            ((mtch_pair tr'' d1 b1 :: tlmp21)
                               ++ mtch_pair tr'' d0 b0 :: mp22)) as l3.

        exists l1.
        rewrite app_assoc.
        reflexivity.
    Qed.          
                
    (* ******************************* *)
    (* inhole_case *)
    (* ******************************* *)

    (* evidence required by call to combine *) 
      
    Lemma inhole_eq1 :  
      forall (t t''' : term)(c : contxt), 
        t = t'''          -> 
        c = hole_contxt_c ->
        {t''' = t /\ c = hole_contxt_c} + {subterm_rel t''' t}.
    Proof.
      auto.
    Defined.
    
    (* evidence of soundness of subterm in a decom of t *)
    Lemma inhole_eq2 : 
      forall {t t'' tc : term}
        {c : contxt}
        (eqp'' : t = t'')
        (proof_subt : subterm_rel tc t''),
        {tc = t /\ c = hole_contxt_c} + {subterm_rel tc t}.
    Proof.
      right.
      rewrite eqp''.
      exact proof_subt.
    Defined.

    (* soundness decom tc *)
    Lemma inhole_subterm : 
      forall tc tc'
        (eqp''' : tc = tc')
        (dh : decom_ev tc'), decom_ev tc.
    Proof.
      intros.
      rewrite eqp'''.
      exact dh.
    Defined.

    (* decreasing size rec. call right param. *)
    Lemma rec_call_right_pat_decre :
      forall (t t'' : term) (pc ph : pat) (g1 g2 : grammar)
        (tc : term) (eqp' : t = t'') (s : subterm_rel tc t''), 
        matching_tuple_order g1 (tc, (ph, g1)) (t, (inhole_pat pc ph, g2)).
    Proof.
      intros.
      rewrite <- eqp' in s.
      matching_tuple_order_build_ev.
    Defined.

    (* fifth equation of M, case in-hole: combines contexts and union of 
       bindings 
       PARAMS:
       t : original term for which we are performing matching/decomp
       pc ph : sub-patterns of the pattern (in-hole pc ph) against which 
       matching/decom is performed 
       g1 : original grammar under which matching/decom is performed 
       g2 : productions from g1 that left to be considered, if under a process of
       pattern expansion and no input consumption
       b : boolean indicating if under input consumption (b = true) or just 
       pattern expansion (b = false)
       M' : original matching/decom function
       
       RETURNS:
       a (mtch_powset_ev t) with the results of the call to M, in-hole case
       *)
    Definition inhole_case
               (t : term)
               (pc ph : pat)
               (g1 g2 : grammar)
               (M' : 
                 forall (tpg2 : matching_tuple),
                   matching_tuple_order g1 tpg2 (t, (inhole_pat pc ph, g2)) ->
                   mtch_powset_ev (matching_tuple_term tpg2)) :
      mtch_powset_ev t :=
       fold_left 
         (* (@app mtch) : ++ with type 
              list  mtch -> list mtch -> list mtch *)
         (@app (mtch_ev t))
         (* iteration over the result of the recursive call over 
              (pc, t) *)
         (map 
            (fun mtch1 : (mtch_ev t) =>
               match mtch1 in (mtch_ev t') 
                     return t = t' -> (mtch_powset_ev t) with
               | mtch_pair t' dec_t bc =>
                   fun eqp' : t = t' =>
                     (match dec_t in (decom_ev t'') return
                            t = t'' -> (mtch_powset_ev t) with
                      | nonempty_d_ev t'' c tc ev_tc_subt =>
                          fun eqp'': t = t'' =>
                            match ev_tc_subt with
                            | left (conj Heq_t Heq_con) =>
                                (*  pattern pc generates hole, hence tc = t: 
                                recursive call over M(ph, t), for every ph
                                returned by call to M(pc, t) *)
                                fold_left
                                  (* (@app mtch) : ++ with type  *)
                                  (* list mtch ->    list mtch -> list mtch *)
                                  (@app (mtch_ev t))
                                  (map
                                     (fun mtch2 : mtch_ev t =>
                                        (match mtch2 in (mtch_ev t''') return 
                                               t = t''' -> (mtch_powset_ev t)
                                         with
                                         | mtch_pair t''' dh bh =>
                                             fun eqp''' : t = t''' =>
                                               let union := (b_union bc
                                                               bh) in
                                               match union with
                                               | None => nil (* match failed  *)
                                               | Some b    =>
                                                   (mtch_pair 
                                                      t 
                                                      (* decom returned by call to 
                                                (M, in-hole)  *)
                                                      (combine t c t'''
                                                         (* evidence of {tc = t} +
                                                         {subterm_rel tc t} *)  
                                                         (inhole_eq1 t t''' c eqp''' Heq_con)
                                                         dh) 
                                                      b) :: nil
                                               end
                                         end eq_refl)
                                     )
                                     (* pat_gen_hole pc g1 => recursive call over 
                                   (ph, t), no consumption of input, same  
                                   grammar g2 *)
                                     (M' (t, (ph, g2))
                                        (matching_tuple_order_pat_evol g1 t
                                           (ph, g2) 
                                           (inhole_pat pc ph, g2)
                                           (pat_grammar_evolution_inhole_right 
                                              g2 pc ph)))
                                  )
                                  nil
                            | right proof_subt =>
                                (*  pattern pc does not generate hole, hence 
                                subterm_rel tc t: 
                                recursive call over M(ph, tc), for every ph
                                returned by call to M(pc, t) *)
                                fold_left
                                  (* (@app mtch) : ++ with type  *)
                                  (* list mtch ->    list mtch -> list mtch *)
                                  (@app (mtch_ev t))
                                  (map
                                     (fun mtch2 : mtch_ev tc =>
                                        (match mtch2 in (mtch_ev tc') return 
                                               tc = tc' -> (mtch_powset_ev t)
                                         with
                                         | mtch_pair tc' dh bh =>
                                             fun eqp''' : tc = tc' =>
                                               let union := (b_union bc
                                                               bh) in
                                               match union with
                                               | None      => nil
                                               | Some b    => 
                                                   (mtch_pair 
                                                      t
                                                      (* decom returned by call to 
                                               (M, in-hole)  *)      
                                                      (combine t c tc 
                                                         (* evidence of {tc = t} + 
                                                        {subterm_rel tc t} *)
                                                         (inhole_eq2 eqp'' 
                                                            proof_subt)
                                                         (inhole_subterm tc tc'
                                                            eqp''' dh))
                                                      b) :: nil
                                               end
                                         end eq_refl))
                                     (* recursive call over (ph, tc), consumption 
                                    of input *)
                                     (M' (tc, (ph, g1))
                                        (rec_call_right_pat_decre t t'' pc ph g1 g2
                                           tc eqp'' 
                                           proof_subt)))
                                  nil
                            end
                      | _ => fun eqp : _ => nil
                      end
                        (* ev. that t = t' *)
                        eqp')
               end eq_refl)
            (* recursive call over (pc, t) *)
            (M' (t, (pc, g2))
               (matching_tuple_order_pat_evol
                  g1 t (pc, g2) (inhole_pat pc ph, g2)
                  (pat_grammar_evolution_inhole_left g2 pc ph))))
         nil.
    
    (* *********************************************************** *)
    (* name_case *)
    (* *********************************************************** *)
    (* for a term t and pattern name x p, given the mtch_ps from the recursive 
       call over p, name_case performs the remaining steps from the equation of 
       M for name pattern *)
    Program Fixpoint name_case (t : term) (mtch_ps : mtch_powset_ev t) 
                               (x : var) : 
      mtch_powset_ev t :=
      match mtch_ps with
      | nil => nil
      | mtch_p :: mtch_ps' =>
        match mtch_p in (mtch_ev t') return t = t' -> mtch_powset_ev t
        with
        | (mtch_pair t' d b)  =>
            fun eqp : t = t' =>
              (* construct a proof of decom_ev t from decom_ev t' *)
              let dec_ev_t := eq_rec t' decom_ev d t (eq_sym eqp) in
              let union := b_union ((x, (named t dec_ev_t)) :: nil) b in
              match union with
              | None   => (* match failed: continue with remaining cases *)
                  (name_case t mtch_ps' x)
              | Some b => (mtch_pair t dec_ev_t b) 
                           :: name_case t mtch_ps' x
              end
        end eq_refl
      end.
    

    (* ******************************* *)
    (* nt_case *)
    (* ******************************* *)
    (* seventh equation of M, case nt
       PARAMS:
       g1 : original grammar under which matching/decom is performed
       g2 : productions from g1 that left to be considered, if under a process of
       pattern expansion and no input consumption
       n : non-term from pattern nt
       t : original term for which we are performing matching/decomp
       M' : original matching/decom function
       
       RETURNS:
       a (mtch_powset_ev t) with the results of the call to M, nt case, under
       pattern expansion considering the remaining productions g2 from g1 *)
    Definition nt_case (g1 g2 : grammar) (n : nonterm) (t : term)  
               (M' : forall (tpg2 : matching_tuple),
                   matching_tuple_order g1 tpg2 (t, (nt_pat n, g2)) ->
                   mtch_powset_ev (fst tpg2)) : mtch_powset_ev t :=
      fold_left 
        (* (@app mtch) : ++ with type list mtch -> list mtch -> *)
        (* list mtch *)
        (@app (mtch_ev t))
        (map (fun pat_proof : {p : pat | prod_in_g (n, p) g2} =>
                (map (fun m : mtch_ev t
                      => match m with
                        | mtch_pair _ d b =>
                            mtch_pair _ d nil
                        end)
                   (* Recursive call *)
                   (* _ in the call to M should be the proof *)
                   (* of In (fst pat_term) (get_rhs G n) *)
                   (* to show that *)
                   (* to_left G pat_term ((nt_pat n), t1) *)
                   match pat_proof with
                   | exist _ pat proof =>
                       M' (t, (pat, remove_prod (n, pat) g2 proof))
                          (* Proof that tpg2 < tpg1 *)
                          (matching_tuple_order_pat_evol 
                             g1 t
                             (pat, remove_prod (n, pat) g2 proof)
                             (nt_pat n, g2)
                             (pat_grammar_evolution_nt g2 pat n proof))
                   end))
           (get_rhs g2 n))
        nil.

    (* ************************************************************ *)
    (* actual returned match/decom pairs for each case of the 
       function M (fig. 10) *)
    (* ************************************************************ *)
    (* first equation of M *)
    Lemma Mev_first_eq : 
      forall (tpg1 : matching_tuple)
        (g1 g2 : grammar)
        (eqp : matching_tuple_inverted tpg1 = ((hole_pat, g2), hole)),
        mtch_powset_ev (matching_tuple_term tpg1).
    Proof.
      intros.
      unfold matching_tuple_inverted in eqp.
      inversion eqp as [ [Heq_snd Heq_fst ] ].
      assert(Hsubt: {hole = hole /\ hole_contxt_c = hole_contxt_c} + {subterm_rel hole hole}).
      {auto.
      }
      rewrite Heq_fst.
      (* returned values *)
      apply (cons (mtch_pair hole
                             (* ((hole, hole), ∅) *)
                             (nonempty_d_ev
                                hole
                                hole_contxt_c
                                hole
                                Hsubt
                             )
                          nil)
                  (cons (mtch_pair
                           hole
                           (* (∙, ∅) *)
                           (empty_d_ev hole)
                           nil)
                    nil)).
      Defined.

    (* second equation *)
    Lemma Mev_second_eq : 
      forall (tpg1 : matching_tuple) 
        (g1 g2 : grammar) 
        (t : term) 
        (eqp : matching_tuple_inverted tpg1 = ((hole_pat, g2), t)),
        mtch_powset_ev (matching_tuple_term tpg1).
    Proof.
      intros.
      unfold matching_tuple_inverted in eqp.
      inversion eqp as [ [Heq_snd Heq_fst ] ].
      rewrite Heq_fst.
      assert({t = t /\ hole_contxt_c = hole_contxt_c} + {subterm_rel t t}).
      {auto.
      }
      apply (cons (mtch_pair t
                             (* returned value: ((hole, t), ∅) *)
                             (nonempty_d_ev t hole_contxt_c t H)
                             nil)
                  nil).
    Defined.

    (* third equation *)
    Lemma Mev_third_eq : 
      forall (tpg1 : matching_tuple) 
        (g1 g2 : grammar) 
        (li1 li2 : lit) 
        (eqp : matching_tuple_inverted tpg1 = ((lit_pat li1, g2), lit_term li2)),
        mtch_powset_ev (matching_tuple_term tpg1).
    Proof.
      intros.
      unfold matching_tuple_inverted in eqp.
      inversion eqp as [ [Heq_snd Heq_fst ] ].
      rewrite Heq_fst.
      destruct (lit_eq_dec li1 li2). 
      (* returned values *)
      + (* li1 = li2 *)
        (* there is a match *)
        apply (cons (mtch_pair (lit_term li2)
                               (* case same literals: (∙, ∅) *)
                               (empty_d_ev (lit_term li2))
                               nil)
                    nil).
      + (* li1 <> li2 *)
        (* no match *)
        apply nil.
    Defined.

    (* fourth equation *)
    Definition build_subterm_proof (tr : term) (tl : list_term) : subterms (ct tr tl) tr tl.
      unfold subterms.
      eauto.
    Defined.
      
    Lemma Mev_fourth_eq : 
      forall (g1 g2 : grammar)
        (tpg1 : matching_tuple)
        (Mev2 : 
          forall tpg2 : matching_tuple,
            matching_tuple_order g1 tpg2 tpg1 ->
            mtch_powset_ev (matching_tuple_term tpg2))
        (pl : pat) (pr : list_pat) (tl : term) (tr : list_term)
        (eqp1 : matching_tuple_inverted tpg1 = 
                ((cp pl pr, g2), ct tl tr)),
        mtch_powset_ev (matching_tuple_term tpg1).
    Proof.
      intros.
      unfold matching_tuple_inverted in eqp1.
      inversion eqp1 as [ [Heq_snd Heq_fst] ].
      rewrite Heq_fst.

      (* recursive call over left pattern *)
      assert(Hrel_l : matching_tuple_order g1
                        (tl, (pl, g1))
                        (ct tl tr, (cp pl pr, g2))).
      {matching_tuple_order_build_ev.
      }

      reconstruct_tuple tpg1 eqp1 Heq.

      rewrite Heq.
      simpl.
      rewrite Heq in Mev2.
      assert(mtch_tl : mtch_powset_ev tl).
      {apply (Mev2 (tl, (pl, g1)) Hrel_l).
      }
      
      (* recursive call over right pattern *)
      assert(Hrel_r : matching_tuple_order g1
                      (list_term_c tr, (list_pat_c pr, g1))
                      (ct tl tr, (cp pl pr, g2))).
      {matching_tuple_order_build_ev.
      }

      assert(mtch_tr : mtch_powset_ev tr).
      {apply (Mev2 (list_term_c tr, (list_pat_c pr, g1)) Hrel_r).
      }
      
      assert(Hsub: subterms (ct tl tr) tl tr).
      {unfold subterms.
       eauto.
      }

      apply (cons_case (ct tl tr) tl tr Hsub mtch_tl mtch_tr).
    Defined.

    (* fourth equation, left context case *)
    Lemma Mev_fourth_eq_l_context : 
      forall (tpg1 : matching_tuple)
        (g1 g2 : grammar)
        (Mev2 : forall tpg2 : matching_tuple,
            matching_tuple_order g1 tpg2 tpg1 ->
            mtch_powset_ev (matching_tuple_term tpg2))
        (pl : pat) (pr : list_pat) (C : contxt) (tr : list_term)
        (eqp1 : matching_tuple_inverted tpg1 = 
                ((cp pl pr, g2), contxt_term (hd_c C tr))),
        mtch_powset_ev (matching_tuple_term tpg1).
    Proof.
      intros tpg1 g1 g2 Mev2  pl pr C tr eqp1.
      unfold matching_tuple_inverted in eqp1.
      inversion eqp1 as [ [Heq_snd Heq_fst ] ].
      reconstruct_tuple tpg1 eqp1 Heq_tup1.
      rewrite Heq_tup1 in Mev2.
      

      (* evidence that we are following the wf rel *)
      assert(Hrel_l : matching_tuple_order g1
                        (contxt_term C, (pl, g1))
                        (ctxt hd_c C tr, (cp pl pr, g2))).
      {matching_tuple_order_build_ev.
      }
      
      (* recursive call over left pattern *)
      assert(mpset_C : mtch_powset_ev (ctxt C)).
      {apply (Mev2 (ctxt C, (pl, g1)) Hrel_l).
      }

      (* evidence that we are following the wf rel *)
      assert(Hrel_r : matching_tuple_order g1
                        (list_term_c tr, (list_pat_c pr, g1))
                        (ctxt (hd_c C tr), (cp pl pr, g2))).
      {matching_tuple_order_build_ev.
      }

      (* recursive call over right pattern *)
      assert(mpset_tr : mtch_powset_ev tr).
      {apply (Mev2 (list_term_c tr, (list_pat_c pr, g1)) Hrel_r).
      }
      
      assert(Hsub: subterms (ctxt hd_c C tr) (ctxt C) (list_term_c tr)).
      {unfold subterms.
       right.
       left.
       eauto.
      }

      rewrite Heq_fst.
      
      (* call cons_case to combine results *)
      apply (cons_case (ctxt (hd_c C tr)) (ctxt C) tr Hsub mpset_C
                       mpset_tr).
    Defined.

        (* fourth equation, right context case *)
    Lemma Mev_fourth_eq_r_context : 
      forall (tpg1 : matching_tuple)
        (g1 g2 : grammar)
        (Mev2 : forall tpg2 : matching_tuple,
            matching_tuple_order g1 tpg2 tpg1 ->
            mtch_powset_ev (matching_tuple_term tpg2))
        (pl : pat) (pr : list_pat) (tl : term) (C : list_contxt)
        (eqp1 : matching_tuple_inverted tpg1 = 
                ((cp pl pr, g2), contxt_term (tail_c tl C))),
        mtch_powset_ev (matching_tuple_term tpg1).
    Proof.
      intros tpg1 g1 g2 Mev2 pl pr tl C eqp1.
      unfold matching_tuple_inverted in eqp1.
      inversion eqp1 as [ [Heq_snd Heq_fst ] ].
      reconstruct_tuple tpg1 eqp1 Heq_tup1.
      rewrite Heq_tup1 in Mev2.
      

      (* evidence that we are following the wf rel *)
      assert(Hrel_l : matching_tuple_order g1
                        (tl, (pl, g1))
                        (contxt_term (tail_c tl C), (cp pl pr, g2))).
      {matching_tuple_order_build_ev.
      }
      
      (* recursive call over left pattern *)
      assert(mpset_tl : mtch_powset_ev tl).
      {apply (Mev2 (tl, (pl, g1)) Hrel_l).
      }

      (* evidence that we are following the wf rel *)
      assert(Hrel_r : matching_tuple_order g1
                        (contxt_term (list_contxt_c C), (list_pat_c pr, g1))
                        (contxt_term (tail_c tl C), (cp pl pr, g2))).
      {matching_tuple_order_build_ev.
      }

      (* recursive call over right pattern *)
      assert(mpset_C : mtch_powset_ev (contxt_term (list_contxt_c C))).
      {apply (Mev2 (contxt_term (list_contxt_c C), (list_pat_c pr, g1)) Hrel_r).
      }
      
      assert(Hsub: subterms (ctxt tail_c tl C) tl (ctxt C)).
      {unfold subterms.
       eauto using subterm_rel.
      }

      rewrite Heq_fst.
      
      (* call cons_case to combine results *)
      apply (cons_case (ctxt tail_c tl C) tl (ctxt C) Hsub mpset_tl
                       mpset_C).
    Defined.

    (* fifth equation *)
    Lemma Mev_fifth_eq :
      forall (tpg1 : matching_tuple)
        (g1 g2 : grammar)
        (Mev2 : forall tpg2 : matching_tuple,
            matching_tuple_order g1 tpg2 tpg1 ->
            mtch_powset_ev (matching_tuple_term tpg2))
        (t : term) (pc ph : pat)
        (eqp : matching_tuple_inverted tpg1 = ((inhole_pat pc ph, g2), t)),
        mtch_powset_ev (matching_tuple_term tpg1).
    Proof.
      intros tpg1 g1 g2 Mev2 t pc ph eqp.
      unfold matching_tuple_inverted in eqp.
      inversion eqp as [ [Heq_snd Heq_fst ] ].
      reconstruct_tuple tpg1 eqp Heq_tup1.
      rewrite Heq_tup1 in Mev2.
      rewrite Heq_fst.
      apply (inhole_case t pc ph g1 g2 Mev2).
    Defined.

    (* sixth equation *)
    Lemma Mev_sixth_eq_rel : 
      forall (tpg : matching_tuple)
        (g1 g2 : grammar) (t : term) (x : var)
        (p : pat) 
        (eqp : matching_tuple_inverted tpg = 
               ((name_pat x p, g2), t)),
        matching_tuple_order g1 (t, (p, g2)) tpg.
    Proof.
      intros.
      inversion eqp as [ [Heq_snd Heq_fst ] ].
      reconstruct_tuple tpg eqp Heq_tup1.
      rewrite Heq_fst.
      rewrite Heq_tup1.
      matching_tuple_order_build_ev.
    Defined.

    Lemma Mev_sixth_eq_trans2 : 
      forall (tpg1 : matching_tuple)
        (g1 g2 : grammar) (t : term) (p : pat) (x : var)
        (eqp : matching_tuple_inverted tpg1 = ((name_pat x p, g2), t))
        (mtch_set : mtch_powset_ev (matching_tuple_term (t, (p, g2)))),
        mtch_powset_ev (matching_tuple_term tpg1).
    Proof.
      intros.
      inversion eqp as [ [Heq_snd Heq_fst ] ].
      rewrite Heq_fst.
      exact mtch_set.
    Defined.

    Lemma Mev_sixth_eq_trans : 
      forall (tpg1 : matching_tuple) (t : term) (p : pat) (x : var) (g1 g2 : grammar)
        (eqp : matching_tuple_inverted tpg1 = ((name_pat x p, g2), t))
        (ev : pat_grammar_evolution (p, g2) (name_pat x p, g2)),
        pat_grammar_evolution (p, g2) (matching_tuple_pat_grammar tpg1).
    Proof.
      intros.
      inversion eqp as [ [Heq_snd Heq_fst ] ].
      rewrite Heq_snd.
      exact ev.
    Defined.
    
    (* seventh equation *)
    Lemma Mev_seventh_eq_trans :
      forall (tpg1 : matching_tuple)
        (g1 g2 : grammar)
        (Mev2 : forall tpg2 : matching_tuple,
            matching_tuple_order g1 tpg2 tpg1 -> 
            mtch_powset_ev (matching_tuple_term tpg2))
        (t : term) (n : nonterm)
        (eqp : matching_tuple_inverted tpg1 = ((nt_pat n, g2), t)),
        (forall tpg2 : matching_tuple,
            matching_tuple_order g1 tpg2 (t, (nt_pat n, g2)) ->
            mtch_powset_ev (matching_tuple_term tpg2)).
    Proof.
      intros tpg1 g1 g2 Mev2 t n eqp.
      reconstruct_tuple tpg1 eqp Heq_tup1.
      inversion eqp as [ [Heq_snd Heq_fst ] ].
      rewrite Heq_tup1 in Mev2.
      rewrite Heq_fst.
      rewrite Heq_snd.
      exact Mev2.
    Defined.

    Lemma eq_proof : 
      forall p g2 t (tpg1 : matching_tuple)
        (eqp : matching_tuple_inverted tpg1 = ((p, g2), t)),
        t = matching_tuple_term tpg1.
    Proof.
      intros p g2 t tpg1 eqp.
      inversion eqp as [ [Heq_snd Heq_fst ] ].
      reflexivity.
    Defined.

    Lemma Mev_eighth_eq : 
      forall (tpg1 : matching_tuple)
        (g1 g2 : grammar)
        (eqp : matching_tuple_inverted tpg1 = 
               ((list_pat_c nil_pat_c, g2), list_term_c nil_term_c)),
        mtch_powset_ev (matching_tuple_term tpg1).
    Proof.
      intros.
      unfold matching_tuple_inverted in eqp.
      inversion eqp as [ [Heq_snd Heq_fst ] ].
      rewrite Heq_fst.

      (* there is a match *)
      apply (cons (mtch_pair (list_term_c nil_term_c)
                     (* case same literals: (∙, ∅) *)
                     (empty_d_ev (list_term_c nil_term_c))
                     nil)
               nil).
      Defined.

    Definition Mev_gen :=
      (fun (g1 : grammar)
         (tpg1 : matching_tuple)
         (Mev2 : forall tpg2 : matching_tuple,
             matching_tuple_order g1 tpg2 tpg1 ->
             mtch_powset_ev (matching_tuple_term tpg2)) =>
         match matching_tuple_inverted tpg1 as tpg1'
               (* changing order of members of tpg1, to obtain a  *)
               (* function that matches, first, over the pattern: it *)
               (* helps in obtaining shorter proofs *)
               (* (observe the equation for the cons pat case) *)
               return matching_tuple_inverted tpg1 = tpg1' ->
                      mtch_powset_ev (matching_tuple_term tpg1)
         with
         | ((hole_pat, g2), contxt_term hole_contxt_c) =>
             fun eqp : matching_tuple_inverted tpg1 =
                       ((hole_pat, g2), contxt_term hole_contxt_c) =>
               (* TODO: cannot convince type checker by mean of match  *)
               (* annotations; forced to introduce the return exp. in  *)
               (* proof mode *)
               Mev_first_eq tpg1 g1 g2 eqp
                 
         (* the hole decomposition rule decomposes any term t  *)
         (* into the empty context and t itself. *)
         | ((hole_pat, g2), t) =>
             fun eqp : matching_tuple_inverted tpg1 =
                       ((hole_pat, g2), t) =>
               Mev_second_eq tpg1 g1 g2 t eqp
                 
         (* TODO: pattern that forces 2 occurrences of the same  *)
         (*    literal li? *)
         | ((lit_pat li1, g2), lit_term li2) =>
             fun eqp : matching_tuple_inverted tpg1 =
                       ((lit_pat li1, g2), lit_term li2) =>
               Mev_third_eq tpg1 g1 g2 li1 li2 eqp
                 
         | ((cp pl pr, g2), ct tl tr) =>
             fun eqp : matching_tuple_inverted tpg1 =
                       ((cp pl pr, g2), ct tl tr) =>
               Mev_fourth_eq g1 g2 tpg1 Mev2 pl pr tl tr eqp
                 
         | ((cp pl pr, g2), ctxt (hd_c C tr)) =>
             fun eqp : matching_tuple_inverted tpg1 =
                       ((cp pl pr, g2), ctxt (hd_c C tr)) =>
               Mev_fourth_eq_l_context tpg1 g1 g2 Mev2 pl pr C tr eqp

         | ((cp pl pr, g2), ctxt (tail_c tl C)) =>
             fun eqp : matching_tuple_inverted tpg1 =
                       ((cp pl pr, g2), ctxt (tail_c tl C)) =>
               Mev_fourth_eq_r_context tpg1 g1 g2 Mev2 pl pr tl C eqp
                 
         | ((inhole_pat pc ph, g2), t) =>
             fun eqp : matching_tuple_inverted tpg1 =
                       ((inhole_pat pc ph, g2), t) =>
               Mev_fifth_eq tpg1 g1 g2 Mev2 t pc ph eqp
                 
         | ((name_pat x p, g2), t) =>
             fun eqp : matching_tuple_inverted tpg1 =
                       ((name_pat x p, g2), t) =>
               name_case (matching_tuple_term tpg1)
                  (Mev_sixth_eq_trans2
                     tpg1 g1 g2 t p x eqp
                     (Mev2 (t, (p, g2))
                        (Mev_sixth_eq_rel tpg1 g1 g2 t x
                           p eqp)))
                  x
                 
         | ((nt_pat n, g2), t) =>
             fun eqp : matching_tuple_inverted tpg1 =
                       ((nt_pat n, g2), t) =>
               (* rewritten in this way to ease proofs *)
               eq_rect t
                  (fun (t : term) => mtch_powset_ev t) 
                  (nt_case g1 g2 n t
                     (Mev_seventh_eq_trans tpg1 g1 g2
                        Mev2 
                        t n eqp))
                  (matching_tuple_term tpg1)
                  (eq_proof (nt_pat n) g2 t tpg1 eqp)
         (* nil list pat against nil list term *)
         | ((list_pat_c nil_pat_c, g2), list_term_c nil_term_c) =>
             fun eqp : matching_tuple_inverted tpg1 =
                       ((list_pat_c nil_pat_c, g2), list_term_c nil_term_c) =>
               Mev_eighth_eq tpg1 g1 g2 eqp
         | _ => fun _ => nil
         end eq_refl).

    Definition Mev (g : grammar) (tup : matching_tuple) :  
      mtch_powset_ev (matching_tuple_term tup) :=
      (Fix
        (matching_tuple_order_well_founded g)
        (* dependent range type of the function that we are building *)
        (fun tup : matching_tuple =>
           mtch_powset_ev (matching_tuple_term tup))
        (* generator function *)
        (Mev_gen g))
        
        tup.

    Definition matches (g : grammar) (p: pat) (t: term) :
      list bindings :=
      (map (fun m => match m with
                  | mtch_pair _ _ b => b
                  end)
           
           (Mev g (t, (p, g)))).
    
    Fixpoint clean_ev (t: term) (mtch_s : mtch_powset_ev t) :
      mtch_powset :=
      match mtch_s with
      | nil => nil
      | mtch_pair t' dec op_b :: tail =>
        (clean_ev_decom t' dec, op_b) :: (clean_ev t' tail)
      end.

    Definition M (g : grammar) (p : pat) (t : term) : mtch_powset :=
      clean_ev t (Mev g (t, (p, g))).

  End MatchDecom.

End Matching.
