Require Import 
        Lists.List
        Logic.Eqdep
        (* inj_pair2_eq_dec *)
        Logic.Eqdep_dec
        Program.Equality
        (* Some_inj *)
        ssr.ssrfun
        FunctionalExtensionality.

Require Export
        patterns_terms
        verification.match_spec
        lib_ext.ListExt
        lib_ext.tactics.

(****************************************)
(* lemmas about matching implementation *)
(****************************************)

Module MatchImplLemmas (pt : PatTermsSymb).
  Import pt.

  Module MatchingSpec := MatchingSpec pt.
  Import MatchingSpec.
  Import Matching.
  Import MatchTads.
  Import WfRel.
  Import GrammarLists.
  
  (******************************)
  (* general results about Mev *)
  (******************************)
  (* function extensionality over recursive cases of Mev (needed for Fix_eq) *)
  Lemma fix_eq_fun_ext : 
    forall (g : grammar)
      (tup : matching_tuple)
      (f f' : forall tup' : matching_tuple, 
          matching_tuple_order g tup' tup -> mtch_powset_ev (matching_tuple_term tup')),
      (forall (tup' : matching_tuple) (proof_lt : matching_tuple_order g tup' tup),
          f tup' proof_lt = f' tup' proof_lt) 
      -> Mev_gen g tup f = Mev_gen g tup f'.
  Proof.
    intros g tup f f' H.
    destruct tup as [t [p g'] ].
    unfold Mev_gen.
    
    (* TODO: avoid doing this unfold... *)
    unfold matching_tuple_inverted.
    unfold matching_tuple_pat_grammar.
    unfold matching_tuple_term.
    simpl.

    Ltac rew_H H := 
      repeat (rewrite <- eq_rect_eq);
      repeat (rewrite <- H);
      reflexivity.

    Ltac finish H t :=
      solve [reflexivity
            | destruct t;
              reflexivity
            | ((unfold Mev_fourth_eq) + 
                (unfold Mev_fourth_eq_l_context) +
                (unfold Mev_fourth_eq_r_context) +
                (unfold Mev_sixth_eq_trans2));
                (rew_H H)].

    destruct p as [ | | l | | | ].
    - (* lit *)
      finish H t.
    - (* hole *)
      finish H t.
    - (* nil *)
      destruct l.
      + finish H t.
      + destruct t as [ | l' | c].
        * finish H t.
        * destruct l';
            finish H t.
        * destruct c.
          -- finish H t.
          -- destruct l0.
             ++ finish H t.
             ++ finish H t.
    - (* name *)
      finish H t.
    - (* nt *)
      repeat (rewrite <- eq_rect_eq).
      unfold Mev_seventh_eq_trans.
      unfold eq_rect_r.
      repeat (rewrite <- eq_rect_eq).
      unfold nt_case.
      get_lhs.
      get_rhs.
      match goal with
      | [ H1 : rhs_term = _ |- _] =>
          match goal with
          | [ H2 : lhs_term = _ |- _] =>
              rewrite <- map_map in H1;
              rewrite <- map_map in H2;
              match goal with
              | [ H1 : rhs_term = ?rhs |- _] =>
                  match goal with
                  | [ H2 : lhs_term = ?lhs |- _] =>
                      match rhs with
                      | context [(map ?f1 (get_rhs g' n))] =>
                          match lhs with
                          | context [(map ?f2 (get_rhs g' n))]  =>
                              rewrite H1;
                              rewrite H2;
                              assert(H0 : f1 = f2)
                          end
                      end
                  end
              end
          end
      end.
      apply functional_extensionality.
      intro x.
      destruct x.
      rewrite H.
      reflexivity.
      rewrite H0.
      reflexivity.
    - (* name *)
      unfold Mev_fifth_eq.
      repeat (rewrite <- eq_rect_eq).
      unfold eq_rec_r.
      repeat (rewrite <- eq_rec_eq).
      unfold inhole_case.
      repeat (rewrite H).
      match goal with
      | [ |- fold_left app (map ?f1 ?l1) nil = fold_left app (map ?f2 ?l2) nil] =>
          assert(H0 : f1 = f2)
      end.
      apply functional_extensionality.
      intro x.
      destruct x as [t' d b].
      destruct d as [ | t'' c sub sum].
      + reflexivity.
      + destruct sum.
        * reflexivity.
        * rewrite H.
          reflexivity.
      + rewrite H0.
        reflexivity.
  Qed.

  (* tactics useful to reason about Mev *)
  Ltac Mev_reduce :=
    unfold Mev;
    rewrite Fix_eq;
    [unfold Mev_gen;
     fold Mev_gen;
     simpl;
     unfold matching_tuple_term;
     simpl;
     unfold eq_rect_r;
     repeat (rewrite <- eq_rect_eq)
    |apply fix_eq_fun_ext].
  
  
  Ltac M_reduce :=
    unfold M;
    repeat (repeat Mev_reduce;
            unfold eq_rec_r;
            repeat (rewrite <- Eqdep.EqdepTheory.eq_rec_eq);
            try (unfold inhole_case);
            try (unfold nt_case)).

  (*******************)
  (* lit pat *)
  (*******************)
  Lemma Mev_rew_lit_case : 
  forall (g1 g2 : grammar) (l : lit),
    Mev g1 (lit_term l, (lit_pat l, g2)) = 
      cons (mtch_pair (lit_term l)
                               (* case same literals: (∙, ∅) *)
                               (empty_d_ev (lit_term l))
                               nil)
                    nil.
  Proof.
    intros g1 g2 l.
    Mev_reduce.
    destruct (lit_eq_dec l l) as [Heq | Hneq].
    - (* = *)
      unfold eq_rec_r.
      rewrite <- Eqdep.EqdepTheory.eq_rec_eq.
      reflexivity.
    - (* <> *)
      assert(l = l).
      {reflexivity.
      }

      contradiction.
  Qed.
  
  (*******************)
  (* nil pat *)
  (*******************)
  Lemma Mev_rew_nil_case : 
  forall (g1 g2 : grammar),
    Mev g1 (list_term_c nil_term_c, (list_pat_c nil_pat_c, g2)) = 
      cons (mtch_pair (list_term_c nil_term_c)
                     (* case same literals: (∙, ∅) *)
                     (empty_d_ev (list_term_c nil_term_c))
                     nil)
               nil.
  Proof.
    intros g1 g2.
    Mev_reduce.
    unfold eq_rec_r.
    rewrite <- Eqdep.EqdepTheory.eq_rec_eq.
    reflexivity.
  Qed.

  (*******************)
  (* hole pat *)
  (*******************)
  Lemma Mev_rew_hole_case : 
    forall (g1 g2 : grammar) (t : term),
    exists (ev_decom : {t = t /\ hole_contxt_c = hole_contxt_c} + {subterm_rel t t}),
      (t = contxt_term hole_contxt_c ->
       (Mev g1 (t, (hole_pat, g2))
        =
        (mtch_pair t
                   (* returned value: ((hole, t), ∅) *)
                   (nonempty_d_ev t hole_contxt_c t ev_decom)
                   nil)
          :: mtch_pair t (empty_d_ev t) nil
          :: nil)) /\
      (t <> contxt_term hole_contxt_c ->
       (Mev g1 (t, (hole_pat, g2))
        =
        (cons (mtch_pair t
                         (* returned value: ((hole, t), ∅) *)
                         (nonempty_d_ev t hole_contxt_c t ev_decom)
                         nil)
              nil))).
  Proof.
    intros g1 g2 t.
    unfold Mev.

    Ltac split_solve :=
      simpl;
      exists (left (conj (erefl _) (erefl _)));
      split;
      [(* t = hole *)
        intro Hlter;
        inversion Hlter
      | (* a <> hole *)
        intro Hlter;
        reflexivity].

    rewrite Fix_eq.
    + (* app of fix Mev is equal to one unfolding step, and hence,
         equals to cons (mtch_pair ... *)
      unfold Mev_gen.
      simpl.
      destruct t.
      - (* t = a *)
        split_solve.
      - (* t = list_term *)
        simpl.
        destruct l;
          split_solve.
      - (* t = ctxt c *)
        destruct c.
        ++ (* c = hole *)
           simpl.
           exists (left (conj (erefl _) (erefl _))).
           split.
           -- (* hole = hole *)
              intro Hhole.
              reflexivity.
           -- (* hole <> hole *)
              intro Hhole.
              assert(hole = hole)
                as Heq.
              {reflexivity.
              }
              contradiction.
        ++ (* c = list_contxt *)
           split_solve.
        (*    split_solve. *)
     + (* rec. call returns the same value, over extensionally equal 
         functions  *)
       apply fix_eq_fun_ext.
  Qed.

  Lemma Mev_rew_hole_term_hole_case : 
    forall (g1 g2 : grammar),
       (Mev g1 (contxt_term hole_contxt_c, (hole_pat, g2))
        =
        (mtch_pair (contxt_term hole_contxt_c)
                   (* returned value: ((hole, t), ∅) *)
                   (nonempty_d_ev (contxt_term hole_contxt_c) hole_contxt_c 
                      (contxt_term hole_contxt_c) 
                      (left (conj (erefl (contxt_term hole_contxt_c)) (erefl hole__t))))
                   nil)
          :: mtch_pair (contxt_term hole_contxt_c) (empty_d_ev (contxt_term hole_contxt_c)) nil
          :: nil).
    Proof.
      intros g1 g2.
      Mev_reduce.
      reflexivity.
    Qed.

    Lemma Mev_rew_hole_term_nhole_case : 
    forall (g1 g2 : grammar) (t : term),
      (t <> contxt_term hole_contxt_c ->
       (Mev g1 (t, (hole_pat, g2))
        =
        (cons (mtch_pair t
                         (* returned value: ((hole, t), ∅) *)
                         (nonempty_d_ev t hole_contxt_c t 
                            (left (conj (erefl t) 
                                     (erefl hole__t))))
                         nil)
              nil))).
  Proof.
    intros g1 g2 t H.
    Mev_reduce.
    destruct t;
      solve [reflexivity
            | match goal with
              | [c : contxt |- _] => destruct c
              end;
              [tauto | reflexivity]
              ].
  Qed.

  (*******************)
  (* name pat *)
  (*******************)
  Lemma name_case_concat :
    forall (t : term) (mtch_ps1 mtch_ps2 : mtch_powset_ev t) (x : var),
      name_case t (mtch_ps1 ++ mtch_ps2) x = 
      (name_case t mtch_ps1 x) ++ (name_case t mtch_ps2 x).
  Proof.
    intros.
    induction mtch_ps1 as [ | hd tl IH].
    + (* nil *)
      reflexivity.
    + (* cons *)
      simpl.
      destruct hd as [t' dec b].
      destruct (bindings_app (rem_rep b) x).
      ++ (* b <> None *)
         destruct (MatchTads.PatTermsDec.term_eq_dec _ _).
         -- (* t' == t *)
            rewrite IH.
            unfold binding.
            reflexivity.
         -- (* t' <> t *)
            apply IH.
      ++ (* b == None *)
         rewrite IH.
         reflexivity.
  Qed.

  Lemma Mev_rew_name_case : 
    forall (g1 g2 : grammar) (t : term) (p : pat) (x : var),
      Mev g1 (t, (name_pat x p, g2))
      =
      name_case (matching_tuple_term (t, (name_pat x p, g2)))
                 (* TODO: check if we can get rid of Mev_sixth_eq_trans2 *)
                 (* (Mev_sixth_eq_trans2 *)
                 (*    (t, (name_pat x p, g2)) g1 g2 t p x eqp *)
                 (*    (Mev g1 (t, (p, g2)))) *)
                 (Mev g1 (t, (p, g2)))
                 x.
  Proof.
    intros.

    simpl.
    remember (name_case _ _ _) as rhs eqn:Heq_rhs.

    (* unfold Mev. *)
    unfold Mev.
    rewrite Fix_eq.
    + (* Fixpoint def *)
      unfold Mev_gen.
      simpl.
      rewrite Heq_rhs.
      reflexivity.
   + (* prove hypothesis of Fix_eq: function extensionality over recursive 
        cases *)
     apply fix_eq_fun_ext.
  Qed.

  Lemma Mev_name_case_in : 
    forall (g1 g2 : grammar) (t : term) (p : pat) (v : var) (b : bindings),
    In (mtch_pair t (empty_d_ev t) b) (Mev g1 (t, (name v p, g2))) ->
    exists b', In (mtch_pair t (empty_d_ev t) b') (Mev g1 (t, (p, g2)))
          /\
          Some b = b_union ((v, (named t (empty_d_ev t))) :: nil) b'.
  Proof.
    intros g1 g2 t p v b H.
    rewrite (Mev_rew_name_case _ _ _ _ _) in H.
    simpl in H.
    unfold Mev_sixth_eq_trans2 in H.
    unfold eq_rec_r in H.
    repeat (rewrite <- eq_rect_eq in H).
    repeat (rewrite <- eq_rec_eq in H).
    unfold name_case in H.
    remember (Mev g1 (t, (p, g2))) as rec_call eqn:Heq_rec_call.
    clear Heq_rec_call.
    induction rec_call as [ | hd tl IH].
    - (* rec_call = nil *)
      inversion H.
    - (* rec_call = hd :: tl *)
      fold name_case in IH.
      simpl in hd.
      destruct hd as [t' dec b'].
      repeat (rewrite <- eq_rec_eq in H).
      remember (b_union (@cons binding 
                           (@pair pt.var pt.term v (named t' dec)) 
                           (@nil binding)) b') as bunion.
      destruct bunion.
      + (* bunion = Some b *)
        fold name_case in H.
        apply in_inv_trans in H.
        inversion H as [Hin_hd | Hin_tl].
        * (* In hd *)
          inversion Hin_hd as [Hdecom].
          apply inj_pair2 in Hdecom.
          rewrite Hdecom.
          exists b'.
          split.
          -- (* In hd *)
             apply in_eq.
          -- (* Some b = ... *)
             subst.
             auto.
        * (* In tl *)
          apply IH in Hin_tl.
          inversion Hin_tl as [b'' [Hin_tl' Hunion] ].
          clear Hin_tl.
          exists b''.
          split.
          -- (* In hd *)
             auto using in_cons_trans.
          -- (* Some b = ... *)
             auto.
      + (* bunion = None *)
        fold name_case in H.
        apply IH in H.
        inversion H as [b'' [Hin Hunion ] ].
        clear H.
        exists b''.
        split.
        * (* In hd *)
          auto using in_cons_trans.
        * (* Some b = ... *)
          auto.
  Qed.

  Lemma Mev_name_non_empty_case_in : 
    forall (g1 g2 : grammar) (t sub_t : term) (c : contxt) (p : pat) (v : var) 
      (ev_decom : {sub_t = t /\ c = hole__t} + {subterm_rel sub_t t}) (b : bindings),
    In (mtch_pair t (nonempty_d_ev t c sub_t ev_decom) b) (Mev g1 (t, (name v p, g2))) ->
    exists b', In (mtch_pair t (nonempty_d_ev t c sub_t ev_decom) b') 
            (Mev g1 (t, (p, g2)))
          /\
          Some b = b_union ((v, contxt_term c) :: ∅) b'.
  Proof.
    intros g1 g2 t sub_t c p v ev_decom b H.
    rewrite (Mev_rew_name_case _ _ _ _ _) in H.
    simpl in H.
    unfold Mev_sixth_eq_trans2 in H.
    unfold eq_rec_r in H.
    repeat (rewrite <- eq_rect_eq in H).
    repeat (rewrite <- eq_rec_eq in H).
    unfold name_case in H.
    remember (Mev g1 (t, (p, g2))) as rec_call eqn:Heq_rec_call.
    clear Heq_rec_call.
    induction rec_call as [ | hd tl IH].
    - (* rec_call = nil *)
      inversion H.
    - (* rec_call = hd :: tl *)
      fold name_case in IH.
      simpl in hd.
      destruct hd as [t' dec b'].
      repeat (rewrite <- eq_rec_eq in H).
      remember (b_union (@cons binding 
                           (@pair pt.var pt.term v (named t' dec)) 
                           (@nil binding)) b') as bunion.
      destruct bunion.
      + (* bunion = Some b *)
        fold name_case in H.
        apply in_inv_trans in H.
        inversion H as [Hin_hd | Hin_tl].
        * (* In hd *)
          inversion Hin_hd as [Hdecom].
          apply inj_pair2 in Hdecom.
          rewrite Hdecom.
          exists b'.
          split.
          -- (* In hd *)
             apply in_eq.
          -- (* Some b = ... *)
             subst.
             auto.
        * (* In tl *)
          apply IH in Hin_tl.
          inversion Hin_tl as [b'' [Hin_tl' Hunion] ].
          clear Hin_tl.
          exists b''.
          split.
          -- (* In hd *)
             auto using in_cons_trans.
          -- (* Some b = ... *)
             auto.
      + (* bunion = None *)
        fold name_case in H.
        apply IH in H.
        inversion H as [b'' [Hin Hunion ] ].
        clear H.
        exists b''.
        split.
        * (* In hd *)
          auto using in_cons_trans.
        * (* Some b = ... *)
          auto.
  Qed.
    
  (*******************)
  (* nt pat *)
  (*******************)
  Lemma Mev_rew_nt_case :
    forall (g1 g2 : grammar) (t : term) (n : nonterm),
      Mev g1 (t, (nt_pat n, g2))
      =
      nt_case g1 g2 n t
               (fun (tpg2 : matching_tuple)
                  (_ : matching_tuple_order g1 tpg2 (t, (nt_pat n, g2)))
                => Mev g1 tpg2).
  Proof.
    intros g1 g2 t n.
    remember (nt_case _ _ _ _ _) as rhs eqn:Heq_rhs.
    unfold Mev.
    rewrite Fix_eq.
    + (* fixpoint def. *)
      unfold Mev_gen.
      fold Mev_gen.
      simpl.
      rewrite Heq_rhs.
      rewrite <- eq_rect_eq.
      auto.
    + (* prove hypothesis of Fix_eq: function extensionality over recursive 
        cases *)
       apply fix_eq_fun_ext.
  Qed.

  Lemma Mev_nt_case_in : 
    forall (g1 g2 : grammar) (t : term) (n : nonterm) (b : bindings),
    In (mtch_pair t (empty_d_ev t) b) (Mev g1 (t, (nt n, g2))) ->
    exists p (proof : prod_in_g (n, p) g2) b', 
      In (mtch_pair t (empty_d_ev t) b') 
        (Mev g1 (t, (p, remove_prod (n, p) g2 proof)))
      /\
      b = ∅.
  Proof.
    intros g1 g2 t n b H.
    rewrite Mev_rew_nt_case in H.
    unfold nt_case in H.
    induction (get_rhs g2 n) as [ | hd tl IH].
    - (* get_rhs g2 n = nil *)
      inversion H.
    - (* get_rhs g2 n = hd :: tl *)
      simpl in H.
      rewrite fold_left_fapp in H.
      apply in_app_or in H.
      inversion H as [Hin_hd | Hin_tail].
      + (* In hd *)
        clear H.
        destruct hd as [p proof].
        remember (Mev g1 (t, (p, remove_prod (n, p) g2 proof)))
          as rec_call eqn:Heq_rec_call.
        exists p.
        exists proof.
        rewrite <- Heq_rec_call.
        clear Heq_rec_call.
        clear IH.
        induction rec_call as [ | hd' tl' IH].
        * (* rec_call = nil *)
          inversion Hin_hd.
        * (* rec_call = hd' :: tl' *)
          simpl in Hin_hd.
          simpl in hd'.
          destruct hd' as [t'' de_ev b'].
          inversion Hin_hd as [Heq_mtch | Hin_tl].
          -- (* mtch_pair = mtch_pair *)
             clear Hin_hd.
             exists b'.
             inversion Heq_mtch as [Hdecom].
             apply inj_pair2 in Hdecom.
             subst.
             split;
               (apply in_eq + auto).
          -- (* In tl *)
             clear Hin_hd.
             apply IH in Hin_tl.
             inversion Hin_tl as [b'' [Hin_tl' Hb] ].
             clear Hin_tl.
             subst.
             exists b''.
             split;
               auto using in_cons_trans.
      + (* In tail *)
        apply IH in Hin_tail.
        exact Hin_tail.
  Qed.

  Lemma Mev_nt_non_empty_case_in : 
    forall (g1 g2 : grammar) (t sub_t: term) (c : contxt) (n : nonterm) (b : bindings)
    (ev_decom : {sub_t = t /\ c = hole__t} + {subterm_rel sub_t t}),
    In (mtch_pair t (nonempty_d_ev t c sub_t ev_decom) b) 
      (Mev g1 (t, (nt n, g2))) ->
    exists p (proof : prod_in_g (n, p) g2) b', 
      In (mtch_pair t (nonempty_d_ev t c sub_t ev_decom) b') 
        (Mev g1 (t, (p, remove_prod (n, p) g2 proof)))
      /\
      b = ∅.
  Proof.
    intros g1 g2 t sub_t c n b ev_decom H.
    rewrite Mev_rew_nt_case in H.
    unfold nt_case in H.
    induction (get_rhs g2 n) as [ | hd tl IH].
    - (* get_rhs g2 n = nil *)
      inversion H.
    - (* get_rhs g2 n = hd :: tl *)
      simpl in H.
      rewrite fold_left_fapp in H.
      apply in_app_or in H.
      inversion H as [Hin_hd | Hin_tail].
      + (* In hd *)
        clear H.
        destruct hd as [p proof].
        remember (Mev g1 (t, (p, remove_prod (n, p) g2 proof)))
          as rec_call eqn:Heq_rec_call.
        exists p.
        exists proof.
        rewrite <- Heq_rec_call.
        clear Heq_rec_call.
        clear IH.
        induction rec_call as [ | hd' tl' IH].
        * (* rec_call = nil *)
          inversion Hin_hd.
        * (* rec_call = hd' :: tl' *)
          simpl in Hin_hd.
          simpl in hd'.
          destruct hd' as [t'' de_ev b'].
          inversion Hin_hd as [Heq_mtch | Hin_tl].
          -- (* mtch_pair = mtch_pair *)
             clear Hin_hd.
             exists b'.
             inversion Heq_mtch as [Hdecom].
             apply inj_pair2 in Hdecom.
             subst.
             split;
               (apply in_eq + auto).
          -- (* In tl *)
             clear Hin_hd.
             apply IH in Hin_tl.
             inversion Hin_tl as [b'' [Hin_tl' Hb] ].
             clear Hin_tl.
             subst.
             exists b''.
             split;
               auto using in_cons_trans.
      + (* In tail *)
        apply IH in Hin_tail.
        exact Hin_tail.
  Qed.

  (*******************)
  (* cons pat *)
  (*******************)
  Lemma Mev_rew_cons_case :
    forall (g1 g2 : grammar) (tl : term) (tr : list_term) (pl : pat) (pr : list_pat),
      Mev g1 (ct tl tr, (cp pl pr, g2))
      =
        cons_case (ct tl tr) tl tr (build_subterm_proof tl tr)
          (Mev g1 (tl, (pl, g1)))
          (Mev g1 (list_term_c tr, (list_pat_c pr, g1))).
  Proof.
    intros g1 g2 tl tr pl pr.
    unfold Mev.
    rewrite Fix_eq.
    - (* app of fix Mev is equal to one unfolding step *)
      unfold Mev_gen.
      fold Mev_gen.
      simpl.
      fold (Mev g1 (tl, (pl, g1))).
      fold (Mev g1 (list_term_c tr, (list_pat_c pr, g1))).
      rewrite <- eq_rect_eq.
      fold (Mev g1 (tl, (pl, g1))).
      fold (Mev g1 (list_term_c tr, (list_pat_c pr, g1))).
      unfold eq_rec_r.
      repeat (rewrite <- eq_rec_eq).
      reflexivity.
    - (* rec. call returns the same value, over extensionally equal 
         functions  *)
      apply fix_eq_fun_ext.
  Qed.

    Lemma Mev_cons_case_aux_pair_in :
    forall (g1 : grammar) (tl : term) (tr : list_term)
      (pr : list_pat) (b : bindings) 
      (proof_subt : subterms (ct tl tr) tl tr)
      (mtch_tl : mtch_ev tl),
      In (mtch_pair (ct tl tr) (empty_d_ev (ct tl tr)) b)
        (cons_case_aux (ct tl tr) tl tr proof_subt mtch_tl
           (Mev g1 (list_term_c tr, (list_pat_c pr, g1)))) ->
      exists (bl br : bindings),
        Some b = (bl ⊔ br) 
        /\
        (mtch_tl = mtch_pair tl (empty_d_ev tl) bl)
        /\
        (In (mtch_pair tr (empty_d_ev tr) br) (Mev g1 (list_term_c tr, (list_pat_c pr, g1)))).
    Proof.
      intros g1 tl tr pr b proof_subt mtch_tl.
      remember (Mev g1 (list_term_c tr, (list_pat_c pr, g1))) 
        as rrec_call eqn:Heq_rrec_call.
      clear Heq_rrec_call.

      simpl in rrec_call.
      
      induction rrec_call as [ | hd_r tl_r IHr].
      - (* rrec_call = nil *)
        simpl.
        intuition.
      - (* rrec_call = hd_r :: tl_r *)
        simpl.
        destruct mtch_tl as [t_l de_ev_l b_l].
        destruct hd_r as [t_r de_ev_r b_r].
        unfold eq_ind.
        remember (select t_l de_ev_l t_r de_ev_r (ct t_l tr) proof_subt)
          as sel eqn:Heq_sel.
        destruct sel.
        * (* select = Some d *)
          remember ((b_l) ⊔ (b_r)) as b_l_r.
          destruct b_l_r.
          -- (* Some b0 = (b_l) ⊔ (b_r) *)
             intro Hin_cons.
             inversion Hin_cons as [Hin_hd | Hin_tl].
             ++ (* In hd *)
                clear Hin_cons.
                inversion Hin_hd as [Hdecom].
                apply inj_pair2 in Hdecom.
                exists b_l.
                exists b_r.
                rewrite Hdecom in Heq_sel.
                unfold select in Heq_sel.
                simpl.
                destruct de_ev_l as [tl' | tl' cl].
                ** (* de_ev_l = empty *)
                   destruct de_ev_r as [tr' | tr' cr].
                   --- (* de_ev_r = empty *)
                       subst.
                       auto.
                   --- (* de_ev_r <> empty *)
                       subst.
                       destruct cr;
                         inversion Heq_sel.
                ** (* de_ev_l <> empty *)
                   destruct de_ev_r as [tr' | tr' cr].
                   --- (* de_ev_r = empty *)
                       destruct tr' as [ | | c].
                       +++ (* tr' = lit impossible case *)
                           inversion proof_subt as [Hcons | [Hhdc | Htlc] ].
                           *** (* tr' = cons *)
                               inversion Hcons as [l' [Hter Hcons' ] ].
                               inversion Hter.
                           *** (* tr' = hd ctxt *)
                               inversion Hhdc as [c' [l' [_ [Hter _ ] ] ] ].
                               inversion Hter.
                           *** (* tr' = tail ctxt *)
                               inversion Htlc as [cl' [Hter _] ].
                               inversion Hter.
                       +++ (* tr' = hd ctxt *)
                           inversion Heq_sel.
                       +++ (* tr' = hd ctxt *)
                           destruct c;
                             inversion Heq_sel.
                   --- (* de_ev_r <> empty *)
                       inversion Heq_sel.
             ++ (* In tl *)
                apply IHr in Hin_tl.
                inversion Hin_tl as [bl [br [Heqb [Hmtch_eq Hin] ] ] ].
                exists bl.
                exists br.
                split.
                ** (* Some b = (bl) ⊔ (br) *)
                   auto.
                ** split.
                   --- (* mtch_pair = mtch_pair *) 
                       exact Hmtch_eq.
                   --- (* In *)
                       right.
                       exact Hin.
          -- (* None = (b_l) ⊔ (b_r) *)
             intro Hin.
             apply IHr in Hin.
             inversion Hin as [bl [br [Hb [Hmtch_eq Hin'] ] ] ].
             exists bl.
             exists br.
             split.
             ** (* b union *)
                auto.
             ** split.
                --- (* mtch_pair = mtch_pair *)
                    exact Hmtch_eq.
                --- (* In *)
                    right.
                    exact Hin'.
        * (* select = None *)
          intro Hin.
             apply IHr in Hin.
             inversion Hin as [bl [br [Hb [Hmtch_eq Hin'] ] ] ].
             exists bl.
             exists br.
             split.
             ** (* Some b = (bl) ⊔ (br) *)
                auto.
             ** split.
                --- (* mtch_pair = mtch_pair *)
                    exact Hmtch_eq.
                --- (* In *)
                    right.
                    exact Hin'.
    Qed.

    Lemma Mev_cons_case_aux_non_empty_pair_in :
    forall (g1 : grammar) (tl subt : term) (tr : list_term) (c : contxt)
      (ev_decom : {subt = (ct tl tr) /\ c = hole__t} 
                                + 
                   {pt.subterm_rel subt (ct tl tr)})
      (pr : list_pat) (b : bindings) 
      (proof_subt : subterms (ct tl tr) tl tr)
      (mtch_tl : mtch_ev tl),
      In (mtch_pair (ct tl tr) (nonempty_d_ev (ct tl tr) c subt ev_decom) b)
        (cons_case_aux (ct tl tr) tl tr proof_subt mtch_tl
           (Mev g1 (list_term_c tr, (list_pat_c pr, g1)))) ->
      exists (bl br : bindings),
        Some b = (bl ⊔ br) 
        /\
        ((mtch_tl = mtch_pair tl (empty_d_ev tl) bl /\
          exists c' c'' ev_decom_subt, 
              In (mtch_pair tr (nonempty_d_ev tr c' subt
                                  ev_decom_subt) br) 
                (Mev g1 (list_term_c tr, (list_pat_c pr, g1))) /\
                c' = list_contxt_c c'' /\
                c = tail_c tl c'')
        \/
        (exists c' ev_decom_subt, 
            mtch_tl = mtch_pair tl (nonempty_d_ev tl c' subt ev_decom_subt) bl /\
              In (mtch_pair tr (empty_d_ev tr) br) 
                (Mev g1 (list_term_c tr, (list_pat_c pr, g1))) /\
               c = hd_c c' tr)).
    Proof.
      intros g1 tl subt tr c ev_decom pr b proof_subt mtch_tl.
      remember (Mev g1 (list_term_c tr, (list_pat_c pr, g1)))
        as rrec_call eqn:Heq_rrec_call.
      clear Heq_rrec_call.

      simpl in rrec_call.
      
      induction rrec_call as [ | hd_r tl_r IHr].
      - (* rrec_call = nil *)
        simpl.
        firstorder.
      - (* rrec_call = hd_r :: tl_r *)
        simpl.
        dependent destruction mtch_tl.
        dependent destruction hd_r.
        unfold eq_ind.
        remember (select t d tr d0 (ct t tr) proof_subt)
          as sel eqn:Heq_sel.
        dependent destruction sel.
        * (* select = Some d *)
          remember ((b0) ⊔ (b1)) as b_l_r.
          dependent destruction b_l_r.
          -- (* Some b0 = (b_l) ⊔ (b_r) *)
             intro Hin_cons.
             inversion Hin_cons as [Hin_hd | Hin_tl].
             ++ (* In hd *)
                clear Hin_cons.
                inversion Hin_hd as [Hdecom].
                apply inj_pair2 in Hdecom.
                exists b0.
                exists b1.
                rewrite Hdecom in Heq_sel.
                unfold select in Heq_sel.
                simpl.
                dependent destruction d.
                ** (* de_ev_l = empty *)
                   dependent destruction d0.
                   --- (* de_ev_r = empty *)
                       inversion Heq_sel.
                   --- (* de_ev_r <> empty *)
                       split.
                       +++ (* Some b = (b_l) ⊔ (b_r) *)
                           subst.
                           auto.
                       +++ (* empty decom on the left *)
                           left.
                           split.
                           *** (* empty decom on the left  *)
                               reflexivity.
                           *** (* In left call *)
                               destruct c0.
                               ---- (* cr = hole *)
                                    inversion Heq_sel.
                               ---- (* cr <> hole *)
                                    inversion Heq_sel.
                                    exists (list_contxt_c l).
                                    exists l.
                                    subst.
                                    exists s.
                                    auto.
                ** (* de_ev_l <> empty *)
                   dependent destruction d0.
                   --- (* de_ev_r = empty *)
                       split.
                       +++ (* b union *)
                           subst.
                           auto.
                       +++ (* non-empty decom on the left *)
                           right.
                           inversion Heq_sel.
                           exists c0.
                           subst.
                           exists s.
                           auto.
                   --- (* de_ev_r <> empty *)
                       inversion Heq_sel.
             ++ (* In tl *)
                apply IHr in Hin_tl.
                inversion Hin_tl as [bl [br [Heqb [Hdecom_r | Hdecom_l] ] ] ].
                ** (* non-empty dec on the right *)
                   exists bl.
                   exists br.
                   split.
                   --- (* Some b = (bl) ⊔ (br) *)
                       auto.
                   --- (* empty decom on the left *)
                       left.
                       inversion Hdecom_r as [Heq Hin].
                       split.
                       +++ (* left call empty *)
                           auto.
                       +++ (* right call non-empty *)
                           inversion Hin as [C' [C'' [ev_tr [Hin' [Heq_C Hc_tail] ] ] ] ].
                           *** (* C' = hole *)
                               exists C'.
                               exists C''.
                               exists ev_tr.
                               auto.
                ** (* non-empty decom on the left *)
                   exists bl.
                   exists br.
                   split.
                   --- (* Some b = (bl) ⊔ (br) *)
                       auto.
                   --- (* non-empty decom on the left *)
                       inversion Hdecom_l as [c' [ev_decom_tl [Heq Hin] ] ].
                       right.
                       exists c'.
                       exists ev_decom_tl.
                       split.
                       +++ (* mtch = mtch *)
                           auto.
                       +++ (* In right call *)
                           tauto.
          -- (* None = (b_l) ⊔ (b_r) *)
             intro Hin.
             apply IHr in Hin.
             inversion Hin as [bl [br [Hb [Hdecom_r | Hdecom_l] ] ] ].
             ** (* non-empty dec. on the right *)
                exists bl.
                exists br.
                split.
                --- (* b union *)
                    auto.
                --- (* empty decom on the left *)
                    inversion Hdecom_r as [Heq [c' [c'' [ev_decom_tr [Hin' [Heqc Heq_tail] ] ] ] ] ].
                    left.
                    split.
                    +++ (* mtch = mtch *)
                        auto.
                    +++ (* In right call *)
                        exists c'.
                        exists c''.
                        exists ev_decom_tr.
                        auto.
             ** (* empty decom on the right *)
                inversion Hdecom_l as [c' [ev_decom_tl [Heq' Hin'] ] ].
                exists bl.
                exists br.
                split.
                --- (* b union *)
                    auto.
                --- (* non-empty decom on the left *)
                    right.
                    exists c'.
                    exists ev_decom_tl.
                    firstorder.
        * (* select = None *)
          intro Hin.
          apply IHr in Hin.
          inversion Hin as [bl [br [Hb [Hdecom_r | Hdecom_l] ] ] ].
          exists bl.
          exists br.
          split.
          ** (* Some b = (bl) ⊔ (br) *)
            auto.
          ** (* empty decom on the left *)
             inversion Hdecom_r as [Heq [c' [tr' [ev_decom_tr Hin'] ] ] ].
             left.
             split.
             --- (* mtch = mtch *)
                 auto.
             --- (* non-empty dec on the right *)
                 exists c'.
                 exists tr'.
                 exists ev_decom_tr.
                 firstorder.
          ** (* empty decom on the right *)
             inversion Hdecom_l as [c' [tl' [ev_decom_tl [Heq' Hin'] ] ] ].
             exists bl.
             exists br.
             split.
             --- (* b union *)
                 auto.
             --- (* non-empty dec on the left *)
                 right.
                 exists c'.
                 exists tl'.
                 eauto.
    Qed.

    Lemma Mev_cons_case_aux_hd_contxt_pair_in :
    forall (g1 : grammar) (c : contxt) (tl : list_term)
      (pr : list_pat) (b : bindings) 
      (proof_subt : subterms (hd_c c tl) c tl)
      (mtch_c : mtch_ev c),
      In (mtch_pair (hd_c c tl) (empty_d_ev (hd_c c tl)) b)
        (cons_case_aux (hd_c c tl) c tl proof_subt mtch_c
           (Mev g1 (list_term_c tl, (list_pat_c pr, g1)))) ->
      exists (bl br : bindings),
        Some b = (bl ⊔ br) 
        /\
        (mtch_c = mtch_pair c (empty_d_ev c) bl)
        /\
        (In (mtch_pair tl (empty_d_ev tl) br) 
           (Mev g1 (list_term_c tl, (list_pat_c pr, g1)))).
    Proof.
      intros g1 c tl pr b proof_subt mtch_c.
      remember (Mev g1 (list_term_c tl, (list_pat_c pr, g1))) 
        as rrec_call eqn:Heq_rrec_call.
      clear Heq_rrec_call.

      simpl in rrec_call.
      
      induction rrec_call as [ | hd_r tl_r IHr].
      - (* rrec_call = nil *)
        simpl.
        intuition.
      - (* rrec_call = hd_r :: tl_r *)
        simpl.
        destruct mtch_c as [t_l de_ev_l b_l].
        destruct hd_r as [t_r de_ev_r b_r].
        unfold eq_ind.
        remember (select t_l de_ev_l t_r de_ev_r (ctxt (hd_c c tl)) proof_subt)
          as sel eqn:Heq_sel.
        destruct sel.
        * (* select = Some d *)
          remember ((b_l) ⊔ (b_r)) as b_l_r.
          destruct b_l_r.
          -- (* Some b0 = (b_l) ⊔ (b_r) *)
             intro Hin_cons.
             inversion Hin_cons as [Hin_hd | Hin_tl].
             ++ (* In hd *)
                clear Hin_cons.
                inversion Hin_hd as [Hdecom].
                apply inj_pair2 in Hdecom.
                exists b_l.
                exists b_r.
                rewrite Hdecom in Heq_sel.
                unfold select in Heq_sel.
                simpl.
                destruct de_ev_l as [tl' | tl' cl].
                ** (* de_ev_l = empty *)
                   destruct de_ev_r as [tr' | tr' cr].
                   --- (* de_ev_r = empty *)
                       subst.
                       auto.
                   --- (* de_ev_r <> empty *)
                       subst.
                       destruct cr;
                         inversion Heq_sel.
                ** (* de_ev_l <> empty *)
                   destruct de_ev_r as [tr' | tr' cr].
                   --- (* de_ev_r = empty *)
                       destruct tr' as [ | | c'].
                       +++ (* tr' = lit impossible case *)
                           inversion proof_subt as [Hcons | [Hhdc | Htlc] ].
                           *** (* tr' = cons *)
                               inversion Hcons as [l' [Hter Hcons' ] ].
                               inversion Hter.
                           *** (* tr' = hd ctxt *)
                               inversion Hhdc as [c' [l' [_ [Hter _ ] ] ] ].
                               inversion Hter.
                           *** (* tr' = tail ctxt *)
                               inversion Htlc as [cl' [Hter _] ].
                               inversion Hter.
                       +++ (* tr' = hd ctxt *)
                           inversion Heq_sel.
                       +++ (* tr' = hd ctxt *)
                           destruct c';
                             inversion Heq_sel.
                   --- (* de_ev_r <> empty *)
                       inversion Heq_sel.
             ++ (* In tl *)
                apply IHr in Hin_tl.
                inversion Hin_tl as [bl [br [Heqb [Hmtch_eq Hin] ] ] ].
                exists bl.
                exists br.
                split.
                ** (* Some b = (bl) ⊔ (br) *)
                   auto.
                ** split.
                   --- (* mtch_pair = mtch_pair *) 
                       exact Hmtch_eq.
                   --- (* In *)
                       right.
                       exact Hin.
          -- (* None = (b_l) ⊔ (b_r) *)
             intro Hin.
             apply IHr in Hin.
             inversion Hin as [bl [br [Hb [Hmtch_eq Hin'] ] ] ].
             exists bl.
             exists br.
             split.
             ** (* b union *)
                auto.
             ** split.
                --- (* mtch_pair = mtch_pair *)
                    exact Hmtch_eq.
                --- (* In *)
                    right.
                    exact Hin'.
        * (* select = None *)
          intro Hin.
             apply IHr in Hin.
             inversion Hin as [bl [br [Hb [Hmtch_eq Hin'] ] ] ].
             exists bl.
             exists br.
             split.
             ** (* Some b = (bl) ⊔ (br) *)
                auto.
             ** split.
                --- (* mtch_pair = mtch_pair *)
                    exact Hmtch_eq.
                --- (* In *)
                    right.
                    exact Hin'.
    Qed.

    Lemma Mev_cons_case_aux_hd_non_empty_pair_in :
    forall (g1 : grammar) (subt : term) (c1 c2 : contxt) (tr : list_term)
      (ev_decom : {subt = (hd_c c1 tr) /\ c2 = hole__t} 
                                + 
                   {pt.subterm_rel subt (hd_c c1 tr)})
      (pr : list_pat) (b : bindings) 
      (proof_subt : subterms (hd_c c1 tr) c1 tr)
      (mtch_c1 : mtch_ev c1),
      In (mtch_pair (hd_c c1 tr) (nonempty_d_ev (hd_c c1 tr) c2 subt ev_decom) b)
        (cons_case_aux (hd_c c1 tr) c1 tr proof_subt mtch_c1
           (Mev g1 (list_term_c tr, (list_pat_c pr, g1)))) ->
      exists (bl br : bindings),
        Some b = (bl ⊔ br) 
        /\
        ((mtch_c1 = mtch_pair c1 (empty_d_ev c1) bl /\
          exists c' c'' ev_decom_subt, 
              In (mtch_pair tr (nonempty_d_ev tr c' subt
                                  ev_decom_subt) br) 
                (Mev g1 (list_term_c tr, (list_pat_c pr, g1))) /\
                c' = list_contxt_c c'' /\
                c2 = tail_c c1 c'')
        \/
        (exists c' ev_decom_subt, 
            mtch_c1 = mtch_pair c1 (nonempty_d_ev c1 c' subt ev_decom_subt) bl /\
              In (mtch_pair tr (empty_d_ev tr) br) 
                (Mev g1 (list_term_c tr, (list_pat_c pr, g1))) /\
               c2 = hd_c c' tr)).
    Proof.
      intros g1 subt c1 c2 tr ev_decom pr b proof_subt mtch_c1.

      remember (Mev g1 (list_term_c tr, (list_pat_c pr, g1)))
        as rrec_call eqn:Heq_rrec_call.
      clear Heq_rrec_call.

      simpl in rrec_call.
      
      induction rrec_call as [ | hd_r tl_r IHr].
      - (* rrec_call = nil *)
        simpl.
        firstorder.
      - (* rrec_call = hd_r :: tl_r *)
        simpl.
        dependent destruction mtch_c1.
        dependent destruction hd_r.
        unfold eq_ind.
        remember (select (ctxt c1) d tr d0 (ctxt (hd_c c1 tr)) proof_subt)
          as sel eqn:Heq_sel.
        dependent destruction sel.
        * (* select = Some d *)
          remember ((b0) ⊔ (b1)) as b_l_r.
          dependent destruction b_l_r.
          -- (* Some b0 = (b_l) ⊔ (b_r) *)
             intro Hin_cons.
             inversion Hin_cons as [Hin_hd | Hin_tl].
             ++ (* In hd *)
                clear Hin_cons.
                inversion Hin_hd as [Hdecom].
                apply inj_pair2 in Hdecom.
                exists b0.
                exists b1.
                rewrite Hdecom in Heq_sel.
                unfold select in Heq_sel.
                simpl.
                dependent destruction d. (* as [tl' | tl' cl subt' ev_tl]. *)
                ** (* de_ev_l = empty *)
                   dependent destruction d0. (* as [tr' | tr' cr subt' ev_tr]. *)
                   --- (* de_ev_r = empty *)
                       inversion Heq_sel.
                   --- (* de_ev_r <> empty *)
                       split.
                       +++ (* Some b = (b_l) ⊔ (b_r) *)
                           subst.
                           auto.
                       +++ (* empty decom on the left *)
                           left.
                           split.
                           *** (* empty decom on the left  *)
                               reflexivity.
                           *** (* In left call *)
                               destruct c.
                               ---- (* cr = hole *)
                                    inversion Heq_sel.
                               ---- (* cr <> hole *)
                                    inversion Heq_sel.
                                    exists (list_contxt_c l).
                                    exists l.
                                    subst.
                                    exists s.
                                    auto.
                ** (* de_ev_l <> empty *)
                   dependent destruction d0. (* as [tr' | tr' cr ]. *)
                   --- (* de_ev_r = empty *)
                       split.
                       +++ (* b union *)
                           subst.
                           auto.
                       +++ (* non-empty decom on the left *)
                           right.
                           inversion Heq_sel.
                           exists c.
                           subst.
                           exists s.
                           auto.
                   --- (* de_ev_r <> empty *)
                       inversion Heq_sel.
             ++ (* In tl *)
                apply IHr in Hin_tl.
                inversion Hin_tl as [bl [br [Heqb [Hdecom_r | Hdecom_l] ] ] ].
                ** (* non-empty dec on the right *)
                   exists bl.
                   exists br.
                   split.
                   --- (* Some b = (bl) ⊔ (br) *)
                       auto.
                   --- (* empty decom on the left *)
                       left.
                       inversion Hdecom_r as [Heq Hin].
                       split.
                       +++ (* left call empty *)
                           auto.
                       +++ (* right call non-empty *)
                           inversion Hin as [C' [C'' [ev_tr [Hin' [Heq_C Hc_tail] ] ] ] ].
                           *** (* C' = hole *)
                               exists C'.
                               exists C''.
                               exists ev_tr.
                               auto.
                ** (* non-empty decom on the left *)
                   exists bl.
                   exists br.
                   split.
                   --- (* Some b = (bl) ⊔ (br) *)
                       auto.
                   --- (* non-empty decom on the left *)
                       inversion Hdecom_l as [c' [ev_decom_tl [Heq Hin] ] ].
                       right.
                       exists c'.
                       exists ev_decom_tl.
                       split.
                       +++ (* mtch = mtch *)
                           auto.
                       +++ (* In right call *)
                           tauto.
          -- (* None = (b_l) ⊔ (b_r) *)
             intro Hin.
             apply IHr in Hin.
             inversion Hin as [bl [br [Hb [Hdecom_r | Hdecom_l] ] ] ].
             ** (* non-empty dec. on the right *)
                exists bl.
                exists br.
                split.
                --- (* b union *)
                    auto.
                --- (* empty decom on the left *)
                    inversion Hdecom_r as [Heq [c' [c'' [ev_decom_tr [Hin' [Heqc Heq_tail] ] ] ] ] ].
                    left.
                    split.
                    +++ (* mtch = mtch *)
                        auto.
                    +++ (* In right call *)
                        exists c'.
                        exists c''.
                        exists ev_decom_tr.
                        auto.
             ** (* empty decom on the right *)
                inversion Hdecom_l as [c' [ev_decom_tl [Heq' Hin'] ] ].
                exists bl.
                exists br.
                split.
                --- (* b union *)
                    auto.
                --- (* non-empty decom on the left *)
                    right.
                    exists c'.
                    exists ev_decom_tl.
                    firstorder.
        * (* select = None *)
          intro Hin.
          apply IHr in Hin.
          inversion Hin as [bl [br [Hb [Hdecom_r | Hdecom_l] ] ] ].
          exists bl.
          exists br.
          split.
          ** (* Some b = (bl) ⊔ (br) *)
            auto.
          ** (* empty decom on the left *)
             inversion Hdecom_r as [Heq [c' [tr' [ev_decom_tr Hin'] ] ] ].
             left.
             split.
             --- (* mtch = mtch *)
                 auto.
             --- (* non-empty dec on the right *)
                 exists c'.
                 exists tr'.
                 exists ev_decom_tr.
                 firstorder.
          ** (* empty decom on the right *)
             inversion Hdecom_l as [c' [tl' [ev_decom_tl [Heq' Hin'] ] ] ].
             exists bl.
             exists br.
             split.
             --- (* b union *)
                 auto.
             --- (* non-empty dec on the left *)
                 right.
                 exists c'.
                 exists tl'.
                 eauto.
    Qed.

    Lemma Mev_cons_case_aux_tail_contxt_pair_in :
    forall (g1 : grammar) (t : term) (tl : list_contxt)
      (pr : list_pat) (b : bindings) 
      (proof_subt : subterms (tail_c t tl) t tl)
      (mtch_t : mtch_ev t),
      In (mtch_pair (tail_c t tl) (empty_d_ev (tail_c t tl)) b)
        (cons_case_aux (tail_c t tl) t tl proof_subt mtch_t
           (Mev g1 (contxt_term tl, (list_pat_c pr, g1)))) ->
      exists (bl br : bindings),
        Some b = (bl ⊔ br) 
        /\
        (mtch_t = mtch_pair t (empty_d_ev t) bl)
        /\
        (In (mtch_pair tl (empty_d_ev tl) br) 
           (Mev g1 (contxt_term tl, (list_pat_c pr, g1)))).
    Proof.
      intros g1 t tl pr b proof_subt mtch_t.
      remember (Mev g1 (contxt_term tl, (list_pat_c pr, g1))) 
        as rrec_call eqn:Heq_rrec_call.
      clear Heq_rrec_call.

      simpl in rrec_call.
      
      induction rrec_call as [ | hd_r tl_r IHr].
      - (* rrec_call = nil *)
        simpl.
        intuition.
      - (* rrec_call = hd_r :: tl_r *)
        simpl.
        destruct mtch_t as [t_l de_ev_l b_l].
        destruct hd_r as [t_r de_ev_r b_r].
        unfold eq_ind.
        remember (select t_l de_ev_l t_r de_ev_r (ctxt (tail_c t_l tl)) proof_subt)
          as sel eqn:Heq_sel.
        destruct sel.
        * (* select = Some d *)
          remember ((b_l) ⊔ (b_r)) as b_l_r.
          destruct b_l_r.
          -- (* Some b0 = (b_l) ⊔ (b_r) *)
             intro Hin_cons.
             inversion Hin_cons as [Hin_hd | Hin_tl].
             ++ (* In hd *)
                clear Hin_cons.
                inversion Hin_hd as [Hdecom].
                apply inj_pair2 in Hdecom.
                exists b_l.
                exists b_r.
                rewrite Hdecom in Heq_sel.
                unfold select in Heq_sel.
                simpl.
                destruct de_ev_l as [tl' | tl' cl].
                ** (* de_ev_l = empty *)
                   destruct de_ev_r as [tr' | tr' cr].
                   --- (* de_ev_r = empty *)
                       subst.
                       auto.
                   --- (* de_ev_r <> empty *)
                       subst.
                       destruct cr;
                         inversion Heq_sel.
                ** (* de_ev_l <> empty *)
                   destruct de_ev_r as [tr' | tr' cr].
                   --- (* de_ev_r = empty *)
                       destruct tr' as [ | | c'].
                       +++ (* tr' = lit impossible case *)
                           inversion proof_subt as [Hcons | [Hhdc | Htlc] ].
                           *** (* tr' = cons *)
                               inversion Hcons as [l' [Hter Hcons' ] ].
                               inversion Hter.
                           *** (* tr' = hd ctxt *)
                               inversion Hhdc as [c' [l' [_ [Hter _ ] ] ] ].
                               inversion Hter.
                           *** (* tr' = tail ctxt *)
                               inversion Htlc as [cl' [Hter _] ].
                               inversion Hter.
                       +++ (* tr' = hd ctxt *)
                           inversion Heq_sel.
                       +++ (* tr' = hd ctxt *)
                           destruct c';
                             inversion Heq_sel.
                   --- (* de_ev_r <> empty *)
                       inversion Heq_sel.
             ++ (* In tl *)
                apply IHr in Hin_tl.
                inversion Hin_tl as [bl [br [Heqb [Hmtch_eq Hin] ] ] ].
                exists bl.
                exists br.
                split.
                ** (* Some b = (bl) ⊔ (br) *)
                   auto.
                ** split.
                   --- (* mtch_pair = mtch_pair *) 
                       exact Hmtch_eq.
                   --- (* In *)
                       right.
                       exact Hin.
          -- (* None = (b_l) ⊔ (b_r) *)
             intro Hin.
             apply IHr in Hin.
             inversion Hin as [bl [br [Hb [Hmtch_eq Hin'] ] ] ].
             exists bl.
             exists br.
             split.
             ** (* b union *)
                auto.
             ** split.
                --- (* mtch_pair = mtch_pair *)
                    exact Hmtch_eq.
                --- (* In *)
                    right.
                    exact Hin'.
        * (* select = None *)
          intro Hin.
             apply IHr in Hin.
             inversion Hin as [bl [br [Hb [Hmtch_eq Hin'] ] ] ].
             exists bl.
             exists br.
             split.
             ** (* Some b = (bl) ⊔ (br) *)
                auto.
             ** split.
                --- (* mtch_pair = mtch_pair *)
                    exact Hmtch_eq.
                --- (* In *)
                    right.
                    exact Hin'.
    Qed.

  Lemma Mev_cons_case_aux_tail_non_empty_pair_in :
    forall (g1 : grammar) (t subt : term) (c : contxt) (tr : list_contxt)
      (ev_decom : {subt = (tail_c t tr) /\ c = hole__t} 
                                + 
                   {pt.subterm_rel subt (tail_c t tr)})
      (pr : list_pat) (b : bindings) 
      (proof_subt : subterms (tail_c t tr) t tr)
      (mtch_t : mtch_ev t),
      In (mtch_pair (tail_c t tr) (nonempty_d_ev (tail_c t tr) c subt ev_decom) b)
        (cons_case_aux (tail_c t tr) t tr proof_subt mtch_t
           (Mev g1 (contxt_term tr, (list_pat_c pr, g1)))) ->
      exists (bl br : bindings),
        Some b = (bl ⊔ br) 
        /\
        ((mtch_t = mtch_pair t (empty_d_ev t) bl /\
          exists c' c'' ev_decom_subt, 
              In (mtch_pair tr (nonempty_d_ev tr c' subt
                                  ev_decom_subt) br) 
                (Mev g1 (contxt_term tr, (list_pat_c pr, g1))) /\
                c' = list_contxt_c c'' /\
                c = tail_c t c'')
        \/
        (exists c' ev_decom_subt, 
            mtch_t = mtch_pair t (nonempty_d_ev t c' subt ev_decom_subt) bl /\
              In (mtch_pair tr (empty_d_ev tr) br) 
                (Mev g1 (contxt_term tr, (list_pat_c pr, g1))) /\
               c = hd_c c' (list_contxt_2_list_term tr))).
    Proof.
      intros g1 t subt c tr ev_decom pr b proof_subt mtch_t.

      remember (Mev g1 (contxt_term tr, (list_pat_c pr, g1)))
        as rrec_call eqn:Heq_rrec_call.
      clear Heq_rrec_call.

      simpl in rrec_call.
      
      induction rrec_call as [ | hd_r tl_r IHr].
      - (* rrec_call = nil *)
        simpl.
        firstorder.
      - (* rrec_call = hd_r :: tl_r *)
        simpl.
        dependent destruction mtch_t.
        dependent destruction hd_r.
        unfold eq_ind.
        remember (select t d (ctxt tr) d0 (ctxt (tail_c t tr)) proof_subt)
          as sel eqn:Heq_sel.
        dependent destruction sel.
        * (* select = Some d *)
          remember ((b0) ⊔ (b1)) as b_l_r.
          dependent destruction b_l_r.
          -- (* Some b0 = (b_l) ⊔ (b_r) *)
             intro Hin_cons.
             inversion Hin_cons as [Hin_hd | Hin_tl].
             ++ (* In hd *)
                clear Hin_cons.
                inversion Hin_hd as [Hdecom].
                apply inj_pair2 in Hdecom.
                exists b0.
                exists b1.
                rewrite Hdecom in Heq_sel.
                unfold select in Heq_sel.
                simpl.
                dependent destruction d. (* as [tl' | tl' cl subt' ev_tl]. *)
                ** (* de_ev_l = empty *)
                   dependent destruction d0. (* as [tr' | tr' cr subt' ev_tr]. *)
                   --- (* de_ev_r = empty *)
                       inversion Heq_sel.
                   --- (* de_ev_r <> empty *)
                       split.
                       +++ (* Some b = (b_l) ⊔ (b_r) *)
                           subst.
                           auto.
                       +++ (* empty decom on the left *)
                           left.
                           split.
                           *** (* empty decom on the left  *)
                               reflexivity.
                           *** (* In left call *)
                               destruct c0.
                               ---- (* cr = hole *)
                                    inversion Heq_sel.
                               ---- (* cr <> hole *)
                                    inversion Heq_sel.
                                    exists (list_contxt_c l).
                                    exists l.
                                    subst.
                                    exists s.
                                    auto.
                ** (* de_ev_l <> empty *)
                   dependent destruction d0. (* as [tr' | tr' cr ]. *)
                   --- (* de_ev_r = empty *)
                       split.
                       +++ (* b union *)
                           subst.
                           auto.
                       +++ (* non-empty decom on the left *)
                           right.
                           inversion Heq_sel.
                           exists c0.
                           subst.
                           exists s.
                           auto.
                   --- (* de_ev_r <> empty *)
                       inversion Heq_sel.
             ++ (* In tl *)
                apply IHr in Hin_tl.
                inversion Hin_tl as [bl [br [Heqb [Hdecom_r | Hdecom_l] ] ] ].
                ** (* non-empty dec on the right *)
                   exists bl.
                   exists br.
                   split.
                   --- (* Some b = (bl) ⊔ (br) *)
                       auto.
                   --- (* empty decom on the left *)
                       left.
                       inversion Hdecom_r as [Heq Hin].
                       split.
                       +++ (* left call empty *)
                           auto.
                       +++ (* right call non-empty *)
                           inversion Hin as [C' [C'' [ev_tr [Hin' [Heq_C Hc_tail] ] ] ] ].
                           *** (* C' = hole *)
                               exists C'.
                               exists C''.
                               exists ev_tr.
                               auto.
                ** (* non-empty decom on the left *)
                   exists bl.
                   exists br.
                   split.
                   --- (* Some b = (bl) ⊔ (br) *)
                       auto.
                   --- (* non-empty decom on the left *)
                       inversion Hdecom_l as [c' [ev_decom_tl [Heq Hin] ] ].
                       right.
                       exists c'.
                       exists ev_decom_tl.
                       split.
                       +++ (* mtch = mtch *)
                           auto.
                       +++ (* In right call *)
                           tauto.
          -- (* None = (b_l) ⊔ (b_r) *)
             intro Hin.
             apply IHr in Hin.
             inversion Hin as [bl [br [Hb [Hdecom_r | Hdecom_l] ] ] ].
             ** (* non-empty dec. on the right *)
                exists bl.
                exists br.
                split.
                --- (* b union *)
                    auto.
                --- (* empty decom on the left *)
                    inversion Hdecom_r as [Heq [c' [c'' [ev_decom_tr [Hin' [Heqc Heq_tail] ] ] ] ] ].
                    left.
                    split.
                    +++ (* mtch = mtch *)
                        auto.
                    +++ (* In right call *)
                        exists c'.
                        exists c''.
                        exists ev_decom_tr.
                        auto.
             ** (* empty decom on the right *)
                inversion Hdecom_l as [c' [ev_decom_tl [Heq' Hin'] ] ].
                exists bl.
                exists br.
                split.
                --- (* b union *)
                    auto.
                --- (* non-empty decom on the left *)
                    right.
                    exists c'.
                    exists ev_decom_tl.
                    firstorder.
        * (* select = None *)
          intro Hin.
          apply IHr in Hin.
          inversion Hin as [bl [br [Hb [Hdecom_r | Hdecom_l] ] ] ].
          exists bl.
          exists br.
          split.
          ** (* Some b = (bl) ⊔ (br) *)
            auto.
          ** (* empty decom on the left *)
             inversion Hdecom_r as [Heq [c' [tr' [ev_decom_tr Hin'] ] ] ].
             left.
             split.
             --- (* mtch = mtch *)
                 auto.
             --- (* non-empty dec on the right *)
                 exists c'.
                 exists tr'.
                 exists ev_decom_tr.
                 firstorder.
          ** (* empty decom on the right *)
             inversion Hdecom_l as [c' [tl' [ev_decom_tl [Heq' Hin'] ] ] ].
             exists bl.
             exists br.
             split.
             --- (* b union *)
                 auto.
             --- (* non-empty dec on the left *)
                 right.
                 exists c'.
                 exists tl'.
                 eauto.
  Qed.

  Lemma Mev_cons_case_pair_in :
    forall (g1 : grammar) (tl : term) (tr : list_term) (pl : pat) 
      (pr : list_pat) (b : bindings) 
      (proof_subt : subterms (ct tl tr) tl tr),
      In (mtch_pair (ct tl tr) (empty_d_ev (ct tl tr)) b)
        (cons_case (ct tl tr) tl tr proof_subt (Mev g1 (tl, (pl, g1))) 
           (Mev g1 (list_term_c tr, (list_pat_c pr, g1)))) ->
      exists (bl br : bindings),
        Some b = bl ⊔ br 
        /\
        (In (mtch_pair tl (empty_d_ev tl) bl) (Mev g1 (tl, (pl, g1))))
        /\
        (In (mtch_pair tr (empty_d_ev tr) br) (Mev g1 (list_term_c tr, (list_pat_c pr, g1)))).
  Proof.
    intros g1 tl tr pl pr b proof_subt.
    remember (Mev g1 (tl, (pl, g1))) as lrec_call eqn:Heq_lrec_call.
    clear Heq_lrec_call.

    remember (Mev g1 (list_term_c tr, (list_pat_c pr, g1))) 
      as rrec_call eqn:Heq_rrec_call.

    simpl in lrec_call.
    simpl in rrec_call.
    
    induction lrec_call, rrec_call as [ | hd_r tl_r ].
    - (* lrec_call, rrec_call = nil *)
      simpl.
      intuition.
    - (* lrec_call = nil, rrec_call = hd :: tl *)
      simpl.
      intuition.
    - (* lrec_call = hd :: tl , rrec_call = nil *)
      simpl.
      intro H.
      apply IHlrec_call in H.
      inversion H as [bl [br [Hb [Hin_l Hin_r] ] ] ].
      inversion Hin_r.
    - (* lrec_call = hd :: tl , rrec_call = hd' :: tl' *)
      intro H.
      unfold cons_case in H.
      fold cons_case in H.
      apply in_app_or in H.
      inversion H as [Hin_cons_case_aux | Hin_cons_case].
      + (* In cons_case_aux *) 
        rewrite Heq_rrec_call in Hin_cons_case_aux.
        apply Mev_cons_case_aux_pair_in in Hin_cons_case_aux.
        inversion Hin_cons_case_aux as [bl [br [Hb [Heq_mtch Hin] ] ] ].
        exists bl.
        exists br.
        rewrite Heq_mtch.
        rewrite Heq_rrec_call.
        split.
        * (* Some b = (bl) ⊔ (br) *)
          auto.
        * split.
          -- (* In tr *)
              simpl.
              left.
              reflexivity.
          -- (* In tl *)
             exact Hin.
      + (* In cons_case *)
        apply IHlrec_call in Hin_cons_case.
        inversion Hin_cons_case as [bl [br [Hb [Hinl Hinr] ] ] ].
        exists bl.
        exists br.
        split.
        * (* Some b = (bl) ⊔ (br) *)
          auto.
        * split.
          -- (* In tl *)
             simpl.
             right.
             exact Hinl.
          -- (* In tr *)
             exact Hinr.
  Qed.

  Lemma Mev_cons_case_nonempty_pair_in :
    forall (g1 : grammar) (tl subt : term) (tr : list_term) (C : contxt) (pl : pat) 
      (pr : list_pat) (b : bindings) 
      (ev_decom : {subt = (ct tl tr) /\ C = hole__t} 
                               + 
                  {pt.subterm_rel subt (ct tl tr)})
      (proof_subt : subterms (ct tl tr) tl tr),
      In (mtch_pair (ct tl tr) (nonempty_d_ev (ct tl tr) C subt ev_decom) b)
        (cons_case (ct tl tr) tl tr proof_subt (Mev g1 (tl, (pl, g1)))
           (Mev g1 (list_term_c tr, (list_pat_c pr, g1)))) ->
      exists (bl br : bindings),
        Some b = (bl ⊔ br) 
        /\
        ((In (mtch_pair tl (empty_d_ev tl) bl) (Mev g1 (tl, (pl, g1)))
          /\
          (exists c' c'' ev_decom_subt, 
              In (mtch_pair tr (nonempty_d_ev tr c' subt
                                  ev_decom_subt) br) 
                (Mev g1 (list_term_c tr, (list_pat_c pr, g1))) /\
                c' = list_contxt_c c'' /\
                C = tail_c tl c''))
            \/
          (exists c' ev_decom_subt, 
              In (mtch_pair tl (nonempty_d_ev tl c' subt ev_decom_subt) bl)
                (Mev g1 (tl, (pl, g1)))
              /\
              In (mtch_pair tr (empty_d_ev tr) br) 
                (Mev g1 (list_term_c tr, (list_pat_c pr, g1))) /\
              C = hd_c c' tr)).
  Proof.
    intros g1 tl subt tr C pl pr b ev_decom proof_subt H.
    generalize (Mev_cons_case_aux_non_empty_pair_in g1 tl subt tr C ev_decom pr b proof_subt).
    intro Mev_cons_case.
    remember (Mev g1 (tl, (pl, g1))) as lrec_call eqn:Heq_lrec_call.
    clear Heq_lrec_call.

    remember (Mev g1 (list_term_c tr, (list_pat_c pr, g1)))
      as rrec_call eqn:Heq_rrec_call.

    simpl in lrec_call.
    simpl in rrec_call.
    
    induction lrec_call, rrec_call as [ | hd_r tl_r ].
    - (* lrec_call, rrec_call = nil *)
      simpl.
      firstorder.
    - (* lrec_call = nil, rrec_call = hd :: tl *)
      simpl.
      firstorder.
    - (* lrec_call = hd :: tl , rrec_call = nil *)
      revert H.
      unfold cons_case.
      simpl.
      fold cons_case.
      intro H.
      apply IHlrec_call in H.
      inversion H as [bl [br [Hb [Hin_l | Hin_r] ] ] ].
      + (* empty decom on the left *)
        inversion Hin_l as [_ [c' [tr' [ev_dec_tr Hin_rrec] ] ] ].
        inversion Hin_rrec as [Hin _].
        inversion Hin.
      + (* empty decom on the right *)
        inversion Hin_r as [c' [ev_tl [Hin_l [Hin_r' Heq_C] ] ] ].
        inversion Hin_r'.
    - (* lrec_call = hd :: tl , rrec_call = hd' :: tl' *)
      unfold cons_case in H.
      fold cons_case in H.
      apply in_app_or in H.
      inversion H as [Hin_cons_case_aux | Hin_cons_case].
      + (* In cons_case_aux *)
        clear H.
        apply Mev_cons_case in Hin_cons_case_aux.
        inversion Hin_cons_case_aux as [bl [br [Hb [Hl | Hr] ] ] ].
        * (* empty dec on the left  *)
          clear Hin_cons_case_aux.
          exists bl.
          exists br.
          split.
          -- (* Some b = (bl) ⊔ (br) *)
             auto.
          -- (* empty dec on the left *)
             left.
             match goal with
             | [mt : mtch_ev tl |-_] => destruct mt as [tl' dec_tl b_tl]
             end.
             inversion Hl as [Heq [c' [tr' [ev_tr Hin] ] ] ].
             split.
             ++ (* In left call *)
                rewrite Heq.
                apply in_eq.
             ++ (* In right call *)
                eauto.
        * (* non-empty dec on the left  *)
          inversion Hr as [c' [tl' [ev_tl [Heq Hin] ] ] ].
          exists bl.
          exists br.
          split.
          -- (* Some b = (bl) ⊔ (br) *)
             auto.
          -- (* empty dec on the left *)
             right.
             exists c'.
             exists tl'.
             firstorder.
      + (* In cons_case *)
        apply IHlrec_call in Hin_cons_case.
        inversion Hin_cons_case as [bl [br [Hb [Hinl | Hinr] ] ] ].
        * (* empty decom on the left *)
          exists bl.
          exists br.
          split.
          -- (* b union *)
             auto.
          -- left.
             inversion Hinl as [Heq [c' [tr' [ev_tr Hin] ] ] ].
             split.
             ++ (* In left call *)
                eauto using in_cons_trans.
             ++ (* In right call *)
                eauto.
        * (* non-empty decom on the left *)
          inversion Hinr as [c' [tl' [ev_tl [Heq Hin] ] ] ].
          exists bl.
          exists br.
          split.
          -- (* Some b = (bl) ⊔ (br) *)
             auto.
          -- (* empty dec on the left *)
             right.
             exists c'.
             exists tl'.
             split.
             ++ (* In left call *)
                eauto using in_cons_trans.
             ++ (* In right call *)
                eauto.
  Qed.

  Lemma Mev_cons_case_hd_contxt_pair_in :
    forall (g1 : grammar) (c : contxt) (tl : list_term) (pl : pat) 
      (pr : list_pat) (b : bindings) 
      (proof_subt : subterms (hd_c c tl) c tl),
      In (mtch_pair (hd_c c tl) (empty_d_ev (hd_c c tl)) b)
        (cons_case (hd_c c tl) c tl proof_subt 
           (Mev g1 (contxt_term c, (pl, g1))) 
           (Mev g1 (list_term_c tl, (list_pat_c pr, g1)))) ->
      exists (bl br : bindings),
        Some b = bl ⊔ br 
        /\
        (In (mtch_pair c (empty_d_ev c) bl) (Mev g1 (contxt_term c, (pl, g1))))
        /\
        (In (mtch_pair tl (empty_d_ev tl) br) (Mev g1 (list_term_c tl, (list_pat_c pr, g1)))).
  Proof.
    intros g1 c tl pl pr b proof_subt.
    remember (Mev g1 (contxt_term c, (pl, g1))) as lrec_call eqn:Heq_lrec_call.
    clear Heq_lrec_call.

    remember (Mev g1 (list_term_c tl, (list_pat_c pr, g1))) 
      as rrec_call eqn:Heq_rrec_call.

    simpl in lrec_call.
    simpl in rrec_call.
    
    induction lrec_call, rrec_call as [ | hd_r tl_r ].
    - (* lrec_call, rrec_call = nil *)
      simpl.
      intuition.
    - (* lrec_call = nil, rrec_call = hd :: tl *)
      simpl.
      intuition.
    - (* lrec_call = hd :: tl , rrec_call = nil *)
      simpl.
      intro H.
      apply IHlrec_call in H.
      inversion H as [bl [br [Hb [Hin_l Hin_r] ] ] ].
      inversion Hin_r.
    - (* lrec_call = hd :: tl , rrec_call = hd' :: tl' *)
      intro H.
      unfold cons_case in H.
      fold cons_case in H.
      apply in_app_or in H.
      inversion H as [Hin_cons_case_aux | Hin_cons_case].
      + (* In cons_case_aux *) 
        rewrite Heq_rrec_call in Hin_cons_case_aux.
        apply Mev_cons_case_aux_hd_contxt_pair_in in Hin_cons_case_aux.
        inversion Hin_cons_case_aux as [bl [br [Hb [Heq_mtch Hin] ] ] ].
        exists bl.
        exists br.
        rewrite Heq_mtch.
        rewrite Heq_rrec_call.
        split.
        * (* Some b = (bl) ⊔ (br) *)
          auto.
        * split.
          -- (* In tr *)
              simpl.
              left.
              reflexivity.
          -- (* In tl *)
             exact Hin.
      + (* In cons_case *)
        apply IHlrec_call in Hin_cons_case.
        inversion Hin_cons_case as [bl [br [Hb [Hinl Hinr] ] ] ].
        exists bl.
        exists br.
        split.
        * (* Some b = (bl) ⊔ (br) *)
          auto.
        * split.
          -- (* In tl *)
             simpl.
             right.
             exact Hinl.
          -- (* In tr *)
             exact Hinr.
  Qed.

  Lemma Mev_cons_case_hd_contxt_nonempty_pair_in :
    forall (g1 : grammar) (subt : term) (c1 c2 : contxt) (tr : list_term)
      (ev_decom : {subt = (hd_c c1 tr) /\ c2 = hole__t} 
                                + 
                   {pt.subterm_rel subt (hd_c c1 tr)})
      (pl : pat)
      (pr : list_pat) (b : bindings) 
      (proof_subt : subterms (hd_c c1 tr) c1 tr),
      In (mtch_pair (hd_c c1 tr) (nonempty_d_ev (hd_c c1 tr) c2 subt ev_decom) b)
        (cons_case (hd_c c1 tr) c1 tr proof_subt (Mev g1 (contxt_term c1, (pl, g1)))
           (Mev g1 (list_term_c tr, (list_pat_c pr, g1)))) ->
      exists (bl br : bindings),
        Some b = (bl ⊔ br) 
        /\
        ((In (mtch_pair c1 (empty_d_ev c1) bl) (Mev g1 (contxt_term c1, (pl, g1)))
          /\
          (exists c' c'' ev_decom_subt, 
              In (mtch_pair tr (nonempty_d_ev tr c' subt
                                  ev_decom_subt) br) 
                (Mev g1 (list_term_c tr, (list_pat_c pr, g1))) /\
                c' = list_contxt_c c'' /\
                c2 = tail_c c1 c''))
            \/
          (exists c' ev_decom_subt, 
              In (mtch_pair c1 (nonempty_d_ev c1 c' subt ev_decom_subt) bl)
                (Mev g1 (contxt_term c1, (pl, g1)))
              /\
              In (mtch_pair tr (empty_d_ev tr) br) 
                (Mev g1 (list_term_c tr, (list_pat_c pr, g1))) /\
              c2 = hd_c c' tr)).
  Proof.
    intros g1 subt c1 c2 tr ev_decom pl pr b proof_subt H.
    generalize (Mev_cons_case_aux_hd_non_empty_pair_in g1 subt c1 c2 tr ev_decom pr b proof_subt).
    intro Mev_cons_case.
    remember (Mev g1 (contxt_term c1, (pl, g1))) as lrec_call eqn:Heq_lrec_call.
    clear Heq_lrec_call.

    remember (Mev g1 (list_term_c tr, (list_pat_c pr, g1)))
      as rrec_call eqn:Heq_rrec_call.

    simpl in lrec_call.
    simpl in rrec_call.
    
    induction lrec_call, rrec_call as [ | hd_r tl_r ].
    - (* lrec_call, rrec_call = nil *)
      simpl.
      firstorder.
    - (* lrec_call = nil, rrec_call = hd :: tl *)
      simpl.
      firstorder.
    - (* lrec_call = hd :: tl , rrec_call = nil *)
      revert H.
      unfold cons_case.
      simpl.
      fold cons_case.
      intro H.
      apply IHlrec_call in H.
      inversion H as [bl [br [Hb [Hin_l | Hin_r] ] ] ].
      + (* empty decom on the left *)
        inversion Hin_l as [_ [c' [tr' [ev_dec_tr Hin_rrec] ] ] ].
        inversion Hin_rrec as [Hin _].
        inversion Hin.
      + (* empty decom on the right *)
        inversion Hin_r as [c' [ev_tl [Hin_l [Hin_r' Heq_C] ] ] ].
        inversion Hin_r'.
    - (* lrec_call = hd :: tl , rrec_call = hd' :: tl' *)
      unfold cons_case in H.
      fold cons_case in H.
      apply in_app_or in H.
      inversion H as [Hin_cons_case_aux | Hin_cons_case].
      + (* In cons_case_aux *)
        clear H.
        apply Mev_cons_case in Hin_cons_case_aux.
        inversion Hin_cons_case_aux as [bl [br [Hb [Hl | Hr] ] ] ].
        * (* empty dec on the left  *)
          clear Hin_cons_case_aux.
          exists bl.
          exists br.
          split.
          -- (* Some b = (bl) ⊔ (br) *)
             auto.
          -- (* empty dec on the left *)
             left.
             match goal with
             | [mt : mtch_ev (ctxt c1) |-_] => destruct mt as [tl' dec_tl b_tl]
             end.
             inversion Hl as [Heq [c' [tr' [ev_tr Hin] ] ] ].
             split.
             ++ (* In left call *)
                rewrite Heq.
                apply in_eq.
             ++ (* In right call *)
                eauto.
        * (* non-empty dec on the left  *)
          inversion Hr as [c' [tl' [ev_tl [Heq Hin] ] ] ].
          exists bl.
          exists br.
          split.
          -- (* Some b = (bl) ⊔ (br) *)
             auto.
          -- (* empty dec on the left *)
             right.
             exists c'.
             exists tl'.
             firstorder.
      + (* In cons_case *)
        apply IHlrec_call in Hin_cons_case.
        inversion Hin_cons_case as [bl [br [Hb [Hinl | Hinr] ] ] ].
        * (* empty decom on the left *)
          exists bl.
          exists br.
          split.
          -- (* b union *)
             auto.
          -- left.
             inversion Hinl as [Heq [c' [tr' [ev_tr Hin] ] ] ].
             split.
             ++ (* In left call *)
                eauto using in_cons_trans.
             ++ (* In right call *)
                eauto.
        * (* non-empty decom on the left *)
          inversion Hinr as [c' [tl' [ev_tl [Heq Hin] ] ] ].
          exists bl.
          exists br.
          split.
          -- (* Some b = (bl) ⊔ (br) *)
             auto.
          -- (* empty dec on the left *)
             right.
             exists c'.
             exists tl'.
             split.
             ++ (* In left call *)
                eauto using in_cons_trans.
             ++ (* In right call *)
                eauto.
  Qed.

  Lemma Mev_cons_case_tail_contxt_pair_in :
    forall (g1 : grammar) (t : term) (tl : list_contxt) (pl : pat) 
      (pr : list_pat) (b : bindings) 
      (proof_subt : subterms (tail_c t tl) t tl),
      In (mtch_pair (tail_c t tl) (empty_d_ev (tail_c t tl)) b)
        (cons_case (tail_c t tl) t tl proof_subt 
           (Mev g1 (t, (pl, g1))) 
           (Mev g1 (contxt_term tl, (list_pat_c pr, g1)))) ->
      exists (bl br : bindings),
        Some b = bl ⊔ br 
        /\
        (In (mtch_pair t (empty_d_ev t) bl) (Mev g1 (t, (pl, g1))))
        /\
        (In (mtch_pair tl (empty_d_ev tl) br) (Mev g1 (contxt_term tl, (list_pat_c pr, g1)))).
  Proof.
    intros g1 t tl pl pr b proof_subt.
    remember (Mev g1 (t, (pl, g1))) as lrec_call eqn:Heq_lrec_call.
    clear Heq_lrec_call.

    remember (Mev g1 (contxt_term tl, (list_pat_c pr, g1))) 
      as rrec_call eqn:Heq_rrec_call.

    simpl in lrec_call.
    simpl in rrec_call.
    
    induction lrec_call, rrec_call as [ | hd_r tl_r ].
    - (* lrec_call, rrec_call = nil *)
      simpl.
      intuition.
    - (* lrec_call = nil, rrec_call = hd :: tl *)
      simpl.
      intuition.
    - (* lrec_call = hd :: tl , rrec_call = nil *)
      simpl.
      intro H.
      apply IHlrec_call in H.
      inversion H as [bl [br [Hb [Hin_l Hin_r] ] ] ].
      inversion Hin_r.
    - (* lrec_call = hd :: tl , rrec_call = hd' :: tl' *)
      intro H.
      unfold cons_case in H.
      fold cons_case in H.
      apply in_app_or in H.
      inversion H as [Hin_cons_case_aux | Hin_cons_case].
      + (* In cons_case_aux *) 
        rewrite Heq_rrec_call in Hin_cons_case_aux.
        apply Mev_cons_case_aux_tail_contxt_pair_in in Hin_cons_case_aux.
        inversion Hin_cons_case_aux as [bl [br [Hb [Heq_mtch Hin] ] ] ].
        exists bl.
        exists br.
        rewrite Heq_mtch.
        rewrite Heq_rrec_call.
        split.
        * (* Some b = (bl) ⊔ (br) *)
          auto.
        * split.
          -- (* In tr *)
              simpl.
              left.
              reflexivity.
          -- (* In tl *)
             exact Hin.
      + (* In cons_case *)
        apply IHlrec_call in Hin_cons_case.
        inversion Hin_cons_case as [bl [br [Hb [Hinl Hinr] ] ] ].
        exists bl.
        exists br.
        split.
        * (* Some b = (bl) ⊔ (br) *)
          auto.
        * split.
          -- (* In tl *)
             simpl.
             right.
             exact Hinl.
          -- (* In tr *)
             exact Hinr.
  Qed.

  Lemma Mev_cons_case_tail_contxt_nonempty_pair_in :
    forall (g1 : grammar) (t subt : term) (c : contxt) (tr : list_contxt)
      (ev_decom : {subt = (tail_c t tr) /\ c = hole__t} 
                                + 
                   {pt.subterm_rel subt (tail_c t tr)})
      (pl : pat)
      (pr : list_pat) (b : bindings) 
      (proof_subt : subterms (tail_c t tr) t tr),
      In (mtch_pair (tail_c t tr) 
            (nonempty_d_ev (tail_c t tr) c subt ev_decom) b)
        (cons_case (tail_c t tr) t tr proof_subt 
           (Mev g1 (t, (pl, g1)))
           (Mev g1 (contxt_term tr, (list_pat_c pr, g1)))) ->
      exists (bl br : bindings),
        Some b = (bl ⊔ br) 
        /\
        ((In (mtch_pair t (empty_d_ev t) bl) (Mev g1 (t, (pl, g1)))
          /\
          (exists c' c'' ev_decom_subt, 
              In (mtch_pair tr (nonempty_d_ev tr c' subt
                                  ev_decom_subt) br) 
                (Mev g1 (contxt_term tr, (list_pat_c pr, g1))) /\
                c' = list_contxt_c c'' /\
                c = tail_c t c''))
            \/
          (exists c' ev_decom_subt, 
              In (mtch_pair t (nonempty_d_ev t c' subt ev_decom_subt) bl)
                (Mev g1 (t, (pl, g1)))
              /\
              In (mtch_pair tr (empty_d_ev tr) br) 
                (Mev g1 (contxt_term tr, (list_pat_c pr, g1))) /\
              c = hd_c c' (list_contxt_2_list_term tr))).
  Proof.
    intros g1 t subt c tr ev_decom pl pr b proof_subt H.

    generalize (Mev_cons_case_aux_tail_non_empty_pair_in g1 t subt c tr ev_decom pr b proof_subt).
    intro Mev_cons_case.
    remember (Mev g1 (t, (pl, g1))) as lrec_call eqn:Heq_lrec_call.
    clear Heq_lrec_call.

    remember (Mev g1 (contxt_term tr, (list_pat_c pr, g1)))
      as rrec_call eqn:Heq_rrec_call.

    simpl in lrec_call.
    simpl in rrec_call.
    
    induction lrec_call, rrec_call as [ | hd_r tl_r ].
    - (* lrec_call, rrec_call = nil *)
      simpl.
      firstorder.
    - (* lrec_call = nil, rrec_call = hd :: tl *)
      simpl.
      firstorder.
    - (* lrec_call = hd :: tl , rrec_call = nil *)
      revert H.
      unfold cons_case.
      simpl.
      fold cons_case.
      intro H.
      apply IHlrec_call in H.
      inversion H as [bl [br [Hb [Hin_l | Hin_r] ] ] ].
      + (* empty decom on the left *)
        inversion Hin_l as [_ [c' [tr' [ev_dec_tr Hin_rrec] ] ] ].
        inversion Hin_rrec as [Hin _].
        inversion Hin.
      + (* empty decom on the right *)
        inversion Hin_r as [c' [ev_tl [Hin_l [Hin_r' Heq_C] ] ] ].
        inversion Hin_r'.
    - (* lrec_call = hd :: tl , rrec_call = hd' :: tl' *)
      unfold cons_case in H.
      fold cons_case in H.
      apply in_app_or in H.
      inversion H as [Hin_cons_case_aux | Hin_cons_case].
      + (* In cons_case_aux *)
        clear H.
        apply Mev_cons_case in Hin_cons_case_aux.
        inversion Hin_cons_case_aux as [bl [br [Hb [Hl | Hr] ] ] ].
        * (* empty dec on the left  *)
          clear Hin_cons_case_aux.
          exists bl.
          exists br.
          split.
          -- (* Some b = (bl) ⊔ (br) *)
             auto.
          -- (* empty dec on the left *)
             left.
             match goal with
             | [mt : mtch_ev t |-_] => destruct mt as [tl' dec_tl b_tl]
             end.
             inversion Hl as [Heq [c' [tr' [ev_tr Hin] ] ] ].
             split.
             ++ (* In left call *)
                rewrite Heq.
                apply in_eq.
             ++ (* In right call *)
                eauto.
        * (* non-empty dec on the left  *)
          inversion Hr as [c' [tl' [ev_tl [Heq Hin] ] ] ].
          exists bl.
          exists br.
          split.
          -- (* Some b = (bl) ⊔ (br) *)
             auto.
          -- (* empty dec on the left *)
             right.
             exists c'.
             exists tl'.
             firstorder.
      + (* In cons_case *)
        apply IHlrec_call in Hin_cons_case.
        inversion Hin_cons_case as [bl [br [Hb [Hinl | Hinr] ] ] ].
        * (* empty decom on the left *)
          exists bl.
          exists br.
          split.
          -- (* b union *)
             auto.
          -- left.
             inversion Hinl as [Heq [c' [tr' [ev_tr Hin] ] ] ].
             split.
             ++ (* In left call *)
                eauto using in_cons_trans.
             ++ (* In right call *)
                eauto.
        * (* non-empty decom on the left *)
          inversion Hinr as [c' [tl' [ev_tl [Heq Hin] ] ] ].
          exists bl.
          exists br.
          split.
          -- (* Some b = (bl) ⊔ (br) *)
             auto.
          -- (* empty dec on the left *)
             right.
             exists c'.
             exists tl'.
             split.
             ++ (* In left call *)
                eauto using in_cons_trans.
             ++ (* In right call *)
                eauto.
  Qed.
  
  Lemma Mev_rew_cons_case_hd_ctxt :
    forall (g1 g2 : grammar) (c : contxt) (tr : list_term) (pl : pat) (pr : list_pat),
      exists (proof_subt : subterms (ctxt (hd_c c tr)) (ctxt c) tr),
        Mev g1 (ctxt (hd_c c tr), (cp pl pr, g2))
        =
        cons_case (ctxt (hd_c c tr)) (ctxt c) tr proof_subt
          (Mev g1 (ctxt c, (pl, g1)))
          (Mev g1 (list_term_c tr, (list_pat_c pr, g1))).
  Proof.
    intros g1 g2 c tr pl pr.
    unfold Mev.
    rewrite Fix_eq.
    - (* app of fix Mev is equal to one unfolding step *)
      unfold Mev_gen.
      fold Mev_gen.
      simpl.
      fold (Mev g1 (ctxt c, (pl, g1))).
      fold (Mev g1 (list_term_c tr, (list_pat_c pr, g1))).
      unfold eq_rect_r.
      simpl.

      (* forced to use the same proof term for proof_subt, to guarantee
         equality afterwards *)
      remember (or_intror _) as Hsubt.
      exists Hsubt.
      repeat (rewrite <- eq_rect_eq).
      reflexivity.
    - (* rec. call returns the same value, over extensionally equal 
         functions  *)
      apply fix_eq_fun_ext.
  Qed.

  Lemma Mev_rew_cons_case_tail_ctxt :
    forall (g1 g2 : grammar) (tl : term) (c : list_contxt) (pl : pat) (pr : list_pat),
      exists (proof_subt : subterms (ctxt (tail_c tl c)) tl (ctxt c)),
        Mev g1 (ctxt (tail_c tl c), (cp pl pr, g2))
        =
        (cons_case (ctxt (tail_c tl c)) tl (ctxt c) proof_subt
                   (Mev g1 (tl, (pl, g1)))
                   (Mev g1 (ctxt c, (list_pat_c pr, g1)))).
  Proof.
    intros g1 g2 tl c pl pr.
    unfold Mev.
    rewrite Fix_eq.
    - (* app of fix Mev is equal to one unfolding step *)
      unfold Mev_gen.
      fold Mev_gen.
      fold (Mev g1 (tl, (pl, g1))).
      fold (Mev g1 (ctxt c, (list_pat_c pr, g1))).
      simpl.
      (* forced to use the same proof term for proof_subt, to guarantee
         equality afterwards *)
      remember (or_intror _) as Hsubt.
      exists Hsubt.
      repeat (rewrite <- eq_rect_eq).
      reflexivity.
    - (* rec. call returns the same value, over extensionally equal 
         functions  *)
      apply fix_eq_fun_ext.
  Qed.

  (*******************)
  (* inhole pat *)
  (*******************)
  Lemma Mev_rew_inhole_case :
    forall (g1 g2 : grammar) (t : term) (pc ph : pat),
      Mev g1 (t, (inhole_pat pc ph, g2))
      =
      inhole_case t pc ph g1 g2
                  (fun (tpg2 : matching_tuple)
                     (_ : matching_tuple_order g1 
                            tpg2
                            (t, (inhole_pat pc ph, g2)))
                   => Mev g1 tpg2).
  Proof.
    intros g1 g2 t pc ph.
    unfold Mev.
    rewrite Fix_eq.
    - (* app of fix Mev is equal to one unfolding step *)
      unfold Mev_gen.
      simpl.
      fold Mev_gen.
      unfold eq_rect_r.
      simpl.
      repeat (rewrite <- eq_rect_eq).
      reflexivity.
    - (* rec. call returns the same value, over extensionally equal 
         functions  *)     
      apply fix_eq_fun_ext.
  Qed.

  (* inversion lemma for inhole case spec., in terms of 
     matching/decomposition algorithm *)
  Lemma Mev_inhole_case_in : 
    forall (g1 g2 : grammar) (t : term) (p1 p2 : pat) (b : bindings),
    In (mtch_pair t (empty_d_ev t) b) (Mev g1 (t, (inhole p1 p2, g2))) ->
    exists C subt g3 b1 b2 proof,
    In (mtch_pair t (nonempty_d_ev t C subt proof) b1)
      (Mev g1 (t, (p1, g2)))
    /\
    In (mtch_pair subt (empty_d_ev subt) b2) (Mev g1 (subt, (p2, g3)))
    /\
    (t = subt -> g3 = g2 /\ subt = t /\ C = hole_contxt_c)
    /\
    (subterm_rel subt t -> g3 = g1)   
    /\
    b1 ⊔ b2 = Some b.
  Proof.
    intros g1 g2 t p1 p2 b H.
    rewrite Mev_rew_inhole_case in H.
    unfold inhole_case in H.
    remember (Mev g1 (t, (p1, g2))) as lrec_call eqn:Heq_lrec_call.
    clear Heq_lrec_call.
    induction lrec_call as [ | hdl tll IHl].
    - (* lrec_call = nil *)
      simpl in H.
      inversion H.
    - (* lrec_call = hdl :: tll *)
      simpl in H.
      rewrite fold_left_fapp in H.
      simpl in hdl.
      destruct hdl as [t' dec_t b1].
      destruct dec_t as [ | t' C subt dec_t_proof].
      + (* empty dec *)
        simpl in H.
        apply IHl in H.
        clear IHl.
        inversion H 
          as [C [subt [g3 [b1' [b2 [proof [Hin_tll [Hin_tr Hunion] ] ] ] ] ] ] ].
        exists C.
        exists subt.
        exists g3.
        exists b1'.
        exists b2.
        exists proof.
        split.
        * (* In tll *)
          eauto using in_cons_trans.
        * split.
          -- (* subterm *)
             auto.
          -- (* union *)
             auto.
      + (* non-empty dec *)
        simpl in tll.
        remember dec_t_proof as dec_t_proof' eqn:Heq_dec_t_proof.
        destruct dec_t_proof' as [ [Heq_t Heq_C] | Hsubt].
        * (* subt = t *)
          apply in_app_or in H.
          inversion H as [Hin_hd | Hin_tl].
          -- (* In hd *)
             clear H.
             exists C.
             exists subt.
             exists g2.
             rewrite Heq_t.
             remember (Mev g1 (t', (p2, g2))) as rcall eqn:Heq_rcall.
             clear Heq_rcall.
             clear IHl.
             induction rcall as [ | hd tl IHtl].
             ++ (* Mev g1 (t', (p2, g2)) = nil *)
                inversion Hin_hd.
             ++ (* Mev g1 (t', (p2, g2)) = hd :: tl *)
                simpl in Hin_hd.
                simpl in hd.
                destruct hd as [t'' dec_r br].
                remember (b1 ⊔ br) as bunion.
                destruct bunion.
                ** (* bunion = Some ... *)
                   rewrite fold_left_fapp in Hin_hd.
                   apply in_app_or in Hin_hd.
                   inversion Hin_hd as [Hin_hd' | Hin_tl'].
                   --- (* In hd *)
                       exists b1.
                       exists br.
                       clear Hin_hd.
                       revert dec_t_proof Heq_dec_t_proof.
                       rewrite Heq_t.
                       intros dec_t_proof Heq_dec_t_proof.
                       exists dec_t_proof.
                       split.
                       +++ (* In left pat*)
                           subst.
                           apply in_eq.
                       +++ split.
                           *** (* In right pat *)
                               subst.
                               apply in_inv in Hin_hd'.
                               inversion Hin_hd' as [Hin_hd'' | Hin_tl].
                               ---- (* In hd *)
                                    inversion Hin_hd'' as [Hcombine].
                                    apply inj_pair2 in Hcombine.
                                    destruct dec_r.
                                    ++++ (* dec_r = empty decom *)
                                         apply in_eq.
                                    ++++ (* dec_r <> empty decom *)
                                         inversion Hcombine.
                               ---- (* In tl *)
                                    inversion Hin_tl.
                           *** split.
                               ---- (* t'' = t'' *)
                                    intro Heq.
                                    intuition.
                                    
                               ---- split.
                                    ++++ (* subterm t'' t'' *)
                                         intro Hsubt.
                                         generalize (subterm_rel_non_reflex t'').
                                         intro Hnon_reflx.
                                         contradiction.
                                    ++++ (* b union *)
                                         apply in_inv in Hin_hd'.
                                         inversion Hin_hd' as [Hin_hd'' | Hin_tl].
                                         **** (* In hd *)
                                              inversion Hin_hd'' as [Hcombine].
                                              subst.
                                              auto.
                                         **** (* In tl *)
                                              inversion Hin_tl.
                   --- (* In tl *)
                       clear Hin_hd.
                       apply IHtl in Hin_tl'.
                       inversion Hin_tl' as [b2 [b3 [proof [Hin_left [Hin_right [Heq_t' [Hsubt_t Hunion] ] ] ] ] ] ].
                       exists b2.
                       exists b3.
                       exists proof.
                       split.
                       +++ (* In left call *)
                           apply in_inv in Hin_left.
                           inversion Hin_left as [Heq_match | Hin_tl].
                           *** (* mtch = mtch *)
                               inversion Heq_match as [Hdecom].
                               apply inj_pair2 in Hdecom.
                               apply inj_pair2 in Hdecom.
                               apply inj_pair2 in Hdecom.
                               subst.
                               apply in_eq.
                           *** (* In tl *)
                               auto using in_cons_trans.
                       +++ split.
                           *** (* In right call *)
                               eauto using in_cons_trans.
                           *** split.
                               ---- (* t'' = t'' *)
                                    intuition.
                               ---- split.
                                    ++++ (* subterm t'' t'' *)
                                         intro Hsubt.
                                         generalize (subterm_rel_non_reflex t'').
                                         intro Hnon_reflx.
                                         contradiction.
                                    ++++ (* union *)
                                         auto.
                ** (* bunion = None *)
                   apply IHtl in Hin_hd.
                   clear IHtl.
                   inversion Hin_hd as [b2 [b3 [proof [Hin_left [Hin_right [Heq_t' [Hsubt Hbunion] ] ] ] ] ] ].
                   exists b2.
                   exists b3.
                   exists proof.
                   split.
                   --- (* In left *)
                       apply in_inv in Hin_left.
                       inversion Hin_left as [Hin_hd' | Hin_tl].
                       +++ (* In hd *)
                           inversion Hin_hd' as [Hdecom].
                           apply inj_pair2 in Hdecom.
                           apply inj_pair2 in Hdecom.
                           apply inj_pair2 in Hdecom.
                           subst.
                           apply in_eq.
                       +++ (* In tl *)
                           auto using in_cons_trans.
                   --- split.
                       +++ (* In right *)
                           auto using in_cons_trans.
                       +++ split.
                           *** (* t'' = t'' *)
                               intuition.
                           *** split.
                               ---- (* subterm t'' t'' *)
                                    intro Hsubt'.
                                    generalize (subterm_rel_non_reflex t'').
                                    intro Hnon_reflx.
                                    contradiction.
                               ---- (* b union *)
                                    auto.
          -- (* In tl *)
             apply IHl in Hin_tl.
             inversion Hin_tl as [C' [subt' [g3 [b1' [b2 [proof [Hin_left [Hin_right [Heq_t' [Hsubt Hbunion] ] ] ] ] ] ] ] ] ].
             exists C'.
             exists subt'.
             exists g3.
             exists b1'.
             exists b2.
             exists proof.
             split.
             ++ (* In left *)
                auto using in_cons_trans.
             ++ split.
                ** (* In right *)
                   auto.
                ** split.
                   --- (* t' = subt' *)
                       auto.
                   --- split.
                       +++ (* subterm subt' t' *)
                           auto.
                       +++ (* b union *)
                           auto.
        * (* subterm subt  t *)
          apply in_app_or in H.
          inversion H as [Hin_hd | Hin_tl].
          -- (* In hd *)
             clear H.
             exists C.
             exists subt.
             exists g1.
             remember (Mev g1 (subt, (p2, g1))) as rcall eqn:Heq_rcall.
             clear Heq_rcall.
             clear IHl.
             induction rcall as [ | hd tl IHtl].
             ++ (* Mev g1 (t', (p2, g2)) = nil *)
                inversion Hin_hd.
             ++ (* Mev g1 (t', (p2, g2)) = hd :: tl *)
                simpl in Hin_hd.
                simpl in hd.
                destruct hd as [t'' dec_r br].
                remember (b1 ⊔ br) as bunion.
                destruct bunion.
                ** (* bunion = Some ... *)
                   rewrite fold_left_fapp in Hin_hd.
                   apply in_app_or in Hin_hd.
                   inversion Hin_hd as [Hin_hd' | Hin_tl'].
                   --- (* In hd *)
                       exists b1.
                       exists br.
                       clear Hin_hd.
                       revert dec_t_proof Heq_dec_t_proof.
                       intros dec_t_proof Heq_dec_t_proof.
                       exists dec_t_proof.
                       split.
                       +++ (* In left pat*)
                           subst.
                           apply in_eq.
                       +++ split.
                           *** (* In right pat *)
                               subst.
                               apply in_inv in Hin_hd'.
                               inversion Hin_hd' as [Hin_hd'' | Hin_tl].
                               ---- (* In hd *)
                                    inversion Hin_hd'' as [Hcombine].
                                    apply inj_pair2 in Hcombine.
                                    destruct dec_r.
                                    ++++ (* dec_r = empty decom *)
                                         apply in_eq.
                                    ++++ (* dec_r <> empty decom *)
                                         inversion Hcombine.
                               ---- (* In tl *)
                                    inversion Hin_tl.
                           *** split.
                               ---- (* t' = t'' *)
                                    intro Heq.
                                    assert(Hlt : subterm_rel t'' t').
                                    {auto.
                                    }
                                    rewrite Heq in Hlt.
                                    generalize (subterm_rel_non_reflex t'').
                                    intro Hnon_reflx.
                                    contradiction.
                               ---- split.
                                    ++++ (* subterm t'' t' *)
                                         intuition.
                                    ++++ (* b union *)
                                         apply in_inv in Hin_hd'.
                                         inversion Hin_hd' as [Hin_hd'' | Hin_tl].
                                         **** (* In hd *)
                                           inversion Hin_hd'' as [Hcombine].
                                           subst.
                                           auto.
                                         **** (* In tl *)
                                           inversion Hin_tl.
                   --- (* In tl *)
                       clear Hin_hd.
                       apply IHtl in Hin_tl'.
                       inversion Hin_tl' as [b2 [b3 [proof [Hin_left [Hin_right [Heq_t' [Hsubt' Hunion] ] ] ] ] ] ].
                       exists b2.
                       exists b3.
                       exists proof.
                       split.
                       +++ (* In left call *)
                           apply in_inv in Hin_left.
                           inversion Hin_left as [Heq_match | Hin_tl].
                           *** (* mtch = mtch *)
                               inversion Heq_match as [Hdecom].
                               apply inj_pair2 in Hdecom.
                               apply inj_pair2 in Hdecom.
                               apply inj_pair2 in Hdecom.
                               subst.
                               apply in_eq.
                           *** (* In tl *)
                               auto using in_cons_trans.
                       +++ split.
                           *** (* In right call *)
                               eauto using in_cons_trans.
                           *** split.
                               ---- (* t' = t'' *)
                                    auto.
                               ---- split.
                                    ++++ (* subterm t'' t' *)
                                         auto.
                                    ++++ (* union *)
                                         auto.
                ** (* bunion = None *)
                   apply IHtl in Hin_hd.
                   clear IHtl.
                   inversion Hin_hd as [b2 [b3 [proof [Hin_left [Hin_right [Heq_t' [Hsubt' Hbunion] ] ] ] ] ] ].
                   exists b2.
                   exists b3.
                   exists proof.
                   split.
                   --- (* In left *)
                       apply in_inv in Hin_left.
                       inversion Hin_left as [Hin_hd' | Hin_tl].
                       +++ (* In hd *)
                           inversion Hin_hd' as [Hdecom].
                           apply inj_pair2 in Hdecom.
                           apply inj_pair2 in Hdecom.
                           apply inj_pair2 in Hdecom.
                           subst.
                           apply in_eq.
                       +++ (* In tl *)
                           auto using in_cons_trans.
                   --- split.
                       +++ (* In right *)
                           auto using in_cons_trans.
                       +++ split.
                           *** (* t' = t'' *)
                               auto.
                           *** split.
                               ---- (* subterm t'' t' *)
                                    auto.
                               ---- (* b union *)
                                    auto.
          -- (* In tl *)
             apply IHl in Hin_tl.
             inversion Hin_tl as [C' [subt' [g3 [b1' [b2 [proof [Hin_left [Hin_right [Heq_t' [Hsubt' Hbunion] ] ] ] ] ] ] ] ] ].
             exists C'.
             exists subt'.
             exists g3.
             exists b1'.
             exists b2.
             exists proof.
             split.
             ++ (* In left *)
                auto using in_cons_trans.
             ++ split.
                ** (* In right *)
                   auto.
                ** split.
                   --- (* t' = subt' *)
                       auto.
                   --- split.
                       +++ (* subterm subt' t' *)
                           auto.
                       +++ (* b union *)
                           auto.
  Qed.

  Lemma Mev_inhole_non_empty_case_in : 
    forall (g1 g2 : grammar) (t sub_t : term) (c : contxt) (p1 p2 : pat) (b : bindings)
      (ev_decom : {sub_t = t /\ c = hole__t} + {subterm_rel sub_t t}),
    In (mtch_pair t (nonempty_d_ev t c sub_t ev_decom) b) 
      (Mev g1 (t, (inhole p1 p2, g2))) ->
    exists c' sub_t' g3 c'' b1 b2 proof1 proof2,
    In (mtch_pair t (nonempty_d_ev t c' sub_t' proof1) b1)
      (Mev g1 (t, (p1, g2)))
    /\
    In (mtch_pair sub_t' (nonempty_d_ev sub_t' c'' sub_t proof2) b2) 
      (Mev g1 (sub_t', (p2, g3)))
    /\
    (t = sub_t' -> g3 = g2 /\ c' = hole_contxt_c)
    /\
    (subterm_rel sub_t' t -> g3 = g1)   
    /\
    b1 ⊔ b2 = Some b
    /\ 
    c = context_com c' c''.
  Proof.
    intros g1 g2 t sub_t c p1 p2 b ev_decom H.
    rewrite Mev_rew_inhole_case in H.
    unfold inhole_case in H.
    remember (Mev g1 (t, (p1, g2))) as lrec_call eqn:Heq_lrec_call.
    clear Heq_lrec_call.
    induction lrec_call as [ | hdl tll IHl].
    - (* lrec_call = nil *)
      simpl in H.
      inversion H.
    - (* lrec_call = hdl :: tll *)
      simpl in H.
      rewrite fold_left_fapp in H.
      simpl in hdl.
      destruct hdl as [t' dec_t b1].
      destruct dec_t as [ | t' C subt dec_t_proof].
      + (* empty dec *)
        simpl in H.
        apply IHl in H.
        clear IHl.
        inversion H 
          as [c' [c'' [sub_t' [g3 [b1' [b2 [proof1 [proof2 [Hin_tll [Hin_tr [Hhole [Hsubt [Hunion Hc] ] ] ] ] ] ] ] ] ] ] ] ].
        exists c'.
        exists c''.
        exists sub_t'.
        exists g3.
        exists b1'.
        exists b2.
        exists proof1.
        exists proof2.
        split.
        * (* In tll *)
          eauto using in_cons_trans.
        * split.
          -- (* subterm *)
             auto.
          -- (* union *)
             auto.
      + (* non-empty dec *)
        simpl in tll.
        remember dec_t_proof as dec_t_proof' eqn:Heq_dec_t_proof.
        destruct dec_t_proof' as [ [Heq_t Heq_C] | Hsubt].
        * (* subt = t *)
          apply in_app_or in H.
          inversion H as [Hin_hd | Hin_tl].
          -- (* In hd *)
             clear H.
             exists C.
             exists subt.
             exists g2.
             exists c.
             rewrite Heq_t.
             remember (Mev g1 (t', (p2, g2))) as rcall eqn:Heq_rcall.
             clear Heq_rcall.
             clear IHl.
             induction rcall as [ | hd tl IHtl].
             ++ (* Mev g1 (t', (p2, g2)) = nil *)
                inversion Hin_hd.
             ++ (* Mev g1 (t', (p2, g2)) = hd :: tl *)
                simpl in Hin_hd.
                simpl in hd.
                destruct hd as [t'' dec_r br].
                remember (b1 ⊔ br) as bunion.
                destruct bunion.
                ** (* bunion = Some ... *)
                   rewrite fold_left_fapp in Hin_hd.
                   apply in_app_or in Hin_hd.
                   inversion Hin_hd as [Hin_hd' | Hin_tl'].
                   --- (* In hd *)
                       exists b1.
                       exists br.
                       clear Hin_hd.
                       revert dec_t_proof Heq_dec_t_proof.
                       rewrite Heq_t.
                       intros dec_t_proof Heq_dec_t_proof.
                       exists dec_t_proof.
                       dependent destruction dec_r.
                       +++ (* dec_r = empty *)
                           simpl in Hin_hd'.
                           inversion Hin_hd' as [H | H];
                             inversion H.
                       +++ (* dec_r <> empty *)
                           simpl in Hin_hd'.
                           inversion Hin_hd' as [Hin_hd'' | Hin_tl].
                           *** (* In hd *)
                               inversion Hin_hd'' as [Hcombine].
                               subst.
                               exists s.
                               split.
                               ---- (* In hd *)
                                    apply in_eq.
                               ---- split.
                                    ++++ (* In hd *)
                                         simpl.
                                         left.
                                         reflexivity.
                                    ++++ split.
                                         **** (* t = t *)
                                              tauto.
                                         **** split.
                                              ----- (* subterm_rel t t *)
                                                    intro Hsubt.
                                                    generalize (subterm_rel_non_reflex t).
                                                    intro Hnsubt.
                                                    contradiction.
                                              ----- (* (b1) ⊔ (br) = Some b /\ c0 = c0 *)
                                                    auto.
                           *** (* Hin_tl : False *)
                               inversion Hin_tl. 
                   --- (* In tl *)
                       clear Hin_hd.
                       apply IHtl in Hin_tl'.
                       inversion Hin_tl' as [b2 [b3 [proof1 [proof2 [Hin_left [Hin_right [Heq_t' [Hsubt_t [Hunion Hc] ] ] ] ] ] ] ] ].
                       exists b2.
                       exists b3.
                       exists proof1.
                       exists proof2.
                       split.
                       +++ (* In left call *)
                           apply in_inv in Hin_left.
                           inversion Hin_left as [Heq_match | Hin_tl].
                           *** (* mtch = mtch *)
                               inversion Heq_match as [Hdecom].
                               apply inj_pair2 in Hdecom.
                               apply inj_pair2 in Hdecom.
                               apply inj_pair2 in Hdecom.
                               subst.
                               apply in_eq.
                           *** (* In tl *)
                               auto using in_cons_trans.
                       +++ split.
                           *** (* In right call *)
                               eauto using in_cons_trans.
                           *** split.
                               ---- (* t'' = t'' *)
                                    intuition.
                               ---- split.
                                    ++++ (* subterm t'' t'' *)
                                         intro Hsubt.
                                         generalize (subterm_rel_non_reflex t'').
                                         intro Hnon_reflx.
                                         contradiction.
                                    ++++ (* union *)
                                         auto.
                ** (* bunion = None *)
                   apply IHtl in Hin_hd.
                   clear IHtl.
                   inversion Hin_hd as [b2 [b3 [proof1 [proof2 [Hin_left [Hin_right [Heq_t' [Hsubt [Hbunion Hc] ] ] ] ] ] ] ] ].
                   exists b2.
                   exists b3.
                   exists proof1.
                   exists proof2.
                   split.
                   --- (* In left *)
                       apply in_inv in Hin_left.
                       inversion Hin_left as [Hin_hd' | Hin_tl].
                       +++ (* In hd *)
                           inversion Hin_hd' as [Hdecom].
                           apply inj_pair2 in Hdecom.
                           apply inj_pair2 in Hdecom.
                           apply inj_pair2 in Hdecom.
                           subst.
                           apply in_eq.
                       +++ (* In tl *)
                           auto using in_cons_trans.
                   --- split.
                       +++ (* In right *)
                           auto using in_cons_trans.
                       +++ split.
                           *** (* t'' = t'' *)
                               intuition.
                           *** split.
                               ---- (* subterm t'' t'' *)
                                    intro Hsubt'.
                                    generalize (subterm_rel_non_reflex t'').
                                    intro Hnon_reflx.
                                    contradiction.
                               ---- (* b union *)
                                    auto.
          -- (* In tl *)
             apply IHl in Hin_tl.
             inversion Hin_tl as [C' [C'' [subt' [g3 [b1' [b2 [proof1 [proof2 [Hin_left [Hin_right [Heq_t' [Hsubt [Hbunion HeqC] ] ] ] ] ] ] ] ] ] ] ] ].
             exists C'.
             exists C''.
             exists subt'.
             exists g3.
             exists b1'.
             exists b2.
             exists proof1.
             exists proof2.
             split.
             ++ (* In left *)
                auto using in_cons_trans.
             ++ split.
                ** (* In right *)
                   auto.
                ** split.
                   --- (* t' = subt' *)
                       auto.
                   --- split.
                       +++ (* subterm subt' t' *)
                           auto.
                       +++ (* b union *)
                           auto.
        * (* subterm subt  t *)
          apply in_app_or in H.
          inversion H as [Hin_hd | Hin_tl].
          -- (* In hd *)
             clear H.
             exists C.
             exists subt.
             exists g1.
             remember (Mev g1 (subt, (p2, g1))) as rcall eqn:Heq_rcall.
             clear Heq_rcall.
             clear IHl.
             induction rcall as [ | hd tl IHtl].
             ++ (* Mev g1 (t', (p2, g2)) = nil *)
                inversion Hin_hd.
             ++ (* Mev g1 (t', (p2, g2)) = hd :: tl *)
                simpl in Hin_hd.
                simpl in hd.
                dependent destruction hd.
                remember (b1 ⊔ b0) as bunion.
                destruct bunion.
                ** (* bunion = Some ... *)
                   rewrite fold_left_fapp in Hin_hd.
                   apply in_app_or in Hin_hd.
                   inversion Hin_hd as [Hin_hd' | Hin_tl'].
                   --- (* In hd *)
                       dependent destruction d.
                       +++ (* dec_r = empty *)
                           simpl in Hin_hd'.
                           inversion Hin_hd' as [H | H];
                             inversion H.
                       +++ (* dec_r non empty *)
                           exists c0.
                           exists b1.
                           exists b0.
                           clear Hin_hd.
                           exists dec_t_proof.
                           simpl in Hin_hd'.
                           inversion Hin_hd' as [H | H].
                           *** (* In hd *)
                               inversion H.
                               subst.
                               exists s.
                               split.
                               ---- (* In left pat*)
                                    apply in_eq.
                               ---- split.
                                    ++++ (* In right pat *)
                                         apply in_eq.
                                    ++++ (* In hd *)
                                         split.
                                         **** (* t' = t *)
                                              intro Heq.
                                              subst.
                                              generalize (subterm_rel_non_reflex t).
                                              intro Hnref.
                                              contradiction.
                                         **** split;
                                                auto.
                           *** inversion H.
                   --- (* In tl *)
                       clear Hin_hd.
                       apply IHtl in Hin_tl'.
                       inversion Hin_tl' as [c'' [b2' [b3 [proof1 [proof2 [Hin_left [Hin_right [Heq_t' [Hsubt' [Hunion Heq_c] ] ] ] ] ] ] ] ] ].
                       exists c''.
                       exists b2'.
                       exists b3.
                       exists proof1.
                       exists proof2.
                       split.
                       +++ (* In left call *)
                           apply in_inv in Hin_left.
                           inversion Hin_left as [Heq_match | Hin_tl].
                           *** (* mtch = mtch *)
                               inversion Heq_match as [Hdecom].
                               apply inj_pair2 in Hdecom.
                               apply inj_pair2 in Hdecom.
                               apply inj_pair2 in Hdecom.
                               subst.
                               apply in_eq.
                           *** (* In tl *)
                               auto using in_cons_trans.
                       +++ split.
                           *** (* In right call *)
                               eauto using in_cons_trans.
                           *** split.
                               ---- (* t' = t'' *)
                                    auto.
                               ---- split.
                                    ++++ (* subterm t'' t' *)
                                         auto.
                                    ++++ (* union *)
                                         auto.
                ** (* bunion = None *)
                   apply IHtl in Hin_hd.
                   clear IHtl.
                   inversion Hin_hd as [c'' [b2' [b3 [proof1 [proof2 [Hin_left [Hin_right [Heq_t' [Hsubt' [Hbunion Heq_C] ] ] ] ] ] ] ] ] ].
                   exists c''.
                   exists b2'.
                   exists b3.
                   exists proof1.
                   exists proof2.
                   split.
                   --- (* In left *)
                       apply in_inv in Hin_left.
                       inversion Hin_left as [Hin_hd' | Hin_tl].
                       +++ (* In hd *)
                           inversion Hin_hd' as [Hdecom].
                           apply inj_pair2 in Hdecom.
                           apply inj_pair2 in Hdecom.
                           apply inj_pair2 in Hdecom.
                           subst.
                           apply in_eq.
                       +++ (* In tl *)
                           auto using in_cons_trans.
                   --- split.
                       +++ (* In right *)
                           auto using in_cons_trans.
                       +++ split.
                           *** (* t' = t'' *)
                               auto.
                           *** split.
                               ---- (* subterm t'' t' *)
                                    auto.
                               ---- (* b union *)
                                    auto.
          -- (* In tl *)
             apply IHl in Hin_tl.
             inversion Hin_tl as [C' [subt' [g3 [C'' [b1' [b2 [proof1 [proof2 [Hin_left [Hin_right [Heq_t' [Hsubt' [Hbunion Heq_C] ] ] ] ] ] ] ] ] ] ] ] ].
             exists C'.
             exists subt'.
             exists g3.
             exists C''.
             exists b1'.
             exists b2.
             exists proof1.
             exists proof2.
             split.
             ++ (* In left *)
                auto using in_cons_trans.
             ++ split.
                ** (* In right *)
                   auto.
                ** split.
                   --- (* t' = subt' *)
                       auto.
                   --- split.
                       +++ (* subterm subt' t' *)
                           auto.
                       +++ (* b union *)
                           auto.
  Qed.


  (* experimental evaluator using the previous lemmas as a general 
     memoization technique *)
  Ltac Mev_reduce_memo :=
    repeat (rewrite Mev_rew_inhole_case);
    repeat (rewrite Mev_rew_hole_term_hole_case);
    repeat (rewrite Mev_rew_hole_term_nhole_case);
    repeat (rewrite Mev_rew_name_case);
    repeat (rewrite Mev_rew_nt_case);
    repeat (rewrite Mev_rew_cons_case);
    repeat (rewrite Mev_rew_nil_case);
    repeat (rewrite Mev_rew_lit_case).

End MatchImplLemmas.
