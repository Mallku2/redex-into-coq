Require Import 
        Coq.Lists.List        
        (* dependent induction *)
        Coq.Program.Equality
        (* well-foundedness of lt *)
        Coq.Arith.Wf_nat
        (* lia *)
        Psatz.

Require Import 
        patterns_terms
        patterns_terms_dec
        lib_ext.ListExt
        lib_ext.PeanoNatExt.

Import ListNotations.
Open Scope list_scope. 

Module Type Grammar(pt : PatTermsSymb).
  Import pt.

  Definition production := prod nonterm pat.

  (* useful for specification purposes *)
  Definition productions := list production.

  Parameter production_eq_dec : forall (p1 p2 : production), {p1 = p2} + {p1 <> p2}.

  (* type with which grammars are implemented *)
  Parameter grammar : Set.

  (* constructor *)
  Parameter new_grammar : productions -> grammar.

  Parameter grammar_eq_dec : forall (g1 g2 : grammar), {g1 = g2} + {g1 <> g2}.

  (* query functions  *)
  (* membership of a production to a given grammar *)
  Parameter prod_in_g : production -> grammar -> Prop.

  Parameter prod_in_g_dec : forall (p : production) (g : grammar),
      {prod_in_g p g} + {not (prod_in_g p g)}.

  Parameter grammar_length : grammar -> nat.

  (* modifiers *)
  Parameter remove_prod : forall (p : production) (g : grammar)
                            (proof : prod_in_g p g), grammar.
  
  (* minimal characterization of remove_prod *)
  Parameter remove_prod_length_decrease : 
    forall (g : grammar) prod (proof : prod_in_g prod g),
      grammar_length (remove_prod prod g proof) < grammar_length g.

  Parameter remove_prod_in_g :
    forall (pr1 pr2 : production) (g : grammar)
      (proof_in : prod_in_g pr1 g),
      prod_in_g pr2 (remove_prod pr1 g proof_in) ->
      prod_in_g pr2 g.
       
End Grammar.

(* ********************************************************* *)
(* Grammars as extensional sets of productions, using lists. *)
(* ********************************************************* *)
Module GrammarLists(pt : PatTermsSymb) <: Grammar pt.
  Import pt.

  (* import decidability results about pats and terms *)
  Module PatTermsDec := PatTermsDec(pt).
  Import PatTermsDec.

  Definition production := (prod nonterm pat).

  Definition productions := list (production).
  
  Definition grammar := productions.


  (* ********************************************************* *)
  (* Theory. *)
  (* ********************************************************* *)

  Lemma production_eq_dec : forall (p1 p2 : production), {p1 = p2} + {p1 <> p2}.
  Proof.
    intros.
    destruct p1,p2.
    destruct (pat_eq_dec p p0).
    + destruct (nonterm_eq_dec n n0).
      - left.
        rewrite e.
        rewrite e0.
        reflexivity.
      - right.
        intro.
        inversion H.
        contradiction.
    + destruct (nonterm_eq_dec n n0).
      - right.
        intro.
        inversion H.
        contradiction.
      - right.
        intro.
        inversion H.
        contradiction.
  Defined.

  Lemma list_prod_eq_dec : forall (prods1 prods2 : productions), 
      {prods1 = prods2} + {prods1 <> prods2}.
  Proof.
    intros.
    dependent induction prods1.
    - induction prods2.
      + left.
        reflexivity.
      + right.
        intro.
        inversion H.
    - dependent induction prods2.
      + right.
        intro.
        inversion H.
      + destruct (production_eq_dec a a0).
        -- assert({prods1 = prods2} + {prods1 <> prods2}).
           {apply (IHprods1 prods2).
           }
           inversion H.
           ++ left.
              rewrite e.
              rewrite H0.
              reflexivity.
           ++ right.
              intro.
              inversion H1.
              contradiction.
        -- right.
           intro.
           inversion H.
           contradiction.
  Defined. 

  Lemma grammar_eq_dec : forall (g1 g2 : grammar), {g1 = g2} + {g1 <> g2}.
  Proof.
    apply list_prod_eq_dec.
  Defined.
    

  (* ********************************* *)
  (* Manipulation of grammars   *)
  (* ********************************* *)
  
  (* ********************************* *)
  (* new_gramar *)
  (* ********************************* *)
  
  Definition new_grammar (prods : productions) : grammar :=
    (remove_rep_elem production production_eq_dec prods).

  (* ********************************* *)
  (* grammar_length *)
  (* ********************************* *)

  Definition grammar_length (g : grammar) : nat := length g.

  (* ********************************* *)
  (* prod_in_g *)
  (* ********************************* *)
  Inductive _prod_in_g : production -> grammar -> Prop :=
  | prod_in_g_ev : forall (prod : production) (g : grammar),
      (In prod g) -> _prod_in_g prod g.

  (* TODO: "The kernel does not recognize yet that a parameter can be 
     instantiated by an inductive type"
     no idea about this error, but this seems to be the workaround:
     https://sympa.inria.fr/sympa/arc/coq-club/2017-09/msg00042.html *)
  Definition prod_in_g := _prod_in_g.

  Definition prod_in_g_dec (prod : production) (g : grammar) :
    {prod_in_g prod g} + {not (prod_in_g prod g)}.
    refine (
        match (in_dec production_eq_dec prod g) as in_prod_proof return
              (in_dec production_eq_dec prod g) = in_prod_proof
              -> {prod_in_g prod g} + {not (prod_in_g prod g)} with
        | left proof  =>
          fun eqp : (in_dec production_eq_dec prod g) = left proof  => _
        | right proof =>
          fun eqp : (in_dec production_eq_dec prod g) = right proof => _
        end eq_refl).
    - left.
      apply (prod_in_g_ev _ _ proof).
    - right.
      intro.
      inversion H.
      contradiction.
  Defined.

  Lemma prod_in_g_split :
    forall (g : grammar) (pr : production) (proof_in : prod_in_g pr g),
    exists (g1 g2 : grammar), g = g1 ++ pr :: g2 /\ not (prod_in_g pr g1).
  Proof.
    intros g pr Hproof_in.
    inversion Hproof_in as [prod g' Hin Heq_prof Heq_g].
    apply in_split in Hin.
    inversion Hin as [l1 (l2, Hin'')].
    clear Hin.

    clear Hproof_in.
    rewrite Hin''.
    clear Hin''.
    (* look for the first occurrence *)
    induction l1 as [| hdl1 tll1 IH].
    - (* l1 = nil -> we already have the first occurrence of pr *)
      exists nil.
      exists l2.
      split.
      + (* g = split *)
        reflexivity.
      + (* not prod_in *)
        intro Hprod_in.
        inversion Hprod_in as [pr' g'' Hin Heq_pr Heq_g''].
        inversion Hin.
    - (* l1 = hdl1 :: tll1 *)
      destruct (production_eq_dec hdl1 pr) as [Heq_pr | Hneq_pr].
      + (* hdl1 = pr *)
        exists nil.
        exists (tll1 ++ pr :: l2).
        split.
        * (* split eq *)
          rewrite Heq_pr.
          reflexivity.
        * (* not prod_in *)
          intro Hprod_in.
          inversion Hprod_in as [pr' nilg Hin Heq_pr' Heq_nil].
          inversion Hin.
      + (* hdl1 <> pr *)
        (* we just use the induction hypothesis *)
        inversion IH as [g1 (g2, IH')].
        clear IH.
        exists (hdl1 :: g1).
        exists g2.
        inversion IH' as [Heq_split Hnprod_in].
        clear IH'.
        simpl.
        rewrite <- Heq_split.
        split.
        * (* eq split *)
          reflexivity.
        * (* not prod_in *)
          intro Hprod_in_hd_g1.
          assert(prod_in_g pr g1) as Hprod_in_g1.
          {inversion Hprod_in_hd_g1 as [pr' g'' Hin Heq_prod Heq_g'].
           rewrite (in_inv_iff _ hdl1 pr g1) in Hin.
           inversion Hin as [Heq_pr | Hin_g1].
           - (* hdl1 = pr *)
             contradiction.
           - (* In pr g1 *)
             constructor.
             exact Hin_g1.
          }
          contradiction.
  Qed.

  (* tactic useful to discard a goal with a hypothesis of the form 
     prod_in_g pr [] *)
  Ltac prod_in_g_discard :=
    match goal with
    | [H : prod_in_g _ []%list |- _] =>
        inversion H;
        match goal with
        | [H' : In ?pr [] |- _] =>
            inversion H'
        end
    end.
        
      
  (* useful for reasoning about membership *)
  (* ********************************* *)
  (* remove_prod *)
  (* ********************************* *)

  (* auxiliary functions *)
  (* removes a given production from a grammar (assumes productions do not
     repeat) *)
  Fixpoint remove_prod_aux (g : grammar) (prod : production) : grammar :=
    match g with
    | nil          => nil
    | prod' :: tail => 
      match production_eq_dec prod prod' with
      | left _ => tail
      | _      => prod' :: remove_prod_aux tail prod
      end
    end.

  Definition remove_prod (p : production) (g : grammar) 
             (proof : prod_in_g p g) : grammar :=
    (remove_prod_aux g p). 

  Lemma remove_prod_length_decrease : 
    forall (g : grammar) prod (proof : prod_in_g prod g),
     grammar_length (remove_prod prod g proof) < grammar_length g.
  Proof.
    intros.
    induction g.
    - inversion proof.
      inversion H.
    - inversion proof.
      apply (in_inv_trans production a prod g) in H.
      inversion H.
      + unfold remove_prod.
        simpl.
        destruct (production_eq_dec prod a).
        -- apply suc_prop_trans.
        -- simpl.
           unfold remove_prod in IHg.
           assert(In prod g).
           {assert(a = prod \/ In prod g).
            {apply in_inv_trans.
             exact H.
            }
            inversion H3.
            ++ symmetry in H4.
               contradiction.
            ++ exact H4.
           }
           assert(prod_in_g prod g).
           {constructor.
            exact H3.
           }
           apply IHg in H4.
           apply (lt_n_S_trans (grammar_length (remove_prod_aux g prod))
                               (grammar_length g)
                               H4).
      + unfold remove_prod.
        simpl.
        destruct (production_eq_dec prod a).
        -- apply suc_prop_trans.
        -- simpl.
           unfold remove_prod in IHg.
            simpl.
           assert(In prod g).
           {assert(a = prod \/ In prod g).
            {apply in_inv_trans.
             exact H.
            }
            inversion H3.
            ++ symmetry in H4.
               contradiction.
            ++ exact H4.
           }
           assert(prod_in_g prod g).
           {constructor.
            exact H3.
           }
           apply IHg in H4.
           apply (lt_n_S_trans (grammar_length (remove_prod_aux g prod))
                               (grammar_length g)
                               H4).
  Defined.

  (* remove_prod removes just the first occurrence  *)
  Lemma remove_prod_first_occ :
    forall (pr : production) (g1 g2 : grammar)
      (proof_nin : not (prod_in_g pr g1))
      (proof_in : prod_in_g pr (g1 ++ pr :: g2)),
      remove_prod pr (g1 ++ pr :: g2) proof_in = g1 ++ g2.
   Proof.
     intros pr g1 g2 Hprood_nin Hproof_in.
     induction g1 as [| hdg1 tlg1 IH].
     - (* g1 = nil *)
       simpl.
       unfold remove_prod.
       unfold remove_prod_aux.
       destruct (production_eq_dec pr pr) as [Heq_pr | Hneq_pr].
       + (* pr = pr *)
         reflexivity.
       + (* pr <> pr *)
         assert (pr = pr) as Heq_pr.
         {reflexivity.
         }
         contradiction.
     - (* g1 = hdg1 :: tlg1 *)
       unfold remove_prod.
       unfold remove_prod_aux.
       simpl.
       destruct (production_eq_dec pr hdg1) as [Heq_pr | Hneq_pr].
       + (* pr = hdg1 *)
         rewrite <- Heq_pr in Hprood_nin.
         assert (prod_in_g pr (pr :: tlg1)) as Hprod_in.
         {unfold prod_in_g.
          constructor.
          apply in_eq.
         }
         contradiction.
       + (* pr <> hdg1 *)
         fold remove_prod_aux.
         (* use IH *)
         assert(prod_in_g pr (tlg1 ++ pr :: g2)) as Hprod_in.
         {constructor.
          apply in_elt.
         }
         assert(remove_prod pr (tlg1 ++ pr :: g2) Hprod_in = tlg1 ++ g2)
           as IHinst.
         {assert (~ prod_in_g pr tlg1) as Hnprod_in_tlg1.
          {intro Hprod_in_tlg1.
           assert(prod_in_g pr (hdg1 :: tlg1)) as Hprod_in_hd_tlg1.
           {constructor.
            inversion Hprod_in_tlg1 as [pr' tlg1' Hin Heq_pr Heq_tlg1].
            apply in_cons.
            exact Hin.
           }
           contradiction.
          }
          apply (IH Hnprod_in_tlg1 Hprod_in).
         }

         unfold remove_prod in IHinst.
         rewrite IHinst.
         reflexivity.
   Qed.

   (* another way of specifying that remove_prod only removes one prod *)
  Lemma remove_prod_in_g :
    forall (pr1 pr2 : production) (g : grammar)
      (proof_in : prod_in_g pr1 g),
      prod_in_g pr2 (remove_prod pr1 g proof_in) ->
      prod_in_g pr2 g.
  Proof.
    intros pr1 pr2 g Hproof_in Hprod_in.
    assert(exists (g1 g2 : grammar), g = g1 ++ pr1 :: g2 /\
          not (prod_in_g pr1 g1))
      as Hg_split.
    {apply prod_in_g_split.
     exact Hproof_in.
    }
    inversion Hg_split as [g1 (g2, Hg_split')].
    clear Hg_split.

    inversion Hg_split' as [Hg_split Hnprod_in].

    revert Hprod_in.
    revert Hproof_in.
    rewrite Hg_split.
    intros Hproof_in Hprod_in.
    
    assert(remove_prod pr1 (g1 ++ pr1 :: g2) Hproof_in = g1 ++ g2)
      as Hremove_prod.
    {apply remove_prod_first_occ.
     exact Hnprod_in.
    }

    rewrite Hremove_prod in Hprod_in.
    inversion Hprod_in as [pr2' g1_g2 Hin_g1_g2 Heq_pr2 Heq_g1_g2].
    
    rewrite in_app_iff in Hin_g1_g2.

    constructor.
    rewrite in_app_iff.
    inversion Hin_g1_g2 as [Hin_pr2_g1 | Hin_pr2_g2].
    - (* In pr2 g1 *)
      left.
      exact Hin_pr2_g1.
    - (* In pr2 g2 *)
      right.
      apply in_cons.
      exact Hin_pr2_g2.
  Qed. 


  (* more characterization lemmas for remove_prod *)
  Lemma remove_prod_in_g_neq :
    forall (pr1 pr2 : production) (g : grammar)
      (proof_in : prod_in_g pr2 g)
      (proof_neq : pr1 <> pr2),
      prod_in_g pr1 g ->
      prod_in_g pr1 (remove_prod pr2 g proof_in).
  Proof.
    intros pr1 pr2 g Hproof_in_pr2 Hneq Hproof_in_pr1.

    assert(exists (g1 g2 : grammar), g = g1 ++ pr2 :: g2 /\
                                not (prod_in_g pr2 g1))
      as [g1 (g2, (Hsplit_g_pr2, Hnot_pr2_g1))].
    {generalize prod_in_g_split; intro lemma.
     eauto.
    }

    revert Hproof_in_pr2.
    rewrite Hsplit_g_pr2.
    intro Hproof_in_pr2.
    assert(remove_prod pr2 (g1 ++ pr2 :: g2) Hproof_in_pr2 = g1 ++ g2)
      as Hremove_pr2.
    {generalize remove_prod_first_occ; intro lemma.
     eauto.
    }

    rewrite Hremove_pr2.
    clear Hnot_pr2_g1 Hproof_in_pr2 Hremove_pr2.
    
    rewrite Hsplit_g_pr2 in Hproof_in_pr1.
    unfold prod_in_g in Hproof_in_pr1.
    inversion Hproof_in_pr1 as [prod g' Hin_pr1_g Heq_prod Heq_g'].

    rewrite in_app_iff in Hin_pr1_g.

    inversion Hin_pr1_g as [Hin_pr1_g1 | Hin_pr1_tl].
    - (* In pr1 g1 *)
      unfold prod_in_g.
      constructor.

      rewrite in_app_iff.
      left.
      exact Hin_pr1_g1.
    - (* In pr1 tl *)
      inversion Hin_pr1_tl as [Heq_pr1_pr2 | Hin_pr1_g2].
      + (* pr1 = pr2 *)
        apply eq_sym in Heq_pr1_pr2.
        contradiction.
      + (* In pr1 g2 *)
        constructor.
        rewrite in_app_iff.
        right.
        exact Hin_pr1_g2.
  Qed.
    
  Lemma remove_prod_in_g_comm :
    forall (pr1 pr2 : production) (g : grammar)
      (proof_in : prod_in_g pr1 g),
      prod_in_g pr2 (remove_prod pr1 g proof_in) ->
      exists (proof_in_pr2 : prod_in_g pr2 g),
        prod_in_g pr1 (remove_prod pr2 g proof_in_pr2).
  Proof.
    intros pr1 pr2 g Hproof_in_pr1 Hprod_in_pr2.

    assert(prod_in_g pr2 g)
      as Hprod_in_pr2'.
    {apply (remove_prod_in_g pr1 pr2 g Hproof_in_pr1).
     exact Hprod_in_pr2.
    }

    exists Hprod_in_pr2'.

    (* reason about the result of remove_prod *)
    assert(exists (g1 g2 : grammar), g = g1 ++ pr1 :: g2 /\ not (prod_in_g pr1 g1))
      as Hsplit_g_pr1.
    {apply prod_in_g_split.
     exact Hproof_in_pr1.
    }
    inversion Hsplit_g_pr1 as [g1 (g2, (Heq_g_pr1, Hnot_prod_in_pr1))].
    clear Hsplit_g_pr1.

    assert(remove_prod pr1 g Hproof_in_pr1 = g1 ++ g2)
      as Heq_g_remove_pr1.
    {clear Hprod_in_pr2.
     revert Hproof_in_pr1.
     rewrite Heq_g_pr1.
     intros Hproof_in_pr1.
     apply (remove_prod_first_occ pr1 g1 g2 Hnot_prod_in_pr1 Hproof_in_pr1).
    }

    rewrite Heq_g_remove_pr1 in Hprod_in_pr2.
    inversion Hprod_in_pr2 as [prod g_res Hin_pr2 Heq_prod Heq_g_res].

    rewrite (in_app_iff_strong _ _ _ _ production_eq_dec) in Hin_pr2.

    inversion Hin_pr2 as [Hpr2_in_g1 | Hpr2_in_g2].
    - (* In pr2 g1 *)
      apply prod_in_g_ev in Hpr2_in_g1.
      fold prod_in_g in Hpr2_in_g1.
      apply prod_in_g_split in Hpr2_in_g1.
      inversion Hpr2_in_g1 as [g11 (g12, (Heq_g1, Hnot_prod_in_pr2))].
      clear Hpr2_in_g1.

      revert Hprod_in_pr2'.
      rewrite Heq_g_pr1.
      rewrite Heq_g1.
      rewrite <- app_assoc.

      intro Hprod_in_pr2'.
      assert(remove_prod pr2 (g11 ++ (pr2 :: g12) ++ pr1 :: g2) Hprod_in_pr2'
             = g11 ++ g12 ++ pr1 :: g2)
        as Heq_remove_prod_pr2.
      {apply remove_prod_first_occ.
       exact Hnot_prod_in_pr2.
      }

      rewrite Heq_remove_prod_pr2.

      constructor.
      rewrite in_app_iff.
      right.
      rewrite in_app_iff.
      right.
      apply in_eq.
    - (* In pr2 g2 *)
      (* analogous to the previous case *)
      inversion Hpr2_in_g2 as [Hnot_in_g1 Hpr2_in_g2'].
      clear Hpr2_in_g2.
      
      apply prod_in_g_ev in Hpr2_in_g2'.
      fold prod_in_g in Hpr2_in_g2'.
      apply prod_in_g_split in Hpr2_in_g2'.
      inversion Hpr2_in_g2' as [g21 (g22, (Heq_g2, Hnot_prod_in_pr2))].
      clear Hpr2_in_g2'.

      revert Hprod_in_pr2'.
      rewrite Heq_g_pr1.
      rewrite Heq_g2.

      intro Hprod_in_pr2'.

      destruct (production_eq_dec pr1 pr2) as [Heq_pr1_pr2 | Hneq_pr1_pr2].
      * (* pr1 = pr2 *)
        rewrite <- Heq_pr1_pr2 in Hnot_in_g1.
        
      assert(remove_prod pr2 (g1 ++ pr1 :: g21 ++ pr2 :: g22) Hprod_in_pr2'
             = g1 ++ g21 ++ pr2 :: g22)
        as Heq_remove_prod_pr2.
      {revert Hprod_in_pr2'.
       rewrite Heq_pr1_pr2.
       intro Hprod_in_pr2'.
       apply remove_prod_first_occ.
       rewrite Heq_pr1_pr2 in Hnot_in_g1.
       intro Hprod_in.
       inversion Hprod_in as [pr2' g1' Hin_g1 Heq_g1].
       contradiction.
      }

      rewrite Heq_remove_prod_pr2.

      constructor.
      rewrite in_app_iff.
      right.
      rewrite in_app_iff.
      right.
      rewrite Heq_pr1_pr2.
      apply in_eq.
    * (* pr1 <> pr2 *)
      assert(not (In pr2 (g1 ++ pr1 :: g21)))
        as Hnot_pr2_in.
      {intro Hpr2_in.
       rewrite in_app_iff in Hpr2_in.
       inversion Hpr2_in as [Hpr2_in_g1 | Hpr2_in_tl].
       - (* In pr2 g1 *)
         contradiction.
       - (* In pr2 (pr1 :: g21) *)
         inversion Hpr2_in_tl as [Hpr2_in_hd | Hpr2_in_tl'].
         + (* pr1 = pr2 *)
           contradiction.
         + (* In pr2 g21 *)
           apply prod_in_g_ev in Hpr2_in_tl'.
           fold prod_in_g in Hpr2_in_tl'.
           contradiction.
      }

      assert(remove_prod pr2 (g1 ++ pr1 :: g21 ++ pr2 :: g22) Hprod_in_pr2'
             = (g1 ++ pr1 :: g21) ++ g22)
        as Heq_remove_prod_pr2.
      {assert(~ (prod_in_g pr2 (g1 ++ pr1 :: g21)))
          as Hnot_pr2_in'.
       {intro Hpr2_in.
        inversion Hpr2_in as [pr2' g' Hin_pr2' Heq_pr2' Heq_g'].
        contradiction.
       }

       assert(g1 ++ pr1 :: g21 ++ pr2 :: g22
              =
              (g1 ++ pr1 :: g21) ++ pr2 :: g22)
         as Hassoc.
       {apply (app_assoc g1 (pr1 :: g21) (pr2 :: g22)).
       }
       revert Hprod_in_pr2'.
       rewrite Hassoc.
       clear Hassoc.

       intro Hprod_in_pr2'.
       apply (remove_prod_first_occ pr2 (g1 ++ pr1 :: g21) g22
                                    Hnot_pr2_in' Hprod_in_pr2').
      }

      rewrite Heq_remove_prod_pr2.

      constructor.
      rewrite in_app_iff.
      left.
      rewrite in_app_iff.
      right.
      apply in_eq.
  Qed.

  (* useful when reasoning about soundness of our manipulation of 
     grammars *)
  Lemma remove_prod_comm :
    forall (pr1 pr2 : production)
      (g : grammar)
      (proof_in_pr1 : prod_in_g pr1 g)
      (proof_in_pr2 : prod_in_g pr2 (remove_prod pr1 g proof_in_pr1)),
    exists (proof_in_pr2' : prod_in_g pr2 g)
      (proof_in_pr1' : prod_in_g pr1 (remove_prod pr2 g proof_in_pr2')),
        remove_prod pr2 (remove_prod pr1 g proof_in_pr1) proof_in_pr2
        = remove_prod pr1 (remove_prod pr2 g proof_in_pr2') proof_in_pr1'.
  Proof.
    intros pr1 pr2 g Hproof_in_pr1 Hproof_in_pr2.

    assert(exists (proof_in_pr2 : prod_in_g pr2 g),
              prod_in_g pr1 (remove_prod pr2 g proof_in_pr2))
      as Hprod_in_g_pr1.
    {apply (remove_prod_in_g_comm pr1 pr2 g Hproof_in_pr1 Hproof_in_pr2).
    }
    inversion Hprod_in_g_pr1 as [Hprod_in_g_pr2 Hprod_in_g_pr1'].
    clear Hprod_in_g_pr1.

    exists Hprod_in_g_pr2.
    exists Hprod_in_g_pr1'.

    (* reason about the result of remove_prod *)
    assert(exists (g1 g2 : grammar), g = g1 ++ pr1 :: g2 /\ not (prod_in_g pr1 g1))
      as Hsplit_g_pr1.
    {apply prod_in_g_split.
     exact Hproof_in_pr1.
    }
    inversion Hsplit_g_pr1 as [g1 (g2, (Heq_g_pr1, Hnot_prod_in_pr1))].
    clear Hsplit_g_pr1.

    assert(remove_prod pr1 g Hproof_in_pr1 = g1 ++ g2)
      as Heq_remove_pr1.
    {revert Hproof_in_pr2.
     revert Hproof_in_pr1.
     rewrite Heq_g_pr1.
     intros Hproof_in_pr1 Hproof_in_pr2.
     apply remove_prod_first_occ.
     exact Hnot_prod_in_pr1.
    }

    revert Hproof_in_pr2.
    rewrite Heq_remove_pr1.
    intro Hproof_in_pr2.

    inversion Hproof_in_pr2 as [prod' g' Hin_pr2_g1_g2 Heq_prod Heq_g'].
    rewrite (in_app_iff_strong _ _ _ _ production_eq_dec) in Hin_pr2_g1_g2.

    clear Heq_g' Heq_prod g' prod'.
    
    inversion Hin_pr2_g1_g2 as [Hin_pr2 | (Hnin_pr2_g1, Hin_pr2_g2)].
    - (* In pr2 g1 *)
      apply prod_in_g_ev in Hin_pr2.
      fold prod_in_g in Hin_pr2.

      assert(exists (g11 g12 : grammar), g1 = g11 ++ pr2 :: g12 /\
                                    not (prod_in_g pr2 g11))
      as Hsplit_g1_pr2.
      {apply (prod_in_g_split g1 pr2 Hin_pr2).
      }
      inversion Hsplit_g1_pr2 as [g11 (g12, (Heq_g_pr2, Hnot_prod_in_pr2))].
      clear Hsplit_g1_pr2.

      assert(remove_prod pr2 g Hprod_in_g_pr2 = g11 ++ g12 ++ pr1 :: g2)
      as Heq_remove_pr2.
      {revert Hprod_in_g_pr1'.
       revert Hprod_in_g_pr2.
       rewrite Heq_g_pr1.
       rewrite Heq_g_pr2.
       intros Hprod_in_g_pr2 Hprod_in_g_pr1'.

       assert((g11 ++ pr2 :: g12) ++ pr1 :: g2 =
              g11 ++ (pr2 :: g12 ++ pr1 :: g2))
         as Hassoc.
       {rewrite <- app_assoc.
        reflexivity.
       }

       revert Hprod_in_g_pr1'.
       revert Hprod_in_g_pr2.
       rewrite Hassoc.
       intros Hprod_in_g_pr2 Hprod_in_g_pr1'.
       
       apply remove_prod_first_occ.
       exact Hnot_prod_in_pr2.
      }
      revert Hprod_in_g_pr1'.
      rewrite Heq_remove_pr2.
      revert Hproof_in_pr2.
      rewrite Heq_g_pr2.
      intros Hproof_in_pr2 Hprod_in_g_pr1'.

      clear Heq_remove_pr1 Heq_remove_pr2.
      assert(remove_prod pr2 ((g11 ++ pr2 :: g12) ++ g2) Hproof_in_pr2
             = g11 ++ g12 ++ g2)
        as Heq_remove_pr2.
      {revert Hproof_in_pr2.
       rewrite <- (app_assoc g11 (pr2 :: g12) g2).
       intro Hproof_in_pr2.
       apply remove_prod_first_occ.
       exact Hnot_prod_in_pr2.
      }

      rewrite Heq_remove_pr2.
      clear Heq_remove_pr2.

      assert(remove_prod pr1 (g11 ++ g12 ++ pr1 :: g2) Hprod_in_g_pr1'
             =
             (g11 ++ g12) ++ g2)
        as Heq_remove_pr1.
      {assert(g11 ++ g12 ++ pr1 :: g2 = (g11 ++ g12) ++ pr1 :: g2)
          as Hassoc.
       {rewrite app_assoc.
        reflexivity.
       }
       revert Hprod_in_g_pr1'.
       rewrite Hassoc.
       intro Hprod_in_g_pr1'.
       
       apply remove_prod_first_occ.

       intro Hnot_prod_in_pr1'.
       assert(prod_in_g pr1 (g11 ++ pr2 :: g12))
         as Hprod_in_pr1.
       {rewrite Heq_g_pr2 in Hnot_prod_in_pr1.

       inversion Hnot_prod_in_pr1' as [prod g' Hin_pr1_g11_g12 Heq_prod
                                            Heq_g'].

       rewrite in_app_iff in Hin_pr1_g11_g12.
       constructor.
       rewrite in_app_iff.
       
       inversion Hin_pr1_g11_g12 as [Hin_pr1_g11 | Hin_pr1_g12].
        - (* In pr1 g11 *)
          left.
          exact Hin_pr1_g11.
        - (* In pr1 g12 *)
          right.
          apply in_cons.
          exact Hin_pr1_g12.
       }

       rewrite <- Heq_g_pr2 in Hprod_in_pr1.

       contradiction.
      }

      rewrite Heq_remove_pr1.

      rewrite app_assoc.
      reflexivity.
    - (* In pr2 g2 *)
      apply prod_in_g_ev in Hin_pr2_g2.
      fold prod_in_g in Hin_pr2_g2.

      destruct (production_eq_dec pr1 pr2) as [Heq_pr1_pr2 | Hneq_pr1_pr2].
      + (* pr1 = pr2 *)
        assert(remove_prod pr2 g Hprod_in_g_pr2 = g1 ++ g2)
          as Heq_remove_pr2.
        {revert Hprod_in_g_pr1'.
         revert Hprod_in_g_pr2.
         rewrite Heq_g_pr1.
         rewrite Heq_pr1_pr2.
         intros Hprod_in_g_pr2 Hprod_in_g_pr1'.
         
         apply remove_prod_first_occ.
         rewrite Heq_pr1_pr2 in Hnot_prod_in_pr1.
         exact Hnot_prod_in_pr1.
        }
        revert Hprod_in_g_pr1'.
        rewrite Heq_remove_pr2.
        rewrite Heq_pr1_pr2.
        intro Hprod_in_g_pr1'.

        assert(exists (g21 g22 : grammar), g2 = g21 ++ pr2 :: g22 /\
                                      not (prod_in_g pr2 g21))
          as Hsplit_g1_pr2.
        {apply (prod_in_g_split g2 pr2 Hin_pr2_g2).
        }
        inversion Hsplit_g1_pr2 as [g21 (g22, (Heq_g_pr2, Hnot_prod_in_pr2))].
        clear Hsplit_g1_pr2.

        revert Hproof_in_pr2.
        revert Hprod_in_g_pr1'.
        rewrite Heq_g_pr2.
        intros Hprod_in_g_pr1' Hproof_in_pr2.
        
        clear Hproof_in_pr1 Hprod_in_g_pr2 Heq_g_pr1 Hnot_prod_in_pr1
              Heq_remove_pr1 Hin_pr2_g1_g2 Heq_remove_pr2.
        assert(remove_prod pr2 (g1 ++ g21 ++ pr2 :: g22) Hproof_in_pr2
               =
               g1 ++ g21 ++ g22)
          as Heq_remove_pr2.
        { assert(g1 ++ g21 ++ pr2 :: g22 = (g1 ++ g21) ++ pr2 :: g22)
            as Hassoc.
         {rewrite app_assoc.
          reflexivity.
         }
         revert Hproof_in_pr2.
         rewrite Hassoc.
         clear Hassoc.
         intro Hproof_in_pr2.

         assert(g1 ++ g21 ++ g22 = (g1 ++ g21) ++ g22)
           as Hassoc.
         {rewrite app_assoc.
          reflexivity.
         }
         rewrite Hassoc.
         
         apply remove_prod_first_occ.

         intro Hprod_in_g1_g21.
         inversion Hprod_in_g1_g21 as [prod' g' Hin_pr2_g1_g21 Heq_prod Heq_g'].

         rewrite in_app_iff in Hin_pr2_g1_g21.

         inversion Hin_pr2_g1_g21 as [Hpr2_in_g1 | Hpr2_in_g21].
          - (* In pr2 g1 *)
            contradiction.
          - (* In pr2 g21 *)
            apply prod_in_g_ev in Hpr2_in_g21.
            fold prod_in_g in Hpr2_in_g21.
            contradiction.
        }

        rewrite Heq_remove_pr2.
        clear Heq_remove_pr2.
        
        assert(remove_prod pr2 (g1 ++ g21 ++ pr2 :: g22) Hprod_in_g_pr1'
               =
               g1 ++ g21 ++ g22)
          as Heq_remove_pr2.
        { assert(g1 ++ g21 ++ pr2 :: g22 = (g1 ++ g21) ++ pr2 :: g22)
            as Hassoc.
         {rewrite app_assoc.
          reflexivity.
         }
         revert Hproof_in_pr2.
         revert Hprod_in_g_pr1'.
         rewrite Hassoc.
         clear Hassoc.
         intros Hprod_in_g_pr1' Hproof_in_pr2.

         assert(g1 ++ g21 ++ g22 = (g1 ++ g21) ++ g22)
           as Hassoc.
         {rewrite app_assoc.
          reflexivity.
         }
         rewrite Hassoc.
         
         apply remove_prod_first_occ.

         intro Hprod_in_g1_g21.
         inversion Hprod_in_g1_g21 as [prod' g' Hin_pr2_g1_g21 Heq_prod Heq_g'].

         rewrite in_app_iff in Hin_pr2_g1_g21.

         inversion Hin_pr2_g1_g21 as [Hpr2_in_g1 | Hpr2_in_g21].
          - (* In pr2 g1 *)
            contradiction.
          - (* In pr2 g21 *)
            apply prod_in_g_ev in Hpr2_in_g21.
            fold prod_in_g in Hpr2_in_g21.
            contradiction.
        }
        rewrite Heq_remove_pr2.

        reflexivity.
      + (* pr1 <> pr2 *)
        assert(exists (g21 g22 : grammar), g2 = g21 ++ pr2 :: g22 /\
                                      not (prod_in_g pr2 g21))
          as Hsplit_g1_pr2.
        {apply (prod_in_g_split g2 pr2 Hin_pr2_g2).
        }
        inversion Hsplit_g1_pr2 as [g21 (g22, (Heq_g_pr2, Hnot_prod_in_pr2))].
        clear Hsplit_g1_pr2.

        revert Hproof_in_pr2.
        revert Hprod_in_g_pr1'.
        rewrite Heq_g_pr2.
        intros Hprod_in_g_pr1' Hproof_in_pr2.
        
        clear Hproof_in_pr1
              Heq_remove_pr1 Hin_pr2_g1_g2.

        assert(g = (g1 ++ pr1 :: g21) ++ pr2 :: g22)
          as Hg_eq.
        {rewrite Heq_g_pr1.
         rewrite Heq_g_pr2.
         rewrite <- app_assoc.
         reflexivity.
        }
        revert Hprod_in_g_pr1'.
        revert Hprod_in_g_pr2.
        rewrite Hg_eq.
        intros Hprod_in_g_pr2 Hprod_in_g_pr1'.
        
        assert(remove_prod pr2 ((g1 ++ pr1 :: g21) ++ pr2 :: g22) Hprod_in_g_pr2
               =
               (g1 ++ pr1 :: g21) ++ g22)
          as Heq_remove_pr2.
        {apply remove_prod_first_occ.
         intro Hpr2_in_g1_g21.
         inversion Hpr2_in_g1_g21 as [prod' g' Hin_pr2_g1_pr1_g21 Heq_prod
                                            Heq_g'].
         clear Heq_prod Heq_g'.

         rewrite in_app_iff in Hin_pr2_g1_pr1_g21.

         inversion Hin_pr2_g1_pr1_g21 as [Hpr2_g1 | Hpr2_g21].
         - (* In pr2 g1 *)
           contradiction.
         - (* In pr2 pr1 :: g21 *)
           simpl in Hpr2_g21.
           inversion Hpr2_g21 as [Heq_pr1_pr2 | Hpr2_in_g21].
           + (* pr1 = pr2 *)
             contradiction.
           + (* In pr2 g21 *)
             apply prod_in_g_ev in Hpr2_in_g21.
             fold prod_in_g in Hpr2_in_g21.
             contradiction.
        }
        revert Hprod_in_g_pr1'.
        rewrite Heq_remove_pr2.
        intro Hprod_in_g_pr1'.
        clear Heq_remove_pr2.

        assert(g1 ++ g21 ++ pr2 :: g22 = (g1 ++ g21) ++ pr2 :: g22)
          as Hassoc.
        {rewrite app_assoc.
         reflexivity.
        }
        revert Hproof_in_pr2.
        rewrite Hassoc.
        intro Hproof_in_pr2.
        clear Hassoc.
        
        assert(remove_prod pr2 ((g1 ++ g21) ++ pr2 :: g22) Hproof_in_pr2
              = (g1 ++ g21) ++ g22)
          as Heq_remove.
        {apply remove_prod_first_occ.
         intro Hprod_in_g1_g21.
         inversion Hprod_in_g1_g21 as [prod g' Hev_in Heq_prod Heq_g].
         clear Heq_prod Heq_g prod g'.

         rewrite in_app_iff in Hev_in.
         inversion Hev_in as [Hpr2_in_g1 | Hpr2_in_g21].
         - (* In pr2 g1 *)
           contradiction.
         - (* In pr2 g21 *)
           apply prod_in_g_ev in Hpr2_in_g21.
           fold prod_in_g in Hpr2_in_g21.
           contradiction.
        }
        rewrite Heq_remove.
        clear Heq_remove.

        assert((g1 ++ pr1 :: g21) ++ g22 = g1 ++ pr1 :: (g21 ++ g22))
          as Hassoc.
        {rewrite <- app_assoc.
         reflexivity.
        }
        revert Hprod_in_g_pr1'.
        rewrite Hassoc.
        clear Hassoc.
        intro Hprod_in_g_pr1'.
        
        assert(remove_prod pr1 (g1 ++ pr1 :: g21 ++ g22) Hprod_in_g_pr1'
              = g1 ++ (g21 ++ g22))
          as Heq_remove.
        {apply remove_prod_first_occ.
         exact Hnot_prod_in_pr1.
        }
        rewrite Heq_remove.
        clear Heq_remove.

        rewrite app_assoc.
        reflexivity.
  Qed.

  (* proof of prod_in_g does not determine the result of remove_prod *)
  Lemma remove_prod_prod_in_g_irrelevance :
    forall (g : grammar) (pr : production)
      (proof1 proof2 : prod_in_g pr g),
      remove_prod pr g proof1 = remove_prod pr g proof2.
  Proof.
    intros g pr proof1 proof2.

    assert(exists (g1 g2 : grammar), g = g1 ++ pr :: g2 /\
                                not (prod_in_g pr g1))
      as [g1 (g2, (Hprod_in_g_split, Hnin_pr_g2))].
    {generalize prod_in_g_split; intro lemma.
     eauto.
    }

    revert proof1 proof2.
    rewrite Hprod_in_g_split.
    intros proof1 proof2.
    
    assert(remove_prod pr (g1 ++ pr :: g2) proof1 = g1 ++ g2)
      as Hremove_proof1.
    {generalize remove_prod_first_occ; intro lemma.
     eauto.
    }
    rewrite Hremove_proof1.
    clear Hremove_proof1.
    
    assert(remove_prod pr (g1 ++ pr :: g2) proof2 = g1 ++ g2)
      as Hremove_proof2.
    {generalize remove_prod_first_occ; intro lemma.
     eauto.
    }
    rewrite Hremove_proof2.
    clear Hremove_proof2.

    reflexivity.
  Qed.
      
  (* useful for inductive reasoning *)
  
  (* transforms the proofs of membership to prods_suf, from proofs_suf , into 
     proofs of membership to [(n1, p)] ++ prods_suf *)
  Fixpoint get_rhs_prods_aux (prods_suf prods : productions)
          (n1 n2 : nonterm)
          (p : pat)
          (eq_proof : prods = [(n1, p)] ++ prods_suf)
          (proofs_suf : list {p' : pat | In (n2, p') prods_suf}) :
    list {p' : pat | In (n2, p') prods} :=
    (match proofs_suf as proofs_suf'
           return proofs_suf = proofs_suf' ->
                  list {p : pat | In (n2, p) prods} with
     | nil                       => (fun eq => nil)
     | (exist _ p' proof) :: tail =>
       (fun eq => (exist (fun pat => In (n2, pat) prods)
                      p'
                      (eq_ind_r (fun prods0 : productions => In (n2, p') prods0)
                                (in_cons_trans production (n1, p) (n2, p') 
                                               prods_suf proof) 
                                eq_proof)) 
                 :: (get_rhs_prods_aux prods_suf prods 
                                      n1 n2 p eq_proof tail))
     end eq_refl).

  (* simple distribution property of get_rhs_prods_aux prods_suf over its last 
     argument, to simplify reasoning about some statements over
     get_rhs_prods_aux   *)
  Lemma get_rhs_prods_aux_dist :
    forall (prods_suf prods : productions)
      (n1 n2 : nonterm)
      (p : pat)
      (eq_proof : prods = [(n1, p)] ++ prods_suf)
      (proofs_suf1 proofs_suf2 : list {p' : pat | In (n2, p') prods_suf}),
      get_rhs_prods_aux prods_suf prods n1 n2 p eq_proof
                        (proofs_suf1 ++ proofs_suf2) =
      (get_rhs_prods_aux prods_suf prods n1 n2 p eq_proof proofs_suf1)
        ++
        (get_rhs_prods_aux prods_suf prods n1 n2 p eq_proof proofs_suf2).
  Proof.
    intros prods_suf prods n1 n2 p eq_proof.
    induction proofs_suf1 as [ | h tail Hind].
    + (* proofs_suf1 = nil *)
      reflexivity.
    + (* proofs_suf1 = a :: proofs_suf1' *)
      intro proofs_suf2.
      destruct h.
      simpl.
      assert(get_rhs_prods_aux prods_suf prods n1 n2 p eq_proof
                               (tail ++ proofs_suf2) =
             get_rhs_prods_aux prods_suf prods n1 n2 p eq_proof tail
             ++
             get_rhs_prods_aux prods_suf prods n1 n2 p eq_proof proofs_suf2)
        as Heq.
      {apply Hind.
      }
      rewrite Heq.
      reflexivity.
  Qed.

  (* returns a list with patterns and proofs of membership for every pair
     (n, p) in prods *)
  Fixpoint get_rhs_prods (prods : productions) (n : nonterm) : 
    list {p : pat | In (n, p) prods} :=
    
    (match prods as prods' return prods = prods' -> 
                                  list {p : pat | In (n, p) prods} with
     | nil            => (fun _ => nil)

     | (n', p) :: tail =>

       (fun eq : prods = (n', p) :: tail =>
          
         match (nonterm_eq_dec n n') as proof return
         (nonterm_eq_dec n n') = proof -> list {p : pat | In (n, p) prods} with
         
         | left eq_proof => 
           
           fun eqp : (nonterm_eq_dec n n') = left eq_proof =>
             (exist (fun pat => In (n, pat) prods)
                    p 
                    (eq_ind_r (fun prods0 : productions => In (n, p) prods0)
                              (* In (n', p) tail *)
                              (eq_ind_r
                                 (fun n0 : nonterm => In (n0, p) ((n', p) :: tail))
                                 (in_eq_trans production (n', p) tail) eq_proof)
                              eq)) 
               :: (get_rhs_prods_aux tail prods n n p
                                    (* prods = [(n, p)] ++ tail *)
                                    (eq_ind_r 
                                       (fun n0 : nonterm => 
                                          prods = [(n0, p)] ++ tail)
                                       eq eq_proof)
                                    (get_rhs_prods tail n))
         | right _ => 
           
           fun eqp : _ =>
           (get_rhs_prods_aux tail prods n' n p
                                            eq
                                            (get_rhs_prods tail n))
         end eq_refl)
     end eq_refl).

  (* transforms proofs of In (n, p) g into proofs of prod_in_g (n, p) g *)
  Fixpoint get_rhs_aux (g : grammar) (n : nonterm)
                       (l : list {p : pat | In (n, p) g}) : 
    list {p : pat | prod_in_g (n, p) g} :=
    
    match l as l' return l = l' -> list {p : pat | prod_in_g (n, p) g} with
    | nil                      => fun eqp : l = nil => nil
    | (exist _ p proof) :: tail =>
      fun eqp : l = (exist _ p proof) :: tail =>
        (exist (fun p => prod_in_g (n, p) g) p (prod_in_g_ev (n, p) g proof)) 
          :: (get_rhs_aux g n tail)
    end eq_refl.

  Lemma get_rhs_aux_split :
    forall (g : grammar) (n : nonterm) (l1 l2 : list {p : pat | In (n, p) g}),
      get_rhs_aux g n (l1 ++ l2) = (get_rhs_aux g n l1) ++ get_rhs_aux g n l2.
  Proof.
    intros g n.
    induction l1 as [ | hl1 tl1].
    - (* l1 = nil *)
      intro l2.
      reflexivity.
    - (* l1 = a :: l1' *)
      intro l2.
      simpl.
      destruct hl1 as [p ev].
      remember (exist (fun p0 : pat => prod_in_g (n, p0) g) p
                      (prod_in_g_ev (n, p) g ev)) as elem.
      rewrite (IHtl1 l2).
      rewrite <- app_comm_cons.
      reflexivity.
  Qed.
  
  (* to obtain the right-hand side of every production from a given 
     non-terminal *)
  Definition get_rhs (g : grammar) (n : nonterm) : 
    list {p : pat | prod_in_g (n, p) g} :=
    (get_rhs_aux g n (get_rhs_prods g n)).

  Lemma get_rhs_prods_split : forall (prods : productions) (n : nonterm) (p : pat)
                                (_ : In (n, p) prods),
      exists (l1 l2 : list {pa : pat | In (n, pa) prods})
        (proof' : In (n, p) prods),
        get_rhs_prods prods n = l1 ++ ((exist (fun pa => In (n, pa) prods)
                                              p
                                              proof') :: nil) ++ l2.
  Proof.
    induction prods.
    + (* prods = nil *)
      intros n p proof.
      inversion proof.
    + (* prods = a :: prods'' *)
      intros n p proof.
      inversion proof as [Heq | Hin].
      - (* a = (n, p) *)
        revert proof.
        rewrite Heq.
        intro proof.
        simpl.
        destruct (nonterm_eq_dec n n).
        ++ (* n = n *)
           destruct e.
           exists nil.
           simpl.
           (* simplifying sub-expressions *)
           assert(eq_ind_r
                    (fun n0 : nonterm =>
                       (n, p) :: prods = (n0, p) :: prods)
                    eq_refl eq_refl = eq_refl) as Heq_refl.
           {reflexivity.
           }
           (* TODO: how to avoid this? *)
           unfold productions.
           unfold production.
           rewrite Heq_refl.
           assert (eq_ind_r
                    (fun n0 : nonterm =>
                       (n, p) = (n0, p) \/ In (n0, p) prods)
                    (in_eq_trans (nonterm * pat) (n, p) prods)
                    eq_refl = (in_eq_trans (nonterm * pat) (n, p) prods))
             as Hin_eq.
           {reflexivity.
           }
           rewrite Hin_eq.
           assert (eq_ind_r
                     (fun prods0 : list (nonterm * pat) =>
                        In (n, p) prods0)
                     (in_eq_trans (nonterm * pat) (n, p) prods)
                     eq_refl = (in_eq_trans (nonterm * pat) (n, p) prods))
             as Hin_eq'.
           {reflexivity.
           }
           rewrite Hin_eq'.
           exists (get_rhs_prods_aux prods ((n, p) :: prods) n n p
                                eq_refl (get_rhs_prods prods n)).
           exists (in_eq_trans (nonterm * pat) (n, p) prods).
           reflexivity.
        ++ (* n <> n *)
           assert(n = n) as Heq_n.
           {reflexivity.
           }
           contradiction.
      - (* In (n, p) prods *)
        destruct a.
        simpl.
        destruct (nonterm_eq_dec n n0) as [Heqn | Hneqn].
        ++ (* n = n0 *)
           destruct Heqn.
           assert(exists (l1' l2' : list {pa : pat | In (n, pa) prods}) 
                    (proof' : In (n, p) prods),
                     get_rhs_prods prods n =
                     l1' ++ [exist (fun pa : pat => In (n, pa) prods) p proof'] ++
                         l2') as Hget_rhs.
           {apply IHprods.
            exact Hin.
           }
           inversion Hget_rhs as [l1' Hget_rhs'].
           clear Hget_rhs.
           inversion Hget_rhs' as [l2' Hget_rhs''].
           clear Hget_rhs'.
           inversion Hget_rhs'' as [proof'' Hget_rhs'''].
           clear Hget_rhs''.
           rewrite Hget_rhs'''.
           clear Hget_rhs'''.
           assert(eq_ind_r
                    (fun n0 : nonterm =>
                       (n, p0) :: prods = (n0, p0) :: prods)
                    eq_refl eq_refl = eq_refl) as Heq_refl.
           {reflexivity.
           }
           (* TODO: how to avoid this? *)
           unfold productions.
           unfold production.
           rewrite Heq_refl.
           clear Heq_refl.
           rewrite app_assoc.
           assert(get_rhs_prods_aux prods ((n, p0) :: prods) n n p0 eq_refl
                                    ((l1'
                                      ++
                                      [exist (fun pa : pat => In (n, pa) prods) p
                                             proof'']) ++ l2') =
                  (get_rhs_prods_aux prods ((n, p0) :: prods) n n p0 eq_refl
                                     (l1' ++
                                          [exist (fun pa : pat => In (n, pa) prods) p
                                                 proof'']))
                    ++
                  (get_rhs_prods_aux prods ((n, p0) :: prods) n n p0 eq_refl l2'))
             as Hget_rhs_prods_aux.
           {apply get_rhs_prods_aux_dist.
           }
           (* TODO: same problem here *)
           unfold productions in Hget_rhs_prods_aux.
           unfold production in Hget_rhs_prods_aux.
           rewrite Hget_rhs_prods_aux.
           clear Hget_rhs_prods_aux.
           assert(get_rhs_prods_aux prods ((n, p0) :: prods) n n
                                    p0 eq_refl
                                    (l1' ++
                                         [exist (fun pa : pat => In (n, pa) prods) p
                                                proof'']) =
                  (get_rhs_prods_aux prods ((n, p0) :: prods) n n
                                    p0 eq_refl l1')
                  ++
                  (get_rhs_prods_aux prods ((n, p0) :: prods) n n
                                     p0 eq_refl
                                     [exist (fun pa : pat => In (n, pa) prods) p
                                            proof'']))
           as Hget_rhs_prods_aux.
           {apply get_rhs_prods_aux_dist.
           }
           unfold productions in Hget_rhs_prods_aux.
           unfold production in Hget_rhs_prods_aux.
           rewrite Hget_rhs_prods_aux.
           clear Hget_rhs_prods_aux.
           assert(eq_ind_r
                    (fun n0 : nonterm =>
                       (n, p0) = (n0, p0) \/ In (n0, p0) prods)
                    (in_eq_trans (nonterm * pat) (n, p0) prods)
                    eq_refl =
                  (in_eq_trans (nonterm * pat) (n, p0) prods)) as Heq_trans.
           {reflexivity.
           }
           rewrite Heq_trans.
           clear Heq_trans.
           assert(eq_ind_r
                    (fun prods0 : list (nonterm * pat) =>
                       In (n, p0) prods0)
                    (in_eq_trans (nonterm * pat) (n, p0) prods)
                    eq_refl = (in_eq_trans (nonterm * pat) (n, p0) prods))
             as Heq_trans.
           {reflexivity.
           }
           rewrite Heq_trans.
           clear Heq_trans.
           remember (get_rhs_prods_aux prods ((n, p0) :: prods) n n
                                       p0 eq_refl l2') as l2'' eqn:Heql2'.
           unfold productions in Heql2'.
           unfold production in Heql2'.
           rewrite <- Heql2'.
           remember (get_rhs_prods_aux prods ((n, p0) :: prods) n n
                                       p0 eq_refl l1') as l1'' eqn:Heql1'.
           unfold productions in Heql1'.
           unfold production in Heql1'.
           rewrite <- Heql1'.
           simpl.
           assert(eq_ind_r
                    (fun prods0 : productions =>
                       In (n, p) prods0)
                    (in_cons_trans production 
                                   (n, p0) (n, p) prods proof'') eq_refl =
                  (in_cons_trans production 
                                 (n, p0) (n, p) prods proof''))
             as Hin_cons.
           {reflexivity.
           }
           unfold productions.
           unfold production.
           unfold productions in Hin_cons.
           unfold production in Hin_cons.
           rewrite Hin_cons.
           clear Hin_cons.
           remember (exist
                     (fun pat0 : pat =>
                        (n, p0) = (n, pat0) \/ In (n, pat0) prods) p0
                     (in_eq_trans (nonterm * pat) (n, p0) prods)) as hd eqn : Heqhd.
           remember (exist
                       (fun pat0 : pat =>
                          (n, p0) = (n, pat0) \/ In (n, pat0) prods)
                       p
                       (in_cons_trans (nonterm * pat) 
                                      (n, p0) (n, p) prods proof''))
             as in_proof eqn : Heqin_cons.

           exists (hd :: l1'').
           exists l2''.
           exists (in_cons_trans (nonterm * pat)
                            (n, p0) (n, p) prods proof'').
           rewrite <- Heqin_cons.
           rewrite <- app_comm_cons.
           rewrite app_comm_cons.
           rewrite (app_comm_cons _ [in_proof] _).
           rewrite <- (app_assoc (hd :: l1'') [in_proof] l2'').
           rewrite (app_comm_cons _ ([in_proof] ++ l2'') _).
           reflexivity.
        ++ (* n <> n0 *)
           assert(exists (l1' l2' : list {pa : pat | In (n, pa) prods}) 
                    (proof' : In (n, p) prods),
                     get_rhs_prods prods n =
                     l1' ++ [exist (fun pa : pat => In (n, pa) prods) p proof'] ++
                         l2') as Hget_rhs.
           {apply IHprods.
            exact Hin.
           }
           inversion Hget_rhs as [l1' Hget_rhs'].
           clear Hget_rhs.
           inversion Hget_rhs' as [l2' Hget_rhs''].
           clear Hget_rhs'.
           inversion Hget_rhs'' as [proof'' Hget_rhs'''].
           clear Hget_rhs''.
           rewrite Hget_rhs'''.
           clear Hget_rhs'''.
           rewrite app_assoc.
           assert(get_rhs_prods_aux prods ((n0, p0) :: prods) n0 n p0 eq_refl
                                    ((l1'
                                      ++
                                      [exist (fun pa : pat => In (n, pa) prods) p
                                             proof'']) ++ l2') =
                  (get_rhs_prods_aux prods ((n0, p0) :: prods) n0 n p0 eq_refl
                                     (l1' ++
                                          [exist (fun pa : pat => In (n, pa) prods) p
                                                 proof'']))
                    ++
                  (get_rhs_prods_aux prods ((n0, p0) :: prods) n0 n p0 eq_refl l2'))
             as Hget_rhs_prods_aux.
           {apply get_rhs_prods_aux_dist.
           }
           (* TODO: same problem here *)
           unfold production.
           rewrite Hget_rhs_prods_aux.
           clear Hget_rhs_prods_aux.
           assert(get_rhs_prods_aux prods ((n0, p0) :: prods) n0 n
                                    p0 eq_refl
                                    (l1' ++
                                         [exist (fun pa : pat => In (n, pa) prods) p
                                                proof'']) =
                  (get_rhs_prods_aux prods ((n0, p0) :: prods) n0 n
                                    p0 eq_refl l1')
                  ++
                  (get_rhs_prods_aux prods ((n0, p0) :: prods) n0 n
                                     p0 eq_refl
                                     [exist (fun pa : pat => In (n, pa) prods) p
                                            proof'']))
           as Hget_rhs_prods_aux.
           {apply get_rhs_prods_aux_dist.
           }
           rewrite Hget_rhs_prods_aux.
           clear Hget_rhs_prods_aux.
           remember (get_rhs_prods_aux prods ((n0, p0) :: prods) n0 n
                                       p0 eq_refl l2') as l2'' eqn:Heql2'.
           remember (get_rhs_prods_aux prods ((n0, p0) :: prods) n0 n
                                       p0 eq_refl l1') as l1'' eqn:Heql1'.
           simpl.
           assert(eq_ind_r
                    (fun prods0 : productions =>
                       In (n, p) prods0)
                    (in_cons_trans production 
                                   (n0, p0) (n, p) prods proof'') eq_refl =
                  (in_cons_trans production 
                                 (n0, p0) (n, p) prods proof''))
             as Hin_cons.
           {reflexivity.
           }
           unfold productions.
           unfold production.
           unfold productions in Hin_cons.
           unfold production in Hin_cons.
           rewrite Hin_cons.
           clear Hin_cons.
           remember (exist
                       (fun pat0 : pat =>
                          (n0, p0) = (n, pat0) \/ In (n, pat0) prods)
                       p
                       (in_cons_trans (nonterm * pat) 
                                      (n0, p0) (n, p) prods proof''))
             as in_proof eqn : Heqin_cons.
           exists l1''.
           exists l2''.
           exists (in_cons_trans (nonterm * pat)
                            (n0, p0) (n, p) prods proof'').
           rewrite <- Heqin_cons.
           rewrite <- app_assoc.
           reflexivity.
  Qed.

  Lemma get_rhs_split : forall (g : grammar) (p : pat) (n : nonterm),
                          prod_in_g (n, p) g ->
                          exists (proof : prod_in_g (n, p) g)
                            (g' g'' : list {p : pat | prod_in_g (n, p) g}),
                            get_rhs g n =  g'
                                           ++ ((exist (fun pa =>
                                                         prod_in_g (n, pa) g)
                                                      p
                                                      proof) :: nil)
                                           ++ g''.
  Proof.
    intros g p n ev.
    induction g.
    + (* g = nil *)
      inversion ev as [prod g Hin H0 H1].
      inversion Hin.
    + (* g = a :: g' *)
      unfold get_rhs.
      assert(exists (l1 l2 : list {pa : pat | In (n, pa) (a :: g)})
               (proof' : In (n, p) (a :: g)),
                get_rhs_prods (a :: g) n = l1 ++ ((exist (fun pa => In (n, pa) (a :: g))
                                                        p
                                                        proof') :: nil) ++ l2)
        as Hget_rhs_prods.
      {apply get_rhs_prods_split.
       inversion ev as [prod g0 Hin H0 H1].
       exact Hin.
      }
      inversion Hget_rhs_prods as [l1 Hget_rhs_prods'].
      clear Hget_rhs_prods.
      inversion Hget_rhs_prods' as [l2 Hget_rhs_prods''].
      clear Hget_rhs_prods'.
      inversion Hget_rhs_prods'' as [proof' Hget_rhs_prods'''].
      clear Hget_rhs_prods''.
      rewrite Hget_rhs_prods'''.
      clear Hget_rhs_prods'''.
      rewrite app_assoc.
      remember (exist (fun pa : pat => In (n, pa) (a :: g)) p proof') as elem.
      assert(get_rhs_aux (a :: g) n ((l1 ++ [elem]) ++ l2) =
             (get_rhs_aux (a :: g) n (l1 ++ [elem])) ++ get_rhs_aux (a :: g) n l2)
      as Hget_rhs_aux.
      {apply get_rhs_aux_split.
      }
      rewrite Hget_rhs_aux.
      clear Hget_rhs_aux.
      assert(get_rhs_aux (a :: g) n (l1 ++ [elem]) =
             (get_rhs_aux (a :: g) n l1) ++ get_rhs_aux (a :: g) n [elem])
        as Hget_rhs_aux.
      {apply get_rhs_aux_split.
      }
      rewrite Hget_rhs_aux.
      clear Hget_rhs_aux.
      destruct elem as [p' Hin].
      inversion Heqelem as [Hp].
      clear Heqelem.
      revert Hin.
      rewrite Hp.
      intro Hin.
      simpl.
      remember (get_rhs_aux (a :: g) n l1) as l1'.
      remember (get_rhs_aux (a :: g) n l2) as l2'.
      exists (prod_in_g_ev (n, p) (a :: g) Hin).
      exists l1'.
      exists l2'.
      remember (exist (fun p0 : pat => prod_in_g (n, p0) (a :: g)) p
                      (prod_in_g_ev (n, p) (a :: g) Hin)) as elem.
      rewrite <- app_assoc.
      reflexivity.
  Qed.

  (* to help in cases where we need to reason over the whole set of
     productions of a given n *)
  Lemma prod_in_g_get_rhs :
    forall (g : grammar) (p : pat) (n : nonterm),
      prod_in_g (n, p) g ->
      exists (proof : prod_in_g (n, p) g),
        In (exist _ p proof) (get_rhs g n).
  Proof.
    intros g p n Hprod_in.
    assert(exists (proof : prod_in_g (n, p) g)
             (g' g'' : list {p : pat | prod_in_g (n, p) g}),
              get_rhs g n =  g'
                               ++ ((exist (fun pa =>
                                             prod_in_g (n, pa) g)
                                          p
                                          proof) :: nil)
                               ++ g'')
      as Hget_rhs_split.
    {apply get_rhs_split.
     exact Hprod_in.      
    }
    inversion Hget_rhs_split as [Hproof_prod_in Hget_rhs_split'].
    clear Hget_rhs_split.
    inversion Hget_rhs_split' as [g' Hget_rhs_split''].
    clear Hget_rhs_split'.
    inversion Hget_rhs_split'' as [g'' Hget_rhs_split'''].
    clear Hget_rhs_split''.
    rewrite Hget_rhs_split'''.
    clear Hget_rhs_split'''.
    exists Hproof_prod_in.
    rewrite in_app_iff.
    right.
    simpl.
    left.
    reflexivity.
  Qed.

  (* to get rid of membership evidence *)
  Definition get_rhs_no_ev (g : grammar) (n : nonterm) : list pat :=
    (map (fun p_ev =>
            match p_ev with
            | (exist _ p _) => p
            end)
         (get_rhs g n)).

  Lemma get_rhs_no_ev_sound :
    forall (g : grammar) (p : pat) (n : nonterm),
      (exists (proof : prod_in_g (n, p) g),
          In (exist _ p proof) (get_rhs g n)) <-> In p (get_rhs_no_ev g n).
  Proof.
    intros g p n.
    split.
    - (* In (exist _ p proof) (get_rhs g n)) -> In p (get_rhs_no_ev g n) *)
      intro Hin_ev.
      (* compute get_rhs_no_ev, considering hypothesis Hin_ev *)
      inversion Hin_ev as [proof Hin_ev'].
      clear Hin_ev.
      unfold get_rhs_no_ev.
      assert(exists l1 l2 : list {p : pat | prod_in_g (n, p) g},
                (get_rhs g n) = l1
                                  ++
                                  (exist (fun p : pat => prod_in_g (n, p) g) p
                                         proof)
                                  :: l2)
        as Hget_rhs_split.
      {apply in_split.
       exact Hin_ev'.
      }
      inversion Hget_rhs_split as [l1 Hget_rhs_split'].
      clear Hget_rhs_split.
      inversion Hget_rhs_split' as [l2 Hget_rhs_split''].
      clear Hget_rhs_split'.
      rewrite Hget_rhs_split''.
      clear Hget_rhs_split''.
      
      rewrite map_app.
      simpl.

      rewrite in_app_iff.
      right.
      simpl.
      left.
      reflexivity.
    - (* In p (get_rhs_no_ev g n) ->
         In (exist (fun p0 : pat => prod_in_g (n, p0) g) p proof) 
            (get_rhs g n) *)
      intro Hin_no_ev.
      unfold get_rhs_no_ev in Hin_no_ev.
      rewrite in_map_iff in Hin_no_ev.
      inversion Hin_no_ev as [x Hin_no_ev'].
      clear Hin_no_ev.
      inversion Hin_no_ev' as [Heq_x Hin_x].
      clear Hin_no_ev'.
      destruct x.
      revert Hin_x.
      revert p0.
      rewrite Heq_x.
      intros Hprod_in_p Hin_p.
      exists Hprod_in_p.
      exact Hin_p.
  Qed.

  (* lemma built on the previous, to simplify the extraction of patterns
     of a given nonterm to just one lemma *)
  Lemma prod_in_g_get_rhs_no_ev :
    forall (g : grammar) (p : pat) (n : nonterm),
      prod_in_g (n, p) g ->
      In p (get_rhs_no_ev g n).
  Proof.
    intros g p n Hprod_in.
    apply prod_in_g_get_rhs in Hprod_in.
    rewrite get_rhs_no_ev_sound in Hprod_in.
    exact Hprod_in.
  Qed.

    Section GrammarIndPrin.
    
    Definition lt_grammar (g2 g1 : grammar) : Prop := 
      (grammar_length g2) < (grammar_length g1).

    Lemma wf_lt_grammar_transparent : well_founded lt_grammar.
    Proof.
      apply well_founded_ltof.
    Defined.

    (* Inductive principle for reasoning over <. *)

    Variable P : grammar -> Prop.
    
    Hypothesis base_case : forall (g : grammar),
        grammar_length g = 0 -> P g.

    Hypothesis ind_case : forall (g1 : grammar), 
        (forall (g2 : grammar), lt_grammar g2 g1 -> P g2) -> P g1.
    
    Definition grammar_ind_princ (g : grammar) : P g.
      refine 
        (Fix 
           wf_lt_grammar_transparent
           (* dependent range type of the function that we are building *)
           (fun g : grammar  => P g) 
           (* The function body *)
           (fun (g1 : grammar)
              (lt_ind_princ' : forall (g2 : grammar), lt_grammar g2 g1 -> P g2) =>
              match grammar_length g1 as len_g1
                    return grammar_length g1 = len_g1 -> P g1 with
              | 0   => 
                fun eqp : grammar_length g1 = 0 => base_case g1 eqp
              | S n => 
                fun eqp : grammar_length g1 = S n => 
                  ind_case g1 lt_ind_princ'
              end eq_refl) g).
    Defined.

  End GrammarIndPrin.

      
  (* Section GrammarIndPrin. *)
    
  (*   Definition lt_grammar (g2 g1 : grammar) : Prop :=  *)
  (*     (grammar_length g2) < (grammar_length g1). *)

  (*   Lemma lt_grammar_acc_transparent : forall (g : grammar), Acc lt_grammar g. *)
  (*   Proof. *)
  (*     intro. *)
  (*     unfold lt_grammar. *)
  (*     unfold grammar_length. *)
  (*     constructor. *)
  (*     induction (length g). *)
  (*     - intros. *)
  (*       inversion H. *)
  (*     - intros. *)
  (*       inversion H. *)
  (*       + constructor. *)
  (*         intros. *)
  (*         rewrite H1 in H0. *)
  (*         apply (IHn y0 H0). *)
  (*       + apply (IHn y H1). *)
  (*   Defined. *)

  (*   Lemma wf_lt_grammar_transparent : well_founded lt_grammar. *)
  (*   Proof. *)
  (*     constructor. *)
  (*     intros. *)
  (*     apply lt_grammar_acc_transparent. *)
  (*   Defined. *)

  (*   (* Inductive principle for reasoning over <. *) *)

  (*   Variable P : grammar -> Prop. *)
    
  (*   Hypothesis base_case : forall (g : grammar), *)
  (*       g = nil -> P g. *)
  (*   Hypothesis ind_case : forall (g1 : grammar),  *)
  (*       (forall (g2 : grammar), lt_grammar g2 g1 -> P g2) -> P g1. *)
    
  (*   Definition grammar_ind_princ (g : grammar) : P g. *)
  (*     refine  *)
  (*       (Fix  *)
  (*          wf_lt_grammar_transparent *)
  (*          (* dependent range type of the function that we are building *) *)
  (*          (fun g : grammar  => P g)  *)
  (*          (* The function body *) *)
  (*          (fun (g1 : grammar) *)
  (*             (lt_ind_princ' : forall (g2 : grammar), *)
  (*                 lt_grammar g2 g1 -> P g2) => *)
  (*             match g1 as proj  *)
  (*                   return g1 = proj -> P g1 with *)
  (*             | nil =>  *)
  (*               fun eqp : g1 = nil => (base_case g1 eqp) *)
  (*             | prod :: tail =>  *)
  (*               fun eqp : g1 = prod :: tail =>  *)
  (*                 (ind_case g1 lt_ind_princ') *)
  (*             end eq_refl) g). *)
  (*   Defined. *)

  (*   End GrammarIndPrin. *)
  
End GrammarLists.
