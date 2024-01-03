Require Import
  (* dependent induction *)
  Program.Equality
  (* to solve some inequalities between size of terms *)
  Lia
  (* to build-up our theory of decidability of predicates over pats and terms *)
  stdpp.base stdpp.finite
  (* results about le, mod, div *)
  Nat
  Coq.Strings.String
  Coq.Logic.FunctionalExtensionality.

Require Import
  patterns_terms
  lib_ext.PeanoNatExt
  lib_ext.tactics.

(* tactics for reason about pats and terms, and some results about
   decidability of predicates over pats and terms *)

Module PatTermsDec (pt : PatTermsSymb).
  Import pt.
  
  (* hints db *)
  Create HintDb terms_pats_dec_db.
  #[global] Hint Constructors term : terms_pats_dec_db.
  #[global] Hint Constructors pat : terms_pats_dec_db.
  Ltac auto_tp_db := auto with terms_pats_db.
  Ltac auto_tp_dec_db := auto with terms_pats_dec_db.

  (* ********************************************************************* *)
  (* some tactics for reasoning about terms and patterns *)
  (* ********************************************************************* *)
  
  (* to implement an algorithm to decide about equality of literals,
       sometimes it is needed to introduce hypotheses about equality
       of some parameters of type constructors; we use this tactic to
       that end *)
  Ltac intro_eq_hyp :=
    match goal with
    | [ S1 : string, S2 : string |- _ ] =>
        not_hyp (S1 = S2);
        not_hyp (S2 = S1);
        not_hyp (S1 <> S2);
        not_hyp (S2 <> S1);
        destruct (string_dec S1 S2)
    | [ N1 : nat, N2 : nat |- _ ]          =>
        not_hyp (N1 = N2);
        not_hyp (N2 = N1);
        not_hyp (N1 <> N2);
        not_hyp (N2 <> N1);
        destruct (PeanoNat.Nat.eq_dec N1 N2)
    | [ L1 : lit, L2 : lit |- _ ]      =>
        not_hyp (L1 = L2);
        not_hyp (L2 = L1);
        not_hyp (L1 <> L2);
        not_hyp (L2 <> L1);
        destruct (lit_eq_dec L1 L2)
    | [ V1 : var, V2 : var |- _ ]      =>
        not_hyp (V1 = V2);
        not_hyp (V2 = V1);
        not_hyp (V1 <> V2);
        not_hyp (V2 <> V1);
        destruct (var_eq_dec V1 V2)
    | [ N1 : nonterm, N2 : nonterm |- _ ]      =>
        not_hyp (N1 = N2);
        not_hyp (N2 = N1);
        not_hyp (N1 <> N2);
        not_hyp (N2 <> N1);
        destruct (nonterm_eq_dec N1 N2)             
    | [ IH : forall e2 : ?T, {?E1 = e2} + {?E1 <> e2} |- _] =>
        match goal with
        (* do not add eq hypotheses for some term for which there
           are already some eq hypotheses*)
        | [ _ : E1 = ?E3 |- _ ] =>
            fail 1
        | [ _ : E1 <> ?E3 |- _ ] =>
                     fail 1
        | [ _ : ?E3 = E1 |- _ ] =>
            fail 1
        | [ _ : ?E3 <> E1 |- _ ] =>
            fail 1
        | [ E2 : T |- _] =>
            match goal with
            (* do not add eq hypotheses about subterms of the same
               construction *)
            | [ |- context [?const E1 E2]] =>
                fail 1
            | [ |- context [?const E2 E1]] =>
                fail 1
            | [ _ : ?E3 = E2 |- _ ] =>
                fail 1
            | [ _ : ?E3 <> E2 |- _ ] =>
                fail 
            | [ _ : E2 = ?E3 |- _ ] =>
                fail 1
            | [ _ : E2 <> ?E3 |- _ ] =>
                fail 1
            | _ =>
                let Heq := fresh "Heq" in
                assert (Heq : {E1 = E2} + {E1 <> E2});
                [apply IH
                |];
                destruct Heq
            end
        end
    end.

  (* solves equality comparison for simple inductive types:
     - built, at most, over one parameter of type string or nat
     - can handle recursive types in their most simple form

     if needed, the user must introduce inductive hypotheses, or
     destruct terms as required
  *)
  Ltac solve_eq :=
    match goal with
    | [|- {?T1 = ?T2} + {?T1 <> ?T2}] =>
        (* solve cases that are obviously true or false: *)
        try ((* patterns that are built with different constructors *)
            (right;
             intro H;
             solve [inversion H]) +
              (* patterns that are exactly the same *)
              (left;
               solve [reflexivity]));
        (* what remain are constructors that receive at least one
             parameter; we introduce equality hypotheses about their
             parameters *)
        try (intro_eq_hyp;
             (* every subgoal is trivially true or false *)
             solve [subst;
                    tauto |
                     right;
                     let fresh_name := fresh "H" in
                     intro fresh_name;
                     inversion fresh_name;
                     contradiction])
    end.

  (* solves equality comparison for an inductive type that is defined
     in a mutually recursive fashion, with another type
     PARAMS
     type1, type2 : types involved in the definition; the goal
                  predicates about an equality comparison between terms
                  of type type1
     type1_mut : a mutually recursive inductive principle to reason
                 about type1 terms *)
  Ltac solve_eq_2_mut_rec type1 type2 type1_mut :=
    match goal with
    | [|- {?T1 = ?T2} + {?T1 <> ?T2}] =>
        (* TODO: how can we generate the induction principle here? *)
        (* Scheme type1_mut := Induction for type1 Sort Type *)
        (*   with type2_mut := Induction for type2 Sort Type; *)

    apply (type1_mut (fun v1 : type1 => forall v2 : type1, {v1 = v2} + {v1 <> v2})
                     (fun v3 : type2 => forall v4 : type2, {v3 = v4} + {v3 <> v4}));
        (* destruct the other pat/list_pat *)
      try (((intros;
            app_destruct type1) +
             (intros;
              app_destruct type2)
           );
           (* introduce eq. hypotheses (if needed) *)
           (intro_eq_hyp +
            (intros;
             intro_eq_hyp;
             intro_eq_hyp) +
              idtac);
           (* eqs. should be clearly true or false by now *)
            solve[left; (* patterns =, for constructors with signature * -> * *)
                  subst;
                  reflexivity
                 | left; (* patterns =, for constructors without parameters *)
                   auto
                 | right; (* patterns <> *)
                   let H := fresh "H" in
                   intro H;
                   solve [inversion H;
                          contradiction
                         | inversion H]])
    end.
  
  (* solves equality comparison for an inductive type that is defined
     in a mutually recursive fashion, with respect to 3 other types
     PARAMS
     type1, type2, type3, type4 : types involved in the definition; the goal
                  predicates about an equality comparison between terms
                  of type type1
     type1_mut : a mutually recursive inductive principle to reason
                 about type1 terms *)
  Ltac solve_eq_4_mut_rec type1 type2 type3 type4 type1_mut :=
    match goal with
    | [|- {?T1 = ?T2} + {?T1 <> ?T2}] =>
        (* TODO: how can we generate the induction principle here? *)
        (* Scheme type1_mut := Induction for type1 Sort Type *)
        (*   with type2_mut := Induction for type2 Sort Type; *)

    apply (type1_mut (fun v1 : type1 => forall v2 : type1, {v1 = v2} + {v1 <> v2})
                     (fun v3 : type2 => forall v4 : type2, {v3 = v4} + {v3 <> v4})
                     (fun v5 : type3 => forall v6 : type3, {v5 = v6} + {v5 <> v6})
                     (fun v7 : type4 => forall v8 : type4, {v7 = v8} + {v7 <> v8}));
        (* destruct the other term *)
      try (((intros;
            app_destruct type1) +
             (intros;
              app_destruct type2) +
              (intros;
              app_destruct type3) +
              (intros;
              app_destruct type4)
           );
           (* introduce eq. hypotheses (if needed) *)
           (intro_eq_hyp +
            (intros;
             intro_eq_hyp;
             intro_eq_hyp) +
              idtac);
           (* eqs. should be clearly true or false by now *)
            solve[left; (* patterns =, for constructors with signature * -> * *)
                  subst;
                  reflexivity
                 | left; (* patterns =, for constructors without parameters *)
                   auto
                 | right; (* patterns <> *)
                   let H2 := fresh "H" in
                   intro H2;
                   solve [inversion H2;
                          contradiction
                         | inversion H2]])
    end.
  
  (* some results about decidability of predicates about pats and terms *)
  Section Decidability.
    (* decidability as {p} + {not p} using stdpp typeclass *)
    (* we use EqDecision instead of just Decision to take advantage of
       the already defined instances of the first *)
    #[export] Instance pat_eq_dec : EqDecision pat.
    Proof.
      unfold EqDecision.
      intros x y.
      unfold Decision.
      solve_eq_2_mut_rec pat list_pat pat_mut_rec.
    Qed.

    Hint Resolve pat_eq_dec : terms_pats_dec_db.
    
    (* create induction principles for our mutually recursive types term,
       list and context *)

    #[export] Instance term_eq_dec : EqDecision term.
    Proof.
      unfold EqDecision.
      intros x y.
      unfold Decision.
      
      solve_eq_4_mut_rec term list_term contxt list_contxt term_mut_rec.
    Qed.

    Hint Resolve term_eq_dec : terms_pats_dec_db.

    #[export] Instance contxt_eq_dec : EqDecision contxt.
    Proof.
      unfold EqDecision.
      intros x y.
      unfold Decision.
      solve_eq_4_mut_rec term list_term contxt list_contxt contxt_mut_rec.
    Qed.

    Hint Resolve contxt_eq_dec : terms_pats_dec_db.

    #[export] Instance list_contxt_eq_dec : EqDecision list_contxt.
    Proof.
      unfold EqDecision.
      intros x y.
      unfold Decision.
      solve_eq_4_mut_rec term list_term contxt list_contxt list_contxt_mut_rec.
    Qed.

    Hint Resolve contxt_eq_dec : terms_pats_dec_db.

    #[export] Instance list_term_eq_dec : EqDecision list_term.
    Proof.
      unfold EqDecision.
      intros x y.
      unfold Decision.
      
      solve_eq_4_mut_rec term list_term contxt list_contxt list_term_mut_rec.    
    Qed.

    Hint Resolve list_term_eq_dec : terms_pats_dec_db.
    
  End Decidability.                                        

End PatTermsDec.
