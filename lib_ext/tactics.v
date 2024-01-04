(* general purpose tactics whose definition do not depend on other
   modules *)

Require Import 
        Coq.Strings.String.

Declare Scope ltac_scope.

(* introduces evidence Ev necessary to prove the goal, and solves 
       using eauto *)
Tactic Notation "solve_with" constr(Ev) :=
  generalize Ev;
  intro;
  eauto.

(* tactic taken from Certified Programming with Dependent Types,
     ch. 14 *)
(* checks that a given proposition is not among the hypotheses *)
Ltac not_hyp P :=
  match goal with
  | [_ : P |- _ ] => fail 1
  | _             => idtac
  end.

(* applies specialize over every implication or universal quantification
   that appears as hypotheses; continues inferring using firstorder 
   tactic *)
Ltac app_specialize :=
  repeat match goal with
         | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] =>
           specialize (H1 H2 ); firstorder
         | [ H1 : forall (_ : ?P), _, H2 : ?P |- _ ] =>
           specialize (H1 H2 ); firstorder
         end.

(* simple tactic that applies destruct on some hypothesis, useful
   for simple contexts with few hypotheses over which we want to
   apply destruct *)
Ltac app_destruct type :=
  match goal with
  | [ t : type |- _ ] =>
      destruct t
  end.

Ltac intro_exist type :=
  match goal with
  | [ t : type |- _ ] =>
      exists t
  end.

(* to take out of the way some side of an equation *)
Ltac get_lhs :=
  match goal with
  | [|- context[?lhs = ?rhs]] =>
      let lhs_term := fresh "lhs_term" in
      let Heq_lhs_term := fresh "Heq_lhs_term" in
      remember lhs as lhs_term eqn:Heq_lhs_term
  end.
Ltac get_rhs :=
  match goal with
  | [|- context[?lhs = ?rhs]] =>
      let rhs_term := fresh "rhs_term" in
      let Heq_rhs_term := fresh "Heq_rhs_term" in
      remember rhs as rhs_term eqn:Heq_rhs_term
  end.

(* tactics for deciding equality among terms *)

(* to implement an algorithm to decide about equality of literals,
   sometimes it is needed to introduce hypotheses about equality
   of some parameters of type constructors; we use this tactic to
   that end *)
Ltac intro_eq_hyp :=
  match goal with
  | [ N1 : nat, N2 : nat |- _ ]          =>
      not_hyp (N1 = N2);
      not_hyp (N2 = N1);
      not_hyp (N1 <> N2);
      not_hyp (N2 <> N1);
      destruct (PeanoNat.Nat.eq_dec N1 N2)
  | [ S1 : string, S2 : string |- _ ]          =>
      not_hyp (S1 = S2);
      not_hyp (S2 = S1);
      not_hyp (S1 <> S2);
      not_hyp (S2 <> S1);
      destruct (string_dec S1 S2)
  | [ IH : forall e2 : ?T, {?E1 = e2} + {?E1 <> e2} |- _] =>
      match goal with
      (* do not add eq hypotheses for some term for which there
v           are already some eq hypotheses*)
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
                   intro fresh;
                   inversion fresh;
                   contradiction])
  end.
