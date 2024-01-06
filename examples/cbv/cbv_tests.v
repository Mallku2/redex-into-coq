Require Import
        cbn
        lib_ext.ListExt.

Require Import 
        Coq.Strings.String
        Coq.Strings.Ascii.

Import cbn.
Import CNBase.
Import CallNeedTerms.
Import Reduction.
Import MatchingSpecOrig.
Import MatchSpecLemmas.
Import MatchImplLemmas.
Import MatchingSpec.
Import Matching.
Import MatchTads.
Import WfRel.
Import GrammarLists.
Import PatTermsDec.


(* bindings *)
Example b_union_ex1 : b_union nil nil = Some nil.
Proof. reflexivity. Qed.

Example b_union_ex2 :
  b_union (("x", lit_term lamb) :: nil) nil =
  Some (("x", lit_term lamb) :: nil).
Proof. reflexivity. Qed.

Example b_union_ex3 : b_union (("x", lit_term lamb) :: nil)
                               (("x", lit_term lamb) :: nil) =
                      Some (("x", lit_term lamb) :: nil).
Proof.
  reflexivity.
Qed.

Example b_union_ex4 : b_union (("x", lit_term lamb) :: nil)
                               (("x", lit_term (str "lamb")) :: nil) =
                      None.
Proof.
  reflexivity.
Qed.

(* matching and decomposition *)
(* first equation *)
(* match and decomposition *)
Example test1 :
  M cbn_grammar [ ] hole = (hole [[ hole ]], nil) :: ([[]], nil) :: nil.
Proof.
  M_reduce.
  reflexivity.
Qed.

(* TODO: take advantage of the Coercion rules: avoid things like 
   lter (str "x") *)
(* second equation *)
(* just decomposition *)
Example test2 :
  M cbn_grammar [ ] (lter (str "x")) =
  (hole [[ lter (str "x") ]], nil) :: nil.
Proof.
  M_reduce.
  reflexivity. 
Qed.

Example test22 :
  M cbn_grammar [ ] ( (|| (lter (str "x")) (lter (str "x")) ||)) =
  (hole
     [[ (|| (lter (str "x")) (lter (str "x")) ||) ]],
   nil) :: nil.
Proof.
  M_reduce.
  reflexivity. 
Qed.

(* third equation *)
(* just match (and no binding required) *)
Example test3 :
  M cbn_grammar (lp (str "x")) (lter (str "x")) = ([[ ]], nil) :: nil.
Proof. 
  M_reduce.
  reflexivity.
Qed.

Example test32 :
  M cbn_grammar (lp (str "x")) (lter (str "y")) = nil.
Proof. 
  M_reduce.
  reflexivity.
Qed.

(* fourth equation *)
Example test4 :
  (M cbn_grammar
     ( (| ((lp (str "y")) __ "arg") ((lp (str "x")) __ "body") |) )
     
     ( (|| (lter (str "y")) (lter (str "x")) ||) )) =
  ([[ ]],
   (("arg", lter (str "y"))
      :: ("body", lter (str "x"))
      :: nil)) :: nil.
Proof.
  M_reduce.
  reflexivity.
Qed.

(* Example test42 : *)
(*   (M cbn_grammar *)
     
(*      ( (| ((nt E) [ (lp (str "x")) ]) (lp (str "x")) |) ) *)
     
(*      ( (|| (lter (str "x")) (lter (str "x")) ||) )) = *)
(*  ([[]], nil) :: nil. *)
(* Proof. *)
(*   M_reduce. *)
(*   reflexivity.  *)
(* Qed. *)

(* fifth equation *)
Example test5 :
  (M cbn_grammar
     ([] [ (lp (str "x")) __ "body" ])
     (lter (str "x"))) =
  ([[]], (("body", lter (str "x")) :: nil)) :: nil.
Proof.
  M_reduce.
  reflexivity. 
Qed.

(* call-by-need: the redex is the formal parameter*)
(* Example test52 : *)
(*   (M cbn_grammar (((| ((| (lp lamb) *)
(*                             ((| ((nt x) __ "x") *)
(*                                ((nt E) [ (nt x) __ "x"]) |) ) |)) *)
(*              (nt E) |)) [ lp (str "x") ]) *)
           
(*      ((|| ((|| (lter lamb) *)
(*                ((|| (lter (str "x")) *)
(*                      (lter (str "x")) ||)) ||)) *)
(*         (lter (str "x")) ||))) = *)
(*   ([[]], (("x", lter (str "x")) :: nil)) :: nil. *)
(* Proof. *)

(* call-by-need: the redex does not coincide with the formal parameter*)
(* Example test53 : *)
(*   (M cbn_grammar ((cp (cp (lp lamb) *)
(*                  (cp ((nt x) __ "x" ) *)
(*                      ((nt E) [ ((nt_pat x) __ "x" ) ]))) *)
(*              (nt_pat E)) *)
(*            [ (lp (str "x")) ]) *)
           
(*      (ct (ct (lter lamb) *)
(*              (ct (lter (str "x")) *)
(*                  (lter (str "y")))) *)
(*          (lter (str "x"))))  *)
(*   = *)
(*   nil. *)
(* Proof. reflexivity. Qed. *)


(* sixth equation *)
Example test6 :
  M cbn_grammar ((lp (str "x")) __ "body") (lter (str "x")) =
  ([[]], (("body", lter (str "x")) :: nil)) :: nil.
Proof.
  M_reduce.
  reflexivity.
Qed.

(* seventh equation *)
Example test7 :
  M cbn_grammar (nt x) (lter (str "x")) = ([[]], nil) :: nil.
Proof.
  M_reduce.
  simpl.
  M_reduce.
  reflexivity.
Qed.

(* semantics  *)
Example test_plus1 :
  apply_reduction cbn_grammar
              ((|| (lter plus1) (lter (n 1)) ||) )
              cbn_rel = 
  Some (lter n 2) :: nil.
Proof.
  reflexivity.
Qed.

Example test_plus1_compat1 :
  (apply_reduction cbn_grammar
              (ct (ct (lter lamb)
                      (ct (lter (str "x"))
                          (ct (lter plus1) (lter (str "x")))))
                  (lter (n 1)))
              cbn_rel) = 
  Some (ct (ct (lter lamb)
               (ct (lter str "x") (ct (lter plus1) (lter n 1)))) 
           (lter n 1)) :: nil.
Proof.
  reflexivity.
Qed.

Example test_plus1_compat2 :
  (apply_reduction cbn_grammar
               (ct (ct (lter lamb)
                       (ct (lter str "x") (ct (lter plus1) (lter n 1)))) 
                   (lter n 1))
               cbn_rel) =
  Some (ct (ct (lter lamb) (ct (lter str "x") (lter n 2))) (lter n 1))
       :: nil.
Proof.
  reflexivity.
Qed.

Example test_plus1_compat3 :
  (apply_reduction cbn_grammar
              (ct (ct (lter lamb) (ct (lter str "x") (lter n 2)))
                  (lter n 1))
              cbn_rel) = 
  Some (lter n 2) :: nil.
Proof.
  reflexivity.
Qed.
