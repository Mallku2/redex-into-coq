Require Import
        examples.cbv.cbv_grammar
        examples.cbv.cbv_meta_functions
        examples.cbv.cbv_sem
        lib_ext.ListExt.

Require Import 
        Coq.Strings.String
        Coq.Strings.Ascii.

Import cbv_grammar.
Import CBVBase.
Import CallByValueTerms.
Import cbv_meta_functions.
Import cbv_sem.
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
  M cbv_grammar [ ] hole = (hole [[ hole ]], nil) :: ([[]], nil) :: nil.
Proof.
  M_reduce.
  reflexivity.
Qed.

(* second equation *)
(* just decomposition *)
Example test2 :
  M cbv_grammar [ ] (lter (str "x")) =
  (hole [[ lter (str "x") ]], nil) :: nil.
Proof.
  M_reduce.
  reflexivity. 
Qed.

Example test22 :
  M cbv_grammar [ ] ( (|| (lter (str "x")) (lter (str "x")) ||)) =
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
  M cbv_grammar (lp (str "x")) (lter (str "x")) = ([[ ]], nil) :: nil.
Proof. 
  M_reduce.
  reflexivity.
Qed.

Example test32 :
  M cbv_grammar (lp (str "x")) (lter (str "y")) = nil.
Proof. 
  M_reduce.
  reflexivity.
Qed.

(* fourth equation *)
Example test4 :
  (M cbv_grammar
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

(* fifth equation *)
Example test5 :
  (M cbv_grammar
     ([] [ (lp (str "x")) __ "body" ])
     (lter (str "x"))) =
  ([[]], (("body", lter (str "x")) :: nil)) :: nil.
Proof.
  M_reduce.
  reflexivity. 
Qed.

(* sixth equation *)
Example test6 :
  M cbv_grammar ((lp (str "x")) __ "body") (lter (str "x")) =
  ([[]], (("body", lter (str "x")) :: nil)) :: nil.
Proof.
  M_reduce.
  reflexivity.
Qed.

(* seventh equation *)
Example test7 :
  M cbv_grammar (nt x) (lter (str "x")) = ([[]], nil) :: nil.
Proof.
  M_reduce.
  simpl.
  M_reduce.
  reflexivity.
Qed.
