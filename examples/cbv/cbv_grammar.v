Require Import 
        Coq.Strings.String
        Coq.Strings.Ascii
        Lists.List
        Lia.

Require Import
        patterns_terms
        patterns_terms_dec
        reduction
        lib_ext.ListExt
        lib_ext.tactics.

Open Scope string_scope.

(* call-by-value lambda-calculus *)

(* symbols of the model *)
Module CBVBase <: Symbols.
  Inductive cnlit : Type :=
  (* to represent lambda variables *)
  | str : string -> cnlit
  (* to tag lambda abstractions *)
  | lamb : cnlit .
  
  Definition lit := cnlit.

  Lemma lit_eq_dec (l1 l2 : lit) : {l1 = l2} + {l1 <> l2}.
    destruct l1, l2;
    solve_eq.
  Defined.

  (* names in name_pat *)
  Definition var := string.
  
  Definition var_eq_dec := fun x y => string_dec x y.
 
  Inductive cnnonterm : Type :=
  | e : cnnonterm
  | x : cnnonterm
  | v : cnnonterm
  | E : cnnonterm.

  Definition nonterm := cnnonterm.

  Definition nonterm_eq_dec (n1 n2 : cnnonterm) : {n1 = n2} + {n1 <> n2}.
    destruct n1, n2;
      solve_eq.
  Defined.

End CBVBase.

(* we instantiate our language of patterns and terms, with the previous symbols *)
Export CBVBase.
Module CallByValueTerms := PatTermsFunc(CBVBase).
Export CallByValueTerms.

Module CallByValueTermsDec := PatTermsDec(CallByValueTerms).
Export CallByValueTermsDec.

(* the present implementation has a "stack" design; 
   this is to avoid the existence of different instances of objects like grammars;
   we need to import each layer of the implementation, down to GrammarLists *)
Module Reduction := Reduction CallByValueTerms.
Export Reduction.
Export MatchingSpecOrig.
Export MatchSpecLemmas.
Export MatchImplLemmas.
Export MatchingSpec.
Export Matching.
Export MatchTads.
Export WfRel.
Export GrammarLists.

(* grammar of the model  *)
Definition cbv_grammar :=
  new_grammar ((* e *)
      (e, (| (nt e) (nt e) |) )
        :: (e, nt x)
        :: (e, nt v)
        ::
        
        (* v *)
        (v, (| (lp lamb) (| (nt x) (nt e) |) |)) ::
        
        (* x *)
        (x, lp (str "x")) ::
        (x, lp (str "y")) ::
        (x, lp (str "z")) ::
        
        (* E *)
        (E, [ ]) ::
        (E, (| (nt E) (nt e) |)) ::
        (E, (| (nt v) (nt E) |)) :: nil).
