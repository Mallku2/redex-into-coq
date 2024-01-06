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
        lib_ext.tactics
        cbv_grammar
        cbv_meta_functions.

Open Scope string_scope.

(* call-by-value lambda-calculus *)

(* we instantiate our language of patterns and terms, with the previous symbols *)
Import cbv_grammar.
Import CBVBase.
Import CallByValueTerms.
Import CallByValueTermsDec.

Import cbv_meta_functions.

(* the present implementation has a "stack" design; 
   this is to avoid the existence of different instances of objects like grammars;
   we need to import each layer of the implementation, down to GrammarLists *)
Import Reduction.
Import MatchingSpecOrig.
Import MatchSpecLemmas.
Import MatchImplLemmas.
Import MatchingSpec.
Import Matching.
Import MatchTads.
Import WfRel.
Import GrammarLists.

(* semantics relation: we combine the primitive computations and the
   standard reduction into one relation *)
Definition cbv_rel := 
  ((* beta-contraction *)
    (((nt E) __ "E") [ (| ((| (lp lamb) (| ((nt x)__"x") ((nt e)__"e") |) |))
                           ((nt v)__"v") |) ],
      inhole_temp 
        (var_temp "E1") 
        (app_temp substitute (var_temp "e")) (var_temp "x") (var_temp "v"))))
    ) :: nil.
