Require Export
        patterns_terms
        verification.match_spec_lemmas.


(**
Specification of matching --- Figure 9.
*)

Module MatchingSpecOrig (pt : PatTermsSymb).
  Include pt.
  Import pt.
  Module MatchSpecLemmas := MatchSpecLemmas pt.
  Import MatchSpecLemmas.
  Import MatchImplLemmas.
  Import MatchingSpec.
  Import Matching.
  Import MatchTads.
  Import WfRel.
  Import GrammarLists.

  Reserved Notation "G ⊢ t : p | b" (at level 0, t at next level, p at next level).
  Reserved Notation "G ⊢ t1 ⩦ C [ t2 ] : p | b" (at level 0, C at next level, t1 at next level, t2 at next level).

  Inductive match_spec (G : grammar) : term -> pat -> bindings -> Prop :=
  (* rule for literals       *)
  | lit_match_spec: forall (a : lit),
      G ⊢ a : a | ∅

  (* rule for holes          *)
  | hole_match_spec:
      G ⊢ hole__t : hole__p | ∅

  (* rule for named patterns *)
  | name_match_spec: forall t x p bp b,
      G ⊢ t : p | bp             ->
      ((x, t) :: ∅) ⊔ bp = Some b ->
      G ⊢ t : name x p | b

  (* rule for non-terminals  *)
  | nt_match_spec: forall n p t b
      (proof : prod_in_g (n, p) G),
      G ⊢ t : p | b  ->
      G ⊢ t : nt n | ∅

  (* rules for cons: cons case *)
  | cons_cons_match_spec: forall t1 p1 b1 t2 p2 b2 b,
      G ⊢ t1 : p1 | b1                            ->
      G ⊢ (list_term_c t2) : (list_pat_c p2) | b2 ->
      b1 ⊔ b2 = Some b                             ->
      G ⊢ (ct t1 t2) : cp p1 p2 | b

  (* rules for cons: left case *)
  | cons_left_match_spec: forall p1 b1 t2 p2 b2 b (C : contxt),
      G ⊢ C : p1 | b1                             ->
      G ⊢ (list_term_c t2) : (list_pat_c p2) | b2 ->
      b1 ⊔ b2 = Some b                             ->
      G ⊢ (hd_c C t2) : cp p1 p2 | b

  (* rules for cons: right case *)
  | cons_right_match_spec: forall t1 p1 b1 p2 b2 b (C : list_contxt),
      G ⊢ t1 : p1 | b1           ->
      G ⊢ C : list_pat_c p2 | b2 ->
      b1 ⊔ b2 = Some b            ->
      G ⊢ (tail_c t1 C) : cp p1 p2 | b
  (* rule for nil *)
  | nil_nil_match_spec
    : G ⊢ (list_term_c nil_term_c) : list_pat_c nil_pat_c | ∅ 

  (* rules for in-hole *)
  | in_hole_match_spec: forall t1 t2 C p1 p2 b1 b2 b,
      G ⊢ t1 ⩦ C[t2] : p1 | b1 ->
      G ⊢ t2 : p2 | b2         ->
      b1 ⊔ b2 = Some b          ->
      G ⊢ t1 : inhole p1 p2 | b
 
 (* definition of the decompose relation *)
  with
    decompose_spec (G : grammar) : term -> contxt -> term -> pat -> bindings -> Prop :=
  (* decomposing for holes *)
  | hole_decompose_spec: forall t,
      G ⊢ t ⩦ hole__t[t] : hole__p | ∅

  (* decomposing left contexts *)
  | cons_left_decompose_spec: forall t1 t2 p1 p2 t1' b1 b2 C b,
      G ⊢ t1 ⩦ C[t1'] : p1 | b1                   ->
      G ⊢ (list_term_c t2) : (list_pat_c p2) | b2 ->
      b1 ⊔ b2 = Some b                             ->
      G ⊢ ct t1 t2 ⩦ (hd_c C t2)[t1'] : cp p1 p2 | b

  | left_left_decompose_spec
    : forall (C : contxt) t2 p1 p2 sub_C b1 b2 C' b,
      G ⊢ C ⩦ C'[sub_C] : p1 | b1                 ->
      G ⊢ (list_term_c t2) : (list_pat_c p2) | b2 ->
      b1 ⊔ b2 = Some b                             ->
      G ⊢ hd_c C t2 ⩦ (hd_c C' t2)[sub_C] : cp p1 p2 | b

 | right_left_decompose_spec: forall t1 (C : list_contxt) p1 p2 t1' b1 b2 C' b,
     G ⊢ t1 ⩦ C'[t1'] : p1 | b1                                 ->
     G ⊢ (contxt_term (list_contxt_c C)) : (list_pat_c p2) | b2 ->
     b1 ⊔ b2 = Some b                                            ->
     G ⊢ tail_c t1 C ⩦ (hd_c C' (list_contxt_2_list_term C))[t1'] : cp p1 p2 | b

  (* decomposing right contexts *)
  | cons_right_decompose_spec: forall t1 t2 p1 p2 t2' b1 b2 C b,
      G ⊢ t1 : p1 | b1                                                     ->
      G ⊢ (list_term_c t2) ⩦ (list_contxt_c C)[t2'] : (list_pat_c p2) | b2 ->
      b1 ⊔ b2 = Some b                                                      ->
      G ⊢ ct t1 t2 ⩦ (tail_c t1 C)[t2'] : cp p1 p2 | b

  | left_right_decompose_spec: forall t2 p1 p2 t2' b1 b2 (C : contxt) (C' : list_contxt) b,
      G ⊢ C : p1 | b1                                       ->
      G ⊢ (list_term_c t2) ⩦ C'[t2'] : (list_pat_c p2) | b2 ->
      b1 ⊔ b2 = Some b                                       ->
      G ⊢ hd_c C t2 ⩦ (tail_c C C')[t2'] : cp p1 p2 | b

 | right_right_decompose_spec: forall t1 (C : list_contxt) p1 p2 sub_C b1 b2 C' b,
     G ⊢ t1 : p1 | b1                                         ->
     G ⊢ C ⩦ (list_contxt_c C')[sub_C] : (list_pat_c p2) | b2 ->
     b1 ⊔ b2 = Some b                                          ->
     G ⊢ tail_c t1 C ⩦ (tail_c t1 C')[sub_C] : cp p1 p2 | b

 | nt_decompose_spec: forall n p t1 C t2 b,
     prod_in_g (pair n p) G ->
     G ⊢ t1 ⩦ C[t2] : p | b ->
     G ⊢ t1 ⩦ C[t2] : nt n | ∅
                    
 | in_hole_decompose_spec: forall t C1 t1 p1 b1 C2 t2 p2 b2 b,
     G ⊢ t ⩦ C1[t1] : p1 | b1  ->
     G ⊢ t1 ⩦ C2[t2] : p2 | b2 ->
     b1 ⊔ b2 = Some b           -> 
     G ⊢ t ⩦ (context_com C1 C2)[t2] : inhole p1 p2 | b

 | name_pat_decompose_spec: forall t1 C t2 x p b1 b,
     G ⊢ t1 ⩦ C[t2] : p | b1                ->
     ((x, contxt_term C) :: ∅) ⊔ b1 = Some b -> 
     G ⊢ t1 ⩦ C[t2] : name x p | b
  where "G ⊢ t : p | b" := (match_spec G t p b)
  and "G ⊢ t1 ⩦ C [ t2 ] : p | b" := (decompose_spec G t1 C t2 p b).
  
End MatchingSpecOrig.
