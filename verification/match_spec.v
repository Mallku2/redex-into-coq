Require Export match_impl.


(**
Specification of matching --- Figure 9.
*)

Module MatchingSpec (pt : PatTermsSymb).
  Import pt.

  (* in order to avoid name clashes, we keep just a single instance of a grammar,
     in WfRel; a single instance of MatchTads, in Matching, etc *)
  Module Matching := Matching pt.
  Import Matching.
  Import MatchTads.
  Import WfRel.
  Import GrammarLists.

  (** decomp_term is Some just when it is used by decomp_spec.
      This is needed to avoid an error when defining the match
      type specification. *)

  Definition match_type :=
    term -> pat -> grammar -> bindings -> Prop.
  
  Reserved Notation "G ⊢ t : p , G' | b" (at level 0, t at next level, p at next level, G' at next level).
  Reserved Notation "G ⊢ t1 ⩦ C [ t2 ] : p , G' | b" (at level 0, C at next level, t1 at next level, t2 at next level, G' at next level).

  Inductive match_spec (G : grammar) : match_type :=
  (* rule for literals       *)
  | lit_match_spec
    : forall (a : lit) G', G ⊢ a : a, G' | ∅
  (* rule for holes          *)
  | hole_match_spec
    : forall G', G ⊢ hole__t : hole__p, G' | ∅
  (* rule for named patterns *)
  | name_match_spec
    : forall t x p bp b G',
      G ⊢ t : p, G' | bp         ->
      ((x, t) :: ∅) ⊔ bp = Some b ->
      G ⊢ t : name x p, G' | b
  (* rule for non-terminals  *)
  | nt_match_spec
    : forall n p t b G'
      (proof : prod_in_g (n, p) G'),
      G ⊢ t : p, remove_prod (n, p) G' proof | b  ->
      G ⊢ t : nt n, G' | ∅
  (* rules for cons: cons case *)
  (* we reset the second grammar, for future inspections of productions *)
  | cons_cons_match_spec
    : forall t1 p1 b1 t2 p2 b2 b G',
      G ⊢ t1 : p1, G | b1                            ->
      G ⊢ (list_term_c t2) : (list_pat_c p2), G | b2 ->
      b1 ⊔ b2 = Some b                                ->
      G ⊢ (ct t1 t2) : cp p1 p2, G' | b
  (* rules for cons: left case *)
  | cons_left_match_spec 
    : forall p1 b1 t2 p2 b2 b (C : contxt) G',
      G ⊢ C : p1, G | b1                             ->
      G ⊢ (list_term_c t2) : (list_pat_c p2), G | b2 ->
      b1 ⊔ b2 = Some b                                ->
      G ⊢ (hd_c C t2) : cp p1 p2, G' | b
  (* rules for cons: right case *)
  | cons_right_match_spec
    : forall t1 p1 b1 p2 b2 b (C : list_contxt) G',
      G ⊢ t1 : p1, G | b1           ->
      G ⊢ C : list_pat_c p2, G | b2 ->
      b1 ⊔ b2 = Some b               ->
      G ⊢ (tail_c t1 C) : cp p1 p2, G' | b
(* nil *)
  | nil_nil_match_spec
    : forall G',
      G ⊢ (list_term_c nil_term_c) : (list_pat_c nil_pat_c), G' | ∅ 
  (* rules for in-hole *)
  (* input consumption *)
  | in_hole_match_spec_inp_cons
    : forall t1 t2 C p1 p2 b1 b2 b G',
      G ⊢ t1 ⩦ C[t2] : p1, G' | b1  ->
      subterm_rel t2 t1              ->
      G ⊢ t2 : p2, G | b2           ->
      b1 ⊔ b2 = Some b               ->
      G ⊢ t1 : inhole p1 p2, G' | b
  (* no input consumption*)
  | in_hole_match_spec_noinp_cons
    : forall t p1 p2 b1 b2 b G',
      G ⊢ t ⩦ hole_contxt_c [t]  : p1, G' | b1 ->
      G ⊢ t : p2, G' | b2                      ->
      b1 ⊔ b2 = Some b                          ->
      G ⊢ t : inhole p1 p2, G' | b
  (* definition of the decompose relation *)
  with
    decompose_spec (G : grammar) : term -> contxt -> term -> pat -> grammar -> bindings -> Prop :=
  (* decomposing for holes *)
  | hole_decompose_spec
    : forall t G',
      G ⊢ t ⩦ hole__t[t] : hole__p, G' | ∅
  (* decomposing left contexts *)
  | cons_left_decompose_spec
    : forall t1 t2 p1 p2 t1' b1 b2 C b G',
      G ⊢ t1 ⩦ C[t1'] : p1, G | b1                   ->
      G ⊢ (list_term_c t2) : (list_pat_c p2), G | b2 ->
      b1 ⊔ b2 = Some b                                ->
      G ⊢ ct t1 t2 ⩦ (hd_c C t2)[t1'] : cp p1 p2, G' | b
  | left_left_decompose_spec
    : forall (C : contxt) t2 p1 p2 sub_C b1 b2 C' b G',
      G ⊢ C ⩦ C'[sub_C] : p1, G | b1                 ->
      G ⊢ (list_term_c t2) : (list_pat_c p2), G | b2 ->
      b1 ⊔ b2 = Some b                                ->
      G ⊢ hd_c C t2 ⩦ (hd_c C' t2)[sub_C] : cp p1 p2, G' | b
 | right_left_decompose_spec
   : forall t1 (C : list_contxt) p1 p2 t1' b1 b2 C' b G',
     G ⊢ t1 ⩦ C'[t1'] : p1, G | b1                                          ->
     (* recall that hd_contxt and tail_contxt point into a position from a list of 
        terms  *)
     G ⊢ (contxt_term (list_contxt_c C)) : (list_pat_c p2), G | b2          ->
     b1 ⊔ b2 = Some b                                                        ->
     G ⊢ tail_c t1 C ⩦ (hd_c C' (list_contxt_2_list_term C))[t1'] : cp p1 p2, G' | b
  (* decomposing right contexts *)
  | cons_right_decompose_spec
    : forall t1 t2 p1 p2 t2' b1 b2 C b G',
      G ⊢ t1 : p1, G | b1                                                      ->
      G ⊢ (list_term_c t2) ⩦ (list_contxt_c C)[t2'] : (list_pat_c p2), G | b2  ->
      b1 ⊔ b2 = Some b                                                          ->
      G ⊢ ct t1 t2 ⩦ (tail_c t1 C)[t2'] : cp p1 p2, G' | b 
  | left_right_decompose_spec
    : forall t2 p1 p2 t2' b1 b2 (C : contxt) C' b G',
      G ⊢ C : p1, G | b1                                                       ->
      G ⊢ (list_term_c t2) ⩦ (list_contxt_c C')[t2'] : (list_pat_c p2), G | b2 ->
      b1 ⊔ b2 = Some b                                                          ->
      G ⊢ hd_c C t2 ⩦ (tail_c C C')[t2'] : cp p1 p2, G' | b
 | right_right_decompose_spec
   : forall t1 (C : list_contxt) p1 p2 sub_C b1 b2 (C' : list_contxt) b G',
     G ⊢ t1 : p1, G | b1                                       ->
     G ⊢ C ⩦ C'[sub_C] : (list_pat_c p2), G | b2               ->
     b1 ⊔ b2 = Some b                                           ->
     G ⊢ tail_c t1 C ⩦ (tail_c t1 C')[sub_C] : cp p1 p2, G' | b

 | nt_decompose_spec
   : forall n p t1 C t2 b G' (proof : prod_in_g (pair n p) G'),
     G ⊢ t1 ⩦ C[t2] : p, (remove_prod (n, p) G' proof) | b ->
     G ⊢ t1 ⩦ C[t2] : nt n, G' | ∅
                    
 | in_hole_decompose_spec_inp_cons
   : forall t C1 t1 p1 b1 C2 t2 p2 b2 b G',
     G ⊢ t ⩦ C1[t1] : p1, G' | b1 ->
     subterm_rel t1 t              ->
     G ⊢ t1 ⩦ C2[t2] : p2, G | b2 ->
     b1 ⊔ b2 = Some b              -> 
     G ⊢ t ⩦ (context_com C1 C2)[t2] : inhole p1 p2, G' | b

| in_hole_decompose_spec_noinp_cons
   : forall t p1 b1 C2 t2 p2 b2 b G',
     G ⊢ t ⩦ hole__t[t] : p1, G' | b1 ->
     G ⊢ t ⩦ C2[t2] : p2, G' | b2   ->
     b1 ⊔ b2 = Some b                ->
     G ⊢ t ⩦ (context_com hole__t C2)[t2] : inhole p1 p2, G' | b                                                                                      
 | name_pat_decompose_spec
   : forall t1 C t2 x p b1 b G',
     G ⊢ t1 ⩦ C[t2] : p, G' | b1            ->
     ((x, contxt_term C) :: ∅) ⊔ b1 = Some b -> 
     G ⊢ t1 ⩦ C[t2] : name x p, G' | b
  where "G ⊢ t : p , G' | b" := (match_spec G t p G' b)
        and 
        "G ⊢ t1 ⩦ C [ t2 ] : p , G' | b" := (decompose_spec G t1 C t2 p G' b).
  
End MatchingSpec.
