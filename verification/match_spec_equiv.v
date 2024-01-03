Require Import match_spec_orig.
Require Import ssreflect.

Module Equiv(pt : PatTermsSymb).
  Module MSO := MatchingSpecOrig pt.
  Import MSO.
  Import MatchSpecLemmas.
  Import MatchImplLemmas.
  Import MatchingSpec.
  Import Matching.
  Import WfRel.
  Import GrammarLists.
  Import MatchTads.
  
  (* TODO: put this theory in grammar.v *)
  Axiom gleq : grammar -> grammar -> Prop.
  Axiom gleq_refl : forall G, gleq G G.
  Axiom gleq_trans : forall G G' G'', gleq G G' -> gleq G' G'' -> gleq G G''.
  Axiom gleq_weakening : forall {G G' p}, gleq G' G -> prod_in_g p G' -> prod_in_g p G.
  Axiom gleq_remove: forall p G pf, gleq (remove_prod p G pf) G.

  Ltac apply_gleq :=
    apply: gleq_refl || apply: gleq_weakening || apply: gleq_remove.

  Ltac happly := match goal with | [H : _ |- ?p] => eapply H end.

  Ltac cons_case :=
    (econstructor; last by eassumption);
      happly; by apply: gleq_refl.

  (* from reference manual: default implementation of the done tactic, from the 
     ssreflect.v file: *)
  Ltac done :=  trivial; hnf; intros; solve
     [ do ![solve [eassumption | trivial | apply: sym_equal; trivial | apply_gleq; eassumption
                  ]
           | discriminate | contradiction | split | happly]
       | case not_locked_false_eq_true; assumption
       | match goal with H : ~ _ |- _ => solve [case H; trivial] end
     ].
  
  Theorem to_orig :
    forall G G' t p b,
      gleq G' G ->
      G ⊢ t : p, G' | b -> G ⊢ t : p | b
  with to_orig_decomp :
    forall G G' C t1 t2 p b,
      gleq G' G ->
      G ⊢ t1 ⩦ C [ t2 ] : p , G' | b ->
      G ⊢ t1 ⩦ C [ t2 ] : p | b.
  Proof.
    - intros G G' t p b leqG'G H.
      induction H.
      + by constructor.
      + by constructor.
      + by econstructor.
      + econstructor.
        * by [].
        * happly.
          apply: gleq_trans.
          -- apply: gleq_remove.
          -- eassumption.
      + cons_case.
      + cons_case.
      + cons_case.
      + econstructor.
      + econstructor.
        * by apply: to_orig_decomp.
        * by [].
        * by [].
      + econstructor.
        * by apply: to_orig_decomp.
        * by [].
        * by [].
    - intros G G' C t1 t2 p b leqG'G H.
      generalize gleq_refl.
      intro gleq_refl.
      induction H.
      + by constructor.
      + econstructor;
          repeat happly.
        (* cons_left_decompose to_orig. *)
      + econstructor;
          repeat happly.
        (* cons_left_decompose to_orig. *)
      + econstructor;
          repeat happly.
        (* cons_left_decompose to_orig. *)
      + econstructor;
          repeat happly.
      + econstructor;
          repeat happly.
      + econstructor;
          repeat happly.
      + econstructor.
        * by apply: gleq_weakening; eassumption.
        * happly.
          apply: gleq_trans.
          -- apply: gleq_remove.
          -- eassumption.
      + econstructor;
          repeat happly.
      + econstructor;
          repeat happly.
      + econstructor;
          repeat happly.
  Qed.

  Theorem from_orig :
    forall G t p b,
      non_left_recursive_grammar ->
      G ⊢ t : p | b ->
      G ⊢ t : p, G | b
  with from_orig_decomp :
    forall G C t1 t2 p b,
      non_left_recursive_grammar ->
      G ⊢ t1 ⩦ C [ t2 ] : p | b ->
                              G ⊢ t1 ⩦ C [ t2 ] : p , G | b.
  Proof.
    - intros G t p b nonLR H.
      induction H.
      + by constructor.
      + by constructor.
      + by econstructor; eassumption.
      + econstructor.
        by eapply non_left_g_rm_sound.
        Unshelve.
        by [].
      + econstructor; last by eassumption.
        * by apply: from_orig.
        * by apply: from_orig.
      + econstructor; last by eassumption.
        * by apply: from_orig.
        * by apply: from_orig.
      + econstructor; last by eassumption.
        * by apply: from_orig.
        * by apply: from_orig.
      + by constructor.
      + have from_decomp := from_orig_decomp _ _ _ _ _ _ nonLR H.
        have subt_char := subterm_rel_characterization G p1 G t1 C t2 b1 from_decomp.
        case: subt_char => [// | [t1eqt2 C_is_hole] ].
        * econstructor; eassumption.
        * move: from_decomp.
          rewrite t1eqt2 C_is_hole.
          intros. by eapply in_hole_match_spec_noinp_cons.
    - intros G C t1 t2 p b nonLR H.
      induction H; try (econstructor; by [ | happly]).
      + (* nt *)
        econstructor.
        eapply non_left_g_rm_sound; first by [].
        eassumption.
        Unshelve.
        by [].
      + match goal with
        | [H : _ ⊢ t ⩦ _[_] : _ | _ |- _] => 
            have from_decomp := from_orig_decomp _ _ _ _ _ _ nonLR H
        end.
        have subt_char := subterm_rel_characterization _ _ _ _ _ _ _ from_decomp.
        case: subt_char => [// | [t1eqt C_is_hole] ].
        * econstructor; eassumption.
        * rewrite t1eqt C_is_hole.
          eapply in_hole_decompose_spec_noinp_cons; try eassumption.
          by rewrite C_is_hole t1eqt in from_decomp.
  Qed.
  
End Equiv.
