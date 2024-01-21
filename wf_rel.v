Require Import 
        (* Lists.List *)
        (* well-foundedness results about lexicographic product *)
        Coq.Wellfounded.Lexicographic_Product
        (* def. of disjoint union of relations. *)
        Relations.Relation_Operators
        (* dependent induction *)
        Coq.Program.Equality
        (* Decision typeclass and instances *)
        stdpp.finite.

Require Import
        patterns_terms
        grammar
        lib_ext.PeanoNatExt
        (* lib_ext.ListExt *)
        lib_ext.tactics.

(* ******************************* *)
(* relation that captures consumption of both, input and 
   productions of the grammar, during matching *)
(* ******************************* *)

Module WfRel(pt : PatTermsSymb).
  Import pt.

  Module GrammarLists := GrammarLists(pt).
  Import GrammarLists.

  (* import decidability results about pats and terms *)
  Import PatTermsDec.

  (* a well-founded relation over the domain of the matching function *)
  Section MatchRel.

    (* evolution of the input, during matching, when there is actual input 
       consumption: for the actual implementation, it is just subterm_rel *)
    Definition input_cons_evolution := subterm_rel.

    (* evolution of the pattern and grammar during matching, in the phase of no 
       consumption of input *)
    Inductive pat_grammar_evolution : pat * grammar -> pat * grammar -> Prop :=
    (* TODO: better name *)
    | pat_grammar_evolution_inhole_right : 
      forall g pc ph, pat_grammar_evolution (ph, g) (inhole_pat pc ph, g)
    | pat_grammar_evolution_inhole_left : 
      forall g pc ph, pat_grammar_evolution (pc, g) (inhole_pat pc ph, g)
    | pat_grammar_evolution_name : 
      forall g p n, pat_grammar_evolution (p, g) (p __ n , g)
    | pat_grammar_evolution_nt : 
      forall g p n (proof : prod_in_g (n, p) g),
        pat_grammar_evolution (p, remove_prod (n, p) g proof) (nt_pat n, g).

    (* to formalize non-left-recursive grammars, following definition
       of left recursive grammars from pag. 10 *)
    Definition pat_grammar_evolution_trans := 
      clos_trans_1n (pat * grammar) pat_grammar_evolution.

    (* we should allow a different grammar in each pair, since following
       the order imposed by the relation we remove productions from the
       grammar *)
    (* TODO: we should ask for g1 to be included in g2 *)
    Definition non_left_recursive_grammar :=
      forall (p : pat) (g1 g2 : grammar), 
        not (pat_grammar_evolution_trans (p, g1) (p, g2)).

    (* lexicographic product between input_cons_evolution and
       pat_grammar_evolution: the product is done in that way, 
       to make our slexprod coincide with the order in which
       terms and (pat, grammar) decrease:
       - input consumption also involves changes in the pattern 
       - pat_grammar_evolution explains the part of the matching 
         process where there are no changes to the input *)
    Definition term_pat_grammar := 
      slexprod term (pat * grammar) input_cons_evolution pat_grammar_evolution.

    (* well-founded order over the tuples of our matching algorithm *)

    (* domain of our matching algorithm *)
    Definition matching_tuple : Type := term * (pat * grammar).

    (* accessors  *)
    Definition matching_tuple_term (mt : matching_tuple) : term := fst mt.

    Definition matching_tuple_pat_grammar (mt : matching_tuple) : pat * grammar :=
      snd mt.

    Definition matching_tuple_inverted (mt : matching_tuple) :=
      (matching_tuple_pat_grammar mt, matching_tuple_term mt).

    (* order among our matching tuples: just term_pat_grammar parameterized by
       a fixed grammar *)
    Definition matching_tuple_order (G : grammar) := term_pat_grammar.
        
    (* injections into matching_tuple_order: input consumption *)
    Definition matching_tuple_order_input_cons
      (g : grammar)
      (t t' : term)
      (pg pg' : pat * grammar)
      (ev : input_cons_evolution t t') :
      matching_tuple_order g (t, (fst pg, snd pg)) (t', (fst pg', snd pg')).

      destruct pg as [p1 g1].
      destruct pg' as [p2 g2].
      unfold matching_tuple_order.
      apply (left_slex _ _
                  input_cons_evolution 
                  pat_grammar_evolution
                  t t'
                  (p1, g1) (p2, g2)
                  ev).
    Defined.

    Definition matching_tuple_order_pat_evol
      (g : grammar)
      (t : term)
      (pg pg' : pat * grammar)
      (ev : pat_grammar_evolution pg pg') :
      matching_tuple_order g (t, (fst pg, snd pg)) (t, (fst pg', snd pg')).
      destruct pg as [p1 g1].
      destruct pg' as [p2 g2].
      apply (right_slex _ _
                  input_cons_evolution 
                  pat_grammar_evolution
                  t
                  (p1, g1) (p2, g2)
                  ev).
    Defined.

  End MatchRel.

  (* ************************************************************ *)
  (* some tactics for matching_tuple_order and related types         *)
  (* ************************************************************ *)

  (* since we'll be working with tuples from a symmetric mapping
     over matching_tuples,
     usually we'll need to reconstruct their original shape; this tactic 
     implements it 
       
     tpg: the actual tuple to be reconstructed
     eqp: the hypothesis stating describing the shape of the symmetric tuple
     Heq: to name to be given to the new hypothesis showing the
            reconstructed tuple *)
    Ltac reconstruct_tuple tpg eqp Heq :=
      let Heq_snd     := fresh "Heq_snd" in
      let Heq_fst     := fresh "Heq_fst" in
      unfold matching_tuple_inverted in eqp;
      inversion eqp as [ [Heq_snd Heq_fst ] ];

      match goal with
      | [eqp : (matching_tuple_pat_grammar tpg, matching_tuple_term tpg) = 
                 ((?p, ?g2), ?t) |- _] =>

          assert(Heq: tpg = (t, (p, g2)));
          [unfold matching_tuple_pat_grammar in Heq_snd;
           rewrite <- Heq_snd;
           unfold matching_tuple_term in Heq_fst;
           rewrite <- Heq_fst;
           rewrite <- surjective_pairing;
           reflexivity
          |];

          clear Heq_snd Heq_fst
      end.

  (* tactic that encapsulates usual procedures to build evidence
       for pairs related by matching_tuple_order *)
  Ltac matching_tuple_order_build_ev :=
    match goal with
    | (* cons case left *)
      [ |- matching_tuple_order ?g1 
            (?tl, (?pl, ?g1)) 
            (ct ?tl ?tr, (cp ?pl ?pr, ?g2))] =>
        apply (matching_tuple_order_input_cons
                 g1 tl (ct tl tr) (pl, g1) (cp pl pr, g2)
                 (subterm_cons_l tl tr))
    | (* cons case right *)
      [ |- matching_tuple_order ?g1
            (list_term_c ?tr, (list_pat_c ?pr, ?g1))
            (ct ?tl ?tr, (cp ?pl ?pr, ?g2))] =>
        apply (matching_tuple_order_input_cons
                 g1 (list_term_c tr) (ct tl tr) 
                 (list_pat_c pr, g1) (cp pl pr, g2)
                 (subterm_cons_r tl tr))
    | (* nt case *)
      [ |- matching_tuple_order ?g1
            (?t, (?p, remove_prod (?n, ?p) ?g2 ?proof))
            (?t, (nt ?n, ?g2))] =>
        apply (matching_tuple_order_pat_evol
                 g1 t (p, remove_prod (n, p) g2 proof) (nt n, g2)
                 (pat_grammar_evolution_nt g2 p n proof))
    | (* hd contxt case left *)
      [ |- matching_tuple_order ?g1
            (contxt_term ?C, (?pl, ?g1))
            (ctxt hd_c ?C ?tr, (cp ?pl ?pr, ?g2))] =>
        apply (matching_tuple_order_input_cons
                 g1 (contxt_term C) (ctxt hd_c C tr) (pl, g1) (cp pl pr, g2)
                 (subterm_hd_contxt_l C tr))
    | (* hd contxt case right *)
      [ |- matching_tuple_order ?g1
            (list_term_c ?tr, (list_pat_c ?pr, ?g1))
            (ctxt hd_c ?C ?tr, (cp ?pl ?pr, ?g2))] =>
        apply (matching_tuple_order_input_cons
                 g1 tr (ctxt hd_c C tr) (list_pat_c pr, g1) 
                 (cp pl pr, g2)
                 (subterm_hd_contxt_r C tr))
    | (* tail contxt case left *)
      [ |- matching_tuple_order ?g1
            (?tl, (?pl, ?g1))
            (ctxt tail_c ?tl ?C, (cp ?pl ?pr, ?g2))] =>
        apply (matching_tuple_order_input_cons
                 g1 tl (ctxt tail_c tl C) (pl, g1) 
                 (cp pl pr, g2)
                 (subterm_tail_contxt_l tl C))
    | (* tail contxt case right *)
      [ |- matching_tuple_order ?g1
            (contxt_term (list_contxt_c ?C), (list_pat_c ?pr, ?g1))
            (ctxt tail_c ?tl ?C, (cp ?pl ?pr, ?g2))] =>
        apply (matching_tuple_order_input_cons
                 g1 (contxt_term (list_contxt_c C))
                 (ctxt tail_c tl C) (list_pat_c pr, g1) 
                 (cp pl pr, g2)
                 (subterm_tail_contxt_r tl C)
                 (* (input_cons_evolution_tail_contxt_r tl C) *)
          )
    | (* name pat *)
      [ |- matching_tuple_order ?g1
            (?t, (?p, ?g2))
            (?t, (name_pat ?x ?p, ?g2))] =>
        apply (matching_tuple_order_pat_evol
                 g1 t (p, g2) (name_pat x p, g2)
                 (pat_grammar_evolution_name g2 p x))
    | (* inhole left pat *)
      [ |- matching_tuple_order ?g1
            (?t, (?pl, ?g2))
            (?t, (inhole ?pl ?pr, ?g2))] =>
        apply (matching_tuple_order_pat_evol
                 g1 t (pl, g2) (inhole pl pr, g2)
                 (pat_grammar_evolution_inhole_left g2 pl pr))
    | (* inhole right pat, input consumption *)
      [ |- matching_tuple_order ?g1
            (?t2, (?pr, ?g1))
            (?t1, (inhole ?pl ?pr, ?g2))] =>
        match goal with
        | [ H : subterm_rel t2 t1 |- _ ] =>
            apply (matching_tuple_order_input_cons
                     g1 t2 t1 (pr, g1) (inhole pl pr, g2)
                     H)
        end
    | (* inhole right pat, no input consumption *)
      [ |- matching_tuple_order ?g1
            (?t, (?pr, ?g2))
            (?t, (inhole ?pl ?pr, ?g2))] =>
        apply (matching_tuple_order_pat_evol
                 g1 t (pr, g2) (inhole pl pr, g2)
                 (pat_grammar_evolution_inhole_right g2 pl pr))
    end.
  
  Section InputConsEvolutionProps.
      (* some results about well-foundedness of input_cons_evolution *)
      (* TODO: improve this proof *)
      Lemma input_cons_evolution_acc : forall t, Acc input_cons_evolution t.
      Proof.
        apply subterm_rel_well_founded.
      Defined.

      Theorem input_cons_evolution_well_founded : well_founded input_cons_evolution.
      Proof.
        constructor.
        intros y H.
        apply input_cons_evolution_acc.
      Defined.

    End InputConsEvolutionProps.

    Section PatGrammarEvolutionProps.
      Lemma pat_grammar_evolution_acc : 
        forall g2 p, Acc pat_grammar_evolution (p, g2).
      Proof.
        intros.
        revert p.
        apply (grammar_ind_princ
                 (fun g2 =>
                    forall (p : pat),
                      Acc pat_grammar_evolution
                          (p, g2))).
        + (* grammar = nil *)
          intros g Hg p.
          induction p;
            constructor;
            intros p_g H;
            inversion H.
          - (* name *)
            auto.
          - (* nt *)
            assert(Hg_nil : g = nil).
            {destruct g.
             - reflexivity.
             - simpl in Hg.
               lia.
            }
            subst.
            match goal with
            | [H' : prod_in_g (n, p) []%list |- _] =>
                inversion H'
            end.
            match goal with
            | [H'' : In (n, p) [] |- _] =>
                inversion H''
            end.
          - (* inhole right pat *)
            auto.
          - (* inhole left pat *)
            auto.
        + (* grammar not nil *)
          intros.
          induction p;
            constructor;
            intros p_g H';
            inversion H'.
          - (* cons *)
            apply IHp.
          - (* nt *)
            match goal with
            | [IH : ∀ g2 : grammar,
                  lt_grammar g2 g1 → ∀ p : pat, Acc pat_grammar_evolution (p, g2) |- _] =>
                apply H
            end.
            subst.
            apply remove_prod_length_decrease.
          - (* inhole right pat *)
            auto.
          - (* inhole left pat *)
            auto.
      Defined.
      
      Lemma pat_grammar_evolution_well_founded :
        well_founded pat_grammar_evolution.
      Proof.
        constructor.
        intros.
        destruct y.
        apply pat_grammar_evolution_acc.
      Defined.
      
      (* pat_grammar_evolution does not add productions *)
      Lemma pat_grammar_evolution_no_prod_added :
        forall (p1 p2 p3 : pat) (n : nonterm) (g1 g2 : grammar),
          pat_grammar_evolution (p1, g1) (p2, g2) ->
          prod_in_g (n, p3) g1                    ->
          prod_in_g (n, p3) g2.
      Proof.
        intros p1 p2 p3 n g1 g2 Hmrel Hprod_in_g1.
        inversion Hmrel as [g1' pc ph Heq_ph Heq_p2 |
                            g1' pc ph Heq_ph Heq_p2 |
                            g1' p1' v Heq_p1 Heq_p2  |].
        - (* p2 = inhole, case ph *)
          rewrite H0 in Hprod_in_g1.
          exact Hprod_in_g1.
        - (* p2 = inhole, case pc *)
          rewrite H0 in Hprod_in_g1.
          exact Hprod_in_g1.
        - (* p2 = name *)
          rewrite H0 in Hprod_in_g1.
          exact Hprod_in_g1.
        - (* p2 = nt *)
          rewrite <- H0 in Hprod_in_g1.
          rewrite <- H2.
          apply (remove_prod_in_g (n0, p1) (n, p3) g
                                  proof Hprod_in_g1).
      Qed.

    End PatGrammarEvolutionProps.

    (* well-foundedness and structure results about matching_tuple_order *)
    Section MatchRelProps.
      Lemma term_pat_grammar_well_founded : well_founded term_pat_grammar.
      Proof.
        apply wf_slexprod.
        - (* well_founded input_cons_evolution *)
          apply input_cons_evolution_well_founded.
        - (* well_founded pat_grammar_evolution *)
          apply pat_grammar_evolution_well_founded.
      Defined.

      Theorem matching_tuple_order_well_founded : 
        forall g, well_founded (matching_tuple_order g).
      Proof.
        intro g.
        apply wf_slexprod.
        - (* well_founded grammar_rel *)
          unfold input_cons_evolution.
          apply subterm_rel_well_founded.
        - (* well_founded term_pat_grammar *)
          apply pat_grammar_evolution_well_founded.
      Defined.

      (* induction principle over tuples derived from the well-foundedness of
         matching_tuple_order *)
      Definition matching_tuple_ind (P : matching_tuple -> Prop) (g : grammar) :=
        well_founded_ind (matching_tuple_order_well_founded g) P.
        
      (* results and definitions about matching_tuple_order's structure *)

      (* the only minimals that are of interest to the matching process *)
      Definition match_minimals (p : pat) (t : term) :=
        p = hole_pat \/
          (exists l, (t, p) = (lit_term l, lit_pat l)).
      
      
      (* an algorithm to reason about minimals *)
      Definition match_minimals_dec (p : pat) (t : term) :
        {match_minimals p t} + {not (match_minimals p t)}.
      Proof.
        unfold match_minimals.

        assert (Decision (p = hole__p)) as HeqDecHole.
        {apply pat_eq_dec.
        }
      
        assert (Decision (∃ l : lit, (t, p) = (lter l, lp l))) as HeqDecLit.
        {unfold Decision.
         destruct t, p;
           solve[right;
                 intros [l' Heq];
                 inversion Heq
                | (* lit  *)
                  match goal with
                  | [l1 : lit, l2 : lit |- _] =>
                      destruct (lit_eq_dec l1 l2)
                  end;
                 [(* = *)
                   left;
                   subst;
                   eauto
                 | (* <> *)
                   right;
                   intros [l' Heq];
                   inversion Heq;
                   subst;
                   auto] ].
        }
        
        apply or_dec;
          assumption.
      Defined.

      (* non-minimals of interest to the matching process *)
      Definition match_non_minimals (p : pat) (t : term) :=
        ((exists pl pr, p = cp pl pr) /\ 
           ((exists tl tr, t = ct tl tr) \/ 
            (exists c tr, t = ctxt (hd_c c tr)) \/
            (exists tl c, t = ctxt (tail_c tl c)))) 
        \/
          (exists pc ph, p = inhole_pat pc ph) 
        \/
          (exists x p', p = p' __ x) 
        \/
          (exists n, p = nt n).

      (* we have an algorithm to decide about non-minimals *)
      Definition match_non_minimals_dec (p : pat) (t : term) :
        {match_non_minimals p t} + {not (match_non_minimals p t)}.
        refine(
            match p as p' return p = p' -> {match_non_minimals p t} +
                                          {not (match_non_minimals p t)}
            with
            | cp pl pr => 
                fun eqp : p = cp pl pr =>
                  match t as t' return t = t' -> {match_non_minimals p t} +
                                                {not (match_non_minimals p t)}
                  with
                  | ct tl tr             => 
                      fun eqt : t = ct tl tr => _

                  | contxt_term (hd_c c tr) => 
                      fun eqt : t = contxt_term (hd_c c tr) => _

                  | contxt_term (tail_contxt tl c) =>
                      fun eqt : t = contxt_term (tail_c tl c) => _
                                                                  
                  | _ => fun eqt : _ => _
                  end eq_refl
            | inhole_pat pc ph => 
                fun eqp : p = inhole_pat pc ph => _

            | p' __ x =>
                fun eqp : p = p' __ x => _

            | nt n => 
                fun eqp : p = nt n=> _

            | _ =>
                fun eqp : p = _ => _
            end eq_refl);
          solve [right;
                 intro H;
                 inversion H 
                   as [[[pl [pr Heq_p]] _] | 
                        [[pc [ph Heq_p]] | [[x [p' Heq_p]] | [n Heq_p]]]];
                   rewrite eqp in Heq_p;
                   inversion Heq_p
                | right;
                  intro H;
                  unfold match_non_minimals in H;
                  inversion H 
                    as [[_ [[tl [tr Heq_t]] | 
                             [[c' [tr Heq_t]] | [tl [c' Heq_t]]]]] | 
                         [[pc [ph Heq_p]] | [[x [p' Heq_p]] | [n Heq_p]]]];
                  (rewrite eqt in Heq_t; inversion Heq_t) + 
                  (rewrite eqp in Heq_p; inversion Heq_p)
                | left;
                  unfold match_non_minimals;
                  (rewrite eqp;
                   rewrite eqt) +
                    rewrite eqp;  
                  firstorder eauto].
        Defined.

    End MatchRelProps.
    
  End WfRel.
