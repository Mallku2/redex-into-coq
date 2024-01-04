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
        induction t using lt_term_ind_princ.
        + (* size_term t = 0 *)
          assert(size_term t <> 0).
          {apply size_term_neq_0.
          }
          contradiction.
        + (* case (exists l : lit, t = lit_term l) \/  *)
          (*       t = contxt_term hole_contxt *)
          assert(H0 : (exists l, t = lit_term l) \/ 
                        t = contxt_term hole_contxt_c
                      \/ t = list_term_c nil_term_c).
          {apply size_term_lit_contxt_1.
           exact H.
          }
          inversion H0 as [H1 | H3].
          - (* lit *)
            constructor.
            intros t' Hinput.
            inversion H1.
            subst.
            inversion Hinput.
            assert(not (exists l', (lit_term x) = (lit_term l'))).
            {subst.
             eauto using subterm_rel_lit_min.
            }
            subst.
            contradiction.
          - (* hole or nil *)
            inversion H3 as [H1 | H2].
            -- (* hole *)
               rewrite H1.
               constructor.
               intros.
               inversion H2.
               assert(contxt_term hole_contxt_c <> contxt_term hole_contxt_c).
               {subst.
                eauto using subterm_rel_hole_min.
               }
               assert(contxt_term hole_contxt_c = contxt_term hole_contxt_c).
               {reflexivity.
               }
               contradiction.
            -- (* nil *)
               rewrite H2.
               constructor.
               intros t' H1.
               inversion H1.
               assert(list_term_c nil_term_c <> list_term_c nil_term_c).
               {eauto using subterm_rel_nil_min.
               }
               contradiction.
        + (* 1 < size_term t *)
          assert((exists tl tr, t = list_term_c (cons_term_c tl tr)) \/
                 (exists cl tr, t = contxt_term (hd_c cl tr)) \/
                 (exists tl cr, t = contxt_term (tail_c tl cr)))
          as [[tl [tr Heq_t]] | [[cl [tr Heq_t]] | [tl [cr Heq_t]]]].
          {apply (size_term_lt_1 t H).
          } 
          - (* cons *)
            constructor.
            intros t' Hinput.
            rewrite Heq_t in Hinput.
            inversion Hinput.
            ++ (* left *)
               assert(lt_term tl (ct tl tr)).
               {unfold lt_term.
                simpl.
                rewrite <- succ_ord_left.
                apply suc_prop_add.
               }
               subst.
               eauto.
            ++ (* right *)
               assert(lt_term tr (ct tl tr)).
               {unfold lt_term.
                simpl.
                rewrite sum_comm.
                rewrite <- succ_ord_left.
                apply suc_prop_add.
               }
               subst.
               eauto.
            ++ (* inhole case: subterm *)
               subst.
               assert(size_term t' < size_term (ct tl tr)).
               {apply subterm_rel_decre.
                auto.
               }
               auto.
          - (* left contxt *)
            constructor.
            intros t' Hinput.
            rewrite Heq_t in Hinput.
            inversion Hinput;
              solve[assert (lt_term t' t);
                    [unfold lt_term;
                     subst;
                     (simpl;
                      lia) +
                       eauto using subterm_rel_decre
                    |];
                    subst;
                    eauto].
          - (* right contxt *)
            constructor.
            intros t' Hinput.
            rewrite Heq_t in Hinput.
            inversion Hinput.
            * (* left sub-pat *)
              assert (lt_term t' t);
                [unfold lt_term;
                 subst;
                 simpl;
                 lia
                |].
              subst.
              eauto.
            * (* right sub-pat *)
              subst.
              constructor.
              intros y H1.
              inversion H1.
              -- (* right sub-pat *)
                 subst.
                 apply H0.
                 unfold lt_term.
                 simpl.
                 lia.
              -- (* nil *)
                 subst.
                 apply H0.
                 unfold lt_term.
                 simpl.
                 lia.
              -- (* context c *)
                 subst.
                 apply H0.
                 unfold lt_term.
                 simpl.
                 lia.
              -- (* tr *)
                 subst.
                 apply H0.
                 unfold lt_term.
                 simpl.
                 lia.
              -- (* smaller than tl *)
                 subst.
                 apply H0.
                 unfold lt_term.
                 unfold input_cons_evolution in H1.
                 unfold input_cons_evolution in Hinput.
                 apply (subterm_rel_decre y (ctxt cr)) in H1.
                 simpl in H1.
                 simpl.
                 lia.
            * (* tail contxt, right sub-pattern *)
              assert (lt_term t' t);
                [unfold lt_term;
                 subst;
                 (simpl;
                  lia) +
                   eauto using subterm_rel_decre
                |];
                subst;
                eauto.
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
  
    (* TODO: check if we really need pat_gen_hole *)
    (* ************************************************************************ *)
    (* pat_gen_hole: a simple decidable criterion to determine if a given pattern
       matches against a "hole"; useful to define, later, an induction principle               to reason about tuples grammar * term * pat * grammar               *)
    (* ************************************************************************ *)
    Section PatGenHole.
      Definition hole_term := contxt_term hole_contxt_c.

      (* TODO: prove soundness of pat_gen_hole *)
      (* pat_gen_hole (p, g) <-> g |- hole : p | b, for some b *)
      Inductive pat_gen_hole : pat * grammar  -> Prop :=
      | pat_gen_hole_hole_case : forall g, pat_gen_hole (hole_pat, g)
      | pat_gen_hole_name_case : 
        forall v p g, 
          pat_gen_hole (p, g) -> 
          pat_gen_hole (name_pat v p, g)
      | pat_gen_hole_nt_case : 
        forall g n p (proof : prod_in_g (n, p) g), 
          pat_gen_hole (p, remove_prod (n, p) g proof) ->
          pat_gen_hole (nt n, g) 
      | pat_gen_hole_inhole_case : 
        forall p1 p2 g, pat_gen_hole (p1, g) -> 
                   pat_gen_hole (p2, g) ->
                   pat_gen_hole (inhole_pat p1 p2, g).

      (* iterates over get_rhs g n looking for pats p such that *)
      (* pat_gen_hole (p, remove_prod (n, p) g proof); returns them,
       or returns a vacuous statement if no such patterns are found *)
      Fixpoint extract_pat_gen_hole_aux
        (tup_g_t : grammar * term)
        (g : grammar)
        (n : nonterm)
        (g_rhs : list {p : pat | prod_in_g (n, p) g})
        (IH : forall tup : pat * grammar,
            pat_grammar_evolution tup (nt n, g) ->
            {pat_gen_hole tup} + {~ (pat_gen_hole tup)}) :
        list {p : pat | {proof : prod_in_g (n, p) g |
                          pat_gen_hole (p, remove_prod (n, p) g proof)}}
        :=

        match g_rhs with
        | nil                    => nil 
        | (exist _ p proof) :: tail =>

            (* reason about pat_gen_hole p *)
            (match (IH (p, remove_prod (n, p) g proof)
                      (pat_grammar_evolution_nt g p n proof)) as IH'
                   return (IH (p, remove_prod (n, p) g proof)
                             (pat_grammar_evolution_nt g p n proof) = IH') ->
                          list {p : pat | 
                                 {proof : prod_in_g (n, p) g |
                                   pat_gen_hole (p, remove_prod (n, p) g proof)}}
             with
             | left proof_pat  =>
                 
                 (* pat_gen_hole p *)
                 (fun proof_IH : (IH (p, remove_prod (n, p) g proof)
                                  (pat_grammar_evolution_nt g p n proof)) =
                                 left proof_pat =>
                    (exist (fun p : pat =>
                              {proof : prod_in_g (n, p) g |
                                pat_gen_hole (p, remove_prod (n, p) g
                                                   proof)})
                       p
                       (exist
                          (fun proof : prod_in_g (n, p) g =>
                             (pat_gen_hole (p, remove_prod (n, p) g proof)))
                          proof
                          proof_pat))
                      :: (extract_pat_gen_hole_aux tup_g_t g n tail IH)
                      
                 )
                   
             | right proof_pat =>
                 
                 (* not pat_gen_hole p *)
                 (fun proof_IH : (IH (p, remove_prod (n, p) g proof)
                                  (pat_grammar_evolution_nt g p n proof)) =
                                 right proof_pat =>
                    (extract_pat_gen_hole_aux tup_g_t g n tail IH)
                 )
                   
             end eq_refl)
        end.
      
      (* extracts every pat from get_rhs g n, then computes as  *)
      (* extract_npat_gen_hole_aux *)
      Definition extract_pat_gen_hole
        (tup_g_t : grammar * term)
        (g : grammar)
        (n : nonterm)
        (IH : forall tup : pat * grammar,
            pat_grammar_evolution tup (nt n, g) ->
            {pat_gen_hole tup} + {~ (pat_gen_hole tup)}) :
        list {p : pat | {proof : prod_in_g (n, p) g |
                          pat_gen_hole (p, remove_prod (n, p) g proof)}} :=
        extract_pat_gen_hole_aux tup_g_t g n (get_rhs g n) IH.

      (* an algorithm to decide about pat_gen_hole *)
      Definition pat_gen_hole_dec (tup : pat * grammar) : 
        {pat_gen_hole tup} + {not (pat_gen_hole tup)}.
        refine (Fix 
                  (* note that pat_gen_hole follows the same path described by
                   pat_grammar_evolution: there is no consumption of input while
                   expanding/consuming the pattern *)
                  pat_grammar_evolution_well_founded
                  (* dependent range type of the function that we are building *)
                  (fun tup : pat * grammar  => {pat_gen_hole tup} + 
                                              {not (pat_gen_hole tup)}) 
                  (* the function body *)
                  (fun (tup1 : pat * grammar)
                     (dec_pat_gen_hole' : forall (tup2 : pat * grammar),
                         (pat_grammar_evolution tup2 tup1) -> 
                         {pat_gen_hole tup2} + {not (pat_gen_hole tup2)}) =>
                     match tup1 as tup1' 
                           return tup1 = tup1' -> {pat_gen_hole tup1} + 
                                                   {not (pat_gen_hole tup1)}
                     with
                     | (hole_pat, g')     =>
                         fun eqp : tup1 = (hole_pat, g') =>
                           _
                     | (name_pat v p, g') =>
                         fun eqp : tup1 = (name_pat v p, g') =>
                           _
                     | (nt n, g') =>
                         fun eqp : tup1 = (nt n, g') =>
                           _
                     | (inhole_pat p1 p2, g') =>
                         fun eqp : tup1 = (inhole_pat p1 p2, g') =>
                           match (dec_pat_gen_hole' (p1, g') _), 
                             (dec_pat_gen_hole' (p2, g') _) with
                           | left proof_p1, right proof_p2 => _ 
                           | _, _                         => _
                           end
                     | _ => fun eqp : _ => _
                     end eq_refl) tup).
        - (* lit_pat *)
          right.
          intro H.
          rewrite eqp in H.
          inversion H.
        - (* hole pat *)
          rewrite eqp.  
          left. 
          apply (pat_gen_hole_hole_case g').
        - (* cons_pat *)
          right.
          intro H.
          rewrite eqp in H.
          inversion H.
        - (* name pat *)
          rewrite eqp.
          rewrite eqp in dec_pat_gen_hole'.
          destruct (dec_pat_gen_hole' (p, g') (pat_grammar_evolution_name g' p v)).
          + (* pat_gen_hole (p, g') *)
            left.
            apply (pat_gen_hole_name_case v p g' p1).
          + (* not pat_gen_hole (p, g') *)
            right.
            intro H.
            inversion H.
            contradiction.
        - (* nt pat *)
          (* m_rel_noinp_cons step *)
          rewrite eqp.
          rewrite eqp in dec_pat_gen_hole'.
          clear eqp.

          (* reason about extract_pat_gen_hole to obtain evidence that
           pat_gen_hole nt or not pat_gen_hole nt *)
          remember (extract_pat_gen_hole (snd tup, hole_term) g' n 
                                         dec_pat_gen_hole')
            as ev_pat_gen_hole eqn:Hev_pat_gen_hole.
          destruct ev_pat_gen_hole as [ | hd_pat_gen tl_pat_gen].
          + (* extract_pat_gen_hole = nil *)
            right.
            intro Hpat_gen_hole.
            unfold extract_pat_gen_hole in Hev_pat_gen_hole.
            inversion Hpat_gen_hole.
            assert(exists (proof : prod_in_g (n, p0) g')
                     (g1 g2 : list {p : pat | prod_in_g (n, p) g'}),
                      get_rhs g' n =  g1
                                        ++ ((exist (fun pa =>
                                                      prod_in_g (n, pa) g')
                                               p0
                                               proof) :: nil)
                                        ++ g2)
              as [proof' [g1 [g2 Hget_rhs_split]]].
            {apply get_rhs_split.
             exact proof.
            }
            rewrite Hget_rhs_split in Hev_pat_gen_hole.

            assert(forall g1 g2,
                      extract_pat_gen_hole_aux (snd tup, hole_term) g' n
                        (g1 ++ g2)
                        dec_pat_gen_hole' =
                        (extract_pat_gen_hole_aux (snd tup, hole_term) g' n g1
                           dec_pat_gen_hole')
                          ++
                          (extract_pat_gen_hole_aux (snd tup, hole_term) g' n g2
                             dec_pat_gen_hole'))
              as Hextrat_pat_dist.
            {clear Hev_pat_gen_hole.
             intros g1' g2'.
             induction g1' as [ | hdg1' tlg1' IH].
             - (* g1' = nil *)
               reflexivity.
             - (* g1 = hdg1 :: tlg1 *)
               destruct hdg1'.
               simpl.
               destruct (dec_pat_gen_hole' (x, remove_prod (n, x) g' p1)
                           (pat_grammar_evolution_nt g' x n p1))
                 as [Hpat_gen_x | Hnpat_gen_x];
                 rewrite IH;
                 reflexivity.
            }
            assert(extract_pat_gen_hole_aux 
                     (snd tup, hole_term) g' n
                     (g1 ++
                        (exist
                           (fun pa : pat => prod_in_g (n, pa) g') p0
                           proof' :: nil) ++ g2) dec_pat_gen_hole' =
                     (extract_pat_gen_hole_aux 
                        (snd tup, hole_term) g' n g1 dec_pat_gen_hole')
                       ++
                       (extract_pat_gen_hole_aux 
                          (snd tup, hole_term) g' n ((exist
                                                        (fun pa : pat => prod_in_g
                                                                           (n, pa) g') p0
                                                        proof' :: nil) ++ g2))
                       dec_pat_gen_hole')
              as Hextract_pat_dist_g1.
            {apply Hextrat_pat_dist.
            }
            clear Hextrat_pat_dist.
            rewrite Hextract_pat_dist_g1 in Hev_pat_gen_hole.
            clear Hextract_pat_dist_g1.

            apply eq_sym in Hev_pat_gen_hole.
            apply app_eq_nil in Hev_pat_gen_hole.
            inversion Hev_pat_gen_hole as [Hnil_g1 Hnil_g2].
            clear Hnil_g1.

            simpl in Hnil_g2.
            destruct (dec_pat_gen_hole'
                        (p0, remove_prod (n, p0) g' proof')
                        (pat_grammar_evolution_nt g' p0 n proof'))
              as [Hpat_gen_p0 | Hnpat_gen_p0].
            -- (* pat_gen p0 *) 
               inversion Hnil_g2.
            -- (* not pat_gen p0 *)
               contradiction.
          + (* extract_pat_gen_hole = hd_pat_gen :: tl_pat_gen  *)
            destruct hd_pat_gen as [p' Hproof_pat_gen_p'].
            inversion Hproof_pat_gen_p' as [proof_pat_gen_p' Hproof_pat_gen_p''].
            left.
            apply (pat_gen_hole_nt_case g' n p' proof_pat_gen_p' Hproof_pat_gen_p'').  
        - (* inhole_pat p1 p2 *)
          (* m_rel_noinp_cons p1 step *)
          rewrite eqp.
          apply (pat_grammar_evolution_inhole_left g' p1 p2).
        - (* actual proof of pat_gen_hole *)
          (* both sub-patterns generate hole *)
          rewrite eqp.
          left.
          apply (pat_gen_hole_inhole_case p1 p2 g' p0 p3).
        - (* actual proof of pat_gen_hole *)
          (* some sub-pattern does not generate hole *)
          rewrite eqp.
          right.
          intro H.
          inversion H.
          contradiction.
        - (* inhole_pat p1 p2 *)
          (* pat_gen_hole *)
          rewrite eqp.
          right.
          intro H.
          inversion H.
          contradiction.

          Unshelve.
          rewrite eqp.
          apply (pat_grammar_evolution_inhole_right g' p1 p2).
      Defined.
      

    End PatGenHole.
    
    (* (* inductive principle for reasoning over tuples (g1, (t, (p, g2))) *) *)
    (* (* TODO: check if we really need this induction principle *) *)
    (* Section MrelTupIndPrinc. *)
    (*   Variable P : matching_tuple -> Prop. *)
      
    (*   (* pairs term * pat that do not represent a matching, last equation of M *) *)
    (*   Hypothesis default_eq :  *)
    (*     forall g1 g2 p t, *)
    (*       not (match_minimals p t) -> *)
    (*       not (match_non_minimals p t) -> *)
    (*       P (g1, (t, (p, g2))). *)

    (*   (* pairs term * pat corresponding to the remaining equations of M *) *)
    (*   Hypothesis first_eq :  *)
    (*     forall g1 g2, P (g1, (hole, (hole_pat, g2))). *)

    (*   Hypothesis second_eq :  *)
    (*     forall g1 g2 t, t <> hole -> P (g1, (t, (hole_pat, g2))). *)

    (*   Hypothesis third_eq :  *)
    (*     forall g1 g2 l1 l2, P (g1, (lit_term l2, (lit_pat l1, g2))). *)
      
    (*   Hypothesis fourth_eq_cons_term : *)
    (*     forall g1 g2 pl pr tl tr, P (g1, (tl, (pl, g1))) -> *)
    (*                          P (g1, (list_term_c tr, (list_pat_c pr, g1))) -> *)
    (*                          P (g1, (ct tl tr, (cp pl pr, g2))). *)
      
    (*   Hypothesis fourth_eq_contxt_term_l : *)
    (*     forall g1 g2 pl pr c tr, P (g1, (ctxt c, (pl, g1))) -> *)
    (*                         P (g1, (list_term_c tr, (list_pat_c pr, g1))) -> *)
    (*                         P (g1, (ctxt (lc c tr), (cp pl pr, g2))). *)

    (*   Hypothesis fourth_eq_contxt_term_r : *)
    (*     forall g1 g2 pl pr tl c, P (g1, (tl, (pl, g1))) -> *)
    (*                         P (g1, (ctxt c, (list_pat_c pr, g1))) -> *)
    (*                         P (g1, (ctxt (rc tl c), (cp pl pr, g2))). *)

    (*   (* in-hole case, not (pat_gen_hole (pc, g2)): pattern pc implies a  *)
    (*    decomposition of t between a context C <> hole, and a subterm tc <> t  *) *)
    (*   Hypothesis fifth_eq_inp_cons : *)
    (*     forall g1 g2 pc ph t, P (g1, (t, (pc, g2))) -> *)
    (*                      (* TODO: check if this is actually needed *) *)
    (*                      not (pat_gen_hole (pc, g2)) -> *)
    (*                      (* NOTE: maybe we are asking for more than what it is needed *) *)
    (*                      (forall tc, subterm_rel tc t -> P (g1, (tc, (ph, g1)))) -> *)
    (*                      P (g1, (t, (inhole_pat pc ph, g2))). *)

    (*   (* in-hole case, pat_gen_hole (pc, g2): pattern pc implies a  *)
    (*    decomposition of t between a context C = hole, and a subterm tc = t  *) *)
    (*   Hypothesis fifth_eq_noinp_cons : *)
    (*     forall g1 g2 pc ph t, P (g1, (t, (pc, g2))) -> *)
    (*                      (* TODO: check if this is actually needed *) *)
    (*                      pat_gen_hole (pc, g2) -> *)
    (*                      P (g1, (t, (ph, g2))) -> *)
    (*                      P (g1, (t, (inhole_pat pc ph, g2))). *)

    (*   Hypothesis sixth_eq : *)
    (*     forall g1 g2 x p t, *)
    (*       P (g1, (t, (p, g2))) -> *)
    (*       P (g1, (t, (name_pat x p, g2))). *)

    (*   Hypothesis seventh_eq : *)
    (*     forall g1 g2 n t, *)
    (*       (forall p (proof : prod_in_g (n, p) g2), *)
    (*           P (g1, (t, (p, remove_prod (n, p) g2 proof)))) -> *)
    (*           P (g1, (t, (nt n, g2))). *)

    (*   (* some useful tactics that cannot be in another section (because of *)
    (*      visibility rules reasons) *) *)

    (*   (* a tactic to prove that a pair (p, t) is not a minimal, and to name H *)
    (*      the obtained lemma *) *)
    (*   Ltac prove_not_minimal p t H := *)
    (*     assert(H : not (match_minimals p t)); *)
    (*     [let Hmin_dec := fresh "Hmin_dec" in *)
    (*      assert(Hmin_dec: {match_minimals p t} + {not (match_minimals p t)}); *)
    (*      [apply match_minimals_dec *)
    (*      |]; *)
    (*      let Hmin := fresh "Hmin" in *)
    (*      let Hnmin := fresh "Hnmin" in *)
    (*      inversion Hmin_dec as [Hmin | Hnmin]; *)
    (*      [(* match_minimals p t *) *)
    (*       inversion Hmin as [Hhole_lit | [l' Hcons_lit]]; *)
    (*       [(* p = hole__p *) *)
    (*         inversion Hhole_lit *)
    (*       |(* (t, p) = (lter l', lp l') *) *)
    (*         inversion Hcons_lit *)
    (*       ] *)
    (*      | (* ¬ match_minimals l t *) *)
    (*        exact Hnmin] *)
    (*     |]. *)

    (*   (* a tactic to prove that a pair (p, t) is not a non-minimal, and to name H *)
    (*      the obtained lemma *) *)
    (*   Ltac prove_not_non_minimal p t H := *)
    (*   assert(H: not (match_non_minimals p t)); *)
    (*   [let Hdec := fresh "Hdec" in *)
    (*    assert(Hdec : {match_non_minimals p t} + {not (match_non_minimals p t)}); *)
    (*     [apply match_non_minimals_dec *)
    (*     |]; *)

    (*    let Hnmin' := fresh "Hnmin'" in *)
    (*    let Hnnmin := fresh "Hnnmin" in *)
    (*    inversion Hdec as [Hnmin' | Hnnmin]; *)
    (*     [(* match_non_minimals (lp l) l0 *) *)
    (*       let pl    := fresh "pl" in *)
    (*       let pr    := fresh "pr" in *)
    (*       let Heq_p := fresh "Heq_p" in *)
    (*       let x     := fresh "x" in *)
    (*       let p     := fresh "p" in *)
    (*       let n     := fresh "n" in *)
    (*       let tl    := fresh "tl" in *)
    (*       let tr    := fresh "tr" in *)
    (*       let Heq_t := fresh "Heq_t" in *)
    (*       let c     := fresh "c" in *)
    (*       inversion Hnmin'  *)
    (*       as [[[pl [pr Heq_p]] *)
    (*              [[tl [tr Heq_t]] |  *)
    (*                [[c [tr Heq_t]] | [tl [c Heq_t]]]]] |  *)
    (*            [[pl [pr Heq_p]] | [[x [p Heq_p]] | [n Heq_p]]]]; *)
    (*       solve[inversion Heq_p | inversion Heq_t] *)
    (*     |(* ¬ match_non_minimals (lp l) l0 *) *)
    (*       exact Hnnmin *)
    (*       ] *)
    (*   |]. *)

    (*   Definition matching_tuple_order_ind_princ (tup : matching_tuple) : P tup. *)
    (*     refine *)
    (*       (Fix *)
    (*          matching_tuple_order_well_founded *)
    (*          (* dependent range type of the function that we are building *) *)
    (*          (fun tup : matching_tuple => P tup) *)
    (*          (* the function body *) *)
    (*          (fun (tup1 : matching_tuple) *)
    (*             (ind_princ' :  *)
    (*               forall (tup2 : matching_tuple), *)
    (*                 matching_tuple_order tup2 tup1 -> P tup2) => *)
    (*             (* changing order of members of tup1, to obtain a  *) *)
    (*             (* function that matches, first, over the pattern: it *) *)
    (*             (* helps in obtaining shorter proofs *) *)
    (*             match (matching_tuple_inverted tup1) as tup1' *)
    (*                   return (matching_tuple_inverted tup1) = tup1' -> P tup1 with *)
    (*             (* the hole decomposition rule decomposes any term t  *) *)
    (*             (* into the empty context and t itself. *) *)
    (*             | ((hole_pat, g2), (g1, t)) => *)
    (*                 fun eqp : matching_tuple_inverted tup1 = *)
    (*                           ((hole_pat, g2), (g1, t)) => *)
    (*                   match term_eq_dec t (contxt_term hole_contxt_c) with *)
    (*                   | left proof  => _ *)
    (*                   | right proof => _ *)
    (*                   end *)

    (*             | ((lit_pat li1, g2), (g1, lit_term li2)) => *)
    (*                 fun eqp : matching_tuple_inverted tup1 = *)
    (*                           ((lit_pat li1, g2), (g1, lit_term li2)) => *)
    (*                   _ *)
                        
    (*             | ((cp pl pr, g2), (g1, ct tl tr)) => *)
    (*                 fun eqp : matching_tuple_inverted tup1 = *)
    (*                           ((cp pl pr, g2), (g1, ct tl tr)) => *)
    (*                   _ *)
                        
    (*             | ((cp pl pr, g2), (g1, contxt_term (hd_c c tr))) => *)
    (*                 fun eqp : matching_tuple_inverted tup1 = *)
    (*                           ((cp pl pr, g2), (g1, ctxt (lc c tr))) => *)
    (*                   _ *)
                        
    (*             | ((cp pl pr, g2), (g1, contxt_term (tail_c tl c))) => *)
    (*                 fun eqp : matching_tuple_inverted tup1 = *)
    (*                           ((cp pl pr, g2), (g1, ctxt (rc tl c))) => *)
    (*                   _ *)
                        
    (*             | ((inhole_pat pc ph, g2), (g1, t)) => *)
    (*                 fun eqp : matching_tuple_inverted tup1 = *)
    (*                           ((inhole_pat pc ph, g2), (g1, t)) => *)
    (*                   _ *)
                        
    (*             | ((name_pat x p, g2), (g1, t)) => *)
    (*                 fun eqp : matching_tuple_inverted tup1 = *)
    (*                           ((name_pat x p, g2), (g1, t)) => *)
    (*                   _ *)
                        
    (*             | ((nt n, g2), (g1, t)) => *)
    (*                 fun eqp : matching_tuple_inverted tup1 = *)
    (*                           ((nt n, g2), (g1, t)) => *)
    (*                   _ *)
    (*             | ((p, g2), (g1, t)) => fun eqp : _ => _ *)
    (*             end eq_refl) tup). *)
    (*     - (*  lit_term, lit_pat  *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
    (*       apply (third_eq g1 g2 li1 li2). *)
    (*     - (*  lit_pat, cons_term *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
    (*       prove_not_minimal (lit_pat l) l0 Hnmin. *)
    (*       prove_not_non_minimal (lit_pat l) l0 Hnnmin. *)
    (*       apply (default_eq g1 g2 (lit_pat l) l0 Hnmin Hnnmin). *)
    (*     - (*  lit_pat, contxt_term c *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
    (*       prove_not_minimal (lp l) (ctxt c) Hnmin. *)
    (*       prove_not_non_minimal (lp l) (ctxt c) Hnnmin. *)
    (*       apply (default_eq g1 g2 (lp l) (ctxt c) Hnmin Hnnmin). *)
    (*     - (* contxt_term hole_contxt_c, hole_pat *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
    (*       rewrite proof. *)
    (*       apply (first_eq g1 g2). *)
    (*     - (* t, hole_pat *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
    (*       apply (second_eq g1 g2 t proof). *)
    (*     - (* t, nil *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
    (*       prove_not_minimal (list_pat_c nil_pat_c) t Hnmin. *)
    (*       prove_not_non_minimal (list_pat_c nil_pat_c) t Hnnmin. *)
    (*       apply (default_eq g1 g2 (list_pat_c nil_pat_c) t Hnmin Hnnmin). *)
    (*     - (*  lit_term, cons_pat *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
    (*       prove_not_minimal (cp p2 l0) (lter l1) Hnmin. *)
    (*       prove_not_non_minimal (cp p2 l0) (lter l1) Hnnmin. *)
    (*       apply (default_eq g1 g2 (cp p2 l0) (lter l1) Hnmin Hnnmin). *)
    (*     - (* cons, nil *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
    (*       prove_not_minimal (cp p2 l0) (list_term_c nil_term_c) Hnmin. *)
    (*       prove_not_non_minimal (cp p2 l0) (list_term_c nil_term_c) Hnnmin. *)
    (*       apply (default_eq g1 g2 (cp p2 l0) (list_term_c nil_term_c) Hnmin Hnnmin). *)
    (*     - (* cons_pat, cons_term *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
    (*       assert(Hind_tl: P (g1, (tl, (pl, g1)))). *)
    (*       {rewrite Heq_tup1 in ind_princ'. *)
    (*        apply (ind_princ' (g1, (tl, (pl, g1))) *)
    (*                 (matching_tuple_order_input_cons *)
    (*                    g1 tl (ct tl tr) *)
    (*                    (pl, g1) *)
    (*                    (cp pl pr, g2) *)
    (*                    (input_cons_evolution_cons_left tl tr))). *)
    (*       } *)
          
    (*       assert(Hind_tr : P (g1, (list_term_c tr, (list_pat_c pr, g1)))). *)
    (*       {rewrite Heq_tup1 in ind_princ'. *)
    (*        apply (ind_princ' (g1, (list_term_c tr, (list_pat_c pr, g1))) *)
    (*                 (matching_tuple_order_input_cons *)
    (*                    g1 tr (ct tl tr) (list_pat_c pr, g1) *)
    (*                    (cp pl pr, g2) *)
    (*                    (input_cons_evolution_cons_right tl tr))). *)
    (*       } *)
    (*       apply (fourth_eq_cons_term g1 g2 pl pr tl tr Hind_tl Hind_tr). *)
    (*     - (* cons_pat p0 p1, contxt_term hole_contxt_c *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
    (*       prove_not_minimal (cp p2 l0) hole Hnmin. *)
    (*       prove_not_non_minimal (cp p2 l0) hole Hnnmin. *)
    (*       apply (default_eq g1 g2 (cp p2 l0) hole Hnmin Hnnmin). *)
    (*     - (* cons_pat, contxt_term (hd_c c tr) *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
          
    (*       assert(Hind_l: P (g1, (ctxt c, (pl, g1)))). *)
    (*       {rewrite Heq_tup1 in ind_princ'. *)
    (*        apply (ind_princ' (g1, (ctxt c, (pl, g1))) *)
    (*                 (matching_tuple_order_input_cons *)
    (*                    g1 (ctxt c) (ctxt (lc c tr)) (pl, g1) *)
    (*                    (cp pl pr, g2) *)
    (*                    (input_cons_evolution_hd_c_l c tr))). *)
    (*       } *)

    (*       assert(Hind_r: P (g1, (list_term_c tr, (list_pat_c pr, g1)))). *)
    (*       {rewrite Heq_tup1 in ind_princ'. *)
    (*        apply (ind_princ' (g1, (list_term_c tr, (list_pat_c pr, g1))) *)
    (*                 (matching_tuple_order_input_cons  *)
    (*                    g1 tr *)
    (*                    (ctxt (lc c tr)) *)
    (*                    (list_pat_c pr, g1) *)
    (*                    (cp pl pr, g2) *)
    (*                    (input_cons_evolution_hd_c_r c tr))). *)
    (*       } *)
    (*       apply (fourth_eq_contxt_term_l g1 g2 pl pr c tr Hind_l Hind_r). *)

    (*     - (* cons_pat, contxt_term (tail_c tl c) *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
          
    (*       assert(Hind_l: P (g1, (tl, (pl, g1)))). *)
    (*       {rewrite Heq_tup1 in ind_princ'. *)
    (*        apply (ind_princ' (g1, (tl, (pl, g1))) *)
    (*                 (matching_tuple_order_input_cons *)
    (*                    g1 tl (ctxt (rc tl c)) (pl, g1) *)
    (*                    (cp pl pr, g2) *)
    (*                    (input_cons_evolution_tail_c_l tl c))). *)
    (*       } *)

    (*       assert(Hind_r: P (g1, (ctxt c, (list_pat_c pr, g1)))). *)
    (*       {rewrite Heq_tup1 in ind_princ'. *)
    (*        apply (ind_princ' (g1, (ctxt c, (list_pat_c pr, g1))) *)
    (*                 (matching_tuple_order_input_cons  *)
    (*                    g1 (ctxt c) *)
    (*                    (ctxt (rc tl c)) *)
    (*                    (list_pat_c pr, g1) *)
    (*                    (cp pl pr, g2) *)
    (*                    (input_cons_evolution_tail_c_r tl c))). *)
    (*       } *)
    (*       apply (fourth_eq_contxt_term_r g1 g2 pl pr tl c Hind_l Hind_r). *)
    (*     - (* name_pat *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
          
    (*       assert(Hind: P (g1, (t, (p, g2)))). *)
    (*       {rewrite Heq_tup1 in ind_princ'. *)
    (*        apply (ind_princ' (g1, (t, (p, g2))) *)
    (*                 (matching_tuple_order_pat_evol *)
    (*                    g1 t (p, g2) (name x p, g2) *)
    (*                    (pat_grammar_evolution_name g2 p x))). *)
    (*       } *)
    (*       apply (sixth_eq g1 g2 x p t Hind). *)
    (*     - (* nt *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
          
    (*       assert(Hnt:  *)
    (*               forall (p : pat) *)
    (*                 (proof : prod_in_g (n, p) g2), *)
    (*                 P (g1, (t, (p, remove_prod (n, p) g2 proof)))). *)
    (*       {rewrite Heq_tup1 in ind_princ'. *)
    (*        intros p' Hprod_in. *)
    (*        assert(Hrel: *)
    (*                matching_tuple_order *)
    (*                  (g1, (t, (p', remove_prod (n, p') g2 Hprod_in))) *)
    (*                  (g1, (t, (nt n, g2)))). *)
    (*        {assert(Hpat_evol_rel: *)
    (*                 pat_grammar_evolution  *)
    (*                   (p', remove_prod (n, p') g2 Hprod_in)  *)
    (*                   (nt n, g2)). *)
    (*         {apply (pat_grammar_evolution_nt g2 p' n Hprod_in). *)
    (*         } *)
            
    (*         apply (matching_tuple_order_pat_evol *)
    (*                  g1 t (p', remove_prod (n, p') g2 Hprod_in)  *)
    (*                  (nt n, g2) Hpat_evol_rel). *)
    (*        } *)
           
    (*        apply (ind_princ' (g1, (t, (p', remove_prod (n, p') g2 Hprod_in))) *)
    (*                 Hrel). *)
    (*       } *)
          
    (*       apply (seventh_eq g1 g2 n t Hnt). *)
    (*     - (* inhole_pat *) *)
    (*       reconstruct_tuple tup1 eqp Heq_tup1. *)
    (*       rewrite Heq_tup1. *)
    (*       rewrite Heq_tup1 in ind_princ'. *)

    (*       assert(Hind: P (g1, (t, (pc, g2)))). *)
    (*       {assert(matching_tuple_order *)
    (*                 (g1, (t, (pc, g2))) *)
    (*                 (g1, (t, (inhole pc ph, g2)))) *)
    (*           as Hrel. *)
    (*        {apply (matching_tuple_order_pat_evol  *)
    (*                  g1 t (pc, g2) (inhole pc ph, g2) *)
    (*                  (pat_grammar_evolution_inhole_left g2 pc ph)). *)
    (*        } *)
           
    (*        apply (ind_princ' (g1, (t, (pc, g2))) Hrel). *)
    (*       } *)
          
    (*       destruct (pat_gen_hole_dec (pc, g2)) as [Hgen_hole | Hngen_hole]. *)
    (*       + (* pat_gen_hole (pc, g2) *) *)
    (*         assert(Hind_ph: P (g1, (t, (ph, g2)))). *)
    (*         {assert(matching_tuple_order  *)
    (*                   (g1, (t, (ph, g2))) *)
    (*                   (g1, (t, (inhole pc ph, g2)))) *)
    (*             as Hrel. *)
    (*          {apply (matching_tuple_order_pat_evol g1  *)
    (*                    t (ph, g2) (inhole pc ph, g2) *)
    (*                    (pat_grammar_evolution_inhole_right g2 pc ph)). *)
    (*          } *)
             
    (*          apply (ind_princ' (g1, (t, (ph, g2))) Hrel). *)
    (*         } *)

    (*         apply (fifth_eq_noinp_cons g1 g2 pc ph t Hind Hgen_hole Hind_ph). *)

    (*       + (* ~ pat_gen_hole (pc, g2) *) *)
    (*         assert(forall tc : term, subterm_rel tc t -> P (g1, (tc, (ph, g1)))) *)
    (*           as Hph_P. *)
    (*         {intros tc Hsubterm. *)
    (*          assert(matching_tuple_order  *)
    (*                   (g1, (tc, (ph, g1))) *)
    (*                   (g1, (t, (inhole pc ph, g2)))) *)
    (*            as Hm_rel. *)
    (*          {apply (matching_tuple_order_input_cons *)
    (*                    g1 tc t (ph, g1) (inhole pc ph, g2) *)
    (*                    (input_cons_evolution_hole_r t tc Hsubterm)). *)
    (*          } *)
    (*          apply (ind_princ' (g1, (tc, (ph, g1))) Hm_rel). *)
    (*         } *)

    (*         apply (fifth_eq_inp_cons g1 g2 pc ph t Hind Hngen_hole Hph_P). *)
    (*   Defined. *)
      
    (* End MrelTupIndPrinc. *)
    
  End WfRel.
