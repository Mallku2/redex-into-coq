(* TODO: put all the required modules in a single base file 
         as Require Exports *)
Require Import
  (* dependent induction *)
  Program.Equality
  (* to solve some inequalities between size of terms *)
  Lia
  (* to build-up our theory of decidability of predicates over pats and terms *)
  stdpp.base stdpp.finite.

Require Import 
        lib_ext.PeanoNatExt
        lib_ext.tactics.


(* hints db *)
Create HintDb terms_pats_db.

(* one component of the semantics for "reduction semantics": a template for the 
   language of terms, contexts and patterns (fig. 8). *)

Module Type Symbols.
  (* literals for both, pats and terms *)
  Parameter lit: Set.
  (* names in name_pat *)
  Parameter var: Set.
  (* representation of the non-terms of a given grammar, for patterns nt *)
  Parameter nonterm: Set.

  (* some assumptions to ease the reasoning about decidability *)
  Parameter nonterm_eq_dec : EqDecision nonterm.
  #[global] Hint Resolve nonterm_eq_dec : terms_pats_db.
  Parameter var_eq_dec : EqDecision var.
  #[global] Hint Resolve var_eq_dec : terms_pats_db.
  Parameter lit_eq_dec : EqDecision lit.
  #[global] Hint Resolve lit_eq_dec : terms_pats_db.

   (* lits and nonterms are finite *)
  Parameter lit_finite : Finite (EqDecision0 := lit_eq_dec) lit.
  #[global] Hint Resolve lit_finite : terms_pats_db.
  Parameter nonterm_finite : Finite (EqDecision0 := nonterm_eq_dec) nonterm.
  #[global] Hint Resolve nonterm_finite : terms_pats_db.

End Symbols.

(* from a given set of symbols, we instantiate a language of terms and
   patterns *)
Module Type PatTerms (S : Symbols).
  
  Import S.

  Inductive term : Set :=
  | lit_term    : lit -> term
  | list_term_c : list_term -> term
  | contxt_term : contxt -> term

  with list_term : Set :=
  | nil_term_c  : list_term
  | cons_term_c : term -> list_term -> list_term

  with contxt : Set :=
  | hole_contxt_c : contxt
  | list_contxt_c : list_contxt -> contxt

  (* hd_contxt and tail_contxt point into a position of a list of terms  *)
  with list_contxt : Set :=
  | hd_contxt   : contxt -> list_term -> list_contxt
  | tail_contxt : term -> list_contxt -> list_contxt.
  
  Inductive pat : Set :=
  | lit_pat    : lit -> pat
  | hole_pat   : pat
  | list_pat_c : list_pat -> pat
  | name_pat   : var -> pat -> pat
  | nt_pat     : nonterm -> pat
  | inhole_pat : pat -> pat -> pat

  with list_pat : Set :=
  | nil_pat_c  : list_pat
  | cons_pat_c : pat -> list_pat -> list_pat.

  #[global] Hint Constructors term : terms_pats_db.
  #[global] Hint Constructors pat : terms_pats_db.

  (* mutual induction principles *)
  Scheme term_mut_ind := Induction for term Sort Prop
      with list_term_mut_ind := Induction for list_term Sort Prop
      with contxt_mut_ind := Induction for contxt Sort Prop
      with list_contxt_mut_ind := Induction for list_contxt Sort Prop.
  
  Scheme term_mut_rec := Induction for term Sort Set
      with list_term_mut_rec := Induction for list_term Sort Set
      with contxt_mut_rec := Induction for contxt Sort Set
      with list_contxt_mut_rec := Induction for list_contxt Sort Set.

  Scheme term_mut_rect := Induction for term Sort Type
      with list_term_mut_rect := Induction for list_term Sort Type
      with contxt_mut_rect := Induction for contxt Sort Type
      with list_contxt_mut_rect := Induction for list_contxt Sort Type.
 
  Scheme pat_mut_ind := Induction for pat Sort Prop
      with list_pat_mut_ind := Induction for list_pat Sort Prop.

  Scheme pat_mut_rec := Induction for pat Sort Set
      with list_pat_mut_rec := Induction for list_pat Sort Set.

  Scheme pat_mut_rect := Induction for pat Sort Type
      with list_pat_mut_rect := Induction for list_pat Sort Type.

  (* notations *)
  Notation "[ ]" := hole_pat.

  Notation "'lp' x" := (lit_pat x)
                         (at level 50).
  
  Notation "'cp' p1 p2" := (list_pat_c (cons_pat_c p1 p2))
                             (at level 50, p1 at level 9).
  
  Notation "C [ e ]" := (inhole_pat C e) (at level 50).
  
  (* x at a lower level so the parser does not consider "x p" as
       function application *)
  Notation "p '__' x" := (name_pat x p)
                           (at level 50).

  Notation "'nt' x" := (nt_pat x) (at level 50).

  (* terms *)

  (* to avoid clash with lt rel *)
  Notation "'lter' x" := (lit_term x)
                           (at level 50).
  
  Notation "'ct' t1 t2 " := (list_term_c (cons_term_c t1 t2))
                              (at level 50, t1 at level 9).
  
  Notation "'hole'" := (contxt_term hole_contxt_c).

  Notation "'ctxt' C" := (contxt_term C)
                           (at level 50).

  Notation "'hd_c' C t" := (list_contxt_c (hd_contxt C t))
                           (at level 50, C at level 9).

  Notation "'tail_c' t C" := (list_contxt_c (tail_contxt t C))
                           (at level 50, t at level 9).

  Notation "'hole__t'" := hole_contxt_c (at level 0).
  Notation "'hd__t'" := hd_contxt (at level 0).
  Notation "'tail__t'" := tail_contxt (at level 0).
  Notation "'hole__p'" := hole_pat (at level 0).
  Notation "'lit__t'" := lit_term (at level 0).
  Notation "'lit__p'" := lit_pat (at level 0).
  Notation "'cons__t'" := list_term (at level 0).
  Notation "'cons__p'" := list_pat (at level 0).
  Notation "'nt'" := nt_pat (at level 0).
  Notation "'name'" := name_pat (at level 0).
  Notation "'inhole'" := inhole_pat (at level 0).
  
  Coercion contxt_term : contxt    >-> term.
  Coercion list_term_c : list_term >-> term.
  Coercion lit_term    : lit       >-> term.
  Coercion list_pat_c  : list_pat  >-> pat.
  Coercion lit_pat     : lit       >-> pat.
  
  (* we need a coercion from list_contxt into list_terms 
     NOTE: we do not declare it as such, to avoid ambiguities *)
  Fixpoint list_contxt_2_list_term (l : list_contxt) : list_term :=
    match l with
    | hd_contxt c l'     => cons_term_c (contxt_term c) l'
    | tail_contxt t lc'  => cons_term_c t (list_contxt_2_list_term lc')
    end.

  Coercion list_contxt_c : list_contxt >-> contxt.
  
  Section TermPatLangProps.
    (* **************************************** *)
    (* minimum theory about pattern and terms *)
    (* **************************************** *)
    
    (* size function, to obtain a better (more general) induction principle over 
     terms

     it counts only term constructors present in the original language
     of terms (lits, nil, cons, l_contxt and r_contxt)
     *)
    Fixpoint size_term (t : term) : nat :=
      match t with
      | lit_term l    => 1
      | list_term_c l => size_list_term l
      | contxt_term c => size_contxt c
      end

    with size_list_term (l : list_term) : nat :=
           match l with
           | nil_term_c      => 1
           | cons_term_c t l => 1 + (size_term t) + (size_list_term l)
           end               

    with size_contxt (c : contxt) : nat :=
           match c with
           | hole_contxt_c   => 1
           | list_contxt_c l => size_list_contxt l
           end
    with size_list_contxt (l : list_contxt) : nat :=
           match l with
           | hd_contxt c t => 1 + (size_contxt c) + (size_list_term t)
           | tail_contxt t lc' => 1 + (size_term t) + (size_list_contxt lc')
           end.

    (* some properties of size_term *)
    
    (* useful for discarding bogus cases *)
    Lemma size_term_neq_0 : forall (t : term), size_term t <> 0.
    Proof.
      intro t.
      destruct t;
        solve [easy
              | app_destruct list_term;
                easy
              | app_destruct contxt;
                solve[easy
                     | app_destruct list_contxt;
                       easy]].
    Defined.

    Hint Resolve size_term_neq_0 : terms_pats_db.

    Lemma size_contxt_neq_0 : forall (c : contxt), size_contxt c <> 0.
    Proof.
      intro c.
      destruct c;
        solve[easy
             | app_destruct list_contxt;
               easy].
    Defined.

    Hint Resolve size_contxt_neq_0 : terms_pats_db.

    Lemma size_list_term_neq_0 : forall (l : list_term), size_list_term l <> 0.
    Proof.
      intro t.
      destruct t;
        easy.
    Defined.
    
    Hint Immediate size_list_term_neq_0 : terms_pats_db.

    Lemma size_term_ge_1 : forall (t : term), 1 <= size_term t.
    Proof.
      intro.
      apply (gt_1_trans (size_term t)
                        (size_term_neq_0 t)).
    Defined.

    Hint Immediate size_term_ge_1 : terms_pats_db.

    Lemma size_list_term_ge_1 : forall (l : list_term), 1 <= size_list_term l.
    Proof.
      intro.
      apply (gt_1_trans (size_list_term l)
                        (size_list_term_neq_0 l)).
    Defined.

    Hint Resolve size_list_term_ge_1 : terms_pats_db.

    Lemma size_contxt_ge_1 : forall (c : contxt), 1 <= size_contxt c.
    Proof.
      intro c.
      apply (gt_1_trans (size_contxt c)
                        (size_contxt_neq_0 c)).
    Defined.

    Hint Resolve size_contxt_ge_1 : terms_pats_db.

    Lemma size_term_lit_contxt_1 : 
      forall (t : term), size_term t = 1 -> 
                    (exists l, t = lit_term l) \/ t = contxt_term hole_contxt_c
                    \/ t = list_term_c nil_term_c.
    
    Proof.
      intros t H.

      let tac := inversion H;
                 generalize size_list_term_neq_0;
                 generalize sum_zero;
                 generalize size_term_neq_0;
                 firstorder
      in
      destruct t;
        solve[eauto
             | app_destruct list_term;
               solve [ auto
                     | tac]
             | app_destruct contxt;
               solve [ auto
                     | app_destruct list_contxt;
                       tac]
             ].
    Defined.

    Hint Resolve size_term_lit_contxt_1 : terms_pats_db.

    Lemma size_term_lt_1 : 
      forall (t : term), 1 < size_term t -> 
                    (exists tl tr, t = list_term_c (cons_term_c tl tr)) \/ 
                    (exists cl tr, t = contxt_term (hd_contxt cl tr)) \/
                    (exists tl cr, t = contxt_term (tail_contxt tl cr)).
    
    Proof.
      intros t H.
      (* simple iteration through possible t / 1 < size_term t *)
      destruct t.
      - (* lit *)
        inversion H.
        easy.
      - (* list term *)
        app_destruct list_term.
        + (* nil *)
          inversion H;
            easy.
        + (* cons *)
          eauto.
      - (* contxt *)
        app_destruct contxt.
        + (* hole *)
          inversion H;
            easy.
        + (* list contxt *)
          app_destruct list_contxt;
            inversion H;
              eauto.
    Defined.

    Hint Resolve size_term_lt_1 : terms_pats_db.

    Lemma size_list_term_contxt_eq : 
      forall l : list_contxt, size_list_contxt l = size_list_term (list_contxt_2_list_term l).
    Proof.
      apply (induction_ltof1 _ size_list_contxt).
      intros l IH.
      destruct l.
      - (* hd contxt *)
        reflexivity.
      - (* tail contxt *)
        simpl.
        rewrite (IH _).
        + (* goal *)
          reflexivity.
        + (* size ltof *)
          unfold ltof.
          simpl.
          lia.
    Qed.
          

  End TermPatLangProps.
  
  (* *********************** *)
  (* subterm rel. *)
  (* *********************** *)
  Section SubtermRel.
    (* "immediate" subterms, useful to formalize some statements about terms *)
    Definition subterms (t t1 t2 : term) :=
      (exists l : list_term, t2 = list_term_c l /\ t = list_term_c (cons_term_c t1 l)) \/
        (exists (c : contxt) (l : list_term), 
            t1 = contxt_term c /\ t2 = list_term_c l /\
            t = contxt_term (hd_contxt c l)) \/
        exists cl, t2 = contxt_term (list_contxt_c cl) /\ 
                t = contxt_term (tail_contxt t1 cl).
    
    Inductive subterm_rel : term -> term -> Prop :=
    (* term *)
    | subterm_cons_l : forall tl tr,
        subterm_rel tl (list_term_c (cons_term_c tl tr))
    | subterm_cons_r : forall tl tr,
        subterm_rel (list_term_c tr) (list_term_c (cons_term_c tl tr))
    (* context *)
    | subterm_hd_contxt_l : forall c tr,
        subterm_rel (contxt_term c) (contxt_term (hd_contxt c tr))
    | subterm_hd_contxt_r : forall c tr,
        subterm_rel (list_term_c tr) (contxt_term (hd_contxt c tr))
    | subterm_tail_contxt_l : forall tl c,
        subterm_rel tl (contxt_term (tail_contxt tl c))
    | subterm_tail_contxt_r : forall tl c,
        subterm_rel (contxt_term (list_contxt_c c)) (contxt_term (tail_contxt tl c))
    (* transitivity *)
    | subterm_trans : forall t1 t2 t3,
        subterm_rel t1 t2 -> subterm_rel t2 t3 -> subterm_rel t1 t3.

    Hint Constructors subterm_rel : terms_pats_db.
    (* ********************* *)
    (* Well-foundedness *)
    (* ********************* *)
    Lemma subterm_rel_decre : forall t1 t2,
        subterm_rel t1 t2 -> size_term t1 < size_term t2.
    Proof.
      intros.
      dependent induction H.
      - (* t2 = ct, t1 = left sub-pat*)
        simpl.
        lia.
      - (* t2 = ct, t1 = right sub-pat*)
        simpl.
        lia.
      - (* t2 = hd_c, t1 = left sub-pat*)
        simpl.
        lia.
      - (* t2 = hd_c, t1 = right sub-pat*)
        simpl.
        lia.
      - (* t2 = tail_c, t1 = left sub-pat*)
        simpl.
        lia.
      - (* t2 = tail_c, t1 = right sub-pat*)
        simpl.
        lia.
      - (* trans. step *)
        lia.
    Defined.

    Lemma subterm_rel_well_founded : well_founded subterm_rel.
    Proof.
      apply (well_founded_lt_compat _ size_term).
      apply subterm_rel_decre.
    Qed.
    
    Lemma subterm_rel_non_reflex : forall t, not (subterm_rel t t).
    Proof.
      intro t.
      intro H.
      assert(size_term t < size_term t). 
      {apply subterm_rel_decre.
       assumption.
      }
      assert(not (size_term t < size_term t)).
      {apply PeanoNat.Nat.lt_irrefl.
      }
      contradiction.
    Defined.

    Definition lt_term (t2 t1 : term) : Prop := 
      (size_term t2) < (size_term t1).

    Lemma lt_term_acc_transparent : forall (t : term), Acc lt_term t.
    Proof.
      intro.
      unfold lt_term.
      constructor.
      induction (size_term t).
      + intros.
        inversion H.
      + intros.
        constructor.
        intros.
        inversion H.
      - rewrite H2 in H0.
        apply (IHn y0 H0).
      - assert(size_term y0 < n).
        {assert(size_term y < n).
         {exact H2.
         }
         apply (lt_trans_transp (size_term y0) (size_term y) n).
         exact H0.
         exact H3.
        }
        apply (IHn y0 H3).
    Defined.

    Lemma wf_lt_term_transparent : well_founded lt_term.
    Proof.
      constructor.
      intros.
      apply lt_term_acc_transparent.
    Defined.
    
    (* induction principle for reasoning over < *)
    Section LtTermIndPrinc.  
      Variable P : term -> Prop.
      
      (* TODO: how to get rid of this hypothesis? *)
      Hypothesis bogus_case : forall (t : term), size_term t = 0 -> P t.
      Hypothesis base_case : forall (t : term), size_term t = 1 -> P t.
      Hypothesis ind_case : forall (t1 : term), 1 < size_term t1 -> 
                                           (forall (t2 : term), lt_term t2 t1 -> P t2) -> 
                                           P t1.
      
      Definition lt_term_ind_princ (t : term) : P t.
        refine 
          (Fix 
             wf_lt_term_transparent
             (* dependent range type of the function that we are building *)
             (fun t : term  => P t) 
             (* The function body *)
             (fun (t1 : term)
                (lt_term_ind_princ' : forall (t2 : term),
                    lt_term t2 t1 -> P t2) =>
                match (size_term t1) as st1 
                      return (size_term t1) = st1 -> P t1 with
                | 0 =>
                  fun eqp : (size_term t1) = 0 => (bogus_case t1 eqp)
                | 1 => 
                  fun eqp : (size_term t1) = 1 => (base_case t1 eqp)
                | S (S n) => 
                  fun eqp : (size_term t1) = S (S n) => 
                    (ind_case t1 _ lt_term_ind_princ')
                end eq_refl) t).    
        - rewrite eqp.
          apply (lt_n_S_trans 0 (S n) (lt_0_succ_trans n)).
      Defined.
    End LtTermIndPrinc.

    (* some lemmas about topology of subterm_rel *)
    Lemma subterm_rel_lit_min : forall t1 t2, 
        subterm_rel t1 t2 -> not (exists l, t2 = lit_term l).
    Proof.
      intros t1 t2 H.
      induction H;
        solve [intro H;
               inversion H as [l H'];
               inversion H'
              | intro;
                contradiction].
    Defined.

    Lemma subterm_rel_hole_min : forall t1 t2, 
        subterm_rel t1 t2 -> t2 <> contxt_term hole_contxt_c.
    Proof.
      intros t1 t2 H.
      induction H;
        solve [intro H;
               inversion H
              | assumption].
    Defined.

    Lemma subterm_rel_nil_min : forall t1 t2, 
        subterm_rel t1 t2 -> t2 <> list_term_c nil_term_c.
    Proof.
      intros t1 t2 H.
      induction H;
        solve [intro H;
               inversion H
              | assumption].
    Defined.

    (* some lemmas characterizing subterm_rel *)

    Lemma subterm_rel_incl_cons :
      forall t1 t2 t3,
        subterm_rel t1 (list_term_c (cons_term_c t2 t3)) ->
        (t1 = t2 \/ subterm_rel t1 t2)
        \/
        (t1 = list_term_c t3 \/ subterm_rel t1 (list_term_c t3)).
    Proof.
      intros t1 t2 t3 Hsub.
      dependent induction Hsub;
        solve [tauto
              | assert(Hinst_IH : (t0 = t2 \/ subterm_rel t0 t2) \/
                                  (t0 = t3 \/ subterm_rel t0 t3));
                [eauto with terms_pats_db
                |];
                inversion Hinst_IH as [H | H];
                solve [inversion H;
                       [subst;
                        tauto
                       | eauto with terms_pats_db]
                      ]].
    Qed.

  End SubtermRel.

End PatTerms.

Module Type PatTermsSymb := Symbols <+ PatTerms.

Module PatTermsFunc (S : Symbols).
  Include S.
  Include PatTerms.
End PatTermsFunc.
