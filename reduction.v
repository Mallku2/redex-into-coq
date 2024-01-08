Require Import
        match_spec_orig
        (* matches *)
        match_impl.

(* semantics of a reduction step (fig. 11) *)
Module Reduction (pt : PatTermsSymb).
  Include pt.

  Module MatchingSpecOrig := MatchingSpecOrig pt.
  Import MatchingSpecOrig.
  Import MatchSpecLemmas.
  Import MatchImplLemmas.
  Import MatchingSpec.
  Import Matching.
  Import MatchTads.
  Import WfRel.
  Import GrammarLists.

  (* language of templates of right-hand side of the reduction rules *)
  Inductive temp : Set :=
  | lit_temp : lit -> temp
  | hole_temp : temp
  | var_temp : var -> temp
  | app_temp : (term -> term) -> temp -> temp
  | inhole_temp : temp -> temp -> temp
  (* there is no need to include the notion of lists of terms (as list_term), *)
  (* since the actual instance of the cons_temp template is done with the *)
  (* help of join *)
  | cons_temp : temp -> temp -> temp.

  (* plug into a context, definition from fig. 11 *)
  (* plug for contexts *)
  Fixpoint plug_contxt_in_contxt (c1 c2 : contxt) : contxt := 
    match c1 with
    | hole_contxt_c   => c2
    | list_contxt_c l => list_contxt_c (plug_contxt_in_list_contxt l c2)
    end

  with plug_contxt_in_list_contxt (l : list_contxt) (c : contxt) : list_contxt :=
         match l with
         | hd_contxt c1' t   => hd_contxt (plug_contxt_in_contxt c1' c) t
         | tail_contxt t c1' => tail_contxt t (plug_contxt_in_list_contxt c1' c)
         end.

  (* original plug function *)
  (* TODO: original definition of plug does not preserve "contexts as terms"    
     while the grammar does allow them *)
  Fixpoint plug (c : contxt) (t : term) : term :=
    match c with
    | hole_contxt_c   => t
    | list_contxt_c l => 
        match l with
        | hd_contxt c' t' =>   
            match t with
            | contxt_term c'' =>
                (* plugin a context into a context produces a context *)
                contxt_term (hd_c (plug_contxt_in_contxt c' c'') t')
            | _               =>
                (* plugin a term into a context produces a term *)
                ct (plug c' t) t'
            end
        | tail_contxt t' c' =>
            match t with
            | contxt_term c'' =>
                (* plugin a context into a context produces a new context *)
                contxt_term (tail_c t' (plug_contxt_in_list_contxt c' c''))
            | _            =>
                (* plugin a term into a context produces a term *)
                ct t' (plug_list_contxt c' t)
            end
        end
    end

  with plug_list_contxt (l : list_contxt) (t : term) : list_term :=
    match l with
    | hd_contxt c' t'   => cons_term_c (plug c' t) t'
    | tail_contxt t' c' => cons_term_c t (plug_list_contxt c' t)
    end.
  
  (* no-ctxts property from fig. 11 *)
  Inductive no_ctxts : term -> Prop :=
  | lit_no_ctxts : forall l : lit, no_ctxts (lit_term l)
  | cons_nt_ctxts : forall l, no_ctxts_list l -> no_ctxts (list_term_c l)

  with no_ctxts_list : list_term -> Prop :=
  | nil_no_ctxts_list  : no_ctxts_list nil_term_c
  | cons_no_ctxts_list : forall t l, no_ctxts t      ->
                                no_ctxts_list l ->
                                no_ctxts_list (cons_term_c t l).

  (* to compute proofs of no_ctxts *)
  Fixpoint no_ctxts_dec (t : term) : option (no_ctxts t) :=
    match t with
    | lit_term l    => Some (lit_no_ctxts l)
    | list_term_c l =>
        match no_ctxts_list_dec l with
        | Some proof => Some (cons_nt_ctxts l proof)
        | None       => None
        end
    | _             => None
    end

  with  no_ctxts_list_dec (l : list_term) : option (no_ctxts_list l) :=
          match l with
          | nil_term_c      => Some nil_no_ctxts_list
          | cons_term_c t l =>
              match no_ctxts_dec t, no_ctxts_list_dec l with
              | Some proof_t, Some proof_l => 
                  Some (cons_no_ctxts_list t l proof_t proof_l)
              | _,_                        => None
              end
          end.
    
  (* implements join, fig. 11 *)
  Definition join (t1 t2 : term) : term :=
    match t1, t2 with
    | contxt_term c, _ =>
        match no_ctxts_dec t2 as p return no_ctxts_dec t2 = p -> term with
        | Some proof => 
            fun eqp : no_ctxts_dec t2 = Some proof =>
              match t2 as t2' return t2 = t2' -> term with
              | lit_term _    => 
                  fun _ : _ =>
                    contxt_term (hd_c c (cons_term_c t2 nil_term_c))
              | list_term_c l => 
                  fun _ : _ =>
                    contxt_term (hd_c c l)
              | contxt_term c' =>
                  fun eqp_t2 : t2 = contxt_term c' => 
                    (* impossible case, we return some arbitrary term *)
                    list_term_c nil_term_c
              end eq_refl
        | None      =>
            fun eqp : no_ctxts_dec t2 = None =>
              match t2 as t2' return t2 = t2' -> term with
              | lit_term l    => 
                  fun eqp_t2 : t2 = lit_term l => 
                    (* impossible case, we return some arbitrary term *)
                    list_term_c nil_term_c

              | list_term_c l => 
                  fun _ : _                    => 
                    list_term_c (cons_term_c t1 l)

              | contxt_term c =>
                  fun _ : _                    => 
                    list_term_c (cons_term_c t1 (cons_term_c t2 nil_term_c))

              end eq_refl

        end eq_refl

    | t', _ =>
        match no_ctxts_dec t' with
        | Some proof => 
            match t2 with
            | lit_term _    => ct t1 (cons_term_c t2 nil_term_c)
            | list_term_c l => ct t1 l
            | contxt_term c =>
                match c with
                | hole_contxt_c   => 
                    contxt_term (tail_c t1 (hd_contxt hole_contxt_c nil_term_c))
                | list_contxt_c l =>
                    contxt_term (tail_c t1 l)
                end
            end
        | None       => ct t1 (cons_term_c t2 nil_term_c)
        end
    end.

  (* instantiates a rhs template of a rule, given a set of bindings;
     fig. 11 *)
  Fixpoint inst (r : temp) (b : bindings) : option term :=
    match r with
    | lit_temp l        => Some (lit_term l)
    | hole_temp         => Some (contxt_term hole_contxt_c)
    | var_temp x        => bindings_app b x
    | inhole_temp r1 r2 =>
      match inst r1 b with
      | Some t =>
        match t with
        (* TODO: how to guarantee that r1 generates just a context? *)
        | contxt_term c =>
          match inst r2 b with
          | Some t' => Some (plug c t')
          | None    => None
          end
        | _             => None
        end
      | None   => None
      end
    | cons_temp r1 r2  =>
      match inst r1 b, inst r2 b with
      | Some t1, Some t2 => Some (join t1 t2)
      | _,_              => None
      end
    | app_temp f r'    =>
      match inst r' b with
      | Some t => Some (f t)
      | None   => None
      end
    end.

  (* definition of semantics relation *)
  Definition sem_rel := list (pat * temp).

  (* instantiates a given template with every bindings from a provided 
     list of  bindings  *)
  Fixpoint inst_bindings (r : temp) (binds : list bindings) :
    list (option term) :=
    match binds with
    | nil         => nil
    | bs :: binds' => (inst r bs) :: (inst_bindings r binds')
    end.
      
  (* applies every rule from rel whose left-hand side pat matches against
     t *)    
  Fixpoint apply_reduction (g : grammar) (t : term) (rel : sem_rel)
    : list (option term) :=
    match rel with
    | nil => nil
    | (p, r) :: rel' => inst_bindings r (matches g p t) ++ apply_reduction g t rel'
    end.

  (* formal system to prove judgments about a single reduction rule *)
  Reserved Notation "G ⊢ t / p -> t' / r" (at level 0, t at next level, 
                                            p at next level, t' at next level, 
                                            r at next level).

  Inductive reduction_spec (g : grammar) : term -> pat -> term -> temp -> Prop :=
  | intro_reduction_spec : forall t p b t' r,
      MatchingSpecOrig.match_spec g t p b -> Some t' = inst r b -> g ⊢ t / p -> t' / r
  where "g ⊢ t / p -> t' / r" := (reduction_spec g t p t' r).

End Reduction.
