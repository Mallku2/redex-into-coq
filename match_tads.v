Require Import 
        Lists.List
        Logic.Eqdep
        Logic.Eqdep_dec
        Program.Equality
        (* ltof *)
        Arith.Wf_nat
        (* induction on lexicographic product *)
        Relations.Relation_Operators
        Wellfounded.Lexicographic_Product.

Require Import 
        patterns_terms
        patterns_terms_dec
        lib_ext.ListExt
        (* custom tactics *)
        lib_ext.tactics.

Declare Scope ltac_scope.
(* bindings, decompositions, match sets *)
Module MatchTads(pt: PatTermsSymb).
  Import pt.

  (* import decidability results about pats and terms *)
  Module PatTermsDec := PatTermsDec(pt).
  Import PatTermsDec.

  (* Bindings (fig. 9) *)
  Definition binding := prod var term.
  Definition bindings := list binding.

  Notation "∅" := (@nil binding).

  Lemma binding_eq_dec : forall (b1 b2 : binding), {b1 = b2} + {b1 <> b2}.
  Proof.
    intros.
    destruct b1,b2.
    assert({v = v0} + {v <> v0}).
    {apply var_eq_dec.
    }
    assert({t = t0} + {t <> t0}).
    {apply term_eq_dec.
    }
    inversion H.
    + inversion H0.
    - left.
      rewrite H1.
      rewrite H2.
      reflexivity.
    - right.
      intro.
      inversion H3.
      contradiction.
      + inversion H0.
    - right.
      intro.
      inversion H3.
      contradiction.
    - right.
      intro.
      inversion H3.
      contradiction.
  Defined.

  Lemma bindings_eq_dec : forall (b1 b2 : bindings), {b1 = b2} + {b1 <> b2}.
  Proof.
    intros.
    dependent induction b1.
    + destruct b2.
    - left.
      reflexivity.
    - right.
      intro.
      inversion H.
      + destruct b2.
    - right.
      intro.
      inversion H.
    - assert({b1 = b2} + {b1 <> b2}).
      {apply (IHb1 b2).
      }
      destruct H.
      -- assert (H: {a = b} + {a <> b}).
         {apply binding_eq_dec.
         }
         destruct H.
         ++ left.
            rewrite e.
            rewrite e0.
            reflexivity.
         ++ right.
            intro.
            inversion H.
            contradiction.
      -- right.
         intro.
         inversion H.
         contradiction.
  Defined.

  Definition bindings_dom (b: bindings) : list var :=
    (map (fun b => match b with
                | (v, t) => v
                end)
         b).

  (* for given bindings b, var v, it returns Some term t associated with v in b,
     or None, otherwise *)
  Fixpoint bindings_app (b: bindings) (v: var) : option term :=
    match b with
    | nil => None 
    | ((v', t) :: b') => if var_eq_dec v v' then
                         Some t
                       else
                         bindings_app b' v
    end.

  (* abbv. *)
  Definition rem_rep (b : bindings) := 
    remove_rep_elem (prod var term) binding_eq_dec b.
  
  (* disjoint union of bindings: implements the semantics of the "name" pattern *)
  (* RETURNS:
     Some bindings, if domains of b1 and b2 are disjoint OR the bindings for their 
     common vars.  are the same

     None, otherwise *)

  Fixpoint b_union_lists (b1 b2 : bindings) : (option bindings) :=
    match b1 with
    | nil             =>
      (* ensure NoDup b2 *)
      Some (rem_rep b2)
    | ((v1, t1) :: b1') =>
      (* check if v1 \in dom(b2) *)
      match b_union_lists b1' b2 with
      | None       => None
      | Some binds =>
        match bindings_app binds v1 with
        | None      => Some (rem_rep ((v1, t1) :: binds))
        | Some t1'  =>
          if term_eq_dec t1 t1' then
            Some (rem_rep binds)
          else
            None
        end
      end
    end.

  (* disjoint union of bindings: implements the semantics of the "name" 
     pattern (pag. 6, fig. 9 and 10) *)
  (* PARAMS:
     b1 b2 : option bindings to better support the manipulation of option 
             bindings that are returned from a match
     RETURNS:
     - Some bindings, if domains of b1 and b2 are disjoint OR the bindings for 
     their common vars.  are the same

     - None, otherwise *)
  Definition b_union (b1 b2 : bindings) : (option bindings) :=
    (b_union_lists b1 b2).
  
  Notation "x ⊔ y" := (b_union x y) (at level 0).

  (* decomposition of a term into a context and a term (pag. 6, fig. 9 and 10) *)
  Inductive decom : Set :=
  | empty_d : decom
  | nonempty_d : term -> term -> decom.

  (* TODO: put it into another module *)
  Notation "C [[ e ]]" := (nonempty_d C e) (at level 50).

  Notation "[[ ]]" := empty_d (at level 50).

  (* decomposition of a term into a context and a term, together with evidence
     of the soundness of the decom *)
  (* TODO: put info about the pattern used in the matching *)
  Inductive decom_ev : term -> Set :=
  | empty_d_ev : forall (t : term), decom_ev t 
  | nonempty_d_ev : forall t (c : contxt) subt,
      {subt = t /\ c = hole_contxt_c} + {subterm_rel subt t} -> decom_ev t.

  (* match *)
  (* TODO: cannot do general dependent pattern match on the following def of 
     mtch_ev:  *)
  Inductive mtch_ev : term -> Set :=
  | mtch_pair : forall t, decom_ev t -> bindings -> mtch_ev t.

  Definition mtch_powset_ev (t : term) := list (mtch_ev t).

  (* just decom and bindings, to ease the reading of results *)
  Definition mtch := (prod decom bindings).

  Definition mtch_powset := list mtch.

  (* context_com c1 c2 = c1 ++ c2 (fig. 9) *)
  Fixpoint context_com (c1 c2 : contxt) : contxt :=
    match c1 with
    | hole_contxt_c   => c2
    | list_contxt_c l => list_contxt_c (list_contxt_com l c2)
    end
  with list_contxt_com (l : list_contxt) (c : contxt) : list_contxt :=
         match l with
         | hd_contxt c1' t   => hd_contxt (context_com c1' c) t
         | tail_contxt t c1' => tail_contxt t (list_contxt_com c1' c)
         end.

  (* to clean evidence from a decom_ev *)
  Definition clean_ev_decom (t : term) (dc : decom_ev t) : decom :=
    match dc with
    | empty_d_ev _             => empty_d
    | nonempty_d_ev _ c subt _ => nonempty_d (contxt_term c) subt
    end.

End MatchTads.
