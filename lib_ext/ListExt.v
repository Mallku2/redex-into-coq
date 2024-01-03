Require Import
        Lists.List
        Lia.

Require Import 
        lib_ext.PeanoNatExt.
        (* lib_ext.LibTactics. *)
        

Open Scope list_scope. 

(* some transparent redefinitions of Coq's list library services  *)

Section ListLibTrans.
  (* transparent redefinition of Coq.Lists.List.in_eq *)
  Theorem in_eq_trans : forall (A : Type) (a:A) (l:list A), In a (a :: l).
  Proof.
    simpl; auto.
  Defined.
  
  (* transparent redefinition of Coq.Lists.List.not_in_cons *)
  Lemma not_in_cons_trans (A : Type) (x a : A) (l : list A) :
    ~ In x (a::l) <-> x<>a /\ ~ In x l.
  Proof.
    simpl. intuition.
  Defined.

  (* transparent redefinition of Coq.Lists.List.in_inv *)
  Lemma in_inv_trans : forall (A : Type) (a b : A) (l : list A),
      In b (a :: l) -> a = b \/ In b l.
  Proof.
    intros.
    inversion H.
    + left.
      exact H0.
    + right.
      exact H0.
  Defined.

  (* transparent redefinition of Coq.Lists.List.in_cons *)
  Lemma in_cons_trans : forall (A : Type) (a b : A) (l : list A),
      In b l -> In b (a :: l).
Proof.
  intros.
  unfold In.
  right.
  exact H.
Defined.

(* simple function that removes repeated elements in a given list
   easy way of obtaining a NoDup property for a list *)

End ListLibTrans.

(* some extensions to the list's library *)
Section ListLibExt.
  
  Lemma in_inv_iff : forall (A : Type) (a b:A) (l:list A),
    In b (a :: l) <-> a = b \/ In b l.
  Proof.
    intros A a b.
    split.
    + apply in_inv.
    + induction l.
      - simpl.
        intro H.
        exact H.
      - intro H.
      inversion H as [Heq | Hin].
      ++ rewrite Heq.
         apply in_eq.
      ++ simpl.
         right.
         inversion Hin as [Heq' | Hin'].
         -- left.
            exact Heq'.
         -- right.
            exact Hin'.
  Qed.
         
  (* transparent filter to remove repeated elements from a list *)
  Fixpoint remove_rep_elem (A : Type) 
           (eq_dec : forall (x1 x2 : A), {x1 = x2} + {x1 <> x2})
           (l : list A) : list A :=
    match l with
    | nil         => nil
    | x :: tail =>
      (* check if x is repeated *)
      (* in_dec is transparent *)
      match (in_dec eq_dec x tail) with
      | left _  => remove_rep_elem A eq_dec tail (* {In x tail} *)
      | right _ => x :: remove_rep_elem A eq_dec tail
      end
    end.

  (* some lemmas characterizing remove_rep_elem *)

  (* remove_rep_elem does not add elements *)
  Lemma remove_rep_elem_no_add :
    forall (A : Type) 
      (eq_dec : forall (x1 x2 : A), {x1 = x2} + {x1 <> x2})
      (l : list A)
      (x : A)
      (not_in : not (In x l)),
      not (In x (remove_rep_elem A eq_dec l)).
  Proof.
    intros A eq_dec l x Hnot_in.


    induction l as [| hd tl IH].
    - (* l = nil *)
      remember (remove_rep_elem A eq_dec nil) as l_not_rep eqn:Heq_l_not_rep.
      simpl in Heq_l_not_rep.
      rewrite Heq_l_not_rep.
      exact Hnot_in.
    - (* l = hd :: tl *)
      simpl in Hnot_in.
      (* TODO: remove this *)
      apply Decidable.not_or in Hnot_in.
      inversion Hnot_in as [Hneq_hd Hnin_tl].
      intro Hnin.
      simpl in Hnin.

      destruct (in_dec eq_dec hd tl) as [Hin_hd_tl | Hnin_hd_tl].
      + (* In hd tl *)
        apply IH in Hnin_tl.
        contradiction.
      + (* not In hd tl *)
        simpl in Hnin.
        inversion Hnin as [Heq_x_hd | Hin_tl].
        * (* hd = x *)
          contradiction.
        * (* In x (remove_rep_elem A eq_dec tl) *)
          apply IH in Hnin_tl.
          contradiction.
  Qed.

  (* remove_rep_elem satisfies NoDup *)
  Lemma remove_rep_charact :
    forall (A : Type) (eq_dec : forall (x1 x2 : A), {x1 = x2} + {x1 <> x2})
      (l : list A),
      NoDup (remove_rep_elem A eq_dec l).
  Proof.
    intros A eq_dec l.
    induction l as [| hd tl IH].
    - (* l = nil *)
      simpl.
      apply NoDup_nil.
    - (* l = hd :: tl *)
      assert({In hd tl} + {not (In hd tl)})
        as Hin_dec.
      {apply in_dec.
       exact eq_dec.
      }

      inversion Hin_dec as [Hin | Hnin].
      + (* In hd tl *)
        simpl.
        destruct (in_dec eq_dec hd tl) as [Hin_hd_tl' | Hnin_hd_tl].
        * (* In hd tl *)
          exact IH.
        * (* not In hd tl *)
          contradiction.
      + (* not In hd tl *)
        simpl.
        destruct (in_dec eq_dec hd tl) as [Hin_hd_tl | Hnin_hd_tl'].
        * (* In hd tl *)
          exact IH.
        * (* not In hd tl *)
          apply NoDup_cons.
          -- (* not In hd remove tl *)
             apply remove_rep_elem_no_add.
             exact Hnin_hd_tl'.
          -- (* NoDup remove tl *)
             exact IH.
  Qed.

  (* another way of characterizing remove_rep_elem *)
  Lemma remove_rep_elem_preserves_NoDup :
    forall (A : Type) (eq_dec : forall (x1 x2 : A), {x1 = x2} + {x1 <> x2})
      (l : list A),
      List.NoDup l ->
      (remove_rep_elem A eq_dec l) = l.
  Proof.
    intros A eq_dec l H.

    induction l as [| hd tl IH].
    - (* l = nil *)
      reflexivity.
    - (* l = hd :: tl *)
      inversion H.
      simpl.
      destruct (in_dec eq_dec hd tl) as [Hin_hd_tl | Hnin_hd_tl'].
      + (* In hd tl *)
        contradiction.
      + (* not In hd tl *)
        intuition.
        congruence.
  Qed.

  Lemma remove_rep_elem_preserves_NoDup_list :
    forall (A : Type) (eq_dec : forall (x1 x2 : A), {x1 = x2} + {x1 <> x2})
      (l : list A),
      (remove_rep_elem A eq_dec (remove_rep_elem A eq_dec l)) =
      remove_rep_elem A eq_dec l.
  Proof.
    intros A eq_dec l.

    assert(List.NoDup (remove_rep_elem A eq_dec l))
      as Hnodup.
    {apply remove_rep_charact.
    }

    apply remove_rep_elem_preserves_NoDup.
    exact Hnodup.
  Qed.
  
  (* a missing lemma in Coq's fold library *)
  Lemma fold_left_fapp : forall (A : Type) (l : list (list A))
                           (acc : list A),
      fold_left (app (A := A))
                l acc =
      acc ++ (fold_left (app (A:=A)) l
                        (nil (A := A))).
  Proof.
    intros A.
    induction l.
    + intros acc.
    simpl.
    rewrite <- app_nil_end.
    reflexivity.
    + intros acc.
    simpl.
    assert(fold_left (app (A:= A)) l a =
           a ++ fold_left (app (A:=A)) l nil) as Ha.
    {apply IHl.
    }
    rewrite Ha.
    assert(fold_left (app (A:= A)) l (acc ++ a) =
           (acc ++ a) ++ fold_left (app (A:=A)) l nil) as Hacca.
    {apply IHl.
    }
    rewrite Hacca.
    rewrite app_assoc.
    reflexivity.
  Qed.
    
  (* when equality is decidable, we can get a stronger in_app lemma *)
  Lemma in_app_iff_strong :
    forall (A : Type) l l' (a:A),
      (forall x y:A, {x = y} + {x <> y}) ->
      In a (l ++ l') <-> In a l \/ (not (In a l) /\ In a l').
  Proof.
    intros A l l' a Heq_dec.
    split.
    - (* In a (l ++ l') <-> In a l \/ (not (In a l) /\ In a l') *)
      intro Hin.
      assert({In a l} + {~ In a l})
        as Hin_dec.
      {apply in_dec.
       apply Heq_dec.
      }

      inversion Hin_dec as [Hin_l | Hnin_l].
      + (* In a l *)
        left.
        exact Hin_l.
      + (* not In a l *)
        right.
        split.
        * (* not In a l *)
          exact Hnin_l.
        * (* In a l' *)
          rewrite in_app_iff in Hin.
          inversion Hin as [Ha_in_l | Ha_in_l'].
          -- (* In a l *)
            contradiction.
          -- (* In a l' *)
            exact Ha_in_l'.
    - (* In a l \/ ~ In a l /\ In a l' -> In a (l ++ l') *)
      intro Hin_l_or_l'.
      rewrite in_app_iff.
      inversion Hin_l_or_l' as [Hin_l | Hin_l'].
      + (* In a l *)
        left.
        exact Hin_l.
      + (* In a l' *)
        inversion Hin_l' as [Hnin_l Hin_l''].
        right.
        exact Hin_l''.
  Qed.

  (* removelast actually reduces the length *)
  Lemma removelast_reduce_length : 
    forall (A : Type) (l : list A),
      length l >= 1 ->
      length (removelast l) < length l.
  Proof.
    intros A l.
    induction l as [ | a l'].
    - (* l = nil *)
      intro Hlength.
      simpl in Hlength.
      lia.
    - (* l = cons *)
      intro Hlength.
      unfold removelast.
      fold (removelast l').
      destruct l' as [ | a' l''].
      + simpl.
        lia.
      + remember (removelast (a' :: l'')) as remove eqn:Heq_remove.
        simpl.
        assert(IH_inst : length remove < length (a' :: l'')).
        {assert(Hlength' : length (a' :: l'') >= 1).
         {simpl.
          lia.
         }
         eauto.
        }
        simpl in IH_inst.
        lia.
  Qed.

  Lemma removelast_reduce_length_1 : 
    forall (A : Type) (l : list A),
      length l >= 1 ->
      length (removelast l) = length l - 1.
  Proof.
    intros A l.
    induction l as [ | a l'].
    - (* l = nil *)
      intro Hlength.
      simpl in Hlength.
      lia.
    - (* l = cons *)
      intro Hlength.
      unfold removelast.
      fold (removelast l').
      destruct l' as [ | a' l''].
      + (* nil *)
        simpl.
        lia.
      + (* cons *)
        remember (removelast (a' :: l'')) as remove eqn:Heq_remove.
        simpl.
        assert(Hlen : length (a' :: l'') >= 1).
        {simpl.
         lia.
        }
        
        assert(IH_inst : length remove = length (a' :: l'') - 1).
        {apply IHl'.
         exact Hlen.
        }
        rewrite IH_inst.
        simpl.
        lia.
  Qed.

  Lemma head_dist_concat :
    forall (A : Type) (l1 l2 : list A) (Hl1_nempty : l1 <> nil),
      head (l1 ++ l2) = head l1.
  Proof.
    intros A l1 l2 Hl1_nempty.
    destruct l1 as [ | hdl1 tll1].
    - (* nil *)
      exfalso.
      unfold not in Hl1_nempty.
      apply Hl1_nempty.
      reflexivity.
    - (* cons *)
      reflexivity.
  Qed.

End ListLibExt.
