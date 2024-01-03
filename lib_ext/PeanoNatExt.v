Require Import 
        Arith.Arith
        Lia.

Section Succ.
  
  Lemma succ_ord_right : forall n m, n + S m = S (n + m).
  Proof.
    intros.
    induction n.
    + simpl.
      reflexivity.
    + simpl.
      rewrite IHn.
      reflexivity.
  Defined.

  Lemma succ_ord_left : forall n m, S n + m = S (n + m).
  Proof.
    intros.
    induction n.
    + simpl.
      reflexivity.
    + simpl.
      rewrite <- IHn.
      reflexivity.
  Defined.
End Succ.

Section Sum.
  
  Lemma zero_neutral : forall n, n = n + 0.
  Proof.
    intro.
    induction n.
    + reflexivity.
    + simpl.
      rewrite <- IHn.
      reflexivity.
  Defined.

  Lemma sum_comm : forall n m, n + m = m + n.
  Proof.
    intros.
    induction n.
    + simpl.
      rewrite <- zero_neutral.
      reflexivity.
    + simpl.
      rewrite IHn.
      rewrite succ_ord_right.
      reflexivity.
  Defined.

  Lemma sum_zero : forall (n1 n2 : nat), n1 + n2 = 0 -> n1 = 0 /\ n2 = 0.
  Proof.
    intros.
    destruct n1.
    - split.
      + reflexivity.
      + simpl in H.
        exact H.
    - inversion H.
  Defined.

End Sum.

Section Le.
  Lemma gt_1_trans : forall n, n <> 0 -> 1 <= n.
  Proof.
    induction n.
    - intro.
      assert(0 = 0).
      {reflexivity.
      }
      contradiction.
    - intro.
      destruct n.
      + reflexivity.
      + assert(S n <> 0).
        {unfold not.
         intro.
         inversion H0.
        }
        apply IHn in H0.
        apply (le_S 1 (S n) H0).
  Defined.

  Lemma le_pred : forall n m, S n <= S m -> n <= m.
  Proof.
    intros.
    induction m.
    + inversion H.
      - reflexivity.
      - destruct n.
        ++ reflexivity.
        ++ inversion H1.
    + inversion H.
      - reflexivity.
      - apply IHm in H1.
        apply (le_S n m H1).
  Defined. 

  Lemma le_pred_succ : forall n m, n <= m -> S n <= S m.
  Proof.
    intro n.
    apply (le_ind n (fun m => S n <= S m)).
    + apply (le_n (S n)).
    + intros.
      apply (le_S (S n) (S m) H0).
  Defined. 

  (* transparent redefinition of Coq.Arith.Plus.le_plus_l *)
  Lemma le_plus_l_trans : forall n m : nat, n <= n + m.
  Proof.
    intros.
    induction m.
    + assert(n = n + 0).
      {apply (zero_neutral n).
      }
      rewrite <- H.
      apply (le_n n).
    + assert(n + S m = S (n + m)).
      {apply (succ_ord_right n m).
      }
      rewrite H.
      apply (le_S n (n + m) IHm).
  Defined.

End Le.


Section Lt.

  Lemma O_l_1 : 0 < 1.
  Proof.
    unfold lt.
    apply (le_n 1).
  Defined.
      
  Lemma suc_prop_trans : forall n, n < S n.
  Proof.
    intro.
    (* lt is defined in terms of le *)
    unfold lt.
    apply (le_n (S n)).
  Defined.
        
  (* transparent redefinition of Coq.Numbers.Natural.Abstract.NOrder.lt_0_succ *)
  Lemma lt_0_succ_trans : forall n, 0 < S n.
  Proof.
    induction n.
    - apply O_l_1.
    - unfold lt in IHn.
      unfold lt.
      apply (le_S _ _ IHn).
  Defined.
      
  Lemma lt_trans_transp : forall n1 n2 n3, n1 < n2 -> n2 < n3 -> n1 < n3.
  Proof.
    intros.
    unfold lt.
    unfold lt in H, H0.
    induction H0.
    + apply (le_S (S n1) n2 H).
    + apply (le_S (S n1) m IHle). 
  Defined.

  Lemma suc_prop_add : forall n m, n < S n + m.
  Proof.
    intros.
    induction m.
    + rewrite <- zero_neutral.
      apply suc_prop_trans.
    + simpl.
      rewrite succ_ord_right.
      rewrite <- succ_ord_left.
      assert(S n + m < S (S n + m)).
      {apply suc_prop_trans.
      }
      auto.
  Defined.

  (* transparent redefinition of Coq.Arith.Lt.lt_S_n *)
  Lemma lt_S_n_trans : forall n m : nat, S n < S m -> n < m.
  Proof.
    intros.
    unfold lt.
    unfold lt in H.
    apply (le_pred (S n) m H).
  Defined.
  
  (* transparent redefinition of Coq.Arith.Lt.lt_n_S *)
  Lemma lt_n_S_trans : forall n m : nat, n < m -> S n < S m.
  Proof.
    intros.
    unfold lt.
    unfold lt in H.
    apply (le_pred_succ (S n) m H).
  Defined.

End Lt.

Section RelLtLe.
  (* transparent redefinition of Coq.Arith.Lt.le_lt_n_Sm *)
  Lemma le_lt_n_Sm_trans :  forall n m : nat, n <= m -> n < S m.
  Proof.
    intros.
    unfold lt.
    apply (le_pred_succ n m H).
  Defined.

  Lemma lt_le_trans :  forall n m : nat, n < m -> n <= m.
  Proof.
    intros.
    induction H.
    - apply (le_S n n (le_n n)).
    - apply (le_S n m IHle).
  Defined.

End RelLtLe.

Section NatLeb.
  Lemma ltb_div : forall n m : nat, m > 1 -> Nat.ltb n m = false -> n / m < n.
  Proof.
    intros n m Hmgt Hltb.
    rewrite Nat.ltb_ge in Hltb.
    apply PeanoNat.Nat.div_lt.
    - (* 0 < n *)
      lia.
    - (* 1 < base *)
      exact Hmgt.
  Qed.
End NatLeb.
    

