Require Import Psatz.
Require Import Reals.
Local Open Scope R_scope.


Lemma Rmult_opp_1 (r: R)
  :
    - 1 * r = - r.
Proof. lra. Qed.

Lemma Rplus_opp (r0 r1: R)
  :
    r0 + (- r1) = r0 - r1.
Proof. lra. Qed.


Lemma Un_cv_sub_inf f r N b
      (UN: Un_cv f r)
      (INF: forall n (LE: (n >= N)%nat), exists m, (n <= m)%nat /\ b <= f m)
  :
    b <= r.
Proof.
  destruct (total_order_T b r) as [[LT|EQ]|GT]; try lra.
  assert (EPS: (b-r) > 0) by lra.
  specialize (UN _ EPS). destruct UN as [M UN].
  assert (LE0: (N + M >= N)%nat) by lia.
  specialize (INF _ LE0). destruct INF as [m [LE1 INF]].
  assert (LE2: (m >= M)%nat) by lia.
  specialize (UN _ LE2).
  unfold R_dist in UN.
  rewrite Rabs_pos_eq in UN; try lra.
Qed.

Lemma Un_cv_inf f r N b
      (UN: Un_cv f r)
      (INF: forall n (LE: (n >= N)%nat), b <= f n)
  :
    b <= r.
Proof.
  eapply Un_cv_sub_inf; eauto.
Qed.

Lemma Un_cv_sub_sup f r N b
      (UN: Un_cv f r)
      (SUP: forall n (LE: (n >= N)%nat), exists m, (n <= m)%nat /\ b >= f m)
  :
    b >= r.
Proof.
  destruct (total_order_T b r) as [[LT|EQ]|GT]; try lra.
  assert (EPS: (r-b) > 0) by lra.
  specialize (UN _ EPS). destruct UN as [M UN].
  assert (LE0: (N + M >= N)%nat) by lia.
  specialize (SUP _ LE0). destruct SUP as [m [LE1 SUP]].
  assert (LE2: (m >= M)%nat) by lia.
  specialize (UN _ LE2).
  unfold R_dist in UN.
  rewrite <- Rabs_Ropp in UN.
  rewrite Rabs_pos_eq in UN; try lra.
Qed.

Lemma Un_cv_sup f r N b
      (UN: Un_cv f r)
      (SUP: forall n (LE: (n >= N)%nat), b >= f n)
  :
    b >= r.
Proof.
  eapply Un_cv_sub_sup; eauto.
Qed.


Module Q.

  Definition mk (divisor: Z) (dividend: Z): R :=
    IZR dividend / IZR divisor.

  Lemma unfold p q
    :
      mk p q = IZR q / IZR p.
  Proof. auto. Qed.
  Global Opaque mk.

  Definition approx_left (p q n: Z): Z :=
    ((n * q) / p).

  Definition approx_right (p q n: Z): Z :=
    Z.succ ((n * q) / p).

  Lemma IZR_pos n
        (LE: (1 <= n)%Z)
    :
      0 < IZR n.
  Proof.
    eapply Rlt_le_trans with (r2 := IZR 1); [lra|].
    apply IZR_le. lia.
  Qed.

  Lemma approx_left_left p q n
        (LE0: (1 <= p)%Z)
        (LE1: (1 <= n)%Z)
    :
      mk n (approx_left p q n) <= mk p q.
  Proof.
    set (RLE0:= IZR_pos _ LE0).
    set (RLE1:= IZR_pos _ LE1).
    repeat rewrite unfold.
    apply (Rmult_le_reg_r (IZR n)); auto.
    unfold Rdiv at 1. rewrite Rmult_assoc.
    rewrite Rinv_l; [|lra]. rewrite Rmult_1_r.
    unfold Rdiv. rewrite Rmult_assoc. rewrite Rmult_comm.
    apply (Rmult_le_reg_l (IZR p)); auto.
    repeat rewrite <- Rmult_assoc.
    rewrite Rinv_r; [|lra]. rewrite Rmult_1_l.
    repeat rewrite <- mult_IZR. apply IZR_le.
    apply Zdiv.Z_mult_div_ge. lia.
  Qed.

  Lemma approx_right_right p q n
        (LE0: (1 <= p)%Z)
        (LE1: (1 <= n)%Z)
    :
      mk p q <= mk n (approx_right p q n).
  Proof.
    set (RLE0:= IZR_pos _ LE0).
    set (RLE1:= IZR_pos _ LE1).
    repeat rewrite unfold.
    apply (Rmult_le_reg_r (IZR p)); auto.
    unfold Rdiv at 1. rewrite Rmult_assoc.
    rewrite Rinv_l; [|lra]. rewrite Rmult_1_r.
    unfold Rdiv. rewrite Rmult_assoc. rewrite Rmult_comm.
    apply (Rmult_le_reg_l (IZR n)); auto.
    repeat rewrite <- Rmult_assoc.
    rewrite Rinv_r; [|lra]. rewrite Rmult_1_l.
    repeat rewrite <- mult_IZR. apply IZR_le.
    apply Z.lt_le_incl. apply Z.mul_succ_div_gt. lia.
  Qed.

  Lemma plus_same_commute x y n
    :
      mk n x + mk n y = mk n (x + y)
  .
  Proof.
    repeat rewrite unfold.
    rewrite (plus_IZR x y). lra.
  Qed.

End Q.




Definition PI_tg_left' (n: nat) :=
  ((/ INR (2 * (2 * n) + 1)) - (/ INR (2 * (2 * n + 1) + 1))).

Definition PI_tg_left (n: nat) :=
  (Q.mk (2 * (2 * (Z.of_nat n)) + 1) 1)
  +
  (Q.mk (2 * (2 * (Z.of_nat n) + 1) + 1) (-1))
.

Lemma PI_tg_left_eq n
  :
    PI_tg_left n = PI_tg_left' n.
Proof.
  unfold PI_tg_left', PI_tg_left.
  repeat rewrite INR_IZR_INZ.
  repeat rewrite Q.unfold.
  rewrite <- Rplus_opp. f_equal.
  { replace (2 * (2 * Z.of_nat n) + 1)%Z with (Z.of_nat (2 * (2 * n) + 1))%Z;
      [simpl; lra|lia]. }
  { replace (2 * (2 * Z.of_nat n + 1) + 1)%Z with (Z.of_nat (2 * (2 * n + 1) + 1))%Z;
      [simpl; lra|lia]. }
Qed.

Lemma PI_tg_left_pos n
  :
    PI_tg_left n >= 0.
Proof.
  rewrite PI_tg_left_eq.
  unfold PI_tg_left. apply Rge_minus.
  apply Rle_ge. apply Rinv_le_contravar.
  { eapply Rlt_le_trans with (r2 := INR 1).
    { simpl. lra. }
    { apply le_INR. lia. }
  }
  { apply le_INR. lia. }
Qed.

Definition PI_left_n (n: nat) :=
  sum_f_R0 PI_tg_left n.

Lemma PI_left_incr n m
      (LE: (n <= m)%nat)
  :
    PI_left_n n <= PI_left_n m.
Proof.
  induction LE.
  { lra. }
  { unfold PI_left_n in *. simpl.
    eapply Rle_trans with (r2 := sum_f_R0 PI_tg_left m); auto.
    set (PI_tg_left_pos (S m)). lra.
  }
Qed.

Lemma PI_left_n_odd (n: nat)
  :
    PI_left_n n = sum_f_R0 (tg_alt PI_tg) (2 * n + 1).
Proof.
  induction n.
  { unfold PI_left_n. simpl. rewrite PI_tg_left_eq. compute. lra. }
  unfold PI_left_n in *. simpl. rewrite IHn.
  replace (n + S (n + 0) + 1)%nat with (S (2 * n + 1))%nat; [|lia]. simpl.
  rewrite Rplus_assoc. f_equal.
  rewrite PI_tg_left_eq. unfold PI_tg_left', tg_alt, PI_tg.
  replace ((-1) ^ S (n + (n + 0) + 1)) with 1; cycle 1.
  { replace (S (n + (n + 0) + 1))%nat with (2 * (n + 1))%nat; [|lia]. simpl.
    symmetry. apply pow_1_even. }
  replace ((-1) ^ S (S (n + (n + 0) + 1))) with (- 1); cycle 1.
  { replace (S (S (n + (n + 0) + 1))) with (S (2 * (n + 1))); [|lia].
    symmetry. apply pow_1_odd. }
  rewrite Rmult_1_l. rewrite Rmult_opp_1. rewrite Rplus_opp. f_equal.
  { f_equal. f_equal. lia. }
  { f_equal. f_equal. lia. }
Qed.

Theorem PI_left_bound n
  :
    4 * (PI_left_n n) <= PI.
Proof.
  rewrite <- Alt_PI_eq. unfold Alt_PI.
  rewrite (@Rmult_comm 4 (let (a, _) := exist_PI in a)).
  rewrite (@Rmult_comm 4 (PI_left_n n)).
  apply Rmult_le_compat_r; [lra|].
  eapply Un_cv_inf.
  { apply (proj2_sig exist_PI). }
  { instantiate (1:=(2 * n + 1)%nat). intros. simpl.
    assert (((exists m, n <= m /\ n0 = 2 * m + 1) \/
             (exists m, n <= m /\ n0 = S (2 * m + 1)))%nat).
    { induction LE.
      { left. exists n. eauto. }
      destruct IHLE.
      { destruct H as [n0 [LE0 IHLE]]. subst. right.
        exists n0. split; eauto. }
      { destruct H as [n0 [LE0 IHLE]]. subst. left.
        exists (S n0). split; eauto. lia. }
    }
    clear LE. destruct H as [[m [LE EQ]]|[m [LE EQ]]]; subst.
    { rewrite <- PI_left_n_odd. apply PI_left_incr; auto. }
    { simpl. replace (m + (m + 0) + 1)%nat with (2 * m + 1)%nat; [|lia].
      rewrite <- PI_left_n_odd.
      eapply Rle_trans with (r2 := PI_left_n m).
      { apply PI_left_incr; auto. }
      { assert (0 <= tg_alt PI_tg (S (2 * m + 1))); [|lra].
        unfold tg_alt. left. eapply Rmult_lt_0_compat.
        { replace (S (2 * m + 1))%nat with (2 * (m + 1))%nat; [|lia].
          rewrite pow_1_even. lra. }
        { unfold PI_tg. apply Rinv_0_lt_compat.
          eapply Rlt_le_trans with (r2 := INR 1).
          { simpl. lra. }
          { apply le_INR. lia. }
        }
      }
    }
  }
Qed.


Definition PI_tg_right' (n: nat) :=
  (- (/ INR (2 * (2 * n + 1) + 1)) + (/ INR (2 * (2 * n + 2) + 1))).

Definition PI_tg_right (n: nat) :=
  (Q.mk (2 * (2 * (Z.of_nat n) + 2) + 1) 1)
  +
  (Q.mk (2 * (2 * (Z.of_nat n) + 1) + 1) (-1)).

Lemma PI_tg_right_eq n
  :
    PI_tg_right n = PI_tg_right' n.
Proof.
  unfold PI_tg_right', PI_tg_right.
  repeat rewrite INR_IZR_INZ.
  repeat rewrite Q.unfold. rewrite Rplus_comm. f_equal.
  { replace (2 * (2 * Z.of_nat n + 1) + 1)%Z with (Z.of_nat (2 * (2 * n + 1) + 1))%Z;
      [simpl; lra|lia]. }
  { replace (2 * (2 * Z.of_nat n + 2) + 1)%Z with (Z.of_nat (2 * (2 * n + 2) + 1))%Z;
      [simpl; lra|lia]. }
Qed.

Lemma PI_tg_right_neg n
  :
    PI_tg_right n <= 0.
Proof.
  rewrite PI_tg_right_eq. unfold PI_tg_right'.
  cut (/ INR (2 * (2 * n + 2) + 1) <= / INR (2 * (2 * n + 1) + 1)); [lra|].
  apply Rinv_le_contravar.
  { eapply Rlt_le_trans with (r2 := INR 1).
    { simpl. lra. }
    { apply le_INR. lia. }
  }
  { apply le_INR. lia. }
Qed.

Definition PI_right_n (n: nat) :=
  1 + sum_f_R0 PI_tg_right n.

Lemma PI_right_decr n m
      (LE: (n <= m)%nat)
  :
    PI_right_n n >= PI_right_n m.
Proof.
  induction LE.
  { lra. }
  { unfold PI_right_n in *. simpl.
    eapply Rge_trans; [apply IHLE|].
    set (PI_tg_right_neg (S m)). lra.
  }
Qed.

Lemma PI_right_n_even (n: nat)
  :
    PI_right_n n = sum_f_R0 (tg_alt PI_tg) (2 * n + 2).
Proof.
  induction n.
  { unfold PI_right_n. simpl. rewrite PI_tg_right_eq. compute. lra. }
  unfold PI_right_n in *. simpl.
  rewrite <- Rplus_assoc. rewrite IHn.
  replace (n + S (n + 0) + 2)%nat with (S (2 * n + 2))%nat; [|lia]. simpl.
  rewrite Rplus_assoc. f_equal.
  rewrite PI_tg_right_eq. unfold PI_tg_right', tg_alt, PI_tg. f_equal.
  { replace (n + (n + 0) + 2)%nat with (2 * (n + 1))%nat; [|lia].
    rewrite pow_1_odd.
    replace (2 * (2 * S n + 1) + 1)%nat with (2 * S (2 * (n + 1)) + 1)%nat; [|lia].
    lra. }
  { replace (S (S (n + (n + 0) + 2)))%nat with (2 * (n + 2))%nat; [|lia].
    rewrite pow_1_even.
    replace (2 * (2 * S n + 2) + 1)%nat with (2 * (2 * (n + 2)) + 1)%nat; [|lia].
    lra. }
Qed.

Theorem PI_right_bound n
  :
    PI <= 4 * (PI_right_n n).
Proof.
  rewrite <- Alt_PI_eq. unfold Alt_PI.
  rewrite (@Rmult_comm 4 (let (a, _) := exist_PI in a)).
  simpl.
  rewrite (@Rmult_comm 4 (PI_right_n n)).
  apply Rmult_le_compat_r; [lra|].
  apply Rge_le. eapply Un_cv_sup.
  { apply (proj2_sig exist_PI). }
  { instantiate (1:=(2 * n + 2)%nat). intros. simpl.
    assert (((exists m, n <= m /\ n0 = 2 * m + 2) \/
             (exists m, n <= m /\ n0 = S (2 * m + 2)))%nat).
    { induction LE.
      { left. exists n. eauto. }
      destruct IHLE.
      { destruct H as [n0 [LE0 IHLE]]. subst. right.
        exists n0. split; eauto. }
      { destruct H as [n0 [LE0 IHLE]]. subst. left.
        exists (S n0). split; eauto. lia. }
    }
    clear LE. destruct H as [[m [LE EQ]]|[m [LE EQ]]]; subst.
    { rewrite <- PI_right_n_even. apply PI_right_decr; auto. }
    { simpl. replace (m + (m + 0) + 2)%nat with (2 * m + 2)%nat; [|lia].
      rewrite <- PI_right_n_even.
      eapply Rge_trans with (r2 := PI_right_n m).
      { apply PI_right_decr; auto. }
      { assert (0 >= tg_alt PI_tg (S (2 * m + 2))); [|lra].
        unfold tg_alt. left.
        replace (S (2 * m + 2))%nat with (S (2 * (m + 1)))%nat; [|lia].
        rewrite pow_1_odd.
        cut (PI_tg (S (2 * (m + 1))) > 0); [lra|].
        unfold PI_tg. apply Rinv_0_lt_compat.
        eapply Rlt_le_trans with (r2 := INR 1).
        { simpl. lra. }
        { apply le_INR. lia. }
      }
    }
  }
Qed.




Definition PI_tg_left_approx (m: Z) (n: Z) :=
  ((Q.approx_left (2 * (2 * n) + 1) 1 m) +
   (Q.approx_left (2 * (2 * n + 1) + 1) (-1) m))%Z
.

Lemma PI_tg_left_approx_left m n
      (LE: (1 <= m)%Z)
  :
    Q.mk m (PI_tg_left_approx m (Z.of_nat n)) <= PI_tg_left n.
Proof.
  unfold PI_tg_left_approx, PI_tg_left.
  rewrite <- Q.plus_same_commute. apply Rplus_le_compat.
  { apply Q.approx_left_left; auto. lia. }
  { apply Q.approx_left_left; auto. lia. }
Qed.

Fixpoint sum_f_Z0 (f: Z -> Z) (n: nat): Z :=
  match n with
  | O => f (Z.of_nat O)
  | S n' => (sum_f_Z0 f n' + f (Z.of_nat n))%Z
  end.

Fixpoint sum_f_Z0_tail (f: Z -> Z) (n: nat) (sum: Z): Z :=
  match n with
  | O => (sum + f (Z.of_nat O))%Z
  | S n' =>
    let fn := f (Z.of_nat n) in
    let sum' := (sum + fn)%Z in
    sum_f_Z0_tail f n' sum'
  end.

Lemma sum_f_Z0_tail_eq f n sum
  :
    (sum + sum_f_Z0 f n)%Z = sum_f_Z0_tail f n sum.
Proof.
  revert sum. induction n; intros; simpl; auto.
  rewrite <- IHn. lia.
Qed.

Definition PI_left_n_approx (m: Z) (n: nat) :=
  Q.mk m (sum_f_Z0_tail (PI_tg_left_approx m) n 0).

Lemma PI_left_n_approx_left m n
      (LE: (1 <= m)%Z)
  :
    PI_left_n_approx m n <= PI_left_n n.
Proof.
  unfold PI_left_n_approx, PI_left_n.
  rewrite <- sum_f_Z0_tail_eq. simpl.
  induction n.
  { simpl. apply (PI_tg_left_approx_left m 0). auto. }
  { simpl. rewrite <- Q.plus_same_commute. apply Rplus_le_compat; auto.
    apply (PI_tg_left_approx_left m (S n)); auto. }
Qed.

Theorem PI_left_approx_bound m n
      (LE: (1 <= m)%Z)
  :
    4 * (PI_left_n_approx m n) <= PI.
Proof.
  apply Rle_trans with (r2 := 4 * (PI_left_n n)).
  { apply Rmult_le_compat_l; [lra|].
    apply PI_left_n_approx_left; auto. }
  { apply PI_left_bound. }
Qed.

Goal 314/100 <= PI.
Proof.
  Local Opaque PI Rmult Rinv Rplus Rle.
  cut (4 * PI_left_n_approx 200000 1000 <= PI); cycle 1.
  { apply (PI_left_approx_bound 200000 1000). lia. }
  { intros X.

    unfold PI_left_n_approx, Z.to_nat, PI_tg_left_approx in X.

    simpl in X.
Admitted.
