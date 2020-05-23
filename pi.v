Require Import Program.
Require Import Coq.Classes.RelationClasses.

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

  Record t: Set :=
    mk
      {
        divisor: Z;
        dividend: Z;
        nzero: (0 < divisor \/ divisor < 0)%Z;
      }.

  Definition IQR (x: t): R :=
    IZR (dividend x) / IZR (divisor x).

  Lemma IQR_unfold p q r
    :
      IQR (mk p q r) = IZR q / IZR p.
  Proof. auto. Qed.

  Global Opaque IQR.

  Program Definition plus (x1 x2: t): t :=
    mk (x1.(divisor) * x2.(divisor))%Z
       (x1.(divisor) * x2.(dividend) +
        x2.(divisor) * x1.(dividend))%Z
       _.
  Next Obligation.
  Proof.
    destruct x1.(nzero), x2.(nzero).
    - left. apply Z.mul_pos_pos; auto.
    - right. apply Z.mul_pos_neg; auto.
    - right. apply Z.mul_neg_pos; auto.
    - left. apply Z.mul_neg_neg; auto.
  Qed.

  Program Definition reduce (x: t): t :=
    let d := Z.gcd x.(divisor) x.(dividend) in
    mk (Z.div x.(divisor) d)
       (Z.div x.(dividend) d)
       _.
  Next Obligation.
  Admitted.

  Lemma plus_commute x1 x2
    :
      IQR x1 + IQR x2 =
      IQR (plus x1 x2).
  Proof.
  Admitted.

  Lemma reduce_commute x
    :
      IQR x =
      IQR (reduce x).
  Proof.
  Admitted.

  Ltac compute_once H :=
    (try rewrite plus_commute in H;
     try rewrite reduce_commute in H).

  Ltac compute H :=
    repeat (compute_once H).

End Q.



Definition PI_tg_left' (n: nat) :=
  ((/ INR (2 * (2 * n) + 1)) - (/ INR (2 * (2 * n + 1) + 1))).

Program Definition PI_tg_left (n: nat) :=
  (Q.IQR (Q.mk (2 * (2 * Z.of_nat n) + 1) 1 _))
  +
  (Q.IQR (Q.mk (2 * (2 * Z.of_nat n + 1) + 1) (-1) _))
.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Lemma PI_tg_left_eq n
  :
    PI_tg_left n = PI_tg_left' n.
Proof.
  unfold PI_tg_left', PI_tg_left.
  repeat rewrite INR_IZR_INZ.
  repeat rewrite Q.IQR_unfold.
  rewrite <- Rplus_opp. f_equal.
  { replace (2 * (2 * Z.of_nat n) + 1)%Z with (Z.of_nat (2 * (2 * n) + 1))%Z; [lra|lia]. }
  { replace (2 * (2 * Z.of_nat n + 1) + 1)%Z with (Z.of_nat (2 * (2 * n + 1) + 1))%Z; [lra|lia]. }
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

Program Definition PI_tg_right (n: nat) :=
  (Q.IQR (Q.mk (2 * (2 * Z.of_nat n + 2) + 1) 1 _))
  +
  (Q.IQR (Q.mk (2 * (2 * Z.of_nat n + 1) + 1) (-1) _))
.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Lemma PI_tg_right_eq n
  :
    PI_tg_right n = PI_tg_right' n.
Proof.
  unfold PI_tg_right', PI_tg_right.
  repeat rewrite INR_IZR_INZ.
  repeat rewrite Q.IQR_unfold. rewrite Rplus_comm. f_equal.
  { replace (2 * (2 * Z.of_nat n + 1) + 1)%Z with (Z.of_nat (2 * (2 * n + 1) + 1))%Z; [lra|lia]. }
  { replace (2 * (2 * Z.of_nat n + 2) + 1)%Z with (Z.of_nat (2 * (2 * n + 2) + 1))%Z; [lra|lia]. }
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

Program Definition PI_right_n (n: nat) :=
  Q.IQR (Q.mk 1 1 _) + sum_f_R0 PI_tg_right n.
Next Obligation.
  left. lia.
Qed.

Definition PI_right_n' (n: nat) :=
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


Theorem PI_bound (n: nat)
  :
    4 * (PI_left_n n) <= PI /\ PI <= 4 * (PI_right_n n).
Proof.
  split.
  - apply PI_left_bound.
  - apply PI_right_bound.
Qed.


(* example *)
Goal (8 / 3) <= PI /\ PI <=  (52 / 15).
Proof.
  Local Opaque PI Rmult Rinv Rplus.
  generalize (PI_bound 0). intros H.
  unfold PI_left_n, PI_right_n, sum_f_R0, PI_tg_left, PI_tg_right in H.
  simpl in H.
  Q.compute_once H. compute in H.
  unfold Q.reduce in H. simpl.

  Q.compute H.



  lra.
Qed.



(* (* example *) *)
(* Goal (8 / 3) <= PI /\ PI <=  (52 / 15). *)
(* Proof. *)
(*   Local Opaque PI. *)
(*   generalize (PI_bound 0). *)
(*   unfold PI_left_n, PI_right_n, sum_f_R0, PI_tg_left, PI_tg_right. simpl. lra. *)
(* Qed. *)

(* example *)
Goal (304 / 105) <= PI /\ PI <=  (1052 / 315).
Proof.
  Local Opaque PI.
  generalize (PI_bound 1).
  unfold PI_left_n, PI_right_n, sum_f_R0, PI_tg_left, PI_tg_right. simpl.
  lra.
Qed.

(* example *)
Goal (10312 / 3465) <= PI /\ PI <=  (147916 / 45045).
Proof.
  Local Opaque PI.
  generalize (PI_bound 2).
  unfold PI_left_n, PI_right_n, sum_f_R0, PI_tg_left, PI_tg_right. simpl.
  lra.
Qed.

(* example *)
Goal (10312 / 3465) <= PI /\ PI <=  (147916 / 45045).
Proof.
  Local Opaque PI.
  generalize (PI_bound 2).
  unfold PI_left_n, PI_right_n, sum_f_R0, PI_tg_left, PI_tg_right. simpl.
  lra.
Qed.




(* Lemma *)

(* Lemma pi_cal *)


(* example *)
Goal PI <= (512321475000 / 162998802113).
Proof.
Abort.
