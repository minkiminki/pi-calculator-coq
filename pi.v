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
      }.

  Definition IQR (x: t): R :=
    IZR (dividend x) / IZR (divisor x).

  Lemma IQR_unfold x
    :
      IQR x = IZR x.(dividend) / IZR x.(divisor).
  Proof. auto. Qed.

  Global Opaque IQR.

  Definition plus (x1 x2: t): t :=
    mk (x1.(divisor) * x2.(divisor))%Z
       (x1.(divisor) * x2.(dividend) +
        x2.(divisor) * x1.(dividend))%Z
  .

  Definition plus_opt (x1 x2: t): t :=
    let g := Z.gcd x1.(divisor) x2.(divisor) in
    mk ((x1.(divisor) / g) * x2.(divisor))%Z
       ((x1.(divisor) / g) * x2.(dividend) +
        (x2.(divisor) / g) * x1.(dividend))%Z
  .

  Definition mult (x1 x2: t): t :=
    mk (x1.(divisor) * x2.(divisor))%Z
       (x1.(dividend) * x2.(dividend))%Z
  .

  Definition reduce_rev (x: t) (n: Z): t :=
    mk (x.(divisor) * n)
       (x.(dividend) * n).

  Lemma Z_divide_mult (p q: Z)
        (DIV: (p | q)%Z)
        (NEQ: p <> 0%Z)
    :
      q = ((q / p) * p)%Z.
  Proof.
    destruct DIV as [d EQ]. subst.
    rewrite Z.div_mul; auto.
  Qed.

  Lemma Z_divide_gcd_nzero p q
        (NEQ: p <> 0%Z)
    :
      (p / Z.gcd p q <> 0)%Z.
  Proof.
    assert (NEQGCD: Z.gcd p q <> 0%Z).
    { intros EQ. apply Z.gcd_eq_0 in EQ. destruct EQ. exfalso. eauto. }
    generalize (Z.gcd_divide_l p q). intros DIV.
    destruct DIV as [g EQ]. rewrite EQ at 1.
    rewrite Zdiv.Z_div_mult_full; auto.
    intros GEQ. subst. lia.
  Qed.

  Lemma reduce_rev_eq x n
        (NEQ0: x.(divisor) <> 0%Z)
        (NEQ1: n <> 0%Z)
    :
      IQR x =
      IQR (reduce_rev x n).
  Proof.
    assert (RNEQ0: IZR (divisor x) <> 0).
    { intros EQ. apply NEQ0, eq_IZR, EQ. }
    assert (RNEQ1: IZR (divisor x * n) <> 0).
    { intros EQ. apply eq_IZR_R0 in EQ.
      apply Zmult_integral in EQ.
      destruct EQ; exfalso; eauto. }
    unfold reduce_rev. repeat rewrite IQR_unfold. simpl.
    apply (Rmult_eq_reg_r (IZR (divisor x))); auto.
    unfold Rdiv at 1. rewrite Rmult_assoc. rewrite Rinv_l; auto.
    rewrite Rmult_1_r. rewrite Rmult_comm. unfold Rdiv at 1.
    apply (Rmult_eq_reg_r (IZR (divisor x * n))); auto.
    repeat rewrite Rmult_assoc. rewrite Rinv_l; auto.
    rewrite Rmult_1_r. repeat rewrite <- mult_IZR.
    f_equal. lia.
  Qed.

  Definition reduce (x: t): t :=
    let g := Z.gcd x.(divisor) x.(dividend) in
    mk (Z.div x.(divisor) g)
       (Z.div x.(dividend) g)
  .

  Lemma reduce_eq x
        (NEQ: x.(divisor) <> 0%Z)
    :
      IQR x =
      IQR (reduce x).
  Proof.
    assert (NEQGCD: Z.gcd (divisor x) (dividend x) <> 0%Z).
    { intros EQ. apply Z.gcd_eq_0 in EQ. destruct EQ. exfalso. eauto. }
    set (NEQDIV:= Z_divide_gcd_nzero (divisor x) (dividend x)).
    transitivity (IQR (reduce_rev (reduce x) (Z.gcd (divisor x) (dividend x)))).
    { unfold reduce. repeat rewrite IQR_unfold. simpl. f_equal.
      { f_equal. apply Z_divide_mult; auto.
        apply Z.gcd_divide_r. }
      { f_equal. apply Z_divide_mult; auto.
        apply Z.gcd_divide_l. }
    }
    { symmetry. apply reduce_rev_eq; auto. }
  Qed.

  Lemma plus_commute x1 x2
        (NEQ1: x1.(divisor) <> 0%Z)
        (NEQ2: x2.(divisor) <> 0%Z)
    :
      IQR x1 + IQR x2 =
      IQR (plus x1 x2).
  Proof.
    assert (RNEQ1: IZR (divisor x1) <> 0).
    { intros EQ. apply NEQ1, eq_IZR, EQ. }
    assert (RNEQ2: IZR (divisor x2) <> 0).
    { intros EQ. apply NEQ2, eq_IZR, EQ. }
    unfold plus.
    repeat rewrite IQR_unfold. simpl.
    rewrite plus_IZR. rewrite Rdiv_plus_distr.
    repeat rewrite mult_IZR. rewrite Rplus_comm. f_equal.
    { rewrite (Rmult_comm (IZR (divisor x1)) (IZR (dividend x2))).
      rewrite (Rmult_comm (IZR (divisor x1)) (IZR (divisor x2))).
      apply (Rmult_eq_reg_r (IZR (divisor x2) * IZR (divisor x1))); cycle 1.
      { intros EQ. apply Rmult_integral in EQ.
        destruct EQ; exfalso; eauto. }
      unfold Rdiv. f_equal.
      repeat rewrite Rmult_assoc. f_equal.
      rewrite Rinv_mult_distr; auto.
      rewrite Rmult_comm. rewrite Rmult_assoc.
      rewrite Rinv_l; auto. lra.
    }
    { rewrite (Rmult_comm (IZR (divisor x2)) (IZR (dividend x1))).
      rewrite (Rmult_comm (IZR (divisor x1)) (IZR (divisor x2))).
      apply (Rmult_eq_reg_r (IZR (divisor x1) * IZR (divisor x2))); cycle 1.
      { intros EQ. apply Rmult_integral in EQ.
        destruct EQ; exfalso; eauto. }
      unfold Rdiv. f_equal.
      repeat rewrite Rmult_assoc. f_equal.
      rewrite Rinv_mult_distr; auto.
      rewrite <- Rmult_assoc.
      rewrite Rinv_r; auto. lra.
    }
  Qed.

  Lemma plus_opt_commute x1 x2
        (NEQ1: x1.(divisor) <> 0%Z)
        (NEQ2: x2.(divisor) <> 0%Z)
    :
      IQR x1 + IQR x2 =
      IQR (plus_opt x1 x2).
  Proof.
    assert (NEQGCD: Z.gcd (divisor x1) (divisor x2) <> 0%Z).
    { intros EQ. apply Z.gcd_eq_0 in EQ. destruct EQ. exfalso. eauto. }
    set (NEQDIV:= Z_divide_gcd_nzero (divisor x1) (divisor x2)).
    rewrite plus_commute; auto.
    transitivity (IQR (reduce_rev (plus_opt x1 x2) (Z.gcd (divisor x1) (divisor x2)))).
    { unfold plus, plus_opt, reduce_rev. simpl. f_equal. f_equal.
      { rewrite <- Zmult_assoc.
        rewrite (Zmult_comm (divisor x2) (Z.gcd (divisor x1) (divisor x2))).
        rewrite (Z_divide_mult (Z.gcd (divisor x1) (divisor x2)) (divisor x1)) at 1; auto.
        { lia. }
        { apply Z.gcd_divide_l. }
      }
      { rewrite Z.mul_add_distr_r. f_equal.
        { rewrite (Z_divide_mult (Z.gcd (divisor x1) (divisor x2)) (divisor x1)) at 1; auto.
          { lia. }
          { apply Z.gcd_divide_l. }
        }
        { rewrite (Z_divide_mult (Z.gcd (divisor x1) (divisor x2)) (divisor x2)) at 1; auto.
          { lia. }
          { apply Z.gcd_divide_r. }
        }
      }
    }
    { symmetry. apply reduce_rev_eq; auto.
      unfold plus_opt. simpl.
      apply Z.neq_mul_0. split; auto. }
  Qed.

  Lemma mult_commute x1 x2
        (NEQ1: x1.(divisor) <> 0%Z)
        (NEQ2: x2.(divisor) <> 0%Z)
    :
      IQR x1 * IQR x2 =
      IQR (mult x1 x2).
  Proof.
    assert (RNEQ1: IZR (divisor x1) <> 0).
    { intros EQ. apply NEQ1, eq_IZR, EQ. }
    assert (RNEQ2: IZR (divisor x2) <> 0).
    { intros EQ. apply NEQ2, eq_IZR, EQ. }
    unfold mult. repeat rewrite IQR_unfold. simpl.
    repeat rewrite mult_IZR. unfold Rdiv.
    rewrite Rinv_mult_distr; auto. lra.
  Qed.

  Lemma plus_reduce_commute x1 x2
        (NEQ1: x1.(divisor) <> 0%Z)
        (NEQ2: x2.(divisor) <> 0%Z)
    :
      IQR x1 + IQR x2 =
      IQR (reduce (plus x1 x2)).
  Proof.
    rewrite plus_commute; auto.
    apply reduce_eq; auto.
    simpl. intros EQ. apply Zmult_integral in EQ.
    destruct EQ; exfalso; eauto.
  Qed.

  Lemma plus_opt_reduce_commute x1 x2
        (NEQ1: x1.(divisor) <> 0%Z)
        (NEQ2: x2.(divisor) <> 0%Z)
    :
      IQR x1 + IQR x2 =
      IQR (reduce (plus_opt x1 x2)).
  Proof.
    rewrite plus_opt_commute; auto.
    apply reduce_eq; auto.
    simpl. apply Z.neq_mul_0. split; auto.
    apply Z_divide_gcd_nzero; auto.
  Qed.

  Lemma mult_reduce_commute x1 x2
        (NEQ1: x1.(divisor) <> 0%Z)
        (NEQ2: x2.(divisor) <> 0%Z)
    :
      IQR x1 * IQR x2 =
      IQR (reduce (mult x1 x2)).
  Proof.
    rewrite mult_commute; auto.
    apply reduce_eq; auto.
    simpl. intros EQ. apply Zmult_integral in EQ.
    destruct EQ; exfalso; eauto.
  Qed.

  Definition of_z (n: Z): t := Q.mk 1 n.
  Lemma of_z_IZR n
    :
      Q.IQR (of_z n) = IZR n.
  Proof.
    unfold of_z. rewrite Q.IQR_unfold. simpl. lra.
  Qed.

  Ltac nonzerotac :=
    let H := fresh in
    intros H; inversion H.

  Ltac plus_once H :=
    rewrite plus_commute in H; [compute in H|nonzerotac|nonzerotac].

  Ltac plus_reduce_once H :=
    rewrite plus_reduce_commute in H; [compute in H|nonzerotac|nonzerotac].

  Ltac plus_opt_once H :=
    rewrite plus_opt_reduce_commute in H; [compute in H|nonzerotac|nonzerotac].

  Ltac mult_once H :=
    rewrite mult_commute in H; [compute in H|nonzerotac|nonzerotac].

  Ltac mult_reduce_once H :=
    rewrite mult_reduce_commute in H; [compute in H|nonzerotac|nonzerotac].

  Ltac reduce H :=
    rewrite reduce_eq in H; [|nonzerotac].

  Ltac compute H :=
    repeat (plus_reduce_once H);
    try (reduce H); compute in H.

  Ltac compute_opt H :=
    repeat (plus_opt_once H);
    try (reduce H); compute in H.

  Ltac finish H :=
    repeat rewrite IQR_unfold in H; simpl in H.

End Q.



Definition PI_tg_left' (n: nat) :=
  ((/ INR (2 * (2 * n) + 1)) - (/ INR (2 * (2 * n + 1) + 1))).

Definition PI_tg_left (n: nat) :=
  let z := Z.of_nat n in
  (Q.IQR (Q.mk ((4 * z + 1) * (4 * z + 3)) 2)).

Lemma PI_tg_left_eq n
  :
    PI_tg_left n = PI_tg_left' n.
Proof.
  Local Opaque Z.mul.
  unfold PI_tg_left', PI_tg_left.
  transitivity ((Q.IQR (Q.mk (2 * (2 * Z.of_nat n) + 1) 1))
                +
                (Q.IQR (Q.mk (2 * (2 * Z.of_nat n + 1) + 1) (-1)))).
  { rewrite Q.plus_commute; simpl; try lia.
    unfold Q.plus. simpl. f_equal. f_equal; try lia.
  }
  { repeat rewrite INR_IZR_INZ.
    repeat rewrite Q.IQR_unfold.
    rewrite <- Rplus_opp. f_equal.
    { replace (2 * (2 * Z.of_nat n) + 1)%Z with (Z.of_nat (2 * (2 * n) + 1))%Z;
        [simpl; lra|lia]. }
    { replace (2 * (2 * Z.of_nat n + 1) + 1)%Z with (Z.of_nat (2 * (2 * n + 1) + 1))%Z;
        [simpl; lra|lia]. }
  }
  Local Transparent Z.mul.
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
    (Q.IQR (Q.of_z 4)) * (PI_left_n n) <= PI.
Proof.
  rewrite <- Alt_PI_eq. unfold Alt_PI.
  rewrite Q.of_z_IZR.
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
  let z := Z.of_nat n in
  Q.IQR (Q.mk ((4 * z + 5) * (4 * z + 3)) (-2))
.

Lemma PI_tg_right_eq n
  :
    PI_tg_right n = PI_tg_right' n.
Proof.
  Local Opaque Z.mul.
  unfold PI_tg_right', PI_tg_right.
  transitivity ((Q.IQR (Q.mk (2 * (2 * Z.of_nat n + 2) + 1) 1))
                +
                (Q.IQR (Q.mk (2 * (2 * Z.of_nat n + 1) + 1) (-1)))).
  { rewrite Q.plus_commute; simpl; try lia.
    unfold Q.plus. simpl. f_equal. f_equal; try lia.
  }
  repeat rewrite INR_IZR_INZ.
  repeat rewrite Q.IQR_unfold. rewrite Rplus_comm. f_equal.
  { replace (2 * (2 * Z.of_nat n + 1) + 1)%Z with (Z.of_nat (2 * (2 * n + 1) + 1))%Z;
      [simpl; lra|lia]. }
  { replace (2 * (2 * Z.of_nat n + 2) + 1)%Z with (Z.of_nat (2 * (2 * n + 2) + 1))%Z;
      [simpl; lra|lia]. }
  Local Transparent Z.mul.
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
  Q.IQR (Q.mk 1 1) + sum_f_R0 PI_tg_right n.

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
  { unfold PI_right_n. simpl. rewrite PI_tg_right_eq.
    rewrite Q.IQR_unfold. compute. lra. }
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
    PI <= (Q.IQR (Q.of_z 4)) * (PI_right_n n).
Proof.
  rewrite <- Alt_PI_eq. unfold Alt_PI.
  rewrite Q.of_z_IZR.
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


Theorem PI_bound (n: nat)
  :
    (Q.IQR (Q.of_z 4)) * (PI_left_n n) <= PI /\ PI <= (Q.IQR (Q.of_z 4)) * (PI_right_n n).
Proof.
  split.
  - apply PI_left_bound.
  - apply PI_right_bound.
Qed.


Ltac pi_finish H :=
  repeat Q.mult_reduce_once H;
  Q.finish H.

Ltac pi_cal H :=
  unfold Q.of_z, PI_left_n, PI_right_n, sum_f_R0, PI_tg_left, PI_tg_right in H;
  Q.compute_opt H;
  pi_finish H.

Ltac pi_left_bound n H :=
  let X := fresh H in
  generalize (PI_left_bound n); intro X;
  pi_cal X.

Ltac pi_right_bound n H :=
  let X := fresh H in
  generalize (PI_right_bound n); intro X;
  pi_cal X.

Ltac pi_bound n H :=
  let X := fresh H in
  generalize (PI_bound n); intro X;
  pi_cal X.



Lemma fraction_compare (a b c d: Z)
      (POS0: (0 < b)%Z)
      (POS1: (0 < d)%Z)
      (LE: (a * d <= b *c)%Z)
  :
    IZR a / IZR b <= IZR c / IZR d.
Proof.
  assert (RPOS0: 0 < IZR b).
  { eapply Rlt_le_trans with (r2 := IZR 1); [lra|].
    apply IZR_le. lia. }
  assert (RPOS1: 0 < IZR d).
  { eapply Rlt_le_trans with (r2 := IZR 1); [lra|].
    apply IZR_le. lia. }
  apply Rmult_le_reg_r with (r := IZR b); auto.
  unfold Rdiv at 1. rewrite Rmult_assoc.
  rewrite Rinv_l; [|lra]. rewrite Rmult_1_r.
  rewrite Rmult_comm. unfold Rdiv.
  apply Rmult_le_reg_r with (r := IZR d); auto.
  repeat rewrite Rmult_assoc.
  rewrite Rinv_l; [|lra]. rewrite Rmult_1_r.
  repeat rewrite <- mult_IZR. apply IZR_le. auto.
Qed.




(* example *)
Goal (313 / 100) <= PI /\ PI <=  (315 / 100).
Proof.
  Local Opaque PI Rmult Rinv Rplus Rle.
  pi_bound 60%nat BOUND. lra.
Qed.

(* final goal *)
Goal PI <= (512321475000 / 162998802113).
Proof.
  Local Opaque PI Rmult Rinv Rplus Rle.
  (* it takes more than 5 min  *)
  pi_right_bound 340%nat BOUND.
  lra.
  (* and Qed takes much more... *)
Qed.
