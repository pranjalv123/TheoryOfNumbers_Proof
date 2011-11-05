Require Export ZArith.
Require Import CpdtTactics.

Open Scope Z_scope.
Set Implicit Arguments.

Ltac simpl_power := unfold Zpower; unfold Zpower_pos; simpl; fold Zpower_pos; try omega.

Theorem Zind_ge0 : forall (P : Z -> Prop), P 0 -> (forall n : Z, n >= 0 -> P n -> P (Zsucc n)) -> (forall n, n >= 0 -> P n).
  intro.
  intro.
  intro.
  assert (forall k x, x <= k -> 0 < x -> P x).
  apply (Zind (fun k => forall x, x <= k -> 0 < x -> P x)).
  crush.
  intros.
  rewrite <- Zsucc_succ' in H2.
  destruct (Z_le_lt_eq_dec x0 (Zsucc x) H2).
  apply Zlt_succ_le in z.
  apply H1; assumption.
  subst x0; apply H0.
  omega.
  apply Zlt_succ_le in H3.
  destruct (Z_le_lt_eq_dec 0 x H3).
  apply H1; crush.
  crush.
  intros.
  rewrite <- Zpred_pred' in H2.
  apply H1; try assumption.
  pose (Zle_pred x); omega.
  intros.
  apply Zge_le in H2.
  destruct (Z_le_lt_eq_dec 0 n H2).
  apply (H1 n n); crush.
  crush.
Qed.

Theorem Zind_ge_m : forall (P : Z -> Prop) (m : Z), P m -> (forall n : Z, n >= m -> P n -> P (Zsucc n)) -> (forall n, n >= m -> P n).
  intros.
  assert (n - m >= 0) by omega.
  pose (Q := fun k => P (k + m)).
  assert (Q (n - m)).
  apply Zind_ge0; unfold Q; simpl; crush.
  rewrite Zplus_succ_l.
  apply H0; try omega; try assumption.
  unfold Q in H3.
  rewrite Zplus_comm in H3.
  rewrite Zplus_minus in H3.
  assumption.
Qed.

Lemma exp_big : forall p, p > 1 -> forall e, e >= 0 -> p ^ e >= 1.
  intros.
  apply (Zind_ge0 (fun x => p ^ x >= 1)); crush.
  change (Zsucc n) with (n + 1).
  rewrite Zpower_exp; try omega.
  rewrite <- Zmult_1_r.
  apply Zmult_ge_compat; try omega.
  simpl_power.
Qed.

Lemma exp_cancel : forall p e1 e2 m n, e2 >= 0 -> e1 > e2 -> p > 1 -> p ^ e1 * m = p ^ e2 * n -> p ^ (e1 - e2) * m = n.
  intros.
  apply (Zmult_reg_l) with (p := p ^ e2).
  pose (exp_big H1 H).
  omega.
  ring_simplify.
  rewrite <- (Zpower_exp); try omega.
  rewrite Zplus_minus.
  assumption.
Qed.

Theorem Z_bounded_dec : forall (P : Z -> Prop), (forall n, {P n} + {~ P n}) -> forall n, (exists x, 0 <= x < n /\ P x) \/ (forall x, 0 <= x < n -> ~ P x).
  do 2 intro.
  pose (Q := (fun n => (exists x, 0 <= x < n /\ P x) \/ (forall x, 0 <= x < n -> ~ P x))).
  assert (forall n, n >= 0 -> Q n).
  apply (Zind_ge0 Q).
  right; crush.
  intros.
  destruct H1.
  destruct H1.
  left; exists x; crush.
  destruct (H n).
  left; exists n; crush.
  right.
  intros.
  intro.
  destruct (Z_le_lt_eq_dec x n).
  omega.
  specialize (H1 x).
  crush.
  crush.
  intros.
  destruct (Z_lt_ge_dec n 0).
  crush.
  apply (H0 _ z).
Qed.