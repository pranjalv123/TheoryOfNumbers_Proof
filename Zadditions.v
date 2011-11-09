Require Export ZArith.
Require Export Zpow_facts.
Require Import Even.
Require Import ConstructiveEpsilon.
Require Import CpdtTactics.

Open Scope Z_scope.
Set Implicit Arguments.

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).

Ltac simpl_power := unfold Zpower; unfold Zpower_pos; simpl; fold Zpower_pos; try omega.

Hint Resolve ex_intro.

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

Definition nat_in_Z (n : nat) : Z :=
  match (even_odd_dec n) with
    | left _ => (Z_of_nat n) / 2
    | right _ => - ((Z_of_nat n) + 1) / 2
  end.

Definition Z_pred_to_nat_pred (P : Z -> Prop) : nat -> Prop :=
  fun x => P (nat_in_Z x).

Definition Z_in_nat (z : Z) : nat :=
  match z with
    | Z0 => O
    | Zpos p => Pmult_nat p 2
    | Zneg p => minus (Pmult_nat p 2) 1
  end.

Require Import Pnat.

Open Scope nat_scope.

Lemma even_diag : forall n, even (n + n).
  intros.
  induction n.
  crush.
  rewrite <- plus_n_Sm.
  apply even_ind; crush.
Qed.

Lemma odd_diag : forall n : nat, (n > O) -> ~ even (n + n - 1).
  do 3 intro.
  assert (n + n >= 1) by omega.
  apply (not_even_and_odd (n + n - 1)).
  assumption.
  pose (even_diag n).
  inversion e.
  elimtype False; omega.
  assert (n0 >= 1) by omega.
  rewrite <- minus_Sn_m; try omega.
  change (S _) with (1 + (n0 - 1)).
  rewrite <- (le_plus_minus 1 n0); crush.
Qed.
  
Theorem Z_nat_inv : forall z, nat_in_Z (Z_in_nat z) = z.
  intros.
  unfold Z_in_nat.
  destruct z.
  crush.
  rewrite ZL6.
  unfold nat_in_Z.
  simpl.
  destruct (even_odd_dec (nat_of_P p + nat_of_P p)).
  rewrite inj_plus.
  rewrite <- (Zmult_1_r (Z_of_nat (nat_of_P p))).
  rewrite <- Zmult_plus_distr_r.
  simpl.
  rewrite Z_div_mult_full; try discriminate.
  change (Pmult_nat p 1) with (nat_of_P p).
  symmetry.
  apply Zpos_eq_Z_of_nat_o_nat_of_P.
  elimtype False.
  apply (not_even_and_odd (nat_of_P p + nat_of_P p)).
  apply even_diag.
  assumption.
  unfold nat_in_Z.
  destruct (even_odd_dec (Pmult_nat p 2 - 1)).
  rewrite ZL6 in e.
  elimtype False.
  apply (@odd_diag (nat_of_P p)).
  destruct (ZL4 p).
  omega.
  assumption.
  rewrite ZL6 in *.
  assert (Z_of_nat 1 = 1%Z) by crush.
  rewrite <- H.
  rewrite <- inj_plus.
  rewrite plus_comm.
  rewrite <- (le_plus_minus _ _).
  rewrite inj_plus.
  rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
  rewrite <- (Zmult_1_r (Zpos p)).
  rewrite <- Zmult_plus_distr_r.
  change (1 + 1)%Z with 2%Z.
  rewrite Zopp_mult_distr_l.
  rewrite Z_div_mult_full.
  crush.
  crush.
  destruct (ZL4 p).
  omega.
Qed.

Close Scope nat_scope.

Definition dec_to_bounded_dec : forall (P : Z -> Prop), (forall n, {P n} + {~ P n}) -> (forall n x, {0 <= x < n /\ P x} + {~ (0 <= x < n /\ P x)}).
  intros.
  destruct (Z_le_gt_dec 0 x).
  destruct (Z_lt_le_dec x n).
  destruct (H x).
  left; tauto.
  right; tauto.
  right; omega.
  right; omega.
Qed.
  
Lemma Z_bounded_dec : forall (P : Z -> Prop), (forall n, {P n} + {~ P n}) -> forall n, {exists x, 0 <= x < n /\ P x} + {forall x, 0 <= x < n -> ~ P x}.
  do 2 intro.
  pose (Q := (fun n => {exists x, 0 <= x < n /\ P x} + {forall x, 0 <= x < n -> ~ P x})).
  assert (forall n, 0 <= n -> Q n).
  apply (natlike_rec2 Q).
  right; crush.
  intros.
  destruct H1.
  pose (constructive_indefinite_description Z Z_in_nat nat_in_Z Z_nat_inv _ (dec_to_bounded_dec _ H z)).
  simpl in s.
  specialize (s e).
  destruct s.
  destruct a.
  left; exists x; crush.
  destruct (H z).
  left; exists z; crush.
  right.
  intros.
  intro.
  destruct (Z_le_lt_eq_dec x z).
  omega.
  specialize (n x).
  crush.
  crush.
  intros.
  destruct (Z_lt_ge_dec n 0).
  crush.
  assert (0 <= n) by omega.
  apply (H0 _ H1).
Qed.