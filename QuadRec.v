Require Import CpdtTactics.
Require Import ZArith.
Require Import Znumtheory.
Load Zadditions.

Open Scope Z_scope.
Set Implicit Arguments.

(* Congruence modulo n *)
Notation "( a == b ) (mod m )" := (eqm m a b).

Theorem cong_equiv : forall a b m, 0 < m -> ((a == b) (mod m) <-> (m | a - b)).
  intros.
  split; intro.
  apply Zeq_minus in H0.
  apply Zmod_divide; try omega.
  rewrite Zminus_mod.
  crush.
  destruct H0.
  assert (a = b + q * m) by omega.
  rewrite H1.
  apply Z_mod_plus_full.
Qed.

Definition qr_by (m a x : Z) : Prop := (x * x == a) (mod m).
Definition qr m (mge0 : 0 < m) a : Prop := exists x, qr_by m a x.

Hint Unfold qr qr_by eqm.

Theorem qr_by_dec : forall m a x, {qr_by m a x} + {~ qr_by m a x}.
  intros.
  unfold qr_by.
  unfold eqm.
  repeat decide equality.
Qed.

Hint Rewrite <- Zmult_mod : cpdt.
Hint Resolve Z_mod_lt.

Lemma qr_small : forall m (mge0 : 0 < m) a, (qr mge0 a) <-> exists x, 0 <= x < m /\ qr_by m a x.
  intros.
  split; intros.
  destruct H.
  exists (x mod m).
  split.
  apply Z_mod_lt; try omega.
  unfold qr_by.
  unfold eqm.
  rewrite <- Zmult_mod.
  apply H.
  destruct H.
  exists x.
  tauto.
Qed.

Hint Resolve ex_intro.

Ltac unf_crush := autounfold with *; crush.

Lemma qr_dec : forall m (mge0 : 0 < m) a, {qr mge0 a} + {forall x, ~ (x * x == a) (mod m)}.
  intros.
  destruct (Z_bounded_dec (qr_by m a) (qr_by_dec _ _) m).
  destruct (constructive_indefinite_description Z Z_in_nat nat_in_Z Z_nat_inv _ (dec_to_bounded_dec _ (qr_by_dec m a) m) e).
  destruct a0.
  intuition (eauto with *).
  right.
  do 2 intro.
  assert (m > 0) by omega.
  apply (n (x mod m));
  [ auto | unf_crush].
Qed.

Definition legendre m (mgt0 : 0 < m) a (pr : prime m) (oddpr : 2 < m) : Z :=
  match (Zdivide_dec a m) with
    | left _ => 0
    | right _ => match (qr_dec mgt0 a) with
              | left _ => 1
              | right _ => -1
            end
  end.

Theorem fermats_little : forall a p, prime p -> (a ^ p == a) (mod p).
  intros.
  apply (Zind (fun a => (a ^ p == a) (mod p))).
  rewrite Zpower_0_l; crush.
  destruct H; omega.
  intros.
  rewrite <- (Zsucc_succ').
  