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

Theorem qr_by_dec : forall m a x, {qr_by m a x} + {~ qr_by m a x}.
  intros.
  unfold qr_by.
  unfold eqm.
  repeat decide equality.
Qed.

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

SearchAbout (forall _, {_} + {_}).

Lemma qr_dec : forall m (mge0 : 0 < m) a, {qr mge0 a} + {forall x, ~ (x * x == 0) (mod m)}.
  intros.
  pose (Z_bounded_dec (qr_by m a) (qr_by_dec _ _) m).
  destruct o.
  