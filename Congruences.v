Require Export ZArith.
Require Export Znumtheory.
Require Import Zpow_facts.
Require Import CpdtTactics.

Set Implicit Arguments.

(* Congruence modulo n *)
Notation " a == b  (mod  m )" := (eqm m a b) (at level 65, no associativity).

Hint Rewrite Zminus_diag : cpdt.
Theorem cong_equiv : forall a b m, m <> 0 -> (a == b (mod m) <-> (m | a - b)).
  intros.
  split; intro.
  apply Zmod_divide; try omega.
  rewrite Zminus_mod.
  crush.
  destruct H0.
  assert (a = b + q * m) by omega.
  rewrite H1.
  apply Z_mod_plus_full.
Qed.

