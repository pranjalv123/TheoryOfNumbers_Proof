Require Import CpdtTactics.
Require Import List.
Require Import ZArith.
Require Import Znumtheory.
Require Import Classical.

Set Implicit Arguments.

Ltac destruct_div :=
  intros;
  repeat match goal with
           | [ |- (?m | ?n) ] => constructor
           | [ H : (?m | ?n) |- _ ] => destruct H
         end;
  match goal with
    | [ |- (?a | ?b) \/ (?c | ?d) ] => destruct (Zdivide_dec a b); [ left; assumption | right ]
  end.

Inductive prod_primes : Z -> Prop :=
  | idprime : forall n, prime n -> prod_primes n
  | recprime : forall n a b, (n = b * a /\ prod_primes a /\ prod_primes b) -> prod_primes n.

Hint Constructors prod_primes.
Hint Resolve prime_alt.

Lemma not_prime_divisible : forall z, z > 1 -> ~ (prime z) -> exists x, 1 < x < z /\ (x | z).
  intros.
  assert (~ prime' z).
  destruct (prime_alt z).
  crush.
  unfold prime' in H1.
  apply not_and_or in H1.
  crush.
  apply not_all_ex_not in H2.
  destruct H2.
  apply imply_to_and in H1.
  crush.
  apply NNPP in H3.
  exists x.
  crush.
Qed.

Hint Resolve not_prime_divisible.

Lemma prime_or_divisible : forall z, prime z \/ exists x, (x | z).
  eauto with zarith.
Qed.

Hint Resolve prime_or_divisible.

Hint Resolve Zdivide_Zdiv_eq.

(* what a piece of shit... *)
Theorem all_prod_primes : forall n, n > 1 -> prod_primes n.
  assert (forall k n, n <= k -> n > 1 -> prod_primes n).
  apply (Zind (fun k => (forall n, n <= k -> n > 1 -> prod_primes n))); crush.
  rewrite <- Zsucc_succ' in H0.
  destruct (prime_dec n).
  crush.
  assert (exists z, 1 < z < n /\ (z | n)).
  apply not_prime_divisible; crush.
  destruct H2.
  destruct H2.
  apply (@recprime n (Zabs x0) (n / (Zabs x0))); crush.
  rewrite Zmult_comm.
  apply Zdivide_Zdiv_eq.
  assert (x0 <> 0).
  intro.
  subst.
  assert (n | 0) by crush.
  assert (n = 0 \/ n = -0) by (apply Zdivide_antisym; assumption).
  crush.
  assert (Zabs x0 <> 0).
  pose (Zabs_eq_case x0 0); crush.
  pose (Zabs_pos x0); crush.
  apply Zdivide_Zabs_inv_l; assumption; crush.
  rewrite Zabs_eq.
  apply (H x0); crush.
  apply (Zlt_le_trans x0 n (Zsucc x)) in H0; crush.
  rewrite Zabs_eq.
  assert (0 < n / x0 < n).
  apply Zdivide_Zdiv_lt_pos; crush.
  apply H.
  crush.
  assert (n / x0 <> 1).
  intro.
  assert (n = x0).
  rewrite <- (Zmult_1_r x0).
  rewrite <- H6.
  apply Zdivide_Zdiv_eq; crush.
  crush.
  crush.
  crush.
  rewrite <- (Zpred_pred') in H0.
  pose (Zle_pred x).
  apply (Zle_trans n (Zpred x) x) in z; crush.
  intros.
  specialize (H (Zsucc n) n).
  crush.
Qed.

(* this proof is a piece of shit. *)
Theorem euclids_lemma : forall p a b, prime p -> (p | a * b) -> (p | a) \/ (p | b).
  destruct_div.
  assert (rel_prime p a).
  apply prime_rel_prime; assumption.
  apply rel_prime_bezout in H1.
  destruct H1.
  assert (u * p * b + v * a * b = b).
  rewrite <- (Zmult_plus_distr_l).
  rewrite H1.
  apply Zmult_1_l.
  assert (b = (u * b + v * q) * p).
  rewrite <- (Zmult_assoc v a b) in H2.
  rewrite H0 in H2.
  rewrite (Zmult_assoc v q p) in H2.
  rewrite <- (Zmult_assoc u p b) in H2.
  rewrite (Zmult_comm p b) in H2.
  rewrite (Zmult_assoc) in H2.
  rewrite <- (Zmult_plus_distr_l) in H2.
  auto.
  pose (Zdivide_intro p b (u * b + v * q)).
  auto.
Qed.

Require Import Classical_sets.
Require Import Finite_sets.

Inductive prime_exp_pair := pep_intro : forall p e, prime p -> e >= 0 -> prime_exp_pair.

Inductive prime_power_list :=
  | ppl_intro : forall (pairs : Ensemble prime_exp_pair), Finite _ pairs -> prime_power_list.

Fixpoint ppl_product (ppl : prime_power_list) : Z :=
  match ppl with
    | ppl_intro _ fin => match fin with
                           | Empty_is_finite => 1
                           | Union_is_finite ppl' pairs' x nin => 1
                         end
  end.

Theorem fundamental_theorem_of_arithmetic : forall n : nat