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
Lemma left_not_or : forall P1 P2 : Prop,  (P1 \/ P2) -> (P1 -> False) -> P2. intuition. Qed.
Lemma right_not_or : forall P1 P2 : Prop, (P1 \/ P2) ->(P2 -> False)  -> P1. intuition. Qed.
Hint Extern 1 => match goal with
                   | [H:((_ -> False) -> False)|- _] => (apply NNPP in H )
                   | [H: (_ -> _ -> _ ) -> _ |- _] => apply imply_to_and in H
                   | [H: ~ (_) |- _ ] => unfold not in H
                   | [H: _ /\ _ |- _ ] => decompose [and] H; clear H
                   | [H: exists _, _ |- _ ] => destruct H
                   | [H: (forall _, _) -> False |- _ ] => apply not_all_ex_not in H
                   | [H: _ \/ _ |- _ ] => apply left_not_or in H; intuition
                   | [H: _ \/ _ |- _ ] => apply right_not_or in H; intuition
                 end.
Hint Extern 1 => match goal with
                   | [H: (_ /\ _) -> False |- _] => apply not_and_or in H
                 end.

Lemma not_prime_divisible : forall z, z > 1 -> ~ (prime z) -> exists x, 1 < x < z /\ (x | z).
  intros.
  assert (~ prime' z);
  destruct (prime_alt z);
  intuition;
  unfold prime' in H1.
  eauto 15.
Qed.

Hint Resolve not_prime_divisible.

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

Theorem prime_divis : forall n, n > 1 -> exists p, prime p /\ (p | n).
  assert (forall k n, n <= k -> n > 1 -> exists p, prime p /\ (p | n)).
  apply (Zind (fun k => forall n, n <= k -> n > 1 -> exists p, prime p /\ (p | n))).
  crush.
  crush.
  destruct (prime_dec n).
  exists n; crush.
  pose (not_prime_divisible H1 n0).
  destruct e.
  specialize (H x0).
  rewrite <- Zsucc_succ' in H0.
  destruct H2.
  assert (exists p : Z, prime p /\ (p | x0)) by (apply H; crush).
  destruct H4.
  destruct H4.
  exists x1.
  crush.
  eapply Zdivide_trans; eauto.
  intros.
  apply H.
  rewrite <- Zpred_pred' in H0.
  pose (Zle_pred x).
  crush.
  assumption.
  intros.
  specialize (H n n).
  crush.
Qed.

Require Import MSets.

Module PEP.
  Inductive prime_exp_pair := pep_intro : forall p e, prime p -> e >= 0 -> prime_exp_pair.

  Definition pair_to_prime (pep : prime_exp_pair) : sig prime :=
    match pep with
      | pep_intro p _ pf _ => exist prime p pf
    end.
  
  Definition t := prime_exp_pair.
  
  Definition pep_to_pair (pep : t) : Z * Z :=
    match pep with
      | pep_intro p e _ _ => (p, e)
    end.
  
  Definition eq := @eq t.
  Definition eq_equiv : Equivalence eq := eq_equivalence.
  
  Theorem eq_dec : forall x y : t, {x = y} + {x <> y}.
    intros.
    destruct x.
    destruct y.
    destruct (Z_eq_dec p p1);
      destruct (Z_eq_dec e e0).
    left.
    subst.
    assert (p0 = p2) by (apply proof_irrelevance).
    assert (z0 = z) by (apply proof_irrelevance).
    crush.
    right; crush.
    right.
    intro.
    inversion H.
    crush.
    right; crush.
  Qed.

  Definition pep_value (pep : t) : Z :=
    let (p, e) := pep_to_pair pep in p ^ e.  
End PEP.

Module PPL.
  Include MSetWeakList.Make PEP.

  Axiom unique_first : forall s n, (is_empty s = true) \/ cardinal (filter (fun x : PEP.t => Zeq_bool (fst (PEP.pep_to_pair x)) n) s) = (S O).

  Definition ppl_product (ppl : PPL.t) : Z :=
    fold_left Zmult (map PEP.pep_value (elements ppl)) 1.
End PPL.

Theorem all_ppl : forall n : Z, n >= 1 -> exists ppl : PPL.t, PPL.ppl_product ppl = n.
  assert (forall k n, n <= k -> n >= 1 -> exists ppl : PPL.t, PPL.ppl_product ppl = n).
  apply (Zind (fun k => forall n, n <= k -> n >= 1 -> exists ppl : PPL.t, PPL.ppl_product ppl = n)).
  crush.
  intros.
  rewrite <- Zsucc_succ' in H0.
  destruct (Z_le_lt_eq_dec 1 n).
  crush.
  apply Zlt_gt in z.
  pose (prime_divis z).
  destruct e.
  destruct H2.
  destruct H3.
  destruct (H q).
  assert (q | n).
  crush.
  pose (Zdivide_bounds q n).



  
  exists PPL.empty.
  crush.