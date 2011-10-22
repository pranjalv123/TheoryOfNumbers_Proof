Require Import CpdtTactics.
Require Import List.
Require Import Znumtheory.
Require Import BinInt.

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

Theorem all_prod_primes : forall n, n > 2 -> prod_primes n.
  apply (Zind (fun n => n>2 -> prod_primes n));  crush.
  
  

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
  rewrite <- (Zmult_assoc v a b) in H2.
  rewrite H0 in H2.
  rewrite (Zmult_assoc v q p) in H2.
  rewrite <- (Zmult_assoc u p b) in H2.
  rewrite (Zmult_comm p b) in H2.
  rewrite (Zmult_assoc) in H2.
  rewrite <- (Zmult_plus_distr_l) in H2.
  symmetry in H2.
  pose (Zdivide_intro p b (u * b + v * q)).
  auto.
Qed.

Theorem fundamental_theorem_of_arithmetic : 

(*Inductive divides : nat -> nat -> Prop :=
  div : forall a b, (exists x, b = a * x) -> divides a b.

Hint Constructors divides.

Theorem div5_15 : divides 5 15.
  constructor.
  crush.
  exists 3.
  crush.
Qed.

Hint Resolve mult.

Notation "( a | b )" := (divides a b).

Lemma div_add : forall a b c, (a | b) -> (a | c) -> (a | (b + c)).
  intros.
  constructor.
  destruct H.
  destruct H0.
  destruct H.
  destruct H0.
  subst.
  exists (x + x0).
  rewrite mult_plus_distr_l.
  reflexivity.
Qed.

Lemma div_mult : forall a b c, (a | b) -> (a | b * c).
  intros.
  destruct H.
  constructor.
  destruct H.
  exists (x * c); crush.
Qed.

Hint Resolve div_add div_mult.

Theorem div_lin_comb : forall a b c x y, (a | b) -> (a | c) -> (a | b * x + c * y).
  intros.
  apply div_add; crush.
Qed.

Lemma div_bound : forall a b, (a | b) -> b > 0 -> a <= b.
  intros.
  destruct H.
  destruct H.
  destruct x.
  crush.
  rewrite mult_comm in H.
  crush.
Qed.

Theorem div_dec : forall a b, (a | b) \/ ~(a | b).
  

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'YesT'" := (inleft _ _).
Notation "'NoT'" := (inright _ _).

Fixpoint gcd (a b : nat) : nat :=
  match (le_lt_dec a b) with
    | left _ => gcd a (b - a)
    | right _ => gcd b (a - b)
  end.

Inductive prime : nat -> Prop :=
  pr_intro : forall a p, ((a | p) -> (a = 1) \/ (a = p)) -> prime p.


  
Lemma def_divides : forall a b, divides a b -> (exists x, b = a * x).
  intros.
  

Theorem T1_1_a : forall a b c, divides a b -> divides a (b*c).
  crush.
  constructor.
  assert (exists y, b = a * y). *)