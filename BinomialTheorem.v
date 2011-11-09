(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

(**  Modified proofs from two projects: *)

(** 1*)
(**  Correctness of RSA algorithm proofs, by Jose C. Almeida *)
(**  and Laurent Thery, INRIA Sophia Antipolis and University of Minho *)
(**  1999 *)
(**  http://coq.inria.fr/contribs/RSA.html *)
(**  https://gforge.inria.fr/projects/coq-contribs/ *)

(**  2*)
(**  Library for floating point numbers, by Laurent Thery and Sylvie Boldo *)
(**  INRIA Sophia-Antipolis and ENS Lyon *)
(**  2001 *)
(**  http://coq.inria.fr/contribs/Float.html *)
(**  https://gforge.inria.fr/projects/coq-contribs/ *)

(**  from "nat" to "Z"  , and other things  *)

(** 	Modifier: Ricardo Peixoto    				*)
(** 	Supervisor: Flavio de Moura 				*)
(** 	UnB-Brazil            				        	*)
(** 	http://www.cic.unb.br/~flavio/english.html 	*)

(**   Included in TheoryOfNumber_proof by    *)
(**   Patrick Hulin and Pranjal Vachaspati    *)
(**   with some deletions and addition    *)

(**  Part from Proof of AKS Primality Test *)

Require Import ZArith.
Require Import Zpow_facts.
Require Import Znumtheory.
Require Import CpdtTactics.

(***********************************************************************
**********************************************************************
**********************************************************************

	ITERATED SUMS
*)

Fixpoint sum_nm (n : nat) : nat -> (nat -> Z) -> Z :=
  fun (m : nat) (f : nat -> Z) =>
  match n with
  | O => f m
  | S n' => (f m + sum_nm n' (S m) f)%Z
  end.

Lemma sum_nm_i :
 forall (m n : nat) (f : nat -> Z),
 sum_nm (S n) m f = (f m + sum_nm n (S m) f)%Z.
auto.
Qed.

Lemma sum_nm_f :
 forall (m n : nat) (f : nat -> Z),
 sum_nm (S n) m f = (sum_nm n m f + f (m + S n)%nat)%Z.
intros m n f; generalize m; clear m; elim n; simpl in |- *; intros.
rewrite (plus_comm m); auto.
rewrite H; repeat (rewrite (plus_comm m); simpl in |- *).
omega.
Qed.

Lemma sum_nm_ext :
 forall (m n : nat) (f g : nat -> Z),
 (forall x : nat, (x <= n)%nat -> f (m + x)%nat = g (m + x)%nat) ->
 sum_nm n m f = sum_nm n m g.
intros m n f g; generalize m; clear m; elim n; simpl in |- *; intros.
rewrite (plus_n_O m); auto.
rewrite H; auto.
rewrite (plus_n_O m); auto.
rewrite H0; auto with arith.
intros x H'; simpl in |- *; rewrite plus_n_Sm; auto with arith.
Qed.

Lemma sum_nm_add :
 forall (m n : nat) (f g : nat -> Z),
 (sum_nm n m f + sum_nm n m g)%Z = sum_nm n m (fun i : nat => (f i + g i)%Z).
intros m n f g; generalize m; elim n; auto; intros; simpl in |- *.
rewrite <- H.
repeat rewrite Zplus_assoc_reverse; apply (f_equal2 (A1:=Z) (A2:=Z)); auto with zarith.
Qed.

Lemma sum_nm_times :
 forall (m n: nat) (x : Z) (f : nat -> Z),
 (x * sum_nm n m f)%Z = sum_nm n m (fun i : nat => (x * f i)%Z).
intros m n x f; generalize m; elim n; auto; intros; simpl in |- *.
rewrite <- H; auto with arith.
repeat rewrite (Zmult_comm x); auto.
rewrite Zmult_plus_distr_l; auto.
Qed.

Lemma inv_sum_nm :
 forall (P : Z -> Prop) (n i : nat) (f : nat -> Z),
 (forall a b : Z, P a -> P b -> P (a + b)%Z) ->
 (forall x : nat, (x <= n)%nat -> P (f (i + x)%nat)) -> P (sum_nm n i f).
intros P i n f; generalize n; clear n. elim i; clear i; intros; simpl in |- *.
rewrite (plus_n_O n); auto with zarith.
apply H0; auto.
rewrite (plus_n_O n0); auto with arith.
apply H; auto.
intros x H'; simpl in |- *; rewrite plus_n_Sm; auto with arith.
Qed.

Lemma t_sum_Svars :
 forall (n k : nat) (f : nat -> Z),
 sum_nm k n f = sum_nm k (S n) (fun i : nat => f (pred i)).
intros n k f; generalize n; elim k; auto; intros; simpl in |- *.
rewrite <- H; auto.
Qed.

(*
	BINOMIAL
*)

Fixpoint binomial (a: nat): nat  -> Z :=
  fun b : nat =>
  match a, b with
  | _, O => 1%Z
  | O, S b' => 0%Z
  | S a', S b' => (binomial a' (S b') + binomial a' b')%Z
  end.

Lemma binomial_def1 : forall n : nat, binomial n 0 = 1%Z.
simple induction n; auto.
Qed.

Lemma binomial_def2 : forall n m : nat, (n < m)%nat -> binomial n m = 0%Z.
simple induction n; simpl in |- *; auto.
intros m; case m; simpl in |- *; auto.
intros H'; inversion H'; auto.
intros n0 H' m; case m; simpl in |- *; auto.
intros H'0; inversion H'0; auto.
intros n1 H'0.
rewrite H'; auto with arith.
rewrite H'; auto with arith.
Qed.

Lemma binomial_def3 : forall n : nat, binomial n n = 1%Z.
simple induction n; intros; simpl in |- *; auto.
rewrite (binomial_def2 n0 (S n0)); auto.
Qed.

Lemma binomial_def4 :
forall n k : nat, (k < n)%nat -> binomial (S n) (S k) = (binomial n (S k) + binomial n k)%Z.
simpl in |- *; auto.
Qed.

Lemma binomial_fact :
forall m n : nat,
binomial (n + m) n  * (Z_of_nat(fact n) * Z_of_nat(fact m))%Z = Z_of_nat(fact (n + m)).
intros m; elim m; clear m.
intros.
simpl.
replace (n+0)%nat with n; auto with zarith.
rewrite binomial_def3; auto with zarith.
intros m H' n; elim n; clear n.
simpl (fact 0); simpl (0+S m)%nat; simpl (Z_of_nat 1).
rewrite binomial_def1; auto with zarith.
intros n H'0.
replace (S n + S m)%nat with (S (S n + m)); [ idtac | simpl in |- * ]; auto.
rewrite binomial_def4;
 [ idtac | rewrite plus_comm; simpl in |- *; rewrite plus_comm ];
 auto with arith.
rewrite Zmult_plus_distr_l.
apply
 (trans_equal (A:=Z))
  with (y := Z_of_nat (fact (S n + m)) * Z_of_nat (S m) + Z_of_nat (fact (n + S m))
 * Z_of_nat (S n)).
apply f_equal2 with (A1 := Z) (A2 := Z); auto.
rewrite <- H'.
repeat rewrite Zmult_assoc_reverse; rewrite (Zmult_comm (Z_of_nat (fact m))).
replace (fact (S m)) with (S m * fact m)%nat; auto with zarith.
rewrite inj_mult; auto with zarith.
rewrite <- H'0.
rewrite <- plus_n_Sm; auto.
rewrite Zmult_assoc_reverse; rewrite Zmult_comm with (m := Z_of_nat (S n));
 rewrite (Zmult_assoc (Z_of_nat(S n))).
replace (fact (S n)) with (S n * fact n)%nat; auto with zarith.
rewrite inj_mult; auto with zarith.
apply (trans_equal (A:=Z)) with (y := Z_of_nat ((S m + S n)) * Z_of_nat (fact (S n + m))).
rewrite inj_plus.
rewrite Zmult_plus_distr_l; apply f_equal2 with (A1 := Z) (A2 := Z).
rewrite (Zmult_comm (Z_of_nat (S m))); auto with zarith.
rewrite (Zmult_comm (Z_of_nat (S n))); rewrite <- plus_n_Sm; auto.
rewrite (plus_comm (S m)); rewrite <- plus_n_Sm; auto.
replace (fact (S (S n + m))) with ((S (S n + m)) * fact (S n + m))%nat; auto with zarith.
rewrite inj_mult.
auto with zarith.
Qed.

Theorem exp_Pascal :
 forall (a b:Z) (n: nat),
 Zpower_nat (a + b) n =
 sum_nm n 0 (fun k : nat => binomial n k * (Zpower_nat a (n - k) * Zpower_nat b k))%Z.
simple induction n; auto.
intros n0; case n0.
unfold sum_nm.
unfold binomial.
repeat rewrite <- minus_n_n.
rewrite <- minus_n_O.
rewrite Zplus_0_l.
repeat rewrite Zmult_1_l.
unfold Zpower_nat.
unfold iter_nat; auto with zarith.
intros n1 H'.
apply trans_equal with (y := ((a + b)%Z * Zpower_nat (a + b) (S n1))%Z).
simpl in |- *; auto.
rewrite H'; rewrite Zmult_plus_distr_l; repeat rewrite sum_nm_times.
rewrite sum_nm_i; rewrite binomial_def1.
replace (1 * (Zpower_nat a (S n1 - 0) * Zpower_nat b 0))%Z with (Zpower_nat a (S n1));
 [ idtac
 | rewrite Zmult_comm with (m := 1%Z);
    repeat rewrite Zplus_comm with (m := 0) ]; auto with zarith.
rewrite sum_nm_f; rewrite binomial_def3.
replace (S n1 - (0 + S n1))%nat with 0%nat;
 [ idtac | simpl in |- *; auto with zarith]. 
replace (Zpower_nat a 0) with 1%Z; auto.
replace (b * (1 * (1 * Zpower_nat b (0 + S n1))))%Z with (b * Zpower_nat b (S n1))%Z;
 [ idtac | repeat rewrite <- Zplus_n_O ]; 
 auto.
rewrite (t_sum_Svars 0 n1).
replace
 (a * Zpower_nat a (S n1) +
  sum_nm n1 1
    (fun z : nat =>
     a * (binomial (S n1) z * (Zpower_nat a (S n1 - z) * Zpower_nat b z)))+
  (sum_nm n1 1
     (fun x : nat =>
      b *
      (binomial (S n1) (pred x) *
       (Zpower_nat a (S n1 - pred x) * Zpower_nat b (pred x)))) + 
   b * Zpower_nat b (S n1)))%Z with 
 (Zpower_nat a (S (S n1)) +
  (sum_nm n1 1
     (fun x : nat =>
      binomial (S (S n1)) x * (Zpower_nat a (S (S n1) - x) * Zpower_nat b x)) +
   Zpower_nat b (S (S n1))))%Z.
rewrite (sum_nm_i 0); rewrite (sum_nm_f 1).
rewrite binomial_def1; rewrite binomial_def3.
replace (S (S n1) - 0)%nat with (S (S n1))%nat; auto.
replace (S (S n1) - (1 + S n1))%nat with 0%nat; auto with arith.
replace (Zpower_nat a 0) with 1%Z; auto.
replace (Zpower_nat b 0) with 1%Z; auto.
replace (1 * (Zpower_nat a (S (S n1)) * 1))%Z with (Zpower_nat a (S (S n1)));
 [ idtac
 | repeat rewrite Zmult_comm with (m := 1);
    repeat rewrite Zplus_comm with (m := 0)];
 auto with zarith.
replace (1 + S n1)%nat with (S (S n1))%nat; auto.
replace (1 * (1 * Zpower_nat b (S (S n1))))%Z with (Zpower_nat b (S (S n1)));
 [ idtac
 | repeat rewrite Zmult_comm with (m := 1%Z)];
 auto with zarith.
repeat rewrite Zplus_assoc_reverse; apply (f_equal2 Zplus); auto.
repeat rewrite Zplus_assoc; apply (f_equal2 Zplus); auto.
rewrite sum_nm_add.
apply sum_nm_ext.
intros x H'0.
replace (pred (1 + x)) with x; [ idtac | auto ].
replace (S (S n1) - (1 + x))%nat with (S n1 - x)%nat; [ idtac | auto ].
replace (S n1 - (1 + x))%nat with (n1 - x)%nat; [ idtac | auto ].
replace (1 + x)%nat with (S x); [ idtac | auto ].
rewrite (binomial_def4 (S n1)); auto with arith.
rewrite Zmult_plus_distr_l.
apply (f_equal2 Zplus).
repeat rewrite Zmult_assoc; apply (f_equal2 Zmult); auto.
rewrite (Zmult_comm a); repeat rewrite Zmult_assoc_reverse; 
apply (f_equal2 Zmult); auto with zarith.
rewrite <- minus_Sn_m; simpl in |- *; auto with zarith.
rewrite (Zmult_comm b); repeat rewrite Zmult_assoc_reverse;
apply (f_equal2 Zmult); auto with zarith.
apply (f_equal2 Zmult); auto with zarith.
rewrite Zmult_comm; auto with zarith.
repeat rewrite Zmult_1_l; auto with zarith.
repeat rewrite Zmult_1_l; auto with zarith.
Qed.

Hint Immediate Zpos_eq_Z_of_nat_o_nat_of_P.
Lemma Zabs_convert : forall n, 0 <= n -> n = Z_of_nat (Zabs_nat n).
  intros.
  destruct n; simpl; eauto.
  elimtype False.
  pose (Zlt_neg_0 p).
  omega.
Qed.

Hint Immediate nat_of_P_o_P_of_succ_nat_eq_succ.
Lemma Zabs_cancel : forall n, Zabs_nat (Z_of_nat n) = n.
  destruct n; crush.
Qed.

Hint Rewrite Zabs_cancel Zpos_eq_Z_of_nat_o_nat_of_P Zpower_nat_Zpower : cpdt.

Definition binomial_Z (n : Z) (k : Z) : Z :=
  binomial (Zabs_nat n) (Zabs_nat k).

Definition sum_nm_Z (n m : Z) (f : Z -> Z) :=
  sum_nm (Zabs_nat n) (Zabs_nat m) (fun k => f (Z_of_nat k)).

Theorem binomial_theorem : forall a b n, 0 <= n -> (a + b) ^ n = sum_nm_Z n 0 (fun k => binomial_Z n k * (Zpower a (n - k) * Zpower b k)).
  intros.
  destruct n.
  crush.
  pose (exp_Pascal a b (Zabs_nat (Zpos p))).
  rewrite (Zpower_nat_Zpower _ _ H).
  unfold sum_nm_Z.
  unfold binomial_Z.
  rewrite e.
  unfold Zabs_nat at 1 2 3 4 5 6.
  apply sum_nm_ext.
  intros.
  change (0 + x)%nat with x.
  rewrite Zabs_cancel.
  f_equal.
  assert (0 <= Zpos p - Z_of_nat x).
  apply inj_le in H0.
  rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
  omega.
  rewrite (Zpower_nat_Zpower); try assumption.
  rewrite (Zpower_nat_Zpower).
  f_equal.
  rewrite Zabs_nat_Zminus.
  crush.
  omega.
  crush.
  crush.
  elimtype False.
  pose (Zlt_neg_0 p).
  omega.
Qed.