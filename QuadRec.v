Require Import CpdtTactics.
Require Import ZArith.
Require Import Znumtheory.
Load Zadditions.
Load Congruences.

Open Scope Z_scope.
Set Implicit Arguments.

Definition qr_by (m a x : Z) : Prop := x * x == a (mod m).
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

Ltac unf_crush := autounfold with *; crush.

Lemma qr_dec : forall m (mge0 : 0 < m) a, {qr mge0 a} + {forall x, ~ x * x == a (mod m)}.
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

Hint Rewrite Zmod_mod : cpdt.
Lemma sum_nm_Z_mod : forall n m f p, 0 <= n -> sum_nm_Z n m f == sum_nm_Z n m (fun x => (f x) mod p) (mod p).
  intros.
  unfold sum_nm_Z.
  unfold eqm.
  apply Zle_ge in H.
  generalize n H.
  apply Zind_ge0.
  crush.
  intros.
  unfold sum_nm_Z.
  change (Zsucc n0) with (n0 + 1).
  rewrite (Zabs_nat_Zplus).
  simpl.
  rewrite nat_of_P_xH.
  rewrite plus_comm.
  change (1 + Zabs_nat n0)%nat with (S (Zabs_nat n0)).
  do 2 rewrite sum_nm_f.
  apply Zplus_eqm.
  crush.
  unfold eqm.
  crush.
  omega.
  omega.
Qed.

Lemma elim_match : forall z : Z, match z with
                                   | Z0 => Z0
                                   | Zpos z' => Zpos z'
                                   | Zneg z' => Zneg z'
                                 end = z.
  destruct z; crush.
Qed.

Lemma Zabs_nat_0 : forall z, Zabs_nat z = 0%nat -> z = 0.
  destruct z; crush.
  destruct (ZL4 p).
  crush.
Qed.

Hint Rewrite Zabs_nat_Zsucc.
Lemma fact_divide : forall p, 0 < p -> (p | Z_of_nat (fact (Zabs_nat p))).
  intros.
  assert (p >= 1) by omega.
  generalize p H0.
  apply (Zind_ge_m).
  crush.
  intros.
  SearchAbout (Zabs_nat (Zsucc _)).
  rewrite Zabs_nat_Zsucc; try omega.
  simpl.
  rewrite <- (mult_1_l (fact (Zabs_nat n))) at 1.
  rewrite <- (mult_plus_distr_r).
  change (1 + Zabs_nat n)%nat with (S (Zabs_nat n)).
  rewrite <- Zabs_nat_Zsucc.
  rewrite inj_mult.
  rewrite <- Zabs_convert.
  crush.
  omega.
  omega.
Qed.

Lemma Zind_bounded_weak : forall (P : Z -> Prop) m p, P m -> (forall n, m < n < p -> (P (Zpred n)) -> P n) -> (forall n, m <= n < p -> P n).
  intros.
  assert (forall n, n >= m -> n < p -> P n).
  apply (Zind_ge_m (fun n0 => n0 < p -> P n0)).
  crush.
  intros.
  assert (n0 < p) by omega.
  apply H0.
  omega.
  rewrite <- Zpred_succ; crush.
  apply H2; crush.
Qed.

Hint Rewrite Zabs_nat_Zsucc : cpdt.
Hint Resolve Zlt_0_le_0_pred.
Lemma not_fact_divide : forall p, prime p -> forall k, 0 < k < p -> ~ (p | Z_of_nat (fact (Zabs_nat k))).
  intros.
  assert (1 <= k < p) by omega.
  generalize k H1.
  apply Zind_bounded_weak.
  crush.
  apply Zdivide_1 in H2.
  crush.
  intros.
  rewrite (Zsucc_pred n).
  autorewrite with cpdt.
  simpl.  
  rewrite <- (mult_1_l (fact (Zabs_nat (Zpred n)))) at 1.
  rewrite <- (mult_plus_distr_r).
  intro.
  rewrite inj_mult in H4.
  destruct (prime_mult _ H _ _ H4); try tauto.
  rewrite inj_plus in H5.
  rewrite <- Zabs_convert in H5.
  rewrite inj_S in H5.
  unfold Z_of_nat in H5.
  rewrite Zplus_succ_l in H5.
  change (0 + _) with (Zpred n) in H5.
  rewrite <- (Zsucc_pred n) in H5.
  pose (Zdivide_bounds _ _ H5).
  do 2 rewrite Zabs_eq in z; omega.
  crush.
  crush.
Qed.

Lemma binomial_prime_divide : forall p, prime p -> forall k, 0 < k -> k < p -> (p | binomial_Z p k).
  intros.
  unfold binomial_Z.
  pose (binomial_fact (Zabs_nat (p - k)) (Zabs_nat k)).
  rewrite <- Zabs_nat_Zplus in e; try omega.
  rewrite Zplus_minus in e.
  assert (0 < p) by omega.
  pose (fact_divide H2).
  rewrite <- e in z.
  destruct (prime_mult _ H _ _ z); try assumption.
  elimtype False.
  destruct (prime_mult _ H _ _ H3).
  apply (not_fact_divide H) with (k := k); crush.
  apply (not_fact_divide H) with (k := p - k); crush.
Qed.
  
Hint Rewrite Zminus_0_r nat_of_P_xH inj_S inj_0 nat_of_P_o_P_of_succ_nat_eq_succ : cpdt.
Hint Rewrite Zpower_1_r Zpower_1_l Zpower_0_l Zpower_0_r Zminus_diag : cpdt.
Hint Rewrite binomial_def1 binomial_def3 : cpdt.
Hint Rewrite elim_match Zmult_1_r Zmult_1_l : cpdt.
Theorem fermats_little' : forall a p, 0 <= a -> prime p -> a ^ p == a (mod p).
  intros.
  apply (Zind_ge0 (fun a => a ^ p == a (mod p))); try omega.
  rewrite Zpower_0_l; crush.
  destruct H0; omega.
  intros.
  change (Zsucc n) with (n + 1).
  pose H0; destruct p0.
  rewrite binomial_theorem; try omega.
  rewrite sum_nm_Z_mod; try omega.
  unfold sum_nm_Z.
  simpl.
  case_eq (Zabs_nat p).
  intros.
  crush.
  assert (Zabs_nat 1 < Zabs_nat p)%nat.
  apply Zabs_nat_lt; omega.
  elimtype False.
  crush.
  intros.
  rewrite sum_nm_i.
  case_eq n0.
  assert (Zabs_nat 1 < Zabs_nat p)%nat by (apply Zabs_nat_lt; omega).
  intros.
  elimtype False.
  simpl in H6.
  rewrite nat_of_P_xH in H6.
  crush.
  intros.
  rewrite sum_nm_f.
  apply Zplus_eqm.
  autorewrite with cpdt in *; try omega.
  simpl.
  unfold binomial_Z.
  repeat (autorewrite with cpdt in *; simpl).
  unfold eqm in *.
  crush.
  change 1 with (0 + 1) at 3.
  apply Zplus_eqm.
  rewrite <- (sum_nm_ext _ _ (fun _ => 0)).
  generalize n1.
  induction n2.
  crush.
  rewrite sum_nm_f.
  crush.
  intros.
  symmetry.
  apply Zdivide_mod.
  apply Zdivide_mult_l.
  apply binomial_prime_divide; try assumption.
  crush.
  rewrite (Zabs_convert p); try omega.
  apply (inj_lt (1 + x) (Zabs_nat p)).
  omega.
  subst n0.
  change (1 + S n1)%nat with (S (S n1)).
  rewrite <- H5.
  rewrite <- Zabs_convert; try omega.
  rewrite Zminus_diag.
  unfold binomial_Z, eqm.
  crush.
Qed.

Hint Rewrite Zpower_2 Zmult_opp_opp : cpdt.
Lemma Zsqr_opp : forall a, (- a) ^ 2 = a ^ 2.
  intros.
  autorewrite with cpdt in *.
  reflexivity.
Qed.

Lemma Zpower_even_opp : forall a e, 0 <= e -> (2 | e) -> (- a) ^ e = a ^ e.
  intros.
  destruct H0.
  subst e.
  rewrite Zmult_comm.
  repeat rewrite Zpower_mult; try omega.
  f_equal.
  apply Zsqr_opp.
Qed.

Lemma Zmod_2_dec : forall n, {n mod 2 = 0} + {n mod 2 = 1}.
  intros.
  destruct (Z_mod_lt n 2); try omega.
  destruct (Z_le_lt_eq_dec _ _ H).
  right; omega.
  left; omega.
Qed.

Hint Rewrite Zpower_even_opp : cpdt.
Lemma Zpower_odd_opp : forall a e, 0 <= e -> ~ (2 | e) -> (- a) ^ e = - (a ^ e).
  intros.
  destruct (Z_le_lt_eq_dec _ _ H).
  destruct (Zmod_2_dec e).
  elimtype False.
  apply H0.
  apply Zmod_divide; crush.
  assert ((e - 1) mod 2 = 0).
  rewrite Zminus_mod.
  crush.
  rewrite <- (Zplus_minus 1 e).
  repeat rewrite Zpower_exp; try omega.
  repeat rewrite Zpower_1_r.
  rewrite Zopp_mult_distr_l.
  apply Zmod_divide in H1; try omega.
  crush.
  elimtype False.
  apply H0.
  apply Zmod_divide; crush.
Qed.

Theorem odd_prime : forall p, prime p -> 2 < p -> ~ (2 | p).
  intros.
  intro.
  apply prime_alt in H.
  destruct H.
  apply (H2 2); crush.
Qed.

Hint Rewrite Zmod_0_r : cpdt.
Lemma Zopp_eqm : forall m a b, -a == -b (mod m) -> a == b (mod m).
  intros.
  destruct (Z_eq_dec m 0).
  unfold eqm.
  crush.
  apply cong_equiv in H; [ | assumption ].
  unfold Zminus in H.
  rewrite <- Zopp_plus_distr in H.
  apply Zdivide_opp_r_rev in H.
  change (a + - b) with (a - b) in H.
  apply cong_equiv; assumption.
Qed.

Lemma Zsqr_idemp_mod2 : forall a, a ^ 2 == a (mod 2).
  intro.
  unfold eqm.
  rewrite Zpower_2.
  rewrite Zmult_mod.
  destruct (Zmod_2_dec a); rewrite e; crush.
Qed.

Hint Resolve not_prime_0 not_prime_1 odd_prime.
Theorem fermats_little : forall p, prime p -> forall a, a ^ p == a (mod p).
  intros.
  destruct (Z_lt_le_dec a 0).
  destruct (Z_le_lt_eq_dec 2 p (prime_ge_2 _ H)).
  assert (0 <= -a) by omega.
  pose (fermats_little' H0 H).
  apply Zopp_eqm.
  eapply eqm_trans; try apply (fermats_little' H0 H).
  rewrite Zpower_odd_opp; crush.
  apply (odd_prime H); crush.
  subst p.
  apply Zsqr_idemp_mod2.
  apply fermats_little'; assumption.
Qed.