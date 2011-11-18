Require Import CpdtTactics.
Require Import ZArith.
Require Import Znumtheory.
Require Import List.
Require Import Arith.
Require Import Div2.
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

Hint Rewrite Zmod_mod nat_of_P_xH : cpdt.
Lemma sum_nm_Z_mod : forall n m f p, 0 <= n -> sum_nm_Z n m f == sum_nm_Z n m (fun x => (f x) mod p) (mod p).
  intros.
  unfold sum_nm_Z.
  induction_ge_m 0 n.
  ucrush.
  intros.
  unfold sum_nm_Z.
  change (Zsucc n0) with (n0 + 1).
  rewrite (Zabs_nat_Zplus); try omega.
  simpl.
  rewrite plus_comm.
  rewrite nat_of_P_xH.
  change (1 + Zabs_nat n0)%nat with (S (Zabs_nat n0)).
  do 2 rewrite sum_nm_f.
  apply Zplus_eqm; ucrush.
Qed.

Lemma Zabs_nat_0 : forall z, Zabs_nat z = 0%nat -> z = 0.
  destruct z; crush; destruct (ZL4 p); crush.
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
  
Hint Rewrite Zminus_0_r nat_of_P_xH inj_S inj_0 nat_of_P_o_P_of_succ_nat_eq_succ Zpos_P_of_succ_nat : cpdt.
Hint Rewrite Zminus_diag : cpdt.
Hint Rewrite binomial_def1 binomial_def3 : cpdt.
Hint Rewrite elim_match Zmult_1_r Zmult_1_l : cpdt.
Hint Rewrite Zpower_1_l Zpower_1_r Zpower_0_l Zpower_0_r : cpdt.
Theorem fermats_little' : forall a p, 0 <= a -> prime p -> a ^ p == a (mod p).
  intros.
  apply (natlike_ind (fun a => a ^ p == a (mod p))); try omega.
  rewrite Zpower_0_l; crush.
  destruct H0; omega.
  intros.
  unfold Zsucc.
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
  case_eq n.
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
  generalize n0.
  induction n1.
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
  apply (inj_lt (1 + x0) (Zabs_nat p)).
  omega.
  subst n.
  change (1 + S n0)%nat with (S (S n0)).
  rewrite <- H5.
  rewrite <- Zabs_convert; try omega.
  unfold binomial_Z, eqm.
  crush.
Qed.

Hint Rewrite Zpower_2 Zmult_opp_opp : cpdt.
Lemma Zsqr_opp : forall a, (- a) ^ 2 = a ^ 2.
  intros; ring.
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
  destruct (Z_le_lt_eq_dec _ _ H); crush.
Qed.

Hint Rewrite Zpower_even_opp Zpower_Zsucc : cpdt.
Hint Resolve Zmod_divide.
Lemma Zpower_odd_opp : forall a e, 0 <= e -> ~ (2 | e) -> (- a) ^ e = - (a ^ e).
  intros.
  destruct (Z_le_lt_eq_dec _ _ H).
  destruct (Zmod_2_dec e).
  elimtype False.
  apply H0.
  crush.
  assert ((e - 1) mod 2 = 0).
  rewrite Zminus_mod.
  crush.
  replace e with (Zsucc (e - 1)) by omega.
  autorewrite with cpdt; crush.
  rewrite Zopp_mult_distr_l; reflexivity.
  crush.
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

Hint Rewrite Zpower_2.
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

Open Scope nat_scope.
Fixpoint Fp_lower_nat (p : nat) : list nat :=
  match p with
    | S (S p') => div2 (S p') :: Fp_lower_nat p'
    | _ => nil
  end.
Close Scope nat_scope.

Hint Rewrite nat_of_P_succ_morphism Zpos_succ_morphism : cpdt.
Lemma Div2_Zdiv_2 : forall n, Z_of_nat (div2 n) = (Z_of_nat n) / 2.
  apply ind_0_1_SS; crush.
  replace (Zsucc (Zsucc _)) with (Z_of_nat n + 1 * 2) by omega.
  rewrite Z_div_plus_full; crush.
Qed.

Lemma diff_squares : forall a, a ^ 2 - 1 = (a - 1) * (a + 1).
  intros.
  rewrite Zpower_2.
  ring.
Qed.

Section quadratic_reciprocity.
  Variable p : Z.
  Variable pr : prime p.
  Variable pgt2 : 2 < p.
  Definition podd := (odd_prime pr pgt2).
  Lemma pgt0 : 0 < p.
    omega.
  Qed.

  Variable a : Z.
  Variable aprp : ~ a == 0 (mod p).

  Notation "/ a" := (Fp_inv p a).

  Instance def' : (DefaultRelation (eqm p)).

  Instance Fp_inv_comp' : Proper (eqm p ==> eqm p) (Fp_inv p).
    apply Fp_inv_comp; crush.
  Qed.

  Instance Zpower_comp : Proper (eqm p ==> eq ==> eqm p) Zpower.
    unfold Proper; unfold respectful; apply Zpower_mor.
  Qed.

  Instance Fp_power_comp : Proper (eqm p ==> eq ==> eqm p) (Fp_power p).
    unfold Proper; unfold respectful; apply Fp_power_mor; crush.
  Qed.
  
  Add Field Fp' : (Fp_field_theory pr).

  Hint Rewrite Fp_inv_spec : cpdt.
  Theorem fermats_little_strong : a ^ (p - 1) == 1 (mod p).
    intros.
    setoid_replace (a ^ (p - 1)) with (/ a * a ^ p).
    rewrite fermats_little; crush.
    assert (p = (1 + (p - 1))) by omega.
    rewrite H at 4.
    rewrite Zpower_exp; try omega.
    rewrite Zpower_1_r.
    field.
    assumption.
  Qed.
  
  Definition Fp_lower (p : Z) : list Z :=
    map (Z_of_nat) (Fp_lower_nat (Zabs_nat p)).

  Instance def'' : DefaultRelation (@eq Z).
  
  Hint Resolve fermats_little_strong odd_prime.
  Lemma fermats_little_sqrt :
    let r := a ^ ((p - 1) / 2) in r == 1 (mod p) \/ r == -1 (mod p).
    intros.
    assert (r^2 == 1 (mod p)).
    subst r. 
    rewrite <- Zpower_mult; try omega.
    rewrite Zmult_comm.
    rewrite <- (Zdivide_Zdiv_eq); try omega.
    crush.
    destruct (Zmod_2_dec p).
    rewrite <- (Zmod_0_l 2) in e.
    apply cong_equiv in e.
    rewrite Zminus_0_r in e.
    elimtype False.
    apply podd; assumption.
    omega.
    apply cong_equiv; try omega.
    unfold eqm; rewrite e; crush.
    apply Z_div_pos; omega.
    apply cong_equiv in H; try omega.
    rewrite diff_squares in H.
    destruct (prime_mult p pr (r - 1) (r + 1) H); [ left | right ]; apply cong_equiv; crush.
  Qed.

  Notation "a  '^p'  b" := Fp_power a b.

  Inductive Fp_order : Z -> Z -> Prop :=
    | Fp_order_intro : forall b e, 0 < e -> Fp_power p b e == 1 (mod p) -> (forall f, 0 < f < e -> ~ Fp_power p b f == 1 (mod p)) -> Fp_order b e.

  Hint Resolve Zdivide_intro Zplus_eqm.
  Hint Rewrite Zmod_0_l Z_mod_plus_full prime_Zmod_1_l Fp_power_mult Fp_power_0_l Fp_power_0_r Fp_power_1_l Fp_power_1_r : cpdt.
  Hint Rewrite Fp_power_exp Fp_power_mult : cpdt.
  Lemma order_divide : forall h, Fp_order a h -> forall k, (Fp_power p a k == 1 (mod p) <-> (h | k)).
    intros; split; intros.
    destruct H.
    destruct (Ztrichotomy_inf e k).
    destruct s.
    assert (Hegr0 : e > 0) by omega.
    destruct (Zdiv_eucl_exist Hegr0 k).
    destruct x.
    destruct y.
    rewrite H3 in H0.
    destruct H4.
    assert (0 <= z0).
    apply (Zmult_le_0_reg_r e).
    omega.
    assert (0 <= e * z0) by omega.
    rewrite Zmult_comm; assumption.
    destruct (Z_le_lt_eq_dec _ _ H4).
    elimtype False; apply (H2 z1).
    omega.
    rewrite Fp_power_exp, Fp_power_mult, H1 in H0; crush.
    crush.
    crush.
    destruct (Z_lt_le_dec 0 k).
    exfalso.
    apply (H2 k); crush.
    crush.
    destruct H1.
    destruct H.
    rewrite H1.
    rewrite Zmult_comm.
    assert (0 <= q) by (apply (Zmult_le_0_reg_r e q); omega).
    rewrite Zpower_mult; try omega.
    crush.
  Qed.

  
  
  Theorem eulers_criterion_1 : qr pgt0 a <-> Fp_power a ((p - 1) / 2) == 1 (mod p).
    intros; split; intros.
    destruct fermats_little_sqrt; try assumption.
    destruct H.
    elimtype False.
    
End quadratic_reciprocity.

Require Import Ensembles.
Require Import Finite_sets.

Definition Fp_lower (p q : Z) : Ensemble (Z * Z) :=
  fun z => let (x, y) := z in  (1 <= x <= (p - 1) / 2) /\ (1 <= y <= (q - 1) / 2).

Lemma Fp_lower_finite : forall p q, Finite _ (Fp_lower p q).
  intros.
  destruct (Z_lt_le_dec p 1).
  replace (Fp_lower p q) with (Empty_set (Z * Z)).
  apply Empty_is_finite.
  apply Extensionality_Ensembles.
  split.
  unfold Included.
  intros.
  destruct H.
  intros.