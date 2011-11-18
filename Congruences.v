Require Export ZArith.
Require Export Znumtheory.
Require Import Zpow_facts.
Require Import CpdtTactics.
Require Export Field.
Require Import Morphisms Setoid Bool.
Load Zadditions.

Set Implicit Arguments.

(* Congruence modulo n *)
Notation " a == b  (mod  m )" := (eqm m a b) (at level 65, no associativity).

Ltac fcrush := crush; field; crush.
Ltac ucrush := unfold eqm; crush.

Ltac succ_simpl :=
  repeat match goal with
           | [ |- context [ Zsucc ?a + ?b ] ] => replace (Zsucc a + b) with (Zsucc (a + b)) by omega
           | [ |- context [ ?a + Zsucc ?b ] ] => replace (a + Zsucc b) with (Zsucc (a + b)) by omega
           | [ |- context [ Zpred ?a + ?b ] ] => rewrite Zpred_plus_l
           | [ |- context [ ?a + Zpred ?b ] ] => rewrite Zpred_plus_r
         end.

Ltac power_succ_crush := intros; succ_simpl; fcrush.

Hint Rewrite Zminus_diag Z_mod_plus_full : cpdt.
Theorem cong_equiv : forall a b m, m <> 0 -> (a == b (mod m) <-> (m | a - b)).
  intros.
  split; intro.
  apply Zmod_divide; try omega.
  rewrite Zminus_mod.
  crush.
  destruct H0.
  replace a with (b + q * m) by omega.
  ucrush.
Qed.

Lemma Z_mod_dec : forall m a b, { a == b (mod m) } + { ~ a == b (mod m) }.
  intros.
  exact (Z_eq_dec (a mod m) (b mod m)).
Qed.

Section Fp_field_theory.
  Variable p : Z.
  Hypothesis pr : prime p.

  Definition Fp_eq_bool (a b : Z) : bool :=
    Zeq_bool (a mod p) (b mod p).

  Lemma Fp_eq_bool_eqm : forall a b, Fp_eq_bool a b = true -> a == b (mod p).
    intros.
    apply Zeq_is_eq_bool; crush.
  Qed.

  Lemma Fp_eqm_eq_bool : forall a b, a == b (mod p) -> Fp_eq_bool a b = true.
    intros.
    apply Zeq_is_eq_bool; crush.
  Qed.
    
  Theorem Fp_ring_theory : @ring_theory Z 0 1 Zplus Zmult Zminus Zopp (eqm p).
    apply mk_rt; intros.
    crush.
    rewrite (Zplus_comm x y); crush.
    rewrite (Zplus_assoc); crush.
    rewrite (Zmult_1_l); crush.
    rewrite (Zmult_comm); crush.
    rewrite (Zmult_assoc); crush.
    rewrite (Zmult_plus_distr_l); crush.
    unfold Zminus; crush.
    rewrite Zplus_opp_r; crush.
  Qed.

  Add Ring Fp_rt : Fp_ring_theory.

  Definition Fp_inv' (a : Z) : Z :=
    match (euclid a p) with
      | Euclid_intro u v d pf gcd => match d with
                                       | Z0 => 0
                                       | Zpos _ => u
                                       | Zneg _ => - u
                                     end
    end.

  Definition Fp_inv (a : Z) : Z :=
    match (Z_mod_dec p a 0) with
      | Yes => 0
      | No => Fp_inv' a
    end.

  Notation "/ a" := (Fp_inv a) (at level 35, right associativity).
  Hint Unfold Fp_inv.
  
  Lemma Fp_inv_0 : forall a, a == 0 (mod p) -> / a == 0 (mod p).
    intros.
    unfold Fp_inv.
    destruct (Z_mod_dec p a 0); crush.
  Qed.

  Lemma Fp_inv_0_weak : / 0 == 0 (mod p).
    rewrite Fp_inv_0; crush.
  Qed.

  Hint Rewrite Z_mod_plus_full Z_mod_mult : cpdt.
  Lemma Fp_inv_spec : forall a : Z, ~ a == 0 (mod p) -> / a * a == 1 (mod p).
    intros.
    unfold Fp_inv; destruct (Z_mod_dec p a 0).
    tauto.
    clear n.
    unfold Fp_inv'; destruct (euclid a p).
    destruct (Zdivide_dec p a).
    pose pr; destruct p0.
    assert (p <> 0) by omega.
    destruct (cong_equiv a 0 H2).
    crush.
    pose (prime_rel_prime _ pr a n).
    unfold rel_prime in r.
    apply Zis_gcd_sym in r.
    destruct (Zis_gcd_uniqueness_apart_sign _ _ _ _ z r).
    rewrite H0.
    replace 1 with (u * a + v * p) by omega.
    symmetry.
    ucrush.
    rewrite H0.
    unfold Zopp at 1.
    replace (- u * a) with (1 + v * p) by (rewrite <- Zopp_mult_distr_l; omega).
    unfold eqm.
    apply Z_mod_plus_full.
  Qed.

  Instance def : DefaultRelation (eqm p).

  Definition Fp_div a b := a * / b.

  Hint Resolve Fp_inv_0.
  Instance Fp_inv_comp : Proper (eqm p ==> eqm p) Fp_inv.
    unfold respectful.
    unfold Proper.
    intros.
    destruct (Z_mod_dec p y 0).
    assert (x == 0 (mod p)) by (ring [H e]).
    setoid_replace (/ y) with 0; crush.
    pose (Fp_inv_spec n).
    destruct (Z_mod_dec p x 0).
    crush.
    pose (Fp_inv_spec n0).
    setoid_rewrite H in e0 at 2.
    assert ((/ x - / y) * y == 0 (mod p)) by (ring [e0 e]).
    pose pr; destruct p0.
    apply cong_equiv in H0; try omega.
    rewrite Zminus_0_r in H0.
    destruct (prime_mult _ pr _ _ H0).
    apply cong_equiv; crush.
    replace y with (y - 0) in H3 by crush.
    apply cong_equiv in H3; crush.
  Qed.

   Lemma prime_Zmod_1_l : 1 mod p = 1.
    apply Zmod_small; destruct pr; crush.
  Qed.

  Hint Rewrite Zplus_0_r Zplus_0_l Z_mod_mult Zmult_1_r Zmult_1_l Zmult_0_l Zmult_0_r Zmod_0_l Z_mod_plus_full prime_Zmod_1_l : cpdt.
  Theorem Fp_field_theory : field_theory 0 1 Zplus Zmult Zminus Zopp Fp_div Fp_inv (eqm p).
    constructor.
    apply Fp_ring_theory.
    ucrush.
    unfold Fp_div; crush.
    exact Fp_inv_spec.
  Qed.

  Add Field Fp : (Fp_field_theory).

  Lemma Fp_inv_spec_r : forall a, ~ a == 0 (mod p) -> a * / a == 1 (mod p).
    intros; field; crush.
  Qed.

  Hint Rewrite Zpower_Zsucc : cpdt.
  Add Parametric Morphism : Zpower
    with signature (eqm p ==> eq ==> eqm p)
      as Zpower_mor.
    intros.
    destruct (Z_lt_le_dec y0 0).
    pose (Zgt_pos_0); destruct y0; crush.
    apply (natlike_ind (fun y0 => x ^ y0 == y ^ y0 (mod p))); crush.
  Qed.
    
  Lemma Fp_inv_1 : forall a, a == 1 (mod p) -> / a == 1 (mod p).
    intros.
    assert (~ a == 0 (mod p)) by (unfold eqm in *; crush).
    setoid_rewrite <- (@Fp_inv_spec a); crush.
  Qed.

  Lemma Fp_inv_1_weak : / 1 == 1 (mod p).
    apply Fp_inv_1; crush.
  Qed.

  Hint Rewrite Fp_inv_0_weak : cpdt.
  Lemma Fp_inv_involutive : forall a, / (/ a) == a (mod p).
    intros.
    destruct (Z_mod_dec p a 0).
    crush.
    field; unfold eqm; crush.
  Qed.

  Lemma Fp_inv_mult_distr : forall a b, / (a * b) == (/ a) * (/ b) (mod p).
    intros.
    destruct (Z_mod_dec p a 0). crush.
    destruct (Z_mod_dec p b 0). crush.
    field; crush.
  Qed.
    
  Definition Fp_power (a : Z) (e : Z) : Z :=
    match (Z_lt_le_dec 0 e) with
      | No => / (a ^ (- e))
      | Yes => a ^ e
    end.

  Hint Unfold Fp_power.

  Ltac simpl_Fp_power := intros; unfold Fp_power;
                           match goal with
                             | [ |- context [if ?h then _ else _] ] => destruct h
                           end.

  Ltac solve_Fp_power := simpl_Fp_power; simpl; unfold Zpower_pos; crush.

  Hint Rewrite Zpower_0_l : cpdt.
  Lemma Fp_power_0_l : forall e, e <> 0 -> Fp_power 0 e == 0 (mod p).
    solve_Fp_power.
  Qed.

  Hint Rewrite Fp_inv_1_weak : cpdt.
  Hint Immediate eqm_refl.
  Lemma Fp_power_0_r : forall a, Fp_power a 0 == 1 (mod p).
    solve_Fp_power.
  Qed.

  Hint Rewrite Zpower_1_l : cpdt.
  Lemma Fp_power_1_l : forall e, Fp_power 1 e == 1 (mod p).
    solve_Fp_power.
  Qed.

  Hint Rewrite Zpower_pos_1_r : cpdt.
  Lemma Fp_power_1_r : forall a, Fp_power a 1 == a (mod p).
    solve_Fp_power.
  Qed.

  Hint Rewrite Fp_inv_involutive Fp_inv_mult_distr Fp_power_1_l Fp_power_1_r : cpdt.
  Hint Resolve Zmult_eqm.

  Lemma Fp_power_inv_opp : forall a e, Fp_power (/ a) (- e) == Fp_power a e (mod p).
    intros.
    unfold Fp_power.
    destruct (Z_lt_le_dec 0 e); destruct (Z_lt_le_dec 0 (-e)); try (elimtype False; omega); try rewrite Zopp_involutive.
    apply (natlike_ind (fun e => / (/ a) ^ e == a ^ e (mod p))); crush.
    apply (natlike_ind (fun e0 => (/ a) ^ e0 == / a ^ e0 (mod p))); crush.
    assert (e = 0) by omega; crush.
  Qed.

  Hint Rewrite Fp_power_inv_opp : cpdt.
  Lemma Fp_power_inv_opp_2 : forall a e, Fp_power (/ a) e == Fp_power a (- e) (mod p).
    intros.
    rewrite <- (Zopp_involutive e) at 1.
    crush.
  Qed.
  Hint Rewrite Fp_power_inv_opp_2 : cpdt.

  Lemma Fp_power_2 : forall a, Fp_power a 2 == a * a (mod p).
    solve_Fp_power.
  Qed.

  Lemma elim_match : forall z : Z, match z with
                                     | Z0 => Z0
                                     | Zpos z' => Zpos z'
                                     | Zneg z' => Zneg z'
                                   end = z.
    destruct z; crush.
  Qed.

  Lemma Fp_power_ge0 : forall e, 0 <= e -> forall a, Fp_power a e == a ^ e (mod p).
    solve_Fp_power.
    assert (e = 0) by omega; crush.
  Qed.

  Hint Rewrite <- Zsucc_succ' Zpred_pred' : cpdt.
  Lemma Zpower_Fp_inv_comm : forall a e, (/ a) ^ e == / a ^ e (mod p).
    intros.
    destruct (Z_lt_le_dec e 0).
    pose (Zgt_pos_0); destruct e; crush.
    induction_ge_m 0 e; crush.
  Qed.

  Hint Rewrite <- Zpower_Fp_inv_comm : cpdt.
  Lemma Fp_power_le0 : forall e, e <= 0 -> forall a, Fp_power a e == (/ a) ^ (- e) (mod p).
    solve_Fp_power.
  Qed.

  Hint Rewrite Zplus_opp_l : cpdt.
  Hint Rewrite <- Zmult_power : cpdt.
  Lemma Fp_power_exp_partial : forall a, ~ a == 0 (mod p) -> forall m n, m >= 0 -> n <= 0 -> m + n >= 0 -> a ^ (m + n) == a ^ m * / a ^ (- n) (mod p).
    intros.
    induction_ge_m (- n) m.
    crush.
    rewrite Fp_inv_spec_r; crush.
    power_succ_crush.
  Qed.

  Lemma Fp_power_Zsucc : forall a, ~ a == 0 (mod p) -> forall e, Fp_power a (Zsucc e) == a * Fp_power a e (mod p).
    do 2 solve_Fp_power.
    assert (e = 0) by omega; crush.
    replace (- e) with (Zsucc (- Zsucc e)) by omega; crush.
    field; crush.
  Qed.
  
  Hint Rewrite Fp_power_Zsucc : cpdt.
  Lemma Fp_power_Zpred : forall a, ~ a == 0 (mod p) -> forall e, Fp_power a (Zpred e) == / a * Fp_power a e (mod p).
    intros.
    rewrite (Zsucc_pred e) at 2.
    crush.
    field; crush.
  Qed.
  
  Hint Rewrite Fp_power_Zpred : cpdt.
  Lemma Fp_power_exp : forall a, ~ a == 0 (mod p) -> forall m n, Fp_power a (m + n) == Fp_power a m * Fp_power a n (mod p).
    intros.
    generalize n.
    apply Zind; intros; try rewrite <- Zsucc_succ'; try rewrite <- Zpred_pred'; power_succ_crush.
  Qed.

  Add Parametric Morphism : Fp_power
    with signature (eqm p ==> eq ==> eqm p)
      as Fp_power_mor.
    simpl_Fp_power.
    induction_ge_m 1 y0; power_succ_crush.
    induction_ge_m 0 (- y0); power_succ_crush.
  Qed.

  Hint Rewrite Fp_power_0_l : cpdt.
  Lemma Fp_power_theory : @power_theory Z 1 Zmult (eqm p) Z Z_of_N Fp_power.
    constructor.
    intros.
    unfold pow_N.
    generalize n.
    apply Nind.
    crush.
    destruct n0; crush.
    rewrite Zpos_succ_morphism.
    rewrite pow_pos_Psucc; try unfold Setoid_Theory; intros; try ring; crush.
    destruct (Z_mod_dec p r 0).
    setoid_rewrite e at 1 2; crush.
    change (Zpos (p0 + 1)) with (Zpos p0 + 1).
    rewrite Fp_power_exp; try assumption.
    fcrush.
  Qed.

  Ltac induction_Z var := generalize var; apply Zind; intros; try rewrite <- Zsucc_succ'; try rewrite <- Zpred_pred'.

  Lemma Fp_mult_integral : forall a b, (a * b) == 0 (mod p) -> a == 0 (mod p) \/ b == 0 (mod p).
    intros.
    destruct (Z_mod_dec p a 0).
    crush.
    right.
    rewrite <- (Zmult_1_l b).
    rewrite <- (Fp_inv_spec n).
    ring [H].
  Qed.

  Hint Rewrite Fp_power_Zsucc Fp_power_Zpred Zmult_succ_l Fp_power_exp: cpdt.
  
  Lemma Zmult_Fp_power : forall a b m, (Fp_power a m) * (Fp_power b m) == (Fp_power (a * b) m) (mod p).
    intros.
    destruct (Z_eq_dec m 0).
    crush.
    destruct (Z_mod_dec p (a) 0).
    crush.
    destruct (Z_mod_dec p b 0).
    crush.
    induction_Z m.
    crush.
    crush.
    ring [H].
    destruct (Fp_mult_integral a b); crush.
    crush.
    ring [H].
    destruct (Fp_mult_integral a b); crush.
  Qed.

  Hint Rewrite <- Zmult_Fp_power : cpdt.
  Hint Rewrite Zmult_plus_distr_l Zmult_plus_distr_r : cpdt.
  
  Lemma Fp_power_mult : forall a m n, Fp_power a (m * n) == Fp_power (Fp_power a m) n (mod p).
    intros.
    destruct (Z_mod_dec p a 0).
    destruct (Z_eq_dec (m * n) 0).
    destruct (Zmult_integral _ _ e0); crush.
    crush.
    induction_Z m.
    crush.
    crush.
    ring.
    crush.
    unfold Zpred.
    rewrite Zmult_plus_distr_l.
    replace (x * n + -1 * n) with (x * n + - n) by omega.
    crush.
    ring.
  Qed.
End Fp_field_theory.