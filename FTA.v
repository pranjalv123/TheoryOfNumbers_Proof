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

Check Zind.

Theorem Zind_ge0 : forall P : Z -> Prop, P 0 -> (forall n : Z, n >= 0 -> P n -> P (Zsucc n)) -> (forall n, n >= 0 -> P n).
  intro.
  intro.
  intro.
  assert (forall k x, x <= k -> 0 < x -> P x).
  apply (Zind (fun k => forall x, x <= k -> 0 < x -> P x)).
  crush.
  intros.
  rewrite <- Zsucc_succ' in H2.
  destruct (Z_le_lt_eq_dec x0 (Zsucc x) H2).
  apply Zlt_succ_le in z.
  apply H1; assumption.
  subst x0; apply H0.
  omega.
  apply Zlt_succ_le in H3.
  destruct (Z_le_lt_eq_dec 0 x H3).
  apply H1; crush.
  crush.
  intros.
  rewrite <- Zpred_pred' in H2.
  apply H1; try assumption.
  pose (Zle_pred x); omega.
  intros.
  apply Zge_le in H2.
  destruct (Z_le_lt_eq_dec 0 n H2).
  apply (H1 n n); crush.
  crush.
Qed.

Ltac simpl_power := unfold Zpower; unfold Zpower_pos; simpl; try omega.

Lemma power_div : forall p e, p > 1 -> e >= 1 -> (p | p ^ e).
  intros.
  rewrite (Zsucc_pred e) in *.
  change (Zsucc _) with (Zpred e + 1).
  rewrite Zpower_exp; try omega.
  simpl_power.
  apply Zdivide_mult_r.
  crush.
Qed.

Lemma prime_power_div : forall p q e, prime p -> prime q -> e >= 0 -> (q | p ^ e) -> q = p.
  do 5 intro.
  apply (Zind_ge0 (fun e => (q | p ^ e) -> q = p)).
  simpl_power.
  intro.
  destruct (Zdivide_1 q); try assumption; intros; destruct H0; omega.
  intros.
  unfold Zsucc in H3.
  rewrite Zpower_exp in H3; try omega.
  unfold Zpower at 2 in H3; unfold Zpower_pos in H3; simpl in H3.
  rewrite Zmult_1_r in H3.
  destruct (euclids_lemma _ _ H0 H3).
  tauto.
  apply prime_div_prime; assumption.
Qed.
  
Lemma exp_big : forall p, p > 1 -> forall e, e >= 0 -> p ^ e >= 1.
  intros.
  apply (Zind_ge0 (fun x => p ^ x >= 1)); crush.
  change (Zsucc n) with (n + 1).
  rewrite Zpower_exp; try omega.
  rewrite <- Zmult_1_r.
  apply Zmult_ge_compat; try omega.
  simpl_power.
Qed.

Lemma exp_cancel : forall p e1 e2 m n, e2 >= 0 -> e1 > e2 -> p > 1 -> p ^ e1 * m = p ^ e2 * n -> p ^ (e1 - e2) * m = n.
  intros.
  apply (Zmult_reg_l) with (p := p ^ e2).
  pose (exp_big H1 H).
  omega.
  ring_simplify.
  rewrite <- (Zpower_exp); try omega.
  rewrite Zplus_minus.
  assumption.
Qed.

Require Import MSets.
Require Import Equalities.

Module PEP.
  Inductive prime_exp_pair := pep_intro : forall p e, prime p -> e >= 1 -> prime_exp_pair.

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

  Definition pep_prime (pep : t) : Z :=
    let (p, e) := pep_to_pair pep in p.

  Definition pep_exp (pep : t) : Z :=
    let (p, e) := pep_to_pair pep in e.

  Ltac simpl_peps := unfold PEP.pep_prime in *; unfold PEP.pep_exp in *; unfold PEP.pep_value in *; unfold PEP.pep_to_pair in *; simpl in *; fold PEP.pep_prime in *; fold PEP.pep_exp in *; fold PEP.pep_value in *.
  Ltac simpl_peps_in hyp := unfold PEP.pep_prime in hyp; unfold PEP.pep_exp in hyp; unfold PEP.pep_value in hyp; unfold PEP.pep_to_pair in hyp; simpl in hyp; fold PEP.pep_prime in hyp; fold PEP.pep_exp in hyp; fold PEP.pep_value in hyp.

  Lemma pep_exp_succ :
    forall pep1 pep2, pep_prime pep1 = pep_prime pep2 -> pep_exp pep1 = Zsucc (pep_exp pep2) -> pep_value pep1 = (pep_prime pep1) * (pep_value pep2).
    intros.
    destruct pep1.
    destruct pep2.
    simpl_peps.
    subst.
    unfold Zsucc.
    rewrite Zpower_exp; crush.
    unfold Zpower_pos.
    crush.
    ring.
  Qed.

  Lemma pep_pair_sufficient : forall pep1 pep2, pep_to_pair pep1 = pep_to_pair pep2 -> pep1 = pep2.
    intros.
    destruct pep1.
    destruct pep2.
    simpl_peps.
    inversion H; clear H.
    subst.
    rewrite (proof_irrelevance _ p0 p2).
    rewrite (proof_irrelevance _ z0 z).
    reflexivity.
  Qed.
    
End PEP.

Hint Unfold PEP.pep_value PEP.pep_to_pair.

Module PPL.
  Include MSetWeakList.Make PEP.

  Definition unique_primes (ppl : PPL.t) : Prop :=
    forall pep1 pep2, In pep1 ppl -> In pep2 ppl -> PEP.pep_prime pep1 = PEP.pep_prime pep2 -> pep1 = pep2.

  Definition add_to_product (pep : PEP.t) (product : Z) : Z :=
    (PEP.pep_value pep) * product.
  
  Definition ppl_product (ppl : PPL.t) : Z :=
    fold add_to_product ppl 1.
  
  Inductive unique_prod (t0 : t) (n : Z) : Type :=
    | up_intro : unique_primes t0 -> ppl_product t0 = n -> unique_prod t0 n.
End PPL.

Hint Unfold Zpower_pos.

Module PPLProps.
  Include WPropertiesOn PEP PPL.
  
  Hint Rewrite Zmult_assoc : cpdt.

  Lemma proper_atp : Proper (eq==>eq==>eq) PPL.add_to_product.
    crush.
  Qed.

  Lemma transpose_atp : transpose eq PPL.add_to_product.
    unfold transpose.
    unfold PPL.add_to_product.
    intros.
    ring.
  Qed.

  Lemma ppl_product_empty : forall ppl, PPL.Empty ppl -> PPL.ppl_product ppl = 1.
    intros.
    unfold PPL.ppl_product.
    rewrite PPL.fold_spec.
    destruct (elements_Empty ppl).
    rewrite (H0 H).
    crush.
  Qed.
  
  Lemma ppl_product_add : forall (pep : PEP.t) (ppl : PPL.t), ~ PPL.In pep ppl -> PPL.ppl_product (PPL.add pep ppl) = (PEP.pep_value pep) * (PPL.ppl_product ppl).
    intros.
    apply (fold_add eq_equivalence proper_atp transpose_atp 1 H).
  Qed.

  Lemma ppl_product_remove : forall (pep : PEP.t) (ppl : PPL.t), PPL.In pep ppl -> PPL.ppl_product ppl = (PEP.pep_value pep) * PPL.ppl_product (PPL.remove pep ppl).
    intros.
    unfold PPL.ppl_product.
    rewrite <- (remove_fold_1 eq_equivalence proper_atp transpose_atp 1 H).
    crush.
  Qed.

  Lemma ppl_product_big : forall ppl, PPL.ppl_product ppl >= 1.
    intros.
    unfold PPL.ppl_product.
    apply fold_rec; intros.
    omega.
    unfold PPL.add_to_product.
    destruct x.
    PEP.simpl_peps.
    rewrite <- (Zmult_1_r 1).
    apply (Zmult_ge_compat); try omega.
    destruct p0.
    apply exp_big; omega.
  Qed.

  Lemma ppl_product_value_div : forall pep ppl, PPL.In pep ppl -> forall n, PPL.ppl_product ppl = n -> (PEP.pep_value pep | n).
    intros.
    rewrite (ppl_product_remove H) in H0.
    rewrite <- H0.
    apply Zdivide_mult_l; crush.
  Qed.

  Lemma ppl_product_prime_div : forall pep ppl, PPL.In pep ppl -> forall n, PPL.ppl_product ppl = n -> forall p, PEP.pep_prime pep = p -> (p | n).
    intros.
    rewrite (ppl_product_remove H) in H0.
    rewrite <- H0.
    destruct pep.
    PEP.simpl_peps.
    apply Zdivide_mult_l.
    subst p0.
    pose z.
    rewrite (Zsucc_pred e) in *.
    apply Zge_le in z0.
    change 1 with (Zsucc 0) in z0.
    apply Zsucc_le_reg in z0.
    change (Zsucc _) with (Zpred e + 1).
    rewrite Zpower_exp; try omega.
    apply Zdivide_mult_r.
    simpl_power.
    crush.
  Qed.
    
End PPLProps.

Theorem all_ppl : forall n : Z, n >= 1 -> exists ppl : PPL.t, PPL.unique_prod ppl n.
  assert (forall k n, n <= k -> n >= 1 -> exists ppl : PPL.t, PPL.ppl_product ppl = n /\ PPL.unique_primes ppl).
  apply (Zind (fun k => forall n, n <= k -> n >= 1 -> exists ppl : PPL.t, PPL.ppl_product ppl = n /\ PPL.unique_primes ppl)).
  crush.
  intros.
  rewrite <- Zsucc_succ' in H0.
  destruct (Z_le_lt_eq_dec 1 n); try omega.
  apply Zlt_gt in z.
  destruct (prime_divis z).
  destruct H2.
  destruct H3.
  pose H2.
  destruct p.
  assert (n / x0 = q).
  rewrite H3.
  apply Z_div_mult; try omega.
  destruct (Z_le_lt_eq_dec q n).
  assert (Zabs q = q).
  apply Zabs_eq; try omega.
  rewrite <- H6.
  apply Z_div_pos; omega.
  assert (Zabs n = n) by (apply Zabs_eq; omega).
  rewrite <- H7.
  rewrite <- H8.
  apply Zdivide_bounds; crush.
  assert (q <= x).
  assert (q | n) by crush.
  apply Zlt_succ_le.
  apply (Zlt_le_trans q n (Zsucc x)); crush.
  destruct (H q).
  crush.
  rewrite <- H6.
  assert (0 < n / x0 < n) by (apply Zdivide_Zdiv_lt_pos; crush).
  crush.
  destruct H8.
  destruct (classic (exists pep, PPL.In pep x1 /\ PEP.pep_prime pep = x0)).
  do 2 destruct H10.
  pose x2.
  destruct x2.
  unfold PEP.pep_prime in H11.
  unfold PEP.pep_to_pair in H11.
  assert (Zsucc e0 >= 1) by omega.
  pose (PEP.pep_intro p0 H12).
  exists (PPL.add p1 (PPL.remove (PEP.pep_intro p0 z1) x1)).
  rewrite PPLProps.ppl_product_add.
  split.
  rewrite (PEP.pep_exp_succ p1 e).
  rewrite H3.
  rewrite <- H8.
  rewrite (PPLProps.ppl_product_remove H10).
  PEP.simpl_peps.
  subst x0.
  ring.
  PEP.simpl_peps; crush.
  PEP.simpl_peps; crush.
  unfold PPL.unique_primes in *; intros.
  apply PPL.add_spec in H13; apply PPL.add_spec in H14; destruct H13; destruct H14.
  crush.
  apply PPL.remove_spec in H14; destruct H14.
  specialize (H9 _ _ H10 H14).
  elimtype False.
  apply H16.
  symmetry.
  apply H9.
  rewrite <- H15.
  subst pep1 p1.
  PEP.simpl_peps; crush.
  apply PPL.remove_spec in H13; destruct H13.
  specialize (H9 _ _ H10 H13).
  elimtype False.
  apply H16.
  rewrite H9.
  reflexivity.
  rewrite H15.
  subst pep2 p1.
  PEP.simpl_peps; crush.
  apply PPL.remove_spec in H14; destruct H14.
  apply PPL.remove_spec in H13; destruct H13.
  apply H9; try assumption.
  intro.
  apply PPL.remove_spec in H13; destruct H13.
  apply H14.
  apply PEP.pep_pair_sufficient.
  PEP.simpl_peps; crush.
  assert (1 >= 1) by omega.
  exists (PPL.add (PEP.pep_intro H2 H11) x1).
  split.
  rewrite PPLProps.ppl_product_add.
  PEP.simpl_peps.
  unfold Zpower.
  unfold Zpower_pos.
  simpl.
  rewrite Zmult_1_r.
  rewrite H8.
  rewrite H3.
  apply Zmult_comm.
  pose (@not_ex_all_not PEP.t (fun pep => PPL.In pep x1 /\ PEP.pep_prime pep = x0)).
  simpl in n0.
  specialize (n0 H10 (PEP.pep_intro H2 H11)).
  apply not_and_or in n0.
  destruct n0; crush.
  unfold PPL.unique_primes in *.
  intros.
  apply PPL.add_spec in H13.
  apply PPL.add_spec in H12.
  pose (@not_ex_all_not PEP.t (fun pep => PPL.In pep x1 /\ PEP.pep_prime pep = x0)).
  simpl in n0.
  specialize (n0 H10).
  destruct H12; destruct H13; crush.
  specialize (n0 pep2).
  elimtype False.
  apply n0.
  split; try assumption.
  unfold PEP.pep_prime at 1 in H14.
  subst pep1.
  simpl in H14.
  crush.
  specialize (n0 pep1).
  elimtype False.
  apply n0.
  split; try assumption.
  unfold PEP.pep_prime at 2 in H14.
  subst pep2.
  simpl in H14.
  assumption. (* repetitive *)
  subst n.
  elimtype False.
  eapply Zlt_irrefl.
  instantiate (1 := q * x0).
  rewrite <- e at 1.
  rewrite <- Zmult_1_r at 1.
  apply Zmult_lt_compat_l; omega.
  exists PPL.empty.
  split.
  crush.
  unfold PPL.unique_primes.
  intros.
  elimtype False.
  pose (PPLProps.FM.empty_iff pep1).
  crush.
  intros.
  assert (n <= x).
  rewrite <- Zpred_pred' in H0.
  apply (Zle_trans n (Zpred x) x); [assumption | apply Zle_pred].
  crush.
  intros.
  destruct (H n n); try omega.
  destruct H1.
  exists x.
  apply (PPL.up_intro H2 H1).
Qed.

Ltac destruct_keep hyp := let name := fresh in pose (name := hyp); destruct hyp.

Lemma euclids_ppl : forall ppl n m, PPL.ppl_product ppl = n -> (m | n) -> prime m -> exists pep, PPL.In pep ppl /\ PEP.pep_prime pep = m.
  apply (@PPLProps.set_induction_bis (fun ppl => forall n m, PPL.ppl_product ppl = n -> (m | n) -> prime m -> exists pep, PPL.In pep ppl /\ PEP.pep_prime pep = m)).
  intros.
  destruct (H0 n m); try assumption.
  rewrite <- H1.
  unfold PPL.ppl_product.
  apply PPLProps.fold_equal; crush.
  apply PPLProps.transpose_atp.
  exists x.
  destruct (H x).
  crush.
  intros.
  destruct H1.
  elimtype False.
  rewrite (@PPLProps.ppl_product_empty PPL.empty) in H.
  assert (Zabs m <= Zabs n) by (apply Zdivide_bounds; crush).
  rewrite (Zabs_eq m) in H3; crush.
  apply PPL.empty_spec.
  intros.
  rewrite PPLProps.ppl_product_add in H1; try assumption.
  subst n.
  apply euclids_lemma in H2; try assumption.
  destruct H2.
  destruct x.
  unfold PEP.pep_value in H1.
  unfold PEP.pep_to_pair in H1.
  assert (m = p) by (apply (@prime_power_div p m e); try omega; try assumption).
  exists (PEP.pep_intro p0 z).
  crush.
  destruct (H0 (PPL.ppl_product s) m); crush.
  exists x0; crush.
Qed.

Ltac classical_contradiction :=
  match goal with
    | [ |- ?g ] => destruct (classic g); [ assumption | elimtype False ]
  end.

Ltac make_subgoals impl :=
  match type of impl with
    | ?a -> ?b => assert b; try apply impl; make_subgoals b
    | _ => idtac
  end.

Theorem unique_ppl : forall n ppl1 ppl2, PPL.unique_prod ppl1 n -> PPL.unique_prod ppl2 n -> PPL.Equal ppl1 ppl2.
  unfold PPL.Equal.
  assert (forall n ppl1 ppl2, PPL.unique_prod ppl1 n -> PPL.unique_prod ppl2 n -> forall a, PPL.In a ppl1 -> PPL.In a ppl2).
  intros.
  destruct H.
  destruct H0.
  destruct a.
  assert (p | n).
    apply (PPLProps.ppl_product_prime_div H1); try assumption.
    PEP.simpl_peps; reflexivity.
  destruct (@euclids_ppl ppl2 n p); try assumption.
  assert (PEP.pep_intro p0 z = x).
  destruct H0.
  destruct x.
  apply PEP.pep_pair_sufficient.
  unfold PEP.pep_to_pair; simpl.
  PEP.simpl_peps_in H2.
  subst p1.
  f_equal.
  pose (PPLProps.ppl_product_remove H0).
  rewrite e0 in e3.
  PEP.simpl_peps_in e3.
  pose (PPLProps.ppl_product_remove H1).
  PEP.simpl_peps_in e4.
  rewrite e in e4.
  rewrite e3 in e4.
  assert (e1 >= 0) by omega.
  assert (e2 >= 0) by omega.
  destruct p0. 
  assert (p > 1) by omega.
  destruct (Ztrichotomy e1 e2); try assumption.
    assert (e2 > e1) by omega.  
    pose (exp_cancel _ _ H2 H6 H4 e4).
    assert (e2 - e1 >= 1) by omega.
    assert (p | PPL.ppl_product (PPL.remove (PEP.pep_intro (prime_intro p z1 r) z) ppl1)).
    rewrite <- e5.
    apply Zdivide_mult_l.
    apply power_div; omega.
    apply euclids_ppl with (ppl := (PPL.remove (PEP.pep_intro (prime_intro p z1 r) z) ppl1)) in H8; try reflexivity; try assumption.
    do 2 destruct H8.
    apply (PPL.remove_spec) in H8; destruct H8.
    elimtype False.
    apply H10.
    destruct x; f_equal; auto.
    destruct H5.
    assumption.
    symmetry in e4.
    pose (exp_cancel _ _ H3 H5 H4 e4).
    assert (e1 - e2 >= 1) by omega.
    assert (p | PPL.ppl_product (PPL.remove (PEP.pep_intro p2 z0) ppl2)).
    rewrite <- e5.
    apply Zdivide_mult_l.
    apply power_div; omega.
    apply euclids_ppl with (ppl := (PPL.remove (PEP.pep_intro p2 z0) ppl2)) in H7; try reflexivity; try assumption.
    do 2 destruct H7.
    apply (PPL.remove_spec) in H7; destruct H7.
    elimtype False.
    apply H9.
    destruct x; f_equal; auto.
  rewrite H2.
  destruct H0.
  assumption.
  intros; split; eauto.
Qed.