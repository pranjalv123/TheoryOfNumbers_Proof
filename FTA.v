Require Import CpdtTactics.
Require Import List.
Require Export ZArith.
Require Export Znumtheory.
Require Import ProofIrrelevance.
Require Export MSets.
Require Import Equalities.

Load Zadditions.

Set Implicit Arguments.

(* tactics *)
Ltac spec hyp arg := specialize arg; simpl in hyp.
Ltac make_subgoals impl :=
  match type of impl with
    | ?a -> ?b => assert b; try apply impl; make_subgoals b
    | _ => idtac
  end.

Hint Immediate proof_irrelevance.

Hint Rewrite <- Zsucc_succ' Zpred_pred' : cpdt.
Hint Immediate Zdivide_refl Zone_divide Zdivide_0.

Hint Extern 2 (_ < _) => omega.
Hint Extern 2 (_ > _) => omega.
Hint Extern 2 (_ <= _) => omega.
Hint Extern 2 (_ >= _) => omega.
Hint Extern 2 (_ <> _) => omega.
Hint Extern 3 ((?a | ?b)) => match goal with
                               | [ H : (a | ?c), H' : (?c | b) |- _ ] => eapply Zdivide_trans
                             end.

Theorem prime_divis : forall n, n > 1 -> exists p, prime p /\ (p | n).
  assert (forall k n, n <= k -> n > 1 -> exists p, prime p /\ (p | n)).
  apply (Zind (fun k => forall n, n <= k -> n > 1 -> exists p, prime p /\ (p | n))).
  crush.
  intros.
  destruct (prime_dec n).
  eauto.
  destruct (not_prime_divide n); eauto.
  specialize (H x0).
  assert (exists p : Z, prime p /\ (p | x0)) by (apply H; crush).
  do 2 destruct H3.
  destruct H2.
  exists x1; eauto.
  intros.
  pose (Zle_pred x).
  crush.
  intros.
  specialize (H n n).
  crush.
Qed.

Lemma power_div : forall p e, p > 1 -> e >= 1 -> (p | p ^ e).
  intros.
  rewrite (Zsucc_pred e) in *.
  change (Zsucc _) with (Zpred e + 1).
  rewrite Zpower_exp; try omega.
  simpl_power.
  apply Zdivide_mult_r.
  crush.
Qed.

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
      destruct (Z_eq_dec e e0);
        [ left | right | right | right ];
          try (intro; inversion H; tauto).
    subst.
    f_equal; auto.
  Qed.

  Definition pep_value (pep : t) : Z :=
    let (p, e) := pep_to_pair pep in p ^ e.

  Definition pep_prime (pep : t) : Z :=
    let (p, e) := pep_to_pair pep in p.

  Definition pep_exp (pep : t) : Z :=
    let (p, e) := pep_to_pair pep in e.

  Ltac simpl_peps := unfold PEP.pep_prime, PEP.pep_exp, PEP.pep_value, PEP.pep_to_pair in *; simpl in *; eauto.
  Ltac simpl_peps_in hyp := unfold PEP.pep_prime, PEP.pep_exp, PEP.pep_value, PEP.pep_to_pair in hyp; simpl in hyp.

  Lemma pep_exp_succ :
    forall pep1 pep2, pep_prime pep1 = pep_prime pep2 -> pep_exp pep1 = Zsucc (pep_exp pep2) -> pep_value pep1 = (pep_prime pep1) * (pep_value pep2).
    intros.
    destruct pep1.
    destruct pep2.
    simpl_peps.
    subst.
    unfold Zsucc.
    rewrite Zpower_exp; try omega.
    simpl_power.
    ring.
  Qed.

  Lemma pep_pair_sufficient : forall pep1 pep2, pep_to_pair pep1 = pep_to_pair pep2 -> pep1 = pep2.
    intros.
    destruct pep1.
    destruct pep2.
    simpl_peps.
    inversion H.
    subst.
    f_equal; auto. 
  Qed.
End PEP.

Hint Unfold PEP.pep_value PEP.pep_to_pair PEP.pep_prime PEP.pep_exp.
Hint Resolve PEP.pep_intro.

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
    unfold PPL.add_to_product.
    unfold transpose.
    intros.
    ring.
  Qed.

  Lemma empty_in_contr : forall x ppl, PPL.Empty ppl -> PPL.In x ppl -> False.
    intros.
    unfold PPL.Empty, not in *.
    eauto.
  Qed.
  Hint Resolve empty_in_contr.
  Hint Immediate PPL.empty_spec.

  Hint Constructors PPL.unique_prod.
  Hint Unfold PPL.unique_primes PPL.ppl_product.
  Lemma ppl_product_empty : PPL.unique_prod PPL.empty 1.
    split.
    unfold PPL.unique_primes; intros.
    pose (PPL.empty_spec).
    elimtype False; eauto.
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

  Hint Rewrite ppl_product_add ppl_product_remove : cpdt.

  Lemma ppl_product_big : forall ppl, PPL.ppl_product ppl >= 1.
    intros.
    unfold PPL.ppl_product.
    apply fold_rec; intros.
    omega.
    unfold PPL.add_to_product.
    destruct x.
    PEP.simpl_peps.
    rewrite <- (Zmult_1_r 1).
    destruct p0.
    assert (0 < p ^ e) by (apply Zpower_gt_0; omega).
    eauto with zarith.
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
    apply Zpower_divide; omega.
  Qed.

  Hint Unfold PPL.For_all PPL.Exists.
  Lemma exists_dec : forall (P : PEP.t -> Prop) ppl, (forall x, {P x} + {~ P x}) -> PPL.Exists P ppl \/ PPL.For_all (fun x => ~ (P x)) ppl.
    intros.
    apply (@set_induction ((fun ppl => PPL.Exists P ppl \/ PPL.For_all (fun x => ~ (P x)) ppl) : PPL.t -> Type)).
    eauto.
    intros.
    destruct (H2 x).
    assert (PPL.In x s') by tauto; clear H3 H4.
    destruct H0.
    left.
    destruct H0.
    destruct H0.
    edestruct H2; eauto 7.
    destruct (H x).
    eauto.
    right.
    do 3 intro.
    destruct (H2 x0).
    destruct (H6 H3).
    crush.
    apply (H0 x0); assumption.
  Qed.
End PPLProps.

Hint Rewrite PPLProps.ppl_product_add PPLProps.ppl_product_remove.
Hint Immediate PPLProps.proper_atp PPLProps.transpose_atp PPLProps.ppl_product_big PPLProps.ppl_product_empty.

Hint Resolve PPLProps.FM.empty_iff.
Hint Rewrite Zabs_eq.
Hint Resolve Z_div_pos.
Theorem all_ppl : forall n : Z, n >= 1 -> exists ppl : PPL.t, PPL.unique_prod ppl n.
  set (P := fun k => forall n, n >= 1 -> n <= k -> exists ppl : PPL.t, PPL.unique_prod ppl n).
  assert (forall k, k >= 1 -> P k).
  apply (Zind_ge_m P); unfold P.
  intros.
  assert (n = 1) by omega.
  subst n.
  eauto.
  intros.
  destruct (Z_le_lt_eq_dec 1 n0); try omega.
  apply Zlt_gt in z.
  destruct (prime_divis z).
  destruct H3.
  pose H3.
  destruct p.
  destruct H4.
  assert (n0 / x = q).
  rewrite H4.
  apply Z_div_mult; try omega.
  destruct (Z_le_lt_eq_dec q n0).
  assert (Zabs q = q).
  apply Zabs_eq; try omega.
  rewrite <- H7.
  apply Z_div_pos; omega.
  assert (Zabs n0 = n0) by (apply Zabs_eq; omega).
  rewrite <- H8.
  rewrite <- H9.
  apply Zdivide_bounds; crush.
  assert (q | n0) by crush.
  destruct (H0 q); try omega.
  assert (0 < n0 / x < n0) by (apply Zdivide_Zdiv_lt_pos; crush).
  omega.
  destruct H9.
  destruct (PPLProps.exists_dec (fun pep => PEP.pep_prime pep = x) x0).
  intros; repeat decide equality.
  do 2 destruct H9.
  destruct x1.
  PEP.simpl_peps_in H9.
  assert (Zsucc e0 >= 1) by omega.
  pose (PEP.pep_intro p0 H11).
  exists (PPL.add p1 (PPL.remove (PEP.pep_intro p0 z1) x0)).
  split.
  unfold PPL.unique_primes in *; intros.
  apply PPL.add_spec in H12; apply PPL.add_spec in H13; destruct H12; destruct H13.
  crush.
  apply PPL.remove_spec in H13; destruct H13.
  specialize (u _ _ H9 H13).
  elimtype False.
  apply H15.
  symmetry.
  apply u.
  rewrite <- H14.
  subst pep1 p1.
  PEP.simpl_peps; crush.
  apply PPL.remove_spec in H12; destruct H12.
  specialize (u _ _ H9 H12).
  elimtype False.
  apply H15.
  rewrite u.
  reflexivity.
  rewrite H14.
  subst pep2 p1.
  PEP.simpl_peps; crush.
  apply PPL.remove_spec in H13; destruct H13.
  apply PPL.remove_spec in H12; destruct H12.
  apply u; try assumption.
  rewrite PPLProps.ppl_product_add.
  rewrite (PEP.pep_exp_succ p1 (PEP.pep_intro p0 z1)).
  rewrite <- Zmult_assoc.
  rewrite <- (PPLProps.ppl_product_remove H9).
  PEP.simpl_peps.
  crush.
  PEP.simpl_peps; crush.
  PEP.simpl_peps; crush.
  intro.
  apply PPL.remove_spec in H12; destruct H12.
  apply H13.
  apply PEP.pep_pair_sufficient.
  PEP.simpl_peps; crush.
  assert (1 >= 1) by omega.
  exists (PPL.add (PEP.pep_intro H3 H10) x0).
  split.
  unfold PPL.unique_primes in *.
  intros.
  apply PPL.add_spec in H11.
  apply PPL.add_spec in H12.
  destruct H11; destruct H12; try (subst pep1 pep2); intuition; elimtype False.
  spec H9 (H9 pep2).
  subst pep1.
  auto with zarith.
  spec H9 (H9 pep1).
  subst pep2.
  auto with zarith.
  subst n0.
  rewrite PPLProps.ppl_product_add.
  PEP.simpl_peps.
  simpl_power.
  rewrite Zmult_1_r.
  rewrite e.
  apply Zmult_comm.
  intro.
  apply (H9 _ H4).
  PEP.simpl_peps.
  elimtype False.
  subst n0.
  apply (@Zlt_irrefl (q * x)).
  rewrite <- e at 1.
  rewrite <- Zmult_1_r at 1.
  apply Zmult_lt_compat_l; omega.
  exists PPL.empty.
  split.
  unfold PPL.unique_primes.
  intros.
  elimtype False.
  pose (PPLProps.FM.empty_iff pep1).
  tauto.
  crush.
  intros.
  subst P; simpl in H.
  specialize (H _ H0 _ H0).
  apply H; omega.
Qed.

Lemma euclids_ppl : forall ppl n m, PPL.ppl_product ppl = n -> (m | n) -> prime m -> exists pep, PPL.In pep ppl /\ PEP.pep_prime pep = m.
  apply (@PPLProps.set_induction_bis (fun ppl => forall n m, PPL.ppl_product ppl = n -> (m | n) -> prime m -> exists pep, PPL.In pep ppl /\ PEP.pep_prime pep = m)).
  intros.
  destruct (H0 n m); try assumption.
  rewrite <- H1.
  unfold PPL.ppl_product.
  apply PPLProps.fold_equal; crush.
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
  apply prime_mult in H2; try assumption.
  destruct H2.
  destruct x.
  unfold PEP.pep_value in H1.
  unfold PEP.pep_to_pair in H1.
  assert (m = p) by (apply (@prime_power_prime m p e); eauto).
  exists (PEP.pep_intro p0 z).
  crush.
  destruct (H0 (PPL.ppl_product s) m); crush.
  exists x0; crush.
Qed.

Theorem fundamental_theorem_of_arithmetic : forall n ppl1 ppl2, PPL.unique_prod ppl1 n -> PPL.unique_prod ppl2 n -> PPL.Equal ppl1 ppl2.
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