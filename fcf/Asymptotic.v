(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* Definitions of asymptotic notions such as polynomial and negligible functions, and related theory. *)

Set Implicit Arguments.

Require Import fcf.StdNat.

Definition polynomial (f : nat -> nat) :=
    exists x c1 c2, forall n,
      (f n <= c1 * expnat n x + c2)%nat.

Definition polynomial_nz(f : nat -> nat) :=
  exists x c1 c2, 
    x > 0 /\ c1 > 0 /\ c2 > 0 /\
    forall n, 
      (f n <= c1 * expnat n x + c2)%nat.

Theorem polynomial_nz_equiv : 
  forall f, 
    polynomial f ->
    polynomial_nz f.
  
  intuition.
  unfold polynomial, polynomial_nz in *.
  do 3 (destruct H).
  exists (S x).
  exists (S x0).
  exists (x0 + S x1).
  intuition.
  rewrite H.
  rewrite plus_assoc.
  eapply plus_le_compat; intuition.
  simpl.
  destruct (eq_nat_dec x 0).
  subst.
  simpl.
  repeat rewrite mult_1_r.
  rewrite <- plus_0_l at 1.
  eapply plus_le_compat; intuition.
  
  rewrite <- plus_0_l at 1.
  rewrite <- plus_0_r at 1.
  
  eapply plus_le_compat; intuition.
  eapply plus_le_compat; intuition.
  eapply mult_le_compat; intuition.
  destruct (eq_nat_dec n 0); subst.
  
  rewrite expnat_0;
    omega.
  
  rewrite <- mult_1_l at 1.
  eapply mult_le_compat; intuition.
Qed.        

Theorem polynomial_plus : 
  forall f1 f2 ,
    polynomial f1 ->
    polynomial f2 ->
    polynomial (fun n => f1 n + f2 n).
  
  intuition.
  
  apply polynomial_nz_equiv in H.
  apply polynomial_nz_equiv in H0.
  
  unfold polynomial, polynomial_nz in *.
  
  Ltac des := 
    match goal with
      | [H : exists _, _ |- _] => destruct H
    end.
  repeat des.
  intuition.
  exists (max x2 x).
  exists (x3 + x0).
  exists (x4 + x1).
  intuition.
  
  eapply le_trans.
  eapply plus_le_compat.
  eapply H6; trivial.
  eapply H7; trivial.
  rewrite mult_plus_distr_r.
  repeat rewrite plus_assoc.
  eapply plus_le_compat; trivial.
  rewrite plus_comm.
  rewrite plus_assoc.
  eapply plus_le_compat; trivial.
  rewrite plus_comm.
  eapply plus_le_compat;
    eapply mult_le_compat; intuition.
  
  eapply expnat_exp_le; intuition.
  eapply expnat_exp_le; intuition.
Qed.

Theorem polynomial_const : 
  forall c, 
    polynomial (fun n => c).
  
  intuition.
  unfold polynomial.
  exists 0.
  exists 0.
  exists c.
  intuition.
Qed.

Theorem polynomial_ident :
  polynomial (fun n => n).
  
  unfold polynomial.
  intuition.
  exists 1.
  exists 1.
  exists 0.
  intuition.
  simpl.
  omega.
  
Qed.

Theorem polynomial_mult : 
  forall f1 f2 ,
    polynomial f1 ->
    polynomial f2 ->
    polynomial (fun n => f1 n * f2 n).
  
  intuition.
  apply polynomial_nz_equiv in H.
  apply polynomial_nz_equiv in H0.
  
  unfold polynomial, polynomial_nz in *.
  repeat des.
  intuition.
  exists (x + x2).
  exists (3 * (x3 * x0 * x4 * x1)).
  exists (x4 * x1).
  intuition.
  eapply le_trans.
  eapply mult_le_compat.
  eapply H6; intuition.
  eapply H7; intuition.
  repeat rewrite mult_plus_distr_l.
  repeat rewrite mult_plus_distr_r.
  
  rewrite plus_assoc.
  eapply plus_le_compat; trivial.
  
  rewrite expnat_plus.
  simpl.
  rewrite plus_0_r.
  repeat rewrite mult_plus_distr_r.
  rewrite plus_assoc.
  eapply plus_le_compat.
  eapply plus_le_compat.
  rewrite (mult_comm (expnat n x)).
  repeat rewrite mult_assoc.
  eapply mult_le_compat; intuition.
  rewrite mult_comm.
  rewrite mult_assoc.
  eapply mult_le_compat; intuition.
  rewrite <- mult_1_r at 1.
  rewrite <- mult_1_r at 1.
  eapply mult_le_compat; intuition.
  eapply mult_le_compat; intuition.
  rewrite mult_comm.
  intuition.
  
  destruct (eq_nat_dec n 0); subst.
  repeat rewrite expnat_0.
  simpl.
  repeat rewrite mult_0_r.
  intuition.
  trivial.
  trivial.
  rewrite (mult_comm (expnat n x)).
  repeat rewrite mult_assoc.
  eapply mult_le_compat; trivial.
  rewrite <- mult_1_r at 1.
  eapply mult_le_compat; trivial.
  rewrite <- mult_1_r at 1.
  eapply mult_le_compat; trivial.
  rewrite mult_comm.
  eapply mult_le_compat; trivial.
  rewrite <- mult_1_l at 1.
  eapply mult_le_compat; trivial.
  eapply expnat_ge_1.
  omega.
  
  destruct (eq_nat_dec n 0); subst.
  repeat rewrite expnat_0.
  simpl.
  repeat rewrite mult_0_r.
  intuition.
  trivial.
  trivial.
  rewrite (mult_comm (expnat n x)).
  repeat rewrite mult_assoc.
  rewrite <- mult_1_r at 1.
  eapply mult_le_compat; trivial.
  rewrite <- mult_assoc.
  rewrite (mult_comm (expnat n x2)).
  rewrite mult_assoc.
  eapply mult_le_compat; trivial.
  eapply mult_le_compat; trivial.
  rewrite <- mult_1_r at 1.
  eapply mult_le_compat; trivial.
  rewrite <- mult_1_r at 1.
  eapply mult_le_compat; trivial.
  eapply expnat_ge_1.
  omega.
Qed.     
      

Require Import fcf.Rat.
Local Open Scope rat_scope.

Definition negligible(f : nat -> Rat) :=
  forall c, exists n, forall x (pf_nz : nz x),
    x > n ->
    ~ ((1 / expnat x c) <= f x)%rat.


Theorem negligible_eq : 
  forall (f1 f2 : nat -> Rat),
    negligible f1 ->
    (forall n, f1 n == f2 n) ->
    negligible f2.

  intuition.
  unfold negligible in *.
  intuition.
  edestruct H.
  econstructor.
  intuition.
  eapply H1.
  eauto.
  rewrite H3.
  rewrite <- H0.
  intuition.

Qed.

Lemma negligible_le : 
  forall f1 f2,
    (forall n, f2 n <= f1 n)%rat ->
    negligible f1 ->
    negligible f2.
  
  intuition.
  unfold negligible in *.
  intuition.
  edestruct H0.
  econstructor.
  intuition.
  eapply H1.
  eauto.
  rewrite H3.
  eauto.
  
Qed.

Lemma negligible_plus : 
  forall f1 f2,
    negligible f1 ->
    negligible f2 ->
    negligible (fun n => f1 n + f2 n)%rat.
  
  unfold negligible in *.
  intuition.
  
  destruct (H (S c)).
  destruct (H0 (S c)).
  exists (max 1 (max x x0)).
  intuition.
  
  apply Nat.max_lub_lt_iff in H3.
  intuition.
  
  assert (1 / expnat x1 c <= 2/1 * (maxRat (f1 x1) (f2 x1)))%rat.
  eapply leRat_trans.
  eapply H4.
  
  eapply ratAdd_2_ratMax.
  
  assert (1 / expnat x1 (S c) <= RatIntro 1 (posnatMult (pos 2) (pos (expnat x1 c))))%rat.
  eapply leRat_terms; intuition.
  unfold natToPosnat, posnatToNat, posnatMult.
  eapply expnat_double_le.
  omega.
  
  unfold maxRat in *.
  case_eq (bleRat (f1 x1) (f2 x1)); intuition.
  rewrite H8 in H3.
  
  eapply H2.
  eapply le_lt_trans.
  eapply Max.le_max_r.
  eauto.

  rewrite H7.
  rewrite rat_mult_den.
  rewrite H3.
  rewrite <- ratMult_assoc.
  
  rewrite <- ratMult_num_den.
  rewrite num_dem_same_rat1.
  rewrite ratMult_1_l.
  intuition.
  unfold posnatMult, natToPosnat, posnatToNat.
  omega.
  
  rewrite H8 in H3.
  eapply H1.
  eapply le_lt_trans.
  eapply Max.le_max_l.
  eauto.
  
  rewrite H7.
  rewrite rat_mult_den.
  rewrite H3.
  rewrite <- ratMult_assoc.
  
  rewrite <- ratMult_num_den.
  rewrite num_dem_same_rat1.
  rewrite ratMult_1_l.
  intuition.
  unfold posnatMult, natToPosnat, posnatToNat.
  omega.
Qed.


(* We need several facts about arithmetic to show that an inverse exponential function is negligible. *)
Local Open Scope nat_scope.
Theorem double_log_plus_3_le_h : 
  forall y x,
    y = Nat.log2 x ->
    y >= 4 ->
    2 * y + 3 <= x.
  
  induction y; intuition; simpl in *.
  rewrite plus_0_r in *.
  
  assert (S (y + S y + 3)  = 
    (y + y + 3) + 2).
  omega.
  rewrite H1.
  
  destruct (eq_nat_dec y 3).
  subst.
  assert (x >= Nat.pow 2 4).
  rewrite H.
  eapply Nat.log2_spec.
  destruct (eq_nat_dec x 0).
  subst.
  rewrite log2_0 in H.
  omega.
  omega.
  
  eapply le_trans.
  2:{
    eapply H2.
  }
  simpl.
  omega.
  
  assert ( y + y + 3 <= div2 x).
  eapply IHy.
  
  symmetry.
  apply log2_div2.
  trivial.
  omega.
  
  assert (2 <= div2 x).
  assert (2 = div2 4).
  trivial.
  rewrite H3.
  eapply div2_le_mono.
  eapply le_trans.
  2:{
    eapply Nat.log2_le_lin.
    destruct (eq_nat_dec 0 x); subst.
    rewrite log2_0 in H.
    omega.
    omega.
  }
  omega.
  
  eapply le_trans.
  eapply plus_le_compat.
  eapply H2.
  
  eapply H3.
  
  eapply div2_ge_double.
  
Qed.

Theorem S_log_square_lt_h : 
  forall y x,
    y = Nat.log2 x ->
    6 <= Nat.log2 x->
    S y * S y <= x.
  
  induction y; intuition; simpl in *.
  assert (y = Nat.log2 (div2 x)).
  symmetry.
  eapply log2_div2.
  trivial.

  rewrite (mult_comm _ (S (S y))).
  simpl.
  rewrite (mult_comm _ (S y)) in IHy.
  simpl in *.
  
  assert ( S (S (y + S (S (y + (y + (y + y * y)))))) = 
    (S (y + (y + y * y))) + (2 * y + 3)).
  omega.
  rewrite H2.
  clear H2.
  
  destruct (eq_nat_dec (Nat.log2 x) 6).
  
  assert (y = 5).
  assert (S y = 6).
  rewrite H.
  trivial.
  omega.
  rewrite H2.
  simpl.
  assert (x >= Nat.pow 2 6).
  rewrite <- e.
  
  eapply Nat.log2_spec.
  
  destruct (eq_nat_dec x 0).
  subst.
  rewrite log2_0 in H.
  omega.
  omega.
  
  eapply le_trans.
  2:{
    eapply H3.
  }
  simpl.
  omega.
  
  assert ( S (y + (y + y * y)) <= div2 x).
  eapply IHy.
  trivial.
  omega.
  
  assert (2 * y + 3 <= div2 x).
  eapply double_log_plus_3_le_h; trivial.
  omega.
  eapply le_trans.
  eapply plus_le_compat.
  eapply H2.
  eapply H3.
  
  eapply div2_ge_double.
  
Qed.

Theorem S_log_square_lt : 
  forall x, 
    Nat.pow 2 6 <= x->
    S (Nat.log2 x) * S (Nat.log2 x) <= x.
  
  intuition.
  eapply S_log_square_lt_h; trivial.
  eapply le_trans.
  2:{
    eapply Nat.log2_le_mono.
    eapply H.
  }
  rewrite Nat.log2_pow2; omega.
Qed.

Theorem log_square_lt : 
  forall x, 
    Nat.pow 2 6 <= x->
    Nat.log2 x * Nat.log2 x < x.
  
  intuition.
  
  assert (Nat.log2 x < S (Nat.log2 x)).
  omega.
  eapply lt_le_trans.
  
  eapply mult_lt_compat.
  eapply H0.
  eapply H0.
  eapply S_log_square_lt.
  trivial.
Qed.

Theorem poly_lt_exp_ge_6 : 
  forall c x, 
    x >= (Nat.pow 2 c) ->
    x >= (Nat.pow 2 6) ->
    Nat.pow x c < Nat.pow 2 x.
  
  intuition.
  
  specialize (Nat.log2_spec_alt); intuition.
  destruct (H1 x).
  eapply lt_le_trans.
  2:{
    eapply H.
  }
  eapply (expnat_2_ge_1 c).
  
  intuition.
  (* This case split probably isn't necessary *)
  destruct (eq_nat_dec x0 0).
  rewrite e in H3.
  rewrite plus_0_r in *.
  rewrite H3.
  rewrite <- Nat.pow_mul_r.
  
  eapply Nat.pow_lt_mono_r.
  omega.
  rewrite <- H3.

  assert (c <= Nat.log2 x).
  eapply (@Nat.pow_le_mono_r_iff 2).
  omega.
  rewrite <- H3.
  trivial.
  eapply le_lt_trans.
  eapply mult_le_compat.
  eapply le_refl.
  eapply H4.
  
  eapply log_square_lt.
  eapply le_trans.
  2:{
    eapply H0.
  }
  eapply Nat.pow_le_mono_r.
  omega.
  omega.
  
  destruct (eq_nat_dec c 0).
  rewrite e.
  simpl.
  eapply le_lt_trans.
  assert (1 <= expnat 2 0).
  trivial.
  eapply H4.
  eapply Nat.pow_lt_mono_r.
  omega.
  omega.
  
  assert (expnat x c < expnat (2 ^ S (Nat.log2 x)) c).
  eapply Nat.pow_lt_mono_l.
  omega.
  eapply Nat.log2_spec.
  omega.
  eapply lt_le_trans.
  eapply H4.
      
  rewrite <- Nat.pow_mul_r.
  eapply Nat.pow_le_mono_r.
  omega.
  assert (c <= S (Nat.log2 x)).
  eapply (@Nat.pow_le_mono_r_iff 2).
  omega.
  eapply le_trans.
  eapply H.
  
  eapply lt_le_weak.
  eapply Nat.log2_spec.
  omega.
  
  eapply le_trans.
  eapply mult_le_compat.
  eapply le_refl.
  eapply H6.
  
  eapply S_log_square_lt.
  eapply le_trans.
  2:{
    eapply H0.
  }
  eapply Nat.pow_le_mono_r.
  omega.
  omega.
Qed.

Theorem poly_lt_exp : 
  forall c, 
    exists x, 
      forall y, y >= x ->
        expnat y c < expnat 2 y.
  
  intuition.
  exists (expnat 2 (max c 6)).
  intuition.
  eapply poly_lt_exp_ge_6.
  eapply le_trans.
  2:{
    eapply H.
  }
  eapply Nat.pow_le_mono_r.
  omega.
  eapply Max.le_max_l.
  
  eapply le_trans.
  2:{
    eapply H.
  }
  eapply Nat.pow_le_mono_r.
  omega.
  eapply Max.le_max_r.
Qed.
    
Theorem negligible_exp_den : 
  negligible (fun n => 1 / expnat 2 n)%rat.
  
  unfold negligible in *.
  
  intuition.
  destruct (poly_lt_exp c).
  exists x.
  intuition.
  
  eapply (rat_num_not_le).
  eapply H1.
  
  unfold posnatToNat, natToPosnat.
  eapply H.
  omega.
Qed.


Theorem negligible_const_mult : 
  forall (n : nat) d f,
    negligible f -> 
    negligible (fun x => (RatIntro n d) * (f x))%rat.
  
  unfold negligible in *.
  intuition.
  
  destruct (eq_nat_dec n 0).
  subst.
  exists 1.
  intuition.
  
  assert ((1 / expnat x c) == 0)%rat.
  
  eapply leRat_0_eq.
  rewrite H1.
  rewrite rat_num_0.
  rewrite ratMult_0_l.
  intuition.
  
  eapply rat_num_nz; [idtac | eauto].
  omega.
  
  destruct (H (c + n)).
  exists (x + n)%nat.
  intuition.
  eapply H0.
  omega.
  
  assert (1 / expnat x0 (c + n) == RatIntro 1 (pos  (expnat x0 c)) * RatIntro 1 (pos (expnat x0 n)))%rat.
  rewrite <- ratMult_num_den.
  eapply eqRat_terms.
  symmetry.
  eapply mult_1_r.
  unfold natToPosnat, posnatToNat, posnatMult.
  rewrite expnat_plus.
  trivial.
  
  rewrite H3.
  rewrite H2.
  rewrite ratMult_comm.
  rewrite <- ratMult_assoc.
  
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    rewrite <- ratMult_1_l.
    eapply eqRat_refl.
  }
  eapply ratMult_leRat_compat; intuition.
  
  eapply rat_le_1.
  destruct d.
  unfold natToPosnat, posnatToNat, posnatMult.
  rewrite mult_comm.
  eapply mult_le_compat.
      
  eapply le_trans.
  eapply le_expnat_2.
  eapply expnat_base_le.
  omega.
  omega.

Qed.

Theorem negligible_mult_ident : 
  forall f,
    negligible f -> 
    negligible (fun x => (x / 1) * (f x))%rat.
  
  unfold negligible in *.
  intuition.
  
  destruct (H (S c)).
  exists x.
  intuition.
  eapply H0.
  omega.
  simpl.
  
  assert ( (RatIntro 1 (natToPosnat (expnat_nz (S c) pf_nz)))  == 
    RatIntro 1 (posnatMult (pos x0) (pos expnat x0 c)) )%rat.
  eapply eqRat_terms; trivial.
  
  simpl in *.
  rewrite H3.
  rewrite ratMult_denom.
  rewrite H2.
  rewrite <- ratMult_assoc.
  rewrite <- ratMult_num_den.
  rewrite num_dem_same_rat1.
  rewrite ratMult_1_l.
  intuition.
  unfold natToPosnat, posnatToNat, posnatMult.
  omega.
Qed.

Theorem negligible_exp : 
  forall z, 
    negligible (fun n => expnat n z / expnat 2 n)%rat.
  
  induction z; simpl in *; intuition.
  
  eapply negligible_exp_den.
  
  eapply negligible_eq.
  eapply negligible_mult_ident.
  eauto.
  intuition.
  rewrite <- ratMult_num_den.
  eapply eqRat_terms; trivial.
  unfold posnatToNat, natToPosnat, posnatMult.
  eapply mult_1_l.
  
Qed.

Theorem negligible_const_num : 
  forall k,
    negligible (fun n => k / expnat 2 n)%rat.
  
  intuition.
  eapply negligible_eq.
  eapply (@negligible_const_mult k (pos 1)).
  eapply negligible_exp_den.
  intuition.
  rewrite <- ratMult_num_den.
  eapply eqRat_terms.
  eapply mult_1_r.
  unfold natToPosnat, posnatToNat, posnatMult.
  eapply mult_1_l.
Qed.

Theorem negligible_poly_num : 
  forall f,
    polynomial f ->
    negligible (fun n => f n / expnat 2 n)%rat.
  
  intuition.
  unfold polynomial in *.
  do 3 destruct H.
  eapply negligible_le.
  intuition.
  eapply leRat_terms.
  eapply H.
  eapply le_refl.
  
  eapply negligible_eq. 
  eapply negligible_plus.
  eapply negligible_const_mult.
  eapply negligible_exp.
  eapply negligible_const_num.
  
  intuition.
  symmetry.
  
  rewrite ratAdd_num.
  eapply ratAdd_eqRat_compat.
  rewrite <- ratMult_num_den.
  eapply eqRat_terms.
  eauto.
  assert (posnatToNat (pos expnat 2 n) = posnatToNat (posnatMult (pos 1) (pos expnat 2 n))).
  unfold natToPosnat, posnatToNat, posnatMult.
  symmetry.
  eapply mult_1_l.
  eapply H0.
  eapply eqRat_refl.
Qed.