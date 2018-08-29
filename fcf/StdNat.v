(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
(* Definitions and theory of natural numbers that is useful in cryptographi proofs. *)

Set Implicit Arguments.

Require Export Arith.
Require Export Omega.
Require Export Arith.Div2.
Require Export Coq.Numbers.Natural.Peano.NPeano. 
Require Import Coq.NArith.BinNat.

Lemma mult_same_r : forall n1 n2 n3,
  n3 > 0 ->
  n1 * n3 = n2 * n3 ->
  n1 = n2.

  induction n1; destruct n2; intuition; simpl in *.
  remember (n2 * n3) as x.
  omega.
  remember (n1 * n3) as x.
  omega.
  
  f_equal.
  eapply IHn1; eauto.
  
  eapply plus_reg_l. eauto.
Qed.

Lemma mult_same_l : forall n3 n1 n2,
  n3 > 0 ->
  n3 * n1 = n3 * n2 ->
  n1 = n2.
  
  intuition.
  eapply mult_same_r; eauto.
  rewrite mult_comm.
  rewrite (mult_comm n2 n3).
  trivial.
Qed.

Lemma mult_gt_0 : forall n1 n2,
  n1 > 0 ->
  n2 > 0 ->
  n1 * n2 > 0.
  destruct n1; intuition; simpl in *.
  remember (n1 * n2) as x.
  omega.
Qed.

Lemma minus_eq_compat : forall n1 n2 n3 n4,
  n1 = n2 ->
  n3 = n4 ->
  n1 - n3 = n2 - n4.
  
  intuition.
Qed.

Lemma plus_eq_compat : forall n1 n2 n3 n4,
  n1 = n2 ->
  n3 = n4 ->
  n1 + n3 = n2 + n4.
  
  intuition.
Qed.

Lemma minus_diag_eq : forall n1 n2,
  n1 = n2 ->
  n1 - n2 = 0.
  
  intuition.
Qed.

Lemma le_eq : forall n1 n2,
  n1 = n2 ->
  n1 <= n2.
  
  intuition.
Qed.

Lemma minus_add_assoc : forall n1 n2 n3,
  (n3 <= n2)%nat ->
  (n1 + (n2 - n3) = n1 + n2 - n3)%nat.
  
  intuition.
Qed.




Class nz (a : nat) := {
  agz : a > 0
}.

Instance nz_nat : forall (n : nat), nz (S n).
intuition.
econstructor.
omega.
Defined.

Definition posnat := {n : nat | n > 0}.

Definition posnatToNat(p : posnat) :=
  match p with
    | exist _ n _ => n
  end.

Inductive posnatEq : posnat -> posnat -> Prop :=
  | posnatEq_intro : 
    forall (n1 n2 : nat) pf1 pf2,
      n1 = n2 ->
      posnatEq (exist _ n1 pf1) (exist _ n2 pf2).

Definition posnatMult(p1 p2 : posnat) : posnat :=
    match (p1, p2) with
      | (exist _ n1 pf1, exist _ n2 pf2) =>
        (exist (fun n => n > 0) (n1 * n2) (mult_gt_0 pf1 pf2))
    end.

Lemma posnatMult_comm : forall p1 p2,
  (posnatEq (posnatMult p1 p2) (posnatMult p2 p1)).

  intuition.
  unfold posnatMult.
  destruct p1; destruct p2.
  econstructor.
  apply mult_comm.
Qed.  

Coercion posnatToNat : posnat >-> nat.

Lemma posnat_pos : forall (p : posnat),
  p > 0.
  
  intuition.
  destruct p.
  unfold posnatToNat.
  trivial.
Qed.

Instance nz_posnat : forall (p : posnat),
  nz p.

intuition.
econstructor.
eapply posnat_pos.

Qed.

Definition natToPosnat(n : nat)(pf : nz n) :=
  (exist (fun x => x > 0) n agz).

Notation "'pos' x" := (@natToPosnat x _) (at level 40).

Fixpoint expnat n1 n2 :=
  match n2 with
    | 0 => 1
    | S n2' =>
      n1 * (expnat n1 n2')
  end.

Theorem expnat_pos : forall x n,
  x > 0 ->
  expnat x n > 0.
  
  induction n; intuition; simpl in *.
  remember (x * expnat x n) as y.
  assert (y <> 0); try omega.
  intuition; subst.
  apply mult_is_O in H1.
  destruct H1; omega.

Qed.

Lemma div2_le : forall n,
  le (div2 n) n.
  
  intuition.

  eapply PeanoNat.Nat.div2_decr.
  omega.
  
Qed.

Lemma div2_ge_double : forall n, 
  n >= (div2 n) + (div2 n).
  
  intuition.
  destruct (Even.even_odd_dec n).
  
  rewrite (even_double n) at 1.
  unfold double.
  omega.
  trivial.
  rewrite (odd_double n) at 1.
  unfold double.
  omega.
  trivial.
Qed.

Local Open Scope N_scope.
Definition modNat (n : nat)(p : posnat) : nat :=
  N.to_nat ((N.of_nat n) mod (N.of_nat p)).

Lemma Npos_nz : forall p, 
  Npos p <> N0.

  destruct p; intuition; simpl in *.
  inversion H.
  inversion H.
  inversion H.
Qed.

Lemma modNat_plus : forall n1 n2 p,
    (modNat (n1 + n2) p = modNat ((modNat n1 p) + n2) p)%nat.
  
  unfold modNat.

  intuition.
  rewrite Nnat.Nat2N.inj_add.

  rewrite <- N.add_mod_idemp_l.
  f_equal.
  rewrite <- (Nnat.Nat2N.id n2) at 2.
  rewrite Nnat.Nat2N.inj_add.
  repeat rewrite Nnat.N2Nat.id.
  trivial.

  destruct p.
  simpl.
  
  destruct x;
  simpl.
  omega.
  

  apply Npos_nz.

Qed.


Lemma modNat_arg_eq : forall (p : posnat),
  modNat p p = O.

  intuition.
  unfold modNat.
  rewrite N.mod_same.
  trivial.
  unfold N.of_nat, posnatToNat.
  destruct p.
  destruct x.
  omega.
  apply Npos_nz.

Qed.

Lemma of_nat_ge_0 : forall n,
  0 <= N.of_nat n.

  intuition.
  unfold N.of_nat.
  destruct n.
  intuition.

  simpl.
  unfold N.le.
  case_eq ((0 ?= N.pos (Pos.of_succ_nat n))); intuition;
    try discriminate.
Qed.

Lemma of_posnat_gt_0 : forall (p : posnat),
  0 < N.of_nat p.

  intuition.
  unfold N.of_nat, posnatToNat.
  destruct p.
  destruct x.
  omega.
  destruct x; intuition; simpl in *.
  
  case_eq (N.compare 0 1)%N; intuition.
  inversion H.
  inversion H.

  case_eq (N.compare 0 (N.pos (Pos.succ (Pos.of_succ_nat x))))%N; intuition.
  inversion H.
  inversion H.
Qed.

Lemma modNat_lt : forall x p, (modNat x p < p)%nat.

  intuition.
  unfold modNat.
  assert (N.of_nat x mod N.of_nat p < N.of_nat p)%N.
  apply N.mod_bound_pos.
  apply of_nat_ge_0.
  apply of_posnat_gt_0.

  specialize (Nnat.N2Nat.inj_compare); intuition.
  rewrite <- (Nnat.Nat2N.id p) at 2.
  apply nat_compare_lt.
  rewrite <- H0.
  apply N.compare_lt_iff.
  trivial.

Qed.

Lemma modNat_eq : forall (n : posnat) x, (x < n -> modNat x n = x)%nat.
  
  intuition.
  unfold modNat.
  rewrite N.mod_small.
  apply Nnat.Nat2N.id.
  specialize (Nnat.N2Nat.inj_compare); intuition.
  specialize (N.compare_lt_iff (N.of_nat x) (N.of_nat n)); intuition.
  apply H2.
  rewrite H0.
  repeat rewrite Nnat.Nat2N.id.
  apply nat_compare_lt.
  trivial.
Qed.

Definition modNatAddInverse (n : nat)(p : posnat) :=
  (p - (modNat n p))%nat.

Lemma modNatAddInverse_correct_gen : forall x y p,
  modNat x p = modNat y p ->
  modNat (x + modNatAddInverse y p) p = O.
  
  intuition.
  unfold modNatAddInverse.
  rewrite <- H.
  rewrite modNat_plus.
  rewrite minus_add_assoc.
  rewrite (plus_comm).
  rewrite <- minus_add_assoc.
  rewrite minus_diag.
  rewrite plus_0_r.
  apply modNat_arg_eq.
  
  trivial.
  
  assert (modNat x p < p)%nat.
  apply modNat_lt.
  omega.
  
Qed.

Lemma modNatAddInverse_correct : forall n p,
    modNat (n + modNatAddInverse n p) p = O.

  intuition.
  eapply modNatAddInverse_correct_gen.
  trivial.
  
Qed.

Lemma modNat_correct : forall x (p : posnat),
  exists k, (x = k * p + modNat x p)%nat.

  intuition.
  unfold modNat in *.
  assert (p > 0)%nat.
  eapply posnat_pos.
  assert (posnatToNat p <> 0)%nat.
  omega.
  assert (N.of_nat p <> 0%N).
  intuition.
  eapply H0.
  
  rewrite <- Nnat.Nat2N.id.
  rewrite <- (Nnat.Nat2N.id p).
  f_equal.
  trivial.

  exists (N.to_nat (N.of_nat x / N.of_nat p)).
  rewrite N.mod_eq; trivial.

  rewrite <- (Nnat.Nat2N.id p) at 2.
  rewrite <- Nnat.N2Nat.inj_mul.
  rewrite <- Nnat.N2Nat.inj_add.
  rewrite N.mul_comm.
  remember (N.of_nat p * (N.of_nat x / N.of_nat p)) as z.
  rewrite N.add_sub_assoc.
  rewrite N.add_comm.
  rewrite N.add_sub.
  rewrite Nnat.Nat2N.id.
  trivial.

  subst.  
  eapply N.mul_div_le.
  trivial.
Qed.

Lemma modNat_divides : forall x p,
  modNat x p = O ->
  exists k, (x = k * p)%nat.

  intuition.
  destruct (modNat_correct x p).
  rewrite H in H0.
  econstructor.
  rewrite plus_0_r in H0.
  eauto.
Qed.


Local Open Scope nat_scope.
Lemma modNatAddInverse_sum_0 : forall x y p,
  modNat (x + (modNatAddInverse y p)) p = O ->
  modNat x p = modNat y p.
  
  intuition.
  
  assert (modNat x p < p).
  eapply modNat_lt.
  assert (modNat y p < p).
  eapply modNat_lt.
  
  rewrite modNat_plus in H.
  unfold modNatAddInverse in *.
  rewrite minus_add_assoc in H; intuition.
  rewrite plus_comm in H.
  
  apply modNat_divides in H.
  destruct H.
  
  remember (modNat x p) as a.
  remember (modNat y p) as b.
  assert (p + a >= p).
  omega.
  assert (p + a < 2 * p)%nat.
  omega.
  assert (p + a - b < 2 * p).
  omega.
  assert (p + a - b > 0).
  omega.
  
  assert (x0 * p > 0).
  omega.
  assert (x0 * p < 2 * p).
  omega.
  
  destruct x0.
  omega.
  destruct x0.
  
  simpl in H.
  rewrite plus_0_r in H.
  omega.
  
  assert (p > 0).
  eapply posnat_pos.
  simpl in H7.
  remember (x0 * p)%nat as c.
  omega.
Qed.

Lemma modNat_correct_if : forall x y z (p : posnat),
  x * p + y = z ->
  modNat z p = modNat y p.
  
  induction x; intuition; simpl in *.
  subst.
  trivial.
  
  assert (x * p + (y + p) = z).
  omega.
  apply IHx in H0.
  
  rewrite H0.
  rewrite plus_comm.
  rewrite modNat_plus.
  rewrite modNat_arg_eq.
  rewrite plus_0_l.
  trivial.
Qed.

Lemma modNat_mult : forall x (p : posnat),
  modNat (x * p) p = 0.
  
  induction x; intuition; simpl in *.
  rewrite modNat_plus.
  rewrite modNat_arg_eq.
  rewrite plus_0_l.
  eauto.
  
Qed.

Lemma modNat_add_same_l : forall x y z p,
  modNat (x + y) p = modNat (x + z) p ->
  modNat y p = modNat z p.
  
  induction x; intuition; simpl in *.
  assert (S (x + y) = x + S y).
  omega.
  rewrite H0 in H.
  clear H0.
  assert (S (x + z) = x + S z).
  omega.
  rewrite H0 in H.
  clear H0.
  apply IHx in H.
  
  destruct (modNat_correct (S y) p).
  destruct (modNat_correct (S z) p).
  rewrite H in H0.
  
  assert (S y - x0 * p = modNat (S z) p).
  omega.
  assert (S z - x1 * p = modNat (S z) p).
  omega.
  rewrite <- H2 in H3.
  
  assert (z - x1 * p = y - x0 * p).
  omega.
  
  assert (x1 * p + y = x0 * p + z).
  omega.
  
  apply modNat_correct_if in H5.
  rewrite modNat_plus in H5.
  
  rewrite modNat_mult in H5.
  rewrite plus_0_l in H5.
  auto.
  
Qed.

Lemma modNat_add_same_r : forall x y z p,
  modNat (y + x) p = modNat (z + x) p ->
  modNat y p = modNat z p.
  
  intuition.
  eapply (modNat_add_same_l x y z).
  rewrite plus_comm.
  rewrite H.
  rewrite plus_comm.
  trivial.
Qed.

Lemma expnat_base_S : forall n k,
  ((expnat k n) + n * (expnat k (pred n)) <= expnat (S k) n)%nat.

  induction n; intuition.
  simpl in *.
  eapply le_trans.
  
  2:{
    eapply plus_le_compat.
    eapply IHn.
    eapply mult_le_compat.
    eapply le_refl.
    eapply IHn.
  }

  rewrite mult_plus_distr_l.
  repeat rewrite mult_assoc.
  repeat rewrite plus_assoc.
  eapply plus_le_compat.
  rewrite plus_comm.
  eapply plus_le_compat.
  rewrite <- (plus_0_r (expnat k n)) at 1.
  eapply plus_le_compat. 
  omega.
  intuition.
  intuition.

  rewrite (mult_comm k n).
  rewrite <- (mult_assoc n).
  destruct n; simpl; intuition.
Qed.

Lemma expnat_base_S_same : forall n,
  n > 0 ->
  (2 * (expnat n n) <= expnat (S n) n)%nat.

  intuition.
  simpl in *.
  rewrite plus_0_r.
  eapply le_trans.
  2:{
    eapply expnat_base_S.
  }
  destruct n; simpl.
  omega.
  intuition.
Qed.

Lemma sqrt_le_lin_gen : forall a b,
  (a <= b ->
    Nat.sqrt a <= b)%nat.
  
  intuition.
  eapply le_trans.
  eapply Nat.sqrt_le_lin.
  trivial.
Qed.

Lemma div2_le_mono : forall n1 n2,
  (n1 <= n2 -> 
    div2 n1 <= div2 n2)%nat.
  
  induction n1; intuition.
  destruct n2.
  omega.
  destruct (Even.even_odd_dec n1).
  destruct (Even.even_odd_dec n2).
  repeat rewrite <- even_div2; trivial.
  eapply IHn1.
  omega.
  
  rewrite <- even_div2; trivial.
  rewrite <- odd_div2; trivial.
  econstructor.
  eapply IHn1.
  omega.
  
  destruct (Even.even_odd_dec n2).
  destruct (lt_dec n1 n2).
  assert (n1 <= (S n2))%nat.
  omega.
  destruct n2.
  omega.
  rewrite <- odd_div2; trivial.
  rewrite <- even_div2.
  rewrite <- odd_div2.
  eapply le_n_S.
  eapply IHn1.
  omega.
  inversion e.
  trivial.
  trivial.
  assert (n1 = n2).
  omega.
  subst.
  exfalso.
  eapply Even.not_even_and_odd; eauto.
  
  rewrite <- odd_div2; trivial.
  rewrite <- odd_div2; trivial.
  eapply le_n_S.
  eapply IHn1.
  omega.
  
Qed.

Lemma div2_ge : forall n n',
  n >= n' ->
  forall x,
    (n' = 2 * x)%nat ->
    div2 n >= x.
  
  induction 1; intuition; subst; simpl in *.
  specialize (div2_double x); intuition; simpl in *.
  rewrite H.
  omega.
  
  destruct m.
  omega.
  destruct (Even.even_odd_dec m).
  rewrite even_div2.
  assert (div2 (S m) >= x).
  eapply IHle.
  trivial.
  omega.
  trivial.
  
  rewrite odd_div2.
  
  eapply IHle.
  trivial.
  trivial.
Qed.

Instance expnat_nz : forall k n (p : nz n),
  nz (expnat n k).

intuition.

induction k; intuition; simpl in *.
econstructor.
omega.
econstructor.
edestruct IHk; eauto.
destruct p.
eapply mult_gt_0; intuition.

Qed.
  
Lemma expnat_2_ge_1 : forall n,
  (1 <= expnat 2 n)%nat.

  induction n; intuition; simpl in *.
  omega.
Qed.

Lemma le_expnat_2 : forall n,
  (n <= expnat 2 n)%nat.

  induction n; intuition; simpl in *.
  rewrite plus_0_r.
  assert (S n = 1 + n)%nat.
  omega.
  rewrite H.
  eapply plus_le_compat.
  eapply expnat_2_ge_1.
  trivial.
  
Qed.

Lemma expnat_1 : forall k,
  expnat 1%nat k = 1%nat.

  induction k; intuition; simpl in *.
  rewrite plus_0_r.
  trivial.

Qed.

Theorem expnat_base_le : 
  forall k n1 n2,
    n1 <= n2 ->
    expnat n1 k <=
    expnat n2 k.
  
  induction k; intuition; simpl in *.
  eapply mult_le_compat; intuition.
  
Qed.

Theorem expnat_double_le : 
  forall k n,
    n >= 2 ->
    expnat n (S k) >= 2 * expnat n k.

  induction k; intuition; simpl in *.
  omega.
  rewrite plus_0_r.
  rewrite <- mult_plus_distr_l.
  eapply mult_le_compat.
  trivial.
  rewrite <- plus_0_r at 1.
  rewrite <- plus_assoc.
  eapply IHk.
  trivial.
Qed.

Theorem nat_half_plus : 
  forall x, 
    x > 1 ->
    exists a b,
      a > 0 /\ b <= 1 /\ x = 2 * a + b.
  
  induction x; intuition; simpl in *.
  omega.
  
  destruct (eq_nat_dec x 1); subst.
  exists 1.
  exists 0.
  intuition; omega.
  
  edestruct (IHx).
  omega.
  destruct H0.
  intuition.
  destruct x1.
  rewrite plus_0_r in H3.
  exists x0.
  exists 1.
  subst.
  intuition; omega.
  
  exists (S x0).
  exists 0.
  subst.
  intuition.
            
Qed.

Theorem log2_div2 : 
  forall x y,
    S y = Nat.log2 x ->
    Nat.log2 (div2 x) = y.
  
  intuition.
  specialize (Nat.log2_double); intuition.
  
  destruct (@nat_half_plus x).
  eapply Nat.log2_lt_cancel.
  rewrite Nat.log2_1.
  omega.
  destruct H1.
  intuition.
  subst.
  destruct x1.
  rewrite plus_0_r in *.
  rewrite div2_double.
  rewrite H0 in H.
  omega.
  omega.
  
  destruct x1.
  
  rewrite plus_comm.
  rewrite div2_double_plus_one.
  
  rewrite Nat.log2_succ_double in H.
  omega.
  omega.
  
  omega.
  
Qed.

Lemma log2_0 : 
  Nat.log2 0 = 0.
  trivial.
Qed.

Theorem expnat_0 : 
  forall k,
    k > 0 ->
    expnat 0 k = 0.
  
  induction k; intuition; simpl in *.
  
Qed.

Theorem expnat_plus : 
  forall k1 k2 n,
    expnat n (k1 + k2) = expnat n k1 * expnat n k2.
  
  induction k1; simpl in *; intuition.
  rewrite IHk1.
  rewrite mult_assoc.
  trivial.
  
Qed.

Theorem expnat_ge_1 :
  forall k n,
    n > 0 ->
    1 <= expnat n k.
  
  induction k; intuition; simpl in *.
  rewrite <- mult_1_r at 1.
  eapply mult_le_compat.
  omega.
  eauto.
Qed.


Theorem expnat_exp_le : 
  forall n2 n4 n,
    (n2 > 0 \/ n > 0) ->
    n2 <= n4 ->
    expnat n n2 <= expnat n n4.
  
  induction n2; destruct n4; simpl in *; intuition.
  rewrite <- mult_1_l at 1.
  eapply mult_le_compat.
  omega.
  eapply expnat_ge_1; trivial.
  
  destruct (eq_nat_dec n 0); subst.
  simpl; intuition.
  eapply mult_le_compat; intuition.
  
Qed.

Lemma mult_lt_compat : 
  forall a b c d,
    a < b ->
    c < d ->
    a * c < b * d.
  
  intuition.
  eapply le_lt_trans.
  eapply mult_le_compat.
  assert (a <= b).
  omega.
  eapply H1.
  eapply le_refl.
  eapply mult_lt_compat_l.
  trivial.
  omega.
Qed.

Theorem orb_same_eq_if : 
  forall a b c,
    (a = false -> b = c) ->
    orb a b = orb a c.
  
  intuition.
  destruct a; trivial; intuition.
     
Qed.