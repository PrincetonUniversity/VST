(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* RndNat -- a computation that returns a random nat uniformly distributed in a specified range. *)

Set Implicit Arguments.

Require Import fcf.Crypto.
Require Import Permutation.
Require Import fcf.NotationV1.
  
Definition RndNat_unchecked(n : nat) :=
  v <-$ {0,1} ^ (lognat n);
  let n := (bvToNat v) in
    ret n.

Definition ltNatBool := fun x1 x2 => if (lt_dec x1 x2) then true else false.

(* RndNat uses Repeat to get a number strictly less than n *)
Definition RndNat(n : nat) :=
    (Repeat (RndNat_unchecked n) (fun x => (ltNatBool x n))).

Notation "[ 0 '..' n )" := (RndNat n)
  (right associativity, at level 77) : comp_scope.

Lemma well_formed_RndNat : forall n,
  n > O ->
  well_formed_comp (RndNat n).
  
  intuition.
  unfold RndNat.
  eapply (well_formed_Repeat).
  unfold eq_dec.
  intuition.
  eapply eq_nat_dec.
  unfold RndNat_unchecked.
  eapply well_formed_Bind.
  eapply well_formed_Rnd.
  intuition.
  eapply well_formed_Ret.
  eapply filter_In.
  intuition.
  2:{
    unfold ltNatBool.
    assert ((if (lt_dec O n) then true else false) = true).
    destruct (lt_dec O n).
    trivial.
    omega.
    eapply H0.
  }
  simpl.
  eapply Fold.in_getUnique.
  eapply Fold.in_flatten.
  econstructor.
  split.
  
  eapply in_map_iff.
  econstructor.
  split.
  eauto.
  
  eapply in_getAllBvectors.
  
  specialize (bvNat_zero (lognat n)); intuition.
  simpl in *.
  left.
  eapply H0.
  
Qed.

Lemma RndNat_support_lt : forall n x,
  In x (getSupport (RndNat n)) ->
  x < n.
  
  intuition.
  unfold RndNat in *.
  simpl in *.
  eapply filter_In in H.
  intuition.
  unfold ltNatBool in *.
  destruct (lt_dec x n); congruence.
Qed.

Hint Resolve well_formed_RndNat : wftac.


Lemma RndNat_unchecked_lt_support : forall n v,
  v < n ->
  In v (getSupport (RndNat_unchecked n)).
  
  intuition.
  unfold RndNat_unchecked.

  eapply getSupport_In_Seq.
  eapply in_getAllBvectors.
  simpl.
  left.
  
  eapply bvToNat_natToBv_inverse.
  eapply lognat_monotonic.
  omega.
 
  
Qed.

Local Open Scope rat_scope.

Lemma RndNat_uniform : forall v1 v2 n,
  v1 < n ->
  v2 < n -> 
  evalDist (RndNat n) v1 == evalDist (RndNat n) v2.
  
  intuition.
    
  eapply evalDist_Repeat_eq; intuition.
  unfold RndNat_unchecked.
  remember (lognat n) as length.
  eapply (evalDist_iso
    (BVxor length (BVxor length (natToBv length v1) (natToBv length v2)))
    (BVxor length (BVxor length (natToBv length v1) (natToBv length v2)))); intuition.
  
(*
  eapply getSupport_In_evalDist.
  intuition.
  eapply getSupport_In_evalDist.
  intuition.
*)
 
  remember (BVxor length (natToBv length v1) (natToBv length v2)) as z.
  rewrite <- BVxor_assoc.
  rewrite BVxor_same_id.
  rewrite BVxor_id_l.
  trivial.
  
  rewrite <- BVxor_assoc.
  rewrite BVxor_same_id.
  rewrite BVxor_id_l.
  trivial.

  simpl.
  eapply in_getAllBvectors.
  
  eapply uniformity.
  
  simpl.
  destruct (EqDec_dec nat_EqDec (bvToNat x) v2); subst.
  destruct (EqDec_dec nat_EqDec
    (bvToNat
      (BVxor (lognat n)
        (BVxor (lognat n) (natToBv (lognat n) v1)
          (natToBv (lognat n) (bvToNat x))) x)) v1).
  intuition.
  exfalso.
  eapply n0.
    
  rewrite natToBv_bvToNat_inverse.
  
  rewrite BVxor_assoc.
  rewrite BVxor_same_id.
  rewrite BVxor_id_r.
  
  eapply bvToNat_natToBv_inverse.
  eapply lognat_monotonic.
  omega.
  
  destruct (EqDec_dec nat_EqDec
    (bvToNat
      (BVxor (lognat n)
        (BVxor (lognat n) (natToBv (lognat n) v1)
          (natToBv (lognat n) v2)) x)) v1).
  exfalso.
  eapply n0.
  rewrite BVxor_assoc in e.
  assert ((BVxor (lognat n) (natToBv (lognat n) v2) x) = (Bvect_false (lognat n))).
  eapply BVxor_id_r_inv.
  eapply bvToNat_natToBv_eq.
  eauto.
  apply BVxor_id_inv in H2.
  rewrite <- H2.
  
  eapply bvToNat_natToBv_inverse.
  eapply lognat_monotonic.
  omega.

  intuition.
  
  unfold ltNatBool.
  destruct (lt_dec v1 n); destruct (lt_dec v2 n); congruence.
  
  eapply filter_In; intuition.
  eapply RndNat_unchecked_lt_support.
  trivial.
  unfold ltNatBool.
  destruct (lt_dec v1 n); congruence.
Qed.

Lemma in_getSupport_RndNat : forall x k,
  x < k ->
  In x (getSupport (RndNat k)).
  
  intuition.
  simpl.
  eapply filter_In.
  split.
  eapply in_getUnique.
  eapply in_flatten.
  econstructor.
  split.
  eapply in_map_iff.
  econstructor.
  split.
  eapply eq_refl.
  eapply in_getAllBvectors.
  simpl.
  left.
  eapply bvToNat_natToBv_inverse.
  eapply lognat_monotonic.
  trivial.
  unfold ltNatBool.
  destruct (lt_dec x k); intuition.
Qed.

Lemma RndNat_support_length : 
  forall n, 
    length (getSupport (RndNat n)) = n.
  
  intuition.
  rewrite (@Permutation_length _ _ (forNats n)).
  eapply forNats_length.
  eapply NoDup_Permutation.
  eapply getSupport_NoDup.
  eapply forNats_NoDup.
  intuition.
  
  eapply forNats_In.
  eapply RndNat_support_lt; intuition.
  
  eapply in_getSupport_RndNat.
  eapply forNats_In; intuition.
  
Qed.

Theorem RndNat_prob : 
  forall n i (nzn : nz n),
    i < n ->
    evalDist (RndNat n) i == 1 / n.
  
  intuition.
  
  eapply (@ratMult_same_r_inv _ (n / 1)).
  rewrite ratMult_eq_rat1.
  eapply eqRat_trans.
  2:{
    eapply evalDist_lossless.
    eapply well_formed_RndNat.
    destruct nzn.
    apply agz.
  }
  
  symmetry.
  eapply eqRat_trans.
  eapply sumList_body_eq; intuition.
  eapply (@RndNat_uniform _ i).
  eapply RndNat_support_lt; intuition.
  trivial.
  rewrite sumList_body_const.  
  
  rewrite RndNat_support_length.
  intuition.
  intuition.
  eapply rat_num_nz.
  destruct nzn.
  eapply agz.
  eauto.
Qed.


Theorem RndNat_seq : 
  forall (n : posnat)(A : Set)(c : nat -> Comp A) a,
    evalDist (x <-$ RndNat n; c x) a ==
    (1 / n) * sumList (allNatsLt n) (fun z => evalDist (c z) a).
  
  intuition.
  rewrite evalDist_seq_step.
  eapply eqRat_trans.
  eapply sumList_body_eq.
  intros.
  eapply ratMult_eqRat_compat.
  eapply RndNat_prob.
  eapply RndNat_support_lt.
  trivial.
  eapply eqRat_refl.
  rewrite sumList_factor_constant_l.
  eapply ratMult_eqRat_compat; intuition.
  eapply sumList_permutation.
  eapply NoDup_Permutation.
  eapply getSupport_NoDup.
  eapply allNatsLt_NoDup.
  intuition.
  eapply allNatsLt_lt_if.
  eapply RndNat_support_lt.
  trivial.
  eapply in_getSupport_RndNat.
  eapply allNatsLt_lt.
  trivial.
  
Qed.

Lemma rndNat_sumList : 
  forall (A : Set)(f : nat -> Comp A) n (nzn : nz n) x,
    evalDist (i <-$ RndNat n; f i) x == 
    sumList (forNats n) (fun i => (1 / n) * (evalDist (f i) x)).
  
  intuition.
  unfold evalDist.
  fold evalDist.
  rewrite sumList_permutation.
  2:{
    eapply (@NoDup_Permutation _ _ (forNats n)).
    eapply getSupport_NoDup.
    eapply forNats_NoDup.
    intuition.

    eapply forNats_In.
    eapply RndNat_support_lt.
    trivial.
    eapply in_getSupport_RndNat.
    eapply forNats_In.
    trivial.
  }

  eapply sumList_body_eq.
  intuition.
  eapply ratMult_eqRat_compat; intuition.
  
  eapply RndNat_prob.
  eapply forNats_In.
  trivial.
Qed.