(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* A theory of limits of a sequence *)

Set Implicit Arguments.

Require Import Arith.
Require Import fcf.Fold.
Require Import List.

Require Import fcf.StdNat.
Require Import fcf.Rat.

Section Limit.

  Variable A : Set.
  Variable eq : A -> A -> Prop.
  Hypothesis eq_dec : forall (a1 a2 : A), 
    {eq a1 a2} + {~eq a1 a2}.
  Hypothesis eq_refl : forall (a : A),
    eq a a.
  Hypothesis eq_symm : forall a1 a2,
    eq a1 a2 ->
    eq a2 a1.

  Variable distance : A -> A -> A.
  Hypothesis distance_comm : forall a1 a2,
    eq (distance a1 a2) (distance a2 a1).
  Variable half : A -> A.
  Variable zero : A.
  Hypothesis half_nz : forall (a : A),
    ~eq a zero ->
    ~eq (half a) zero.

  Hypothesis distance_eq_zero : forall (a1 a2 : A),
    eq a1 a2 <->
    eq (distance a1 a2) zero.
  Hypothesis distance_eq_compat : forall a1 a2 a3 a4,
    eq a1 a3 ->
    eq a2 a4 ->
    eq (distance a1 a2) (distance a3 a4).
 

  Variable le : A -> A -> Prop.
  Hypothesis le_eq : forall (a1 a2 : A),
    eq a1 a2 ->
    le a1 a2.
  Hypothesis le_trans : forall (a1 a2 a3 : A),
    le a1 a2 ->
    le a2 a3 ->
    le a1 a3.
  
  (* all numbers positive *)
  Hypothesis all_pos : forall (a : A),
    le zero a.
  Hypothesis le_impl_eq : forall (a1 a2 : A),
    le a1 a2 ->
    le a2 a1 ->
    eq a1 a2.

  Variable plus : A -> A -> A.
  Variable plus_0_eq : forall (a1 a2 : A),
    eq a2 zero ->
    eq a1 (plus a1 a2).
  Variable plus_le_compat : forall a1 a2 a3 a4,
    le a1 a2 ->
    le a3 a4 ->
    le (plus a1 a3) (plus a2 a4).

  Hypothesis triangle_inequality : forall (a1 a2 a3 : A),
    le (distance a1 a2) (plus (distance a1 a3) (distance a3 a2)).
  Hypothesis half_plus : forall (a : A),
    eq (plus (half a) (half a)) a.
  Hypothesis le_half : forall (a : A),
    le a (half a) ->
    eq a zero.

  Theorem le_epsilon_zero : forall (a : A),
    (forall (epsilon : A), ~eq epsilon zero -> le a epsilon) ->
    eq a zero.
    
    intuition.
    
    destruct (eq_dec a zero).
    trivial.
    
    exfalso.
    specialize (H (half a)).
    apply f.
    eapply le_half.
    apply H.
    eapply half_nz.
    trivial.
  Qed.


  Definition left_total(r : nat -> A -> Prop) :=
    forall n, exists a, r n a.

  Definition functional(r : nat -> A -> Prop) :=
    forall n a1 a2,
      r n a1 ->
      r n a2 ->
      eq a1 a2.
    

  Definition inf_limit(f : nat -> A -> Prop)(a : A) :=
    forall (epsilon : A),
      ~eq epsilon zero -> 
      exists n : nat,
        forall (n' : nat),
          n' >= n ->
          forall a',
            f n' a' ->
            le (distance a' a) epsilon.

    (* Note: if the codomain of the relation is empty (after any point), then we can assign any limit to it. *)

  (* We could define inf_limit in terms of inf_limit_2, but inf_limit_2 only shows up in proofs, while inf_limit shows up in top-level definitions. *)
  Definition inf_limit_2(f f' : nat -> A -> Prop) :=
    forall (epsilon : A),
      ~eq epsilon zero -> 
      exists n : nat,
        forall (n' : nat),
          n' >= n ->
          forall a a',
            f n' a ->
            f' n' a' ->
            le (distance a a') epsilon.
  
  Theorem inf_limit_2_const : forall (f : nat -> A -> Prop)(a : A),
    inf_limit_2 f (fun x => eq a) <->
    inf_limit f a.

    intuition.
  Abort.


(*  limits are unique for left-total relations *)
  Theorem limit_eq_h : forall f epsilon a1 a2,
    left_total f ->
    ~eq epsilon zero ->
    inf_limit f a1 ->
    inf_limit f a2 ->
    le (distance a1 a2) epsilon.
    
   (*  remember half as h. *)

    intuition.
    unfold inf_limit in *.
    intuition.
    specialize (H1 (half epsilon)).
    specialize (H2 (half epsilon)).

    destruct H1.
    intuition.
    eapply half_nz; eauto.

    destruct H2.
    intuition.
    eapply half_nz; eauto.

    destruct (H (max x x0)).
    specialize (H1 (max x x0)).
    specialize (H2 (max x x0)).

    eapply le_trans.
    eapply (triangle_inequality _ _ x1).
    eapply le_trans.
    eapply plus_le_compat.
    eapply le_trans.
    eapply le_eq.
    eapply distance_comm.
    eapply H1.
    eapply Max.max_lub_l; eauto.
    trivial.
    eapply H2.
    eapply Max.max_lub_r; eauto.
    trivial.
    eapply le_eq.
    eapply half_plus.
  Qed.    

  Theorem limits_eq : forall f a1 a2,
    left_total f ->
    inf_limit f a1 ->
    inf_limit f a2 ->
    eq a1 a2.

    intuition.
    eapply distance_eq_zero.

    eapply le_epsilon_zero.
    intuition.
 
    eapply limit_eq_h; eauto.
  Qed.

  Theorem limit_f_eq : forall f1 f2 a,
    inf_limit f1 a ->
    (forall n a', (f1 n a' <-> f2 n a')) ->
    inf_limit f2 a.

    unfold inf_limit; intuition.

    destruct (H epsilon).
    trivial.
    exists x.
    intuition.
    eapply H2.
    eapply H3.
    eapply H0.
    trivial.
  Qed.

End Limit.


(* limits for Rat *)
Local Open Scope rat_scope.

Definition rat_inf_limit(f : nat -> Rat -> Prop)(r : Rat) :=
  inf_limit eqRat ratDistance rat0 leRat f r.

Definition rat_inf_limit_2(f1 f2 : nat -> Rat -> Prop) :=
  inf_limit_2 eqRat ratDistance rat0 leRat f1 f2.

Definition rat_limits_eq :=
  limits_eq eq_Rat_dec ratDistance_comm ratHalf ratHalf_ne_0 ratIdentityIndiscernables eqRat_impl_leRat leRat_trans ratAdd ratAdd_leRat_compat ratTriangleInequality ratHalf_add le_ratHalf_0.

Require Import Arith.

Theorem rat_inf_limit_2_trans : forall f1 f2 f3,
  rat_inf_limit_2 f1 f2 ->
  rat_inf_limit_2 f2 f3 ->
  left_total f2 ->
  rat_inf_limit_2 f1 f3.
  
  unfold rat_inf_limit_2, inf_limit_2; intuition.
  edestruct (H (ratHalf epsilon)).
  eapply ratHalf_ne_0; intuition.
  edestruct (H0 (ratHalf epsilon)); eauto.
  eapply ratHalf_ne_0.
  intuition.
  exists (max x x0).
  intuition.
  destruct (H1 n').
  eapply leRat_trans.
  eapply ratDistance_le_trans.
  eapply H3.
  eapply Max.max_lub_l.
  eapply H5.
  trivial.
  eapply H8.
  eapply H4.
  eapply Max.max_lub_r.
  eapply H5.
  eauto.
  trivial.
  eapply eqRat_impl_leRat.
  eapply ratHalf_add.
Qed.



Lemma rat_inf_limit_squeeze : forall (f1 f2 f: nat -> Rat -> Prop) c (v : Rat),
  rat_inf_limit f1 v ->
  rat_inf_limit f2 v ->
  (forall n a a1, n >= c -> f n a -> f1 n a1 -> a1 <= a) ->
  (forall n a a2, n >= c -> f n a -> f2 n a2 -> a <= a2) ->
  left_total f1 ->
  left_total f2 ->
  rat_inf_limit f v.

  unfold rat_inf_limit, inf_limit in *.
  intuition.
  destruct (H epsilon); intuition.
  destruct (H0 epsilon); intuition.
  exists (max c (max x x0)).
  intuition.

  destruct (H3 n').
  destruct (H4 n').
  eapply leRat_trans.
  eapply ratDistance_le_max.
  eapply H1.
  eapply Max.max_lub_l.
  eauto.
  eapply H9.
  eapply H10.

  eapply H2.
  eapply Max.max_lub_l.
  eauto.
  eapply H9.
  eapply H11.

  eapply maxRat_leRat_same; eauto using Max.max_lub_l, Max.max_lub_r.

Qed.

Lemma rat_inf_limit_div_2 : forall (f : nat -> Rat -> Prop)(v : Rat),
  rat_inf_limit f v ->
  rat_inf_limit (fun n => (f (div2 n))) v.

  unfold rat_inf_limit, inf_limit.
  intuition.
  destruct (H epsilon); intuition.
  
  econstructor.
  intuition.
  specialize (H1 (div2 n')).
  eapply H1.

  eapply div2_ge; eauto.
  eauto.
Qed.

Lemma rat_inf_limit_sum : forall (f1 f2 : nat -> Rat -> Prop) v1 v2,
  left_total f1 ->
  left_total f2 ->
  rat_inf_limit f1 v1 ->
  rat_inf_limit f2 v2 ->
  rat_inf_limit (fun n => (ratAdd_rel (f1 n) (f2 n))) (v1 + v2).

  unfold rat_inf_limit, inf_limit in *.
  intuition.
  edestruct (H1 (ratHalf epsilon)).
  eapply ratHalf_ne_0.
  intuition.
  edestruct (H2 (ratHalf epsilon)).
  eapply ratHalf_ne_0.
  intuition.
  exists (Max.max x x0).
  intuition.
  unfold ratAdd_rel in *.
  destruct (H n').
  destruct (H0 n').
  rewrite H7; eauto.
  eapply leRat_trans.
  eapply rat_distance_of_sum.
  rewrite H4.
  rewrite H5.
  rewrite ratHalf_add.
  intuition.
  eapply Max.max_lub_r.
  eauto.
  trivial.
  eapply Max.max_lub_l.
  eauto.
  trivial.
Qed.



Lemma rat_inf_limit_difference : forall (f1 f2 : nat -> Rat -> Prop) c1 c2,
  left_total f1 ->
  left_total f2 ->
  rat_inf_limit f1 c1 ->
  rat_inf_limit f2 c2 -> 
  rat_inf_limit (fun n => (ratSubtract_rel (f1 n) (f2 n))) (ratSubtract c1 c2).

  unfold rat_inf_limit, inf_limit in *.
  intuition.

  destruct (le_Rat_dec c1 c2).

  edestruct (H1 (ratHalf epsilon)).
  eapply ratHalf_ne_0.
  intuition.  
  edestruct (H2 (ratHalf epsilon)).
  eapply ratHalf_ne_0.
  intuition. 
  exists (Max.max x x0).
  intuition.
  unfold ratSubtract_rel in *.
  destruct (H n').
  destruct (H0 n').
  rewrite H7; eauto.
  rewrite (ratSubtract_0 l).
  eapply ratDistance_0_r_le.
  
  eapply leRat_trans.
  eapply ratSubtract_partition_leRat.
  
  eapply ratSubtract_ratDistance_le.
  2:{
    rewrite H4.
    rewrite ratHalf_add.
    intuition.
    eapply Max.max_lub_l.
    eauto.
    trivial.
  }
  eapply leRat_trans.
  eapply ratSubtract_partition_leRat.
  rewrite ratSubtract_0.
  eapply leRat_refl.
  eapply l.
  eapply ratSubtract_ratDistance_le.
  rewrite ratDistance_comm.
  rewrite H5.
  rewrite <- ratAdd_0_l.
  intuition.
  eapply Max.max_lub_r.
  eauto.
  trivial.

  edestruct (H1 (minRat (ratHalf epsilon) (ratHalf (ratSubtract c1 c2)))).
  intuition.
  unfold minRat in *.
  destruct (bleRat (ratHalf epsilon) (ratHalf (ratSubtract c1 c2))).
  eapply ratHalf_ne_0 in H4;
  intuition.
  eapply ratHalf_ne_0 in H4;
  intuition.
  eapply n.
  eapply ratSubtract_0_inv.
  trivial.

  edestruct (H2 (minRat (ratHalf epsilon) (ratHalf (ratSubtract c1 c2)))).
  intuition.
  unfold minRat in *.
  destruct (bleRat (ratHalf epsilon) (ratHalf (ratSubtract c1 c2))).
  eapply ratHalf_ne_0 in H5;
  intuition.
  eapply ratHalf_ne_0 in H5;
  intuition.
  eapply n.
  eapply ratSubtract_0_inv.
  trivial.

  exists (Max.max x x0).
  intuition.
  destruct (H n').
  destruct (H0 n').
  unfold ratSubtract_rel in *.
  rewrite H7; eauto.
  assert (x2 <= x1).
  eapply leRat_trans.
  eapply ratDistance_le_sum.
  eapply H5.
  eapply Max.max_lub_r.
  eauto.
  trivial.
  eapply leRat_trans.
  eapply ratAdd_leRat_compat.
  eapply leRat_refl.

  eapply minRat_le_r.
  eapply (leRat_ratAdd_same_r (ratHalf (ratSubtract c1 c2))).
  rewrite ratAdd_assoc.
  rewrite ratHalf_add.
  rewrite ratSubtract_ratAdd_inverse_2.
  eapply ratDistance_le_sum.
  eapply leRat_trans.
  rewrite ratDistance_comm.
  eapply H4.
  eapply Max.max_lub_l.
  eauto.
  trivial.
  eapply minRat_le_r.
  case_eq (bleRat c1 c2); intuition.
  eapply bleRat_total.
  trivial.

  eapply leRat_trans.
  eapply rat_distance_of_difference.
  trivial.
  case_eq (bleRat c1 c2); intuition.
  eapply bleRat_total.
  trivial.

  eapply H4.
  eapply Max.max_lub_l.
  eauto.
  trivial.

  eapply H5.
  eapply Max.max_lub_r.
  eauto.
  trivial.

  rewrite minRat_le_l.
  rewrite ratHalf_add.
  intuition.
Qed.

Lemma rat_inf_limit_product : forall (f1 f2 : nat -> Rat -> Prop) c1 c2,
  left_total f1 ->
  left_total f2 ->
  rat_inf_limit f1 c1 ->
  rat_inf_limit f2 c2 -> 
  rat_inf_limit (fun n => (ratMult_rel (f1 n) (f2 n))) (c1 * c2).

  (* This is the proof found at http://planetmath.org/ProofOfLimitRuleOfProduct.html *)

  unfold rat_inf_limit, inf_limit in *.
  intuition.

  edestruct (H1 ((ratInverse (1 + c2)) * epsilon * (1/ 2))).
  intuition.
  apply ratMult_0 in H4.
  intuition.
  apply ratMult_0 in H5.
  intuition.
  eapply ratInverse_nz.
  eauto.

  edestruct (H2 ((ratInverse (1 + c1)) * epsilon * (1 / 2))).
  intuition.
  apply ratMult_0 in H5.
  intuition.
  apply ratMult_0 in H6.
  intuition.
  eapply ratInverse_nz.
  eauto.

  edestruct (H2 1).
  intuition.

  exists (maxList (x :: x0 :: x1 :: nil)).
  intuition.
  unfold ratMult_rel in *.
  edestruct H.
  edestruct H0.
  rewrite H8; eauto.
  eapply leRat_trans.
  eapply (ratTriangleInequality _ _ (c1 * x3)).

  rewrite ratMult_ratDistance_factor_r.
  rewrite ratMult_ratDistance_factor_l.
  rewrite ratMult_comm.
  eapply leRat_trans.
  eapply ratAdd_leRat_compat.
  eapply ratMult_leRat_compat.
  eapply ratDistance_le_sum.
  eapply H6; [idtac | eapply H10].
  eapply le_trans.
  eapply (maxList_correct (x :: x0 :: x1 :: nil)).
  simpl.
  intuition.
  trivial.
  eapply H4; [idtac | eapply H9].
  eapply le_trans.
  eapply (maxList_correct (x :: x0 :: x1 :: nil)).
  simpl.
  intuition.
  trivial.
  eapply ratMult_leRat_compat.
  eapply (ratAdd_any_leRat_l 1).
  eapply leRat_refl.
  eapply H5; [idtac | eapply H10].
  eapply le_trans.
  eapply (maxList_correct (x :: x0 :: x1 :: nil)).
  simpl.
  intuition.
  trivial.
  eapply eqRat_impl_leRat.
  repeat rewrite <- ratMult_assoc.
  rewrite (ratAdd_comm c2).
  rewrite (ratAdd_comm c1).
  rewrite (ratMult_assoc ((1 + c2) * (ratInverse (1 + c2)))).
  rewrite (ratMult_assoc ((1 + c1) * (ratInverse (1 + c1)))).
  rewrite <- ratMult_distrib_r.
  rewrite (ratMult_comm (1 + c2)).
  rewrite (ratMult_comm (1 + c1)).
  repeat rewrite ratInverse_prod_1.
  rewrite ratMult_2.
  rewrite ratMult_1_l.
  rewrite ratMult_comm.
  rewrite ratMult_assoc.

  rewrite ratMult_eq_rat1.
  eapply ratMult_1_r.

  intuition.
  assert (1 <= 0).
  eapply leRat_trans.
  eapply (ratAdd_any_leRat_r c1).
  eapply leRat_refl.
  eapply eqRat_impl_leRat.
  rewrite ratAdd_comm.
  trivial.
  intuition.

  intuition.
  assert (1 <= 0).
  eapply leRat_trans.
  eapply (ratAdd_any_leRat_r c2).
  eapply leRat_refl.
  eapply eqRat_impl_leRat.
  rewrite ratAdd_comm.
  trivial.
  intuition.

Qed.

Definition rat_limit(f : Rat -> Rat -> Prop)(p L : Rat) :=
  forall epsilon, 
    ~ (epsilon == 0) ->
    exists delta, (~delta == 0) /\
      forall x v,
        f x v ->
        (ratDistance x p) <= delta ->
        (ratDistance v L) <= epsilon.

Definition continuous_at(f : Rat -> Rat -> Prop)(c : Rat) :=
  forall v, f c v ->
    rat_limit f c v.

Lemma rat_inf_limit_comp : forall (f : nat -> Rat -> Prop)(g : Rat -> Rat -> Prop) a v,
  rat_inf_limit f a ->
  g a v ->
  continuous_at g a ->
  left_total f ->
  rat_inf_limit (fun n r => forall v', (f n v' -> g v' r)) v.

  unfold continuous_at, rat_limit, rat_inf_limit, inf_limit in *.
  intuition.
  edestruct H1; eauto.
  intuition.
  destruct (H x).
  trivial.
  exists x0.
  intuition.
  destruct (H2 n').
  eapply H6.
  eauto.
  eapply H4.
  eapply H7.
  trivial.
Qed.

Lemma rat_inf_limit_trans : forall (f1 f2 : nat -> Rat -> Prop) a,
  rat_inf_limit_2 f1 f2 ->
  rat_inf_limit f2 a ->
  left_total f2 ->
  rat_inf_limit f1 a.

  intuition.
  unfold rat_inf_limit_2, inf_limit_2, rat_inf_limit, inf_limit in *.
  intuition.
  edestruct (H (ratHalf epsilon)).
  eapply ratHalf_ne_0.
  intuition.  
  edestruct (H0 (ratHalf epsilon)).
  eapply ratHalf_ne_0.
  intuition.  
  exists (Max.max x x0).
  intuition.
  destruct (H1 n').
  eapply leRat_trans.
  eapply ratTriangleInequality.
  rewrite H3.
  rewrite H4.
  rewrite ratHalf_add.
  intuition.
  eapply Max.max_lub_r.
  eauto.
  eauto.
  eapply Max.max_lub_l.
  eauto.
  trivial.
  trivial.
Qed.

Lemma rat_inf_limit_eq : forall f a1 a2,
  rat_inf_limit f a1 ->
  a1 == a2 ->
  rat_inf_limit f a2.

  unfold rat_inf_limit, inf_limit in *.
  intuition.
  edestruct H; eauto.
  exists x.
  intuition.
  rewrite <- H0.
  eapply H2.
  eapply H3.
  trivial.
Qed.

Lemma rat_inf_limit_const : forall (f : Rat -> Prop) a,
  f a ->
  (forall a1 a2, f a1 -> f a2 -> a1 == a2) ->
  rat_inf_limit (fun _ => f) a.

  unfold rat_inf_limit, inf_limit in *.
  intuition.
  exists O.
  intuition.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  rewrite <- ratIdentityIndiscernables.
  eauto.
  eapply rat0_le_all.

Qed.


Lemma rat_inf_limit_summation : forall (A : Set)(f1 : A -> nat -> Rat -> Prop)(f2 : A -> Rat)(ls : list A),
  (forall a, rat_inf_limit (f1 a) (f2 a)) ->
  (forall a, left_total (f1 a)) ->
  (forall a n r1 r2, f1 a n r1 -> f1 a n r2 -> r1 == r2) ->
  rat_inf_limit
  (fun n : nat => sumList_rel (fun a0 : A => f1 a0 n) ls)
  (sumList ls f2).

  induction ls; intuition.
  unfold rat_inf_limit, inf_limit.
  intuition.
  exists O.
  intuition.
  inversion H4; clear H4; subst.
  unfold sumList.
  simpl.
  rewrite H5.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  rewrite <- ratIdentityIndiscernables.
  intuition.
  eapply rat0_le_all.

  eapply (@rat_inf_limit_trans _ (fun n : nat => ratAdd_rel (f1 a n) (sumList_rel (fun a0 : A => f1 a0 n) ls))).
  unfold rat_inf_limit_2, inf_limit_2.
  intuition.
  exists O.
  intuition.
  inversion H5; clear H5; subst.
  unfold ratAdd_rel in *.
  rewrite H6.
  rewrite H12.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  rewrite <- ratIdentityIndiscernables.
  eapply eqRat_refl.
  eapply rat0_le_all.
  trivial.
  trivial.
  eapply rat_inf_limit_eq.
  eapply rat_inf_limit_sum.
  eauto.
  unfold left_total; intuition.
  eapply sumList_rel_left_total.
  intuition.
  eapply H0.
  eapply H.
  eauto.
  unfold sumList.
  simpl.
  symmetry.
  rewrite fold_add_body_eq; [idtac | eapply ratAdd_comm | idtac].
  rewrite fold_add_init.
  eapply eqRat_refl.
  intuition.

  unfold left_total; intuition.
  eapply ratAdd_rel_left_total.
  eapply H0.
  eapply sumList_rel_left_total.
  intuition.
  eapply H0.
  eauto.
  intuition.
  eapply sumList_rel_func; eauto.
  intuition.
  eauto.
Qed.
  
Lemma ratInverse_continuous : forall c,
  ~ c == 0 ->
  continuous_at (fun v' r : Rat => r == ratInverse v') c.
  
  unfold continuous_at, rat_limit in *.
  intuition.

  exists (minRat (c * (1 / 2)) (c * (1/2) * c * epsilon)).
  intuition.
  unfold minRat in *.
  destruct (bleRat (c * (1 / 2)) (c * (1 / 2) * c * epsilon)).
  apply ratMult_0 in H2; intuition.
  apply ratMult_0 in H2; intuition.
  apply ratMult_0 in H3; intuition.
  apply ratMult_0 in H2; intuition.

  rewrite H2.
  rewrite H0.
  
  assert (ratDistance x c <= c * (1/2)).
  eapply leRat_trans.
  eapply H3.
  eapply minRat_le_l.

  assert (ratSubtract c (c * (1/2)) <= x).
  eapply ratDistance_ge_difference.
  rewrite ratDistance_comm.
  trivial.
  assert (x <= c + (c * (1/2))).
  eapply ratDistance_le_sum.
  trivial.
  assert (c * (1/2) <= x).

  rewrite <- (ratSubtract_half).
  trivial.

  clear H5.
  assert (x <= c * (3/2)).

  rewrite ratMult_ratAdd_cd in H6.
  simpl in *.
  trivial.

  clear H6.
  assert (ratInverse x <= ratInverse (c * (1 / 2))).
  apply ratInverse_leRat.
  intuition.
  apply ratMult_0 in H6; intuition.
  trivial.

  rewrite ratDistance_ratInverse.
  rewrite H3.
  rewrite minRat_le_r.

  rewrite ratInverse_ratMult; intuition.
  rewrite H6.
  rewrite ratInverse_ratMult; intuition.
  rewrite ratMult_comm.
  repeat rewrite <- ratMult_assoc.
  rewrite (ratMult_assoc ((ratInverse c) * (ratInverse (1/2)))).
  rewrite ratInverse_prod_1; intuition.
  rewrite ratMult_1_r.
  rewrite (ratMult_assoc (ratInverse c)).
  rewrite ratInverse_prod_1; intuition.
  rewrite ratMult_1_r.
  rewrite ratInverse_prod_1; intuition.
  rewrite ratMult_1_l.
  intuition.
  rewrite H8 in H7.
  assert (c * (1 / 2) == 0).
  eapply leRat_impl_eqRat.
  trivial.
  eapply rat0_le_all.
  apply ratMult_0 in H9; intuition.
  intuition.
  rewrite H8 in H7.
  assert (c * (1 / 2) == 0).
  eapply leRat_impl_eqRat.
  trivial.
  eapply rat0_le_all.
  apply ratMult_0 in H9; intuition.
  intuition.
Qed.

Lemma rat_inf_limit_ratInverse : forall (f : nat -> Rat -> Prop) a v,
  rat_inf_limit f a ->
  ~ a == 0 ->
  ratInverse a == v ->
  left_total f ->
  rat_inf_limit (fun n => ratInverse_rel (f n)) v.
  
  intuition.
  eapply rat_inf_limit_comp.
  eauto.
  symmetry.
  trivial.
  eapply ratInverse_continuous.
  trivial.
  trivial.
  
Qed.

Lemma rat_inf_limit_exp_0 : forall (f : nat -> Rat -> Prop) a,
  rat_inf_limit f a ->
  ~ 1 <= a ->
  (forall n, exists r, f n r) ->
  rat_inf_limit (fun n => (expRat_rel (f n) n)) 0.

  intuition.
  unfold rat_inf_limit, inf_limit in *.
  intuition.
  edestruct (H (1 / 2 * (ratSubtract 1 a))); eauto.
  intuition.
  apply ratMult_0 in H3.
  intuition.
  eapply H0.  
  eapply ratSubtract_0_inv.
  trivial.

  edestruct (@expRat_le_exp_exists (a + (1 / 2) * (ratSubtract 1 a)) epsilon).
  eapply half_distance_1_le; trivial.
  trivial.

  exists (Max.max x x0).
  intuition.
  unfold expRat_rel in *.
  destruct (H1 n').
  rewrite H6; eauto.

  apply ratDistance_0_r_le.
  eapply leRat_trans.
  eapply expRat_leRat_compat.
  eapply ratDistance_le_sum.
  eapply H3.
  eapply Max.max_lub_l.
  eauto.
  trivial.
  
  eapply expRat_le'.
  eauto.
  eapply half_distance_1_le; trivial.
  eapply Max.max_lub_r.
  eauto.
 
Qed.

Lemma power_series_limit_2 : forall (f : nat -> Rat -> Prop) a,
  rat_inf_limit f a ->
  (forall n v, f n v -> ~ 1 <= v) ->
  ~ 1 <= a ->
  (forall n, exists v, f n v) ->
  (forall n v1 v2, f n v1 -> f n v2 -> v1 == v2) ->
  rat_inf_limit 
  (fun n => sumList_rel 
    (fun i => expRat_rel (f n) i)
    (getNats O n))
  (ratInverse (ratSubtract 1 a)).

  intuition.
  
  eapply (@rat_inf_limit_trans _ (fun n => (ratMult_rel (ratSubtract_rel (eqRat 1) (expRat_rel (f n) n)) (ratInverse_rel (ratSubtract_rel (eqRat 1) (f n)))))).
  unfold rat_inf_limit_2, inf_limit_2.
  intuition.
  exists (S O).
  intuition.
  destruct (H2 n'). 
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  rewrite <- ratIdentityIndiscernables.
  eapply sum_power_series.
  assert (n' > O).
  omega.
  eapply H9.
  econstructor.
  eapply H8.
  eapply H3.
  intuition.
  eapply H0.
  eapply H9.
  trivial.
  trivial.
  trivial.
  eapply rat0_le_all.

  eapply rat_inf_limit_eq.
  eapply rat_inf_limit_product.
    
  unfold left_total, ratSubtract_rel, expRat_rel. intuition.
  destruct (H2 n).
  exists (ratSubtract 1 (expRat x n)).
  intuition.
  eapply ratSubtract_eqRat_compat; eauto.
  symmetry.
  eapply H6.
  trivial.

  unfold left_total, ratInverse_rel, ratSubtract_rel. intuition.
  destruct (H2 n).
  exists (ratInverse (ratSubtract 1 x)).
  intuition.
  eapply ratInverse_eqRat_compat.
  intuition.
  eapply H0.
  eauto.
  eapply ratSubtract_0_inv.
  trivial.

  symmetry.
  eapply H5; intuition.
  
  eapply rat_inf_limit_difference.

  unfold left_total; intuition.
  exists 1; intuition.
  
  unfold left_total, expRat_rel; intuition.
  destruct (H2 n).
  exists (expRat x n).
  intuition.

  eapply expRat_eqRat_compat; eauto.

  eapply rat_inf_limit_const.
  eapply eqRat_refl.
  intuition.
  rewrite <- H4.
  rewrite H5.
  intuition.

  eapply rat_inf_limit_exp_0.
  eauto.
  trivial.
  trivial.

  eapply rat_inf_limit_ratInverse.
  eapply rat_inf_limit_difference.
  unfold left_total; intuition.
  econstructor.
  eapply eqRat_refl.
  unfold left_total; intuition.
  
  eapply rat_inf_limit_const.
  eapply eqRat_refl.
  intuition.
  rewrite <- H4.
  rewrite H5.
  intuition.
  eauto.
  intuition.
  eapply H1.
  eapply ratSubtract_0_inv.
  trivial.
  
  eapply eqRat_refl.
  unfold left_total; intuition.
  destruct (H2 n).
  exists (ratSubtract 1 x).
  unfold ratSubtract_rel; intuition.
  eapply ratSubtract_eqRat_compat; eauto.
  rewrite ratSubtract_0_r.
  rewrite ratMult_1_l.
  intuition.

  unfold left_total, ratMult_rel, ratSubtract_rel, expRat_rel, ratInverse_rel.
  intuition.
  destruct (H2 n).
  exists ((ratSubtract 1 (expRat x n)) * (ratInverse (ratSubtract 1 x))).
  intuition.
  eapply ratMult_eqRat_compat.
  symmetry.
  eapply H5;
  intuition.
  eapply expRat_eqRat_compat.
  eauto.
  symmetry.
  eapply H6.
  intuition.
  eapply ratSubtract_eqRat_compat; intuition.
  eauto.
Qed.

Lemma rat_inf_limit_mono  : forall (f : nat -> Rat -> Prop) (g : nat -> nat)(v : Rat),
    rat_inf_limit f v -> 
    (forall n1 n2, n1 <= n2 -> g n1 <= g n2)%nat ->
    (forall y, exists x, g x = y) ->
    rat_inf_limit (fun n => f (g n)) v.

  unfold rat_inf_limit, inf_limit.
  intuition.
  destruct (H epsilon); intuition.
  destruct (H1 x).
  econstructor.
  intuition.
  eapply (H3 (g n')).
  eapply le_trans.
  2:{
    eapply H0.
    eapply H5.
  }
  rewrite <- H4.
  eapply le_refl.
  trivial.
Qed.


Lemma rat_inf_limit_sqrt:
  forall (f : nat -> Rat -> Prop) (v : Rat),
    rat_inf_limit f v -> 
    rat_inf_limit (fun n => f (Nat.sqrt n)) v.

  intuition.
  eapply rat_inf_limit_mono.
  trivial.
  intuition.
  eapply Nat.sqrt_le_mono.
  trivial.
  intuition.
  econstructor.
  eapply Nat.sqrt_square.
Qed.