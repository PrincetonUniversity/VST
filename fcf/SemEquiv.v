(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
 (* Equivalance between the oracle machine semantics and the probabilistic semantics. *)

Set Implicit Arguments.

Require Import fcf.Comp.
Require Import fcf.DetSem.
Require Import fcf.DistSem.
Require Import fcf.Rat.
Require Import Arith.
Require Import fcf.StdNat.
Require Import fcf.Fold.
Require Import fcf.Limit.
Require Import Permutation.

Local Open Scope rat_scope.
Local Open Scope list_scope.

Lemma evalDet_step_done_evalDist : forall (A : Set)(eqd : eq_dec A)(c : Comp A) a a' s,
  evalDet_step c nil = (cs_done a s) ->
  evalDist c a' == if (eqd a a') then 1 else 0.
  
  induction c; intuition; simpl in *.
  inversion H; clear H; subst.
  destruct (e a0 a'); subst.
  destruct (eqd a' a').
  intuition.
  congruence.
  destruct (eqd a0 a'); subst.
  congruence.
  intuition.
  
  destruct (evalDet_step c nil); discriminate.
  
  destruct n; discriminate.
  
  congruence.
  
Qed.

Lemma evalDet_step_nil_dist_preserved : forall (A : Set)(c : Comp A),
  well_formed_comp c ->
  forall c' a, 
    evalDet_step c nil = cs_more c' nil ->
    evalDist c a == evalDist c' a.
  
  induction 1; intuition; simpl in *.
  discriminate.
  case_eq (evalDet_step c1 nil); intuition;
    rewrite H3 in H2; try discriminate.
  inversion H2; clear H2; subst.
  erewrite evalDet_step_done_support_singleton; eauto.
  unfold sumList. simpl.
  rewrite <- ratAdd_0_l.
  rewrite (@evalDet_step_done_evalDist _ (comp_eq_dec c1)); eauto.
  destruct (comp_eq_dec c1 b b).
  eapply ratMult_1_l.
  congruence.
  
  inversion H2; clear H2; subst.
  simpl.
  rewrite sumList_permutation.
  2:{
    eapply evalDet_step_more_support_preserved.
    eauto.
  }
  eapply sumList_body_eq.
  intuition.
  eapply ratMult_eqRat_compat; intuition.
  
  destruct n.
  inversion H; clear H; subst.
  simpl.
  
  rewrite (vector_0 a).
  destruct (Bvector_eq_dec [] [] ).
  eapply eqRat_terms; intuition.
  congruence.
  
  discriminate.
  
  inversion H1; clear H1; subst.
  simpl.
  
  destruct (in_dec (comp_eq_dec c) a (getSupport c)).
  
  symmetry.
  eapply eqRat_trans.
  eapply (sumList_filter_partition P).
  eapply eqRat_trans.
  eapply ratAdd_eqRat_compat.
  eapply sumList_body_eq.
  intuition.
  assert (P a0 = true).
  eapply filter_In; eauto.
  rewrite H2.
  simpl.
  eapply eqRat_refl.
  eapply sumList_body_eq.
  intuition.
  assert (P a0 = false).
  assert (negb (P a0) = true).
  apply filter_In in H1.
  intuition.
  eapply negb_true_iff.
  trivial.
  rewrite H2.
  simpl.
  eapply eqRat_refl.
  
  case_eq (P a); intuition.
  unfold indicator.
  rewrite H1.
  rewrite ratMult_1_l.
  assert (sumList (filter P (getSupport c))
    (fun a0 : A => evalDist c a0 * (if comp_eq_dec c a0 a then 1 else 0)) == evalDist c a).
  
  rewrite (@sumList_exactly_one _ a).
  destruct (comp_eq_dec c a a); try congruence.
  eapply ratMult_1_r.
  eapply filter_NoDup.
  eapply getSupport_NoDup.
  eapply filter_In; eauto.
  intuition.
  destruct (comp_eq_dec c b0 a); subst; intuition.
  eapply ratMult_0_r.
  rewrite H2.
  rewrite sumList_factor_constant_r.
  rewrite ratMult_1_l.
  assert (sumList (filter (fun a0 : A => negb (P a0)) (getSupport c)) (evalDist c) == (ratSubtract 1 (sumList (filter P (getSupport c)) (evalDist c)))).
  rewrite <- evalDist_lossless.
  rewrite (sumList_filter_partition P (getSupport c)).
  rewrite ratSubtract_ratAdd_inverse.
  intuition.
  trivial.

  rewrite H3.
  rewrite ratMult_ratSubtract_distrib_r.
  rewrite ratMult_1_l.
  rewrite <- (ratMult_assoc (sumList (filter P (getSupport c)) (evalDist c))).
  rewrite (ratMult_comm (sumList (filter P (getSupport c)) (evalDist c))).
  rewrite ratInverse_prod_1.
  rewrite ratMult_1_l.
  rewrite ratSubtract_ratAdd_inverse_2.
  intuition.
  eapply leRat_trans.
  rewrite <- ratMult_1_l.
  eapply leRat_refl.
  eapply ratMult_leRat_compat; intuition.

  eapply ratInverse_1_swap.
  
  intuition.
  eapply sumList_0 in H4.
  eapply getSupport_In_evalDist.
  eapply filter_In.
  eapply H0.
  eapply H4.
  trivial.
  
  eapply leRat_trans.
  eapply sumList_filter_le.
  rewrite evalDist_lossless.
  intuition.
  trivial.
  
  intuition.
  eapply sumList_0 in H4.
  eapply getSupport_In_evalDist.
  eapply filter_In.
  eapply H0.
  eapply H4.
  trivial.

  unfold indicator.
  rewrite H1.
  rewrite ratMult_0_l.
  assert (sumList (filter P (getSupport c))
    (fun a0 : A => evalDist c a0 * (if comp_eq_dec c a0 a then 1 else 0)) == 0).
  eapply sumList_0.
  intuition.
  destruct (comp_eq_dec c a0 a); subst.
  assert (P a = true).
  eapply filter_In; eauto.
  congruence.
  eapply ratMult_0_r.
  rewrite H2.
  assert (sumList (filter (fun a0 : A => negb (P a0)) (getSupport c))
    (fun a0 : A =>
      evalDist c a0 *
      (0 * ratInverse (sumList (filter P (getSupport c)) (evalDist c)) *
        evalDist c a)) == 0).
  eapply sumList_0.
  intuition.
  repeat rewrite ratMult_0_l.
  eapply ratMult_0_r.
  rewrite H3.
  rewrite <- ratAdd_0_l.
  symmetry.
  eapply ratMult_0_l.
  
  assert (evalDist c a == 0).
  eapply getSupport_not_In_evalDist.
  trivial.
  rewrite H1.
  rewrite ratMult_0_r.
  symmetry.
  eapply sumList_0.
  intuition.
  case_eq (P a0); intuition.
  simpl.
  destruct (comp_eq_dec c a0 a); subst.
  intuition.
  eapply ratMult_0_r.
  simpl.
  rewrite H1.
  repeat rewrite ratMult_0_r.
  intuition.
Qed.

Lemma evalDet_steps_done_evalDist_h : forall (A : Set)(x y : comp_state A),
  evalDet_steps x y ->
  forall (eqd : eq_dec A)(c : Comp A) a a' s,
    x = (cs_more c nil) -> 
    y = (cs_done a s) -> 
    well_formed_comp c ->
    evalDist c a' == if (eqd a a') then 1 else 0.
  
  induction 1; intuition; subst.
  discriminate.
  
  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  
  eapply evalDet_step_done_evalDist; eauto.
  
  assert (s = nil).
  eapply evalDet_step_more_nil_inv.
  eauto.
  subst.
  rewrite <- IHevalDet_steps; eauto.
  erewrite evalDet_step_nil_dist_preserved; eauto.
  intuition.
  
  eapply evalDet_step_well_formed_comp_preserved;
    eauto.
  
Qed.
  

Lemma evalDet_steps_done_evalDist : forall (A : Set)(eqd : eq_dec A)(c : Comp A) a a' s,
  well_formed_comp c ->
  evalDet_steps (cs_more c nil) (cs_done a s) ->
  evalDist c a' == if (eqd a a') then 1 else 0.
  
  intuition.
  eapply evalDet_steps_done_evalDist_h; eauto.
Qed.

Definition lowDistApprox (A : Set)(c : Comp A)(a : A)(n : nat)(v : Rat) :=
  exists vals count,
    rel_map (evalDet c) (getAllBlists n) vals /\
    pred_count (eq (ca_done a)) vals count  /\
    v == (count / expnat 2 n).

Lemma map_Ret_repeat : forall (A : Set)(eqd : eq_dec A)(a : A) ls ls',
  rel_map (evalDet (Ret eqd a)) ls ls' ->
  ls' = listRepeat (ca_done a) (length ls).
  
  induction ls; inversion 1; intuition; subst; simpl in *.
  f_equal.
  inversion H4; clear H4; subst.
  inversion H0; clear H0; subst.
  simpl in *.
  inversion H6; clear H6; subst.
  trivial.
  
  inversion H0; clear H0; subst; simpl in *.
  inversion H6.
  
  inversion H; clear H; subst.
  eapply IHls.
  trivial.
Qed.

Theorem lowDistApprox_Ret_inv : forall (A : Set)(eqd : eq_dec A)(a a' : A) n v,
  lowDistApprox (Ret eqd a) a' n v ->
  v == (if (eqd a a') then 1 else 0).

  intuition.
  destruct H.
  destruct H.
  intuition. 

  specialize (map_Ret_repeat H0); intuition.
  subst.

  destruct (eqd a a'); subst.

  specialize (pred_count_listRepeat_eq_inv _ H); intuition.
  subst.
  rewrite H2.
  rewrite getAllBlists_length.
  eapply num_dem_same_rat1.
  trivial.

  specialize (@pred_count_listRepeat_ne_inv (length (getAllBlists n)) _ (ca_done a') (ca_done a) x0); intuition.
  rewrite H1 in H2.
  rewrite H2.
  apply rat_num_0.
  intuition.
  inversion H3.
  intuition.
  trivial.

Qed. 

Inductive lowDistApprox_bind (A B : Set)(c1 : Comp B)(c2 : B -> Comp A)(a : A)(n : nat) : Rat -> Prop :=
| lda_b_intro : 
  forall v,
    sumList_rel (fun (b : B) r => forall r1 r2, lowDistApprox c1 b n r1 -> lowDistApprox (c2 b) a n r2 -> r == r1 * r2) (getSupport c1) v ->
    lowDistApprox_bind c1 c2  a n v.


(* We will use a tree to represent an approximation at a certain level.  These tree-based approximations are equivalent to the standard approximations above, but they make it easier to prove some properties. *)
Inductive DistApproxTree(A : Set) :=
| dat_leaf : option A -> DistApproxTree A
| dat_internal : DistApproxTree A -> DistApproxTree A -> DistApproxTree A.

(* dat_correct is an inductive predicate that lets us conclude that some tree produces a correct approximation for some computation. *)
Inductive dat_correct_h(A : Set)(c : Comp A)(s : Blist) : nat -> DistApproxTree A -> Prop :=
    | dat_correct_h_leaf_Some :
      forall a n, 
        evalDet c s (ca_done a) ->
        dat_correct_h c s n (dat_leaf (Some a))
    | dat_correct_h_leaf_None :
        (forall a, ~ evalDet c s (ca_done a)) ->
        dat_correct_h c s 0 (dat_leaf None)
    | dat_correct_h_internal :
      forall t1 t2 n, 
        (forall a, ~ evalDet c s (ca_done a)) ->
        dat_correct_h c (s ++ (true :: nil)) n t1 ->
        dat_correct_h c (s ++ (false :: nil)) n t2 ->
        dat_correct_h c s (S n) (dat_internal t1 t2).

Definition dat_correct(A : Set)(c : Comp A)(n : nat) :=
    dat_correct_h c nil n.

Lemma dat_correct_func : forall (A : Set)(c : Comp A) ls n t1,
  dat_correct_h c ls n t1 ->
  forall t2, 
    dat_correct_h c ls n t2 ->
    t1 = t2.
  
  induction 1; intuition.
  inversion H0; clear H0; subst.
  assert (ca_done a = ca_done a0).
  eapply evalDet_func; eauto.
  inversion H0.
  subst.
  trivial.
  specialize (H1 a).
  intuition.
  specialize (H1 a).
  intuition.
  
  inversion H0; clear H0; subst.
  specialize (H a).
  intuition.
  trivial.
  
  inversion H2; clear H2; subst.
  specialize (H a).
  intuition.
  f_equal; eauto.
Qed.

Fixpoint getTreeSupport_dups(A : Set)(t : DistApproxTree A) :=
  match t with
    | dat_leaf o =>
      match o with
        | None => nil
        | Some a => a :: nil
      end
    | dat_internal t1 t2 =>
      getTreeSupport_dups t1 ++ getTreeSupport_dups t2
  end.

Definition getTreeSupport(A : Set)(eqd : eq_dec A)(t : DistApproxTree A) : list A :=
  getUnique (getTreeSupport_dups t) eqd.

Lemma getTreeSupport_in : forall (A : Set)(eqd : eq_dec A)(c : Comp A)(t : DistApproxTree A) n,
  dat_correct c n t ->
  forall a,
    In a (getTreeSupport eqd t) ->
    In a (getSupport c).
  
  induction 1; intuition; simpl in *.
  intuition; subst.
  eapply getSupport_In_evalDet; eauto.
  intuition.
  
  unfold getTreeSupport in *.
  eapply in_getUnique_if in H2.
  simpl in *.
  eapply in_app_or in H2.
  intuition.
  
  eapply IHdat_correct_h1.
  eapply in_getUnique.
  eauto.
  
  eauto using in_getUnique.
Qed.

Lemma getTreeSupport_not_in : forall (A : Set)(eqd : eq_dec A)(c : Comp A)(t : DistApproxTree A) n a,
  dat_correct c n t ->
  ~In a (getSupport c) ->
  ~In a (getTreeSupport eqd t).
  
  intuition.
  eapply H0.
  eauto using getTreeSupport_in.
Qed.

Lemma dat_exists_h : forall n s (A : Set)(c : Comp A),
  well_formed_comp c ->
  exists t : DistApproxTree A,
    dat_correct_h c s n t.
  
  induction n; intuition.

  destruct (@evalDet_dec _ c s).
  trivial.
  destruct H0.
  exists (dat_leaf (Some x)).
  econstructor; eauto.
  exists (dat_leaf None).
  econstructor.
  intuition.

  eapply evalDet_done_eof_func; eauto.
  
  destruct (@evalDet_dec _ c s).
  trivial.
  destruct H0.
  exists (dat_leaf (Some x)).
  econstructor.
  trivial.
  
  destruct (IHn (s ++ (true :: nil)) _ c).
  trivial.
  destruct (IHn (s ++ (false :: nil)) _ c).
  trivial.
  exists (dat_internal x x0).
  econstructor; eauto.
  intuition.
  eapply evalDet_done_eof_func; eauto.
  
Qed.

Theorem dat_exists : forall n (A : Set)(c : Comp A),
  well_formed_comp c ->
  exists t : DistApproxTree A,
    dat_correct c n t.
  
  intuition.
  eapply dat_exists_h.
  trivial.
Qed.

Fixpoint lowDistApproxFromTree(A : Set)(eqd : eq_dec A)(t : DistApproxTree A)(a : A) :=
  match t with
    | dat_leaf o =>
      match o with
        | None => 0
        | Some a' => if (eqd a a') then 1 else 0
      end
    | dat_internal t1 t2 =>
      (lowDistApproxFromTree eqd t1 a) * (1 / 2) + (lowDistApproxFromTree eqd t2 a) * (1 / 2)
  end.

Definition lowDistApprox_ls (A : Set)(c : Comp A) a n (ls : Blist) r :=
  exists vals count,
    rel_map (fun s v => (evalDet c (ls ++ s) v)) (getAllBlists n) vals /\
    pred_count (eq (ca_done a)) vals count /\
    count /expnat 2 n == r.

Lemma lowDistApprox_ls_impl : forall n (A : Set)(c : Comp A) a r,
  lowDistApprox c a n r ->
  lowDistApprox_ls c a n nil r.
  
  intuition.
  destruct H.
  destruct H.
  intuition.
  econstructor.
  econstructor. 
  intuition.
  simpl.
  eapply rel_map_eq.
  eapply H0.
  eauto.
  intuition.
  eauto.
  intuition.
Qed.

Lemma evalDet_lowDistApprox_ls_done_inv : forall (A : Set)(eqd : eq_dec A)(c : Comp A) s a1 a2 n r,
  evalDet c s (ca_done a1) ->
  lowDistApprox_ls c a2 n s r ->
  r == if (eqd a2 a1) then 1 else 0.
  
  intuition.
  destruct H0.
  destruct H0.
  intuition.
  
  destruct (eqd a2 a1); subst.
  rewrite <- H3.
  erewrite pred_count_eq_all_inv at 1.
  erewrite <- rel_map_length.
  rewrite getAllBlists_length.
  apply num_dem_same_rat1.
  unfold posnatToNat.
  unfold natToPosnat.
  eauto.
  eapply H1.
  eauto.
  
  intuition.
  
  eapply rel_map_unary_pred.
  eapply H1.
  intuition.
  
  eapply evalDet_app_eq in H.
  eapply evalDet_func; eauto.
  trivial.
  
  rewrite <- H3.
  erewrite pred_count_eq_0 at 1.
  apply rat_num_0.
  2:{
    eapply H1.
  }
  2:{
    eapply H0.
  }
  intuition.
  subst.
  eapply n0.
  assert (ca_done a1 = ca_done a2).
  eapply evalDet_func.
  eapply evalDet_app_eq.
  eauto.
  eauto.
  inversion H5.
  trivial.
  
Qed.
 
Lemma low_tree_approx_same_inv_h : forall n (A : Set)(eqd : eq_dec A)(c : Comp A) ls t,
  dat_correct_h c ls n t -> 
  forall a r, 
    lowDistApprox_ls c a n ls r ->
    lowDistApproxFromTree eqd t a == r.
  
  induction 1; intuition; simpl in *.
  
  symmetry.
  eapply evalDet_lowDistApprox_ls_done_inv; eauto.
  
  inversion H0; clear H0; subst.
  destruct H1; intuition.
  simpl in *.
  
  rewrite <- H3.
  erewrite pred_count_eq_0 at 1.
  apply eqRat_symm.
  apply rat_num_0.
  2:{
    eapply H1.
  }
  2:{
    eapply H0.
  }
  intuition.
  simpl in *.
  intuition.
  subst.
  rewrite app_nil_r in *.
  eapply H; eauto.
  
  destruct H2.
  destruct H2.
  intuition.
  simpl in *.
  
  apply rel_map_app_inv in H3.
  intuition.
  
  apply rel_map_map_inv in H4.
  apply rel_map_map_inv in H6.
  
  eapply (pred_count_first_skip) in H2.
  destruct H2.
  destruct H2.
  intuition.
  
  rewrite IHdat_correct_h1.
  2:{
    econstructor.
    econstructor.
    intuition.
    eapply rel_map_eq.
    eapply H4.
    trivial.
    intuition.
    rewrite <- app_assoc.
    simpl.
    trivial.
    eapply H3.
    eapply eqRat_refl.
  }
  
  rewrite IHdat_correct_h2.
  2:{
    econstructor.
    econstructor.
    intuition.
    eapply rel_map_eq.
    eapply H6.
    trivial.
    intuition.
    rewrite <- app_assoc.
    simpl.
    trivial.
    eapply H2.
    eapply eqRat_refl.
  }
  rewrite <- ratMult_distrib_r.
  rewrite <- ratAdd_den_same.
  rewrite H8.
  rewrite <- ratMult_num_den.
  rewrite mult_1_r.
  unfold posnatMult.
  unfold natToPosnat.
  rewrite <- H5.
  eapply eqRat_terms; trivial.
  unfold natToPosnat, posnatToNat.
  rewrite mult_comm.
  simpl.
  trivial.
Qed.    

(* The approximation from the tree is the same as the standard approximation. *)
Theorem low_tree_approx_same_inv : forall n (A : Set)(eqd : eq_dec A)(c : Comp A)(t : DistApproxTree A) (a : A) r,
    dat_correct c n t -> 
    lowDistApprox c a n r ->
    lowDistApproxFromTree eqd t a == r.   

  
  intuition.
  eapply low_tree_approx_same_inv_h.
  eauto.
  
  
  eapply lowDistApprox_ls_impl.
  trivial.
  
Qed.

Theorem getSupport_not_In_lowDistApprox : forall n (A : Set)(c : Comp A)(a : A) r,
  ~In a (getSupport c) ->
  lowDistApprox c a n r ->
  r == 0.
  
  intuition.
  destruct H0.
  destruct H0.
  intuition.
  
  
  specialize (@pred_count_eq_0 (comp_answer A) Blist (getAllBlists n) x (evalDet c) (eq (ca_done a)) x0); intuition.
  rewrite H2 in H3.
  rewrite H3.
  apply rat_num_0.
  intuition.
  subst.
  
  
  eapply H.
  eapply getSupport_In_evalDet; eauto.
  trivial.
  trivial.
  
Qed.

Definition getSupport_bind (A B : Set)(c1 : Comp B)(c2 : B -> Comp A) : list (B * (list A)) :=
  (map (fun b => (b , (getSupport (c2 b)))) (getSupport c1)).

Fixpoint flattenPair (A B : Type)(ls : list (A * list B)) :=
  match ls with
    | nil => nil
    | (a, ls_b) :: ls' =>
      (map (fun b => (a, b)) ls_b) ++ (flattenPair ls')
  end.

Theorem in_flattenPair : forall (A B : Type)(ls : list (A * (list B))) a b entryList,
  In (a, entryList) ls ->
  In b entryList ->
  In (a, b) (flattenPair ls).
  
  induction ls; intuition; simpl in *.
  
  intuition.
  inversion H1; clear H1; subst.
  eapply in_or_app.
  left.
  eapply in_map_iff.
  econstructor.
  intuition.
  
  eapply in_or_app.
  right.
  eapply IHls; eauto.
Qed.

Definition getSupport_bind_cp (A B : Set)(c1 : Comp B)(c2 : B -> Comp A) : list (B * A) :=
  flattenPair (getSupport_bind c1 c2).

Lemma In_getSupport_bind_cp : forall (A B : Set)(c1 : Comp B)(c2 : B -> Comp A) b a,
  In b (getSupport c1) ->
  In a (getSupport (c2 b)) ->
  In (b, a) (getSupport_bind_cp c1 c2).
  
  intuition.
  unfold getSupport_bind_cp, getSupport_bind.
 
  eapply in_flattenPair.
  eapply in_map_iff.
  econstructor; intuition.
  trivial.
  
Qed.

Lemma not_In_getSupport_bind_cp : forall (A B : Set)(eqda : eq_dec A)(eqdb : eq_dec B)(c1 : Comp B)(c2 : B -> Comp A) b a,
  ~ In (b, a) (getSupport_bind_cp c1 c2) ->
  ~ In b (getSupport c1) \/ 
  ~ In a (getSupport (c2 b)).
  
  intuition.
  
  destruct (in_dec eqdb b (getSupport c1)); intuition.
  destruct (in_dec eqda a (getSupport (c2 b))); intuition.
  exfalso.
  eapply H.
  eapply In_getSupport_bind_cp; eauto.
Qed.


Instance length_getSupport_nz : forall (A : Set)(c : Comp A),
  well_formed_comp c ->
  nz (length (getSupport c)).
intuition.
econstructor.
eapply getSupport_length_nz.
trivial.
Qed.

Lemma evalDet_lowDistApprox_ls_done:
  forall (A : Set) (eqd : eq_dec A) (c : Comp A) (s : Blist) 
    (a1 a2 : A) (n : nat),
    evalDet c s (ca_done a1) ->
    lowDistApprox_ls c a2 n s (if eqd a2 a1 then 1 else 0).
  
  unfold lowDistApprox_ls.
  intuition.
  exists (listRepeat (ca_done a1) (length (getAllBlists n))).
  
  destruct (eqd a1 a2); subst.
  exists (length (getAllBlists n)).
  intuition.
  eapply rel_map_listRepeat.
  intuition.
  eapply evalDet_app_eq.
  trivial.
  
  eapply pred_count_eq_all; intuition.
  symmetry.
  eapply in_listRepeat_inv.
  eauto.
  rewrite listRepeat_length.
  trivial.
  destruct (eqd a2 a2); try congruence.
  rewrite getAllBlists_length.
  apply num_dem_same_rat1.
  unfold natToPosnat, posnatToNat.
  trivial.
  
  exists O.
  intuition.
  
  eapply rel_map_listRepeat.
  intuition.
  eapply evalDet_app_eq.
  trivial.
  
  eapply pred_count_eq_none; intuition.
  subst.
  assert (ca_done a2 = ca_done a1).
  eapply in_listRepeat_inv.
  eauto.
  inversion H1; subst; clear H1.
  intuition.
  
  destruct (eqd a2 a1); subst; try congruence.
  apply rat_num_0.
Qed.

Lemma evalDet_lowDistApprox_ls_not_done:
  forall (A : Set) (c : Comp A) (s : Blist) 
    (a2 : A) (n : nat),
    well_formed_comp c ->
    (forall s' (a : A), In s' (getAllBlists n) -> evalDet c (s ++ s') (ca_done a) -> False) ->
    lowDistApprox_ls c a2 n s 0.
  
  intuition.
  unfold lowDistApprox_ls.
  exists (listRepeat (@ca_eof A) (length (getAllBlists n))).
  exists O.
  intuition.
  eapply rel_map_listRepeat; intuition.
  destruct (@evalDet_dec _ c (s ++ a)).
  trivial.
  destruct H2.
  exfalso.
  eapply H0.
  eauto.
  eauto.
  trivial.
  
  eapply pred_count_eq_none; intuition.
  assert (a = (ca_eof A)).
  eapply in_listRepeat_inv.
  eauto.
  subst.
  discriminate.
  eapply rat_num_0.
  
Qed.

Lemma low_tree_approx_same_h : forall n (A : Set)(eqd : eq_dec A)(c : Comp A)(t : DistApproxTree A) ls,
                                 dat_correct_h c ls n t ->
                                 forall a, 
                                   well_formed_comp c ->
                                   lowDistApprox_ls c a n ls (lowDistApproxFromTree eqd t a).
  
  induction 1; intuition; simpl in *.
  
  eapply evalDet_lowDistApprox_ls_done.
  trivial.
  
  eapply evalDet_lowDistApprox_ls_not_done.
  trivial.
  intuition.
  simpl in *.
  intuition.
  subst.
  rewrite app_nil_r in *.
  eauto.
  
  destruct (IHdat_correct_h1 a).
  trivial.
  destruct H3.
  
  destruct (IHdat_correct_h2 a).
  trivial.
  destruct H4.
  
  intuition.
  
  unfold lowDistApprox_ls.
  econstructor. econstructor.
  intuition.
  simpl.
  
  eapply rel_map_app.
  eapply rel_map_map.
  eapply rel_map_eq.
  eapply H5.
  trivial.
  intuition.
  rewrite <- app_assoc in H11.
  simpl in *.
  trivial.
  eapply rel_map_map.
  eapply rel_map_eq.
  eapply H3.
  trivial.
  intuition.
  rewrite <- app_assoc in H11.
  simpl in *.
  trivial.
  
  eapply pred_count_app; eauto.
  simpl.
  rewrite <- H8.
  rewrite <- H9.
  repeat rewrite <- ratMult_num_den.
  rewrite <- ratAdd_den_same.
  eapply eqRat_terms.
  repeat rewrite mult_1_r.
  trivial.
  unfold posnatMult, natToPosnat, posnatToNat.
  rewrite mult_comm.
  simpl.
  trivial.
Qed.

Theorem low_tree_approx_same : forall n (A : Set)(eqd : eq_dec A)(c : Comp A)(t : DistApproxTree A),
  well_formed_comp c ->
  dat_correct c n t -> 
  forall a, 
    lowDistApprox c a n (lowDistApproxFromTree eqd t a).
  
  intuition.
  
  unfold dat_correct in *.
  edestruct low_tree_approx_same_h.
  eauto.
  trivial.
  destruct H1.
  econstructor.
  econstructor.
  intuition.
  simpl in *.
  eauto.
  eauto.
  rewrite H4.
  eapply eqRat_refl.
  
Qed.

Lemma lowDistApprox_left_total : forall (A : Set)(eqd : eq_dec A)(c : Comp A) a,
  well_formed_comp c ->
  left_total (lowDistApprox c a).
  
  unfold left_total.
  intuition.
  
  destruct (@dat_exists n _ c).
  trivial.
  exists (lowDistApproxFromTree eqd x a).
  eapply low_tree_approx_same.
  trivial.
  trivial.
Qed.

Inductive datMap(A B : Set)(f : A -> DistApproxTree B -> Prop) : DistApproxTree A -> DistApproxTree B  -> Prop :=
| datMap_leaf_None :
    datMap f (dat_leaf None) (dat_leaf None)
| datMap_leaf_Some : 
  forall a t,
    f a t ->
    datMap f (dat_leaf (Some a)) t
| datMap_internal : 
  forall t1a t2a t1b t2b,
    datMap f t1a t1b ->
    datMap f t2a t2b ->
    datMap f (dat_internal t1a t2a) (dat_internal t1b t2b).

  (* a variant of datMap that builds a tree of a maximum depth *)
Inductive datMap_depth(A B : Set)(f : nat -> A -> DistApproxTree B -> Prop) : nat -> DistApproxTree A -> DistApproxTree B -> Prop :=
| datMap_depth_leaf_None :
  forall n, 
    datMap_depth f n (dat_leaf None) (dat_leaf None)
| datMap_depth_leaf_Some :
  forall n a t,
    f n a t ->
    datMap_depth f n (dat_leaf (Some a)) t
| datMap_depth_internal :
  forall n t1a t2a t1b t2b,
    datMap_depth f n t1a t1b ->
    datMap_depth f n t2a t2b ->
    datMap_depth f (S n) (dat_internal t1a t2a) (dat_internal t1b t2b).

Definition dat_correct_bind(A B : Set)(c1 : Comp B)(c2 : B -> Comp A)(n : nat)(t : DistApproxTree A) :=
  exists tb, dat_correct c1 n tb /\
    (datMap_depth (fun n' b ta => (dat_correct (c2 b) n' ta)) n tb t).

Definition dat_correct_bind2(A B : Set)(c1 : Comp B)(c2 : B -> Comp A)(n : nat)(t : DistApproxTree A) :=
  exists tb, dat_correct c1 n tb /\
    (datMap (fun b ta => (dat_correct (c2 b) n ta)) tb t).

Lemma lowDistApproxFromTree_eq_0 : forall (A : Set)(eqd : eq_dec A)(t : DistApproxTree A) a,
  ~In a (getTreeSupport eqd t) ->
  lowDistApproxFromTree eqd t a == 0.
  
  induction t; intuition; simpl in *.
  destruct o.
  
  destruct (eqd a a0); subst.
  exfalso.
  eapply H.
  simpl.
  intuition.
  intuition.
  intuition.
  
  rewrite IHt1.
  rewrite IHt2.
  rewrite ratMult_0_l.
  rewrite <- ratAdd_0_r.
  intuition.
  
  intuition.
  eapply H.
  unfold getTreeSupport in *.
  simpl.
  eapply in_getUnique.
  eapply in_or_app.
  right.
  eapply in_getUnique_if.
  eauto.
  
  intuition.
  eapply H.
  unfold getTreeSupport in *.
  simpl.
  eapply in_getUnique.
  eapply in_or_app.
  left.
  eapply in_getUnique_if.
  eauto.
  
Qed.

Lemma lowDistApproxFromTree_datMap_inv : forall (A B : Set)(eqda : eq_dec A)(eqdb : eq_dec B)(tb : DistApproxTree B)(ta : DistApproxTree A)(mapRel : B -> DistApproxTree A -> Prop),
  datMap mapRel tb ta ->
  (forall b, In b (getTreeSupport eqdb tb) -> exists t,  mapRel b t) ->
  (forall b t1 t2, mapRel b t1 -> mapRel b t2 -> t1 = t2) -> 
  forall a r, 
    sumList_rel 
    (fun b r' => 
      forall ta', mapRel b ta' ->  
        lowDistApproxFromTree eqdb tb b * lowDistApproxFromTree eqda ta' a == r')
    (getTreeSupport eqdb tb)
    r ->
    lowDistApproxFromTree eqda ta a == r.
  
  induction 1; intuition; simpl in *.
  
  apply sumList_rel_all_0_inv in H1;
    intuition.
  simpl in *.
  intuition.

  eapply sumList_rel_only_one_inv in H2.
  rewrite H2.
  eapply eqRat_refl.
  unfold getTreeSupport.
  simpl.
  eauto.
  unfold getTreeSupport.
  simpl.
  econstructor.
  intuition.
  econstructor.
  intuition.
  simpl in *.
  intuition.

  intuition.
  rewrite <- H3.
  destruct (eqdb a a); intuition.
  rewrite ratMult_1_l.
  eapply eqRat_refl.
  intuition.
  trivial.


  unfold getTreeSupport in *.
  simpl in *.
  assert (sumList_rel
    (fun (b : B) (r' : Rat) =>
      forall ta' : DistApproxTree A,
        mapRel b ta' ->
        ((lowDistApproxFromTree eqdb t1a b * (1 / 2) * lowDistApproxFromTree eqda ta' a) +
          (lowDistApproxFromTree eqdb t2a b * (1 / 2) * lowDistApproxFromTree eqda ta' a) 
          == r'))
    (getUnique (getTreeSupport_dups t1a ++ getTreeSupport_dups t2a) eqdb)
    r).
  
  eapply sumList_rel_body_eq.
  eapply H3.
  intuition.
  rewrite <- ratMult_distrib_r.
  eapply H4; eauto.
  intuition.
  trivial.
  clear H3.
  
  remember (fun b r' => forall ta', 
    (mapRel b ta' -> lowDistApproxFromTree eqdb t1a b * lowDistApproxFromTree eqda ta' a == r')) as rel1.
  remember (fun b r' => forall ta', 
    (mapRel b ta' -> lowDistApproxFromTree eqdb t2a b * lowDistApproxFromTree eqda ta' a == r')) as rel2.
  
  edestruct (sumList_rel_left_total rel1).
  intuition.
  destruct (H1 a0).
  eapply in_getUnique.
  eapply in_or_app.
  left.
  eapply in_getUnique_if.
  eapply H3.
  exists (lowDistApproxFromTree eqdb t1a a0 * lowDistApproxFromTree eqda x a).
  subst.
  intuition.
  assert (x = ta').
  eauto.
  subst.
  intuition.
  
  edestruct (sumList_rel_left_total rel2).
  intuition.
  subst.
  destruct (H1 a0).
  eapply in_getUnique.
  eapply in_or_app.
  right.
  eapply in_getUnique_if.
  eapply H5.
  exists (lowDistApproxFromTree eqdb t2a a0 * lowDistApproxFromTree eqda x0 a).
  intuition.
  assert (x0 = ta').
  eauto.
  subst.
  intuition.

  rewrite IHdatMap1; subst; eauto.
  rewrite IHdatMap2; subst; eauto.

  assert (sumList_rel
    (fun (b : B) (r' : Rat) =>
      forall ta' : DistApproxTree A,
        mapRel b ta' ->
        lowDistApproxFromTree eqdb t1a b * lowDistApproxFromTree eqda ta' a ==
        r' * (2/1)) (getUnique (getTreeSupport_dups t1a) eqdb) (x * (1/2))).
  eapply (sumList_rel_factor_constant (pos 1) (pos 2)).
  eapply sumList_rel_body_eq.
  eapply H3.
  intuition.
  specialize (H6 ta').
  rewrite H6.
  intuition.
  rewrite ratMult_assoc.
  rewrite <- ratMult_1_r at 1.
  eapply ratMult_eqRat_compat; intuition.
  rewrite <- ratMult_num_den.
  symmetry.
  eapply num_dem_same_rat1.
  unfold posnatMult, posnatToNat, natToPosnat.
  trivial.
  trivial.
  rewrite ratMult_assoc.
  rewrite <- ratMult_1_r at 1.
  eapply ratMult_eqRat_compat; intuition.
  rewrite <- ratMult_num_den.
  symmetry.
  eapply num_dem_same_rat1.
  trivial.
  trivial.
  
  clear H3.

  assert (sumList_rel
    (fun (b : B) (r' : Rat) =>
      forall ta' : DistApproxTree A,
        mapRel b ta' ->
        lowDistApproxFromTree eqdb t2a b * lowDistApproxFromTree eqda ta' a ==
        r' * (2/1)) (getUnique (getTreeSupport_dups t2a) eqdb) (x0 * (1/2))).
  eapply (sumList_rel_factor_constant (pos 1) (pos 2)).
  eapply sumList_rel_body_eq.
  eapply H5.
  intuition.
  specialize (H3 ta').
  intuition.
  rewrite H8.
  rewrite ratMult_assoc.
  rewrite <- ratMult_1_r at 1.
  eapply ratMult_eqRat_compat; intuition.
  rewrite <- ratMult_num_den.
  symmetry.
  eapply num_dem_same_rat1.
  unfold posnatMult, posnatToNat, natToPosnat.
  trivial.
  rewrite ratMult_assoc.
  rewrite <- ratMult_1_r at 1.
  eapply ratMult_eqRat_compat; intuition.
  rewrite <- ratMult_num_den.
  symmetry.
  eapply num_dem_same_rat1.
  trivial.
  trivial.

  clear H5.
  
  assert (sumList_rel
    (fun (b : B) (r' : Rat) =>
      forall ta' : DistApproxTree A,
        mapRel b ta' ->
        lowDistApproxFromTree eqdb t1a b * lowDistApproxFromTree eqda ta' a ==
        r' * (2 / 1)) (getUnique (getTreeSupport_dups t1a ++ getTreeSupport_dups t2a) eqdb)
    (x * (1 / 2))).

  eapply sumList_rel_ls_intersect.
  eapply H6.
  eapply getUnique_NoDup.
  eapply getUnique_NoDup.
  trivial.

  intuition.
  destruct (H1 a0). 
  eapply in_getUnique.
  eapply in_or_app.
  left.
  eapply in_getUnique_if.
  eauto.

  assert (r1 * (2/1) == r2 * (2/1)).
  rewrite <- H7.
  rewrite <- H8.
  eapply eqRat_refl.
  eauto.
  eauto.
  
  eapply ratMult_same_r_inv.
  eauto.
  intuition.

  intuition.
  exfalso.
  eapply H7.
  eapply in_getUnique.
  eapply in_or_app.
  left.
  eapply in_getUnique_if.
  eauto.
  
  intuition.
  rewrite ratMult_0_l.
  eapply ratMult_0.
  left.

  eapply lowDistApproxFromTree_eq_0.
  unfold getTreeSupport.
  intuition.
  
  clear H6.
  
  assert (sumList_rel
    (fun (b : B) (r' : Rat) =>
      forall ta' : DistApproxTree A,
        mapRel b ta' ->
        lowDistApproxFromTree eqdb t2a b * lowDistApproxFromTree eqda ta' a ==
        r' * (2 / 1)) (getUnique (getTreeSupport_dups t1a ++ getTreeSupport_dups t2a) eqdb)
    (x0 * (1 / 2))).
  
  eapply sumList_rel_ls_intersect.
  eapply H3.
  eapply getUnique_NoDup.
  eapply getUnique_NoDup.
  trivial.
  
  intuition.
  destruct (H1 a0).
  eapply in_getUnique.
  eapply in_or_app.
  right.
  eapply in_getUnique_if.
  eauto.

  assert (r1 * (2/1) == r2 * (2/1)).
  rewrite <- H7.
  rewrite <- H8.
  eapply eqRat_refl.
  eauto.
  trivial.
  
  eapply ratMult_same_r_inv.
  eauto.
  intuition.
  
  intuition.
  exfalso.
  eapply H7.
  eapply in_getUnique.
  eapply in_or_app.
  right.
  eapply in_getUnique_if.
  eauto.
  
  intuition.
  rewrite ratMult_0_l.
  eapply ratMult_0.
  left.
  eapply lowDistApproxFromTree_eq_0.
  intuition.
  
  clear H3.
 
  symmetry.
  eapply sumList_rel_plus_inv.
  3:{
    eapply H5.
  }
  3:{
    eapply H6.
  }
  eapply H4.
  intuition.
  destruct (H1 a0).
  trivial.
  rewrite <- H7; eauto.
  specialize (H8 _ H10).
  specialize (H9 _ H10).
  eapply ratMult_inverse_nat in H8.
  eapply ratMult_inverse_nat in H9.
  eapply ratAdd_eqRat_compat.
  
  rewrite ratMult_assoc.
  rewrite (ratMult_comm (1/2)).
  rewrite <- ratMult_assoc.
  eapply H8.
  
  rewrite ratMult_assoc.
  rewrite (ratMult_comm (1/2)).
  rewrite <- ratMult_assoc.
  eauto.

  intuition.
  destruct (H1 b).
  eapply in_getUnique.
  eapply in_or_app.
  right.
  eapply in_getUnique_if.
  eauto.
  econstructor.
  eauto.

  intuition.
  destruct (H1 b).
  eapply in_getUnique.
  eapply in_or_app.
  left.
  eapply in_getUnique_if.
  eauto.
  econstructor.
  eauto.
Qed.


Lemma getTreeSupport_approx_0: forall (A : Set)(eqd : eq_dec A)(t : DistApproxTree A) a,
  ~In a (getTreeSupport eqd t) ->
  lowDistApproxFromTree eqd t a == 0.
  
  induction t; intuition; simpl in *.
  destruct o.
  simpl in *.
  intuition.
  destruct (eqd a a0); subst; intuition.
  intuition.
  
  rewrite IHt1.
  rewrite IHt2.
  rewrite ratMult_0_l.
  rewrite <- ratAdd_0_r.
  intuition.
  
  intuition.
  eapply H.
  unfold getTreeSupport in *.
  eapply in_getUnique.
  simpl.
  eapply in_or_app.
  right.
  eapply in_getUnique_if.
  eauto.
  
  intuition.
  eapply H.
  unfold getTreeSupport in *.
  eapply in_getUnique.
  simpl.
  eapply in_or_app.
  left.
  eapply in_getUnique_if.
  eauto.
  
Qed.

Lemma lowDistApprox_le_1 : forall (A : Set)(c : Comp A) a n r,
  lowDistApprox c a n r ->
  r <= 1.
  
  intuition.
  unfold lowDistApprox in *.
  destruct H.
  destruct H.
  intuition.
  rewrite H2.
  eapply rat_le_1.
  
  eapply le_trans.
  eapply pred_count_le_length.
  eapply H.
  
  erewrite <- rel_map_length; eauto.
  rewrite getAllBlists_length.
  rattac.
Qed.



Theorem bind_low_tree_approx_same_inv : forall (A B : Set)(eqda : eq_dec A)(c1 : Comp B)(c2 : B -> Comp A) n a t r,
  well_formed_comp c1 ->
  (forall b, In b (getSupport c1) -> well_formed_comp (c2 b))->
  lowDistApprox_bind c1 c2 a n r ->
  dat_correct_bind2 c1 c2 n t ->
  r == lowDistApproxFromTree eqda t a.
  
  intuition.
  
  destruct H2. (*dat_correct_bind2 *)
  intuition.
  inversion H1; clear H1; subst. (*lowDistApprox_bind *)
  unfold dat_correct in *.
  symmetry.
  eapply lowDistApproxFromTree_datMap_inv; intuition.
  eapply H4.
  destruct (@dat_exists n _ (c2 b)).
  eapply H0.
  eapply getTreeSupport_in.
  eauto.
  eauto.
  econstructor.
  eauto.
  
  simpl in *.
  eapply dat_correct_func; eauto.
  
  eapply sumList_rel_ls_intersect.
  eapply sumList_rel_body_eq_strong.
  eapply H2.
  intuition.
  erewrite H5.
  eapply eqRat_refl.
  
  eapply low_tree_approx_same.
  trivial.
  eapply H3.
  eapply low_tree_approx_same.
  eapply H0.
  eapply H1.
  eapply H6.
  intuition.
  eauto.
  
  eapply getSupport_NoDup.
  eapply getUnique_NoDup.
  eapply comp_eq_dec; eauto.
  
  intuition.
  destruct (@dat_exists n _ (c2 a0)).
  eapply H0.
  trivial.
  rewrite <- H5.
  rewrite H6.
  intuition.
  eauto.
  eauto.
  
  intuition.
  eapply ratMult_0.
  left.
  
  eapply getTreeSupport_approx_0.
  eauto.
  
  intuition.
  eapply ratMult_0.
  left.
  eapply getTreeSupport_approx_0.
  intuition.
  eapply H5.
  eapply getTreeSupport_in; eauto.
  
  Grab Existential Variables.
  eapply comp_eq_dec; eauto.
Qed.

Lemma in_flattenPair_inv : forall (A B : Set)(ls : list (A * list B)) a b,
  In (a, b) (flattenPair ls) ->
  exists lsb,
    In b lsb /\ In (a , lsb) ls.
  
  induction ls; intuition; simpl in *.
  intuition.
  
  apply in_app_or in H.
  intuition.
  apply in_map_iff in H0.
  destruct H0.
  intuition.
  inversion H0; clear H0; subst.
  econstructor.
  split.
  eauto.
  left.
  trivial.
  
  edestruct IHls.
  eauto.
  intuition.
  econstructor.
  split.
  eauto.
  right.
  trivial.
Qed.

Lemma in_getSupport_bind_cp_fst : forall (A B : Set)(c1 : Comp B)(c2 : B -> Comp A) a0,
  In a0 (getSupport_bind_cp c1 c2) -> 
  In (fst a0) (getSupport c1).
  
  intuition.
  unfold getSupport_bind_cp, getSupport_bind in *.
  
  destruct a0.
  eapply in_flattenPair_inv in H.
  destruct H.
  intuition.
  simpl.
  eapply in_map_iff in H1.
  destruct H1.
  intuition.
  inversion H1; clear H1; subst.
  trivial.
  
Qed.

Lemma lowDistApprox_bind_evalDist_limit : forall (A B :Set)(c1 : Comp B)(c2 : B -> Comp A) a,
  well_formed_comp c1 ->
  (forall b, In b (getSupport c1) -> well_formed_comp (c2 b)) ->
  (forall (a : B),
    rat_inf_limit (lowDistApprox c1 a) (evalDist c1 a)) ->
  (forall (b : B) (a : A),
    In b (getSupport c1) ->
    rat_inf_limit (lowDistApprox (c2 b) a) (evalDist (c2 b) a)) ->
  rat_inf_limit (lowDistApprox_bind c1 c2 a) (evalDist (Bind c1 c2) a).
  
  unfold rat_inf_limit, inf_limit.
  intuition.
  
  assert (forall (epsilon : Rat),
    ~ epsilon == 0 ->
    exists n : nat,
      forall n': nat,
        n' >= n -> 
        (forall (b : B) r,
          lowDistApprox c1 b n' r ->
          (ratDistance r (evalDist c1 b)) <= epsilon)).
  
  assert (forall (epsilon : Rat),
    (epsilon == 0 -> False) ->
    forall (a : B),
      exists n : nat,
        forall n' : nat,
          n' >= n -> 
          forall r,
            lowDistApprox c1 a n' r ->
            (ratDistance r (evalDist c1 a) <= epsilon)).
  
  intuition.
  intuition.
  specialize (H4 _ H5).

  edestruct (rel_map_left_total _ (getSupport c1) H4).

  Local Open Scope rat_scope.

  econstructor.
  intuition.
  
  assert (n' >= (maxList x)).
  eapply H7.

  edestruct (in_dec (comp_eq_dec c1) b (getSupport c1)).
  edestruct (rel_map_in_inv H6); eauto.
  intuition.
  eapply H12.

  eapply le_trans.
  eapply maxList_correct; eauto.
  eauto.
  trivial.

  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply (ratIdentityIndiscernables r).  
  eapply eqRat_trans.
  eapply getSupport_not_In_lowDistApprox; eauto.
  eapply eqRat_symm.
  eapply getSupport_not_In_evalDist; eauto.
  eapply rat0_le_all.

  clear H1.

  assert (forall (epsilon : Rat),
      ~ epsilon == 0 ->
      exists n : nat,
        forall n' : nat,
          n' >= n ->
          (forall a b r,
            In b (getSupport c1) ->
            lowDistApprox (c2 b) a n' r ->
            (ratDistance r (evalDist (c2 b) a)) <= epsilon)).


  assert (forall (epsilon : Rat),
    (epsilon == 0 -> False) ->
    forall (x : (B * A)),
      In (fst x) (getSupport c1) ->
      exists n : nat,
        forall n' : nat,
          n' >= n -> 
          forall r,
            lowDistApprox (c2 (fst x)) (snd x) n' r -> 
            (ratDistance r (evalDist (c2 (fst x)) (snd x)) <= epsilon)).

  intuition.

  intuition.
  specialize (H1 epsilon0).
  intuition.
  edestruct (@rel_map_left_total_strong' _ nat (getSupport_bind_cp c1 c2) (fun y => In (fst y) (getSupport c1)) (fun x n => forall n',
         n' >= n ->
         forall r : Rat,
         lowDistApprox (c2 (fst x)) (snd x) n' r ->
         (ratDistance r (evalDist (c2 (fst x)) (snd x))) <= epsilon0)).
  eapply H6.

  eapply in_getSupport_bind_cp_fst.

  exists (maxList x).
  intuition.
  edestruct (in_dec (EqDec_dec (pair_EqDec (comp_EqDec c1) (bind_EqDec c1 c2))) (b, a0) (getSupport_bind_cp c1 c2)).
  edestruct (rel_map_in_inv H1); eauto.
  intuition.
  simpl in *.
  eapply H12.
  eapply le_trans.
  eapply maxList_correct; eauto.
  eauto.
  trivial.

  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply (ratIdentityIndiscernables r).
  apply not_In_getSupport_bind_cp in n.
  edestruct n.
  intuition.

  eapply eqRat_trans.
  eapply getSupport_not_In_lowDistApprox; eauto.
  eapply eqRat_symm.
  eapply getSupport_not_In_evalDist; eauto.
  eauto.
  eapply comp_eq_dec; eauto.
  eapply bind_eq_dec; eauto.
  eapply rat0_le_all.

  clear H2.

  assert (nz (length (getSupport c1))).
  econstructor.
  eapply getSupport_length_nz.
  trivial.

  (*----------------------------- choose epsilon here---------------------------- *)
  specialize (H4 ((1 / 3 ) * (epsilon * (RatIntro 1 (natToPosnat H2))))).
  specialize (H1 ((1 / 3 ) * (epsilon * (RatIntro 1 (natToPosnat H2))))).
  (* ---------------------------- choose epsilon here ------------------------------- *)

  edestruct H4.
  eapply ratMult_nz;
  econstructor.
  rattac.
  eapply ratMult_nz; econstructor; intuition.
  clear H4.
  
  edestruct H1.
  eapply ratMult_nz; econstructor.
  rattac.
  eapply ratMult_nz; econstructor; intuition.
  clear H1.

  exists (max x x0).
  intuition.

  inversion H6; clear H6; subst.

  eapply (@leRat_trans _ (epsilon * (RatIntro 1 (natToPosnat H2)) * (length (getSupport c1) / 1))).

  simpl.
  eapply sumList_rel_distance; eauto.
  intuition.

  2:{
    eapply sumList_rel_sumList.
  }
  simpl in *.
  subst.

  assert (well_formed_comp (c2 a0)).
  eapply H0.
  trivial.

  destruct (@lowDistApprox_left_total _ (comp_eq_dec c1) c1 a0 H n').
  destruct (@lowDistApprox_left_total _ (bind_eq_dec c1 c2) (c2 a0) a H9 n').

  erewrite H8; eauto.

  eapply leRat_trans.
  eapply ratDistance_ratMult_le.

  eapply H5.
  eapply Max.max_lub_l.
  eapply H1.
  trivial.
  eapply H4.
  eapply Max.max_lub_r.
  eapply H1.
  trivial.
  trivial.
  
  eapply lowDistApprox_le_1; eauto.
  eapply lowDistApprox_le_1; eauto.

  eapply evalDist_le_1.
  eapply evalDist_le_1.

  rewrite <- ratMult_assoc.
  rewrite <- ratMult_num_den.

  rewrite num_dem_same_rat1.
  rewrite ratMult_1_l.
  eapply leRat_refl.
  unfold posnatMult, natToPosnat, posnatToNat.
  trivial.

  rewrite ratMult_assoc.
  rewrite ratMult_comm.
  rewrite <- ratMult_num_den.
  rewrite num_dem_same_rat1.
  rewrite ratMult_1_l.
  eapply leRat_refl.
  unfold posnatMult, natToPosnat, posnatToNat.
  rewrite mult_comm.
  trivial.

Qed.

Lemma datMap_left_total : forall (A B : Set)(eqdb : eq_dec A)(t : DistApproxTree A)(f : A -> DistApproxTree B -> Prop),
  (forall a, In a (getTreeSupport eqdb t) -> exists b, f a b) ->
  exists t',
    datMap f t t'.
  
  induction t; intuition; simpl in *.
  destruct o.
  destruct (H a).
  simpl.
  intuition.
  econstructor.
  econstructor.
  eauto.
  
  econstructor.
  econstructor.
  
  edestruct IHt1; eauto.
  intuition.
  edestruct H.
  unfold getTreeSupport in *.
  simpl in *.
  eapply in_getUnique.
  eapply in_or_app.
  left.
  eapply in_getUnique_if.
  eauto.
  econstructor; eauto.

  edestruct IHt2; eauto.
  intuition.
  edestruct H.
  unfold getTreeSupport in *.
  simpl in *.
  eapply in_getUnique.
  eapply in_or_app.
  right.
  eapply in_getUnique_if.
  eauto.
  econstructor; eauto.

  econstructor.
  econstructor; eauto.
  
Qed.
    
Lemma dat_exists_bind2 : forall (A B : Set)(c1 : Comp B)(c2 : B -> Comp A) n,
  well_formed_comp c1 ->
  (forall b, In b (getSupport c1) -> well_formed_comp (c2 b)) ->
  exists t, dat_correct_bind2 c1 c2 n t.
  
  intuition.
  destruct (@dat_exists n _ c1).
  trivial.
  edestruct (@datMap_left_total B A (comp_eq_dec c1) x).
  2:{
    econstructor.
    econstructor.
    intuition.
    eauto.
    eauto.
  }

  intuition.
  destruct (@dat_exists n _ (c2 a)).
  eapply H0.
  eapply getTreeSupport_in.
  eauto.
  eauto.
  econstructor.
  eauto.
  
Qed.

(* dat_better is an inductive predicate that lets us conclude that one tree will produce an approximation that is at least as good as some other tree. *)
Inductive dat_better(A : Set) : DistApproxTree A -> DistApproxTree A -> Prop :=
| dat_better_leaf_None : forall t,
  dat_better t (dat_leaf None)
| dat_better_leaf_Some : forall a,
  dat_better (dat_leaf (Some a)) (dat_leaf (Some a))
| dat_better_internal : forall ta1 ta2 tb1 tb2,
  dat_better ta1 tb1 ->
  dat_better ta2 tb2 ->
  dat_better (dat_internal ta1 ta2) (dat_internal tb1 tb2).

Hint Constructors dat_better : dat.

Lemma dat_better_refl : forall (A : Set)(t : DistApproxTree A),
  dat_better t t.
  
  induction t; intuition.
  destruct o; econstructor.
Qed.

Lemma dat_better_trans : forall (A : Set)(t1 t2 : DistApproxTree A),
  dat_better t1 t2 ->
  forall t3, 
    dat_better t2 t3 ->
    dat_better t1 t3.
  
  induction 1; intuition.
  inversion H; clear H; subst; eauto with  dat.
  inversion H1; clear H1; subst.
  econstructor.
  econstructor; eauto.
Qed.

Lemma dat_correct_dat_better : forall (A : Set)(c : Comp A) ls n1 t1,
  dat_correct_h c ls n1 t1 ->
  forall n2 t2,
    dat_correct_h c ls n2 t2 ->
    n1 >= n2 ->
    dat_better t1 t2.
  
  induction 1; intuition.
  
  inversion H0; clear H0; subst.
  assert (ca_done a = ca_done a0).
  eapply evalDet_func; eauto.
  inversion H0.
  econstructor.
  econstructor.
  specialize (H2 a).
  intuition.
  
  inversion H0; clear H0; subst.
  specialize (H a).
  intuition.
  econstructor.
  omega.
  
  inversion H2; clear H2; subst.
  specialize (H a).
  intuition.
  econstructor.
  assert (n >= n0).
  omega.
  eauto with dat.
Qed.

Lemma lowDistApprox_dat_better_le : forall (A : Set)(eqd : eq_dec A)(t1 t2 : DistApproxTree A),
  dat_better t1 t2 ->
  forall (a : A), 
    lowDistApproxFromTree eqd t2 a <= lowDistApproxFromTree eqd t1 a.
  
  induction 1; intuition; simpl in *.
  apply rat0_le_all.
  rewrite <- IHdat_better1.
  rewrite <- IHdat_better2.
  eapply leRat_refl.
Qed.

Lemma datMap_better : forall (A B : Set)(t : DistApproxTree B) n (rel : nat -> B -> DistApproxTree A -> Prop) t1 t2,
  (forall n b t1 t2, rel n b t1 -> rel (pred n) b t2 -> dat_better t1 t2) ->
  datMap (rel n) t t1 ->
  datMap (rel (pred n)) t t2 ->
  dat_better t1 t2.
  
  induction t; intuition; simpl in *.
  inversion H0; clear H0; subst.
  inversion H1; clear H1; subst.
  econstructor.
  inversion H1; clear H1; subst.
  eapply H; eauto.
  
  inversion H0; clear H0; subst.
  inversion H1; clear H1; subst.
  econstructor; eauto.
  
Qed.

Lemma datMap_depth_better : forall (A B : Set)(tb1 tb2 : DistApproxTree B),
  dat_better tb1 tb2 ->
  forall  n1 n2 (f : nat -> B -> DistApproxTree A -> Prop) t1 t2,
    (forall n1 n2 b t1 t2, n1 >= n2 -> f n1 b t1 -> f n2 b t2 -> dat_better t1 t2) ->
    datMap (f n1) tb1 t1 ->
    datMap_depth f n2 tb2 t2 ->
    n1 >= n2 ->
    dat_better t1 t2.
  
  induction 1; intuition; simpl in *.
  inversion H1; clear H1; subst.
  econstructor.
  
  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  eauto.
  
  inversion H2; clear H2; subst.
  inversion H3; clear H3; subst.
  econstructor.
  eapply IHdat_better1; eauto; omega.
  eapply IHdat_better2; eauto; omega.
Qed.

Lemma dat_bind_2_better : forall (n : nat) (A B : Set)(c1 : Comp B)(c2 : B -> Comp A) t1 t2,
  dat_correct_bind2 c1 c2 n t1 ->
  dat_correct_bind c1 c2 n t2 ->
  dat_better t1 t2.
  
  intuition.
  unfold dat_correct_bind, dat_correct_bind2 in *.
  destruct H.
  destruct H0.
  
  intuition.
  eapply datMap_depth_better.
  4:{
    eauto.
  }
  3:{
    simpl.
    eauto.
  }

  eapply dat_correct_dat_better; eauto.
  
  intuition.
  eapply dat_correct_dat_better; eauto.
  omega.
Qed.

Lemma dat_correct_h_bind_app : forall (A B : Set) t (c1 : Comp B)(c2 : B -> Comp A) n ls1 ls2 a,
  evalDet_steps (cs_more c1 ls1) (cs_done a nil) ->
  dat_correct_h (Bind c1 c2) (ls1 ++ ls2) n t ->
  dat_correct_h (c2 a) ls2 n t.
  
  induction t; intuition; simpl in *.
  inversion H0; clear H0; subst.
  inversion H3; clear H3; subst.
  apply evalDet_steps_bind_done_inv in H1.
  destruct H1. destruct H0.
  intuition.
  assert (evalDet_steps (cs_more c1 (ls1 ++ ls2)) (cs_done a (nil ++ ls2))).
  eapply evalDet_steps_app_eq.
  eauto.
  simpl in *.
  specialize (evalDet_steps_done_func H1 H0); intuition; subst.
  econstructor.
  econstructor.
  eauto.
  
  econstructor.
  intuition.
  inversion H0; clear H0; subst.
  eapply H3.
  econstructor.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eapply evalDet_steps_app_eq.
  eauto.
  simpl.
  eauto.
  
  inversion H0; clear H0; subst.
  econstructor.
  intuition.
  inversion H0; clear H0; subst.
  eapply H3.
  econstructor.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eapply evalDet_steps_app_eq.
  eauto.
  simpl.
  eauto.
  
  eapply IHt1.
  eauto.
  rewrite app_assoc.
  eauto.
  eapply IHt2.
  eauto.
  rewrite app_assoc.
  eauto.
      
Qed.

Lemma dat_correct_bind_same_h : forall n (A : Set)(c : Comp A) ls t,
  dat_correct_h c ls n t ->
  forall (B : Set)(c1 : Comp B)(c2 : B -> Comp A) t1,
    c = Bind c1 c2 ->
    well_formed_comp c1 ->
    (forall a ls', evalDet_steps (cs_more c1 ls) (cs_done a ls') -> ls' = nil) -> 
    dat_correct_h c1 ls n t1 ->  
    datMap_depth
    (fun (depth : nat) (b : B) t2 => dat_correct_h (c2 b) nil depth t2) 
    n t1 t.
  
  induction 1; intuition; subst; simpl in *.
  inversion H; clear H; subst. (*evalDet *)
  inversion H3; clear H3; subst. (*dat_correct *)
  inversion H; clear H; subst. (*evalDet *)
  apply evalDet_steps_bind_done_inv in H4.
  destruct H4. destruct H. intuition.

  econstructor.
  econstructor.
  specialize (evalDet_steps_done_func H3 H0); intuition; subst.
  assert (x0 = nil); eauto; subst.
  econstructor.
  eauto.
  
  apply evalDet_steps_bind_done_inv in H4.
  destruct H4. destruct H0. intuition.
  exfalso.
  eapply H.
  econstructor. 
  eauto.
  apply evalDet_steps_bind_done_inv in H4.
  destruct H4. destruct H3. intuition.
  exfalso.
  eapply H.
  econstructor. 
  eauto.
  
  inversion H3; clear H3; subst.
  inversion H0; clear H0; subst.
  econstructor.
  econstructor.
  intuition.
  inversion H0; clear H0; subst.
  assert (s' = nil); eauto; subst.
  eapply H.
  econstructor.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.      
  eauto.
  eauto.
  
  econstructor.
  
  inversion H5; clear H5; subst.
  inversion H2; clear H2; subst.
  assert (s' = nil); eauto; subst.
  econstructor.
  econstructor.
  intuition.
  inversion H2; clear H2; subst.
  eapply H.
  econstructor.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eauto.
  eauto.
  simpl.  

  eapply dat_correct_h_bind_app; eauto.
  eapply dat_correct_h_bind_app; eauto.

  econstructor.
  eapply IHdat_correct_h1; eauto.
  intuition.
  
  eapply evalDet_app_nil; eauto.
  edestruct (@evalDet_dec _ c1 s); trivial.
  destruct H5.
  exfalso. 
  eauto.
  
  eapply IHdat_correct_h2; eauto.
  intuition.
  eapply evalDet_app_nil; eauto.
  edestruct (@evalDet_dec _ c1 s); trivial.
  destruct H5.
  exfalso.
  eauto.
Qed.

Lemma lowDistApprox_le_bind : forall n (A B : Set)(c1 : Comp B)(c2 : B -> Comp A) a r1 r2,
  well_formed_comp c1 ->
  (forall b, In b (getSupport c1) -> well_formed_comp (c2 b)) ->
  lowDistApprox (Bind c1 c2) a n r1 -> 
  lowDistApprox_bind c1 c2 a n r2 ->
  r1 <= r2.
  
  intuition.
  edestruct dat_exists_bind2.
  eauto.
  eauto.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eapply (bind_low_tree_approx_same_inv).
    eauto.
    eauto.
    eauto.
    eauto.
  }

  edestruct dat_exists.
  eapply well_formed_Bind; eauto.

  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  symmetry.
  eapply low_tree_approx_same_inv.
  eauto.
  eauto.
  
  apply lowDistApprox_dat_better_le.
  
  inversion H3; clear H3; subst.
  intuition.
  eapply datMap_depth_better.
  4:{
    eapply dat_correct_bind_same_h.
    eapply H4.
    eauto.
    trivial.
    intuition.
    eapply evalDet_steps_done_nil_inv; eauto.
    eauto.
  }

  eapply dat_better_refl.
  intuition.
  eapply dat_correct_dat_better.
  eapply H7.
  eapply H8.
  trivial.
  eapply H6.
  auto.
  
  Grab Existential Variables.
  eapply bind_eq_dec; eauto.
  
Qed.

Lemma dat_correct_bind_same: forall (A B : Set)(c1 : Comp B)(c2 : B -> Comp A) n t,
  well_formed_comp c1 ->
  dat_correct (Bind c1 c2) n t ->
  dat_correct_bind c1 c2 n t.
  
  intuition.
  unfold dat_correct_bind in *.
  edestruct (dat_exists).
  eauto.
  econstructor.
  intuition.
  eauto.
  eapply dat_correct_bind_same_h.
  eauto.
  eauto.
  trivial.
  intuition.
  eapply evalDet_nil; eauto.
  
  eauto.
Qed.
    
Fixpoint datDepth (A : Set)(t : DistApproxTree A) : nat :=
  match t with
    | dat_leaf o => O
    | dat_internal t1 t2 =>
      S (max (datDepth t1) (datDepth t2))
  end.

Lemma datMap_depth_better' : forall (B : Set)(tb1 tb2 : DistApproxTree B),
  dat_better tb1 tb2 ->
  forall (A : Set)(rel : nat -> B -> DistApproxTree A -> Prop) n n' t1 t2,
    datMap_depth rel n tb1 t1 ->
    datMap (rel n') tb2 t2 ->
    n >= n' + (datDepth tb2) ->
    (forall b n1 n2 t1 t2, rel n1 b t1 -> rel n2 b t2 -> n1 >= n2 -> dat_better t1 t2) -> 
    dat_better t1 t2.
  
  induction 1; intuition; simpl in *.
  inversion H0; clear H0; subst.
  econstructor.
  
  inversion H0; clear H0; subst.
  inversion H; clear H; subst.
  eapply H2; eauto.
  omega.
  
  inversion H2; clear H2; subst.
  inversion H1; clear H1; subst.
  econstructor.
  eapply IHdat_better1.
  eauto.
  eauto.
  destruct (le_dec (datDepth tb1) (datDepth tb2)).
  rewrite Max.max_r in H3; eauto.
  omega.
  rewrite Max.max_l in H3; omega.
  eauto.
  
  eapply IHdat_better2.
  eauto.
  eauto.
  destruct (le_dec (datDepth tb1) (datDepth tb2)).
  rewrite Max.max_r in H3; omega.
  rewrite Max.max_l in H3; omega.
  eauto.
  
Qed.

Lemma datCorrect_datDepth : forall (A : Set)(c : Comp A) n t,
  dat_correct c n t ->
  (datDepth t <= n)%nat.
  
  induction 1; intuition; simpl in *.
  
  destruct (le_dec (datDepth t1) (datDepth t2)).
  rewrite Max.max_r; eauto.
  omega.
  rewrite Max.max_l; omega.
Qed.

Lemma dat_better_bind_div2 : forall (A B : Set)(c1 : Comp B)(c2 : B -> Comp A) n t1 t2,
  dat_correct_bind c1 c2 n t1 ->
  dat_correct_bind2 c1 c2 (div2 n) t2 ->
  dat_better t1 t2.
  
  intuition.
  unfold dat_correct_bind, dat_correct_bind2 in *.
  destruct H.
  destruct H0.
  intuition.
  
  eapply datMap_depth_better'.
  eapply dat_correct_dat_better.
  eapply H1.
  eapply H.
  eapply div2_le.
  eauto.
  simpl.
  eauto.
  
  eapply le_trans.
  2:{
    eapply div2_ge_double.
  }
  eapply plus_le_compat.
  auto.
  eapply datCorrect_datDepth.
  eauto.
  
  intuition.
  eapply dat_correct_dat_better; eauto.
  
Qed.

Lemma lowDistApprox_bind_le_div2 : forall (A B : Set)(c1 : Comp B)(c2 : B -> Comp A) a n r1 r2,
  well_formed_comp c1 ->
  (forall b, In b (getSupport c1) -> well_formed_comp (c2 b)) ->
  lowDistApprox_bind c1 c2 a (div2 n) r1 ->
  lowDistApprox (Bind c1 c2) a n r2 ->
  r1 <= r2.
  
  intuition.
  
  edestruct (dat_exists_bind2).
  eauto.
  eauto.
  rewrite bind_low_tree_approx_same_inv; eauto.
  edestruct dat_exists.
  eapply well_formed_Bind; eauto.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    eapply low_tree_approx_same_inv.
    eapply H4.
    eapply H2.
  }
  
  eapply lowDistApprox_dat_better_le.
  apply dat_correct_bind_same in H4.
  eapply dat_better_bind_div2; eauto.
  trivial.
  
  Grab Existential Variables.
  eapply bind_eq_dec; eauto.
  
Qed.

Lemma lowDistApprox_func : forall (A : Set)(c : Comp A) a n r1 r2,
  well_formed_comp c ->
  lowDistApprox c a n r1 ->
  lowDistApprox c a n r2 ->
  r1 == r2.
  
  intuition.
  edestruct (dat_exists).
  eauto.
  rewrite <- low_tree_approx_same_inv; eauto.
  eapply low_tree_approx_same_inv; eauto.
  
  Grab Existential Variables.
  eapply comp_eq_dec; eauto.
  
Qed.

Lemma lowDistApprox_bind_left_total : forall (A B : Set)(c1 : Comp B)(c2 : B -> Comp A) a,
  well_formed_comp c1 ->
  (forall b, In b (getSupport c1) -> well_formed_comp (c2 b)) -> 
  left_total (lowDistApprox_bind c1 c2 a).
  
  intuition.
  unfold left_total.
  intuition.
  
  edestruct (sumList_rel_left_total).
  intuition.
  2:{
    econstructor.
    econstructor.
    eauto.
  }
  
  simpl.
  edestruct lowDistApprox_left_total.
  eapply bind_eq_dec; eauto.
  eauto.
  edestruct lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  eapply H.
  
  exists (x0 * x).
  intuition.
  
  eapply ratMult_eqRat_compat.
  eapply lowDistApprox_func; eauto.
  eapply lowDistApprox_func.
  eapply H0.
  eauto.
  eauto.
  eauto.
Qed.

Lemma lowDistApprox_bind_div2_left_total : forall (A B : Set)(c1 : Comp B)(c2 : B -> Comp A) a,
  well_formed_comp c1 ->
  (forall b, In b (getSupport c1) -> well_formed_comp (c2 b)) ->
  left_total (fun n => lowDistApprox_bind c1 c2 a (div2 n)).
  
  intuition.
  unfold left_total.
  intuition.
  eapply lowDistApprox_bind_left_total; eauto.
Qed.

Lemma rel_map_Rnd_NoDup : forall n ls,
  rel_map (evalDet (Rnd n)) (getAllBlists n) ls ->
  NoDup ls.
  
  intuition.
  eapply rel_map_NoDup.
  eauto.
  eapply getAllBlists_NoDup.
  intuition.
  subst.
  
  inversion H4; clear H4; subst.
  inversion H5; clear H5; subst.
  inversion H3; clear H3; subst.
  inversion H5; clear H5; subst.
  simpl in *.
  
  edestruct shiftOut_Some.
  
  eapply le_refl_gen.
  symmetry.
  eapply getAllBlists_In_length.
  eauto.
  rewrite H3 in H9.
  
  edestruct shiftOut_Some.
  eapply le_refl_gen.
  symmetry.
  eapply getAllBlists_In_length.
  eapply H0.
  rewrite H4 in H8.
  destruct x.
  destruct x0.
  
  inversion H9; clear H9; subst.
  inversion H8; clear H8; subst.
  simpl in *.
  inversion H11; clear H11; subst.
  inversion H10; clear H10; subst.
  
  eapply H2.
  specialize (shiftOut_ls_eq _ _ H3 H4); intuition; eauto.
  
  erewrite <- (firstn_eq_all_gen a1).
  erewrite <- (firstn_eq_all_gen a2).
  eauto.
  symmetry.
  eapply getAllBlists_In_length.
  trivial.
  symmetry.
  eapply getAllBlists_In_length.
  trivial.
  
  inversion H5; clear H5; subst.
  simpl in *.
  edestruct shiftOut_Some.
  eapply le_refl_gen.
  symmetry.
  eapply getAllBlists_In_length.
  eapply H1.
  rewrite H4 in H9.
  destruct x.
  inversion H9; clear H9; subst.
  simpl in *.
  inversion H10.
  
Qed.

Lemma rel_map_Rnd_any_in : forall n ls (a : Bvector n),
  rel_map (evalDet (Rnd n)) (getAllBlists n) ls ->
  In (ca_done a) ls.
  
  intuition.
  eapply (rel_map_in H _ _ (VectorDef.to_list a)).
  eapply getAllBlists_length_In.
  eapply to_list_length.
  
  econstructor.
  econstructor.
  eauto.
  simpl.
  
  rewrite shiftOut_to_list.
  econstructor.
  eauto.
  simpl.
  econstructor.
  
  Grab Existential Variables.
  intuition.
  eapply evalDet_func; eauto.
  
Qed.

Theorem lowDistApprox_Rnd: forall n2 n1 (a : Bvector n1) r,
  lowDistApprox (Rnd n1) a (n1 + n2) r ->
  r == (1 / (expnat 2 n1)).
  
  induction n2; intuition; simpl in *.
  
  rewrite plus_0_r in *.
  unfold lowDistApprox in *.
  destruct H.
  destruct H.
  intuition.
  rewrite H2.
  eapply eqRat_terms.
  
  eapply pred_count_eq_1_inv; eauto.
  eapply comp_answer_eq_dec.
  unfold eq_dec.
  intuition.
  eapply Bvector_eq_dec.
  
  eapply rel_map_Rnd_NoDup.
  trivial.
  trivial.
  
  eapply rel_map_Rnd_any_in.
  trivial.
  trivial.

  
  unfold lowDistApprox in H.
  destruct H. 
  destruct H.
  intuition.
  
  edestruct (rel_map_left_total (evalDet (Rnd n1))). 
  intuition.
  eapply evalDet_left_total.
  eapply well_formed_Rnd.
  
  assert (pred_count (eq (ca_done a)) x1 x0).
  eapply pred_count_permutation.
  
  eapply rel_map_permutation.
  eapply getAllBlists_perm.
  intuition.
  eapply evalDet_func; eauto.
  
  2:{
    eapply H0.
  }
    
  intuition.
  eapply evalDet_left_total.
  eapply well_formed_Rnd.
  
  eauto.
  eauto.
  
  assert ((n1 + S n2) = (S (n1 + n2)))%nat.
  omega.
  rewrite H4 in H1.
  simpl in *.
  
  apply rel_map_app_inv in H1.
  intuition.
  rewrite map_length in H5.
  rewrite map_length in H6.
  
  unfold lowDistApprox in *.
  apply rel_map_map_inv in H5.
  apply rel_map_map_inv in H6.
  
  assert (rel_map (evalDet (Rnd n1)) (getAllBlists_app (n1 + n2)) (firstn (length (getAllBlists_app (n1 + n2))) x1)).
  eapply rel_map_eq.
  eapply H5.
  trivial.
  intuition.
  
  assert (length a0 = (n1 + n2)%nat).
  eapply getAllBlists_app_In_length.
  eauto.
  inversion H8; clear H8; subst.
  inversion H10; clear H10; subst.
  simpl in *.
  
  edestruct shiftOut_Some.
  assert (length a0 >= n1)%nat.
  omega.
  eapply H8.
  destruct x2.
  erewrite shiftOut_app in H14; eauto.
  inversion H14; clear H14; subst.
  simpl in *.
  inversion H15; clear H15; subst.
  
  econstructor.
  econstructor.
  eauto.
  simpl.
  rewrite H8.
  econstructor.
  eauto.
  simpl.
  econstructor.
  
  inversion H10; clear H10; subst.
  simpl in *.
  case_eq (shiftOut (a0 ++ true :: nil) n1); intuition.
  rewrite H8 in H14.
  destruct p.
  inversion H14; clear H14; subst.
  simpl in *.
  inversion H15.
  rewrite H8 in H14.
  
  econstructor.
  econstructor.
  eauto.
  simpl.
  erewrite shiftOut_app_None.
  econstructor.
  eauto.
  clear H5.
  
  assert (rel_map (evalDet (Rnd n1)) (getAllBlists_app (n1 + n2)) (skipn (length (getAllBlists_app (n1 + n2))) x1)).
  eapply rel_map_eq.
  eapply H6.
  trivial.
  intuition.
  
  assert (length a0 = (n1 + n2)%nat).
  eapply getAllBlists_app_In_length.
  eauto.
  inversion H8; clear H8; subst.
  inversion H10; clear H10; subst.
  simpl in *.
  
  edestruct shiftOut_Some.
  assert (length a0 >= n1)%nat.
  omega.
  eapply H8.
  destruct x2.
  erewrite shiftOut_app in H14; eauto.
  inversion H14; clear H14; subst.
  simpl in *.
  inversion H15; clear H15; subst.
    
  econstructor.
  econstructor.
  eauto.
  simpl.
  rewrite H8.
  econstructor.
  eauto.
  simpl.
  econstructor.
  
  inversion H10; clear H10; subst.
  simpl in *.
  case_eq (shiftOut (a0 ++ false :: nil) n1); intuition.
  rewrite H8 in H14.
  destruct p.
  inversion H14; clear H14; subst.
  simpl in *.
  inversion H15.
  rewrite H8 in H14.
  
  econstructor.
  econstructor.
  eauto.
  simpl.
  erewrite shiftOut_app_None.
  econstructor.
  eauto.
  
  clear H6.    
  
  eapply (pred_count_first_skip) in H3.
  destruct H3. destruct H3. intuition.
  
  edestruct (rel_map_left_total (evalDet (Rnd n1)) (getAllBlists (n1 + n2))).
  intuition.
  eapply evalDet_left_total.
  eapply well_formed_Rnd.
  
  rewrite H4 in H2.
  simpl in *.
  rewrite <- H8 in H2.
  assert (r * (2/1) == (x2 + x3) / (expnat 2 (n1 + n2))).
  rewrite H2.

  assert (nz (expnat 2 (n1 + n2))%nat).
  econstructor.
  eapply expnat_pos.
  omega.
  
  assert (nz 2)%nat.
  econstructor. omega.
  
  eapply eqRat_trans.
  eapply ratMult_eqRat_compat.
  eapply (@eqRat_terms _ _ (x2 + x3)%nat (posnatMult (natToPosnat H10) (natToPosnat H9))).
  trivial.
  simpl.
  trivial.
  eapply eqRat_refl.
  rewrite <- ratMult_num_den.
  eapply eqRat_trans.
  eapply eqRat_terms.
  eapply mult_comm.
  eapply posnatMult_1_r.
  
  rewrite rat_remove_common_factor.
  eapply eqRat_terms; eauto.
  
  rewrite ratAdd_den_same in H9.

  assert (x2 / (expnat 2 (n1 + n2)) == 1 / expnat 2 n1).
  eapply IHn2.
  econstructor. econstructor.
  intuition.
  eauto.
  eapply pred_count_permutation.
  eapply Permutation_sym.
  eapply rel_map_permutation.
  eapply getAllBlists_perm.
  intuition.
  eapply evalDet_func; eauto.
  2:{
    eauto.
  }
  intuition.
  eapply evalDet_left_total.
  eapply well_formed_Rnd.
  eapply H1.
  eauto.
  eapply eqRat_terms; eauto.
  
  assert (x3 / expnat 2 (n1 + n2) == 1 / expnat 2 n1).
  eapply IHn2.
  econstructor. econstructor.
  intuition.
  eauto.
  eapply pred_count_permutation.
  eapply Permutation_sym.
  eapply rel_map_permutation.
  eapply getAllBlists_perm.
  intuition.
  eapply evalDet_func; eauto.
  2:{
    eapply H7.
  }
  intuition.
  eapply evalDet_left_total.
  eapply well_formed_Rnd.
  eapply H5.
  eauto.
  eapply eqRat_terms; eauto.
  
  rewrite H10 in H9.
  rewrite H11 in H9.
  rewrite ratMult_2 in H9.   
  eapply ratMult_same_r_inv.
  eauto.
  rattac.
Qed.

Definition indicator_rel (A : Set)(P : A -> bool) a (r : Rat) :=
  (P a = true /\ r == 1) \/ (P a = false /\ r == 0).

Definition lowDistApprox_repeat (A : Set)(c : Comp A)(P : A -> bool) a n : Rat -> Prop := 
  let approx := lowDistApprox c a n in
    let empty := sumList_rel (fun a => lowDistApprox c a n) (filter (fun a => negb (P a)) (getSupport c)) in
  ratMult_rel (ratMult_rel (indicator_rel P a)
    (sumList_rel (fun i => (expRat_rel empty i)) (getNats O (S n)))) (* used to be 0 to n *)
  approx.


Lemma lowDistApprox_repeat_left_total : forall (A : Set)(c : Comp A)(P : A -> bool) a,
  well_formed_comp c ->
  left_total (lowDistApprox_repeat c P a).

  unfold left_total; intuition.
  edestruct (sumList_rel_left_total
    (fun (i : nat) (r : Rat) =>
       forall r1'1 : Rat,
       sumList_rel (fun a0 : A => lowDistApprox c a0 n)
         (filter (fun a0 : A => negb (P a0)) (getSupport c)) r1'1 ->
       r == expRat r1'1 i)
    (getNats O (S n))).  (* used to be 0 to n *)
  intuition.

  edestruct (sumList_rel_left_total
    (fun a1 : A => lowDistApprox c a1 n)
    (filter (fun a1 : A => negb (P a1)) (getSupport c)) ).
  intuition.
  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  trivial.
  econstructor.
  intuition.
  eapply expRat_eqRat_compat.
  eapply sumList_rel_func; eauto.
  intuition.
  eapply lowDistApprox_func;
  eauto.
  
  edestruct (@lowDistApprox_left_total).
  eapply comp_eq_dec; eauto.
  eauto.

  unfold lowDistApprox_repeat, ratMult_rel, expRat_rel, indicator_rel.
  econstructor.
  intuition.
  eapply ratMult_eqRat_compat.
  symmetry.
  eapply H2; eauto.
  case_eq (P a); intuition.
  left.
  intuition.
  assert (indicator P a == 1).
  unfold indicator.
  rewrite H4.
  intuition.
  eapply H5.
  right.
  intuition.
  unfold indicator.
  rewrite H4.
  intuition.
  eapply lowDistApprox_func; eauto.
  
Qed.



(* Require Import Coq.Numbers.Natural.Peano.NPeano. *)


Lemma lowDistApprox_repeat_sqrt_div2_left_total : forall (A : Set)(c : Comp A)(P : A -> bool) a,
  well_formed_comp c ->
  left_total (fun n => (lowDistApprox_repeat c P a (Nat.sqrt (div2 n)))).

  unfold left_total.
  intuition.
  edestruct lowDistApprox_repeat_left_total; eauto.

Qed.

Inductive datRepeat (A : Set)(f : DistApproxTree A -> Prop)(P : A -> bool) : nat -> DistApproxTree A -> DistApproxTree A -> Prop :=
  | datRepeat_leaf_None : forall n,
    datRepeat f P n (dat_leaf None) (dat_leaf None)
  | datRepeat_leaf_Some_yes : forall a n,
    P a = true ->
    datRepeat f P n (dat_leaf (Some a)) (dat_leaf (Some a))
  | datRepeat_leaf_Some_no : forall a,
    P a = false ->
    datRepeat f P O (dat_leaf (Some a)) (dat_leaf None)
  | datRepeat_leaf_Some_repeat : forall a t t' n,
    f t ->
    P a = false ->
    datRepeat f P n t t' ->
    datRepeat f P (S n) (dat_leaf (Some a)) t'
  | datRepeat_internal : forall n t1 t2 t1' t2',
    datRepeat f P n t1 t1' ->
    datRepeat f P n t2 t2' ->
    datRepeat f P n (dat_internal t1 t2) (dat_internal t1' t2').

Definition dat_correct_repeat2(A : Set)(c : Comp A)(P : A -> bool)(n : nat)(t : DistApproxTree A) :=
exists t1 : DistApproxTree A,
  dat_correct c n t1 /\
  datRepeat (dat_correct c n) P n t1 t. (* was (pred n) *)

Lemma datRepeat_left_total : forall n (A : Set)(eqd : eq_dec A)(t : DistApproxTree A)(f : DistApproxTree A -> Prop) P,
   (exists b : DistApproxTree A, f b) ->
   exists t', datRepeat f P n t t'.
  
  induction n.
  induction t; intuition.
  destruct o.
  case_eq (P a); intuition.
  econstructor.
  econstructor.
  trivial.
  econstructor.
  eapply datRepeat_leaf_Some_no.
  trivial.
  econstructor.
  econstructor.
  edestruct IHt1.
  eauto.

  edestruct IHt2.
  eauto.

  econstructor.
  econstructor; eauto.

  induction t; intuition.
  destruct o.
  destruct H.
  edestruct (IHn _ eqd x).
  eauto.
  
  case_eq (P a); intuition.
  econstructor.  
  econstructor.
  trivial.
  
  edestruct IHn; eauto.
  econstructor.
  eapply datRepeat_leaf_Some_repeat.
  eauto.
  trivial.
  eauto.

  econstructor.
  econstructor.

  edestruct IHt1; eauto.
  edestruct IHt2; eauto.
  econstructor.
  econstructor; eauto.

  Grab Existential Variables.
  eapply P.

  trivial.

Qed.

Lemma dat_exists_repeat2 : forall (A : Set)(c : Comp A)(P : A -> bool)(n : nat),
  well_formed_comp c ->
  exists t : DistApproxTree A, dat_correct_repeat2 c P n t.

  intuition.
  destruct (@dat_exists n _ c).
  trivial.
  edestruct (@datRepeat_left_total n A (comp_eq_dec c) x  (* was (pred n ) *)
  (dat_correct c n) P).
  eapply dat_exists; eauto.

  econstructor.
  unfold dat_correct_repeat2.
  econstructor.
  intuition.
  eauto.
  eauto.
Qed.

(* A function that computes the total empty space in a distribution approximation. *)
Fixpoint computeEmptySpace(A : Set)(t : DistApproxTree A)(P : A -> bool) :=
  match t with
    | dat_leaf o =>
      match o with
        | Some a => indicator (fun a' => (negb (P a'))) a 
        | None => 0
      end
    | dat_internal t1 t2 =>
      (1 / 2) * (computeEmptySpace t1 P)  + (1 / 2) * (computeEmptySpace t2 P)
  end.

Lemma computeEmptySpace_correct : forall (A : Set)(eqd : eq_dec A)(t : DistApproxTree A) P,
  sumList (filter (fun a => negb (P a)) (getTreeSupport eqd t)) (lowDistApproxFromTree eqd t) == (computeEmptySpace t P).
  
  induction t; intuition; simpl in *.
  destruct o.
  simpl.
  unfold indicator.
  unfold sumList.
  case_eq (P a); intuition.
  simpl.
  intuition.
  simpl.
  destruct (eqd a a); intuition; subst.
  rewrite <- ratAdd_0_l.
  intuition.
  unfold sumList.
  simpl.
  intuition.
  
  rewrite sumList_sum.
  unfold getTreeSupport.
  simpl.
  eapply ratAdd_eqRat_compat.
  rewrite sumList_factor_constant_r.
  
  rewrite <- sumList_subset'.
  rewrite IHt1.
  eapply ratMult_comm.
  trivial.
  eapply filter_NoDup.
  eapply getUnique_NoDup.
  eapply filter_NoDup.
  eapply getUnique_NoDup.
  intuition.
  eapply filter_In; intuition.
  eapply in_getUnique.
  eapply in_or_app.
  left.
  eapply in_getUnique_if.
  eapply filter_In.
  eauto.
  apply filter_In in H.
  intuition.
  intuition.
  eapply getTreeSupport_approx_0.
  intuition.
  eapply H0.
  eapply filter_In.
  intuition.
  apply filter_In in H.
  intuition.
  
  rewrite sumList_factor_constant_r.
  rewrite <- sumList_subset'.
  rewrite IHt2.
  eapply ratMult_comm.
  trivial.
  eapply filter_NoDup.
  eapply getUnique_NoDup.
  eapply filter_NoDup.
  eapply getUnique_NoDup.
  intuition.
  eapply filter_In; intuition.
  eapply in_getUnique.
  eapply in_or_app.
  right.
  eapply in_getUnique_if.
  eapply filter_In.
  eauto.
  apply filter_In in H.
  intuition.
  intuition.
  eapply getTreeSupport_approx_0.
  intuition.
  eapply H0.
  eapply filter_In.
  intuition.
  apply filter_In in H.
  intuition.
Qed.

Lemma lowDistApprox_val_eq : forall (A : Set)(c : Comp A) a n r1 r2,
  lowDistApprox c a n r1 ->
  r1 == r2 ->
  lowDistApprox c a n r2.
 
  intuition.
  unfold lowDistApprox in *.
  destruct H. destruct H. intuition.
  econstructor. econstructor. intuition.
  eauto.
  eauto.
  rewrite <- H0.
  trivial.
Qed.

Lemma repeat_low_tree_approx_same_tree_inv : forall (A : Set)(eqd : eq_dec A)(P : A -> bool)(t1 t2 t3 : DistApproxTree A) n a,
  datRepeat (eq t3) P n t1 t2 ->
  lowDistApproxFromTree eqd t2 a == 
  indicator P a * 
  ((lowDistApproxFromTree eqd t1 a) + 
    (computeEmptySpace t1 P) * 
    sumList (getNats 0 n) (expRat (computeEmptySpace t3 P)) * (lowDistApproxFromTree eqd t3 a)).
  
  induction 1; intuition; simpl in *.
  repeat rewrite ratMult_0_l.
  rewrite <- ratAdd_0_l.
  rewrite ratMult_0_r.
  intuition.
  
  destruct (eqd a a0); subst.
  unfold indicator.
  rewrite H.
  simpl.
  repeat rewrite ratMult_0_l.
  repeat rewrite ratMult_1_l.
  rewrite <- ratAdd_0_r.
  intuition.
  rewrite <- ratAdd_0_l.
  unfold indicator.
  rewrite H.
  simpl.
  repeat rewrite ratMult_0_l.
  rewrite ratMult_0_r.
  intuition.
  
  destruct (eqd a a0); subst.
  unfold indicator.
  rewrite H.
  repeat rewrite ratMult_0_l.
  intuition.
  rewrite <- ratAdd_0_l.
  unfold indicator.
  rewrite H.
  simpl.
  unfold sumList; simpl.
  rewrite ratMult_0_r.
  rewrite ratMult_0_l.
  rewrite ratMult_0_r.
  intuition.
  
  rewrite IHdatRepeat.
  destruct (eqd a a0); subst.
  unfold indicator.
  rewrite H0.
  repeat rewrite ratMult_0_l.
  intuition.
  repeat rewrite <- ratAdd_0_l.
  eapply ratMult_eqRat_compat; intuition.
  unfold indicator.
  rewrite H0.
  simpl.
  rewrite ratMult_1_l.
  
  rewrite <- sumList_factor_constant_l.
  
  rewrite sumList_series_incr.
  
  2:{
    intuition.
    assert (computeEmptySpace t P * expRat (computeEmptySpace t P) n1 == expRat (computeEmptySpace t P) (S n1)).
    simpl.
    intuition.
    eauto.
  }
  
  rewrite sumList_series_split_first.
  simpl.
  rewrite ratMult_distrib_r.
  rewrite ratMult_1_l.
  intuition.
 
  rewrite IHdatRepeat1.
  rewrite IHdatRepeat2.
  
  remember (sumList (getNats 0 n) (expRat (computeEmptySpace t3 P))) as v1.
  remember (lowDistApproxFromTree eqd t1 a) as v2.
  remember (computeEmptySpace t1 P) as v3.
  remember (indicator P a) as v4.
  remember (lowDistApproxFromTree eqd t3 a) as v5.
  remember (lowDistApproxFromTree eqd t2 a) as v6.
  remember (computeEmptySpace t2 P) as v7.
  
  rewrite ratMult_assoc.
  rewrite (ratMult_assoc v4 (v6 + v7 * v1 * v5) (1 / 2)).
  rewrite <- ratMult_distrib.
  eapply ratMult_eqRat_compat; intuition.
  repeat rewrite ratMult_distrib_r.
  repeat rewrite <- ratAdd_assoc.
  eapply ratAdd_eqRat_compat.
  repeat rewrite ratAdd_assoc.
  eapply ratAdd_eqRat_compat; intuition.
  rewrite ratAdd_comm.
  eapply ratAdd_eqRat_compat.
  intuition.
  rewrite ratMult_comm.
  repeat rewrite <- ratMult_assoc.
  intuition.
  rewrite ratMult_comm.
  repeat rewrite <- ratMult_assoc.
  intuition.
  
Qed.

Lemma datRepeat_func_eq : forall n (A : Set)(t1 t2 : DistApproxTree A) f P (P' : DistApproxTree A -> Prop),
  datRepeat f P n t1 t2 ->
  (forall t, f t -> P' t) ->
  datRepeat P' P n t1 t2.
  
  induction 1; intuition; simpl in *.
  econstructor.
  econstructor.
  trivial.
  econstructor.
  trivial.
  econstructor.
  eapply H2.
  eauto.
  trivial.
  trivial.
  econstructor; trivial.
Qed.

Lemma repeat_low_tree_approx_same_inv
  : forall (A : Set) (eqd : eq_dec A)(c : Comp A)(P : A -> bool) (n : nat) (a : A) (t : DistApproxTree A) (r : Rat),
    well_formed_comp c ->
    (exists a, In a (filter P (getSupport c))) ->
    lowDistApprox_repeat c P a n r ->
    dat_correct_repeat2 c P n t -> 
    n > 0 ->
    r == lowDistApproxFromTree eqd t a.
  
  intuition.
  
  destruct H2. 
  intuition.
  unfold lowDistApprox_repeat, ratMult_rel, expRat_rel, indicator_rel in *.
  unfold dat_correct in *.
  symmetry.

  edestruct (sumList_rel_left_total 
    (fun (i : nat) (r : Rat) =>
           forall r1'1 : Rat,
           sumList_rel (fun a : A => lowDistApprox c a n)
             (filter (fun a : A => negb (P a)) (getSupport c)) r1'1 ->
           r == expRat r1'1 i)
    (getNats O (S n))). 
  intuition.
  
  edestruct (sumList_rel_left_total (fun a : A => lowDistApprox c a n) (filter (fun a : A => negb (P a)) (getSupport c))).
  intuition.
  eapply lowDistApprox_left_total.
  trivial.
  trivial.

  exists (expRat x0 a0).
  intuition.
  eapply expRat_eqRat_compat.
  eapply sumList_rel_func; eauto.
  intuition.
  eapply lowDistApprox_func; eauto.

  edestruct lowDistApprox_left_total; eauto.
  rewrite (H1 (indicator P a * x0) x1); eauto.

  edestruct (sumList_rel_left_total (fun a : A => lowDistApprox c a n)
            (filter (fun a : A => negb (P a)) (getSupport c))).
  intuition.
  eapply lowDistApprox_left_total; eauto.

  assert (sumList_rel (fun a : A => lowDistApprox c a n)
         (filter (fun a : A => negb (P a)) (getTreeSupport eqd x)) x2).
  eapply sumList_rel_ls_intersect.
  eauto.
  eapply filter_NoDup.
  eapply getSupport_NoDup.
  eapply filter_NoDup.
  eapply getUnique_NoDup.
  trivial.
  intuition.
  eapply lowDistApprox_func; eauto.
  intuition.

  eapply lowDistApprox_val_eq.
  eapply low_tree_approx_same.
  trivial.
  eapply H4.
  eapply lowDistApproxFromTree_eq_0.
  intuition.
  eapply H9.
  eapply filter_In; intuition; eauto.
  apply filter_In in H8.
  intuition.
  
  intuition.
  exfalso.
  eapply H9.
  eapply filter_In; intuition.
  eapply getTreeSupport_in.
  eauto.
  eapply filter_In.
  eauto.
  apply filter_In in H8.
  intuition.
  
  assert (sumList_rel (fun i => expRat_rel (eqRat x2) i) (getNats O (S n)) x0).
  eapply sumList_rel_body_eq.
  eapply H2.
  intuition.
  unfold expRat_rel in *.
  intuition.
  rewrite H9.
  eapply expRat_eqRat_compat.
  eapply H10.
  trivial.
  intuition.
  trivial.
  clear H2.
  clear H7.

  assert (sumList (getNats O (S n)) (expRat x2) == x0).
  rewrite sumList_rel_func.
  eapply eqRat_refl.
  eapply sumList_rel_sumList_eqRat.
  eapply sumList_rel_body_eq.
  eapply H9.
  intuition.
  unfold expRat_rel in *.
  rewrite H2.
  eapply eqRat_refl.
  intuition.
  intuition.
  intuition.
  intuition.
  rewrite <- H2.
  rewrite H7.
  intuition.
  rewrite <- H2.
  clear H9.
  clear H2.
  
  assert (x1 == (lowDistApproxFromTree eqd x a)).
  eapply lowDistApprox_func.
  eauto.
  eauto.
  eapply low_tree_approx_same; eauto.
  rewrite H2.

  
  assert (x2 == (computeEmptySpace x P)).
  assert (sumList 
         (filter (fun a : A => negb (P a)) (getTreeSupport eqd x)) 
         (fun a : A => lowDistApproxFromTree eqd x a) == x2).
  eapply sumList_rel_func.
  eapply sumList_rel_sumList_eqRat.
  eapply sumList_rel_body_eq.
  eapply H8.
  intuition.
  eapply lowDistApprox_func.
  eauto.
  eapply low_tree_approx_same.
  trivial.
  eauto.
  trivial.
  intuition.
  trivial.
  intuition.
  rewrite <- H7.
  rewrite H9.
  intuition.
  rewrite <- H7.
  eauto. 

  eapply computeEmptySpace_correct; eauto.

  eapply eqRat_trans.
  2:{
    eapply ratMult_eqRat_compat.
    eapply ratMult_eqRat_compat.
    eapply eqRat_refl.
    eapply sumList_body_eq.
    intuition.
    eapply expRat_eqRat_compat.
    symmetry.
    eapply H7.
    eapply eqRat_refl.
  }

  eapply eqRat_trans.
  eapply repeat_low_tree_approx_same_tree_inv; eauto.

  eapply datRepeat_func_eq.
  eauto.
  intuition.
  eapply dat_correct_func; eauto.

  rewrite (ratMult_assoc (indicator P a) (sumList (getNats 0 (S n)) (fun a0 : nat => expRat (computeEmptySpace x P) a0))).
  eapply ratMult_eqRat_compat.
  intuition.
  rewrite <- sumList_factor_constant_l.
  rewrite sumList_series_incr.
  2:{
    intuition.
    assert (computeEmptySpace x P * expRat (computeEmptySpace x P) n0 == expRat (computeEmptySpace x P) (S n0)).
    simpl.
    intuition.
    eapply H9.
  }
  remember (lowDistApproxFromTree eqd x a) as v.
  rewrite <- (ratMult_1_l v) at 1.
  rewrite <- ratMult_distrib_r.
  assert ((expRat (computeEmptySpace x P)) O = 1).
  simpl.
  intuition.
  rewrite <- H9 at 1.
  rewrite <- sumList_series_split_first.
  simpl.
  eapply eqRat_refl.

  unfold indicator.
  intuition.
  rewrite H7.
  rewrite H10.
  repeat rewrite ratMult_1_l.
  eapply sumList_rel_func; eauto.
  intuition.
  edestruct (sumList_rel_left_total (fun a : A => lowDistApprox c a n) (filter (fun a : A => negb (P a)) (getSupport c))).
  intuition.
  eapply lowDistApprox_left_total; eauto.
  rewrite H9; eauto.
  rewrite H11; eauto.
  intuition.

  rewrite H7.
  rewrite H10.
  repeat rewrite ratMult_0_l.
  intuition.

Qed.

Lemma dat_better_antisymm : forall (A : Set)(t1 t2 : DistApproxTree A),
  dat_better t1 t2 ->
  dat_better t2 t1 ->
  t1 = t2.
  
  induction 1; inversion 1; intuition; subst; trivial.
Qed.


Lemma dat_correct_h_repeat_app : forall (A : Set) t (c : Comp A)(P : A -> bool) n ls1 ls2 a,
  evalDet_steps (cs_more c ls1) (cs_done a nil) ->
  P a = false ->
  dat_correct_h (Repeat c P) (ls1 ++ ls2) n t ->
  dat_correct_h (Repeat c P) ls2 n t.

  induction t; intuition.
  inversion H1; clear H1; subst.
  inversion H4; clear H4; subst.
  inversion H2; clear H2; subst.
  simpl in *.
  apply evalDet_steps_bind_done_inv in H6.
  destruct H6. destruct H1.
  intuition.
  assert (evalDet_steps (cs_more c (ls1 ++ ls2)) (cs_done a (nil ++ ls2))).
  eapply evalDet_steps_app_eq.
  eauto.
  simpl in *.
  specialize (evalDet_steps_done_func H1 H2); intuition; subst.
  clear H1.
  econstructor.
  econstructor.
  rewrite H0 in H3.
  eauto.
 
  econstructor.
  intuition.
  inversion H1; clear H1; subst.
  eapply H4.
  econstructor.
  econstructor.
  eauto.
  simpl.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eapply evalDet_steps_app_eq.
  eauto.
  rewrite H0.
  simpl.
  eauto.
  
  inversion H1; clear H1; subst.
  econstructor.
  intuition.
  inversion H1; clear H1; subst.
  eapply H4.
  econstructor.
  econstructor.
  eauto.
  simpl.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eapply evalDet_steps_app_eq.
  eauto.
  rewrite H0.
  simpl.
  eauto.
  eapply IHt1.
  eauto.
  trivial.
  rewrite app_assoc.
  trivial.
  eapply IHt2.
  eauto.
  trivial.
  rewrite app_assoc.
  trivial.

Qed.


Inductive datRepeat_depth (A : Set)(f : nat -> DistApproxTree A -> Prop)(P : A -> bool) : nat -> nat -> DistApproxTree A -> DistApproxTree A -> Prop :=
  | datRepeat_depth_leaf_None : forall n depth,
    datRepeat_depth f P n depth (dat_leaf None) (dat_leaf None)
  | datRepeat_depth_leaf_Some_yes : forall a n depth,
    P a = true ->
    datRepeat_depth f P n depth (dat_leaf (Some a)) (dat_leaf (Some a))
  | datRepeat_depth_leaf_Some_no : forall a depth,
    P a = false ->
    datRepeat_depth f P O depth (dat_leaf (Some a)) (dat_leaf None)
  | datRepeat_depth_leaf_Some_repeat : forall a t t' n depth,
    P a = false ->
    f depth t ->
    datRepeat_depth f P n depth t t' ->
    datRepeat_depth f P (S n) depth (dat_leaf (Some a)) t'
  | datRepeat_depth_internal : forall n depth t1 t2 t1' t2',
    datRepeat_depth f P n depth t1 t1' ->
    datRepeat_depth f P n depth t2 t2' ->
    datRepeat_depth f P n (S depth) (dat_internal t1 t2) (dat_internal t1' t2').

Definition dat_correct_repeat(A : Set) (c : Comp A)(P : A -> bool)(n : nat)(t : DistApproxTree A) :=
exists t1 : DistApproxTree A,
  dat_correct c n t1 /\
  datRepeat_depth (dat_correct c) P n n t1 t.

Lemma datRepeat_depth_0 : forall n2 n1 (A : Set)(f : nat -> DistApproxTree A -> Prop) P t1 t2,
  datRepeat_depth f P n1 O t1 t2 ->
  n2 >= n1 ->
  f O (dat_leaf None) ->
  datRepeat_depth f P n2 O t1 t2.
  
  induction n2; intuition; subst.
  
  inversion H; clear H; subst.
  econstructor.
  econstructor.
  trivial.
  econstructor.
  trivial.
  trivial.
  
  omega.
  
  inversion H; clear H; subst.
  econstructor.
  econstructor; trivial.
  econstructor.
  trivial.
  eauto.
  econstructor.
  
  econstructor; eauto.
  eapply IHn2; eauto.
  omega.
Qed.

Lemma dat_correct_repeat_same_h : forall depth repeats (A : Set)(c : Comp A) P ls t a t1,
  dat_correct_h (Repeat c P) ls depth t ->
  well_formed_comp c ->
  In a (filter P (getSupport c)) ->
  (forall a' n' ls', 
    evalDet_steps (cs_more c (firstn n' ls)) (cs_done a' ls') -> 
    ls' = nil)  -> 
  dat_correct_h c ls depth t1 ->  
  repeats >= depth ->
  datRepeat_depth (dat_correct_h c nil) P repeats depth t1 t.

  induction depth; intuition.
  
  inversion H; clear H; subst.
  inversion H5; clear H5; subst.
  inversion H6; clear H6; subst.
  simpl in *.
  apply evalDet_steps_bind_done_inv in H9.
  destruct H9.
  destruct H.
  intuition.
  inversion H3; clear H3; subst.
  inversion H; clear H; subst.
  case_eq (P x); intuition;
  rewrite H in H6.
  inversion H6; clear H6; subst.
  simpl in *.
  inversion H11; clear H11; subst.
  assert (a1 = a0 /\ s'0 = s').
  eapply evalDet_steps_done_func; eauto.
  intuition.
  subst.
  econstructor.
  rewrite H.
  trivial.
  assert (x0 = nil).
  eapply H2.
  rewrite firstn_eq_all_gen; eauto.
  subst.
  inversion H6; clear H6; subst.
  simpl in *.
  apply evalDet_steps_bind_done_inv in H11.
  destruct H11.
  destruct H3.
  intuition.
  assert (x1 = nil).
  eapply evalDet_nil.
  eauto.
  subst.
  assert (evalDet_steps (cs_more c (nil ++ ls)) (cs_done x0 (nil ++ ls))).
  eapply evalDet_steps_app_eq.
  trivial.
  simpl in *.
  assert (ls = nil).
  eapply H2.
  rewrite firstn_eq_all_gen; eauto.
  subst.
  assert (a = x).
  eapply evalDet_steps_nil_eq; eauto.
  eapply filter_In; eauto.
  subst.
  assert (P x = true).
  eapply filter_In; eauto.
  congruence.
  exfalso.
  eapply H.
  econstructor.
  eauto.

  inversion H3; clear H3; subst.
  inversion H; clear H; subst.
  case_eq (P a0); intuition.
  exfalso.
  eapply H5.
  econstructor.
  econstructor.
  eauto.
  simpl.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eauto.
  rewrite H.
  econstructor.
  eauto.
  simpl.
  econstructor.
  eapply datRepeat_depth_0.
  econstructor.
  trivial.
  trivial.
  econstructor.
  intuition.
  inversion H3; clear H3; subst.
  assert (s'0 = nil).
  eapply evalDet_nil; eauto.
  subst.
  assert (evalDet_steps (cs_more c (nil ++ ls)) (cs_done a1 (nil ++ ls))).
  eapply evalDet_steps_app_eq.
  trivial.
  simpl in *.
  assert (ls = nil).
  eapply H2.
  rewrite firstn_eq_all_gen; eauto.
  subst.
  assert (a0 = a1 /\ s' = nil).
  eapply evalDet_steps_done_func; eauto.
  intuition. subst.
  assert (a = a1).
  eapply evalDet_steps_nil_eq; eauto.
  eapply filter_In; eauto.
  subst.
  assert (P a1 = true).
  eapply filter_In; eauto.
  congruence.

  econstructor.

  inversion H; clear H; subst.
  inversion H5; clear H5; subst.
  inversion H6; clear H6; subst.
  simpl in *.
  apply evalDet_steps_bind_done_inv in H9.
  destruct H9.
  destruct H.
  intuition.

  inversion H3; clear H3; subst.
  inversion H; clear H; subst.
  assert (x = a1 /\ x0 = s'0).
  eapply evalDet_steps_done_func; eauto.
  intuition; subst.
  assert (s'0 = nil).
  eapply H2.
  rewrite firstn_eq_all_gen.
  eauto.
  eauto.
  subst.
  case_eq (P a1); intuition.
  rewrite H in H6.
  inversion H6; clear H6; subst.
  simpl in *.
  inversion H11; clear H11; subst.
  econstructor.
  trivial.

  rewrite H in H6.
  inversion H6; clear H6; subst.
  simpl in *.
  apply evalDet_steps_bind_done_inv in H11.
  destruct H11.
  destruct H3.
  intuition.
  assert (x0 = nil).
  eapply evalDet_nil.
  eauto.
  subst.
  assert (evalDet_steps (cs_more c (nil ++ ls)) (cs_done x (nil ++ ls))).
  eapply evalDet_steps_app_eq.
  eauto.
  simpl in *.
  assert (ls = nil).
  eapply H2.
  rewrite firstn_eq_all_gen;
  eauto.
  subst.
  assert (a = a1).
  eapply evalDet_steps_nil_eq.
  eauto.
  eapply filter_In; eauto.
  subst.
  assert (P a1 = true).
  eapply filter_In; eauto.
  congruence.

  exfalso.
  eapply H7.
  econstructor.
  eauto.

  edestruct (dat_exists_h depth (true::nil)); eauto.
  edestruct (dat_exists_h depth (false::nil)); eauto.
  inversion H3; clear H3; subst.
  inversion H9; clear H9; subst.
  case_eq (P a0); intuition.
  exfalso.
  eapply H6.
  econstructor.
  econstructor.
  eauto.
  simpl.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eauto.
  rewrite H3.
  econstructor.
  eauto.
  simpl.
  econstructor.
  
  destruct repeats.
  omega.

  eapply datRepeat_depth_leaf_Some_repeat.
  trivial.
  eapply dat_correct_h_internal; simpl.
  intuition.
  inversion H9; clear H9; subst.
  assert (s'0 = nil).
  eapply evalDet_nil.
  eauto.
  subst.
  assert (evalDet_steps (cs_more c (nil ++ ls)) (cs_done a1 (nil ++ ls))).
  eapply evalDet_steps_app_eq.
  trivial.
  simpl in *.
  assert (ls = nil).
  eapply H2.
  rewrite firstn_eq_all_gen;
    eauto.
  subst.
  assert (a = a0).
  eapply evalDet_steps_nil_eq.
  eauto.
  eapply filter_In; eauto.
  subst.
  assert (P a0 = true).
  eapply filter_In; eauto.
  congruence.

  eauto.
  eauto.
  assert (s' = nil).
  eapply H2.
  rewrite firstn_eq_all_gen; eauto.
  subst.
  eapply datRepeat_depth_internal.

  eapply IHdepth.
  eapply dat_correct_h_repeat_app.
  eauto.
  trivial.
  eauto.
  trivial.
  eauto.
  intuition.
  destruct n'; simpl in *.
  eapply evalDet_nil; eauto.
  edestruct (@evalDet_dec _ c nil); eauto.
  destruct H11.
  inversion H11; clear H11; subst.
  assert (s' = nil).
  eapply evalDet_nil.
  eauto.
  subst.
  assert (evalDet_steps (cs_more c (nil ++ ls)) (cs_done x1 (nil ++ ls))).
  eapply evalDet_steps_app_eq.
  trivial.
  simpl in *.
  assert (ls = nil).
  eapply H2.
  rewrite firstn_eq_all_gen; eauto.
  subst.
  assert (a = a0).
  eapply evalDet_steps_nil_eq.
  eauto.
  eapply filter_In; eauto.
  subst.
  assert (P a0 = true).
  eapply filter_In; eauto.
  congruence.
  rewrite firstn_nil in H9.
  eapply evalDet_app_nil;
  eauto.
  trivial.
  omega.

  eapply IHdepth.
  eapply dat_correct_h_repeat_app.
  eauto.
  trivial.
  eauto.
  trivial.
  eauto.
  intuition.
  destruct n'; simpl in *.
  eapply evalDet_nil; eauto.
  edestruct (@evalDet_dec _ c nil); eauto.
  destruct H11.
  inversion H11; clear H11; subst.
  assert (s' = nil).
  eapply evalDet_nil.
  eauto.
  subst.
  assert (evalDet_steps (cs_more c (nil ++ ls)) (cs_done x1 (nil ++ ls))).
  eapply evalDet_steps_app_eq.
  trivial.
  simpl in *.
  assert (ls = nil).
  eapply H2.
  rewrite firstn_eq_all_gen; eauto.
  subst.
  assert (a = a0).
  eapply evalDet_steps_nil_eq.
  eauto.
  eapply filter_In; eauto.
  subst.
  assert (P a0 = true).
  eapply filter_In; eauto.
  congruence.
  rewrite firstn_nil in H9.
  eapply evalDet_app_nil;
  eauto.
  trivial.
  omega.

  eapply datRepeat_depth_internal.

  eapply IHdepth;
  eauto.
  intuition.
  edestruct evalDet_steps_dec; eauto.
  destruct H9.
  destruct H9.
  exfalso.
  eapply H10.
  econstructor.
  eauto.
  eapply evalDet_app_nil.
  eauto.
  econstructor.
  eauto.
  destruct (ge_dec n' (length (ls ++ true :: nil))).
  rewrite firstn_ge_all in H3.
  eauto.
  trivial.
  apply not_ge in n.
  exfalso.
  assert (n' <= length ls)%nat.
  rewrite app_length in n.
  simpl in *.
  omega. 
  rewrite firstn_app in H3.
  assert (ls = firstn n' ls ++ skipn n' ls).
  symmetry.
  eapply firstn_skipn.
  assert (evalDet_steps (cs_more c ((firstn n' ls) ++ (skipn n' ls))) (cs_done a' (ls' ++ (skipn n' ls)))).
  eapply evalDet_steps_app_eq.
  trivial.
  specialize (H10 a').
  eapply H10.
  eapply (@evalDet_done _ _ _ a' (ls' ++ skipn n' ls)).
  rewrite H14 at 1.
  eapply H15.
  trivial.
  omega.

  eapply IHdepth;
  eauto.
  intuition.
  edestruct evalDet_steps_dec; eauto.
  destruct H9.
  destruct H9.
  exfalso.
  eapply H10.
  econstructor.
  eauto.
  eapply evalDet_app_nil.
  eauto.
  econstructor.
  eapply H9.
  destruct (ge_dec n' (length (ls ++ false :: nil))).
  rewrite firstn_ge_all in H3.
  eauto.
  trivial.
  apply not_ge in n.
  exfalso.
  assert (n' <= length ls)%nat.
  rewrite app_length in n.
  simpl in *.
  omega. 
  rewrite firstn_app in H3.
  assert (ls = firstn n' ls ++ skipn n' ls).
  symmetry.
  eapply firstn_skipn.
  assert (evalDet_steps (cs_more c ((firstn n' ls) ++ (skipn n' ls))) (cs_done a' (ls' ++ (skipn n' ls)))).
  eapply evalDet_steps_app_eq.
  trivial.
  specialize (H10 a').
  eapply H10.
  eapply (@evalDet_done _ _ _ a' (ls' ++ skipn n' ls)).
  rewrite H14 at 1.
  eapply H15.
  trivial.
  omega.
 Qed.


Lemma dat_correct_repeat_same:
  forall n (A : Set) (t : DistApproxTree A) (c : Comp A) (P : A -> bool),
  well_formed_comp c ->
  (exists a, In a (filter P (getSupport c))) ->
  dat_correct (Repeat c P) n t -> 
  dat_correct_repeat c P n t.

  intuition.
  edestruct (dat_exists); eauto.
  econstructor.
  intuition.
  eauto.
  destruct H0.
  eapply dat_correct_repeat_same_h; eauto.

  intuition.
  rewrite firstn_nil in H3.
  eapply evalDet_nil.
  eauto.

Qed.

Lemma datRepeat_depth_better: forall (n2 : nat) (A : Set) (t2 t1 t1' : DistApproxTree A)(rel : nat -> DistApproxTree A -> Prop) reps depth (P : A -> bool),
  datRepeat_depth rel P reps depth t1 t1' ->
  forall n1 (t2' : DistApproxTree A),
    reps >= n2 ->
    datRepeat (rel n1) P n2 t2 t2' ->
    dat_better t1 t2 ->
    depth >= n1 * n2 + datDepth t2 -> 
    (forall (n1 n2: nat) (t3 t4 : DistApproxTree A),
      rel n1 t3 -> rel n2 t4 -> n1 >= n2 -> dat_better t3 t4) ->
    (forall a, rel 0%nat (dat_leaf (Some a)) -> P a = true) ->
    (forall n t, rel n t -> datDepth t <= n)%nat ->
    dat_better t1' t2'.

  induction n2; induction t2; intuition.
  inversion H2; clear H2; subst.
  inversion H1; clear H1; subst.
  econstructor.
  inversion H1; clear H1; subst.
  inversion H; clear H; subst.
  econstructor.
  congruence.
  congruence.
  econstructor.

  inversion H2; clear H2; subst.
  inversion H1; clear H1; subst.
  inversion H; clear H; subst.
  simpl in *.
  rewrite mult_0_r in *.
  simpl in *.
  assert (depth0  >= (max (datDepth t2_1) (datDepth t2_2))).
  omega.

  econstructor.
  eapply IHt2_1.
  eauto.
  omega.
  eauto.
  eauto.
  rewrite mult_0_r; simpl. 
  eapply Max.max_lub_l.
  eauto.
  trivial.
  trivial.
  trivial.
  trivial.

  eapply IHt2_2.
  eauto.
  omega.
  eauto.
  trivial.
  rewrite mult_0_r; simpl. 
  eapply Max.max_lub_r.
  eauto.
  trivial.
  trivial.
  trivial.
  trivial.

  inversion H2; clear H2; subst.
  inversion H1; clear H1; subst.
  econstructor.
  inversion H1; clear H1; subst.
  inversion H; clear H; subst.
  econstructor.
  congruence.
  congruence.

  inversion H; clear H; subst.
  congruence.
  omega.
  
  rewrite mult_comm in H3.
  simpl in *.

  eapply IHn2.
  eauto.
  omega.
  eauto.
  eapply H4; eauto.
  remember (n2 * n1)%nat as x.
  omega.

  eapply le_trans.
  2:{
    eapply H3.
  }
  rewrite plus_0_r.
  rewrite plus_comm.
  eapply plus_le_compat.
  eauto.
  rewrite mult_comm.
  trivial.
  trivial.
  trivial.
  trivial.

  inversion H2; clear H2; subst.
  inversion H1; clear H1; subst.
  inversion H; clear H; subst.
  simpl in *.
  econstructor.
  eapply IHt2_1.
  eauto.
  trivial.
  eauto.
  trivial.
  eapply le_trans.
  eapply plus_le_compat.
  eapply le_refl.
  eapply (Max.max_lub_l (datDepth t2_1) (datDepth t2_2)).
  eapply le_refl.
  omega.
  trivial.
  trivial.
  trivial.
  
  eapply IHt2_2.
  eauto.
  trivial.
  eauto.
  trivial.
  eapply le_trans.
  eapply plus_le_compat.
  eapply le_refl.
  eapply (Max.max_lub_r (datDepth t2_1) (datDepth t2_2)).
  eapply le_refl.
  omega.
  trivial.
  trivial.
  trivial.
Qed.

Lemma dat_better_repeat_sqrt : forall (A : Set) (c : Comp A)(P : A -> bool)(n : nat) (t1 t2 : DistApproxTree A),
  (exists a, In a (filter P (getSupport c))) ->
  dat_correct_repeat c P n t1 ->
  dat_correct_repeat2 c P (Nat.sqrt (div2 n)) t2 -> 
  well_formed_comp c ->
  dat_better t1 t2.

  intuition.
  unfold dat_correct_repeat, dat_correct_repeat2 in *.
  destruct H0.
  destruct H1.
  intuition.
  
  eapply datRepeat_depth_better.
  eauto.
  2:{
    eauto.
  }

  eapply sqrt_le_lin_gen.
  eapply div2_le.
  eapply dat_correct_dat_better.
  eauto.
  eauto.
  eapply sqrt_le_lin_gen.
  eapply div2_le.
  
  eapply le_trans.
  eapply plus_le_compat.
  eapply Nat.sqrt_spec.
  omega.
  eapply le_trans.
  eapply datCorrect_datDepth.
  eauto.
  eapply Nat.sqrt_le_lin.
  eapply div2_ge_double.

  intuition.
  eapply dat_correct_dat_better; eauto.

  intuition.
  inversion H1; clear H1; subst.
  inversion H8; clear H8; subst.
  destruct H.
  assert (x1 = a).
  eapply evalDet_steps_nil_eq; eauto.
  eapply filter_In; eauto.
  subst.
  eapply filter_In; eauto.

  intuition.
  eapply datCorrect_datDepth; eauto.
  
Qed.


Lemma lowDistApprox_repeat_sqrt_le : forall n (A : Set)(c : Comp A)(P : A -> bool) a v1 v2,
  well_formed_comp c ->
  (exists a, In a (filter P (getSupport c))) ->
  lowDistApprox (Repeat c P) a n v1 ->
  lowDistApprox_repeat c P a (Nat.sqrt (div2 n)) v2 -> 
  n > 1 ->
  v2 <= v1.

  intuition.
  
  edestruct (dat_exists_repeat2).
  eauto.
  rewrite repeat_low_tree_approx_same_inv; eauto.
  destruct H0.
  edestruct dat_exists.
  eapply well_formed_Repeat.
  eapply comp_eq_dec; eauto.
  eauto.
  eauto.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    eapply low_tree_approx_same_inv.
    eapply H0.
    eapply H1.
  }
  
  eapply lowDistApprox_dat_better_le.
  eapply dat_correct_repeat_same in H0.
  eapply dat_better_repeat_sqrt; eauto.
  eauto.
  econstructor; eauto.

  destruct n.
  omega.
  destruct n.
  omega.
  simpl.
  
  eapply lt_le_trans.
  econstructor.
  eapply le_trans.
  rewrite <- Nat.sqrt_1.
  eauto.
  eapply Nat.sqrt_le_mono.
  omega.

  Grab Existential Variables.
  eapply comp_eq_dec; eauto.
  
Qed.

Lemma datRepeat_better_depth: forall (A : Set) n2 (t2 t1 t1' : DistApproxTree A)(rel : nat -> DistApproxTree A -> Prop) reps depth (P : A -> bool),
  forall n1 (t2' : DistApproxTree A),
    datRepeat (rel n1) P n2 t2 t2' ->
    datRepeat_depth rel P reps depth t1 t1' ->
    dat_better t2 t1 ->
    n1 >= depth ->
    n2 >= reps ->  
    (forall (n1 n2: nat) (t3 t4 : DistApproxTree A),
      rel n1 t3 -> rel n2 t4 -> n1 >= n2 -> dat_better t3 t4) ->
    (forall a, rel 0%nat (dat_leaf (Some a)) -> P a = true) ->
    (forall n t, rel n t -> datDepth t <= n)%nat ->
    dat_better t2' t1'.

  induction n2; induction t2; intuition.
  assert (reps = O).
  omega.
  subst.
  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  econstructor.
  inversion H0; clear H0; subst.
  inversion H; clear H; subst.
  econstructor.
  congruence.
  econstructor.

  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  econstructor.
  inversion H0; clear H0; subst.
  inversion H; clear H; subst.
  econstructor.
  eapply IHt2_1; eauto; omega.
  eapply IHt2_2; eauto; omega.

  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  econstructor.
  inversion H0; clear H0; subst.
  inversion H; clear H; subst.
  econstructor.
  congruence.
  econstructor.
  inversion H; clear H; subst.
  congruence.
  eapply IHn2.
  eauto.
  eauto.
  eapply H4; eauto.
  trivial.
  omega.
  trivial.
  trivial.
  trivial.

  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  econstructor.
  inversion H; clear H; subst.
  inversion H0; clear H0; subst.
  econstructor.
  eapply IHt2_1; eauto; omega.
  eapply IHt2_2; eauto; omega.
Qed.

Lemma dat_repeat_better:
  forall (A : Set) n (c : Comp A) (P : A -> bool)
    (t1 t2 : DistApproxTree A),
    (exists a : A, In a (filter P (getSupport c))) ->
    dat_correct_repeat c P n t1 ->
    dat_correct_repeat2 c P n t2 -> 
    dat_better t2 t1.

  intuition.
  unfold dat_correct_repeat, dat_correct_repeat2 in *.
  destruct H0.
  destruct H1.
  intuition.
  
  eapply datRepeat_better_depth.
  eauto.
  eauto.
  eapply dat_correct_dat_better.
  eauto.
  eauto.
  omega.
  omega.
  omega.
  
  intuition.
  eapply dat_correct_dat_better; eauto.

  intuition.
  inversion H1; clear H1; subst.
  inversion H7; clear H7; subst.
  destruct H.
  assert (x1 = a).
  eapply evalDet_steps_nil_eq; eauto.
  eapply filter_In; eauto.
  subst.
  eapply filter_In; eauto.
  
  intuition.
  destruct H.
  eapply datCorrect_datDepth.
  eauto.
Qed.

Lemma lowDistApprox_le_repeat:
  forall (n : nat) (A : Set) (c : Comp A) (P : A -> bool)(a : A) (v1 v2 : Rat),
    well_formed_comp c ->
    (exists a0 : A, In a0 (filter P (getSupport c))) ->
    lowDistApprox (Repeat c P) a n v1 ->
    lowDistApprox_repeat c P a n v2 -> 
    n > O ->
    v1 <= v2.

  intuition.
  edestruct dat_exists_repeat2.
  eauto.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eapply (repeat_low_tree_approx_same_inv); eauto.
  }

  destruct H0.
  edestruct dat_exists.
  eapply well_formed_Repeat; eauto.
  eapply comp_eq_dec; eauto.

  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  symmetry.
  eapply low_tree_approx_same_inv.
  eauto.
  eauto.
  
  apply lowDistApprox_dat_better_le.

  eapply dat_repeat_better.
  econstructor; eauto.
  eapply dat_correct_repeat_same; eauto.
  trivial.
  
  Grab Existential Variables.
  eapply comp_eq_dec; eauto.
Qed.

Lemma lowDistApprox_Rnd_lt : forall n1 n2 a r,
  lowDistApprox (Rnd n1) a n2 r ->
  n2 < n1 ->
  r == 0.
  
  intuition.
  unfold lowDistApprox in *.
  destruct H.
  destruct H.
  intuition.
  rewrite H3.
  assert (x0 = O).
  eapply pred_count_func.
  eauto.
  eapply pred_count_eq_none; intuition.
  subst.
  assert (x = (listRepeat (@ca_eof (Bvector n1)) (length (getAllBlists n2)))).
  eapply rel_map_func.
  eauto.
  eapply rel_map_listRepeat.
  intuition.
  econstructor.
  econstructor.
  eauto.
  simpl.
  
  rewrite shiftOut_lt.
  econstructor.
  erewrite getAllBlists_In_length.
  eauto.
  trivial.
  
  intuition.
  eapply evalDet_func; eauto.
  subst.
  apply in_listRepeat_inv in H2.
  discriminate.
  
  subst.
  eapply rat_num_0.
Qed.

Lemma evalDet_step_done_support_singleton : forall (A : Set)(c : Comp A) a s,
  evalDet_step c nil = (cs_done a s) ->
  getSupport c = a :: nil.
  
  induction c; intuition; simpl in *.
  inversion H; clear H; subst.
  trivial.
  
  case_eq (evalDet_step c nil); intuition;
    rewrite H1 in H0;
      try discriminate.
  
  destruct n; simpl.
  discriminate.
  discriminate.
  
  discriminate.
  
Qed.

Lemma lowDistApprox_low : forall (A : Set)(c : Comp A),
  well_formed_comp c -> 
  forall n a r, 
  lowDistApprox c a n r ->
  r <= evalDist c a.

  induction 1; intuition; simpl in *.
  
  rewrite lowDistApprox_Ret_inv; eauto.
  eapply leRat_refl.

  edestruct (lowDistApprox_bind_left_total); eauto.
  eapply leRat_trans.
  eapply lowDistApprox_le_bind;
  eauto.
  inversion H3; clear H3; subst.
  eapply sumList_rel_le.
  eauto.
  eapply sumList_rel_sumList.
  intuition.
  edestruct lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  eauto.
  edestruct lowDistApprox_left_total.
  eapply bind_eq_dec; eauto.
  eauto.
  rewrite H5; eauto.
  rewrite <- H6; eauto.
  eapply ratMult_leRat_compat; eauto.

  destruct (le_dec n n0).
  assert (exists n1, n0 = n + n1)%nat.
  exists (minus n0 n).
  omega.
  destruct H0.
  subst.
  rewrite lowDistApprox_Rnd; eauto.
  eapply leRat_terms; intuition.

  rewrite lowDistApprox_Rnd_lt.
  eapply rat0_le_all.
  eauto.
  omega.

  destruct n. 
  destruct H1.
  destruct H1.
  intuition.
  simpl in *.
  inversion H2; clear H2; subst.
  inversion H6; clear H6; subst.
  inversion H8; clear H8; subst.
  inversion H2; clear H2; subst.
  apply evalDet_steps_bind_done_inv in H8.
  destruct H8.
  destruct H2.
  intuition.
  apply filter_In in H0.
  intuition.
  assert (b = x).
  eapply evalDet_steps_nil_eq; eauto.
  subst.
  rewrite H6 in H5.
  inversion H5; clear H5; subst.
  simpl in *.
  inversion H10; clear H10; subst.
  inversion H1; clear H1; subst.
  inversion H9; clear H9; subst.
  inversion H7; clear H7; subst.
  rewrite H4.
  unfold indicator.
  rewrite H6.
  rewrite ratMult_1_l.

  erewrite evalDet_steps_done_support_singleton; eauto.
  unfold sumList; simpl.
  rewrite H6.
  simpl.

  rewrite <- ratMult_1_l.
  eapply ratMult_leRat_compat.

  rewrite <- ratInverse_1.
  eapply eqRat_impl_leRat.
  eapply ratInverse_eqRat_compat.
  eapply rat1_ne_rat0.
  rewrite <- ratAdd_0_l.
  rewrite (evalDet_steps_done_evalDist eqd); eauto.
  destruct (eqd a0 a0).
  intuition.
  congruence.
  eapply eqRat_impl_leRat.
  rewrite (evalDet_steps_done_evalDist eqd); eauto.
  destruct (eqd a0 a0).
  eapply num_dem_same_rat1.
  unfold natToPosnat, posnatToNat.
  trivial.
  congruence.
  inversion H7; clear H7; subst.
  rewrite H4.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply rat_num_0.
  eapply rat0_le_all.
  inversion H1; clear H1; subst.
  discriminate.
  inversion H6; clear H6; subst.
  rewrite H4.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply rat_num_0.
  eapply rat0_le_all.

  edestruct lowDistApprox_repeat_left_total; eauto.
  eapply leRat_trans.
  eapply lowDistApprox_le_repeat; eauto.
  omega.
  unfold lowDistApprox_repeat in *.
  unfold ratMult_rel, expRat_rel, indicator_rel in *.
  edestruct lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  eauto.

  edestruct (sumList_rel_left_total
    (fun a1 : A => lowDistApprox c a1 (S n))
       (filter (fun a1 : A => negb (P a1)) (getSupport c))).
  intuition.
  eapply lowDistApprox_left_total; eauto.

  edestruct (sumList_rel_left_total
     (fun (i : nat) (r : Rat) =>
          forall r1' : Rat,
          sumList_rel (fun a : A => lowDistApprox c a (S n))
            (filter (fun a : A => negb (P a)) (getSupport c)) r1' ->
          r == expRat r1' i) 
     (getNats 0 (S (S n)))).
  intuition.  
  econstructor.
  intuition.
  eapply expRat_eqRat_compat; eauto.
  eapply sumList_rel_func.
  eapply H4.
  trivial.
  intuition.
  eapply lowDistApprox_func; eauto.

  case_eq (P a); intuition.
  rewrite H2; eauto.
  2:{
    intuition.
    eapply ratMult_eqRat_compat.
    symmetry.
    eauto.
    eapply sumList_rel_func.
    eapply H5.
    eapply H8.
    intuition.
    rewrite H9.
    rewrite H11.
    eapply eqRat_refl.
    eauto.
    trivial.
    congruence.
  }
  eapply ratMult_leRat_compat.
  eapply ratMult_leRat_compat.
  unfold indicator.
  rewrite H6.
  intuition.

  rewrite (@sum_power_series (S (S n)) (sumList_rel (fun a : A => lowDistApprox c a (S n))
            (filter (fun a : A => negb (P a)) (getSupport c)))); eauto; try omega.
  2:{
    intuition.
    eapply sumList_rel_func; eauto.
    intuition.
    eapply lowDistApprox_func;
    eauto.
  }
 
  3:{
    unfold ratMult_rel, ratSubtract_rel, expRat_rel, ratInverse_rel.
    intuition.
    rewrite H7.
    rewrite H8.
    eapply eqRat_refl.
    intuition.
    eapply ratSubtract_eqRat_compat.
    eauto.
    eapply sumList_rel_func.
    eapply H4.
    trivial.
    intuition.
    eapply lowDistApprox_func; eauto.
    eapply eqRat_refl.
    intuition.
    eapply expRat_eqRat_compat.
    eapply sumList_rel_func.
    eapply H4.
    trivial.
    intuition.
    eapply lowDistApprox_func; eauto.
  }
  eapply leRat_trans.
  eapply ratMult_leRat_compat.
  eapply ratSubtract_le.
  eapply leRat_refl.
  
  eapply ratInverse_leRat.
  2:{
    eapply ratSubtract_leRat.
    eapply leRat_refl.
    eapply sumList_rel_le.
    eauto.
    eapply sumList_rel_sumList.
    intuition.
    rewrite <- H9.
    eapply IHwell_formed_comp.
    eauto.
  }
  intuition.
  eapply getSupport_In_evalDist.
  eapply filter_In; eauto.
  eapply sumList_0.
  rewrite <- evalDist_lossless in H7.
  rewrite sumList_filter_partition in H7.
  rewrite ratAdd_comm in H7.
  rewrite ratSubtract_ratAdd_inverse in H7.
  eapply H7.
  trivial.
  trivial.

  rewrite ratMult_1_l.
  eapply eqRat_impl_leRat.
  eapply ratInverse_eqRat_compat.
  
  intuition.
  eapply getSupport_In_evalDist.
  eapply filter_In; eauto.
  eapply sumList_0.
  rewrite <- evalDist_lossless in H7.
  rewrite sumList_filter_partition in H7.
  rewrite ratAdd_comm in H7.
  rewrite ratSubtract_ratAdd_inverse in H7.
  eapply H7.
  trivial.
  trivial.

  rewrite <- (evalDist_lossless); eauto.
  rewrite (sumList_filter_partition).
  rewrite ratAdd_comm.
  rewrite ratSubtract_ratAdd_inverse.
  intuition.
 
  intuition.

  eapply ratAdd_not_leRat.
  erewrite <- sumList_filter_partition.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply evalDist_lossless.
  eauto.
  eapply leRat_trans.
  eapply H8.
  eapply sumList_rel_le.
  eauto.
  eapply sumList_rel_sumList.
  intuition.
  rewrite <- H11.
  eapply IHwell_formed_comp.
  eauto.
  intuition.

  eapply sumList_0 in H9.
  eapply getSupport_In_evalDist; eauto.
  eapply filter_In; eauto.
  eapply filter_In.
  intuition.
  eapply filter_In; eauto.
  rewrite negb_involutive.
  eapply filter_In; eauto.
  
  eapply IHwell_formed_comp; eauto.

  rewrite H2; eauto.
  2:{
    intuition.
    congruence.
    eapply ratMult_eqRat_compat.
    symmetry.
    eauto.
    eapply sumList_rel_func.
    eapply H5.
    trivial.
    intuition.
    rewrite H9; eauto.
    rewrite H11; eauto.
    intuition.
  }
  repeat rewrite ratMult_0_l.
  eapply rat0_le_all.
Qed.


Lemma lowDistApprox_repeat_scale_limit : forall (A : Set)(c : Comp A)(P : A -> bool),
  well_formed_comp c ->
  (exists a, In a (filter P (getSupport c))) ->
  (forall a, rat_inf_limit (lowDistApprox c a) (evalDist c a)) -> 
  rat_inf_limit
     (fun n : nat =>
      sumList_rel
        (fun i : nat =>
         expRat_rel
           (sumList_rel (fun a0 : A => lowDistApprox c a0 n)
              (filter (fun a0 : A => negb (P a0)) (getSupport c))) i)
        (getNats O n))
     (ratInverse (sumList (filter P (getSupport c)) (evalDist c))).

  intuition.

  eapply rat_inf_limit_eq.
  eapply power_series_limit_2.
  eapply rat_inf_limit_summation.
  eauto.
  intuition.
  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  trivial.
  intuition.
  eapply lowDistApprox_func; eauto.

  intuition.
  destruct H0.

  assert (sumList (filter (fun a0 : A => negb (P a0)) (getSupport c)) (evalDist c) == 1).
  eapply leRat_impl_eqRat.
  eapply leRat_trans.
  
  eapply sumList_filter_le.
  rewrite evalDist_lossless.
  intuition.
  trivial.
  eapply leRat_trans.
  eapply H3.

  eapply sumList_rel_le.
  eapply H2.
  eapply sumList_rel_sumList.
  intuition.
  rewrite <- H6.
  eapply lowDistApprox_low.
  eauto.
  eauto. 
  
  rewrite <- evalDist_lossless in H4; eauto.
  rewrite (sumList_filter_partition P (getSupport c)) in H4.
 
  symmetry in H4.
  rewrite ratAdd_comm in H4.
  apply ratAdd_arg_0 in H4.
  eapply sumList_0 in H4; eauto.
  eapply getSupport_In_evalDist.
  eapply filter_In; eauto.
  trivial.

  destruct H0.
  intuition.

  eapply sumList_filter_evalDist_le_1; eauto.
    
  intuition.
  eapply sumList_rel_left_total.
  intuition.
  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  trivial.
  intuition.
  eapply sumList_rel_func; eauto.
  intuition.
  eapply lowDistApprox_func; eauto.
  
  eapply ratInverse_eqRat_compat.
  intuition.
  apply ratSubtract_0_inv in H2.
  destruct H0.
  eapply sumList_filter_evalDist_le_1; eauto.


  eapply (@eqRat_ratAdd_same_r (sumList (filter (fun a => negb (P a)) (getSupport c)) (evalDist c))).
  rewrite <- sumList_filter_partition.
  rewrite evalDist_lossless.

  rewrite ratAdd_comm.
  rewrite ratSubtract_ratAdd_inverse_2.
  intuition.
  eapply leRat_trans.
  eapply sumList_filter_le.
  rewrite evalDist_lossless.
  intuition.
  trivial.
  trivial.

Qed.

Lemma lowDistApprox_repeat_limit : forall (A : Set)(c : Comp A)(P : A -> bool) a,
  well_formed_comp c ->
  (exists b, In b (filter P (getSupport c))) ->
  (forall a, rat_inf_limit (lowDistApprox c a) (evalDist c a)) ->
  rat_inf_limit (lowDistApprox_repeat c P a) (evalDist (Repeat c P) a).

  intuition.

  unfold lowDistApprox_repeat.
  simpl.
  eapply rat_inf_limit_product; trivial.
  unfold left_total.
  intuition.
  edestruct (sumList_rel_left_total (fun a1 => lowDistApprox c a1 n)  (filter (fun a1 : A => negb (P a1)) (getSupport c))).
  intuition.
  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  trivial.
  edestruct (sumList_rel_left_total (fun i : nat =>
           expRat_rel
             (sumList_rel (fun a1 : A => lowDistApprox c a1 n)
                (filter (fun a1 : A => negb (P a1)) (getSupport c))) i)
          (getNats 0 (S n))).
  intuition.
  unfold expRat_rel.
  exists (expRat x a0).
  intuition.

  eapply expRat_eqRat_compat.

  eapply sumList_rel_func; eauto.
  intuition.
  eapply lowDistApprox_func; eauto.

  unfold ratMult_rel, indicator_rel.
  exists ((if (P a) then 1 else 0) * x0).
  intuition.
  rewrite H4.
  rewrite H7.
  repeat rewrite ratMult_1_l.
  eapply sumList_rel_func; eauto.
  intuition.
  unfold expRat_rel in *.
  edestruct (sumList_rel_left_total (fun a1 : A => lowDistApprox c a1 n)
         (filter (fun a1 : A => negb (P a1)) (getSupport c))).
  intuition.
  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  trivial.
  rewrite H6; eauto.
  rewrite H8; eauto.
  intuition.
  
  rewrite H4.
  rewrite H7.
  repeat rewrite ratMult_0_l.
  intuition.

  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  trivial.

  eapply rat_inf_limit_product.
  unfold left_total, indicator_rel.
  intuition.
  exists (if (P a) then 1 else 0).
  destruct (P a); intuition.
  
  unfold left_total.
  intuition.
  edestruct (sumList_rel_left_total (fun a0 : A => lowDistApprox c a0 n)
              (filter (fun a0 : A => negb (P a0)) (getSupport c))).
  intuition.
  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  trivial.

  eapply sumList_rel_left_total.
  intuition.
  unfold expRat_rel.
  exists (expRat x a0).
  intuition.
  eapply expRat_eqRat_compat.
  eapply sumList_rel_func; eauto.
  intuition.
  eapply lowDistApprox_func; eauto.

  unfold rat_inf_limit, inf_limit, indicator_rel. intuition.
  exists O.
  intuition;
  unfold indicator.
  rewrite H6.
  rewrite H4.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  rewrite <- ratIdentityIndiscernables.
  intuition.
  eapply rat0_le_all.
  rewrite H6.
  rewrite H4.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  rewrite <- ratIdentityIndiscernables.
  intuition.
  eapply rat0_le_all.

  (* split this up and use sum rule.  The limit of the first term is 0 *)
  eapply (@rat_inf_limit_trans _ (fun n : nat =>
    (ratAdd_rel (expRat_rel
           (sumList_rel (fun a0 : A => lowDistApprox c a0 n)
              (filter (fun a0 : A => negb (P a0)) (getSupport c))) n)
      (sumList_rel
        (fun i : nat =>
         expRat_rel
           (sumList_rel (fun a0 : A => lowDistApprox c a0 n)
              (filter (fun a0 : A => negb (P a0)) (getSupport c))) i)
        (getNats 0 n))))).

  unfold rat_inf_limit_2, inf_limit_2.
  intuition.
  exists O.
  intuition.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  rewrite <- ratIdentityIndiscernables.
  inversion H4; clear H4; subst.
  unfold ratAdd_rel in *.
  rewrite H11.
  rewrite H5; eauto.
  intuition.
  eapply rat0_le_all.


  eapply rat_inf_limit_eq.
  eapply rat_inf_limit_sum.
  unfold left_total. intuition.
  eapply expRat_rel_left_total.
  eapply sumList_rel_left_total.
  intuition.
  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  trivial.
  intuition.
  eapply sumList_rel_func; eauto.
  intuition.
  eapply lowDistApprox_func; eauto.
  
  unfold left_total. intuition.
  eapply sumList_rel_left_total.
  intuition.
  eapply expRat_rel_left_total.
  eapply sumList_rel_left_total.
  intuition.
  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  trivial.
  intuition.
  eapply sumList_rel_func; eauto.
  intuition.
  eapply lowDistApprox_func; eauto.

  eapply rat_inf_limit_exp_0.
  eapply rat_inf_limit_summation.
  eapply H1.
  intuition.
  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  trivial.
  intuition.
  eapply lowDistApprox_func; eauto.
  intuition.

  assert (sumList (filter (fun a0 : A => negb (P a0)) (getSupport c)) (evalDist c) == 1).
  eapply leRat_impl_eqRat.
  eapply leRat_trans.
  
  eapply sumList_filter_le.
  rewrite evalDist_lossless.
  intuition.
  trivial.
  eapply H2.
  clear H2.
  
  rewrite <- evalDist_lossless in H3; eauto.
  rewrite (sumList_filter_partition P (getSupport c)) in H3.
 
  destruct H0.
  symmetry in H3.
  rewrite ratAdd_comm in H3.
  apply ratAdd_arg_0 in H3.
  eapply sumList_0 in H3; eauto.
  eapply getSupport_In_evalDist.
  eapply filter_In; eauto.
  trivial.

  intuition.
  eapply sumList_rel_left_total.
  intuition.
  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  trivial.
  
  eapply lowDistApprox_repeat_scale_limit.
  trivial.
  trivial.
  trivial.
  rewrite <- ratAdd_0_l.
  intuition.

  unfold left_total. 
  intuition.
  eapply ratAdd_rel_left_total.
  eapply expRat_rel_left_total.
  eapply sumList_rel_left_total.
  intuition.
  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  trivial.
  intuition.
  eapply sumList_rel_func; eauto.
  intuition.
  eapply lowDistApprox_func; eauto.
  eapply sumList_rel_left_total.
  intuition.
  eapply expRat_rel_left_total.
  eapply sumList_rel_left_total.
  intuition.
  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  trivial.
  intuition.
  eapply sumList_rel_func; eauto.
  intuition.
  eapply lowDistApprox_func; eauto.
  intuition.

  eapply expRat_rel_func; eauto.
  intuition.
  eapply sumList_rel_func; eauto.
  intuition.
  eapply lowDistApprox_func; eauto.
  eapply sumList_rel_left_total.
  intuition.
  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; eauto.
  trivial.
  
  intuition.
  eapply sumList_rel_func; eauto.
  intuition.
  eapply expRat_rel_func; eauto.
  intuition.
  eapply sumList_rel_func; eauto.
  intuition.
  eapply lowDistApprox_func; eauto.
  eapply sumList_rel_left_total; eauto.
  intuition.
  eapply lowDistApprox_left_total; eauto.
  eapply comp_eq_dec; eauto.
Qed.

Lemma lowDistApprox_limit_repeat : forall (A : Set)(c : Comp A)(P : A -> bool) a,
  well_formed_comp c ->
  (exists a, In a (filter P (getSupport c))) ->
  (forall a', rat_inf_limit (lowDistApprox c a') (evalDist c a')) ->
  rat_inf_limit (lowDistApprox (Repeat c P) a) (evalDist (Repeat c P) a).

  intuition.
  eapply (@rat_inf_limit_squeeze (fun n => (lowDistApprox_repeat c P a (Nat.sqrt (div2 n)))) (fun n => eqRat (evalDist (Repeat c P) a))).

  eapply rat_inf_limit_mono.
  eapply lowDistApprox_repeat_limit; trivial.
  intuition.
  eapply Nat.sqrt_le_mono.

  eapply div2_le_mono.
  trivial.

  intuition.
  exists (2 * (y * y))%nat.
  rewrite div2_double.
  rewrite Nat.sqrt_square.
  trivial.

  eapply rat_inf_limit_const.
  intuition.
  intuition.
  rewrite <- H2.
  rewrite H3.
  intuition.

  intuition.
  eapply lowDistApprox_repeat_sqrt_le; eauto.
  intuition.
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    eapply H4.
  }
  eapply lowDistApprox_low.
  destruct H0.
  eapply well_formed_Repeat; eauto.
  eapply comp_eq_dec; eauto.
  eauto.
  
  eapply lowDistApprox_repeat_sqrt_div2_left_total. 

  unfold left_total; intuition.
  econstructor.
  eapply eqRat_refl.

Qed.

Theorem evalDet_evalDist_equiv : forall (A : Set)(c : Comp A),
  well_formed_comp c ->
  forall a, rat_inf_limit (lowDistApprox c a) (evalDist c a).

  induction 1; intuition.
  unfold rat_inf_limit, inf_limit in *; intuition.
  exists O.
  intuition.
  simpl.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  
  eapply (ratIdentityIndiscernables a').
  eapply lowDistApprox_Ret_inv. eauto.
  eapply rat0_le_all.
 
  eapply (@rat_inf_limit_squeeze (fun n => lowDistApprox_bind c1 c2 a (div2 n)) (lowDistApprox_bind c1 c2 a)); intuition.
  eapply rat_inf_limit_div_2.
  eapply lowDistApprox_bind_evalDist_limit; eauto.
  eapply lowDistApprox_bind_evalDist_limit; eauto.
    
  eapply lowDistApprox_bind_le_div2; eauto.
  eapply lowDistApprox_le_bind; eauto.

  eapply lowDistApprox_bind_div2_left_total; trivial.
  eapply lowDistApprox_bind_left_total; trivial.

  exists n.
  intuition.
  simpl.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply (ratIdentityIndiscernables a').
  assert (exists n'', n' = n + n'')%nat.
  exists (n' - n).
  omega.
  destruct H2.
  subst.

  rewrite lowDistApprox_Rnd.
  eapply eqRat_terms; intuition.
  eauto.
  eapply rat0_le_all.

  eapply lowDistApprox_limit_repeat.
  trivial.
  econstructor; eauto.
  trivial.

  Grab Existential Variables.
  (* todo: make a version of the squeeze theorem that doesn't have the extra nat. *)
  eapply O.
  
Qed.

Lemma evalDet_equiv_impl_lowDistApprox_equiv : 
  forall (A : Set)(c1 c2 : Comp A), 
    evalDet_equiv c1 c2 ->
    forall a n r,
      lowDistApprox c1 a n r <-> lowDistApprox c2 a n r.
  
  intuition.
  unfold lowDistApprox, evalDet_equiv in *.
  destruct H0. destruct H0. intuition.
  exists x.
  exists x0.
  intuition.
  
  eapply rel_map_impl.
  eapply H1.
  intuition.
  eapply H.
  trivial.
  
  unfold lowDistApprox, evalDet_equiv in *.
  destruct H0. destruct H0. intuition.
  exists x.
  exists x0.
  intuition.
  
  eapply rel_map_impl.
  eapply H1.
  intuition.
  eapply H.
  trivial.    
  
Qed.

Theorem det_eq_impl_dist_sem_eq : forall (A : Set)(c1 c2 : Comp A),
  well_formed_comp c1 ->
  well_formed_comp c2 -> (* perhaps we can conclude this from the equivalence? *)
  evalDet_equiv c1 c2 -> 
  dist_sem_eq c1 c2.

  unfold dist_sem_eq.
  intuition.

  (* The proof uses the fact that, for all a, the limit of the low approximation function for the deterministic semantics applied to a equals the distribution computation function applied to a.  Then we use the fact that limits are unique to complete the proof. *)  

  eapply rat_limits_eq.
  2:{
    eapply evalDet_evalDist_equiv.
    trivial.
  }
  eapply lowDistApprox_left_total.
  eapply comp_eq_dec; trivial.
  trivial.
  eapply limit_f_eq.
  eapply evalDet_evalDist_equiv.
  trivial.
  eapply evalDet_equiv_impl_lowDistApprox_equiv.
  eapply evalDet_equiv_symm. trivial.

Qed.

Print Assumptions det_eq_impl_dist_sem_eq.