(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
(* Rules used to prove facts based on the distribution semantics *)

Set Implicit Arguments.

Require Import fcf.DistSem.
Require Import fcf.Fold.
Require Import Permutation.
Require Import fcf.SemEquiv.
Require Import fcf.DetSem.
Require Import fcf.NotationV1.

 
Local Open Scope rat_scope.
Local Open Scope comp_scope.
Local Open Scope list_scope.



(* The uniformity rule allows us to conclude that all bit vectors (of the same length) are equally likely. *)
Theorem uniformity : forall n (x1 x2 : Bvector n),
  evalDist ({0, 1} ^ n) x1 == evalDist ({0, 1} ^ n) x2.

  intuition.
  unfold evalDist.
  eapply eqRat_refl.
Qed.

Lemma evalDist_in_f : forall (A B : Set)(c1 : Comp A)(c2 : Comp B)(f : A -> B),
  (forall a, eqRat (evalDist c1 a) (evalDist c2 (f a))) ->
  (forall a, In a (getSupport c1) <-> In (f a) (getSupport c2)).

  intros.
  specialize (getSupport_correct c1).
  specialize (getSupport_correct c2).
  intros.
  inversion H0; clear H0.
  inversion H1; clear H1.

  intuition.
  apply H3.
  intuition.
  eapply H4; eauto.
  eapply eqRat_trans.
  eapply H.
  eauto.


  eapply H4.
  intuition.
  eapply H3; eauto.
  eapply eqRat_trans.
  eapply eqRat_symm.
  eapply H.
  eauto.
Qed.

Lemma perm_map_in : forall (A B : Set)(lsa : list A)(lsb : list B)(f : A -> B)(f_inv : B -> A),
  (forall b, In b lsb -> f (f_inv b) = b) ->
  (forall a, In a lsa <-> In (f a) lsb) ->
  NoDup (map f lsa) ->
  NoDup lsb ->
  Permutation (map f lsa) lsb.

  intuition.
  eapply NoDup_Permutation; intuition.
  apply in_map_iff in H3.
  destruct H3.
  intuition.
  subst.
  eapply H0.
  trivial.

  eapply in_map_iff.
  econstructor.
  split.
  2:{
    eapply H0.
    assert (x = f (f_inv x)).
    symmetry.
    eapply H.
    trivial.
    rewrite H4 in H3.
    eapply H3.
  }
  eapply H.
  trivial.
Qed.

Lemma not_in_map : forall (A B : Set)(ls : list A)(f : A -> B)(f_inv : B -> A)(a : A),
  (forall a, f_inv (f a) = a) -> 
  ~In a ls -> 
  ~In (f a) (map f ls).

  induction ls; intuition.
  simpl in *.

  intuition.
  
  eapply H1.
  rewrite <- (H a).
  rewrite <- (H a0).
  f_equal.
  trivial.

  eapply IHls; eauto.
Qed.

Lemma map_NoDup : forall (A B : Set)(ls : list A)(f : A -> B)(f_inv : B -> A),
  (forall a, In a ls -> f_inv (f a) = a) ->
  NoDup ls ->
  NoDup (map f ls).

  induction ls; intuition; simpl in *.
  econstructor.

  inversion H0; clear H0; subst.
  econstructor; eauto.

  intuition.
  apply in_map_iff in H0.
  destruct H0.
  intuition.
  assert (x = a).
  rewrite <- (H x); intuition.
  rewrite <- (H a); intuition.
  f_equal.
  trivial.
  subst.
  intuition.
Qed.

Lemma support_NoDup : forall (A : Set)(c : Comp A),
  NoDup (getSupport c).

  intuition.
  specialize (getSupport_correct c); intuition.
  inversion H.
  eauto.
Qed.

Lemma filter_NoDup : forall (A : Set)(ls : list A)(P : A -> bool),
  NoDup ls ->
  NoDup (filter P ls).

  induction ls; simpl in *; intuition.
  
  inversion H; clear H; subst.
  destruct (P a).
  econstructor; eauto.
  intuition.
  eapply filter_In in H.
  intuition.

  eapply IHls; eauto.

Qed.


Lemma evalDist_getSupport_perm : forall (A B : Set)(c1 : Comp A)(c2 : Comp B) (f : A -> B)(f_inv : B -> A),
  (forall b, In b (getSupport c2) -> (f (f_inv b)) = b) ->
  (forall a, In a (getSupport c1) -> (f_inv (f a)) = a) -> 
  (forall a, In a (getSupport c1) -> eqRat (evalDist c1 a) (evalDist c2 (f a))) ->
  (forall a, In a (getSupport c2) -> eqRat (evalDist c2 a) (evalDist c1 (f_inv a))) ->
  Permutation (map f (getSupport c1)) (getSupport c2).

  intuition.
  eapply NoDup_Permutation.
  eapply map_NoDup.
  intuition.
  eapply getSupport_NoDup.
  eapply getSupport_NoDup.
  intuition.
  apply in_map_iff in H3.
  destruct H3.
  intuition.
  subst.
  eapply getSupport_In_evalDist.
  intuition.
  eapply getSupport_In_evalDist.
  eauto.
  eapply eqRat_trans.
  eapply H1.
  trivial.
  trivial.

  eapply in_map_iff.
  econstructor.
  split.
  eapply H.
  trivial.
  
  eapply getSupport_In_evalDist.
  intuition.
  eapply getSupport_In_evalDist.
  eapply H3.
  rewrite H2.
  trivial.
  trivial.

Qed.


Lemma evalDist_getSupport_filter_perm : forall (A: Set)(c1 : Comp A)(c2 : Comp A)(P : A -> bool),
  (forall a, P a = true -> eqRat (evalDist c1 a) (evalDist c2 a)) ->
  Permutation (filter P (getSupport c1)) (filter P (getSupport c2)).

  intuition.
  eapply NoDup_Permutation.
  eapply filter_NoDup.
  eapply support_NoDup.
  eapply filter_NoDup.
  eapply support_NoDup.

  intuition.
  eapply filter_In in H0.
  eapply filter_In.
  intuition.
  eapply getSupport_In_evalDist.
  apply getSupport_In_evalDist in H1.
  intuition.
  apply H1.
  eapply eqRat_trans.
  eapply H.
  trivial.
  trivial.

  intuition.
  eapply filter_In in H0.
  eapply filter_In.
  intuition.
  eapply getSupport_In_evalDist.
  apply getSupport_In_evalDist in H1.
  intuition.
  apply H1.
  eapply eqRat_trans.
  eapply eqRat_symm.
  eapply H.
  trivial.
  trivial.
Qed.


Lemma evalDist_getSupport_perm_id : forall (A : Set)(c1 c2 : Comp A),
  (forall a, eqRat (evalDist c1 a) (evalDist c2 a)) ->
  Permutation (getSupport c1) (getSupport c2).

  intuition.
  rewrite <- map_id.
  eapply Permutation_sym.
  eapply evalDist_getSupport_perm; intuition.
  symmetry.
  eauto.
Qed.


Lemma sumList_f_inverse : forall (A B : Set)(ls : list A)(f : A -> B)(f_inv : B -> A)(fa : A -> Rat),
    (forall a, In a ls -> f_inv (f a) = a) ->
    sumList (map f ls) (fun (b : B) => fa (f_inv b) ) ==
    sumList ls fa.
    
  intuition.
  unfold sumList.
  eapply fold_add_f_inverse;
  intuition.
Qed.

Theorem distro_iso_eq : forall (A B C D : Set)(f : C -> D)(f_inv : D -> C)(d : Comp D)(c : Comp C)(f1 : D -> Comp B)(f2 : C -> Comp A)(a : A)(b : B),
  (forall x, In x (getSupport d) -> f (f_inv x) = x) ->
  (forall x, In x (getSupport c) -> f_inv (f x) = x) ->
  (forall x, In x (getSupport d) -> In (f_inv x) (getSupport c)) ->
  (forall x, In x (getSupport c) -> (evalDist d (f x)) == (evalDist c x)) -> 
  (forall x, In x (getSupport c) -> (evalDist (f1 (f x)) b) == (evalDist (f2 x) a)) ->
  (evalDist (Bind d f1) b == evalDist (Bind c f2) a).

  intuition.
  simpl.

  eapply eqRat_trans.
  eapply fold_add_rat_perm.
  eapply Permutation_sym.
  eapply evalDist_getSupport_perm; eauto.

  intuition.
  symmetry.
  eauto.

  intuition.
  rewrite <- (H a0) at 1.
  eapply H2.
  eauto.
  trivial.

  eapply eqRat_refl.
  intuition.
  eapply ratMult_eqRat_compat.
  rewrite <- H at 1.
  eauto.
  trivial.
  rewrite <- H at 1.
  eapply H3.
  eauto.
  trivial.

  eapply eqRat_trans.
  2:{
    eapply fold_add_f_inverse; eauto.
    eapply eqRat_refl.
  }
  simpl.
  eapply eqRat_refl.

Qed.


Lemma evalDist_seq_eq : forall (A1 A2 B : Set)(c1 c2 : Comp B)(f1 : B -> Comp A1)(f2 : B -> Comp A2) y z,
  (forall x : B, evalDist c1 x == evalDist c2 x) ->
  (forall x : B, In x (getSupport c1) -> evalDist (f1 x) y == evalDist (f2 x) z) ->
  evalDist (x <-$ c1; f1 x) y == evalDist (x <-$ c2; f2 x) z.

  intuition.
  eapply (distro_iso_eq (fun b => b)(fun b => b)); intuition.

  eapply getSupport_In_evalDist.
  intuition.
  eapply getSupport_In_evalDist.
  eauto.
  rewrite H.
  trivial.

  eapply H0.
  eapply getSupport_In_evalDist.
  intuition.
  eapply getSupport_In_evalDist.
  eauto.
  rewrite <- H.
  trivial.
Qed.


Theorem distro_irr_eq : forall (A B : Set)(b : Comp B)(a : B -> Comp A)(y : A) v,
  well_formed_comp b ->
  (forall x, In x (getSupport b) -> (evalDist (a x) y) == v) -> 
  evalDist (Bind b a) y == v.
  
  intuition.
  simpl.
  rewrite sumList_body_eq.
  2:{
    intuition.
    rewrite H0 at 1.
    eapply eqRat_refl.
    trivial.
  }
  rewrite sumList_factor_constant_r.
  rewrite evalDist_lossless.
  eapply ratMult_1_l.
  trivial.
Qed.


Lemma sumList_filter : forall (A : Set)(ls : list A)(f : A -> Rat)(P : A -> bool) init,
  fold_left (fun r a => r + if (P a) then (f a) else 0) ls init  ==
  fold_left (fun r a => r + (f a)) (filter P ls) init.

  induction ls; simpl in *; intuition.

  destruct (P a); simpl.
  eapply IHls.
  rewrite fold_add_body_eq.
  eapply IHls.
  symmetry.
  eapply ratAdd_0_r.
  
  intuition.
Qed.


Theorem evalDist_left_ident_eq : forall (B : Set)(eqd : EqDec B)(b : B)(A : Set)(c2 : B -> Comp A)  a,
  (evalDist (x <-$ ret b; (c2 x)) a) == (evalDist (c2 b) a).

  intuition.
  simpl.
  unfold sumList.
  simpl.
  destruct (EqDec_dec eqd b b).
  rewrite <- ratAdd_0_l.
  rewrite ratMult_1_l.
  intuition.
  congruence.

Qed.


Theorem evalDist_assoc_eq : forall (A : Set)(c1 : Comp A)(B C : Set)(c2 : A -> Comp B)(c3 : B -> Comp C),
  dist_sem_eq (Bind (Bind c1 c2) c3) (Bind c1 (fun a => (Bind (c2 a) c3))).

  unfold dist_sem_eq.
  intuition.
  assert (EqDec B).
  eapply bind_EqDec; eauto.
  simpl.
  eapply eqRat_trans.
  eapply sumList_body_eq.
  intuition.
  symmetry.
  eapply sumList_factor_constant_r.
  simpl.
  rewrite sumList_comm.
  eapply sumList_body_eq.
  intuition.
  rewrite <- sumList_factor_constant_l.
  eapply eqRat_trans.
  eapply (sumList_filter_partition (fun b => if (in_dec (EqDec_dec _) b (getSupport (c2 a0))) then true else false)).
  eapply eqRat_trans.
  eapply ratAdd_eqRat_compat.
  eapply eqRat_refl.
  eapply sumList_0.
  intuition.
  eapply filter_In in H1.
  intuition.
  destruct (in_dec (EqDec_dec H) a1 (getSupport (c2 a0))).
  simpl in H3.
  discriminate.
  assert (evalDist (c2 a0) a1 == 0).
  eapply getSupport_not_In_evalDist.
  trivial.
  rewrite H1.
  rewrite ratMult_0_r.
  eapply ratMult_0_l.
  rewrite <- ratAdd_0_r.
  eapply eqRat_trans.
  eapply sumList_permutation.
  2:{
    eapply sumList_body_eq.
    intuition.
    eapply ratMult_assoc.
  }
  eapply NoDup_Permutation.
  eapply filter_NoDup.
  eapply getUnique_NoDup.
  eapply getSupport_NoDup.
  intuition.
  apply filter_In in H1.
  intuition.
  destruct (in_dec (EqDec_dec H) x (getSupport (c2 a0))).
  trivial.
  discriminate.

  eapply filter_In.
  intuition.
  eapply in_getUnique.
  eapply in_flatten.
  econstructor.
  split.
  eapply in_map_iff.
  econstructor.
  split.
  eapply eq_refl.
  eauto.
  eauto.
  destruct (in_dec (EqDec_dec H) x (getSupport (c2 a0)) ).
  trivial.
  intuition.
Qed.


(* We can swap any two independent commands *)
Theorem evalDist_commute_eq : forall (A B : Set)(c1 : Comp A)(c2 : Comp B)(C : Set)(c3 : A -> B -> Comp C),
  dist_sem_eq (a <-$ c1; b <-$ c2; (c3 a b)) (b <-$ c2; a <-$ c1; (c3 a b)). 
  
  intuition.
  unfold dist_sem_eq.
  intuition.
  simpl.
  eapply eqRat_trans.
  eapply sumList_body_eq.
  intuition.
  symmetry.
  eapply sumList_factor_constant_l.
  symmetry.
  eapply eqRat_trans.
  eapply sumList_body_eq.
  intuition.
  symmetry.
  eapply sumList_factor_constant_l.
  rewrite sumList_summation.
  eapply sumList_body_eq.
  intuition.
  eapply sumList_body_eq.
  intuition.
  repeat rewrite <- ratMult_assoc.
  eapply ratMult_eqRat_compat; intuition.
  eapply ratMult_comm.
Qed.

Lemma evalDist_Repeat_eq : forall (A : Set)(c1 c2 : Comp A)(P1 P2 : A -> bool) v1 v2,
  evalDist c1 v1 == evalDist c2 v2 ->
  P1 v1 = P2 v2 ->
  In v1 (filter P1 (getSupport c1)) ->
  sumList (filter P1 (getSupport c1)) (evalDist c1) == sumList (filter P2 (getSupport c2)) (evalDist c2) ->
  evalDist (Repeat c1 P1) v1 == evalDist (Repeat c2 P2) v2.
  
  intuition.
  simpl.
  eapply ratMult_eqRat_compat; intuition.
  eapply ratMult_eqRat_compat.
  unfold indicator.
  rewrite H0.
  intuition.
  eapply ratInverse_eqRat_compat.
  intuition.
  eapply getSupport_In_evalDist.
  eapply filter_In.
  eauto.
  eapply sumList_0 in H3; eauto.
  trivial.
  
Qed.

Definition intersect(A : Set)(eqd : eq_dec A)(ls1 ls2 : list A) :=
  filter (fun x => if (in_dec eqd x ls1) then true else false) ls2.


Lemma in_intersect : forall (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A) a,
  In a (intersect eqd ls1 ls2) <->
  In a ls1 /\ In a ls2.
  
  unfold intersect in *.
  
  intuition.
  apply filter_In in H.
  intuition.
  destruct (in_dec eqd a ls1).
  trivial.
  discriminate.
  apply filter_In in H.
  intuition.
  
  eapply filter_In.
  intuition.
  destruct (in_dec eqd a ls1); intuition.
Qed.

Lemma intersect_comm : forall (A : Set)(eqd : eq_dec A)(ls1 ls2 : list A),
  NoDup ls1 ->
  NoDup ls2 ->
  Permutation (intersect eqd ls1 ls2) (intersect eqd ls2 ls1).
  
  intuition.
  eapply NoDup_Permutation.
  apply filter_NoDup; trivial.
  apply filter_NoDup; trivial.
  
  unfold intersect in *.
  intuition.
  apply filter_In.
  apply filter_In in H1.
  intuition.
  destruct (in_dec eqd x ls1); intuition.
  discriminate.
  destruct (in_dec eqd x ls2); intuition.
  
  apply filter_In.
  apply filter_In in H1.
  intuition.
  destruct (in_dec eqd x ls2); intuition.
  discriminate.
  destruct (in_dec eqd x ls1); intuition.
  
Qed.


Theorem fundamental_lemma_h : forall (A : Set)(eqda : EqDec A)(c1 c2 : Comp (A * bool)),
  (evalDist (Bind c1 (fun x => ret snd x)) true == evalDist (Bind c2 (fun x => ret snd x)) true) ->
  (forall a, evalDist c1 (a, false) == evalDist c2 (a, false)) ->
  forall a, 
    ratDistance (evalDist (Bind c1 (fun x => ret (fst x))) a) (evalDist (Bind c2 (fun x => ret (fst x))) a) <= 
    evalDist (Bind c1 (fun x => ret snd x)) true.

  intuition.
  simpl in *.

  rewrite (sumList_filter_partition (@snd A bool)).
  rewrite (sumList_filter_partition (@snd A bool) (getSupport c2)).

  rewrite ratDistance_add_same_r_gen.

  eapply leRat_trans.
  eapply ratDistance_le_max_triv.
  eapply maxRat_leRat_same.

  eapply leRat_trans.
  2:{
    eapply sumList_filter_le.
  }

  eapply sumList_le; intuition.
  apply filter_In in H1.
  intuition.
  eapply ratMult_leRat_compat; intuition.
  destruct a0.
  simpl in *.
  subst.
  destruct (EqDec_dec bool_EqDec true true); try congruence.
  destruct (EqDec_dec eqda a0 a); intuition.

  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eapply H.
  }
  eapply leRat_trans.
  2:{
    eapply sumList_filter_le.
  }
  eapply sumList_le; intuition.
  apply filter_In in H1.
  intuition.
  eapply ratMult_leRat_compat; intuition.
  destruct a0.
  simpl in *.
  subst.
  destruct (EqDec_dec bool_EqDec true true); try congruence.
  destruct (EqDec_dec eqda a0 a); intuition.

  assert (eq_dec (A * bool)).
  unfold eq_dec.
  eapply (EqDec_dec (pair_EqDec _ _)).

  assert (NoDup (filter (fun a0 : A * bool => negb (snd a0)) (intersect H1 (getSupport c1) (getSupport c2)))).
  eapply filter_NoDup.
  eapply filter_NoDup; eapply getSupport_NoDup.
  
  eapply eqRat_trans.
  symmetry.
  eapply sumList_subset'.
  trivial.
  eapply H2.
  eapply filter_NoDup.
  eapply getSupport_NoDup.
  intuition.
  apply filter_In in H3.
  intuition.
  eapply filter_In.
  split.

  eapply in_intersect.
  eapply Permutation_in.
  eapply intersect_comm.
  eapply getSupport_NoDup.
  2:{
    eauto.
  }
  eapply getSupport_NoDup.
  trivial.

  intuition.
  apply filter_In in H3.
  intuition.
  destruct a0.
  simpl in *.
  destruct (EqDec_dec eqda a0 a); subst.
  rewrite ratMult_1_r.
  destruct b; simpl in *; try discriminate.
  rewrite H0.
  eapply getSupport_not_In_evalDist.
  intuition.
  eapply H4.
  eapply filter_In.
  intuition.
  eapply in_intersect.
  intuition.
  apply ratMult_0_r.

  symmetry.
  eapply eqRat_trans.
  symmetry.
  eapply sumList_subset'.
  trivial.
  eapply H2.
  eapply filter_NoDup.
  eapply getSupport_NoDup.
  intuition.
  apply filter_In in H3.
  intuition.
  eapply filter_In.
  split.

  eapply in_intersect.
  eauto.
  trivial.

  intuition.
  apply filter_In in H3.
  intuition.
  destruct a0.
  simpl in *.
  destruct (EqDec_dec eqda a0 a); subst.
  rewrite ratMult_1_r.
  destruct b; simpl in *; try discriminate.
  rewrite <- H0.
  eapply getSupport_not_In_evalDist.
  intuition.
  eapply H4.
  eapply filter_In.
  intuition.
  eapply in_intersect.
  intuition.
  apply ratMult_0_r.

  eapply sumList_body_eq.
  intuition.
  apply filter_In in H3.
  intuition.
  destruct a0; simpl in *.
  destruct b; simpl in *; try discriminate.
  rewrite H0.
  intuition.
Qed.

Theorem evalDist_right_ident : forall (A : Set)(eqd : EqDec A)(c : Comp A) a,
  evalDist (x <-$ c; ret x) a == evalDist c a.

  intuition.
  destruct (in_dec (EqDec_dec eqd) a (getSupport c)).
  simpl.
  eapply eqRat_trans.
  eapply sumList_exactly_one.
  eapply getSupport_NoDup.
  eauto.
  intuition.
  destruct (EqDec_dec eqd b a).
  subst.
  intuition.
  eapply ratMult_0_r.

  destruct (EqDec_dec eqd a a).
  eapply ratMult_1_r.
  congruence.

  simpl.
  eapply eqRat_trans.
  eapply sumList_0.
  intuition.
  destruct (EqDec_dec eqd a0 a).
  subst.
  intuition.
  eapply ratMult_0_r.
  symmetry.
  eapply getSupport_not_In_evalDist.
  trivial.
Qed.


Theorem fundamental_lemma : forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(c1 c2 : Comp A)(badness : A -> bool)(proj : A -> B),
  Pr [a <-$ c1; ret (badness a)] == Pr[a <-$ c2; ret (badness a)] ->
  (forall x, evalDist (a <-$ c1; ret (proj a, badness a)) (x, false) == evalDist (a <-$ c2; ret (proj a, badness a)) (x, false)) ->
  forall x, 
    | (evalDist (a <-$ c1; ret (proj a)) x)  - (evalDist (a <-$ c2; ret (proj a)) x) | <= 
    Pr [a <-$ c1; ret (badness a)].

  intuition.
  specialize (@fundamental_lemma_h B eqdb (a <-$ c1; ret (proj a, badness a)) (a <-$ c2; ret (proj a, badness a)) ); intuition.
  assert ( | evalDist (x <-$ (a0 <-$ c1; ret (proj a0, badness a0)); ret fst x) x -
       evalDist (x <-$ (a0 <-$ c2; ret (proj a0, badness a0)); ret fst x) x | ==
          | evalDist (a <-$ c1; ret proj a) x - evalDist (a <-$ c2; ret proj a) x |).
  eapply ratDistance_eqRat_compat.

  eapply eqRat_trans.
  eapply evalDist_assoc_eq.
  cbv beta.
  eapply eqRat_trans.
  eapply evalDist_seq_eq.
  intuition.
  eapply eqRat_refl.
  intuition.
  eapply eqRat_trans.
  eapply evalDist_left_ident_eq.
  eapply eqRat_refl.
  cbv beta.
  unfold fst.
  intuition.

  eapply eqRat_trans.
  eapply evalDist_assoc_eq.
  cbv beta.
  eapply evalDist_seq_eq; intuition.
  eapply evalDist_left_ident_eq.

  rewrite <- H2.
  rewrite H1.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply eqRat_trans.
  eapply evalDist_assoc_eq.
  cbv beta.
  eapply evalDist_seq_eq; intuition.
  eapply eqRat_refl.
  eapply eqRat_trans.
  eapply evalDist_left_ident_eq.
  cbv beta.
  eapply eqRat_refl.
  cbv beta.
  unfold snd.
  intuition.
  eapply eqRat_trans.
  eapply evalDist_assoc_eq.
  eapply eqRat_trans.
  eapply evalDist_seq_eq; intuition.
  eapply eqRat_refl.
  eapply eqRat_trans.
  eapply evalDist_left_ident_eq.
  cbv beta.
  eapply eqRat_refl.
  rewrite H.
  symmetry.
  eapply eqRat_trans.
  eapply evalDist_assoc_eq.
  eapply eqRat_trans.
  eapply evalDist_seq_eq; intuition.
  eapply eqRat_refl.
  eapply eqRat_trans.
  eapply evalDist_left_ident_eq.
  eapply eqRat_refl.
  cbv beta.

  simpl.
  intuition.
  intuition.
Qed.


Theorem repeat_unroll_eq: forall (A : Set)(eqd : EqDec A)(c : Comp A)(P : A -> bool) v,
  well_formed_comp c ->
  (exists a, In a (filter P (getSupport c))) ->
  evalDist (Repeat c P) v == evalDist (x <-$ c; if (P x) then ret x else (Repeat c P)) v.
  
  intuition.
  
  eapply det_eq_impl_dist_sem_eq; trivial.
  destruct H0.
  
  eapply well_formed_Repeat; trivial.
  unfold eq_dec.
  intuition.
  eapply (EqDec_dec _).
  eauto.
  econstructor; intuition.
  destruct (P b).
  econstructor.
  destruct H0.
  econstructor.
  unfold eq_dec.
  intuition.
  eapply (EqDec_dec _).
  trivial.
  eauto.
  
  unfold DetSem.evalDet_equiv.
  intuition.
  inversion H1; clear H1; subst.
  
  inversion H2; clear H2; subst.
  simpl in *.
  eapply evalDet_steps_bind_done_inv in H6.
  destruct H6.
  destruct H1.
  intuition.
  econstructor.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eauto.
  destruct (P x).
  inversion H3; clear H3; subst.
  simpl in *.
  inversion H7; clear H7; subst.
  econstructor.
  eauto.
  simpl.
  econstructor.
  trivial.
  
  inversion H2; clear H2; subst.
  simpl in *.
  apply evalDet_steps_bind_eof_inv in H6.
  intuition.
  econstructor.
  eapply evalDet_bind_eof.
  trivial.
  destruct H1.
  destruct H1.
  intuition.
  econstructor.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eauto.
  destruct (P x).
  inversion H3; clear H3; subst.
  simpl in *.
  inversion H7.
  trivial.
  
  inversion H1; clear H1; subst.
  eapply evalDet_steps_bind_done_inv in H2.
  destruct H2.
  destruct H1.
  intuition.
  econstructor.
  econstructor.
  eauto.
  simpl.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eauto.
  destruct (P x).
  inversion H3; clear H3; subst.
  simpl in *.
  inversion H7; clear H7; subst.
  econstructor.
  eauto.
  simpl.
  econstructor.
  trivial.
  
  apply evalDet_steps_bind_eof_inv in H2.
  intuition.
  econstructor.
  econstructor.
  eauto.
  simpl.
  eapply evalDet_bind_eof.
  trivial.
  destruct H1.
  destruct H1.
  intuition.
  econstructor.
  econstructor.
  eauto.
  simpl.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eauto.
  destruct (P x).
  inversion H3; clear H3; subst.
  simpl in *.
  inversion H7.
  trivial.
Qed.


(* rules related to case splits and specifications *)
Lemma evalDist_seq_case_split_eq : forall (B : Set)(e : B -> bool) v v1 v2 (A : Set)(c : Comp B)(f : B -> Comp A) a,
  well_formed_comp c ->
  Pr[b <-$ c; ret (e b)] == v ->
  (forall b, (e b) = true -> (evalDist (f b) a) == v1) ->
  (forall b, (e b) = false -> (evalDist (f b) a) == v2) ->
  (evalDist (Bind c f) a == v * v1 + (ratSubtract 1 v) * v2).
  
  intuition.
  simpl in *.
  rewrite (sumList_partition e).
  eapply ratAdd_eqRat_compat.
  
  rewrite (sumList_body_eq _ _ (fun b => ((evalDist c b) * (if (e b) then 1 else 0)) * v1)).
  rewrite sumList_factor_constant_r.
  eapply ratMult_eqRat_compat; intuition.
  rewrite <- H0.
  eapply sumList_body_eq; intuition.
  destruct (EqDec_dec bool_EqDec (e a0) true).
  rewrite e0.
  intuition.
  destruct (e a0); try congruence.
  intuition.
  
  intuition.
  case_eq (e a0); intuition.
  repeat rewrite ratMult_1_r.
  eapply ratMult_eqRat_compat; intuition.
  repeat rewrite ratMult_0_r.
  rewrite ratMult_0_l.
  intuition.
  
  rewrite (sumList_body_eq _ _ (fun b => ((evalDist c b) * (if (e b) then 0 else 1)) * v2)).
  rewrite sumList_factor_constant_r.
  eapply ratMult_eqRat_compat; intuition.
  rewrite <- H0.
  
  rewrite <- (@evalDist_lossless _ c).
  rewrite (sumList_partition e _ (evalDist c)).
  rewrite ratAdd_comm.
  rewrite ratSubtract_ratAdd_assoc.
  rewrite ratSubtract_0.
  rewrite <- ratAdd_0_r.
  intuition.
  eapply eqRat_impl_leRat.
  eapply sumList_body_eq; intuition.
  destruct (EqDec_dec bool_EqDec (e a0) true).
  rewrite e0.
  intuition.
  destruct (e a0); try congruence.
  intuition.
  eapply eqRat_impl_leRat.
  eapply sumList_body_eq; intuition.
  destruct (EqDec_dec bool_EqDec (e a0) true).
  rewrite e0.
  intuition.
  destruct (e a0); try congruence.
  intuition.
  trivial.
  
  intuition.
  case_eq (e a0); intuition.
  repeat rewrite ratMult_0_r.
  rewrite ratMult_0_l.
  intuition.
  repeat rewrite ratMult_1_r.
  eapply ratMult_eqRat_compat; intuition.
Qed.


Theorem evalDist_bind_distance : forall (A B : Set)(c1 c2 : Comp B)(c3 c4 : B -> Comp A) d,
  well_formed_comp c2 ->
  (forall b, evalDist c1 b == evalDist c2 b) ->
  (forall b a, In b (getSupport c1) -> | evalDist (c3 b) a - evalDist (c4 b) a | <= d) ->
  (forall a, | evalDist (Bind c1 c3) a - evalDist (Bind c2 c4) a | <= d).
  
  intuition.
  simpl.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  rewrite sumList_body_eq.
  2:{
    intros.
    eapply ratMult_eqRat_compat.
    eapply H0.
    eapply eqRat_refl.
  }
  eapply eqRat_refl.
  
  assert (Permutation (getSupport c1) (getSupport c2)).
  eapply NoDup_Permutation; intuition; eauto using getSupport_NoDup.
  eapply getSupport_In_evalDist.
  rewrite <- H0.
  eapply getSupport_In_evalDist.
  trivial.
  eapply getSupport_In_evalDist.
  rewrite H0.
  eapply getSupport_In_evalDist.
  trivial.
  erewrite sumList_permutation; eauto.
  
  rewrite sumList_distance_prod.
  eapply leRat_trans.
  eapply sumList_le; intuition.
  eapply ratMult_leRat_compat.
  eapply leRat_refl.
  eapply H1.
  eapply getSupport_In_evalDist.
  rewrite H0.
  eapply getSupport_In_evalDist.
  trivial.

  rewrite sumList_factor_constant_r.
  rewrite evalDist_lossless.
  rewrite ratMult_1_l.
  intuition.
  trivial.
  
Qed.

Lemma evalDist_Bind_1_le_l : forall (A B : Set) (b : Comp B) (a : B -> Comp A) (y : A) (v : Rat),
  well_formed_comp b ->
  (forall x : B, In x (getSupport b) -> evalDist (a x) y <= v) ->
  evalDist (x <-$ b; a x) y <= v.
  
  intuition.
  simpl.
  eapply leRat_trans.
  eapply sumList_le; intuition.
  eapply ratMult_leRat_compat.
  eapply leRat_refl.
  eapply H0.
  trivial.
  rewrite sumList_factor_constant_r.
  rewrite evalDist_lossless.
  rewrite ratMult_1_l.
  intuition.
  trivial.
Qed.


Lemma evalDist_ret_1 : 
  forall (A : Set)(eqd : eq_dec A)(a1 a2 : A),
    a1 = a2 ->
    evalDist (Ret eqd a1) a2 = 1.
  
  intuition.
  subst.
  simpl.
  destruct (eqd a2 a2); subst; intuition.
  
Qed.

Lemma evalDist_ret_0 : 
  forall (A : Set)(eqd : eq_dec A)(a1 a2 : A),
    a1 <> a2 ->
    evalDist (Ret eqd a1) a2 = 0.
  
  intuition.
  simpl.
  destruct (eqd a1 a2); subst; intuition.
  
Qed.

Lemma evalDist_ret_eq : 
  forall (A : Set)(eqd1 eqd2 : eq_dec A) a1 a2 x,
    a1 = a2 ->
    evalDist (Ret eqd1 a1) x == evalDist (Ret eqd2 a2) x.
  
  intuition.
  simpl.
  subst.
  destruct (eqd1 a2 x); destruct (eqd2 a2 x); subst; intuition.
Qed.

Theorem evalDist_seq_step : 
  forall (A B :Set)(c : Comp A)(f : A -> Comp B) b,
    evalDist (Bind c f) b ==
    sumList (getSupport c) (fun a => evalDist c a * evalDist (f a) b).
  
  intuition.
  simpl.
  eapply sumList_body_eq; intuition.

Qed.


Theorem evalDist_1 : 
  forall (A : Set)(eqd : EqDec A)(c : Comp A) a,
    well_formed_comp c ->
    evalDist c a == 1 ->
    (getSupport c) = (a :: nil)%list.

  intuition.
  
  specialize (evalDist_getSupport_perm_id c (ret a)); intuition.
  assert (forall a0 : A, evalDist c a0 == evalDist (ret a) a0).
  intuition.
  case_eq (eqb a a0); intuition.
  rewrite eqb_leibniz in H2.
  subst.
  simpl.
  destruct (EqDec_dec eqd a0 a0); intuition.
  
  simpl.
  assert (evalDist c a0 == 0).
  eapply evalDist_1_0; intuition.
  eapply H0.
  subst.
  rewrite eqb_refl in H2.
  discriminate.
  rewrite H3.
  destruct ( EqDec_dec eqd a a0); subst; intuition.
  rewrite eqb_refl in H2.
  discriminate.
  
  intuition.
  simpl in *.
  
  eapply Permutation_length_1_inv.
  eapply Permutation_sym.
  trivial.
  
Qed.

Theorem evalDist_bool_equiv_all : 
  forall (c1 c2 : Comp bool),
    well_formed_comp c1 ->
    well_formed_comp c2 ->
    Pr[c1] == Pr[c2] -> 
    (forall b, evalDist c1 b == evalDist c2 b).
  
  intuition.
  destruct b.
  trivial.
  
  rewrite evalDist_complement.
  rewrite evalDist_complement.
  eapply ratSubtract_eqRat_compat; intuition.
  trivial.
  trivial.
Qed.


Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Class RatRel (R : Rat -> Rat -> Prop) :=
{
  refl : forall r1 r2, r1 == r2 -> R r1 r2;
  trans : Transitive R;
  add_proper : Proper (R ==> R ==> R) ratAdd;
  mult_proper : Proper (R ==> R ==> R) ratMult
}.

Instance RatRel_trans : 
  forall (R : Rat -> Rat -> Prop),
    RatRel R -> Transitive R.

intuition.
destruct H.
intuition.

Qed.

Instance RatRel_flip : 
  forall R,
    RatRel R ->
    RatRel (Basics.flip R).

intuition.
econstructor; intuition.
unfold Basics.flip.
eapply refl.
eapply eqRat_symm.
intuition.

unfold Proper, respectful, Basics.flip in *; intuition.
eapply add_proper; trivial.
unfold Proper, respectful, Basics.flip in *; intuition.
eapply mult_proper; trivial.
Qed.

(* The class includes equality and inequality. *)

Instance eqRat_RatRel : RatRel eqRat.

econstructor;
eauto with typeclass_instances.

Qed.

Instance leRat_RatRel : RatRel leRat.

econstructor;
eauto with typeclass_instances.
eapply eqRat_impl_leRat.

Qed.

(* This one comes up some times: *)
Instance eqRat_RatRel_1 : 
  RatRel (fun r r1 : Rat => r1 == r).

eapply RatRel_flip.
intuition.

Qed.

(* some distribution rules that use RatRel *)
Theorem evalDist_left_ident : 
  forall rel (B : Set)(eqd : EqDec B)(b : B)(A : Set)(c2 : B -> Comp A) a,
    RatRel rel ->
    rel (evalDist (x <-$ ret b; (c2 x)) a) (evalDist (c2 b) a).

  intuition.
  eapply refl.
  eapply evalDist_left_ident_eq.
Qed.

Theorem evalDist_assoc : 
  forall rel (A : Set)(c1 : Comp A)(B C : Set)(c2 : A -> Comp B)(c3 : B -> Comp C) x,
    RatRel rel ->
    rel (evalDist (Bind (Bind c1 c2) c3) x) (evalDist (Bind c1 (fun a => (Bind (c2 a) c3))) x).

  intuition.
  eapply refl.
  eapply evalDist_assoc_eq.

Qed.


Theorem evalDist_commute: 
  forall rel  (A B : Set)(c1 : Comp A)(c2 : Comp B)(C : Set)(c3 : A -> B -> Comp C) x,
    RatRel rel ->
    rel (evalDist (a <-$ c1; b <-$ c2; (c3 a b)) x) (evalDist (b <-$ c2; a <-$ c1; (c3 a b)) x). 

  intuition.
  eapply refl.
  eapply evalDist_commute_eq.

Qed.


Lemma rel_sumList_compat : 
  forall (A : Set)(f1 f2 : A -> Rat) ls rel,
    RatRel rel ->
    (forall a, In a ls -> rel (f1 a) (f2 a)) ->
    rel (sumList ls f1) (sumList ls f2).
  
  induction ls; intuition; simpl in *.
  unfold sumList; simpl.
  eapply refl.
  intuition.
  
  eapply trans.
  eapply refl.
  eapply sumList_cons.
  eapply trans.
  2:{
    eapply refl.
    symmetry.
    eapply sumList_cons.
  }
  eapply add_proper.
  intuition.
  eapply IHls; intuition.
Qed.

Lemma rel_seq : 
  forall (A B C : Set)(c : Comp A)(f1 : A -> Comp B)(f2 : A -> Comp C) rel x1 x2,
    RatRel rel ->
    (forall a, In a (getSupport c) -> rel (evalDist (f1 a) x1) (evalDist (f2 a) x2)) ->
    rel (evalDist (a <-$ c; f1 a) x1) (evalDist (a <-$ c; f2 a) x2).
  
  intuition.
  simpl.
  eapply rel_sumList_compat; intuition.
  eapply mult_proper.
  eapply refl.
  intuition.
  intuition.
Qed.

Lemma evalDist_bind_case_split : 
  forall rel (B : Set)(e : B -> bool) v v1 v2 (A : Set)(c : Comp B)(f : B -> Comp A)  a,
    RatRel rel ->
    well_formed_comp c ->
    Pr[b <-$ c; ret (e b)] == v ->
    (forall b, (e b) = true -> rel (evalDist (f b) a) v1) ->
    (forall b, (e b) = false -> rel (evalDist (f b) a) v2) ->
    (rel (evalDist (Bind c f) a) (v * v1 + (ratSubtract 1 v) * v2)).

  intuition.
  simpl in *.
  eapply trans.
  eapply refl.
  rewrite (sumList_filter_partition e).
  eapply eqRat_refl.
  eapply add_proper.

  eapply trans.
  eapply (rel_sumList_compat); intuition.
  eapply mult_proper.
  eapply refl.
  eapply eqRat_refl.
  eapply H2.
  eapply filter_In.
  eauto.
  eapply refl.
  rewrite sumList_factor_constant_r.
  eapply ratMult_eqRat_compat; intuition.
  
  rewrite (sumList_filter_partition e) in H1.
  rewrite <- H1.
  rewrite ratAdd_0_r.
  eapply ratAdd_eqRat_compat.
  eapply sumList_body_eq; intuition.
  rewrite <- ratMult_1_r at 1.
  eapply ratMult_eqRat_compat.
  intuition.
  destruct ( EqDec_dec bool_EqDec (e a0) true); intuition.
  exfalso.
  eapply n.
  eapply filter_In.
  eauto.

  symmetry.
  eapply sumList_0; intuition.
  destruct (EqDec_dec bool_EqDec (e a0) true).
  apply filter_In in H4.
  intuition.
  rewrite e0 in H6.
  simpl in *.
  congruence.
  eapply ratMult_0_r.

  eapply trans.
  eapply (rel_sumList_compat); intuition.
  eapply mult_proper.
  eapply refl.
  eapply eqRat_refl.
  eapply H3.
  eapply filter_In in H4.
  intuition.
  destruct (e a0); intuition.
  eapply refl.
  rewrite sumList_factor_constant_r.
  eapply ratMult_eqRat_compat; intuition.
  
  rewrite <- H1.
  rewrite <- (@evalDist_lossless _ c); trivial.
  symmetry.
  rewrite (sumList_partition e _ (evalDist c)).
  rewrite ratAdd_comm.
  rewrite ratSubtract_ratAdd_assoc.
  rewrite ratSubtract_0.
  rewrite <- ratAdd_0_r.
  
  rewrite (sumList_filter_partition e).
  symmetry.
  rewrite ratAdd_0_l.
  eapply ratAdd_eqRat_compat.
  symmetry.
  eapply sumList_0; intuition.
  apply filter_In in H4.
  intuition.
  rewrite H6.
  eapply ratMult_0_r.
  eapply sumList_body_eq; intuition.
  apply filter_In in H4.
  intuition.
  destruct (e a0); simpl in *; try discriminate.
  symmetry.
  eapply ratMult_1_r.
  eapply sumList_le; intuition.
  destruct (EqDec_dec bool_EqDec (e a0) true).
  rewrite e0.
  intuition.
  destruct (e a0); intuition.

  eapply sumList_le; intuition.
  destruct ( EqDec_dec bool_EqDec (e a0) true).
  destruct (e a0); try discriminate.
  intuition.
  destruct (e a0); intuition.
Qed.

Lemma rel_sumList_factor_r : 
  forall (A : Set) (f : A -> Rat) (ls : list A) c rel,
    RatRel rel ->
    rel (sumList ls (fun a => (f a) * c)) ((sumList ls f) * c).

  induction ls; intuition; simpl in *.
  unfold sumList; simpl.
  eapply refl.
  symmetry.
  eapply ratMult_0_l.

  eapply trans.
  eapply refl.
  eapply sumList_cons.
  eapply trans.
  2:{
    eapply refl.
    symmetry.
    eapply eqRat_trans.
    eapply ratMult_eqRat_compat.
    eapply sumList_cons.
    eapply eqRat_refl.
    eapply ratMult_distrib_r.
  }
  eapply add_proper.
  eapply refl.
  intuition.
  eapply IHls; intuition.
Qed. 

Theorem evalDist_irr_l : 
  forall (A B : Set)(c : Comp A)(f : A -> Comp B)(y : B) rel v,
    RatRel rel ->
    well_formed_comp c ->
    (forall x, In x (getSupport c) -> rel (evalDist (f x) y) v) -> 
    rel (evalDist (Bind c f) y) v.

  intuition.
  simpl.
  eapply trans.
  eapply rel_sumList_compat;
  intuition.
  eapply mult_proper.
  eapply refl.
  eapply eqRat_refl.
  eapply H1.
  trivial.
 
  specialize (rel_sumList_factor_r (evalDist c) (getSupport c) v H); intuition.

  eapply trans.
  eapply H2.
  eapply refl.
  rewrite evalDist_lossless.
  eapply ratMult_1_l.
  trivial.
Qed.

Lemma rel_sumList_factor_r_r : 
  forall (A : Set) (f : A -> Rat) (ls : list A) c rel,
    RatRel rel ->
    rel ((sumList ls f) * c) (sumList ls (fun a => (f a) * c)).

  induction ls; intuition; simpl in *.
  unfold sumList; simpl.
  eapply refl.
  eapply ratMult_0_l.

  eapply trans.
  eapply refl.
  eapply eqRat_trans.
  eapply ratMult_eqRat_compat.
  eapply sumList_cons.
  eapply eqRat_refl.
  eapply ratMult_distrib_r.

  eapply trans.
  2:{
    eapply refl.
    symmetry.
    eapply sumList_cons.
  }
  simpl.
  eapply add_proper.
  eapply refl.
  intuition.
  eapply IHls; intuition.
Qed. 

Theorem evalDist_irr_r : 
  forall (A B : Set)(c : Comp A)(f : A -> Comp B)(y : B) rel v,
    RatRel rel ->
    well_formed_comp c ->
    (forall x, In x (getSupport c) -> rel v (evalDist (f x) y)) -> 
    rel v (evalDist (Bind c f) y).

  intuition.
  simpl.
  eapply trans.
  2:{
    eapply rel_sumList_compat;
    intuition.
    eapply mult_proper.
    eapply refl.
    eapply eqRat_refl.
    eapply H1.
    trivial.
  }
  
  specialize (rel_sumList_factor_r_r (evalDist c) (getSupport c) v H); intuition.

  eapply trans.
  2:{
    eapply H2.
  }
  eapply refl.
  rewrite evalDist_lossless.
  symmetry.
  eapply ratMult_1_l.
  trivial.
Qed.


Theorem evalDist_iso : 
  forall rel (A B C D : Set) (f : C -> D) (f_inv : D -> C) 
    (d : Comp D) (c : Comp C) (f1 : D -> Comp B) 
    (f2 : C -> Comp A) (a : A) (b : B),
    RatRel rel ->
    (forall x : D, In x (getSupport d) -> f (f_inv x) = x) ->
    (forall x : C, In x (getSupport c) -> f_inv (f x) = x) ->
    (forall x : D, In x (getSupport d) -> In (f_inv x) (getSupport c)) ->
    (forall x : C, In x (getSupport c) -> evalDist d (f x) == evalDist c x) ->
    (forall x : C,
      In x (getSupport c) -> rel (evalDist (f1 (f x)) b) (evalDist (f2 x) a)) ->
    rel (evalDist (x <-$ d; f1 x) b) (evalDist (x <-$ c; f2 x) a).

  intuition.
  eapply trans.
  eapply refl.
  eapply (distro_iso_eq); intros.
  eapply H0.
  trivial.
  eapply H1.
  eauto.
  eapply H2.
  eauto.

  eapply H3.
  trivial.
  eapply eqRat_refl.

  eapply rel_seq;
  intuition.

Qed.

Theorem evalDist_seq : 
forall rel (A1 A2 B : Set) (c1 c2 : Comp B) (f1 : B -> Comp A1)(f2 : B -> Comp A2) y z,
  RatRel rel ->
  (forall x : B, evalDist c1 x == evalDist c2 x) ->
  (forall x : B,
    In x (getSupport c1) -> rel (evalDist (f1 x) y) (evalDist (f2 x) z)) ->
  rel (evalDist (x <-$ c1; f1 x) y) (evalDist (x <-$ c2; f2 x) z).

  intuition.
  eapply (evalDist_iso (fun b => b)(fun b => b)); intuition.

  eapply getSupport_In_evalDist.
  intuition.
  eapply getSupport_In_evalDist.
  eauto.
  rewrite H0.
  trivial.
  eapply H1.
  eapply getSupport_In_evalDist.
  intuition.
  eapply getSupport_In_evalDist.
  eauto.
  rewrite <- H0.
  trivial.

Qed.



Theorem oc_comp_invariant : 
  forall (A B C : Set)(c : OracleComp A B C)(S : Set)(P : S -> Prop)
    (eqds : EqDec S)
    (o : S -> A -> Comp (B * S))(s : S),
    (forall a b c d, In (a, b) (getSupport (o c d)) -> P c -> P b) ->
      P s ->
      forall a b, In (a, b) (getSupport (c _ _ o s)) -> P b.
  
  Opaque getSupport.
  induction c; intuition; simpl in *.
  eapply H; eauto.

  Transparent getSupport.
  repeat simp_in_support.
  destruct x. 
  simpl in *.

  specialize (IHc (S * S0) (fun x => P (snd x)) _ 
  (fun (x : S * S0) (y : A) =>
                p <-$ (o (fst x) y) S0 eqds o0 (snd x);
                ret (fst (fst p), (snd (fst p), snd p))) (s, s0))%type.
  eapply IHc; intros.
  3:{
    eapply H3.
  }
  repeat simp_in_support.
  simpl.
  destruct c1.
  destruct x.
  eapply H.
  eapply H0.
  eapply H4. 
  eapply H5.
  trivial.

  repeat simp_in_support.
  trivial.

  repeat simp_in_support.
  destruct x.
  eapply H.
  eapply H0.
  eapply IHc.
  eapply H0.
  eapply H1.
  eauto.
  eauto.
Qed.

Theorem oc_comp_invariant_f : 
  forall (A B C : Set)(c : OracleComp A B C)(S : Set)(f : S -> bool)
    (eqds : EqDec S)
    (o : S -> A -> Comp (B * S))(s : S),
    (forall a b c d, In (a, b) (getSupport (o c d)) -> f c = true -> f b = true) ->
    f s = true ->
    forall a b, In (a, b) (getSupport (c _ _ o s)) -> f b = true.
  
  intuition.
  eapply (@oc_comp_invariant _ _ _ _ _ (fun x => f x = true)); intuition.
  eapply H.
  eapply H2.
  eapply H3.
  eapply H0.
  eapply H1.
Qed.



Theorem distro_irr_le
     : forall (A B : Set) (c : Comp A) (f : A -> Comp B) 
         (y : B) (v : Rat),
       (forall x : A, In x (getSupport c) -> (evalDist (f x) y) <=  v) ->
       (evalDist (x <-$ c; f x) y)  <= v.

  intuition.
  simpl.
  rewrite sumList_le.
  2:{
    intuition.
    rewrite H at 1.
    eapply leRat_refl.
    trivial.
  }
  rewrite sumList_factor_constant_r.
  eapply leRat_trans.
  eapply ratMult_leRat_compat.
  eapply evalDist_sum_le_1.
  eapply leRat_refl.
  rewrite ratMult_1_l.
  intuition.
Qed.

Theorem oc_comp_wf : 
  forall (A B C : Set)(c : OracleComp A B C),
    well_formed_oc c ->
    forall (S : Set)(eqds : EqDec S)(o : S -> A -> Comp (B * S))(s : S),
      (forall a b, well_formed_comp (o a b)) ->
      well_formed_comp (c _ _ o s).

  induction 1; intuition; simpl in *; intuition. 
  eapply well_formed_Bind; intuition.

  eapply IHwell_formed_oc; intuition.
  eapply well_formed_Bind; intuition.
  eapply well_formed_Ret.
  eapply well_formed_Ret.

  eapply well_formed_Bind; intuition.
  eapply well_formed_Ret.

  eapply well_formed_Bind; intuition.
  destruct b.
  eauto.
  
Qed.


Theorem repeat_fission : 
  forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(c : Comp A)(P : A -> bool)(f : A -> Comp B) x,
    well_formed_comp c ->
    (exists a, In a (filter P (getSupport c))) ->
    (forall a, In a (getSupport c) -> well_formed_comp (f a)) ->
    evalDist (a <-$ Repeat c P; b <-$ f a; ret (a, b)) x ==
    evalDist
      (Repeat (a <-$ c; b <-$ f a; ret (a, b)) (fun p => P (fst p))) x.

  intuition.

  case_eq (P a); intuition.

  simpl.
  symmetry.
  rewrite <- sumList_factor_constant_l.

  symmetry.
  rewrite (@sumList_subset' A (EqDec_dec _ ) _ (getSupport c)).
  
  eapply sumList_body_eq; intuition.
  unfold indicator.
  simpl.
  rewrite H2.
  case_eq (P a0); intuition.
  repeat rewrite ratMult_1_l.
  rewrite <- ratMult_assoc.
  eapply ratMult_eqRat_compat; intuition.
  eapply ratMult_eqRat_compat; intuition.
  eapply ratInverse_eqRat_compat.
  eapply sumList_nz.
  econstructor; intuition.
  eapply filter_In; intuition; eauto.
  eapply getSupport_In_evalDist;
  eauto.

  symmetry.

  assert ((getUnique
           (flatten
              (map
                 (fun b0 : A =>
                  getUnique
                    (flatten
                       (map (fun b1 : B => (b0, b1) :: nil)
                          (getSupport (f b0))))
                    (bind_eq_dec (f b0) (fun b1 : B => ret (b0, b1))))
                 (getSupport c)))
           (bind_eq_dec c (fun a1 : A => b0 <-$ f a1; ret (a1, b0)))) =
           (flatten
              (map
                 (fun b0 : A =>
                    (map (fun b1 : B => (b0, b1))
                         (getSupport (f b0))))
                 (getSupport c)))).


  rewrite DetSem.getUnique_NoDup_eq.
  f_equal.
  eapply map_ext; intuition.

  rewrite flatten_map_eq.
  rewrite DetSem.getUnique_NoDup_eq.
  intuition.

  eapply map_NoDup; intuition.
  assert (snd (a1, a2) = a2).
  trivial.
  eauto.
  eapply getSupport_NoDup.

  eapply flatten_NoDup;
    intuition.
  
  eapply map_NoDup'; intuition.
  eapply getSupport_NoDup.

  repeat rewrite flatten_map_eq in *.

  edestruct (@well_formed_val_exists _ (f a1)).
  intuition.

  eapply (getUnique_eq_inv (a1, x)) in H8.
  apply in_map_iff in H8.
  destruct H8.
  intuition.
  pairInv.
  intuition.
  eapply in_map_iff.
  econstructor.
  intuition.

  apply in_map_iff in H5.
  destruct H5.
  intuition.
  subst.
  eapply getUnique_NoDup.

  eapply in_map_iff in H5.
  destruct H5.
  intuition.
  eapply in_map_iff in H6.
  destruct H6.
  intuition.
  subst.
  repeat rewrite flatten_map_eq in *.
  eapply app_NoDup; intuition.
  eapply getUnique_NoDup.
  eapply getUnique_NoDup.

  apply in_getUnique_if in H5.
  apply in_getUnique_if in H6.
  apply in_map_iff in H5.
  apply in_map_iff in H6.
  destruct H5.
  destruct H6.
  intuition.
  subst.
  pairInv.
  intuition.

  apply in_getUnique_if in H5.
  apply in_getUnique_if in H6.
  apply in_map_iff in H5.
  apply in_map_iff in H6.
  destruct H5.
  destruct H6.
  intuition.
  subst.
  pairInv.
  intuition.

  rewrite H5.
  clear H5.

  rewrite sumList_filter_twice.
  eapply sumList_body_eq; intuition.
  apply filter_In in H5; intuition.
  eapply eqRat_trans.
  eapply sumList_body_eq; intuition.
  rewrite (@sumList_exactly_one _ a1) at 1.
  eapply eqRat_refl.
  eapply getSupport_NoDup.
  intuition.
  intuition.
  eapply eqRat_trans.
  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  eapply sumList_0; intuition.
  destruct (EqDec_dec (pair_EqDec eqda eqdb) (b0, a3) (a1, a2)).
  pairInv.
  intuition.
  eapply ratMult_0_r.
  eapply ratMult_0_r.
  eapply eqRat_trans.
  eapply sumList_body_eq; intuition.
  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  eapply (@sumList_exactly_one _ a2); intuition.
  eapply getSupport_NoDup.
  destruct (EqDec_dec (pair_EqDec eqda eqdb) (a1, b0) (a1, a2)).
  pairInv.
  intuition.
  eapply ratMult_0_r.
  
  rewrite sumList_factor_constant_l.
  symmetry.
  rewrite <- ratMult_1_r at 1.
  eapply ratMult_eqRat_compat; intuition.
  symmetry.
  eapply eqRat_trans.
  eapply sumList_body_eq; intuition.
  destruct (EqDec_dec (pair_EqDec eqda eqdb) (a1, a2) (a1, a2)).
  eapply ratMult_1_r.
  congruence.
  eapply evalDist_lossless.
  intuition.

  repeat rewrite ratMult_0_l.
  symmetry.
  rewrite ratMult_1_l.
  eapply eqRat_trans.
  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  eapply sumList_0; intuition.
  destruct (EqDec_dec (pair_EqDec eqda eqdb) (a0, a1) (a, b)).
  pairInv.
  congruence.
  eapply ratMult_0_r.
  repeat rewrite ratMult_0_r.
  intuition.
  eapply filter_NoDup.
  eapply getSupport_NoDup.
  eapply getSupport_NoDup.

  intuition.
  apply filter_In in H3; intuition.
  
  intuition.
  unfold indicator.
  case_eq (P a0); intuition.
  exfalso.
  eapply H4.
  eapply filter_In; intuition.
  repeat rewrite ratMult_0_l.
  intuition.

  destruct H0.
  eapply evalDist_irr_l; intuition.
  eapply well_formed_Repeat.
  unfold eq_dec; intuition.
  eapply (EqDec_dec _).
  trivial.
  eauto.

  eapply evalDist_irr_l; intuition.
  simpl in *.
  apply filter_In in H3.
  intuition.

  simpl in *.
  apply filter_In in H3.
  intuition.
  destruct (EqDec_dec (pair_EqDec eqda eqdb) (x0, x1) (a, b)).
  pairInv.
  congruence.

  unfold indicator.
  simpl.
  rewrite H2.
  repeat rewrite ratMult_0_l.
  intuition.
Qed.

Lemma evalDistRepeat_sup_0 : 
  forall (A : Set)(c : Comp A)(P : A -> bool) x,
    evalDist c x == 0 ->
    evalDist (Repeat c P) x == 0.
  
  intuition.
  simpl.
  rewrite H.
  rewrite ratMult_0_r.
  intuition.
  
Qed.

Lemma evalDistRepeat_pred_0 : 
  forall (A : Set)(c : Comp A)(P : A -> bool) x,
    P x = false ->
    evalDist (Repeat c P) x == 0.
  
  intuition.
  simpl.
  unfold indicator.
  rewrite H.
  repeat rewrite ratMult_0_l.
  intuition.
  
Qed.

Theorem repeat_snd_equiv : 
  forall (A B : Set)(eqd : EqDec B)(c : Comp (A * B))(P : B -> bool) x,
    evalDist (p <-$ Repeat c (fun p => P (snd p)); ret (snd p)) x ==
    evalDist (Repeat (p <-$ c; ret (snd p)) P) x.
  
  intuition.
  
  simpl.
  case_eq (P x); intuition.
  
  unfold indicator.
  rewrite H.
  rewrite ratMult_1_l.
  rewrite <- sumList_factor_constant_l.
  
  symmetry.
  rewrite (sumList_filter_partition (fun p : A * B => P (snd p))).
  symmetry.
  rewrite ratAdd_0_r.
  eapply ratAdd_eqRat_compat.
  eapply sumList_body_eq; intuition.
  apply filter_In in H0; intuition.
  rewrite H2.
  destruct (EqDec_dec eqd (snd a) x).
  rewrite ratMult_1_l.
  repeat rewrite ratMult_1_r.
  eapply ratMult_eqRat_compat; intuition.
  
  rewrite flatten_map_eq.
  eapply ratInverse_eqRat_compat.
  intuition.
  destruct a.
  simpl in *.
  subst.
  eapply sumList_nz; eauto.
  exists (a, x).
  intuition.
  eapply filter_In; intuition.
  eapply getSupport_In_evalDist; eauto.
  
  rewrite sumList_comm.
  symmetry.
  rewrite (sumList_filter_partition (fun p : A * B => P (snd p))).
  symmetry.
  rewrite ratAdd_0_r.
  eapply ratAdd_eqRat_compat.
  eapply sumList_body_eq; intuition.
  apply filter_In in H0; intuition.
  rewrite sumList_factor_constant_l.
  rewrite <- ratMult_1_r at 1.
  eapply ratMult_eqRat_compat; intuition.
  symmetry.
  destruct a0.
  simpl in *.
  rewrite (@sumList_exactly_one _ b).
  destruct (EqDec_dec eqd b b); intuition.
  eapply filter_NoDup.
  eapply getUnique_NoDup.
  eapply filter_In; intuition.
  eapply in_getUnique.
  eapply in_map_iff.
  econstructor. split; eauto.
  simpl.
  trivial.

  intuition.
  destruct (EqDec_dec eqd b b0); subst; intuition.

  symmetry.
  eapply sumList_0.
  intuition.
  eapply sumList_0; intuition.
  apply filter_In in H3; intuition.
  apply filter_In in H0; intuition.
  destruct a0.
  simpl in *.
  destruct (EqDec_dec eqd b a1); subst.
  destruct (P a1); simpl in *; discriminate.
  eapply ratMult_0_r.
  
  repeat rewrite ratMult_0_r.
  intuition.
  
  symmetry.
  eapply sumList_0; intuition.
  eapply filter_In in H0; intuition.
  destruct (EqDec_dec eqd (snd a) x); subst.
  destruct (P (snd a)); simpl in *; discriminate.
  
  repeat rewrite ratMult_0_r.
  intuition.
  
  unfold indicator.
  rewrite H.
  repeat rewrite ratMult_0_l.
  eapply sumList_0; intuition.
  apply filter_In in H0.
  intuition.
  rewrite H2.
  rewrite ratMult_1_l.
  destruct a.
  simpl in *.
  destruct (EqDec_dec eqd b x); subst; try congruence.
  rewrite ratMult_0_r.
  intuition.
  
Qed.

Theorem repeat_fst_equiv : 
  forall (A B : Set)(eqd : EqDec A)(c : Comp (A * B))(P : A -> bool) x,
    evalDist (p <-$ Repeat c (fun p => P (fst p)); ret (fst p)) x ==
    evalDist (Repeat (p <-$ c; ret (fst p)) P) x.
  
  intuition.
  
  simpl.
  case_eq (P x); intuition.
  
  unfold indicator.
  rewrite H.
  rewrite ratMult_1_l.
  rewrite <- sumList_factor_constant_l.
  
  symmetry.
  rewrite (sumList_filter_partition (fun p : A * B => P (fst p))).
  symmetry.
  rewrite ratAdd_0_r.
  eapply ratAdd_eqRat_compat.
  eapply sumList_body_eq; intuition.
  apply filter_In in H0; intuition.
  rewrite H2.
  destruct (EqDec_dec eqd (fst a) x).
  rewrite ratMult_1_l.
  repeat rewrite ratMult_1_r.
  eapply ratMult_eqRat_compat; intuition.
  
  rewrite flatten_map_eq.
  eapply ratInverse_eqRat_compat.
  intuition.
  destruct a.
  simpl in *.
  subst.
  eapply sumList_nz; eauto.
  exists (x, b).
  intuition.
  eapply filter_In; intuition.
  eapply getSupport_In_evalDist; eauto.
  
  rewrite sumList_comm.
  symmetry.
  rewrite (sumList_filter_partition (fun p : A * B => P (fst p))).
  symmetry.
  rewrite ratAdd_0_r.
  eapply ratAdd_eqRat_compat.
  eapply sumList_body_eq; intuition.
  apply filter_In in H0; intuition.
  rewrite sumList_factor_constant_l.
  rewrite <- ratMult_1_r at 1.
  eapply ratMult_eqRat_compat; intuition.
  symmetry.
  destruct a0.
  simpl in *.
  rewrite (@sumList_exactly_one _ a0).
  destruct (EqDec_dec eqd a0 a0); intuition.
  eapply filter_NoDup.
  eapply getUnique_NoDup.
  eapply filter_In; intuition.
  eapply in_getUnique.
  eapply in_map_iff.
  econstructor. split; eauto.
  simpl.
  trivial.
  
  intuition.
  destruct (EqDec_dec eqd a0 b0); subst; intuition.
  
  symmetry.
  eapply sumList_0.
  intuition.
  eapply sumList_0; intuition.
  apply filter_In in H3; intuition.
  apply filter_In in H0; intuition.
  destruct a0.
  simpl in *.
  destruct (EqDec_dec eqd a0 a1); subst.
  destruct (P a1); simpl in *; discriminate.
  eapply ratMult_0_r.
  
  repeat rewrite ratMult_0_r.
  intuition.

  symmetry.
  eapply sumList_0; intuition.
  eapply filter_In in H0; intuition.
  destruct (EqDec_dec eqd (fst a) x); subst.
  destruct (P (fst a)); simpl in *; discriminate.
  
  repeat rewrite ratMult_0_r.
  intuition.
  
  unfold indicator.
  rewrite H.
  repeat rewrite ratMult_0_l.
  eapply sumList_0; intuition.
  apply filter_In in H0.
  intuition.
  rewrite H2.
  rewrite ratMult_1_l.
  destruct a.
  simpl in *.
  destruct (EqDec_dec eqd a x); subst; try congruence.
  rewrite ratMult_0_r.
  intuition.
  
Qed.

Theorem repeat_fission' : 
  forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(c : Comp A)(P1 : A -> bool)(P2 : B -> bool)(f : A -> Comp B) x,
    well_formed_comp c ->
    (exists a, In a (filter P1 (getSupport c))) ->
    (forall a, In a (getSupport c) -> well_formed_comp (f a)) -> 
    (forall a b, In a (getSupport c) -> In b (getSupport (f a)) -> (P1 a = P2 b)) ->
    evalDist (a <-$ Repeat c P1; f a) x ==
    evalDist
      (Repeat (a <-$ c; f a) P2) x.

  intuition.

  assert (evalDist (a <-$ Repeat c P1; f a) x  == 
          evalDist (z <-$ (a <-$ Repeat c P1; b <-$ f a; ret (a, b)); ret (snd z)) x).

  rewrite evalDist_assoc.
  eapply evalDist_seq_eq; intuition.
  rewrite evalDist_assoc.
  rewrite <- evalDist_right_ident.
  eapply evalDist_seq_eq; intuition.
  rewrite evalDist_left_ident.
  simpl.
  reflexivity.
  intuition.
  intuition.
  intuition.

  rewrite H3.
  clear H3.

  assert (evalDist (z <-$ (a <-$ Repeat c P1; b <-$ f a; ret (a, b)); ret snd z) x ==
          evalDist (z <-$ (Repeat (a <-$ c; b <-$ f a; ret (a, b)) (fun p => P1 (fst p))); ret snd z) x).

  eapply evalDist_seq_eq; intuition.
  eapply repeat_fission; intuition.
  rewrite H3.
  clear H3.

  assert (evalDist
     (z <-$
      Repeat (a <-$ c; b <-$ f a; ret (a, b)) (fun p : A * B => P1 (fst p));
      ret snd z) x == 
          evalDist
     (z <-$
      Repeat (a <-$ c; b <-$ f a; ret (a, b)) (fun p : A * B => P2 (snd p));
      ret snd z) x).
  
  eapply evalDist_seq_eq; intuition.
  destruct (in_dec (EqDec_dec _ ) a (getSupport c)).
  destruct (in_dec (EqDec_dec _) b (getSupport (f a))).
  case_eq (P1 a); intuition.

  eapply evalDist_Repeat_eq; intuition.
  eapply filter_In; intuition.
  eapply getSupport_In_Seq; eauto.
  eapply getSupport_In_Seq; eauto.
  simpl; intuition.

  eapply sumList_permutation.
  eapply NoDup_Permutation; intuition.
  eapply filter_NoDup.
  eapply getSupport_NoDup.
  eapply filter_NoDup.
  eapply getSupport_NoDup.

  apply filter_In in H4.
  intuition.
  repeat simp_in_support.
  eapply filter_In; intuition.
  eapply getSupport_In_Seq; eauto.
  eapply getSupport_In_Seq; eauto.
  simpl.
  intuition.
  simpl in *.
  erewrite <- H2; eauto.

  apply filter_In in H4.
  intuition.
  repeat simp_in_support.
  eapply filter_In; intuition.
  eapply getSupport_In_Seq; eauto.
  eapply getSupport_In_Seq; eauto.
  simpl.
  intuition.
  simpl in *.
  erewrite H2; eauto.

  assert (P2 b = false).
  erewrite <- H2; eauto.

  repeat rewrite evalDistRepeat_pred_0; intuition.

  repeat rewrite evalDistRepeat_sup_0; intuition;
  eapply getSupport_not_In_evalDist; intuition;
  repeat simp_in_support; intuition.

  repeat rewrite evalDistRepeat_sup_0; intuition;
  eapply getSupport_not_In_evalDist; intuition;
  repeat simp_in_support; intuition.

  rewrite H3.
  clear H3.

  rewrite repeat_snd_equiv.

  (* The following fact comes up a couple times. *)
  assert (forall a, 
             evalDist (p <-$ (a0 <-$ c; b <-$ f a0; ret (a0, b)); ret snd p) a ==
   evalDist (a0 <-$ c; f a0) a).
  intuition.
  rewrite evalDist_assoc; intuition.
  eapply evalDist_seq_eq; intuition.
  rewrite evalDist_assoc; intuition.
  symmetry.
  rewrite <- evalDist_right_ident.
  eapply evalDist_seq_eq; intuition.
  rewrite evalDist_left_ident; intuition.
  simpl.
  reflexivity.

  case_eq (P2 x); intuition.
  destruct (in_dec (EqDec_dec _) x (getSupport (Bind c f))).
  eapply evalDist_Repeat_eq; intuition.
  
  eapply filter_In; intuition.
  repeat simp_in_support.
  eapply getSupport_In_Seq.
  eapply getSupport_In_Seq; eauto.
  eapply getSupport_In_Seq; eauto.
  simpl.
  intuition.
  simpl.
  intuition.


  rewrite sumList_permutation.
  2:{
    eapply (evalDist_getSupport_filter_perm _ (a <-$ c; f a)); intuition.
  }

  eapply sumList_body_eq; intuition.
  
  repeat rewrite evalDistRepeat_sup_0; intuition;
  eapply getSupport_not_In_evalDist; intuition;
  repeat simp_in_support; intuition.
  eapply n.
  eapply getSupport_In_Seq; eauto.

  repeat rewrite evalDistRepeat_pred_0; intuition.
Qed.

Theorem prob_or_le_sum : 
  forall (c1 c2 : Comp bool),
    Pr[x1 <-$ c1;
        x2 <-$ c2;
        ret (x1 || x2)] <= Pr[c1] + Pr[c2].
  
  intuition.
  Local Transparent evalDist.
  simpl.
  rewrite (sumList_partition (fun x => x)).
  eapply ratAdd_leRat_compat.
  
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    eapply evalDist_right_ident.
  }
  simpl.
  eapply sumList_le.
  intuition.
  destruct a; simpl.
  destruct (EqDec_dec bool_EqDec true true).
  rewrite ratMult_1_r.
  eapply ratMult_leRat_compat; intuition.
  eapply leRat_trans.
  eapply sumList_le.
  intros.
  eapply eqRat_impl_leRat.
  eapply ratMult_1_r.
  eapply evalDist_sum_le_1.
  
  intuition.

  rewrite ratMult_0_r.
  eapply rat0_le_all.
  
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    eapply evalDist_right_ident.
  }
  simpl.
  eapply leRat_trans.
  eapply sumList_le.
  intros.
  eapply eqRat_impl_leRat.
  eapply eqRat_trans.
  eapply ratMult_eqRat_compat.
  symmetry.
  eapply sumList_factor_constant_l.
  reflexivity.
  symmetry.
  eapply sumList_factor_constant_r.
  rewrite sumList_summation.
  eapply sumList_le.
  intuition.
  destruct a.
  destruct (EqDec_dec bool_EqDec true true); intuition.
  
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply sumList_body_eq.
  intros.
  rewrite orb_true_r.
  destruct ( EqDec_dec bool_EqDec true true).
  rewrite ratMult_1_r at 1.
  rewrite ratMult_assoc at 1.
  rewrite ratMult_comm at 1.
  eapply ratMult_assoc.
  intuition.
  rewrite sumList_factor_constant_l.
  eapply ratMult_leRat_compat.
  intuition.
  eapply leRat_trans.
  eapply sumList_le.
  intros.
  assert ( (if a then 0 else 1) * evalDist c1 a <= evalDist c1 a).
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    eapply ratMult_1_l.
  }
  eapply ratMult_leRat_compat.
  destruct a;
    intuition.
  reflexivity.
  eapply H1.
  eapply evalDist_sum_le_1.
  
  destruct ( EqDec_dec bool_EqDec false true).
  discriminate.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply sumList_0.
  intuition.
  destruct a; simpl.
  repeat rewrite ratMult_0_r.
  intuition.
  destruct (EqDec_dec bool_EqDec false true ); try discriminate.
  repeat rewrite ratMult_0_r.
  eapply ratMult_0_l.
  
  eapply rat0_le_all.
Qed.

Theorem evalDist_orb_le : 
  forall (A : Set)(c : Comp A) f1 f2,
    Pr [x <-$ c; ret (f1 x || f2 x)] <=
    Pr[ x <-$ c; ret (f1 x)] + Pr[x <-$ c; ret (f2 x)].

  intuition.
  simpl.
  rewrite (sumList_partition f1).
  eapply ratAdd_leRat_compat.

  eapply sumList_le.
  intuition.
  rewrite ratMult_assoc.
  eapply ratMult_leRat_compat; intuition.
  destruct (f1 a); simpl.
  rewrite ratMult_1_r.
  reflexivity.
  rewrite ratMult_0_r.
  eapply rat0_le_all.

  eapply sumList_le.
  intuition.
  rewrite ratMult_assoc.
  eapply ratMult_leRat_compat; intuition.
  destruct (f1 a); simpl.
  rewrite ratMult_0_r.
  eapply rat0_le_all.
  rewrite ratMult_1_r.
  reflexivity.
  
Qed.