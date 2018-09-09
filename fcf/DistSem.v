(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* A denotational semantics for computations that relates every computation to a denotation. *)

Set Implicit Arguments.

Require Export fcf.Comp.
Require Export fcf.Rat.
Require Import fcf.Fold.
Require Import List.
Require Import fcf.Blist.
Require Import Omega.
Require Import fcf.StdNat.
Require Import fcf.NotationV1.
 
 
Local Open Scope list_scope.
Local Open Scope rat_scope.

Ltac simp_in_support := 
  unfold setLet in *;
  match goal with
    | [H : In _ (getSupport (Bind _ _)) |- _ ] =>
      apply getSupport_Bind_In in H; destruct_exists; intuition
    | [H : In _ (getSupport (if ?t then _ else _)) |- _ ] => let x := fresh "x" in remember t as x; destruct x
    | [H : In _ (getSupport (ret _)) |- _ ] => apply getSupport_In_Ret in H; try pairInv; subst
(*     | [H : false = inRange _ _ |- _] => symmetry in H *)
    | [H : true = negb ?t |- _ ] => let x := fresh "x" in remember t as x; destruct x; simpl in H; try discriminate
  end.

(* evalDist is a denotational semantics that produces a distribution instead of a value. *)

Definition Distribution(A : Set) := A -> Rat.

Definition indicator(A : Set)(P : A -> bool) :=
  fun a => if (P a) then rat1 else rat0.

Fixpoint evalDist(A : Set)(c : Comp A) : Distribution A :=
  match c with
    | Ret eqd a => fun a' => if (eqd a a') then 1 else 0
    | Bind c1 c2 => fun a => 
      sumList (getSupport c1) (fun b => (evalDist c1 b) * (evalDist (c2 b) a))
    | Rnd n => fun v => 1 / (expnat 2 n)
    | Repeat c P => fun a => (indicator P a) * (ratInverse (sumList (filter P (getSupport c)) (evalDist c))) * (evalDist c a)
  end.

Definition dist_sem_eq(A : Set)(c1 c2 : Comp A) :=
  forall a, (evalDist c1 a) == (evalDist c2 a).

Definition Support(A : Set)(ls : list A)(d : Distribution A) :=
  NoDup ls /\
  (forall a, In a ls <-> ~((d a) == 0)).

Lemma getSupport_NoDup : forall (A : Set)(c : Comp A),
  NoDup (getSupport c).

  destruct c; intuition; simpl in *.

  econstructor.
  apply in_nil.
  econstructor.

  eapply getUnique_NoDup.

  eapply getAllBvectors_NoDup.

  eapply filter_NoDup.
  eapply getSupport_NoDup.

Qed.

Lemma filter_not_In : forall (A : Set)(ls : list A)(P : A -> bool) a,
                        (~In a ls) \/ P a = false <->
                        ~In a (filter P ls).
  
    intuition.
    eapply H1.
    eapply filter_In; eauto.
    assert (P a = true -> False).
    intuition.
    congruence.
    eapply H.
    eapply filter_In; eauto.
    
    case_eq (P a); intuition.
    left.
    intuition.
    eapply H.
    eapply filter_In; eauto.
    
Qed.

Theorem getSupport_In_evalDist : forall (A : Set)(c : Comp A)(a : A),
  In a (getSupport c) <-> ~(evalDist c a == 0).

  induction c; simpl in *; intuition.
  subst.
  destruct (e a0 a0).
  eapply rat1_ne_rat0.
  trivial.
  congruence.

  destruct (e a a0); subst.
  intuition.
  right.
  intuition.

  apply in_getUnique_if in H0.
  apply in_flatten in H0.

  destruct H0.
  intuition.
  apply in_map_iff in H2.
  destruct H2.
  intuition.

  eapply sumList_0 in H1; eauto.
  apply ratMult_0 in H1; intuition.
  eapply IHc; eauto.
  subst.
  eapply H; eauto.

  apply (in_getUnique (flatten (map (fun b : B => getSupport (c0 b)) (getSupport c)))).
  apply in_flatten.
  apply sumList_nz in H0.
  destruct H0.
  intuition.
  apply ratMult_nz in H2.
  intuition.
  econstructor.
  split.
  eapply in_map_iff.
  econstructor.
  split.
  eapply eq_refl.
  eapply H1.
  eapply H.
  eauto.

  eapply in_getAllBvectors.

  apply ratMult_0 in H0.
  intuition.
  apply ratMult_0 in H1.
  intuition.
  unfold indicator in *.
  case_eq (b a); intuition.
  rewrite H1 in H0.
  eapply rat1_ne_rat0.
  trivial.

  eapply filter_not_In.
  eauto.
  eauto.

  eapply ratInverse_nz; eauto.
  eapply IHc.
  eapply filter_In.
  eauto.
  trivial.

  apply ratMult_nz in H.
  intuition.
  apply ratMult_nz in H0.
  intuition.
  unfold indicator in *.
  case_eq (b a); intuition;
  rewrite H0 in H.
  eapply filter_In.
  intuition.
  eapply IHc.
  trivial.
  exfalso.
  intuition.

Qed.

Theorem getSupport_not_In_evalDist_h : forall (A : Set)(c : Comp A)(a : A),
~In a (getSupport c) -> (evalDist c a == 0).

  induction c; intuition; simpl in *.
  intuition.
  destruct (e a a0); subst;
  intuition.

  eapply sumList_0.
  intuition.
  eapply ratMult_0.
  right.
  eapply H.
  intuition.
  eapply H0.
  eapply (in_getUnique (flatten (map (fun b : B => getSupport (c0 b)) (getSupport c)))).
  eapply in_flatten.
  exists (getSupport (c0 a0)).
  intuition.
  eapply in_map_iff.
  exists a0.
  intuition.

  exfalso.
  eapply H.
  eapply in_getAllBvectors.

  apply filter_not_In in H.
  intuition.
  
  eapply ratMult_0.
  right.
  eauto.
  
  eapply ratMult_0.
  left.
  unfold indicator.
  rewrite H0.
  rewrite ratMult_0_l.
  intuition.  
Qed.

Theorem getSupport_not_In_evalDist : forall (A : Set)(c : Comp A)(a : A),
  ~In a (getSupport c) <-> (evalDist c a == 0).

  intuition.

  eapply getSupport_not_In_evalDist_h.
  intuition.

  eapply getSupport_In_evalDist; eauto.
Qed.

Theorem getSupport_correct : forall (A : Set)(c : Comp A),
  Support (getSupport c)(evalDist c).

  intuition.
  econstructor.
  eapply getSupport_NoDup.
  
  apply getSupport_In_evalDist.
  
Qed.


(* We use evalDist as the probability measure.  Instead of supplying an event on the return type, we expect the computation to test for the occurrence of the event.  *)
Notation "'Pr' [ c  ] " := (evalDist c true) (at level 20).


Lemma evalDist_sum_bind_eq : forall (A B : Set)(eqdb : eq_dec B)(eqda : eq_dec A)(c1 : Comp B)(c2 : B -> Comp A),
  sumList (getSupport (Bind c1 c2)) (evalDist (Bind c1 c2)) ==
  sumList (getSupport c1) (fun b => evalDist c1 b * (sumList (getSupport (c2 b)) (evalDist (c2 b)))).
  
  intuition. simpl.
  eapply eqRat_trans.
  eapply sumList_comm.
  eapply sumList_body_eq; intuition.
  
  eapply eqRat_trans.
  eapply sumList_factor_constant_l.
  eapply ratMult_eqRat_compat; intuition.
  
  eapply eqRat_symm.
  eapply sumList_subset; intuition.
  eapply getSupport_NoDup.
  eapply getUnique_NoDup.
  eapply (in_getUnique (flatten (map (fun b : B => getSupport (c2 b)) (getSupport c1)))).
  eapply in_flatten.
  econstructor.
  split.
  eapply in_map_iff.
  econstructor.
  split.
  eapply eq_refl.
  eauto.
  eauto.
  
  eapply getSupport_not_In_evalDist.
  eauto.
Qed.
  
(*
Lemma evalDist_sum_repeat_eq : forall (A : Set)(eqda : eq_dec A)(c : Comp A) P,
  let scale := (ratInverse (sumList (filter P (getSupport c)) (evalDist c))) in 
  sumList (getSupport (Repeat c P)) (evalDist (Repeat c P)) ==
  sumList (filter P (getSupport c1)) (fun b => scale * evalDist c1 b * (sumList (getSupport (c2 b)) (evalDist (c2 b)))).

  intuition. simpl.
  eapply eqRat_trans.
  eapply sumList_comm.
  eapply sumList_body_eq; intuition.
  
  eapply eqRat_trans.
  eapply sumList_factor_constant_l.
  eapply ratMult_eqRat_compat; intuition.
  
  eapply eqRat_symm.
  eapply sumList_subset; intuition.
  eapply getSupport_NoDup.
  eapply getUnique_NoDup.
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
  
  eapply getSupport_not_In_evalDist.
  eauto.

Qed.
*)

Lemma ratInverse_scale_sum_1 : forall (A : Set)(ls : list A)(f : A -> Rat),
  (forall a, In a ls -> ~f a == 0) ->
  length ls > O ->
  sumList ls (fun a => (ratInverse (sumList ls f)) * (f a)) == 1.
  
  intuition.
  rewrite sumList_factor_constant_l.
  eapply ratInverse_prod_1.
  intuition.
  destruct ls; simpl in *.
  omega.
  eapply sumList_0 in H1.
  eapply H.
  eauto.
  eauto.
  simpl.
  eauto.
  
Qed.

Lemma evalDist_lossless : forall (A : Set)(c : Comp A),
  well_formed_comp c ->
  sumList (getSupport c) (evalDist c) == 1.
  
  induction 1; intuition; simpl in *.
  unfold sumList; simpl in *.
  destruct (pf a a); intuition.
  rewrite <- ratAdd_0_l.
  intuition.    
  
  eapply eqRat_trans.
  apply evalDist_sum_bind_eq.
  eapply comp_eq_dec; eauto.
  eapply bind_eq_dec; eauto.
  eapply eqRat_trans.
  eapply sumList_body_eq.
  intuition.
  apply ratMult_eqRat_compat.
  apply eqRat_refl.
  apply H1.
  trivial.
  eapply eqRat_trans.
  eapply sumList_body_eq; intuition.
  apply ratMult_1_r.
  trivial.
 
  rewrite sumList_body_const.
  rewrite getAllBvectors_length.
  rewrite <- ratMult_num_den.
  rewrite mult_1_l.
  eapply num_dem_same_rat1.

  rewrite posnatMult_1_r.
  unfold posnatToNat, natToPosnat.
  trivial.

  eapply eqRat_trans.
  eapply sumList_body_eq.
  intuition.
  eapply ratMult_eqRat_compat.
  assert (P a = true).
  eapply filter_In; eauto.
  unfold indicator.
  rewrite H2.
  eapply ratMult_1_l.
  eapply eqRat_refl.
  eapply ratInverse_scale_sum_1.
  intuition.
  eapply getSupport_In_evalDist.
  eapply filter_In.
  eapply H1.
  trivial.
  destruct (filter P (getSupport c)); simpl in *; intuition.

Qed.

Lemma sumList_filter_evalDist_le_1 : forall (A : Set)(c : Comp A)(P : A -> bool) a,
  well_formed_comp c ->
  In a (filter P (getSupport c)) ->
  1 <= sumList (filter (fun a' => negb (P a')) (getSupport c)) (evalDist c) ->
  False.
  
  intuition.
  assert (sumList (filter (fun a0 : A => negb (P a0)) (getSupport c)) (evalDist c) == 1).
  eapply leRat_impl_eqRat; trivial.
  eapply leRat_trans.
  eapply sumList_filter_le.
  rewrite evalDist_lossless.
  intuition.
  trivial.
  
  rewrite <- evalDist_lossless in H2; eauto.
  rewrite (sumList_filter_partition P (getSupport c)) in H2.
  symmetry in H2.
  rewrite ratAdd_comm in H2.
  apply ratAdd_arg_0 in H2.
  eapply sumList_0 in H2; eauto.
  eapply getSupport_In_evalDist.
  eapply filter_In; eauto.
  trivial.
Qed.


Theorem sumList_support_bool : 
  forall (c : Comp bool),
    sumList (getSupport c) (evalDist c) ==
    evalDist c true + evalDist c false.
  
  intuition.
  rewrite (sumList_filter_partition (eqb true)).
  eapply ratAdd_eqRat_compat.
  
  destruct (eq_Rat_dec (Pr[c]) 0).
  rewrite e.
  eapply sumList_0.
  intuition.
  apply filter_In in H.
  intuition.
  rewrite eqb_leibniz in H1.
  subst.
  trivial.
  
  eapply sumList_exactly_one.
  eapply filter_NoDup.
  eapply getSupport_NoDup.
  eapply filter_In.
  intuition.
  eapply getSupport_In_evalDist.
  intuition.
  eapply eqb_leibniz.
  trivial.
  intuition.
  eapply filter_In in H.
  intuition.
  rewrite eqb_leibniz in H2.
  subst.
  intuition.
  
  destruct (eq_Rat_dec (evalDist c false) 0).
  rewrite e.
  eapply sumList_0.
  intuition.
  eapply filter_In in H.
  intuition.
  destruct a.
  rewrite eqb_refl in H1.
  simpl in *.
  discriminate.
  trivial.
  
  eapply sumList_exactly_one.
  eapply filter_NoDup.
  eapply getSupport_NoDup.
  eapply filter_In.
  intuition.
  eapply getSupport_In_evalDist.
  intuition.
  case_eq (eqb true false); intuition.
  rewrite eqb_leibniz in H.
  discriminate.
  
  intuition.
  eapply filter_In in H.
  intuition.
  destruct b.
  rewrite eqb_refl in H2.
  simpl in *.
  discriminate.
  intuition.
Qed.
  

Lemma evalDist_sum_le_1 : forall (A : Set)(c : Comp A),
  sumList (getSupport c) (evalDist c) <= 1.
 
  induction c; intuition; simpl in *.
  unfold sumList; simpl in *.
  destruct (e a a); intuition.
  rewrite <- ratAdd_0_l.
  intuition.    
  
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  apply evalDist_sum_bind_eq.
  eapply comp_eq_dec; eauto.
  eapply bind_eq_dec; eauto.
  eapply leRat_trans.
  eapply sumList_le.
  intuition.
  apply ratMult_leRat_compat.
  apply leRat_refl.
  apply H.
  eapply leRat_trans.
  eapply sumList_le; intuition.
  eapply eqRat_impl_leRat.
  eapply ratMult_1_r.
  trivial.
 
  rewrite sumList_body_const.
  rewrite getAllBvectors_length.
  rewrite <- ratMult_num_den.
  rewrite mult_1_l.
  eapply eqRat_impl_leRat.
  eapply num_dem_same_rat1.

  rewrite posnatMult_1_r.
  unfold posnatToNat, natToPosnat.
  trivial.

  destruct (gt_dec (length (filter b (getSupport c))) 0).

  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply sumList_body_eq.
  intuition.
  eapply ratMult_eqRat_compat.
  assert (b a = true).
  eapply filter_In; eauto.

  unfold indicator.
  rewrite H0.
  eapply ratMult_1_l.
  eapply eqRat_refl.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply ratInverse_scale_sum_1.
  intuition.
  eapply getSupport_In_evalDist.
  eapply filter_In.
  eapply H.
  trivial.
  trivial.
  intuition.

  destruct (filter b (getSupport c)); simpl in *.
  unfold sumList.
  simpl.
  eapply rat0_le_all.

  omega.
Qed.

Lemma evalDist_le_1 : forall (A : Set)(c : Comp A) a,
  evalDist c a <= 1.

  intuition.
  eapply leRat_trans.
  2:{
    eapply (@evalDist_sum_le_1 _ c).
  }
  pose proof (comp_EqDec c).
  destruct (in_dec (EqDec_dec _) a (getSupport c)).
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    rewrite (sumList_partition (eqb a)).
    eapply ratAdd_eqRat_compat.
    eapply sumList_exactly_one.
    eapply getSupport_NoDup.
    eauto.
    intuition.
    case_eq (eqb a b); intuition.
    exfalso.
    eapply H1.
    eapply eqb_leibniz.
    trivial.
    eapply ratMult_0_r.
    eapply eqRat_refl.
  }
  
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply ratAdd_0_r.
  eapply ratAdd_leRat_compat.
  rewrite eqb_refl.
  
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eapply ratMult_1_r.
  }
  intuition.
  
  eapply rat0_le_all.
  
  apply getSupport_not_In_evalDist in n.
  rewrite n.
  eapply rat0_le_all.
Qed.

Theorem evalDist_complement : 
  forall (c : Comp bool),
    well_formed_comp c ->
    evalDist c false == ratSubtract 1 (Pr[c]).
  
  intuition.
  eapply (@ratAdd_add_same_l _ (Pr[c])).
  rewrite ratSubtract_ratAdd_inverse_2.
  rewrite <- sumList_support_bool.
  eapply evalDist_lossless.
  trivial.
  
  eapply evalDist_le_1.
Qed.


Theorem evalDist_le_1_gen : 
  forall (A : Set)(eqd : EqDec A)(c : Comp A)(ls : list A),
    NoDup ls ->
    sumList ls (evalDist c) <= 1.
  
  intuition.
  eapply leRat_trans.
  eapply eqRat_impl_leRat.
  eapply (sumList_filter_partition (fun a => if (in_dec (EqDec_dec _) a (getSupport c)) then true else false)).
  
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    symmetry.
    eapply ratAdd_0_r.
  }
  eapply ratAdd_leRat_compat.
  
  eapply leRat_trans.
  eapply sumList_subset_le.
  intuition.
  eapply filter_NoDup.
  trivial.
  eapply (getSupport_NoDup c).
  intuition.
  eapply filter_In in H0.
  intuition.
  destruct (in_dec (EqDec_dec eqd) a (getSupport c)); intuition.
  discriminate.
  eapply evalDist_sum_le_1.

  eapply eqRat_impl_leRat.
  eapply sumList_0.
  intuition.
  eapply filter_In in H0.
  intuition.
  destruct (in_dec (EqDec_dec eqd) a (getSupport c)).
  simpl in *.
  discriminate.
  eapply getSupport_not_In_evalDist.
  trivial.
  
Qed.

Theorem evalDist_1_0 : 
  forall (A : Set){eqd : EqDec A}(c : Comp A) a,
    well_formed_comp c ->
    evalDist c a == 1 ->
      (forall b, b <> a -> evalDist c b == 0).
  
  intuition.
  eapply leRat_impl_eqRat.
  
  eapply (leRat_ratAdd_same_r (evalDist c a)).
  eapply leRat_trans.
  2:{
    eapply eqRat_impl_leRat.
    rewrite H0.
    eapply ratAdd_0_l.
  }
  
  assert ( evalDist c b + evalDist c a ==
    sumList (a :: b :: nil)%list (evalDist c)).
  repeat rewrite sumList_cons.
  rewrite ratAdd_comm.
  eapply ratAdd_eqRat_compat; intuition.
  rewrite ratAdd_0_r at 1.
  eapply ratAdd_eqRat_compat; intuition.
  unfold sumList; simpl; intuition.
  
  rewrite H2.
  eapply evalDist_le_1_gen; intuition.
  econstructor.
  simpl; intuition.
  econstructor; simpl; intuition.
  econstructor.
  
  eapply rat0_le_all.
  
Qed.
   
Local Open Scope comp_scope.

Theorem EqDec_pair_l 
  : forall (A B : Set)(eqd : EqDec (A * B))(b : B),
    EqDec A.

  intuition.
  exists (fun a1 a2 => eqb (a1, b) (a2, b)).
  intuition.
  rewrite eqb_leibniz in H.
  inversion H; intuition.
  subst.
  eapply eqb_refl.
Qed.

Fixpoint evalDist_OC(A B C: Set)(c : OracleComp A B C): forall(S : Set), EqDec S -> (S -> A -> Comp (B * S)) -> S -> Comp (C * S) :=
  match c in (OracleComp A B C) return (forall(S : Set), EqDec S -> (S -> A -> Comp (B * S)) -> S -> Comp (C * S))
    with
    | @OC_Query A' B' a => 
      fun (S : Set)(eqds : EqDec S)(o : S -> A' -> Comp (B' * S))(s : S) =>  
        o s a
    | @OC_Run A'' B'' C' A' B' S' eqds' eqda'' eqdb'' c' o' s' =>
      fun (S : Set)(eqds : EqDec S)(o : S -> A' -> Comp (B' * S))(s : S) =>
      p <-$ evalDist_OC c' (pair_EqDec eqds' eqds) (fun x y => p <-$ evalDist_OC (o' (fst x) y) _ o (snd x); ret (fst (fst p), (snd (fst p), snd p))) (s', s);
      Ret 
      (EqDec_dec (pair_EqDec (pair_EqDec 
        (oc_EqDec c' (fun x => fst (oc_base_exists (o' s' x) (fun y => fst (comp_base_exists (o s y))))) (fun x => EqDec_pair_l (oc_EqDec (o' s' x) (fun y => fst (comp_base_exists (o s y))) (fun y => EqDec_pair_l (comp_EqDec (o s y)) s)) s' ))
        _) _ ))
      (fst p, fst (snd p), snd (snd p))

    | @OC_Ret A' B' C' c => 
      fun (S : Set)(eqds : EqDec S)(o : S -> A' -> Comp (B' * S))(s : S) =>
      x <-$ c; Ret 
      (EqDec_dec (pair_EqDec (comp_EqDec c) _ ))
      (x, s)
    | @OC_Bind A' B' C' C'' c' f' =>
      fun (S : Set)(eqds : EqDec S)(o : S -> A' -> Comp (B' * S))(s : S) =>
      [z, s'] <-$2 evalDist_OC c' _ o s;
      evalDist_OC (f' z) _ o s'
  end.

Coercion evalDist_OC : OracleComp >-> Funclass.


Inductive well_formed_oc : forall (A B C : Set), OracleComp A B C -> Prop :=
| well_formed_OC_Query :
  forall (A B : Set)(a : A),
    well_formed_oc (OC_Query B a)
| well_formed_OC_Run : 
  forall (A B C A' B' S : Set)
  (eqds : EqDec S)(eqdb : EqDec B)(eqda : EqDec A)(c : OracleComp A B C)
  (o : S -> A -> OracleComp A' B' (B * S))(s : S),
  well_formed_oc c ->
  (forall s a, well_formed_oc (o s a)) ->
  well_formed_oc (OC_Run eqds eqdb eqda c o s)
| well_formed_OC_Ret : 
  forall (A B C : Set)(c : Comp C),
      well_formed_comp c ->
      well_formed_oc (OC_Ret A B c)
| well_formed_OC_Bind : 
  forall (A B C C' : Set)(c : OracleComp A B C)(f : C -> OracleComp A B C'),
    well_formed_oc c ->
    (forall c, well_formed_oc (f c)) ->
    well_formed_oc (OC_Bind c f).

Local Open Scope nat_scope.

Definition in_oc_support(A B C : Set)(x : C)(c : OracleComp A B C) :=
  exists (S : Set)(eqds : EqDec S)(o : S -> A -> Comp (B * S))(s s' : S),
    In (x, s') (getSupport (c _ _ o s)).

Inductive queries_at_most : forall (A B C : Set), OracleComp A B C -> nat -> Prop :=
| qam_Bind : 
  forall (A B C C' : Set)(c : OracleComp A B C')(f : C' -> OracleComp A B C) q1 q2,
    queries_at_most c q1 ->
    (forall c',
      in_oc_support c' c ->
       queries_at_most (f c') q2) ->
    queries_at_most (OC_Bind c f) (q1 + q2)
| qam_Query : 
  forall (A B : Set)(a : A),
  queries_at_most (OC_Query B a) 1
| qam_Ret : 
  forall (A B C : Set)(c : Comp C),
    queries_at_most (OC_Ret A B c) 0
| qam_Run :
  forall (A A' B B' C S : Set)(eqds : EqDec S)(eqda : EqDec A)(eqdb : EqDec B)
    (c : OracleComp A B C)(oc : S -> A -> OracleComp A' B' (B * S)) s q1 q2,
    queries_at_most c q1 ->
    (forall s a, queries_at_most (oc s a) q2) ->
    queries_at_most (OC_Run _ _ _ c oc s) (q1 * q2)
| qam_le : 
  forall (A B C : Set)(c : OracleComp A B C) q1 q2,
    queries_at_most c q1 ->
    q1 <= q2 ->
    queries_at_most c q2.

