(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* An operation that returns a (uniformly distributed) random element from a list *)

Set Implicit Arguments.

Require Import fcf.FCF.

Section RndListElem.

  Variable A : Set.
  Hypothesis eqd : EqDec A.

  Local Open Scope list_scope.

  Definition rndListElem(ls : list A) : Comp (option A) :=
    match (length ls) with
      | O => ret None
      | S _ =>
        i <-$ [0 .. (length ls));
          ret (nth_option ls i)
    end.

  Theorem rndListElem_wf :
    forall (ls : list A),
      well_formed_comp (rndListElem ls).
       
    intuition.
    unfold rndListElem.
    case_eq (length ls); intuition; wftac.
  Qed.

End RndListElem.

Local Open Scope list_scope.

Theorem nth_option_In : 
  forall (A : Set)(ls : list A)(a : A) i,
    nth_option ls i = Some a ->
    In a ls.

  induction ls; intuition; simpl in *.
  discriminate.

  destruct i.
  inversion H; clear H; subst.
  intuition.
  right.
  eapply IHls.
  eauto.

Qed.

Fixpoint firstIndexOf(A : Set)(eqd : eq_dec A)(ls : list A)(a : A)(def : nat) :=
  match ls with
      | nil => def
      | a' :: ls' =>
        if (eqd a a') then O else (S (firstIndexOf eqd ls' a def))
  end.

Theorem firstIndexOf_in_lt : 
  forall (A : Set)(eqd : eq_dec A)(ls : list A)(a : A)(def : nat),
    In a ls ->
    firstIndexOf eqd ls a def < length ls.

  induction ls; intuition; simpl in *;
  intuition.
  
  subst.
  destruct (eqd a0 a0); subst.
  omega.
  intuition.

  destruct (eqd a0 a); subst.
  omega.

  eapply lt_n_S.
  eauto.
Qed.

Theorem nth_firstIndexOf : 
  forall (A : Set)(eqd : eq_dec A)(ls : list A)(a : A)(def : nat),
    In a ls ->
    nth_option ls (firstIndexOf eqd ls a def) = Some a.

  induction ls; intuition; simpl in *.
  intuition.

  intuition.
  subst.
  destruct (eqd a0 a0); subst; intuition.
  
  destruct (eqd a0 a); subst; intuition.

Qed.

Lemma rndListElem_support: 
  forall (A : Set)(eqd : EqDec A)(ls : list A) a,
    In a ls <-> 
    In (Some a) (getSupport (rndListElem eqd ls)).

  intuition.
  unfold rndListElem.
  case_eq (length ls); intuition.
  exfalso.
  destruct ls; simpl in *; intuition.
  
  eapply getSupport_In_Seq.

  eapply in_getSupport_RndNat.


  rewrite <- H0.
  eapply firstIndexOf_in_lt; eauto.
  simpl.
  left.

  eapply nth_firstIndexOf; trivial.
  
  unfold rndListElem in *.
  repeat simp_in_support.
  discriminate.
  
  eapply nth_option_In; eauto.

  Grab Existential Variables.
  apply O.
  unfold eq_dec.
  eapply (EqDec_dec eqd).
Qed.

Theorem nth_firstIndexOf_if : 
  forall (A : Set)(eqd : eq_dec A)(ls : list A) n a,
    nth_option ls n = Some a ->
    NoDup ls ->
    firstIndexOf eqd ls a 0 = n.

  induction ls; intuition; simpl in *.
  discriminate.
  inversion H0; clear H0; subst.
  destruct n.
  inversion H; clear H; subst.
  destruct (eqd a0 a0); subst; intuition.

  destruct (eqd a0 a); subst; intuition.
  exfalso.
  eapply H3.
  
  eapply nth_option_In.
  eauto.

Qed.

Theorem nth_option_some : 
  forall (A : Set)(ls : list A) n,
    n < length ls ->
    exists a, nth_option ls n = Some a.
  
  induction ls; intuition; simpl in *.
  omega.
  
  destruct n.
  econstructor; eauto.
  
  destruct (IHls n).
  omega.
  
  econstructor; eauto.
  
Qed.

Theorem rndListElem_support_None : 
  forall (A : Set) eqd (ls : list A),
    In None (getSupport (rndListElem eqd ls)) <->
    ls = nil.

  intuition.
  unfold rndListElem in *.
  case_eq (length ls); intuition.
  destruct ls; simpl in *; trivial; discriminate.

  rewrite H0 in H.
  repeat simp_in_support.
  apply RndNat_support_lt in H1.
  
  edestruct (nth_option_some ls); eauto.
  rewrite H0.
  eauto.
  congruence.

  subst.
  simpl.
  intuition.

Qed.

Theorem rndListElem_uniform : 
  forall (A : Set)(eqd : EqDec A)(ls : list A)(a1 a2 : option A),
    NoDup ls ->
    In a1 (getSupport (rndListElem _ ls)) ->
    In a2 (getSupport (rndListElem _ ls)) ->
    evalDist (rndListElem _ ls) a1 ==
    evalDist (rndListElem _ ls) a2.
  
  intuition.
  
  destruct a1.
  destruct a2.
  
  rewrite <- rndListElem_support in *.

  unfold rndListElem.
  case_eq (length ls); intuition.
  destruct ls; simpl in *. intuition. omega.
  
  eapply comp_spec_impl_eq.
  
  eapply comp_spec_seq.
  apply (Some a).
  apply (Some a).
  eapply eq_impl_comp_spec.
  eapply well_formed_RndNat.
  omega.
  eapply well_formed_RndNat.
  omega.
  eapply RndNat_uniform.
  3:{
    intros.
    simpl in H5.

    eapply comp_spec_ret.
    assert (a1 = (firstIndexOf (EqDec_dec _) ls a 0) <->
      b = (firstIndexOf (EqDec_dec _) ls a0 0)).
    eapply H5.
    clear H5.
    intuition; subst.
  
    rewrite H5.
    eapply nth_firstIndexOf; trivial.

    symmetry.
    eapply nth_firstIndexOf_if; intuition.

    rewrite H7.
    eapply nth_firstIndexOf; trivial.
    symmetry.
    eapply nth_firstIndexOf_if; intuition.
  }
  
  rewrite <- H2.
  apply firstIndexOf_in_lt; trivial.

  rewrite <- H2.
  apply firstIndexOf_in_lt; trivial.

  apply rndListElem_support in H0.
  
  apply rndListElem_support_None in H1.
  subst.
  simpl in *.
  intuition.

  
  destruct a2.
  apply rndListElem_support in H1.
  apply rndListElem_support_None in H0.
  subst.
  simpl in *.
  intuition.

  intuition.

Qed.

Lemma not_in_nth_option : 
  forall (A : Set)(ls : list A)(a : A)(i : nat),
    (~In a ls) ->
    nth_option ls i = Some a -> 
    False.

  induction ls; intuition; simpl in *.
  discriminate.

  destruct i.
  inversion H0; clear H0; subst.
  intuition.
  
  eapply IHls; eauto.

Qed.

Theorem nth_firstIndexOf_None : 
  forall (A : Set)(eqd : eq_dec A)(ls : list A),
    NoDup ls ->
    forall (a a' : A) i,
    In a ls ->
    i <> firstIndexOf eqd ls a O ->
    nth_option ls i = Some a' ->
    a <> a'.

  induction 1; intuition; simpl in *.
  intuition; subst.
  destruct (eqd a' a'); subst; intuition.
 
  destruct i; intuition.

  eapply not_in_nth_option; eauto.

  destruct i; intuition.
  inversion H3; clear H3; subst.
  destruct (eqd a' a'); subst; intuition.

  destruct (eqd a' x); subst; intuition.
  eapply IHNoDup; eauto.
Qed.

Lemma nth_option_not_None : 
  forall (A : Set)(ls : list A)(i : nat),
    i < length ls ->
    nth_option ls i = None ->
    False.

  induction ls; intuition; simpl in *.
  omega.

  destruct i.
  discriminate.
  assert (i < length ls).
  omega.
  eauto.

Qed.


Theorem rndListElem_uniform_gen : 
  forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(ls1 : list A)(ls2 : list B)(a1 :  A)(a2 : B),
    NoDup ls1 ->
    NoDup ls2 ->
    length ls1 = length ls2 ->
    In a1 ls1 ->
    In a2 ls2 ->
    comp_spec 
      (fun x y => x = Some a1 <-> y = Some a2)
      (rndListElem _ ls1) (rndListElem _ ls2).

  intuition.

  unfold rndListElem.
  case_eq (length ls1); intuition.
  rewrite <- H1.
  rewrite H4.

  eapply comp_spec_ret; intuition.
  discriminate.
  discriminate.
  
  rewrite <- H1.
  rewrite H4.

  eapply comp_spec_seq; try eapply None.
  eapply eq_impl_comp_spec.
  eapply well_formed_RndNat; omega.
  eapply well_formed_RndNat; omega.
  eapply (@RndNat_uniform  (firstIndexOf (EqDec_dec _) ls1 a1 O) (firstIndexOf (EqDec_dec _) ls2 a2 O)).

  rewrite <- H4.
  apply firstIndexOf_in_lt; trivial.
  rewrite <- H4.
  rewrite H1.
  apply firstIndexOf_in_lt; trivial.

  intuition.
  eapply comp_spec_ret.
  intuition.
  
  destruct (eq_nat_dec a (firstIndexOf (EqDec_dec _) ls1 a1 O)).
  subst.
  assert (b = firstIndexOf (EqDec_dec _) ls2 a2 0); intuition.
  subst.
  repeat rewrite nth_firstIndexOf; intuition.

  assert (b <> firstIndexOf (EqDec_dec _) ls2 a2 0).
  intuition.

  exfalso.
  eapply nth_firstIndexOf_None.
  eapply H.
  eapply H2.
  eapply n0.
  eauto.
  intuition.

  destruct (eq_nat_dec a (firstIndexOf (EqDec_dec _) ls1 a1 O)).
  subst.
  assert (b = firstIndexOf (EqDec_dec _) ls2 a2 0); intuition.
  subst.
  repeat rewrite nth_firstIndexOf; intuition.

  assert (b <> firstIndexOf (EqDec_dec _) ls2 a2 0).
  intuition.

  exfalso.
  eapply nth_firstIndexOf_None.
  eapply H0.
  eapply H3.
  eapply H10.
  eauto.
  intuition.
Qed.

Theorem rndListElem_support_exists : 
  forall (A : Set)(eqd : EqDec A)(ls : list A),
    exists x,
      In x (getSupport (rndListElem eqd ls)).

  destruct ls; intuition.
  econstructor.
  left.
  eauto.

  unfold rndListElem.
  unfold length.
  econstructor.
  eapply getSupport_In_Seq.

  eapply (@in_getSupport_RndNat O).
  omega.
  simpl.
  intuition.
Qed.

    (*

    Theorem rndListElem_uniform_remove_eq : 
      forall (A : Set)(eqd : EqDec A)(ls : list A)(a1 a2 : A),
        NoDup ls ->
        evalDist (rndListElem _ (removeFirst (EqDec_dec _) ls a1)) (Some a1) == 0.

      intuition.
      eapply getSupport_not_In_evalDist.
      intuition.
      rewrite <- rndListElem_support in H0.
      eapply removeFirst_NoDup_not_in; eauto.
    Qed.

    Notation "$ c1 " := (rndListElem _ c1%comp)
                          (right associativity, at level 89, c1 at next level) : comp_scope.

 Theorem rndListElem_support_exists : 
      forall (A : Set)(eqd : EqDec A)(ls : list A),
        exists x,
          In x (getSupport (rndListElem eqd ls)).

      destruct ls; intuition.
      econstructor.
      left.
      eauto.

      unfold rndListElem.
      unfold length.
      econstructor.
      eapply getSupport_In_Seq.

      eapply (@in_getSupport_RndNat O).
      omega.
      simpl.
      intuition.
    Qed.

*)