(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import VST.msl.base.
Require Import VST.msl.knot.
Require Import VST.msl.ageable.
Require Import VST.msl.sepalg.
Require Import VST.msl.sepalg_generators.
Require Import VST.msl.sepalg_functors.
Require Import VST.msl.age_sepalg.
Require Import VST.msl.knot_lemmas.
Require Import VST.msl.functors.
Require Import VST.msl.sepalg_functors.
Require Import VST.msl.knot_hered.

Import CovariantFunctor.
Import CovariantFunctorLemmas.
Import CovariantFunctorGenerator.

(* This file specializes knot to have T = Prop *)

Local Open Scope nat_scope.

(*
  We get these from knot_hered and knot_hered_sa.

Module Type TY_FUNCTOR_PROP.
  Parameter F : Type -> Type.
  Parameter f_F : functor F.
  EXisting Instance f_F.

  Parameter other : Type.
End TY_FUNCTOR_PROP.

Module Type TY_FUNCTOR_SA_PROP.
  Declare Module TF:TY_FUNCTOR_PROP.
  Import TF.

  Parameter saf_F : safunctor f_F.
  EXisting Instance saf_F.
End TY_FUNCTOR_SA_PROP.
*)

Module Type KNOT_PROP.
  Declare Module TF:TY_FUNCTOR_PROP.
  Import TF.

  Parameter knot : Type.

  Parameter ag_knot : ageable knot.
  Existing Instance ag_knot.
  Existing Instance ag_prod.

  Definition predicate := (knot * other) -> Prop.

  Parameter squash : (nat * F predicate) -> knot.
  Parameter unsquash : knot -> (nat * F predicate).

  Definition approx (n:nat) (p:predicate) : predicate :=
     fun w => level w < n /\ p w.

  Axiom squash_unsquash : forall x, squash (unsquash x) = x.
  Axiom unsquash_squash : forall n x', unsquash (squash (n,x')) = (n, fmap F (approx n) x').

  Axiom knot_level : forall k:knot,
    level k = fst (unsquash k).

  Axiom knot_age1 : forall k:knot,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.
End KNOT_PROP.

(* Coercion *)
Module TyFunctorProp2TyFunctor (TF : TY_FUNCTOR_PROP) <: TY_FUNCTOR.
(*  EXport TFP. Does not seem to work? *)
  Definition F := TF.F.
  Definition T: Type := Prop.
  Definition T_bot : T := False.

  Definition other := TF.other.
End TyFunctorProp2TyFunctor.

Module KnotProp (TF':TY_FUNCTOR_PROP) : KNOT_PROP with Module TF:=TF'.
  Module TF := TF'.

  Module TF_G := TyFunctorProp2TyFunctor(TF).

  Module Knot_G := Knot(TF_G).

  Import TF.
  Definition knot : Type := Knot_G.knot.
  Definition predicate := (knot * other) -> Prop.

  Definition squash : (nat * F predicate) -> knot :=
    Knot_G.squash.
  Definition unsquash : knot -> (nat * F predicate) :=
    Knot_G.unsquash.

  Definition ag_knot := Knot_G.ag_knot.
  Existing Instance ag_knot.
  Existing Instance ag_prod.

  Definition approx (n:nat) (p:predicate) : predicate :=
     fun w => level w < n /\ p w.

  Lemma squash_unsquash : forall x, squash (unsquash x) = x.
  Proof.
    apply Knot_G.squash_unsquash.
  Qed.

  Lemma unsquash_squash : forall n x', unsquash (squash (n,x')) = (n,fmap F (approx n) x').
  Proof.
    replace approx with Knot_G.approx.
    apply Knot_G.unsquash_squash.
    extensionality n p w.
    unfold approx, Knot_G.approx, TF_G.T_bot.
    case (le_gt_dec n (level w)); intro; apply prop_ext; firstorder.
    unfold knot, TF_G.other, ag_knot in *. omega.
  Qed.

  Definition knot_level := Knot_G.knot_level.
  Definition knot_age1 := Knot_G.knot_age1.
End KnotProp.

(* Coercion *)
Module KnotProp2Knot (TF' : TY_FUNCTOR_PROP)
                                   (K : KNOT_PROP with Module TF := TF') <:
                                     KNOT.
  Module TF := TyFunctorProp2TyFunctor(K.TF).
  Import TF.

  Definition knot : Type := K.knot.
  Definition predicate := (knot * other) -> T.

  Definition ag_knot : ageable knot :=
    K.ag_knot.
  Existing Instance ag_knot.
  Existing Instance ag_prod.

  Definition squash : (nat * F predicate) -> knot :=
    K.squash.
  Definition unsquash : knot -> (nat * F predicate) :=
    K.unsquash.

  Definition approx (n:nat) (p:predicate) : predicate :=
     fun w => if le_gt_dec n (level w) then T_bot else p w.

  Lemma squash_unsquash : forall x, squash (unsquash x) = x.
  Proof.
    apply K.squash_unsquash.
  Qed.

  Lemma unsquash_squash : forall n x', unsquash (squash (n,x')) = (n,fmap F (approx n) x').
  Proof.
    replace approx with K.approx.
    apply K.unsquash_squash.
    extensionality n p w.
    unfold approx, K.approx, TF.T_bot.
    case (le_gt_dec n (level w)); intro; apply prop_ext; firstorder.
    unfold knot, ag_knot, other in *.
    omega.
  Qed.


  Definition knot_level := K.knot_level.
  Definition knot_age1 := K.knot_age1.
End KnotProp2Knot.

Module KnotProp_Lemmas (K:KNOT_PROP).
  Import K.
  Import K.TF.

  Module K' := KnotProp2Knot(K.TF)(K).
  Module KL := Knot_Lemmas(K').

  Lemma unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Proof.
    intros.
    rewrite <- (squash_unsquash k1).
    rewrite <- (squash_unsquash k2).
    rewrite H.
    trivial.
  Qed.
  Arguments unsquash_inj [k1 k2] _.

  Lemma squash_surj : forall k, exists n, exists Fp,
    squash (n, Fp) = k.
  Proof.
    intros.
    remember (unsquash k).
    destruct p as [n f].
    exists n.
    exists f.
    rewrite Heqp.
    rewrite squash_unsquash.
    trivial.
  Qed.

  Lemma unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = fmap F (approx n) Fp.
  Proof.
    intros.
    generalize H; intro.
    rewrite <- (squash_unsquash k) in H.
    rewrite H0 in H.
    rewrite unsquash_squash in H.
    inversion H.
    rewrite H2.
    symmetry.
    trivial.
  Qed.
  Arguments unsquash_approx [k n Fp] _.

  Lemma approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).
  Proof.
    intros.
    extensionality p x; destruct x as [k o].
    unfold approx, compose; simpl.
    apply prop_ext; intuition.
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    intros.
    extensionality p x; destruct x as [k o].
    unfold approx, compose; simpl.
    apply prop_ext; intuition.
  Qed.

  (* These are provided since sometimes it is tedious to break things out;
      they are not interesting except as engineering artifacts. *)
  Lemma unsquash_squash_unfolded : forall nf,
    unsquash (squash nf) = (fst nf, fmap F (approx (fst nf)) (snd nf)).
  Proof.
    intros.
    destruct nf.
    apply unsquash_squash.
  Qed.
	
  Lemma unsquash_approx_unfolded : forall k,
    unsquash k = (fst (unsquash k), fmap F (approx (fst (unsquash k))) (snd (unsquash k))).
  Proof.
    intros.
    case_eq (unsquash k); intros.
    simpl.
    apply injective_projections; simpl; trivial.
    apply (unsquash_approx H).
  Qed.

End KnotProp_Lemmas.
