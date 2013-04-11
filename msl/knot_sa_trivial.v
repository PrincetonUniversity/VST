(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require Import msl.sepalg.
Require Import msl.sepalg_generators.
Require Import msl.functors.
Require Import msl.sepalg_functors.
Require Import msl.knot.
Require Import msl.knot_sa.
Require Import msl.knot_hered.
Require Import msl.knot_hered_sa.
Require Import msl.knot_prop.

Module Trivial_TyFunctorSaProp (TF':TY_FUNCTOR_PROP) <: TY_FUNCTOR_SA_PROP.
  Module TF:=TF'.
  Import TF.

  Instance Join_F A : Join (F A) := Join_equiv (F A).
  Definition Perm_F: Perm_paf f_F Join_F := fun (A : Type) _ _ => Perm_equiv (F A).
  Definition Sep_F: Sep_paf f_F Join_F := fun (A : Type) _ _ _ => Sep_equiv (F A).
  Definition Canc_F: Canc_paf f_F Join_F := fun (A : Type) _ _ _ => Canc_equiv (F A).
  Definition Disj_F: Disj_paf f_F Join_F := fun (A : Type) _ _ _ => Disj_equiv (F A).

(*  Implicit Arguments Sep_F. *)

  Lemma fmap_hom : forall A B (f:A->B), join_hom (fmap f).
  Proof.
    unfold join_hom; intuition; auto.
    simpl in H; destruct H; subst.
    compute; auto.
  Qed.

  Lemma F_preserves_unmaps_left : forall A B (f : A -> B) ,
    unmap_left _ _  (fmap f).
  Proof.
    repeat intro.
    simpl in H; destruct H; subst.
    exists z; exists z.
    split. split; trivial.
    split; auto.
  Qed.
  Implicit Arguments F_preserves_unmaps_left.

  Lemma F_preserves_unmaps_right : forall A B (f : A -> B) ,
    unmap_right _ _ (fmap f).
  Proof.
    repeat intro.
    simpl in H; destruct H; subst.
    exists x; exists x.
    split. split; trivial.
    split; auto.
  Qed.
  Implicit Arguments F_preserves_unmaps_right.
 
  Instance paf_F: pafunctor f_F.
  Proof.
    constructor.
    apply fmap_hom.
    apply F_preserves_unmaps_left.
    apply F_preserves_unmaps_right.
  Qed.
 

End Trivial_TyFunctorSaProp.
