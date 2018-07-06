(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import VST.msl.base.
Require Import VST.msl.sig_isomorphism.
Require Import VST.msl.functors.
Require VST.msl.knot.
Require VST.msl.knot_full_variant.

Require Import VST.msl.ageable.
Require Import VST.msl.predicates_hered.

Module Type KNOT_INPUT__COCONTRAVARIANT_HERED_T_OTH_REL.
  Import CoContraVariantBiFunctor.
  Parameter F : functor.

  Parameter other : Type.

  Parameter Rel : forall A B, F A B -> F A B -> Prop.

  Parameter Rel_fmap : forall A B C D (f:A->B) (s:C->D) x y,
    Rel A D x y ->
    Rel B C (fmap F f s x) (fmap F f s y).
  Axiom Rel_refl : forall A B x, Rel A B x x.
  Axiom Rel_trans : forall A B x y z,
    Rel A B x y -> Rel A B y z -> Rel A B x z.

  Parameter ORel : other -> other -> Prop.
  Axiom ORel_refl : reflexive other ORel.
  Axiom ORel_trans : transitive other ORel.

  Parameter T:Type.
  Parameter T_bot:T.

  Parameter T_rel : T -> T -> Prop.
  Parameter T_rel_bot : forall x, T_rel T_bot x.
  Parameter T_rel_refl : forall x, T_rel x x.
  Parameter T_rel_trans : transitive T T_rel.

End KNOT_INPUT__COCONTRAVARIANT_HERED_T_OTH_REL.

Module Type KNOT__COCONTRAVARIANT_HERED_T_OTH_REL.
  Import CoContraVariantBiFunctor.
  Declare Module KI: KNOT_INPUT__COCONTRAVARIANT_HERED_T_OTH_REL.
  Import KI.

  Parameter knot:Type.
  Parameter ageable_knot : ageable knot.
  Existing Instance ageable_knot.

  Parameter hered : (knot * other -> T) -> Prop.
  Definition predicate := { p:knot * other -> T | hered p }.

  Parameter squash : (nat * F predicate predicate) -> knot.
  Parameter unsquash : knot -> (nat * F predicate predicate).

  Parameter approx : nat -> predicate -> predicate.

  Axiom squash_unsquash : forall k:knot, squash (unsquash k) = k.
  Axiom unsquash_squash : forall (n:nat) (f:F predicate predicate),
    unsquash (squash (n,f)) = (n, fmap F (approx n) (approx n) f).

  Axiom approx_spec : forall n p ko,
    proj1_sig (approx n p) ko =
     if (le_gt_dec n (level (fst ko))) then T_bot else proj1_sig p ko.

  Definition knot_rel (k1 k2:knot) :=
    let (n,f) := unsquash k1 in
    let (n',f') := unsquash k2 in
    n = n' /\ Rel predicate predicate f f'.

  Axiom knot_age1 : forall k:knot,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

  Axiom knot_level : forall k:knot,
    level k = fst (unsquash k).

  Axiom hered_spec : forall p,
    hered p =
    (forall k k' k'' o o',
      clos_refl_trans _ age k k' ->
      knot_rel  k' k'' ->
      ORel o o' ->
      T_rel (p (k,o)) (p (k'',o'))).

End KNOT__COCONTRAVARIANT_HERED_T_OTH_REL.

Module Type KNOT_INPUT__COVARIANT_HERED_PROP_OTH_REL.

  Import CovariantFunctor.
  Parameter F : functor.

  Parameter other : Type.

  Parameter Rel : forall A, F A -> F A -> Prop.
  Parameter Rel_fmap : forall A B (f:A->B) x y,
    Rel A x y -> Rel B (fmap F f x) (fmap F f y).

  Parameter Rel_unfmap : forall A B (f:A->B) x y,
    Rel B (fmap F f x) y ->
      exists y', Rel A x y' /\ fmap F f y' = y.

  Axiom Rel_refl : forall A x, Rel A x x.
  Axiom Rel_trans : forall A x y z,
    Rel A x y -> Rel A y z -> Rel A x z.

  Parameter ORel : other -> other -> Prop.
  Axiom ORel_refl : reflexive other ORel.
  Axiom ORel_trans : transitive other ORel.

End KNOT_INPUT__COVARIANT_HERED_PROP_OTH_REL.

Module Type KNOT__COVARIANT_HERED_PROP_OTH_REL.
  Import CovariantFunctor.
  Declare Module KI : KNOT_INPUT__COVARIANT_HERED_PROP_OTH_REL.
  Import KI.

  Parameter knot : Type.

  Parameter ageable_knot : ageable knot.
  Existing Instance ageable_knot.

  Definition ag_knot_other := ag_prod knot other ageable_knot.
  Existing Instance ag_knot_other.

  Parameter expandM : @modality (knot * other) ag_knot_other.
  Definition assert := { p:pred (knot * other) | boxy expandM p }.

  Parameter squash : (nat * F assert) -> knot.
  Parameter unsquash : knot -> (nat * F assert).

  Parameter approx : nat -> assert -> assert.
  Axiom approx_spec : forall n p k,
    proj1_sig (approx n p) k = (level (fst k) < n /\ proj1_sig p k).

  Axiom squash_unsquash : forall x,
    squash (unsquash x) = x.
  Axiom unsquash_squash : forall n x',
    unsquash (squash (n,x')) = (n, fmap F (approx n) x').

  (* Definition of the expandM modality *)

  Definition knot_rel (k1 k2:knot) :=
    let (n,f) := unsquash k1 in
    let (n',f') := unsquash k2 in
    n = n' /\ Rel assert f f'.

  Axiom expandM_spec : forall k k' o o',
    expandM (k,o) (k',o') = (knot_rel k k' /\ ORel o o').

  Axiom expandM_refl : reflexive _ expandM.
  Axiom expandM_trans : transitive _ expandM.
  Hint Resolve expandM_refl expandM_trans.

  (* Definitions of the "ageable" operations *)
  Axiom knot_level : forall (k:knot),
    level k = fst (unsquash k).

  Axiom knot_age1 : forall (k:knot),
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

End KNOT__COVARIANT_HERED_PROP_OTH_REL.

Module Type KNOT_INPUT__COVARIANT_HERED_PROP_OTH.

  Import CovariantFunctor.
  Parameter F : functor.
  Parameter other : Type.

End KNOT_INPUT__COVARIANT_HERED_PROP_OTH.

Module Type KNOT__COVARIANT_HERED_PROP_OTH.
  Declare Module KI : KNOT_INPUT__COVARIANT_HERED_PROP_OTH.
  Import CovariantFunctor.
  Import CovariantFunctorLemmas.
  Import KI.

  Parameter knot : Type.

  Parameter ageable_knot : ageable knot.
  Existing Instance ageable_knot.

  Definition ag_knot_other := ag_prod knot other ageable_knot.
  Existing Instance ag_knot_other.

  Parameter squash : (nat * F (pred (knot * other))) -> knot.
  Parameter unsquash : knot -> (nat * F (pred (knot * other))).

  Parameter approx : nat -> pred (knot * other) -> pred (knot * other).
  Axiom approx_spec : forall n p k,
    approx n p k = (level (fst k) < n /\ p k).

  Axiom squash_unsquash : forall x,
    squash (unsquash x) = x.
  Axiom unsquash_squash : forall n x',
    unsquash (squash (n,x')) = (n, fmap F (approx n) x').


  (* Definitions of the "ageable" operations *)
  Axiom knot_level : forall (k:knot),
    level k = fst (unsquash k).

  Axiom knot_age1 : forall (k:knot),
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.
(*
  Axiom unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Arguments unsquash_inj [k1 k2] _.

  Axiom squash_surj : forall k, exists n, exists Fp,
    squash (n, Fp) = k.

  Axiom unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = KI.fmap (approx n) Fp.
  Implicit Arguments unsquash_approx [k n Fp].

  Axiom approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).

  Axiom approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
*)
End KNOT__COVARIANT_HERED_PROP_OTH.


Module Type KNOT_INPUT__COVARIANT_HERED_PROP.

  Import CovariantFunctor.
  Parameter F : functor.

End KNOT_INPUT__COVARIANT_HERED_PROP.

Module Type KNOT__COVARIANT_HERED_PROP.
  Declare Module KI : KNOT_INPUT__COVARIANT_HERED_PROP.
  Import CovariantFunctor.
  Import CovariantFunctorLemmas.
  Import KI.

  Parameter knot : Type.

  Parameter ageable_knot : ageable knot.
  Existing Instance ageable_knot.

  Parameter squash : (nat * F (pred knot)) -> knot.
  Parameter unsquash : knot -> (nat * F (pred knot)).

  Parameter approx : nat -> pred knot -> pred knot.
  Axiom approx_spec : forall n p k,
    approx n p k = (level k < n /\ p k).

  Axiom squash_unsquash : forall x,
    squash (unsquash x) = x.
  Axiom unsquash_squash : forall n x',
    unsquash (squash (n,x')) = (n, fmap F (approx n) x').

  (* Definitions of the "ageable" operations *)
  Axiom knot_level : forall (k:knot),
    level k = fst (unsquash k).

  Axiom knot_age1 : forall (k:knot),
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.
(*
  (* Convenience lemmas, provable from the above interface *)
  Axiom unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Arguments unsquash_inj [k1 k2] _.

  Axiom squash_surj : forall k, exists n, exists Fp,
    squash (n, Fp) = k.

  Axiom unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = fmap (approx n) Fp.
  Implicit Arguments unsquash_approx [k n Fp].

  Axiom approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).

  Axiom approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
*)
End KNOT__COVARIANT_HERED_PROP.

Module Type KNOT_INPUT__MIXVARIANT_HERED_PROP.

  Import MixVariantFunctor.
  Parameter F : functor.

End KNOT_INPUT__MIXVARIANT_HERED_PROP.

Module Type KNOT__MIXVARIANT_HERED_PROP.
  Declare Module KI : KNOT_INPUT__MIXVARIANT_HERED_PROP.
  Import MixVariantFunctor.
  Import MixVariantFunctorLemmas.
  Import KI.

  Parameter knot : Type.

  Parameter ageable_knot : ageable knot.
  Existing Instance ageable_knot.

  Definition predicate := pred knot.
  Parameter squash : (nat * F (pred knot)) -> knot.
  Parameter unsquash : knot -> (nat * F (pred knot)).

  Parameter approx : nat -> pred knot -> pred knot.
  Axiom approx_spec : forall n p k,
    approx n p k = (level k < n /\ p k).

  Axiom squash_unsquash : forall x,
    squash (unsquash x) = x.
  Axiom unsquash_squash : forall n x',
    unsquash (squash (n,x')) = (n, fmap F (approx n) (approx n) x').

  (* Definitions of the "ageable" operations *)
  Axiom knot_level : forall (k:knot),
    level k = fst (unsquash k).

  Axiom knot_age1 : forall (k:knot),
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

End KNOT__MIXVARIANT_HERED_PROP.

Module Knot_CoContraVariantHeredTOthRel
  (KI': KNOT_INPUT__COCONTRAVARIANT_HERED_T_OTH_REL):
  KNOT__COCONTRAVARIANT_HERED_T_OTH_REL with Module KI:=KI'.

  Import MixVariantFunctor.
  Import MixVariantFunctorLemmas.
  Import GeneralFunctorGenerator.
  Module KI:=KI'.

  Module Input.

    Definition F : functor :=
      CoContraVariantBiFunctor_MixVariantFunctor KI.F.

    Definition other := KI.other.

    Definition Rel (A: Type): F A -> F A -> Prop :=
      KI.Rel A A.

    Definition Rel_fmap (A B: Type): forall (f1: A->B) (f2:B->A) x y,
      Rel A x y ->
      Rel B (fmap F f1 f2 x) (fmap F f1 f2 y) :=
    KI.Rel_fmap A B B A.

    Definition Rel_refl (A: Type): forall x, Rel A x x :=
      KI.Rel_refl A A.

    Definition Rel_trans (A: Type): forall x y z,
      Rel A x y -> Rel A y z -> Rel A x z :=
      KI.Rel_trans A A.

    Definition ORel: other -> other -> Prop := KI.ORel.
    Definition ORel_refl := KI.ORel_refl.
    Definition ORel_trans := KI.ORel_trans.

    Definition T := KI.T.
    Definition T_bot := KI.T_bot.

    Definition T_rel := KI.T_rel.
    Definition T_rel_bot := KI.T_rel_bot.
    Definition T_rel_refl := KI.T_rel_refl.
    Definition T_rel_trans := KI.T_rel_trans.

  End Input.

  Module K := knot_full_variant.Knot_MixVariantHeredTOthRel(Input).

  Definition knot: Type := K.knot.
  Definition ageable_knot: ageable knot := K.ageable_knot.
  Existing Instance ageable_knot.

  Definition hered : (knot * KI.other -> KI.T) -> Prop := K.hered.
  Definition predicate := { p:knot * KI.other -> KI.T | hered p }.

  Definition squash : (nat * KI.F predicate predicate) -> knot := K.squash.
  Definition unsquash : knot -> (nat * KI.F predicate predicate) := K.unsquash.

  Definition approx : nat -> predicate -> predicate := K.approx.

  Definition squash_unsquash : forall k:knot, squash (unsquash k) = k
    := K.squash_unsquash.
  Definition unsquash_squash : forall (n:nat) (f:KI.F predicate predicate),
    unsquash (squash (n,f)) =
     (n, CoContraVariantBiFunctor.fmap KI.F (approx n) (approx n) f)
    := K.unsquash_squash.

  Definition approx_spec : forall n p ko,
    proj1_sig (approx n p) ko =
     if (le_gt_dec n (level (fst ko))) then KI.T_bot else proj1_sig p ko
    := K.approx_spec.

  Definition knot_rel (k1 k2:knot) :=
    let (n,f) := unsquash k1 in
    let (n',f') := unsquash k2 in
    n = n' /\ KI.Rel predicate predicate f f'.

  Definition knot_age1 : forall k:knot,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end
    := K.knot_age1.

  Definition knot_level : forall k:knot,
    level k = fst (unsquash k)
    := K.knot_level.

  Definition hered_spec : forall p,
    hered p =
    (forall k k' k'' o o',
      clos_refl_trans _ age k k' ->
      knot_rel  k' k'' ->
      KI.ORel o o' ->
      KI.T_rel (p (k,o)) (p (k'',o')))
    := K.hered_spec.

End Knot_CoContraVariantHeredTOthRel.

Module KnotLemmas_CoContraVariantHeredTOthRel
  (K: KNOT__COCONTRAVARIANT_HERED_T_OTH_REL).
  Import CoContraVariantBiFunctor.
  Import K.KI.
  Import K.

  Lemma unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.unsquash_inj
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.
  Arguments unsquash_inj [k1 k2] _.

  Lemma squash_surj : forall k, exists n, exists Fp,
    squash (n, Fp) = k.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.squash_surj
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.

  Lemma unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = fmap F (approx n) (approx n) Fp.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.unsquash_approx
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.
  Arguments unsquash_approx [k n Fp] _.

  Lemma pred_ext : forall (p1 p2:predicate),
    (forall x, proj1_sig p1 x = proj1_sig p2 x) ->
    p1 = p2.
  Proof.
    intros.
    destruct p1 as [p1 Hp1]; destruct p2 as [p2 Hp2].
    simpl in *.
    assert (p1 = p2).
    extensionality x; auto.
    subst p2.
    replace Hp2 with Hp1; auto.
    apply proof_irr.
  Qed.

  Lemma approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).
  Proof.
    apply
     (@knot_full_variant.KnotLemmas2.approx_approx1
       (knot_full_variant.KnotLemmas2.Build_Input _ _ _ _ _ _ _ _
          pred_ext approx_spec)),
     (knot_full_variant.KnotLemmas2.Proof).
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas2.approx_approx2
       (knot_full_variant.KnotLemmas2.Build_Input _ _ _ _ _ _ _ _
          pred_ext approx_spec)),
     (knot_full_variant.KnotLemmas2.Proof).
  Qed.

End KnotLemmas_CoContraVariantHeredTOthRel.

Module Knot_CovariantHeredPropOthRel (KI':KNOT_INPUT__COVARIANT_HERED_PROP_OTH_REL)
  : KNOT__COVARIANT_HERED_PROP_OTH_REL with Module KI:=KI'.

  Module KI:=KI'.

  Module Input.
    Import MixVariantFunctor.
    Import MixVariantFunctorLemmas.
    Import GeneralFunctorGenerator.
    Definition F: functor :=
      GeneralFunctorGenerator.CovariantFunctor_MixVariantFunctor KI.F.

    Definition other := KI.other.

    Definition Rel (A: Type): F A -> F A -> Prop := KI.Rel A.

    Definition Rel_fmap (A B: Type): forall (f1: A->B) (f2:B->A) x y,
      Rel A x y ->
      Rel B (fmap F f1 f2 x) (fmap F f1 f2 y) :=
    fun f s => KI.Rel_fmap A B f.

    Definition Rel_refl (A: Type): forall x, Rel A x x := KI.Rel_refl A.

    Definition Rel_trans (A: Type): forall x y z,
      Rel A x y -> Rel A y z -> Rel A x z
      := KI.Rel_trans A.

    Definition ORel := KI.ORel.
    Definition ORel_refl := KI.ORel_refl.
    Definition ORel_trans := KI.ORel_trans.

    Definition T := Prop.
    Definition T_bot := False.

    Definition T_rel (x y:T) := x -> y.
    Lemma T_rel_bot : forall x, T_rel T_bot x.
    Proof.
      compute; intuition.
    Qed.

    Lemma T_rel_refl : forall x, T_rel x x.
    Proof.
      compute; intuition.
    Qed.

    Lemma T_rel_trans : transitive T T_rel.
    Proof.
      repeat intro; intuition.
    Qed.
  End Input.

  Import CovariantFunctor.
  Import CovariantFunctorLemmas.

  Module K0 := knot_full_variant.Knot_MixVariantHeredTOthRel(Input).
  Module KL0 := knot_full_variant.KnotLemmas_MixVariantHeredTOthRel(K0).

  Existing Instance K0.ageable_knot.

  Definition ag_knot_other := ag_prod K0.knot KI.other K0.ageable_knot.
  Existing Instance ag_knot_other.

  Definition expandR : relation (K0.knot * KI.other) :=
    fun x y => K0.knot_rel (fst x) (fst y) /\ KI.ORel (snd x) (snd y).

  Lemma valid_rel_expandR : valid_rel expandR.
  Proof.
    split; hnf; intros.
    destruct H0.
    destruct x as [xk xo].
    destruct y as [yk yo].
    simpl in *.
    hnf in H.
    hnf in H0.
    simpl in H.
    rewrite K0.knot_age1 in H.
    destruct (K0.unsquash yk) as [n f] eqn:?H; intros.
    destruct n; try discriminate.
    inv H.
    destruct z as [zk zo].
    simpl in H0.
    destruct (K0.unsquash zk) as [n0 f0] eqn:?H; intros.
    destruct H0; subst n0.
    simpl in H1.
    exists (K0.squash (n,f0),zo).
    split; simpl; auto.
    hnf; repeat rewrite K0.unsquash_squash; split; auto.
    apply Input.Rel_fmap; auto.
    hnf; simpl.
    rewrite K0.knot_age1.
    rewrite H.
    auto.

    destruct x as [xk xo].
    destruct y as [yk yo].
    destruct H.
    simpl in *.
    hnf in H0; simpl in H0.
    rewrite K0.knot_age1 in H0.
    destruct z as [zk zo]; simpl in *.
    destruct (K0.unsquash zk) as [n f] eqn:?H; intros.
    destruct n; try discriminate.
    inv H0.
    hnf in H.
    rewrite K0.unsquash_squash in H.
    destruct (K0.unsquash xk) as [n0 f0] eqn:?H; intros.
    destruct H; subst.
    destruct (KI.Rel_unfmap _ _ _ _ _ H3)
      as [z [? ?]].
    subst f0.
    exists (K0.squash (S n0,z),xo).
    hnf; simpl.
    rewrite K0.knot_age1.
    rewrite K0.unsquash_squash.
    f_equal.
    f_equal.
    apply KL0.unsquash_inj.
    rewrite K0.unsquash_squash.
    rewrite H0.
    f_equal.
    rewrite MixVariantFunctorLemmas.fmap_app.
    change (S n0) with (1 + n0).
    rewrite <- KL0.approx_approx1.
    auto.
    split; simpl; auto.
    hnf.
    rewrite H2.
    rewrite K0.unsquash_squash; split; auto.
    hnf.
    rewrite (KL0.unsquash_approx H2).
    apply KI.Rel_fmap; auto.
  Qed.

  Definition expandM : @modality (K0.knot * KI.other) ag_knot_other
    := exist _ expandR valid_rel_expandR.

  Lemma expandM_refl : reflexive _ expandM.
  Proof.
    repeat intro.
    split.
    hnf.
    destruct (K0.unsquash (fst x)); split; auto.
    apply KI.Rel_refl.
    apply KI.ORel_refl.
  Qed.

  Lemma expandM_trans : transitive _ expandM.
  Proof.
    simpl; unfold expandR;
      repeat intro; intuition.
    unfold K0.knot_rel in *.
    destruct (K0.unsquash (fst x)).
    destruct (K0.unsquash (fst y)).
    destruct (K0.unsquash (fst z)).
    intuition.
    eapply KI.Rel_trans; eauto.
    eapply KI.ORel_trans; eauto.
  Qed.

  Hint Resolve expandM_refl expandM_trans.

  Definition assert := { p:pred (K0.knot * KI.other) | boxy expandM p }.

  Module Output <: knot_full_variant.KNOT_FULL_OUTPUT with Module KI := Input.
    Module KI := Input.
    Module K0 := K0.
    Definition predicate: Type := assert.

    Lemma boxy_expand_spec: forall (p: pred (K0.knot*KI.other)),
      boxy expandM p <->
      (fun p: pred (K0.knot*KI.other) =>
         forall x y, expandR x y -> proj1_sig p x -> proj1_sig p y) p.
    Proof.
      intros.
      split; intro.
      + pose proof boxy_e _ _ H; auto.
      + pose proof boxy_i _ expandM expandM_refl H; auto.
    Qed.

    Lemma hered_hereditary : forall (p:K0.knot*KI.other -> Prop),
      K0.hered p <->
      (hereditary age p /\ (fun p:K0.knot*KI.other -> Prop => forall x y, expandR x y -> p x -> p y) p).
    Proof.
      intros; split; repeat intro.
      split; repeat intro.
      rewrite K0.hered_spec in H.
      revert H1.
      destruct a; destruct a'.
      hnf in H0; simpl in H0.
      case_eq (age1 k); intros;
        rewrite H1 in H0; try discriminate.
      inv H0.
      apply (H k k0 k0 o0 o0).
      apply rt_step; auto.
      hnf.
      destruct (K0.unsquash k0); split; auto.
      apply Input.Rel_refl.
      apply Input.ORel_refl.
      auto.

      rewrite K0.hered_spec in H.
      destruct H0.
      destruct x as [xk xo].
      destruct y as [yk yo].
      simpl in *.
      revert H1; apply (H xk xk yk xo yo); auto.

      rewrite K0.hered_spec; repeat intro.
      destruct H.
      cut (p (k',o)).
      apply H4.
      split; auto.
      revert H3.
      clear -H0 H; induction H0.
      apply H; hnf; simpl; auto.
      hnf in H0.
      rewrite H0; auto.
      auto.
      intuition.
    Qed.

    Definition pkp: bijection predicate K0.predicate :=
      (bij_sym (sig_sig_iff_bij hered_hereditary)) ooo
      (bij_sym (sig_sigsig_bij (hereditary age) _)) ooo
      (sig_sig_iff_bij boxy_expand_spec).

  End Output.

  Module K := knot_full_variant.KnotFull(Input)(Output).

  Definition knot := K.knot.
  Definition ageable_knot := K.ageable_knot.
  Definition squash: (nat * KI.F assert) -> knot := K.squash.
  Definition unsquash: knot -> (nat * KI.F assert) := K.unsquash.
  Definition approx: nat -> assert -> assert := K.approx.

  Lemma approx_spec : forall n p k,
    proj1_sig (approx n p) k = (level (fst k) < n /\ proj1_sig p k).
  Proof.
    intros.
    apply prop_ext.
    pose proof K.approx_spec n p k.
    match goal with
    | _: ?A = _ |- ?B <-> _ => change B with A
    end.
    rewrite H.
    match goal with
    | |- (if le_gt_dec _ ?A then _ else _) <-> (?B < _ /\ _) =>
            change B with A; remember A as TMP eqn:HHH; clear HHH
    end.
    destruct (le_gt_dec n TMP).
    + split.
      - intros [].
      - intros [? ?]; omega.
    + split.
      - intros; split; [omega | auto].
      - intros [? ?]; auto.
  Qed.

  Definition squash_unsquash := K.squash_unsquash.

  Definition unsquash_squash := K.unsquash_squash.

  Definition knot_age1 := K.knot_age1.

  Definition knot_level := K.knot_level.

  Definition knot_rel (k1 k2:knot) :=
    let (n,f) := unsquash k1 in
    let (n',f') := unsquash k2 in
    n = n' /\ KI.Rel assert f f'.

  Lemma expandM_spec : forall k k' o o',
    expandM (k,o) (k',o') = (K.knot_rel k k' /\ KI.ORel o o').
  Proof.
    intros.
    rewrite K.knot_rel_spec.
    apply prop_ext; intuition.
    + destruct H; simpl in *; auto.
    + destruct H; auto.
    + split; simpl; auto.
  Qed.

End Knot_CovariantHeredPropOthRel.

Module KnotLemmas_CovariantHeredPropOthRel
  (K: KNOT__COVARIANT_HERED_PROP_OTH_REL).

  Import CovariantFunctor.
  Import K.KI.
  Import K.

  Lemma unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.unsquash_inj
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.
  Arguments unsquash_inj [k1 k2] _.

  Lemma squash_surj : forall k, exists n, exists Fp,
    squash (n, Fp) = k.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.squash_surj
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.

  Lemma unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = fmap KI.F (approx n) Fp.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.unsquash_approx
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.
  Arguments unsquash_approx [k n Fp] _.

  Lemma pred_ext : forall (p1 p2: assert),
    (forall x, proj1_sig p1 x = proj1_sig p2 x) ->
    p1 = p2.
  Proof.
    intros.
    apply exist_ext'.
    apply pred_ext'.
    extensionality; auto.
  Qed.

  Lemma approx_spec': forall n p ko,
    proj1_sig (approx n p) ko =
    if (le_gt_dec n (level (fst ko))) then False else proj1_sig p ko.
  Proof.
    intros.
    rewrite approx_spec.
    apply prop_ext.
    destruct (le_gt_dec n (level (fst ko))).
    + split; [intros [? ?]; omega | intros []].
    + tauto.
  Qed.

  Lemma approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).
  Proof.
    apply
     (@knot_full_variant.KnotLemmas2.approx_approx1
       (knot_full_variant.KnotLemmas2.Build_Input _ _ _ _ _ assert
         (@proj1_sig _ _) _ pred_ext approx_spec')),
     (knot_full_variant.KnotLemmas2.Proof).
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas2.approx_approx2
       (knot_full_variant.KnotLemmas2.Build_Input _ _ _ _ _ assert
         (@proj1_sig _ _) _ pred_ext approx_spec')),
     (knot_full_variant.KnotLemmas2.Proof).
  Qed.

End KnotLemmas_CovariantHeredPropOthRel.

Module Knot_CovariantHeredPropOth (KI':KNOT_INPUT__COVARIANT_HERED_PROP_OTH)
  : KNOT__COVARIANT_HERED_PROP_OTH with Module KI:=KI'.

  Import MixVariantFunctor.
  Import MixVariantFunctorLemmas.
  Import GeneralFunctorGenerator.
  Module KI:=KI'.

  Module Input.
    Definition F: functor := CovariantFunctor_MixVariantFunctor KI.F.
    Definition other := KI.other.

    Definition Rel A := @eq (F A).
    Lemma Rel_fmap : forall A B (f:A -> B) (s:B -> A) x y,
      Rel A x y ->
      Rel B (fmap F f s x) (fmap F f s y).
    Proof.
      unfold Rel; intuition; subst; auto.
    Qed.

    Lemma Rel_refl : forall A x, Rel A x x.
    Proof.
      intros; hnf; auto.
    Qed.

    Lemma Rel_trans : forall A x y z,
      Rel A x y -> Rel A y z -> Rel A x z.
    Proof.
      unfold Rel; intuition congruence.
    Qed.

    Definition ORel := @eq other.
    Lemma ORel_refl : reflexive other ORel.
    Proof.
      hnf; unfold ORel; auto.
    Qed.
    Lemma ORel_trans : transitive other ORel.
    Proof.
      hnf; unfold ORel; intros; congruence.
    Qed.

    Definition T := Prop.
    Definition T_bot := False.

    Definition T_rel (x y:T) := x -> y.
    Lemma T_rel_bot : forall x, T_rel T_bot x.
    Proof.
      compute; intuition.
    Qed.

    Lemma T_rel_refl : forall x, T_rel x x.
    Proof.
      compute; intuition.
    Qed.

    Lemma T_rel_trans : transitive _ T_rel.
    Proof.
      hnf; unfold T_rel; intuition.
    Qed.
  End Input.

  Module K0 := knot_full_variant.Knot_MixVariantHeredTOthRel(Input).
  Module KL0 := knot_full_variant.KnotLemmas_MixVariantHeredTOthRel(K0).
  Existing Instance K0.ageable_knot.
  Definition ag_knot_other := ag_prod K0.knot KI.other K0.ageable_knot.
  Existing Instance ag_knot_other.

  Lemma hered_hereditary : forall (p: K0.knot*KI.other -> Prop),
    K0.hered p <-> hereditary age p.
  Proof.
    intros; split; repeat intro.
    rewrite K0.hered_spec in H.
    hnf in H0.
    simpl in H0.
    destruct a; destruct a'.
    simpl in *.
    case_eq (age1 k); intros.
    rewrite H2 in H0.
    inv H0.
    specialize ( H k k0 k0).
    specialize ( H o0 o0).
    spec H.
    apply rt_step; auto.
    spec H.
    hnf.
    destruct (K0.unsquash k0); split; auto.
    hnf; auto.
    apply H; auto.
    hnf; auto.
    rewrite H2 in H0; discriminate.

    rewrite K0.hered_spec; intros.
    assert (k' = k'').
    apply KL0.unsquash_inj.
    hnf in H1.
    hnf in H2; subst o'.
    destruct (K0.unsquash k').
    destruct (K0.unsquash k'').
    destruct H1; hnf in H2.
    subst; auto.
    subst k''.
    hnf in H.

    hnf.
    hnf in H2; subst.
    clear H1.
    induction H0.
    eapply H; eauto.
    hnf; simpl.
    hnf in H0.
    rewrite H0; auto.
    auto.
    eauto.
  Qed.

  Module Output <: knot_full_variant.KNOT_FULL_OUTPUT with Module KI := Input.
    Module KI := Input.
    Module K0 := K0.

    Definition predicate : Type := pred (K0.knot * KI.other).
    Definition pkp: bijection predicate K0.predicate :=
      bij_sym (sig_sig_iff_bij hered_hereditary).
  End Output.

  Module K := knot_full_variant.KnotFull(Input)(Output).

  Definition knot := K.knot.
  Definition ageable_knot := K.ageable_knot.
  Definition squash: (nat * KI.F (pred (knot*KI.other))) -> knot := K.squash.
  Definition unsquash: knot -> (nat * KI.F (pred (knot*KI.other))) := K.unsquash.
  Definition approx: nat -> pred (knot*KI.other) -> pred (knot*KI.other) :=
    K.approx.

  Lemma approx_spec : forall n p k,
    approx n p k = (level (fst k) < n /\ p k).
  Proof.
    intros.
    apply prop_ext.
    pose proof K.approx_spec n p k.
    match goal with
    | _: ?A = _ |- ?B <-> _ => change B with A
    end.
    rewrite H.
    match goal with
    | |- (if le_gt_dec _ ?A then _ else _) <-> (?B < _ /\ _) =>
            change B with A; remember A as TMP eqn:HHH; clear HHH
    end.
    destruct (le_gt_dec n TMP).
    + split.
      - intros [].
      - intros [? ?]; omega.
    + split.
      - intros; split; [omega | auto].
      - intros [? ?]; auto.
  Qed.

  Definition squash_unsquash := K.squash_unsquash.

  Definition unsquash_squash := K.unsquash_squash.

  Definition knot_age1 := K.knot_age1.

  Definition knot_level := K.knot_level.

End Knot_CovariantHeredPropOth.

Module KnotLemmas_CovariantHeredPropOth (K: KNOT__COVARIANT_HERED_PROP_OTH).

  Import CovariantFunctor.
  Import K.KI.
  Import K.

  Lemma unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.unsquash_inj
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.
  Arguments unsquash_inj [k1 k2] _.

  Lemma squash_surj : forall k, exists n, exists Fp,
    squash (n, Fp) = k.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.squash_surj
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.

  Lemma unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = fmap KI.F (approx n) Fp.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.unsquash_approx
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.
  Arguments unsquash_approx [k n Fp] _.

  Lemma pred_ext : forall (p1 p2: pred (knot * other)),
    (forall x, p1 x = p2 x) ->
    p1 = p2.
  Proof.
    intros.
    apply pred_ext'.
    extensionality; auto.
  Qed.

  Lemma approx_spec': forall n p ko,
    (approx n p) ko =
    if (le_gt_dec n (level (fst ko))) then False else proj1_sig p ko.
  Proof.
    intros.
    rewrite approx_spec.
    apply prop_ext.
    destruct (le_gt_dec n (level (fst ko))).
    + split; [intros [? ?]; omega | intros []].
    + tauto.
  Qed.

  Lemma approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).
  Proof.
    apply
     (@knot_full_variant.KnotLemmas2.approx_approx1
       (knot_full_variant.KnotLemmas2.Build_Input _ _ _ _ _ _
         (@proj1_sig _ _) _ pred_ext approx_spec')),
     (knot_full_variant.KnotLemmas2.Proof).
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas2.approx_approx2
       (knot_full_variant.KnotLemmas2.Build_Input _ _ _ _ _ _
         (@proj1_sig _ _) _ pred_ext approx_spec')),
     (knot_full_variant.KnotLemmas2.Proof).
  Qed.

End KnotLemmas_CovariantHeredPropOth.

Module Knot_CovariantHeredProp (KI':KNOT_INPUT__COVARIANT_HERED_PROP)
  : KNOT__COVARIANT_HERED_PROP with Module KI:=KI'.

  Import MixVariantFunctor.
  Import MixVariantFunctorLemmas.
  Import GeneralFunctorGenerator.
  Module KI:=KI'.

  Module Input.
    Definition F: functor := CovariantFunctor_MixVariantFunctor KI.F.
    Definition other := unit.

    Definition Rel A := @eq (F A).
    Lemma Rel_fmap : forall A B (f:A -> B) (s:B -> A) x y,
      Rel A x y ->
      Rel B (fmap F f s x) (fmap F f s y).
    Proof.
      unfold Rel; intuition; subst; auto.
    Qed.

    Lemma Rel_refl : forall A x, Rel A x x.
    Proof.
      intros; hnf; auto.
    Qed.

    Lemma Rel_trans : forall A x y z,
      Rel A x y -> Rel A y z -> Rel A x z.
    Proof.
      unfold Rel; intuition congruence.
    Qed.

    Definition ORel := @eq other.
    Lemma ORel_refl : reflexive other ORel.
    Proof.
      hnf; unfold ORel; auto.
    Qed.
    Lemma ORel_trans : transitive other ORel.
    Proof.
      hnf; unfold ORel; intros; congruence.
    Qed.

    Definition T := Prop.
    Definition T_bot := False.

    Definition T_rel (x y:T) := x -> y.
    Lemma T_rel_bot : forall x, T_rel T_bot x.
    Proof.
      compute; intuition.
    Qed.

    Lemma T_rel_refl : forall x, T_rel x x.
    Proof.
      compute; intuition.
    Qed.

    Lemma T_rel_trans : transitive _ T_rel.
    Proof.
      hnf; unfold T_rel; intuition.
    Qed.
  End Input.

  Module K0 := knot_full_variant.Knot_MixVariantHeredTOthRel(Input).
  Module KL0 := knot_full_variant.KnotLemmas_MixVariantHeredTOthRel(K0).
  Existing Instance K0.ageable_knot.

  Lemma hered_hereditary : forall (p: K0.knot -> Prop),
    K0.hered (fun ko => p (fst ko)) <-> hereditary age p.
  Proof.
    intros; split; repeat intro.
    rewrite K0.hered_spec in H.
    hnf in H0.
    simpl in H0.
    specialize ( H a a' a').
    specialize ( H tt tt).
    spec H.
    apply rt_step; auto.
    spec H.
    hnf.
    destruct (K0.unsquash a'); split; auto.
    hnf; auto.
    apply H; auto.
    hnf; auto.

    rewrite K0.hered_spec; intros.
    assert (k' = k'').
    apply KL0.unsquash_inj.
    hnf in H1.
    destruct (K0.unsquash k').
    destruct (K0.unsquash k'').
    destruct H1; hnf in H3.
    subst; auto.
    subst k''.
    hnf in H.

    hnf.
    simpl.
    clear -H H0.
    induction H0; auto.
    eapply H; eauto.
  Qed.

  Module Output <: knot_full_variant.KNOT_FULL_OUTPUT with Module KI := Input.
    Module KI := Input.
    Module K0 := K0.

    Definition predicate : Type := pred K0.knot.

    Definition pkp: bijection predicate K0.predicate :=
      bij_sym
        ((sig_sig_iff_bij hered_hereditary) ooo
         (bij_sig
           (bij_sym (func_bij (unit_unit1 K0.knot) (bij_refl Prop)))
           K0.hered)).
  End Output.

  Module K := knot_full_variant.KnotFull(Input)(Output).

  Definition knot := K.knot.
  Definition ageable_knot := K.ageable_knot.
  Definition squash: (nat * KI.F (pred knot)) -> knot := K.squash.
  Definition unsquash: knot -> (nat * KI.F (pred knot)) := K.unsquash.
  Definition approx: nat -> pred knot -> pred knot := K.approx.

  Lemma approx_spec : forall n p k,
    approx n p k = (level k < n /\ p k).
  Proof.
    intros.
    apply prop_ext.
    pose proof K.approx_spec n p (k, tt).
    match goal with
    | _: ?A = _ |- ?B <-> _ => change B with A
    end.
    rewrite H.
    match goal with
    | |- (if le_gt_dec _ ?A then _ else _) <-> (?B < _ /\ _) =>
            change B with A; remember A as TMP eqn:HHH; clear HHH
    end.
    destruct (le_gt_dec n TMP).
    + split.
      - intros [].
      - intros [? ?]; omega.
    + split.
      - intros; split; [omega | auto].
      - intros [? ?]; auto.
  Qed.

  Definition squash_unsquash := K.squash_unsquash.

  Definition unsquash_squash := K.unsquash_squash.

  Definition knot_age1 := K.knot_age1.

  Definition knot_level := K.knot_level.

End Knot_CovariantHeredProp.

Module KnotLemmas_CovariantHeredProp (K: KNOT__COVARIANT_HERED_PROP).

  Import CovariantFunctor.
  Import K.KI.
  Import K.

  Lemma unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.unsquash_inj
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.
  Arguments unsquash_inj [k1 k2] _.

  Lemma squash_surj : forall k, exists n, exists Fp,
    squash (n, Fp) = k.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.squash_surj
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.

  Lemma unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = fmap KI.F (approx n) Fp.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.unsquash_approx
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.
  Arguments unsquash_approx [k n Fp] _.

  Lemma pred_ext : forall (p1 p2: pred knot),
    (forall x, p1 x = p2 x) ->
    p1 = p2.
  Proof.
    intros.
    apply pred_ext'.
    extensionality; auto.
  Qed.

  Lemma pred_ext': forall (p1 p2: pred knot),
    (forall x: knot * unit,
      ((fun (p: knot -> Prop) ko => p (fst ko)) oo app_pred) p1 x =
      ((fun (p: knot -> Prop) ko => p (fst ko)) oo app_pred) p2 x) ->
    p1 = p2.
  Proof.
    intros.
    unfold compose in H; simpl in H.
    apply pred_ext'.
    extensionality; apply (H (x, tt)).
  Qed.

  Lemma approx_spec': forall n p k,
    ((fun (p: knot -> Prop) ko => p (@fst _ unit ko)) oo app_pred) (approx n p) k =
    if (le_gt_dec n (level (fst k))) then False else
    ((fun (p: knot -> Prop) ko => p (@fst _ unit ko)) oo app_pred) p k.
  Proof.
    intros.
    unfold compose; simpl.
    rewrite approx_spec.
    apply prop_ext.
    destruct (le_gt_dec n (level (fst k))).
    + split; [intros [? ?]; omega | intros []].
    + tauto.
  Qed.

  Lemma approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).
  Proof.
    apply
     (@knot_full_variant.KnotLemmas2.approx_approx1
       (knot_full_variant.KnotLemmas2.Build_Input _ _ _ _ _ _
         _ _ pred_ext' approx_spec')),
     (knot_full_variant.KnotLemmas2.Proof).
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas2.approx_approx2
       (knot_full_variant.KnotLemmas2.Build_Input _ _ _ _ _ _
         _ _ pred_ext' approx_spec')),
     (knot_full_variant.KnotLemmas2.Proof).
  Qed.

End KnotLemmas_CovariantHeredProp.

Module Knot_MixVariantHeredProp (KI':KNOT_INPUT__MIXVARIANT_HERED_PROP)
  : KNOT__MIXVARIANT_HERED_PROP with Module KI:=KI'.

  Import MixVariantFunctor.
  Import MixVariantFunctorLemmas.
  Import GeneralFunctorGenerator.
  Module KI:=KI'.

  Module Input.
    Definition F: functor := KI.F.
    Definition other := unit.

    Definition Rel A := @eq (F A).
    Lemma Rel_fmap : forall A B (f:A -> B) (s:B -> A) x y,
      Rel A x y ->
      Rel B (fmap F f s x) (fmap F f s y).
    Proof.
      unfold Rel; intuition; subst; auto.
    Qed.

    Lemma Rel_refl : forall A x, Rel A x x.
    Proof.
      intros; hnf; auto.
    Qed.

    Lemma Rel_trans : forall A x y z,
      Rel A x y -> Rel A y z -> Rel A x z.
    Proof.
      unfold Rel; intuition congruence.
    Qed.

    Definition ORel := @eq other.
    Lemma ORel_refl : reflexive other ORel.
    Proof.
      hnf; unfold ORel; auto.
    Qed.
    Lemma ORel_trans : transitive other ORel.
    Proof.
      hnf; unfold ORel; intros; congruence.
    Qed.

    Definition T := Prop.
    Definition T_bot := False.

    Definition T_rel (x y:T) := x -> y.
    Lemma T_rel_bot : forall x, T_rel T_bot x.
    Proof.
      compute; intuition.
    Qed.

    Lemma T_rel_refl : forall x, T_rel x x.
    Proof.
      compute; intuition.
    Qed.

    Lemma T_rel_trans : transitive _ T_rel.
    Proof.
      hnf; unfold T_rel; intuition.
    Qed.
  End Input.

  Module K0 := knot_full_variant.Knot_MixVariantHeredTOthRel(Input).
  Module KL0 := knot_full_variant.KnotLemmas_MixVariantHeredTOthRel(K0).
  Existing Instance K0.ageable_knot.

  Lemma hered_hereditary : forall (p: K0.knot -> Prop),
    K0.hered (fun ko => p (fst ko)) <-> hereditary age p.
  Proof.
    intros; split; repeat intro.
    rewrite K0.hered_spec in H.
    hnf in H0.
    simpl in H0.
    specialize ( H a a' a').
    specialize ( H tt tt).
    spec H.
    apply rt_step; auto.
    spec H.
    hnf.
    destruct (K0.unsquash a'); split; auto.
    hnf; auto.
    apply H; auto.
    hnf; auto.

    rewrite K0.hered_spec; intros.
    assert (k' = k'').
    apply KL0.unsquash_inj.
    hnf in H1.
    destruct (K0.unsquash k').
    destruct (K0.unsquash k'').
    destruct H1; hnf in H3.
    subst; auto.
    subst k''.
    hnf in H.

    hnf.
    simpl.
    clear -H H0.
    induction H0; auto.
    eapply H; eauto.
  Qed.

  Module Output <: knot_full_variant.KNOT_FULL_OUTPUT with Module KI := Input.
    Module KI := Input.
    Module K0 := K0.

    Definition predicate : Type := pred K0.knot.

    Definition pkp: bijection predicate K0.predicate :=
      bij_sym
        ((sig_sig_iff_bij hered_hereditary) ooo
         (bij_sig
           (bij_sym (func_bij (unit_unit1 K0.knot) (bij_refl Prop)))
           K0.hered)).
  End Output.

  Module K := knot_full_variant.KnotFull(Input)(Output).

  Definition knot := K.knot.
  Definition ageable_knot := K.ageable_knot.
  Definition predicate := pred knot.
  Definition squash: (nat * KI.F (pred knot)) -> knot := K.squash.
  Definition unsquash: knot -> (nat * KI.F (pred knot)) := K.unsquash.
  Definition approx: nat -> pred knot -> pred knot := K.approx.

  Lemma approx_spec : forall n p k,
    approx n p k = (level k < n /\ p k).
  Proof.
    intros.
    apply prop_ext.
    pose proof K.approx_spec n p (k, tt).
    match goal with
    | _: ?A = _ |- ?B <-> _ => change B with A
    end.
    rewrite H.
    match goal with
    | |- (if le_gt_dec _ ?A then _ else _) <-> (?B < _ /\ _) =>
            change B with A; remember A as TMP eqn:HHH; clear HHH
    end.
    destruct (le_gt_dec n TMP).
    + split.
      - intros [].
      - intros [? ?]; omega.
    + split.
      - intros; split; [omega | auto].
      - intros [? ?]; auto.
  Qed.

  Definition squash_unsquash := K.squash_unsquash.

  Definition unsquash_squash := K.unsquash_squash.

  Definition knot_age1 := K.knot_age1.

  Definition knot_level := K.knot_level.

End Knot_MixVariantHeredProp.

Module KnotLemmas_MixVariantHeredProp (K': KNOT__MIXVARIANT_HERED_PROP).

  Import MixVariantFunctor.
  Module K := K'.
  Import K.KI.
  Import K.

  Lemma unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.unsquash_inj
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.
  Arguments unsquash_inj [k1 k2] _.

  Lemma squash_surj : forall k, exists n, exists Fp,
    squash (n, Fp) = k.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.squash_surj
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.

  Lemma unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = fmap KI.F (approx n) (approx n) Fp.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas1.unsquash_approx
       (knot_full_variant.KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (knot_full_variant.KnotLemmas1.Proof).
  Qed.
  Arguments unsquash_approx [k n Fp] _.

  Lemma pred_ext : forall (p1 p2: pred knot),
    (forall x, p1 x = p2 x) ->
    p1 = p2.
  Proof.
    intros.
    apply pred_ext'.
    extensionality; auto.
  Qed.

  Lemma pred_ext': forall (p1 p2: pred knot),
    (forall x: knot * unit,
      ((fun (p: knot -> Prop) ko => p (fst ko)) oo app_pred) p1 x =
      ((fun (p: knot -> Prop) ko => p (fst ko)) oo app_pred) p2 x) ->
    p1 = p2.
  Proof.
    intros.
    unfold compose in H; simpl in H.
    apply pred_ext'.
    extensionality; apply (H (x, tt)).
  Qed.

  Lemma approx_spec': forall n p k,
    ((fun (p: knot -> Prop) ko => p (@fst _ unit ko)) oo app_pred) (approx n p) k =
    if (le_gt_dec n (level (fst k))) then False else
    ((fun (p: knot -> Prop) ko => p (@fst _ unit ko)) oo app_pred) p k.
  Proof.
    intros.
    unfold compose; simpl.
    rewrite approx_spec.
    apply prop_ext.
    destruct (le_gt_dec n (level (fst k))).
    + split; [intros [? ?]; omega | intros []].
    + tauto.
  Qed.

  Lemma approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).
  Proof.
    apply
     (@knot_full_variant.KnotLemmas2.approx_approx1
       (knot_full_variant.KnotLemmas2.Build_Input _ _ _ _ _ _
         _ _ pred_ext' approx_spec')),
     (knot_full_variant.KnotLemmas2.Proof).
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    apply
     (@knot_full_variant.KnotLemmas2.approx_approx2
       (knot_full_variant.KnotLemmas2.Build_Input _ _ _ _ _ _
         _ _ pred_ext' approx_spec')),
     (knot_full_variant.KnotLemmas2.Proof).
  Qed.

End KnotLemmas_MixVariantHeredProp.



