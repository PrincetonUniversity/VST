(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import VST.msl.knot.
Require Import VST.msl.knot_hered.
Require Import VST.msl.functors.

Import CovariantFunctor.
Import CovariantFunctorLemmas.
Import CovariantFunctorGenerator.

Module Knot_Lemmas (K : KNOT).
  Import K.TF.
  Import K.

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
    destruct (le_gt_dec n (level k)); auto.
    destruct (le_gt_dec (m+n) (level k)); auto.
    elimtype False; omega.
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    intros.
    extensionality p x; destruct x as [k o].
    unfold approx, compose; simpl.
    destruct (le_gt_dec (m+n) (level k)); auto.
    destruct (le_gt_dec n (level k)); auto.
    elimtype False; omega.
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

(*
  Lemma unsquash_not_surj :
    (exists rbot : rhs, rbot <> rhs_top) ->
    (exists Fp : F predicate, True) ->
    forall n, exists Fp, forall k, unsquash k <> (n, Fp).
  Proof.
  intros.
  destruct H as [bot ?].
  destruct H0 as [anF _].
  remember (fun (p : predicate) (w : knot * other) => bot) as badf.
  remember (fmap badf anF) as badF.
  exists badF.
  repeat intro.
  generalize (unsquash_approx H0); intro.
  rewrite HeqbadF in H1.
  replace (fmap (approx n) (fmap badf anF)) with
    ((fmap (approx n) oo fmap badf) anF) in H1 by trivial.
  rewrite fmap_comp in H1.
  XXXXX  (* Gah, annoying *)
*)

End Knot_Lemmas.

Module KnotHered_Lemmas (K : KNOT_HERED).
  Import K.TF.
  Import K.

  Lemma predicate_eq : forall (p1 p2:predicate),
    proj1_sig p1 = proj1_sig p2 ->
    p1 = p2.
  Proof.
    intros; destruct p1; destruct p2; simpl in H.
    subst x0.
    replace h0 with h by apply proof_irr.
    auto.
  Qed.

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
    extensionality p.
    apply predicate_eq.
    extensionality x; destruct x as [k o].
    unfold compose.
    repeat rewrite approx_spec.
    apply prop_ext. intuition.
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    intros.
    extensionality p. apply predicate_eq.
    extensionality x; destruct x as [k o].
    unfold compose. repeat rewrite approx_spec.
    apply prop_ext. intuition.
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

End KnotHered_Lemmas.
