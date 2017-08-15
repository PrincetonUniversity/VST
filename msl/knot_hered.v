(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import VST.msl.base.
Local Open Scope nat_scope.

Require Import VST.msl.ageable.
Require Import VST.msl.functors.
Require Import VST.msl.predicates_hered.

Import CovariantFunctor.
Import CovariantFunctorLemmas.
Import CovariantFunctorGenerator.

Module Type TY_FUNCTOR_PROP.
  Parameter F : functor.
  Parameter other : Type.
End TY_FUNCTOR_PROP.

Module Type KNOT_HERED.
  Declare Module TF:TY_FUNCTOR_PROP.
  Import TF.

  Parameter knot:Type.
  Parameter ag_knot : ageable knot.
  Existing Instance ag_knot.
  Existing Instance ag_prod.

  Definition predicate := pred (knot * other).

  Parameter squash : (nat * F predicate) -> knot.
  Parameter unsquash : knot -> (nat * F predicate).

  Parameter approx : nat -> predicate -> predicate.

  Axiom squash_unsquash : forall k:knot, squash (unsquash k) = k.
  Axiom unsquash_squash : forall (n:nat) (f:F predicate),
    unsquash (squash (n,f)) = (n, fmap F (approx n) f).

  Axiom approx_spec : forall n p k,
    proj1_sig (approx n p) k = (level k < n /\ proj1_sig p k).

  Axiom knot_level : forall k:knot, level k = fst (unsquash k).

  Axiom knot_age1 : forall k,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

End KNOT_HERED.

Module KnotHered (TF':TY_FUNCTOR_PROP) : KNOT_HERED with Module TF:=TF'.
  Module TF:=TF'.
  Import TF.

  Definition sinv_prod X := prod X (F X * other -> Prop).

  Definition guppy_sig := (fun T:Type => T * (F T * other -> Prop) -> Prop).
  Definition guppy_ty := sigT guppy_sig.

  Definition guppy_step_ty (Z:guppy_ty) : Type :=
    (sig (fun (x:sinv_prod (projT1 Z)) => projT2 Z x)).

  Definition guppy_step_prop (Z:guppy_ty) (xf:sinv_prod (guppy_step_ty Z)) :=
    forall (k:F (guppy_step_ty Z)) (o:other),
      snd xf (k,o) -> snd (proj1_sig (fst xf)) (fmap F (@fst _ _ oo @proj1_sig _ _) k,o).

  Definition guppy_step (Z:guppy_ty) : guppy_ty :=
    existT guppy_sig (guppy_step_ty Z) (guppy_step_prop Z).

  Definition guppy_base : guppy_ty :=
    existT guppy_sig unit (fun _ => True).

  Fixpoint guppy (n:nat) : guppy_ty :=
    match n with
    | 0    => guppy_base
    | S n' => guppy_step (guppy n')
    end.

  Definition sinv (n:nat) : Type := projT1 (guppy n).
  Definition sinv_prop (n:nat) : prod (sinv n) (F (sinv n) * other -> Prop) -> Prop := projT2 (guppy n).

  Fixpoint floor (m:nat) (n:nat) (p:sinv (m+n)) : sinv n :=
    match m as m' return forall (p : sinv (m'+n)), sinv n with
    | O => fun p => p
    | S m' => fun p => floor m' n (fst (proj1_sig p))
    end p.

  Definition knot := { n:nat & F (sinv n) }.

  Definition k_age1 (k:knot) : option (knot) :=
    match k with
      | (existT _ 0 f) => None
      | (existT _ (S m) f) => Some
          (existT (F oo sinv) m (fmap F (@fst _ _ oo @proj1_sig _ _) f))
    end.

  Definition k_age (k1 k2:knot) := k_age1 k1 = Some k2.

  Definition ko_age1 (x:knot * other) :=
    match k_age1 (fst x) with
    | None => None
    | Some a' => Some (a',snd x)
    end.
  Definition ko_age x y := ko_age1 x = Some y.


  Definition predicate := { p:knot * other -> Prop | hereditary ko_age p }.

  Definition app_sinv (n:nat) (p:sinv (S n)) (x:F (sinv n) * other) :=
    snd (proj1_sig p) x.

  Lemma app_sinv_age : forall n (p:sinv (S (S n))) (f:F (sinv (S n)) * other),
    app_sinv (S n) p f ->
    app_sinv n (fst (proj1_sig p)) (fmap F (@fst _ _ oo @proj1_sig _ _) (fst f), snd f).
  Proof.
    intros.
    unfold app_sinv in *.
    destruct p; simpl in *; fold guppy in *.
    apply p; auto.
    destruct f; auto.
  Qed.

  Section stratifies.
    Variable Q:knot * other -> Prop.
    Variable HQ:hereditary ko_age Q.

    Fixpoint stratifies (n:nat) : sinv n -> Prop :=
    match n as n' return sinv n' -> Prop with
    | 0 => fun _ => True
    | S n' => fun (p:sinv (S n')) =>
          stratifies n' (fst (proj1_sig p)) /\
          forall (k:F (sinv n')) (o:other), snd (proj1_sig p) (k,o) <-> Q (existT (F oo sinv) n' k,o)
    end.

    Lemma stratifies_unique : forall n p1 p2,
      stratifies n p1 ->
      stratifies n p2 ->
      p1 = p2.
    Proof.
      induction n; simpl; intuition.
      destruct p1; destruct p2; auto.
      destruct p1; destruct p2.
      simpl in *; fold guppy in *.
      cut (x = x0).
      intros.
      revert p p0 H2 H3.
      rewrite <- H0.
      intros.
      replace p0 with p by (apply proof_irr); auto.
      destruct x; destruct x0; simpl in *.
      apply injective_projections; simpl.
      apply IHn; auto.
      extensionality; intros.
      simpl in *.
      destruct (H2 (fst x) (snd x)); destruct (H3 (fst x) (snd x)).
      apply prop_ext; destruct x; intuition.
    Qed.

    Definition stratify (n:nat) : { x:sinv n | stratifies n x }.
    Proof.
      induction n.
      exists tt; simpl; exact I.
      assert (HX:
        projT2 (guppy n)
        (proj1_sig IHn, fun v : F (sinv n) * other => Q (existT (F oo sinv) n (fst v),snd v))).
      destruct n.
      simpl; exact I.
      simpl; intros.
      destruct IHn; simpl.
      simpl in s; destruct s.
      destruct x; simpl in *; fold guppy in *.
      destruct x; simpl in *.
      hnf; simpl; intros.
      rewrite H0.
      eapply HQ.
      2: apply H1.
      simpl; reflexivity.
      exists ((exist (fun x => projT2 (guppy n) x) ( proj1_sig IHn, fun v:F (sinv n) * other => Q (existT (F oo sinv) n (fst v),snd v) ) HX)).
      simpl; split.
      destruct IHn; auto.
      unfold app_sinv; simpl; intros.
      split; trivial.
    Qed.
  End stratifies.

  Lemma decompose_nat : forall (x y:nat), { m:nat & y = (m + S x) } + { ge x y }.
  Proof.
    intros x y; revert x; induction y; simpl; intros.
    right; auto with arith.
    destruct (IHy x) as [[m H]|H].
    left; exists (S m); omega.
    destruct (eq_nat_dec x y).
    left; exists O; omega.
    right; omega.
  Qed.

  Definition unstratify (n:nat) (p:sinv n) : knot * other -> Prop := fun w =>
    match w with (existT _ nw w',o) =>
      match decompose_nat nw n with
        | inleft (existT _ m Hm) => snd (proj1_sig (floor m (S nw) (eq_rect  n _ p (m + S nw) Hm))) (w',o)
        | inright H => False
      end
    end.

  Lemma floor_shuffle:
    forall (m1 n : nat)
      (p1 : sinv (m1 + S n)) (H1 : (m1 + S n) = (S m1 + n)),
      floor (S m1) n (eq_rect (m1 + S n) sinv p1 (S m1 + n) H1) = fst (proj1_sig (floor m1 (S n) p1)).
  Proof.
    intros.
    remember (fst (proj1_sig (floor m1 (S n) p1))) as p.
    fold guppy in *.
    revert n p1 H1 p Heqp.
    induction m1; simpl; intros.
    replace H1 with (refl_equal (S n)) by (apply proof_irr); simpl; auto.
    assert (m1 + S n = S m1 + n) by omega.
    destruct p1 as [[p1 f'] Hp1]; simpl in *; fold guppy in *.
    generalize (IHm1 n p1 H p Heqp).
    clear.
    revert Hp1 H1; generalize H.
    revert p1 f'.
    rewrite H.
    simpl; intros.
    replace H1 with (refl_equal (S (S (m1 + n)))) by (apply proof_irr).
    simpl.
    replace H0 with (refl_equal (S (m1+n))) in H2 by (apply proof_irr).
    simpl in H2.
    trivial.
  Qed.

  Lemma unstratify_hered : forall n p,
    hereditary ko_age (unstratify n p).
  Proof.
    intros.
    hnf; intros k k'; intros.
    simpl in H.
    destruct k.
    destruct k as [x f]. destruct x.
    discriminate.
    destruct k' as [k' o'].
    assert (o = o').
    hnf in H.
    simpl in H.
    inv H. auto.
    subst o'.
    replace k' with
      (existT (F oo sinv) x (fmap F (@fst _ _ oo @proj1_sig _ _ ) f)).
    2: inversion H; auto.
    clear H.
    case_eq (decompose_nat x n); intros.
    destruct s.
    case_eq (decompose_nat (S x) n); intros.
    destruct s.
    destruct n.
    elimtype False; omega.
    assert (S x1 = x0) by omega; subst x0.
    revert H0.
    unfold unstratify.
    rewrite H; rewrite H1.
    generalize e e0; revert p; rewrite e0; intros.
    rewrite floor_shuffle.
    replace e2 with (refl_equal (x1 + S (S x))) in H0;
      simpl eq_rect in H0.
    2: apply proof_irr.
    change f with (fst (f,o)).
    change o with (snd (f,o)).
    eapply app_sinv_age; apply H0.

    revert H0.
    unfold unstratify.
    rewrite H; rewrite H1.
    intuition.

    case_eq (decompose_nat (S x) n); intros.
    destruct s.
    elimtype False; omega.
    revert H0.
    unfold unstratify.
    rewrite H; rewrite H1; auto.
  Qed.

  Lemma unstratify_Q : forall n (p:sinv n) Q,
    stratifies Q n p ->
    forall (k:knot) o,
      projT1 k < n ->
      (unstratify n p (k,o) <-> Q (k,o)).
  Proof.
    intros.
    unfold unstratify.
    destruct k.
    destruct (decompose_nat x n).
    destruct s.
    simpl in H0.
    2: simpl in *; elimtype False; omega.
    clear H0.
    revert p H.
    generalize e.
    rewrite e.
    intros.
    replace e0 with (refl_equal (x0 + S x)) by apply proof_irr.
    simpl.
    clear e e0.
    revert p H.
    induction x0; simpl; intros.
    destruct H.
    auto.
    destruct H.
    apply IHx0.
    auto.
  Qed.

  Lemma stratifies_unstratify_more :
    forall (n m1 m2:nat) (p1:sinv (m1+n)) (p2:sinv (m2+n)),
      floor m1 n p1 = floor m2 n p2 ->
      (stratifies (unstratify (m1+n) p1) n (floor m1 n p1) ->
       stratifies (unstratify (m2+n) p2) n (floor m2 n p2)).
  Proof.
    induction n; intuition.
    split.
    assert (m2 + S n = S m2 + n) by omega.
    erewrite <- floor_shuffle.
    instantiate (1:=H1).
    replace (unstratify (m2 + S n) p2)
      with (unstratify (S m2 + n) (eq_rect (m2 + S n) sinv p2 (S m2 + n) H1)).
    assert (m1 + S n = S m1 + n) by omega.
    eapply (IHn (S m1) (S m2)
      (eq_rect (m1 + S n) sinv p1 (S m1 + n) H2)).
    rewrite floor_shuffle.
    rewrite floor_shuffle.
    rewrite H; auto.
    clear - H0.
    rewrite floor_shuffle.
    simpl in H0.
    destruct H0.
    clear H0.
    revert p1 H.
    generalize H2.
    rewrite <- H2.
    intros.
    replace H0 with (refl_equal (m1 + S n)) by apply proof_irr; auto.
    clear.
    revert p2.
    generalize H1.
    rewrite H1.
    intros.
    replace H0 with (refl_equal (S m2 + n)) by apply proof_irr; auto.

    intros.
    simpl.
    destruct (decompose_nat n (m2 + S n)).
    destruct s.
    assert (m2 = x).
    omega.
    subst x.
    replace e with (refl_equal (m2 + S n)).
    simpl; tauto.
    apply proof_irr.
    elimtype False; omega.
  Qed.

  Lemma stratify_unstratify : forall n p H,
    proj1_sig (stratify (unstratify n p) H n) = p.
  Proof.
    intros.
    apply stratifies_unique with (unstratify n p).
    destruct (stratify _ H n).
    simpl; auto.
    clear H.
    revert p; induction n.
    simpl; intros; auto.
    intros.
    simpl; split.

    assert (stratifies (unstratify n (fst (proj1_sig p))) n (fst (proj1_sig p))).
    apply IHn.
    apply (stratifies_unstratify_more n 0 1 (fst (proj1_sig p)) p).
    simpl; auto.
    auto.

    intros.
    destruct (decompose_nat n (S n)).
    destruct s.
    assert (x = 0) by omega.
    subst x.
    simpl.
    simpl in e.
    replace e with (refl_equal (S n)) by apply proof_irr.
    simpl.
    split; auto.
    elimtype False; omega.
  Qed.


  Definition strat (n:nat) (p:predicate) : sinv n :=
    proj1_sig (stratify (proj1_sig p) (proj2_sig p) n).

  Definition unstrat (n:nat) (p:sinv n) : predicate :=
    exist (hereditary ko_age) (unstratify n p) (unstratify_hered n p).

  Definition squash (x:nat * F predicate) : knot :=
    match x with (n,f) => existT (F oo sinv) n (fmap F (strat n) f) end.

  Definition unsquash (k:knot) : nat * F predicate :=
    match k with existT _ n f => (n, fmap F (unstrat n) f) end.

  Definition level (x:knot) : nat := fst (unsquash x).
  Program Definition approx (n:nat) (p:predicate) : predicate :=
     fun w => level (fst w) < n /\ p w.
  Next Obligation.
    hnf; simpl; intros.
    intuition.
    unfold level in *.
    unfold unsquash in *.
    destruct a0; simpl in H.
    destruct x; try discriminate.
    inv H.
    simpl in *; omega.
    destruct p; simpl in *.
    eapply h; eauto.
  Qed.

  Lemma strat_unstrat : forall n,
    strat n oo unstrat n = id (sinv n).
  Proof.
    intros; extensionality p.
    unfold compose, id.
    unfold strat, unstrat.
    simpl.
    rewrite stratify_unstratify.
    auto.
  Qed.

  Lemma predicate_eq : forall (p1 p2:predicate),
    proj1_sig p1 = proj1_sig p2 ->
    p1 = p2.
  Proof.
    intros; destruct p1; destruct p2; simpl in H.
    subst x0.
    replace h0 with h by apply proof_irr.
    auto.
  Qed.

  Lemma unstrat_strat : forall n,
    unstrat n oo strat n = approx n.
  Proof.
    intros.
    extensionality.
    unfold compose.
    unfold unstrat, strat.
    unfold approx.
    apply predicate_eq.
    simpl.
    extensionality k.
    apply prop_ext; intuition.
    unfold unstratify in H.
    destruct a.
    destruct (decompose_nat x0 n).
    unfold level.
    simpl.
    destruct s.
    omega.
    elim H.
    rewrite <- unstratify_Q.
    apply H.
    destruct (stratify (proj1_sig x) (proj2_sig x) n); auto.
    unfold unstratify in H.
    destruct a; simpl.
    destruct (decompose_nat x0 n).
    destruct s; omega.
    elim H.
    rewrite unstratify_Q.
    apply H1.
    destruct (stratify (proj1_sig x) (proj2_sig x) n); auto.
    unfold level in H0.
    destruct a; simpl in *.
    auto.
  Qed.

  Lemma squash_unsquash : forall k, squash (unsquash k) = k.
  Proof.
    intros.
    destruct k as [x f]; simpl.
    f_equal.
    change ((fmap F (strat x) oo fmap F (unstrat x)) f = f).
    rewrite fmap_comp.
    rewrite strat_unstrat.
    rewrite fmap_id.
    auto.
  Qed.

  Lemma unsquash_squash : forall n f,
    unsquash (squash (n,f)) = (n, fmap F (approx n) f).
  Proof.
    intros.
    unfold unsquash, squash.
    f_equal.
    change ((fmap F (unstrat n) oo fmap F (strat n)) f = fmap F (approx n) f).
    rewrite fmap_comp.
    rewrite unstrat_strat.
    auto.
  Qed.

  Lemma strat_unstrat_Sx : forall x,
    @fst _ _ oo @proj1_sig _ _ = strat x oo unstrat (S x).
  Proof.
    intros.
    extensionality k.
    change (sinv (S x)) in k.
    unfold compose.
    unfold strat, unstrat.
    simpl.
    apply stratifies_unique with (unstratify x (fst (proj1_sig k))).
    revert k; induction x; simpl; auto.
    intros.
    split.
    eapply (stratifies_unstratify_more x 0 1 ).
    simpl; reflexivity.
    simpl.
    apply IHx.
    intros.
    destruct (decompose_nat x (S x)).
    destruct s.
    assert (x0 = 0) by omega; subst x0.
    simpl in *.
    replace e with (refl_equal (S x)) by apply proof_irr; simpl.
    tauto.
    elimtype False; omega.
    destruct (stratify (unstratify (S x) k)
      (unstratify_hered (S x) k) x).
    simpl; auto.
    cut (x0 = (fst (proj1_sig k))); intros.
    subst x0.
    eapply (stratifies_unstratify_more x 1 0).
    simpl; reflexivity.
    simpl; auto.
    eapply stratifies_unique.
    apply s.
    eapply (stratifies_unstratify_more x 0 1).
    simpl; reflexivity.
    simpl.
    generalize (fst (proj1_sig k) : sinv x).
    clear.
    induction x; simpl; intuition.
    eapply (stratifies_unstratify_more x 0 1).
    simpl; reflexivity.
    simpl.
    apply IHx.
    destruct (decompose_nat x (S x)).
    destruct s0.
    assert (x0 = 0) by omega; subst.
    simpl in *.
    replace e with (refl_equal (S x)); simpl; auto.
    apply proof_irr.
    omega.
    destruct (decompose_nat x (S x)).
    destruct s0.
    assert (x0 = 0) by omega; subst.
    simpl in *.
    replace e with (refl_equal (S x)) in H; simpl; auto.
    apply proof_irr.
    elim H.
  Qed.

  Lemma unsquash_inj : forall k k',
    unsquash k = unsquash k' -> k = k'.
  Proof.
    intros.
    rewrite <- (squash_unsquash k).
    rewrite <- (squash_unsquash k').
    congruence.
  Qed.

  Lemma knot_age_age1 : forall k k',
    k_age1 k = Some k' <->
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end = Some k'.
  Proof.
    split; intros.
    unfold k_age1 in H.
    unfold unsquash in H.
    destruct k as [x f].
    destruct x; auto.
    inv H.
    simpl.
    f_equal.
    f_equal.
    change (fmap F (strat x) (fmap F (unstrat (S x)) f))
      with ((fmap F (strat x) oo fmap F (unstrat (S x))) f).
    rewrite fmap_comp.
    simpl.
    f_equal.
    symmetry.
    apply (strat_unstrat_Sx x).

    simpl in H.
    destruct k.
    destruct x.
    discriminate.
    inv H.
    hnf; simpl.
    unfold k_age1.
    f_equal.
    f_equal.
    rewrite strat_unstrat_Sx.
    rewrite <- fmap_comp.
    auto.
  Qed.

  Program Instance ag_knot : ageable knot :=
  { age1 := k_age1
  ; level := level
  }.
  Next Obligation.
    econstructor.
    (* unage *)
    intros.
    destruct (unsquash x') as [n f] eqn:?H; intros.
    exists (squash (S n, f)).
    rewrite knot_age_age1.
    rewrite unsquash_squash.
    f_equal.
    apply unsquash_inj.
    rewrite unsquash_squash.
    rewrite H.
    f_equal.
    cut (f = fmap F (approx n) f).
    intros.
    rewrite fmap_app.
    pattern f at 2. rewrite H0.
    f_equal.
    extensionality p.
    apply predicate_eq.
    extensionality w.
    simpl. apply prop_ext.
    intuition.
    generalize H; intro.
    rewrite <- (squash_unsquash x') in H.
    rewrite H0 in H.
    rewrite unsquash_squash in H.
    congruence.

    (* level 0 *)
    intro x. destruct x; simpl.
    destruct x; intuition; discriminate.

    (* level S *)
    intros. destruct x; simpl in *.
    destruct x. discriminate.
    inv H. simpl. auto.
  Qed.

  Existing Instance ag_prod.

  Lemma approx_spec : forall n p (k:knot * other),
    proj1_sig (approx n p) k = (ageable.level k < n /\ proj1_sig p k).
  Proof.
    intros.
    apply prop_ext.
    unfold approx; simpl.
    intuition; simpl in *; auto.
  Qed.

  Lemma knot_level : forall k:knot, level k = fst (unsquash k).
  Proof. reflexivity. Qed.

  Lemma knot_age1 : forall k,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.
  Proof.
    intros. simpl.
    case_eq (k_age1 k). intros.
    rewrite knot_age_age1 in H.
    auto.
    destruct k; simpl. destruct x. auto.
    intros. discriminate.
  Qed.

End KnotHered.
