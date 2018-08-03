Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import VST.msl.functors.
Import VST.msl.functors.MixVariantFunctor.
Import VST.msl.functors.MixVariantFunctorLemmas.

Module Type KNOT_INPUT__MIXVARIANT_HERED_T_OTH_REL.
  Parameter F : functor.

  Parameter other : Type.

  Parameter Rel : forall A, F A -> F A -> Prop.

  Parameter Rel_fmap : forall A B (f1: A->B) (f2:B->A) x y,
    Rel A x y ->
    Rel B (fmap F f1 f2 x) (fmap F f1 f2 y).
  Axiom Rel_refl : forall A x, Rel A x x.
  Axiom Rel_trans : forall A x y z,
    Rel A x y -> Rel A y z -> Rel A x z.

  Parameter ORel : other -> other -> Prop.
  Axiom ORel_refl : reflexive other ORel.
  Axiom ORel_trans : transitive other ORel.

  Parameter T:Type.
  Parameter T_bot:T.

  Parameter T_rel : T -> T -> Prop.
  Parameter T_rel_bot : forall x, T_rel T_bot x.
  Parameter T_rel_refl : forall x, T_rel x x.
  Parameter T_rel_trans : transitive T T_rel.

End KNOT_INPUT__MIXVARIANT_HERED_T_OTH_REL.

Module Type KNOT__MIXVARIANT_HERED_T_OTH_REL.
  Declare Module KI: KNOT_INPUT__MIXVARIANT_HERED_T_OTH_REL.
  Import KI.

  Parameter knot:Type.
  Parameter ageable_knot : ageable knot.
  Existing Instance ageable_knot.

  Parameter hered : (knot * other -> T) -> Prop.
  Definition predicate := { p:knot * other -> T | hered p }.

  Parameter squash : (nat * F predicate) -> knot.
  Parameter unsquash : knot -> (nat * F predicate).

  Parameter approx : nat -> predicate -> predicate.

  Axiom squash_unsquash : forall k:knot, squash (unsquash k) = k.
  Axiom unsquash_squash : forall (n:nat) (f:F predicate),
    unsquash (squash (n,f)) = (n, fmap F (approx n) (approx n) f).

  Axiom approx_spec : forall n p ko,
    proj1_sig (approx n p) ko =
     if (le_gt_dec n (level (fst ko))) then T_bot else proj1_sig p ko.

  Definition knot_rel (k1 k2:knot) :=
    let (n,f) := unsquash k1 in
    let (n',f') := unsquash k2 in
    n = n' /\ Rel predicate f f'.

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

End KNOT__MIXVARIANT_HERED_T_OTH_REL.

Module Knot_MixVariantHeredTOthRel (KI':KNOT_INPUT__MIXVARIANT_HERED_T_OTH_REL) :
  KNOT__MIXVARIANT_HERED_T_OTH_REL with Module KI:=KI'.
  Module KI := KI'.
  Import KI.

  Definition sinv_prod X := prod X (F X * other -> T).

  Definition guppy_sig := (fun X:Type => X * (F X * other -> T) -> Prop).
  Definition guppy_ty := sigT guppy_sig.

  Definition guppy_step_ty (Z:guppy_ty) : Type :=
    (sig (fun (x:sinv_prod (projT1 Z)) => projT2 Z x)).

  Definition guppy_age (Z:guppy_ty) (x:guppy_step_ty Z) : projT1 Z := fst (proj1_sig x).
  Definition guppy_unage (Z:guppy_ty)
    (H:forall t, projT2 Z (t,fun _ => T_bot))
    (x:projT1 Z) : guppy_step_ty Z :=
    exist (fun z => projT2 Z z) (x, fun _ => T_bot) (H x).

  Definition guppy_step_prop (Z:guppy_ty) (xf:sinv_prod (guppy_step_ty Z)) :=
    (forall (k:F (guppy_step_ty Z)) (o:other) H,
         T_rel (snd xf (k,o))
               (snd (proj1_sig (fst xf)) (fmap F (guppy_age Z) (guppy_unage Z H) k,o))) /\
    (forall (k k':F (guppy_step_ty Z)) (o o':other),
         Rel (guppy_step_ty Z) k k' ->
         ORel o o' ->
         T_rel (snd xf (k,o)) (snd xf (k',o'))).

  Definition guppy_step (Z:guppy_ty) : guppy_ty :=
    existT guppy_sig (guppy_step_ty Z) (guppy_step_prop Z).

  Definition guppy_base : guppy_ty :=
    existT guppy_sig unit
      (fun xf =>
        (forall (k k':F unit) (o o':other),
          Rel unit k k' ->
          ORel o o' ->
          T_rel (snd xf (k,o)) (snd xf (k',o')))).

  Fixpoint guppy (n:nat) : guppy_ty :=
    match n with
    | 0    => guppy_base
    | S n' => guppy_step (guppy n')
    end.

  Definition sinv (n:nat) : Type := projT1 (guppy n).
  Definition sinv_prop (n:nat) : prod (sinv n) (F (sinv n) * other -> T) -> Prop := projT2 (guppy n).

  Fixpoint floor (m:nat) (n:nat) (p:sinv (m+n)) : sinv n :=
    match m as m' return forall (p : sinv (m'+n)), sinv n with
    | O => fun p => p
    | S m' => fun p => floor m' n (fst (proj1_sig p))
    end p.

  Definition knot := { n:nat & F (sinv n) }.

  Definition sinv_age n : sinv (S n) -> sinv n := guppy_age (guppy n).
  Program Definition sinv_unage n : sinv n -> sinv (S n) := guppy_unage (guppy n) _.
  Next Obligation.
    revert t; induction n; simpl; auto.
    repeat intro.
    apply T_rel_bot.
    split; simpl in *; repeat intro.
    apply T_rel_bot.
    apply T_rel_bot.
  Qed.

  Definition F_sinv n := F (sinv n).

  Definition age1_def (k:knot) : option knot :=
    match k with
      | existT _ 0 f => None
      | existT _ (S m) f => Some
          (existT F_sinv m (fmap F (sinv_age m) (sinv_unage m) f))
    end.

  Definition age_def x y := age1_def x = Some y.

  Inductive knot_rel_inner : knot -> knot -> Prop :=
    | intro_krel : forall n (f f':F_sinv n),
         Rel _ f f' ->
         knot_rel_inner (existT (F_sinv) n f) (existT (F_sinv) n f').

  Definition hered (p:knot * other -> T) : Prop :=
    forall k k' k'' o o',
      clos_refl_trans _ age_def k k' ->
      knot_rel_inner k' k'' -> ORel o o' ->
      T_rel (p (k,o)) (p (k'',o')).

  Definition predicate := { p:knot * other -> T | hered p }.

  Definition app_sinv (n:nat) (p:sinv (S n)) (x:F_sinv n * other) :=
    snd (proj1_sig p) x.

  Section stratifies.
    Variable Q:knot * other -> T.
    Variable HQ:hered Q.

    Fixpoint stratifies (n:nat) : sinv n -> Prop :=
    match n as n' return sinv n' -> Prop with
    | 0 => fun _ => True
    | S n' => fun (p:sinv (S n')) =>
          stratifies n' (fst (proj1_sig p)) /\
          forall (k:F_sinv n') (o:other), snd (proj1_sig p) (k,o) = Q (existT F_sinv n' k,o)
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
      destruct x as [x o].
      destruct (H2 x o); destruct (H3 x o).
      rewrite H2.
      rewrite H3.
      auto.
    Qed.

    Definition stratify (n:nat) : { x:sinv n | stratifies n x }.
    Proof.
      induction n.
      exists tt; simpl; exact I.
      assert (HX:
        projT2 (guppy n)
        (proj1_sig IHn, fun v : F_sinv n * other => Q (existT F_sinv n (fst v),snd v))).
      destruct n.
      simpl; intros.
      eapply HQ.
      apply rt_refl.
      constructor; auto.
      auto.
      simpl; intros.
      destruct IHn; simpl.
      simpl in s; destruct s.
      destruct x; simpl in *; fold guppy in *.
      destruct x; simpl in *.
      split; hnf; simpl; intros.
      rewrite H0.
      eapply HQ.
      apply rt_step.
      hnf; simpl.
      reflexivity.
      constructor; auto.
      unfold sinv_unage.
      replace (sinv_unage_obligation_1 n) with H1.
      unfold sinv_age.
      apply Rel_refl.
      apply proof_irr.
      apply ORel_refl.
      eapply HQ.
      apply rt_refl.
      constructor; auto.
      auto.

      exists ((exist (fun x => projT2 (guppy n) x) ( proj1_sig IHn, fun v:F_sinv n * other => Q (existT (F_sinv) n (fst v),snd v) ) HX)).
      simpl; split; auto.
      destruct IHn; auto.
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

  Definition unstratify (n:nat) (p:sinv n) : knot * other -> T := fun w =>
    match w with (existT _ nw w',o) =>
      match decompose_nat nw n with
        | inleft (existT _ m Hm) => snd (proj1_sig (floor m (S nw) (eq_rect  n _ p (m + S nw) Hm))) (w',o)
        | inright H => T_bot
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
    hered (unstratify n p).
  Proof.
    intros.
    hnf; intros.
    apply T_rel_trans with (unstratify n p (k',o)).
    clear o' H0 H1.
    induction H.
    hnf in H; simpl in H.
    destruct x as [x f]; simpl in H.
    destruct x; try discriminate.
    assert (y =
      (existT (F_sinv) x (fmap F (sinv_age x) (sinv_unage x) f))).
    inversion H; auto.
    subst y.
    unfold unstratify.
    case_eq (decompose_nat (S x) n); intros.
    destruct s.
    case_eq (decompose_nat x n); intros.
    destruct s.
    destruct n.
    elimtype False; omega.
    assert (S x0 = x1) by omega; subst x1.
    revert H1.
    generalize e e0; revert p; rewrite e; intros.
    rewrite floor_shuffle.
    replace e1 with (refl_equal (x0 + S (S x)));
      simpl eq_rect.
    2: apply proof_irr.
    revert H1.
    generalize (floor x0 (S (S x)) p).
    intros [[s' fs] Hs] H1; simpl in *; fold guppy in *.
    destruct Hs.
    simpl in H2.
    eapply H2; auto.
    elimtype False.
    omega.
    apply T_rel_bot.
    apply T_rel_refl.
    eapply T_rel_trans; eauto.

    clear H.
    inv H0.
    simpl.
    destruct (decompose_nat n0 n); [ | apply T_rel_bot ].
    destruct s; simpl.
    destruct (floor x (S n0) (eq_rect n sinv p (x +S n0) e)); simpl.
    destruct n0; simpl in x0; destruct x0; simpl.
    apply p0; auto.
    apply p0; auto.
  Qed.

  Lemma unstratify_Q : forall n (p:sinv n) Q,
    stratifies Q n p ->
    forall (k:knot) (o:other),
      projT1 k < n ->
      (unstratify n p (k,o) = Q (k,o)).
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
    exist hered (unstratify n p) (unstratify_hered n p).

  Definition squash (x:nat * F predicate) : knot :=
    match x with (n,f) => existT (F_sinv) n (fmap F (strat n) (unstrat n) f) end.

  Definition unsquash (k:knot) : nat * F predicate :=
    match k with existT _ n f => (n, fmap F (unstrat n) (strat n) f) end.

  Definition knot_level_def (k:knot) : nat :=
    fst (unsquash k).

  Definition knot_age1_def (k:knot) : option knot :=
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

  Definition knot_unage_def (k:knot) :=
    let (n,k) := unsquash k in squash (S n,k).

  Program Definition approx (n:nat) (p:predicate) : predicate :=
    fun w => if (le_gt_dec n (knot_level_def (fst w))) then T_bot else proj1_sig p w.
  Next Obligation.
    hnf; simpl; intros.
    destruct (le_gt_dec n (knot_level_def k)).
    apply T_rel_bot.
    destruct (le_gt_dec n (knot_level_def k'')).
    elimtype False.
    cut (knot_level_def k'' <= knot_level_def k).
    omega.
    replace (knot_level_def k'') with (knot_level_def k').
    clear -H; induction H.
    hnf in H.
    unfold age1_def in H.
    destruct x; destruct y; simpl.
    destruct x; try discriminate.
    inv H.
    simpl.
    unfold knot_level_def; simpl; auto.
    auto.
    eapply le_trans; eauto.
    inv H0.
    unfold knot_level_def; simpl; auto.

    destruct p as [p Hp]; simpl.
    eapply Hp; eauto.
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
    destruct (le_gt_dec n (knot_level_def (fst k))).
    unfold unstratify.
    destruct k.
    destruct k.
    unfold knot_level_def in l.
    simpl in *.
    destruct (decompose_nat x0 n); simpl.
    destruct s; simpl; elimtype False; omega.
    auto.
    destruct x as [x Hx]; simpl.
    destruct (stratify x Hx n); simpl.
    destruct k.
    rewrite unstratify_Q with (Q:=x); auto.
    unfold level in *.
    destruct k; simpl in *; auto.
  Qed.

  Lemma squash_unsquash : forall k, squash (unsquash k) = k.
  Proof.
    intros.
    destruct k as [n f]; simpl.
    f_equal.
    change ((fmap F (strat n) (unstrat n) oo (fmap F (unstrat n) (strat n))) f = f).
    rewrite fmap_comp.
    rewrite strat_unstrat.
    rewrite fmap_id.
    auto.
  Qed.

  Lemma unsquash_squash : forall n f,
    unsquash (squash (n,f)) = (n, fmap F (approx n) (approx n) f).
  Proof.
    intros.
    unfold unsquash, squash.
    f_equal.
    change ((fmap F (unstrat n) (strat n) oo (fmap F (strat n) (unstrat n))) f = fmap F (approx n) (approx n) f).
    rewrite fmap_comp.
    rewrite unstrat_strat.
    auto.
  Qed.

  Lemma strat_Sx_unstrat : forall x,
    sinv_unage x = strat (S x) oo unstrat x.
  Proof.
    intros.
    extensionality k.
    unfold sinv_unage.
    generalize (sinv_unage_obligation_1); intro P.
    unfold guppy_unage.
    unfold compose, strat, unstrat.
    simpl.
    apply stratifies_unique with (unstratify x k).
    revert k.
    induction x; simpl; intuition.
    destruct (decompose_nat 0 0); auto.
    destruct s; elimtype False; omega.
    eapply (stratifies_unstratify_more x 0 1).
    simpl; reflexivity.
    simpl.
    simpl in *.
    destruct (IHx (fst (proj1_sig k))); auto.
    destruct (decompose_nat x (S x)).
    destruct s.
    assert (x0 = 0) by omega; subst x0.
    simpl in *.
    replace e with (refl_equal (S x)) by apply proof_irr; auto.
    elimtype False; omega.
    destruct (decompose_nat x (S x)).
    destruct s.
    assert (x0 = 0) by omega; subst x0.
    simpl in *.
    destruct (decompose_nat (S x) (S x)).
    destruct s; elimtype False; omega.
    auto.
    destruct (decompose_nat (S x) (S x)).
    destruct s; elimtype False; omega.
    auto.

    destruct (stratify (unstratify x k) (unstratify_hered x k) (S x)).
    simpl stratifies in s; case s; intros.
    simpl stratifies; split; auto.
  Qed.

  Lemma strat_unstrat_Sx : forall x,
    sinv_age x = strat x oo unstrat (S x).
  Proof.
    intros.
    extensionality k.
    unfold sinv_age, guppy_age.
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
    elimtype False; omega.
  Qed.

  Lemma age1_eq : forall k,
    age1_def k = knot_age1_def k.
  Proof.
    intros.
    unfold knot_age1_def.
    case_eq (unsquash k); intros.
    case_eq k; intros.
    simpl.
    assert (n = x).
    subst k.
    inv H; auto.
    subst x.
    destruct n; auto.
    f_equal.
    f_equal.

    rewrite strat_Sx_unstrat.
    rewrite strat_unstrat_Sx.
    rewrite <- fmap_comp.
    unfold compose.
    f_equal.
    subst k.
    inv H; auto.
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

  Lemma approx_spec : forall n p ko,
    proj1_sig (approx n p) ko =
     if (le_gt_dec n (knot_level_def (fst ko))) then T_bot else proj1_sig p ko.
  Proof.
    intros; simpl; auto.
  Qed.

  Lemma ag_knot_facts : ageable_facts knot knot_level_def knot_age1_def.
  Proof.
    constructor.

    unfold knot_age1_def; unfold knot_level_def; simpl; intros x'.
    destruct (unsquash x') as [n f] eqn:?H; intros.
    destruct x' as [x f0].
    exists (squash (S x, fmap F (unstrat x) (strat x) f0)).
    rewrite unsquash_squash.
    f_equal. f_equal.
    clear.
    transitivity ((fmap F (strat x) (unstrat x) oo fmap F (approx (S x)) (approx (S x)) oo fmap F (unstrat x) (strat x)) f0); auto.
    do 2 rewrite fmap_comp.
    rewrite compose_assoc.
    replace (strat x oo approx (S x) oo unstrat x) with (@id (sinv x)).
    rewrite fmap_id. auto.
    rewrite <- (strat_unstrat x).
    f_equal.
    extensionality a.
    unfold compose, approx.
    case_eq (unstrat x a); intros.
    match goal with
      [ |- _ = exist _ ?X _ ] =>
      assert (x0 = X)
    end.
   2:{
    generalize (approx_obligation_1 (S x)
      (exist (fun p => hered p) x0 h)).
    rewrite <- H0.
    intros. f_equal. apply proof_irr.
    }
    extensionality.
    destruct x1.
    unfold unstrat in H.
    inv H.
    destruct k.
    unfold unstratify.
    unfold knot_level_def.
    simpl fst.
    destruct (decompose_nat x0 x).
    destruct s.
    destruct (le_gt_dec (S x) x0).
    elimtype False; omega.
    simpl.
    destruct (decompose_nat x0 x).
    destruct s.
    assert (x1 = x2) by omega.
    subst x2.
    replace e0 with e by apply proof_irr.
    auto.
    elimtype False; omega.
    destruct (le_gt_dec (S x) x0); auto.
    simpl.
    destruct (decompose_nat x0 x); auto.
    destruct s. elimtype False. omega.

    intro.
    unfold knot_age1_def, knot_level_def.
    case_eq (unsquash x); intros.
    destruct n; simpl; intuition;
      discriminate.

    intros.
    unfold knot_age1_def, knot_level_def in *.
    case_eq (unsquash x); intros; rewrite H0 in H.
    destruct n; try discriminate; simpl.
    inv H; simpl; auto.
  Qed.

  Definition ageable_knot : ageable knot :=
    mkAgeable knot knot_level_def knot_age1_def ag_knot_facts.
  Existing Instance ageable_knot.

  Definition knot_rel (k1 k2:knot) :=
    let (n,f) := unsquash k1 in
    let (n',f') := unsquash k2 in
    n = n' /\ Rel predicate f f'.

  Lemma hered_spec : forall p,
    hered p =
    (forall k k' k'' o o',
      clos_refl_trans _ age k k' ->
      knot_rel  k' k'' ->
      ORel o o' ->
      T_rel (p (k,o)) (p (k'',o'))).
  Proof.
    intros.
    apply prop_ext.
    intuition.
    eapply H.
    instantiate (1:=k').
    clear -H0; induction H0; auto.
    apply rt_step.
    unfold age_def.
    rewrite age1_eq.
    auto.
    eapply rt_trans; eauto.
    destruct k' as [x f], k'' as [x0 f0].
    unfold knot_rel, unsquash in H1.
    destruct H1; subst.
    constructor.
    apply (Rel_fmap _ _ (strat x0) (unstrat x0)) in H3.
    change f with (id _ f).
    change f0 with (id _ f0).
    rewrite <- fmap_id.
    rewrite <- (strat_unstrat x0).
    rewrite <- fmap_comp.
    auto.
    assumption.

    hnf; intros.
    apply (H k k' k''); auto.
    clear -H0; induction H0; auto.
    apply rt_step.
    hnf.
    rewrite <- age1_eq; auto.
    eapply rt_trans; eauto.

    destruct k'; destruct k''.
    inv H1.
    simpl.
    hnf; split; auto.
    apply Eqdep_dec.inj_pair2_eq_dec in H5; auto.
    apply Eqdep_dec.inj_pair2_eq_dec in H7; auto.
    subst.
    apply Rel_fmap; auto.
    exact eq_nat_dec.
    exact eq_nat_dec.
  Qed.

  Lemma knot_age1 : forall k:knot,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.
  Proof.
    intros; reflexivity.
  Qed.

  Lemma knot_level : forall k:knot,
    level k = fst (unsquash k).
  Proof.
    intros; reflexivity.
  Qed.

End Knot_MixVariantHeredTOthRel.

Module KnotLemmas1.

Class Input: Type := {
  knot: Type;
  Fpred: Type;
  squash: nat * Fpred -> knot;
  unsquash: knot -> nat * Fpred;
  approxF: nat -> Fpred -> Fpred;
  squash_unsquash : forall k:knot, squash (unsquash k) = k;
  unsquash_squash : forall (n:nat) (f:Fpred),
    unsquash (squash (n,f)) = (n, approxF n f)
}.

Class Output (input: Input): Prop := {
  unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2;
  squash_surj : forall k, exists n, exists Fp,
    squash (n, Fp) = k;
  unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = approxF n Fp
}.

Lemma Proof (kli: Input): Output kli.
Proof.
  constructor.
  + intros.
    rewrite <- (squash_unsquash k1).
    rewrite <- (squash_unsquash k2).
    rewrite H.
    trivial.
  + intros.
    remember (unsquash k).
    destruct p as [n f].
    exists n.
    exists f.
    rewrite Heqp.
    rewrite squash_unsquash.
    trivial.
  + intros.
    generalize H; intro.
    rewrite <- (squash_unsquash k) in H.
    rewrite H0 in H.
    rewrite unsquash_squash in H.
    inversion H.
    rewrite H2.
    symmetry.
    trivial.
Qed.

End KnotLemmas1.

Module KnotLemmas2.

Class Input: Type := {
  knot: Type;
  other: Type;
  T: Type;
  t0: T;
  ageable_knot : ageable knot;
  predicate: Type;
  p2p: predicate -> (knot * other -> T);
  approx : nat -> predicate -> predicate;
  pred_ext : forall (p1 p2:predicate),
    (forall x, p2p p1 x = p2p p2 x) ->
    p1 = p2;
  approx_spec : forall n p ko,
    p2p (approx n p) ko =
     if (le_gt_dec n (level (fst ko))) then t0 else p2p p ko
}.

Class Output (input: Input): Prop := {
  approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n);
  approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n
}.

Lemma Proof (kli: Input): Output kli.
Proof.
  constructor.
  + intros.
    extensionality p.
    apply pred_ext.
    intros [k o].
    unfold compose.
    repeat rewrite approx_spec.
    simpl.
    destruct (le_gt_dec n (level k)); auto.
    destruct (le_gt_dec (m+n) (level k)); auto.
    elimtype False; omega.
  + intros.
    extensionality p.
    apply pred_ext.
    intros [k o].
    unfold compose.
    repeat rewrite approx_spec.
    simpl.
    destruct (le_gt_dec (m+n) (level k)); auto.
    destruct (le_gt_dec n (level k)); auto.
    elimtype False; omega.
Qed.

End KnotLemmas2.

Module KnotLemmas_MixVariantHeredTOthRel (K : KNOT__MIXVARIANT_HERED_T_OTH_REL).
  Import K.KI.
  Import K.

  Lemma unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Proof.
    apply
     (@KnotLemmas1.unsquash_inj
       (KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (KnotLemmas1.Proof).
  Qed.
  Arguments unsquash_inj [k1 k2] _.

  Lemma squash_surj : forall k, exists n, exists Fp,
    squash (n, Fp) = k.
  Proof.
    apply
     (@KnotLemmas1.squash_surj
       (KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (KnotLemmas1.Proof).
  Qed.

  Lemma unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = fmap F (approx n) (approx n) Fp.
  Proof.
    apply
     (@KnotLemmas1.unsquash_approx
       (KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (KnotLemmas1.Proof).
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
     (@KnotLemmas2.approx_approx1
       (KnotLemmas2.Build_Input _ _ _ _ _ _ _ _ pred_ext approx_spec)),
     (KnotLemmas2.Proof).
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    apply
     (@KnotLemmas2.approx_approx2
       (KnotLemmas2.Build_Input _ _ _ _ _ _ _ _ pred_ext approx_spec)),
     (KnotLemmas2.Proof).
  Qed.

End KnotLemmas_MixVariantHeredTOthRel.

Module Type KNOT_FULL_OUTPUT.
  Declare Module KI: KNOT_INPUT__MIXVARIANT_HERED_T_OTH_REL.
  Declare Module K0: KNOT__MIXVARIANT_HERED_T_OTH_REL with Module KI := KI.
  Import K0.
  Parameter predicate: Type.
  Parameter pkp: bijection predicate K0.predicate.
End KNOT_FULL_OUTPUT.

Module Type KNOT_FULL.
  Declare Module KI: KNOT_INPUT__MIXVARIANT_HERED_T_OTH_REL.
  Declare Module KO: KNOT_FULL_OUTPUT with Module KI := KI.
  Import KI.
  Import KO.

  Definition knot : Type := KO.K0.knot.
  Definition ageable_knot : ageable knot := KO.K0.ageable_knot.
  Existing Instance ageable_knot.
  Definition predicate: Type := KO.predicate.

  Parameter squash : (nat * F predicate) -> knot.
  Parameter unsquash : knot -> (nat * F predicate).

  Parameter approx : nat -> predicate -> predicate.

  Axiom squash_unsquash : forall k:knot, squash (unsquash k) = k.
  Axiom unsquash_squash : forall (n:nat) (f:F predicate),
    unsquash (squash (n,f)) = (n, fmap F (approx n) (approx n) f).

  Axiom approx_spec : forall n p ko,
    proj1_sig (bij_f _ _ KO.pkp (approx n p)) ko =
     if (le_gt_dec n (level (fst ko)))
     then KI.T_bot
     else proj1_sig (bij_f _ _ KO.pkp p) ko.

  Axiom knot_age1 : forall k:knot,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

  Axiom knot_level : forall k:knot,
    level k = fst (unsquash k).

  Definition knot_rel (k1 k2:knot) :=
    let (n,f) := unsquash k1 in
    let (n',f') := unsquash k2 in
    n = n' /\ KI.Rel predicate f f'.

  Axiom knot_rel_spec: forall k1 k2: knot,
    knot_rel k1 k2 = KO.K0.knot_rel k1 k2.

End KNOT_FULL.

Module Type KNOT_FULL_LEMMAS.
  Declare Module K: KNOT_FULL.
  Import K.

  Axiom unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Arguments unsquash_inj [k1 k2] _.

  Axiom squash_surj : forall k, exists n, exists Fp,
    squash (n, Fp) = k.

  Axiom unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = fmap KI.F (approx n) (approx n) Fp.
  Arguments unsquash_approx [k n Fp] _.

  Axiom approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).

  Axiom approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.

End KNOT_FULL_LEMMAS.

Module KnotFull
  (KI': KNOT_INPUT__MIXVARIANT_HERED_T_OTH_REL)
  (KO': KNOT_FULL_OUTPUT with Module KI := KI'):
  KNOT_FULL with Module KI := KI' with Module KO:=KO'.

  Import MixVariantFunctor.
  Module KI:=KI'.
  Module KO:=KO'.

  Definition knot: Type := KO.K0.knot.
  Definition ageable_knot : ageable knot := KO.K0.ageable_knot.
  Existing Instance ageable_knot.
  Definition predicate: Type := KO.predicate.

  Definition squash : (nat * KI.F predicate) -> knot :=
    fun k => KO.K0.squash
     (fst k, fmap KI.F (bij_f _ _ KO.pkp) (bij_g _ _ KO.pkp) (snd k)).

  Definition unsquash : knot -> (nat * KI.F predicate) :=
    fun k => let (n, f) := KO.K0.unsquash k in
      (n, fmap KI.F (bij_g _ _ KO.pkp) (bij_f _ _ KO.pkp) f).

  Definition approx : nat -> predicate -> predicate :=
    fun n => (bij_g _ _ KO.pkp) oo KO.K0.approx n oo (bij_f _ _ KO.pkp).

  Lemma squash_unsquash : forall k:knot, squash (unsquash k) = k.
  Proof.
    intros; unfold squash, unsquash.
    destruct (KO.K0.unsquash k) as [n f] eqn:?H; simpl.
    rewrite fmap_app, bij_fg_id, fmap_id.
    unfold id.
    rewrite <- H; apply KO.K0.squash_unsquash.
  Qed.

  Lemma unsquash_squash : forall (n:nat) (f:KI.F predicate),
    unsquash (squash (n,f)) = (n, fmap KI.F (approx n) (approx n) f).
  Proof.
    intros; unfold squash, unsquash, approx; simpl.
    rewrite KO.K0.unsquash_squash, !fmap_app, compose_assoc.
    auto.
  Qed.

  Lemma approx_spec : forall n p ko,
    proj1_sig (bij_f _ _ KO.pkp (approx n p)) ko =
     if (le_gt_dec n (level (fst ko)))
     then KI.T_bot
     else proj1_sig (bij_f _ _ KO.pkp p) ko.
  Proof.
    intros.
    rewrite <- KO.K0.approx_spec.
    unfold approx.
    pattern (KO.K0.approx n) at 2.
    rewrite <- (id_unit2 _ _ (KO.K0.approx n)), <- (bij_fg_id KO.pkp).
    reflexivity.
  Qed.

  Lemma knot_age1 : forall k:knot,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.
  Proof.
    intros.
    unfold squash, unsquash.
    rewrite KO.K0.knot_age1.
    destruct (KO.K0.unsquash k) as [n f] eqn:?H.
    destruct n; auto.
    f_equal; simpl.
    rewrite fmap_app, bij_fg_id, fmap_id.
    auto.
  Qed.

  Lemma knot_level: forall k:knot, level k = fst (unsquash k).
  Proof.
    intros.
    unfold unsquash.
    rewrite KO.K0.knot_level.
    destruct (KO.K0.unsquash k) as [n f]; auto.
  Qed.

  Definition knot_rel (k1 k2:knot) :=
    let (n,f) := unsquash k1 in
    let (n',f') := unsquash k2 in
    n = n' /\ KI.Rel predicate f f'.

  Lemma knot_rel_spec: forall k1 k2: knot,
    knot_rel k1 k2 = KO.K0.knot_rel k1 k2.
  Proof.
    intros.
    unfold knot_rel, KO.K0.knot_rel, unsquash.
    destruct (KO.K0.unsquash k1) as [n1 f1].
    destruct (KO.K0.unsquash k2) as [n2 f2].
    f_equal.
    apply prop_ext.
    split; intros.
    + pose proof KI.Rel_fmap _ _ (bij_f _ _ KO.pkp) (bij_g _ _ KO.pkp) _ _ H.
      rewrite !fmap_app, bij_fg_id, fmap_id in H0.
      auto.
    + pose proof KI.Rel_fmap _ _ (bij_g _ _ KO.pkp) (bij_f _ _ KO.pkp) _ _ H.
      auto.
  Qed.

End KnotFull.

Module KnotFullLemmas (K: KNOT_FULL).
  Import K.KI.
  Import K.

  Lemma unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Proof.
    apply
     (@KnotLemmas1.unsquash_inj
       (KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (KnotLemmas1.Proof).
  Qed.
  Arguments unsquash_inj [k1 k2] _.

  Lemma squash_surj : forall k, exists n, exists Fp,
    squash (n, Fp) = k.
  Proof.
    apply
     (@KnotLemmas1.squash_surj
       (KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (KnotLemmas1.Proof).
  Qed.

  Lemma unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = fmap F (approx n) (approx n) Fp.
  Proof.
    apply
     (@KnotLemmas1.unsquash_approx
       (KnotLemmas1.Build_Input _ _ _ _ _ squash_unsquash unsquash_squash)),
     (KnotLemmas1.Proof).
  Qed.
  Arguments unsquash_approx [k n Fp] _.

  Lemma pred_ext : forall (p1 p2:predicate),
    (forall x, proj1_sig (bij_f _ _ KO.pkp p1) x =
               proj1_sig (bij_f _ _ KO.pkp p2) x) ->
    p1 = p2.
  Proof.
    intros.
    change (p1 = p2) with (id K.KO.predicate p1 = id K.KO.predicate p2).
    rewrite <- (bij_gf_id KO.pkp); unfold compose.
    destruct (bij_f _ _ KO.pkp p1) as [pp1 Hp1];
    destruct (bij_f _ _ KO.pkp p2) as [pp2 Hp2].
    simpl in *.
    assert (pp1 = pp2).
    extensionality x; auto.
    subst pp2.
    replace Hp2 with Hp1; auto.
    apply proof_irr.
  Qed.

  Lemma approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).
  Proof.
    apply
     (@KnotLemmas2.approx_approx1
       (KnotLemmas2.Build_Input _ _ _ _ _ _
         (@proj1_sig _ _ oo bij_f _ _ K.KO.pkp) _ pred_ext approx_spec)),
     (KnotLemmas2.Proof).
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    apply
     (@KnotLemmas2.approx_approx2
       (KnotLemmas2.Build_Input _ _ _ _ _ _
         (@proj1_sig _ _ oo bij_f _ _ K.KO.pkp) _ pred_ext approx_spec)),
     (KnotLemmas2.Proof).
  Qed.

End KnotFullLemmas.














(*
Module Type KNOT_FULL_INPUT.
  Parameter F : functor.

  Parameter other : Type.

  Parameter Rel : forall A, F A -> F A -> Prop.

  Parameter Rel_fmap : forall A B (f1: A->B) (f2:B->A) x y,
    Rel A x y ->
    Rel B (fmap F f1 f2 x) (fmap F f1 f2 y).
  Axiom Rel_refl : forall A x, Rel A x x.
  Axiom Rel_trans : forall A x y z,
    Rel A x y -> Rel A y z -> Rel A x z.

  Parameter ORel : other -> other -> Prop.
  Axiom ORel_refl : reflexive other ORel.
  Axiom ORel_trans : transitive other ORel.

  Parameter T:Type.
  Parameter T_bot:T.

  Parameter T_rel : T -> T -> Prop.
  Parameter T_rel_bot : forall x, T_rel T_bot x.
  Parameter T_rel_refl : forall x, T_rel x x.
  Parameter T_rel_trans : transitive T T_rel.

  Parameter Pred: forall K: Type, ageable K -> (K -> K -> Prop) -> Type.

  Parameter Pred2predicate: forall {K agK KRel},
    Pred K agK KRel ->
    { p: K * other -> T |
      (forall k k' k'' o o',
      clos_refl_trans _ age k k' ->
      KRel k' k'' ->
      ORel o o' ->
      T_rel (p (k,o)) (p (k'',o'))) }.

  Parameter predicate2Pred: forall {K agK} {KRel: K -> K -> Prop},
    { p: K * other -> T |
      (forall (k k' k'': K) o o',
      clos_refl_trans _ age k k' ->
      KRel k' k'' ->
      ORel o o' ->
      T_rel (p (k,o)) (p (k'',o'))) } ->
    Pred K agK KRel.

  Axiom P2p2P: forall K agK KRel (P: Pred K agK KRel),
    predicate2Pred (Pred2predicate P) = P.

  Axiom p2P2p: forall K agK KRel p,
    Pred2predicate (@predicate2Pred K agK KRel p) = p.

End KNOT_FULL_INPUT.

Module Type KNOT_FULL.
  Declare Module KI: KNOT_FULL_INPUT.
  Import KI.

  Parameter knot:Type.
  Parameter ageable_knot : ageable knot.
  Existing Instance ageable_knot.
  Parameter knot_rel: knot -> knot -> Prop.

  Definition predicate: Type := Pred knot ageable_knot knot_rel.

  Parameter squash : (nat * F predicate) -> knot.
  Parameter unsquash : knot -> (nat * F predicate).

  Parameter approx : nat -> predicate -> predicate.

  Axiom squash_unsquash : forall k:knot, squash (unsquash k) = k.
  Axiom unsquash_squash : forall (n:nat) (f:F predicate),
    unsquash (squash (n,f)) = (n, fmap F (approx n) (approx n) f).

  Axiom approx_spec : forall n p ko,
    proj1_sig (Pred2predicate (approx n (predicate2Pred p))) ko =
     if (le_gt_dec n (level (fst ko))) then T_bot else proj1_sig p ko.

  Axiom knot_rel_spec: forall (k1 k2:knot),
     knot_rel k1 k2 =
    let (n,f) := unsquash k1 in
    let (n',f') := unsquash k2 in
    n = n' /\ Rel predicate f f'.

  Axiom knot_age1 : forall k:knot,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

  Axiom knot_level : forall k:knot,
    level k = fst (unsquash k).

End KNOT_FULL.

Module KnotFull (KI': KNOT_FULL_INPUT): KNOT_FULL with Module KI:=KI'.

  Import MixVariantFunctor.
  Module KI:=KI'.

  Module Input.
    Definition F: functor := KI.F.
    Definition other: Type := KI.other.
    Definition Rel: forall (A:Type), KI.F A -> KI.F A -> Prop := KI.Rel.

    Definition Rel_fmap : forall A B (f1: A->B) (f2:B->A) x y,
      Rel A x y ->
      Rel B (fmap F f1 f2 x) (fmap F f1 f2 y)
      := KI.Rel_fmap.

    Definition Rel_refl : forall A x, Rel A x x := KI.Rel_refl.

    Definition Rel_trans : forall A x y z,
      Rel A x y -> Rel A y z -> Rel A x z
      := KI.Rel_trans.

    Definition ORel := KI.ORel.
    Definition ORel_refl := KI.ORel_refl.
    Definition ORel_trans := KI.ORel_trans.

    Definition T := KI.T.
    Definition T_bot: T := KI.T_bot.
    Definition T_rel : T -> T -> Prop := KI.T_rel.
    Definition T_rel_bot : forall x, T_rel T_bot x := KI.T_rel_bot.
    Definition T_rel_refl : forall x, T_rel x x := KI.T_rel_refl.
    Definition T_rel_trans : transitive T T_rel := KI.T_rel_trans.
  End Input.

  Module K := Knot_MixVariantHeredTOthRel(Input).
  Module KL := KnotLemmas_MixVariantHeredTOthRel(K).

  Definition knot: Type := K.knot.
  Definition ageable_knot : ageable knot := K.ageable_knot.
  Existing Instance ageable_knot.
  Definition knot_rel: knot -> knot -> Prop := K.knot_rel.
  Definition predicate: Type := KI.Pred knot ageable_knot knot_rel.

  Definition squash : (nat * KI.F predicate) -> knot :=
    fun k => K.squash (fst k, fmap KI.F KI.Pred2predicate KI.predicate2Pred (snd k)).

  Parameter unsquash : knot -> (nat * F predicate).

  Parameter approx : nat -> predicate -> predicate.

  Axiom squash_unsquash : forall k:knot, squash (unsquash k) = k.
  Axiom unsquash_squash : forall (n:nat) (f:F predicate),
    unsquash (squash (n,f)) = (n, fmap F (approx n) (approx n) f).

  Axiom approx_spec : forall n p ko,
    proj1_sig (Pred2predicate (approx n (predicate2Pred p))) ko =
     if (le_gt_dec n (level (fst ko))) then T_bot else proj1_sig p ko.

  Axiom knot_rel_spec: forall (k1 k2:knot),
     knot_rel k1 k2 =
    let (n,f) := unsquash k1 in
    let (n',f') := unsquash k2 in
    n = n' /\ Rel predicate f f'.

  Axiom knot_age1 : forall k:knot,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

  Axiom knot_level : forall k:knot,
    level k = fst (unsquash k).

*)