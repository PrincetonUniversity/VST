(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require Import msl.ageable.
Require Import Eqdep_dec.
Require Import msl.functors.

Open Local Scope nat_scope.

Module Type TY_FUNCTOR.
  Parameter F : Type -> Type.
  Parameter f_F : functor F.
  Existing Instance f_F.

  Parameter T : Type.
  Parameter T_bot : T.

  Parameter other : Type.
End TY_FUNCTOR.

Module Type KNOT.
  Declare Module TF:TY_FUNCTOR.
  Import TF.

  Parameter knot : Type.

  Parameter ag_knot : ageable knot.
  Existing Instance ag_knot.
  Existing Instance ag_prod.

  Definition predicate := (knot * other) -> T.

  Parameter squash : (nat * F predicate) -> knot.
  Parameter unsquash : knot -> (nat * F predicate).

  Definition approx (n:nat) (p:predicate) : predicate := 
     fun w => if le_gt_dec n (level w) then T_bot else p w.

  Axiom squash_unsquash : forall x, squash (unsquash x) = x.
  Axiom unsquash_squash : forall n x', unsquash (squash (n,x')) = (n,fmap (approx n) x').


  Axiom knot_level : forall k:knot,
    level k = fst (unsquash k).

  Axiom knot_age1 : forall k:knot,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

End KNOT.

Module Knot (TF':TY_FUNCTOR) : KNOT with Module TF:=TF'.
  Module TF := TF'.
  Import TF.

  (* Put the discrete pointed order on rhs *)
  Inductive leT : T -> T -> Prop :=
   | leT_refl : forall t, leT t t
   | leT_bot: forall t, leT T_bot t.

  Lemma leT_asym: forall t t',
    leT t t' -> leT t' t -> t = t'.
  Proof.
    intros.
    inversion H; subst; auto.
    inversion H0; subst; auto.
  Qed.

  Fixpoint sinv (n: nat) : Type :=
    match n with
      | O => unit
      | S n => prodT (sinv n) ((F (sinv n) * other) -> T)
    end.

  Fixpoint floor (m:nat) (n:nat) (p:sinv (m+n)) : sinv n :=
    match m as m' return forall (p : sinv (m'+n)), sinv n with
    | O => fun p => p
    | S m' => fun p => floor m' n (fst p)
    end p.

  Definition knot := { n:nat & F (sinv n) }.

  Definition predicate := knot * other -> T.

  Fixpoint stratify (n:nat) (Q:predicate) {struct n} : sinv n :=
    match n as n' return sinv n' with
    | O => tt
    | S n' => ( stratify n' Q, fun v => Q (existT (F oo sinv) n' (fst v),snd v) )
    end.

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

  Definition unstratify (n:nat) (p:sinv n) : predicate := fun w =>
    match w with (existT nw w',e) =>
      match decompose_nat nw n with
        | inleft (existT m Hm) => snd (floor m (S nw) (eq_rect  n _ p (m + S nw) Hm)) (w', e)
        | inright H => T_bot
      end
    end.

  Definition proof_irr_nat := eq_proofs_unicity dec_eq_nat.
  Implicit Arguments proof_irr_nat.

  Lemma floor_shuffle:
    forall (m1 n : nat)
      (p1 : sinv (m1 + S n)) (H1 : (m1 + S n) = (S m1 + n)),
      floor (S m1) n (eq_rect (m1 + S n) sinv p1 (S m1 + n) H1) = fst (floor m1 (S n) p1).
  Proof.
    intros.
    remember (fst (floor m1 (S n) p1)) as p.
    revert n p1 H1 p Heqp.
    induction m1; simpl; intros.
    replace H1 with (refl_equal (S n)) by (apply proof_irr_nat); simpl; auto.
    assert (m1 + S n = S m1 + n) by omega.
    destruct p1 as [p1 f'].
    generalize (IHm1 n p1 H p Heqp).
    simpl.
    clear.
    revert H1; generalize H.
    revert p1 f'.
    rewrite H.
    simpl; intros.
    replace H1 with (refl_equal (S (S (m1 + n)))) by (apply proof_irr_nat).
    simpl.
    replace H0 with (refl_equal (S (m1+n))) in H2 by (apply proof_irr_nat).
    simpl in H2.
    trivial.
  Qed.

  Lemma stratify_unstratify_more : forall n m1 m2 p1 p2,
    floor m1 n p1 = floor m2 n p2 ->

    (stratify n oo unstratify (m1+n)) p1 =
    (stratify n oo unstratify (m2+n)) p2.
  Proof.
    unfold compose; induction n; simpl; intros; auto.
    apply injective_projections; simpl; trivial.

    assert ((m1 + S n) =  (S m1 + n)) by omega.
    assert ((m2 + S n) =  (S m2 + n)) by omega.
    assert (floor (S m1) n (eq_rect (m1 + S n) _ p1 _ H0) = floor (S m2) n (eq_rect (m2 + S n) _ p2 _ H1)).
    do 2 rewrite floor_shuffle.
    congruence.
    generalize (IHn (S m1) (S m2) _ _ H2).
    clear.
    generalize H0 H1.
    revert p1 p2.
    rewrite H0; clear H0.
    rewrite H1; clear H1.
    intros p1 p2 H1 H2.
    replace H1 with (refl_equal (S m1 + n)) by (apply proof_irr_nat).
    replace H2 with (refl_equal (S m2 + n)) by (apply proof_irr_nat).
    simpl; auto.

    apply extensionality; intro v.
    unfold unstratify.
    destruct (decompose_nat n (m2 + S n)) as [[r Hr]|Hr].
    2: elimtype False; omega.
    destruct (decompose_nat n (m1 + S n)) as [[s Hs]|Hs].
    2: elimtype False; omega.
    assert (m2 = r) by omega; subst r.
    assert (m1 = s) by omega; subst s.
    simpl.
    replace Hr with (refl_equal (m2 + S n)) by (apply proof_irr_nat).
    replace Hs with (refl_equal (m1 + S n)) by (apply proof_irr_nat).
    simpl.
    rewrite H; auto.
  Qed.

  Lemma stratify_unstratify : forall n,
         stratify n oo unstratify n = id (sinv n).
  Proof.
    unfold id, compose; intro n; extensionality p; revert n p.
    induction n.

    intros; destruct p; auto.
    
    simpl; intros [p f].
    apply injective_projections; simpl; trivial.

    replace (stratify n (unstratify (S n) (p,f))) with
            (stratify n (unstratify n p)); auto.
    replace (stratify n (unstratify n p)) with
      ((stratify n oo unstratify (0+n)) p) by trivial.
    rewrite (stratify_unstratify_more _ 0 1 p (p,f)); trivial.

    extensionality v.

    destruct (decompose_nat n (S n)) as [[r Hr]|?]; auto.
    assert (r = O) by omega; subst r.
    simpl in *.
    replace Hr with (refl_equal (S n)) by (apply proof_irr_nat); simpl; auto.
    destruct v; auto.

    elimtype False.
    omega.
  Qed.

  Lemma unstratify_stratify1 : forall n (p:predicate) w,
    leT ((unstratify n oo stratify n) p w) (p w).
  Proof.
    unfold compose; induction n; simpl; intros; unfold unstratify.

    (* 0 case *)
    destruct w as [nw rm]; simpl.
    destruct nw as [nw e].
    destruct (decompose_nat nw O) as [[r Hr]|?].
    elimtype False; omega.
    apply leT_bot.

    (* S n case *)
    case_eq w; intros nw rm Hrm.
    destruct nw as [nw e].
    destruct (decompose_nat nw (S n)) as [[r Hr]|?]; try (apply lt_rhs_top).
    destruct r; simpl.

    assert (n = nw) by omega.
    subst nw.
    simpl in Hr.
    replace Hr with (refl_equal (S n)) by apply proof_irr_nat; simpl.
    unfold compose.
    destruct w.
    apply leT_refl.

    simpl in Hr.
    assert (n = r + S nw) by omega.
    revert Hr; subst n.
    intro Hr.
    replace Hr with (refl_equal (S (r+S nw))) by apply proof_irr_nat; simpl.
    clear Hr.

    generalize (IHn p w).
    unfold unstratify.
    rewrite Hrm.
    destruct (decompose_nat nw (r + S nw)) as [[x Hx]|?].
    assert (x = r) by omega; subst x.
    replace Hx with (refl_equal (r + S nw)) by apply proof_irr_nat.
    simpl; auto.
    elimtype False; omega.
    apply leT_bot.
  Qed.

  Lemma unstratify_stratify2 : forall n p w,
     projT1 (fst w) < n ->
        leT (p w) ((unstratify n oo stratify n) p w).
  Proof.
    unfold compose.
    induction n; simpl; intros.

    (* 0 case *)
    inversion H.

    (* S n case *)
    unfold unstratify.
    case_eq w; intros [m rm] e Hw.
    assert (projT1 (fst w) = m).
    rewrite Hw; auto.
    
    destruct (decompose_nat m (S n)) as [[r Hr]|?].
    destruct r; simpl.

    assert (n = m) by omega.
    move H0 after H1.
    subst m. fold sinv. simpl in Hr. rewrite (proof_irr_nat Hr (refl_equal _)). clear Hr. 
    simpl.
    unfold compose.
    rewrite <- Hw.
    apply leT_refl.

    simpl in Hr.
    assert (n = r + S m) by omega.
    revert Hr; subst n.
    intro Hr.
    replace Hr with (refl_equal (S (r+S m))) by apply proof_irr_nat; simpl.
    clear Hr.
    rewrite H0 in H.
    assert (m < (r +  S m)) by omega.
    spec IHn p w.
    rewrite H0 in IHn.
    spec IHn H1.
    revert IHn.
    unfold unstratify.
    rewrite Hw.
    destruct (decompose_nat m (r + S m)) as [[x Hx]|?].
    assert (x = r) by omega; subst x.
    replace Hx with (refl_equal (r + S m)) by apply proof_irr_nat.
    simpl; auto.
    elimtype False; omega.
    elimtype False; omega.
  Qed.

  Lemma unstratify_stratify3 : forall n (p:predicate) w,
    projT1 (fst w) >= n -> leT ((unstratify n oo stratify n) p w) T_bot.
  Proof.
    unfold compose, unstratify; intros n p w H.
    case_eq w; intros [wn rm] e.
    intro Hrm.
    rewrite Hrm in H; simpl in H.
    destruct (decompose_nat wn n) as [[r Hr]|?].
    elimtype False; omega.
    apply leT_bot.
  Qed.

  Definition squash (x:nat * F predicate) : knot :=
    match x with (n,y) => existT (F oo sinv) n (fmap (stratify n) y) end.

  Definition unsquash (x:knot) : (nat * F predicate) :=
    match x with existT n y => (n, fmap (unstratify n) y) end.

  Definition def_knot_level (k:knot) := fst (unsquash k).

  Definition def_knot_age1 (k:knot) : option knot :=
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

  Definition def_knot_unage (k:knot) : knot :=
    match unsquash k with
    | (n,x) => squash (S n,x)
    end.

  Definition approx (n:nat) (p:predicate) : predicate := 
     fun w => if le_gt_dec n (def_knot_level (fst w)) then T_bot else p w.

  Lemma squash_unsquash : forall x, squash (unsquash x) = x.
  Proof.
    intros; destruct x; simpl.
    unfold compose.
    replace (fmap (stratify x) (fmap (unstratify x) f)) with
      ((fmap (stratify x) oo fmap (unstratify x)) f) by trivial.
    rewrite fmap_comp.
    replace (stratify x oo unstratify x) with (id (sinv x)).
    rewrite fmap_id; simpl; auto.
    unfold compose.
    extensionality z.
    replace (stratify x (unstratify x z)) with ((stratify x oo unstratify x) z) by trivial.
    rewrite stratify_unstratify; auto.
  Qed.

  Lemma unsquash_squash : forall n x', unsquash (squash (n,x')) = (n,fmap (approx n) x').
  Proof.
    intros.
    simpl.
    replace (fmap (unstratify n) (fmap (stratify n) x')) with
      ((fmap (unstratify n) oo fmap (stratify n)) x') by trivial.
    rewrite fmap_comp.
    apply injective_projections; simpl; trivial.
    replace (unstratify n oo stratify n) with (approx n); auto.
    extensionality p z.
    apply leT_asym.

    intuition.
    case (le_gt_dec n (def_knot_level a)); intro.
    replace (approx n p (a, b)) with T_bot.
    apply leT_bot.
    unfold approx.
    simpl.
    case (le_gt_dec n (def_knot_level a)); intro.
    trivial.
    elimtype False.
    omega.
    replace (approx n p (a,b)) with (p (a,b)).
    apply unstratify_stratify2.
    simpl.
    destruct a.
    unfold level in g.
    simpl in *.
    auto.
    unfold approx.
    simpl.
    case (le_gt_dec n (def_knot_level a)); intro.
    elimtype False.
    omega.
    trivial.

    intuition.
    destruct (le_lt_dec n (def_knot_level a)).
    replace (approx n p (a, b)) with T_bot.
    apply unstratify_stratify3; auto.
    simpl.
    destruct a.
    unfold level in l.
    simpl in *.
    auto.
    unfold approx.
    simpl.
    case (le_gt_dec n (def_knot_level a)); auto.
    intro.
    elimtype False.
    omega.
    replace (approx n p (a, b)) with (p (a, b)).
    apply unstratify_stratify1; auto.
    unfold approx.
    simpl.
    case (le_gt_dec n (def_knot_level a)); auto.
    intro.
    elimtype False.
    omega.
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
  Implicit Arguments unsquash_inj.

  Lemma ag_knot_facts : ageable_facts knot def_knot_level def_knot_age1.
  Proof.
    constructor.

   unfold def_knot_age1; unfold def_knot_level; simpl; intros x'.
    case_eq (unsquash x'); intros.
    destruct x' as [n' xx']. simpl in *. inv H.
    exists (squash (S n, fmap (unstratify n) xx')).
    rewrite unsquash_squash.
    f_equal.
    f_equal.
    transitivity ((fmap (stratify n) oo fmap (approx (S n)) oo fmap (unstratify n)) xx'); auto.
    do 2 rewrite fmap_comp.
    replace (stratify n oo approx (S n) oo unstratify n) with (@id (sinv n)).
    rewrite fmap_id. auto.
   clear.
    rewrite <- (stratify_unstratify n).
    f_equal. extensionality  a w.
    unfold approx, compose. destruct w.
    simpl fst.
    destruct (le_gt_dec (S n) (def_knot_level k)); auto.
    destruct k. simpl in *.
    unfold def_knot_level in l.
    simpl in *.
    destruct (decompose_nat x n); auto.
    destruct s. elimtype False.
    omega.

    intros.
    unfold def_knot_age1, def_knot_level.
    destruct (unsquash x); simpl.
    destruct n; intuition; try discriminate.

    unfold def_knot_age1, def_knot_level; intros.
    destruct (unsquash x).
    destruct n; inv H; simpl; auto.
  Qed.

  Definition ag_knot : ageable knot :=
    mkAgeable knot def_knot_level def_knot_age1 ag_knot_facts .
  Existing Instance ag_knot.
  Existing Instance ag_prod.


  Lemma knot_level : forall k:knot,
    level k = fst (unsquash k).
  Proof (fun k => refl_equal (def_knot_level k)).

  Lemma knot_age1 : forall k:knot,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.
  Proof (fun k => refl_equal (def_knot_age1 k)).

End Knot.
