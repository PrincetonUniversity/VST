(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

(* Knots with all the bells and whistles *)

Require Import msl.base.
Require Import msl.ageable.

Open Local Scope nat_scope.

Module Type TY_FUNCTOR_FULL.
  Parameter F : Type -> Type -> Type.
  Parameter bimap : forall A B C D, (A -> B) -> (C -> D) -> F B C -> F A D.
  Implicit Arguments bimap [A B C D].

  Axiom bimap_id : forall A B, bimap (id A) (id B) = id (F A B).
  Axiom bimap_comp : forall A B C D E F (f:B -> C) (g:A -> B) (s:F -> E) (t:E -> D),
    bimap s f oo bimap t g = bimap (t oo s) (f oo g).

  Parameter other : Type.

  Parameter Rel : forall A B, F A B -> F A B -> Prop.

  Parameter Rel_bimap : forall A B C D (f:A->B) (s:C->D) x y,
    Rel D A x y ->
    Rel C B (bimap s f x) (bimap s f y).
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

End TY_FUNCTOR_FULL.

Module Type KNOT_FULL.
  Declare Module TF:TY_FUNCTOR_FULL.
  Import TF.

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
    unsquash (squash (n,f)) = (n, bimap (approx n) (approx n) f).

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

End KNOT_FULL.

Module KnotFull (TF':TY_FUNCTOR_FULL) : KNOT_FULL with Module TF:=TF'.
  Module TF:=TF'.
  Import TF.

  Definition sinv_prod X := prod X (F X X * other -> T).

  Definition guppy_sig := (fun X:Type => X * (F X X * other -> T) -> Prop).
  Definition guppy_ty := sigT guppy_sig.

  Definition guppy_step_ty (Z:guppy_ty) : Type :=
    (sig (fun (x:sinv_prod (projT1 Z)) => projT2 Z x)).

  Definition guppy_age (Z:guppy_ty) (x:guppy_step_ty Z) : projT1 Z := fst (proj1_sig x).
  Definition guppy_unage (Z:guppy_ty)
    (H:forall t, projT2 Z (t,fun _ => T_bot))
    (x:projT1 Z) : guppy_step_ty Z :=
    exist (fun z => projT2 Z z) (x, fun _ => T_bot) (H x).

(*
  Definition guppy_step_prop (Z:guppy_ty) (xf:sinv_prod (guppy_step_ty Z)) :=
    forall (k:F (guppy_step_ty Z) (guppy_step_ty Z))
           (k':F (projT1 Z) (projT1 Z)) (o o':other) H,
         ORel o o' ->
         Rel (projT1 Z) (projT1 Z) (bimap (guppy_unage Z H) (guppy_age Z) k) k' ->
         T_rel (snd xf (k,o)) (snd (proj1_sig (fst xf)) (k',o')).
*)

  Definition guppy_step_prop (Z:guppy_ty) (xf:sinv_prod (guppy_step_ty Z)) :=
    (forall (k:F (guppy_step_ty Z) (guppy_step_ty Z)) (o:other) H,
         T_rel (snd xf (k,o))
               (snd (proj1_sig (fst xf)) (bimap (guppy_unage Z H) (guppy_age Z) k,o))) /\
    (forall (k k':F (guppy_step_ty Z) (guppy_step_ty Z)) (o o':other),
         Rel (guppy_step_ty Z) (guppy_step_ty Z) k k' ->
         ORel o o' ->
         T_rel (snd xf (k,o)) (snd xf (k',o'))).

  Definition guppy_step (Z:guppy_ty) : guppy_ty :=
    existT guppy_sig (guppy_step_ty Z) (guppy_step_prop Z).

  Definition guppy_base : guppy_ty :=
    existT guppy_sig unit
      (fun xf =>
        (forall (k k':F unit unit) (o o':other),
          Rel unit unit k k' ->
          ORel o o' ->
          T_rel (snd xf (k,o)) (snd xf (k',o')))).

  Fixpoint guppy (n:nat) : guppy_ty :=
    match n with
    | 0    => guppy_base
    | S n' => guppy_step (guppy n')
    end.

  Definition sinv (n:nat) : Type := projT1 (guppy n).
  Definition sinv_prop (n:nat) : prod (sinv n) (F (sinv n) (sinv n) * other -> T) -> Prop := projT2 (guppy n).

  Fixpoint floor (m:nat) (n:nat) (p:sinv (m+n)) : sinv n :=
    match m as m' return forall (p : sinv (m'+n)), sinv n with
    | O => fun p => p
    | S m' => fun p => floor m' n (fst (proj1_sig p))
    end p.

  Definition knot := { n:nat & F (sinv n) (sinv n) }.

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

  Definition F_sinv n := F (sinv n) (sinv n).

  Definition age1_def (k:knot) : option knot :=
    match k with
      | existT 0 f => None
      | existT (S m) f => Some
          (existT F_sinv m (bimap (sinv_unage m) (sinv_age m) f))
    end.

  Definition age_def x y := age1_def x = Some y.

  Inductive knot_rel_inner : knot -> knot -> Prop :=
    | intro_krel : forall n (f f':F_sinv n),
         Rel _ _ f f' ->
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
        (projT1 IHn, fun v : F_sinv n * other => Q (existT F_sinv n (fst v),snd v))).
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

      exists ((exist (fun x => projT2 (guppy n) x) ( projT1 IHn, fun v:F_sinv n * other => Q (existT (F_sinv) n (fst v),snd v) ) HX)).
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
    match w with (existT nw w',o) =>
      match decompose_nat nw n with
        | inleft (existT m Hm) => snd (proj1_sig (floor m (S nw) (eq_rect  n _ p (m + S nw) Hm))) (w',o)
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
    destruct x; simpl in H.
    destruct x; try discriminate.
    assert (y =
      (existT (F_sinv) x (bimap (sinv_unage x) (sinv_age x) f))).
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

  Definition squash (x:nat * F predicate predicate) : knot :=
    match x with (n,f) => existT (F_sinv) n (bimap (unstrat n) (strat n) f) end.

  Definition unsquash (k:knot) : nat * F predicate predicate :=
    match k with existT n f => (n, bimap (strat n) (unstrat n) f) end.

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
    destruct k; simpl.
    f_equal.
    change ((bimap (unstrat x) (strat x) oo (bimap (strat x) (unstrat x))) f = f).
    rewrite bimap_comp.
    rewrite strat_unstrat.
    rewrite bimap_id.
    auto.
  Qed.

  Lemma unsquash_squash : forall n f,
    unsquash (squash (n,f)) = (n, bimap (approx n) (approx n) f).
  Proof.
    intros.
    unfold unsquash, squash.
    f_equal.
    change ((bimap (strat n) (unstrat n) oo (bimap (unstrat n) (strat n))) f = bimap (approx n) (approx n) f).
    rewrite bimap_comp.
    rewrite unstrat_strat.
    auto.
  Qed.


  Lemma bimap_bimap : forall A B C X Y Z (s:X->Y) (t:Y->Z) (f:B->C) (g:A->B) x,
    bimap s f (bimap t g x) = bimap (t oo s) (f oo g) x.
  Proof.
    intros.
    rewrite <- bimap_comp.
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
    rewrite <- bimap_comp.
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
  Implicit Arguments unsquash_inj.

  
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
    case_eq (unsquash x'); intros.
    destruct x'.
    exists (squash (S x, TF'.bimap (strat x) (unstrat x) f0)).
    rewrite unsquash_squash.
    f_equal. f_equal.
    clear.
    transitivity ((TF'.bimap (unstrat x) (strat x) oo TF'.bimap (approx (S x)) (approx (S x)) oo TF'.bimap (strat x) (unstrat x)) f0); auto.
    do 2 rewrite TF'.bimap_comp.
    rewrite compose_assoc.
    replace (strat x oo approx (S x) oo unstrat x) with (@id (sinv x)).
    rewrite TF'.bimap_id. auto.
    rewrite <- (strat_unstrat x).
    f_equal.
    extensionality a.
    unfold compose, approx.
    case_eq (unstrat x a); intros.
    match goal with
      [ |- _ = exist _ ?X _ ] =>
      assert (x0 = X)
    end.
    Focus 2.
    generalize (approx_obligation_1 (S x)
      (exist (fun p => hered p) x0 h)).
    rewrite <- H0.
    intros. f_equal. apply proof_irr.
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
    n = n' /\ Rel predicate predicate f f'.

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
    destruct k'; destruct k''.
    unfold knot_rel, unsquash in H1.
    destruct H1; subst.
    constructor.
    apply (Rel_bimap _ _ _ _ (strat x0) (unstrat x0)) in H3.
    change f with (id _ f).
    change f0 with (id _ f0).
    rewrite <- bimap_id.
    rewrite <- (strat_unstrat x0).
    rewrite <- bimap_comp.
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
    apply Rel_bimap; auto.
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

End KnotFull.


Module KnotFull_Lemmas (K : KNOT_FULL).
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
  Implicit Arguments unsquash_inj.

  Lemma squash_surj : forall k, exists n, exists Fp,
    squash (n, Fp) = k.
  Proof.
    intros.
    remember (unsquash k).
    destruct p.
    exists n.
    exists f.
    rewrite Heqp.
    rewrite squash_unsquash.
    trivial.
  Qed.

  Lemma unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = bimap (approx n) (approx n) Fp.
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
  Implicit Arguments unsquash_approx.
  
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
    intros.
    extensionality p.
    apply pred_ext.
    intros [k o].
    unfold compose.
    repeat rewrite approx_spec.
    simpl.
    destruct (le_gt_dec n (level k)); auto.
    destruct (le_gt_dec (m+n) (level k)); auto.
    elimtype False; omega.
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    intros.
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



  Lemma bimap_bimap : forall A B C X Y Z (s:X->Y) (t:Y->Z) (f:B->C) (g:A->B) x,
    bimap s f (bimap t g x) = bimap (t oo s) (f oo g) x.
  Proof.
    intros.
    rewrite <- bimap_comp.
    auto.
  Qed.
End KnotFull_Lemmas.
