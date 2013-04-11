(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require msl.knot.
Require msl.knot_full.

Require Import ageable.
Require Import predicates_hered.

Module Type KNOT_INPUT__HERED_PROP_OTH_REL.

  Parameter F : Type -> Type.
  Parameter fmap : forall {A B}, (A->B) -> F A -> F B.

  Axiom fmap_id : forall A, fmap (id A) = id (F A).
  Axiom fmap_comp : forall A B C (f:B->C) (g:A->B),
    fmap f oo fmap g = fmap (f oo g).

  Parameter other : Type.

  Parameter Rel : forall A, F A -> F A -> Prop.
  Parameter Rel_fmap : forall A B (f:A->B) x y,
    Rel A x y -> Rel B (fmap f x) (fmap f y).

  Parameter Rel_unfmap : forall A B (f:A->B) x y,
    Rel B (fmap f x) y ->
      exists y', Rel A x y' /\ fmap f y' = y.

  Axiom Rel_refl : forall A x, Rel A x x.
  Axiom Rel_trans : forall A x y z,
    Rel A x y -> Rel A y z -> Rel A x z.

  Parameter ORel : other -> other -> Prop.
  Axiom ORel_refl : reflexive other ORel.
  Axiom ORel_trans : transitive other ORel.

End KNOT_INPUT__HERED_PROP_OTH_REL.

Module Type KNOT__HERED_PROP_OTH_REL.
  Declare Module KI : KNOT_INPUT__HERED_PROP_OTH_REL.
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
    unsquash (squash (n,x')) = (n, fmap (approx n) x').

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

  (* Convenience lemmas, provable from the above interface *)
  Axiom fmap_fmap : forall A B C (f:B->C) (g:A->B) x,
    fmap f (fmap g x) = fmap (f oo g) x.

  Axiom fmap_id' : forall A (f:A->A),
    (forall x, f x = x) ->
    fmap f = id (F A).

  Axiom unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Implicit Arguments unsquash_inj.
  
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
End KNOT__HERED_PROP_OTH_REL.


Module Type KNOT_INPUT__HERED_PROP_OTH.

  Parameter F : Type -> Type.
  Parameter fmap : forall {A B}, (A->B) -> F A -> F B.

  Axiom fmap_id : forall A, fmap (id A) = id (F A).
  Axiom fmap_comp : forall A B C (f:B->C) (g:A->B),
    fmap f oo fmap g = fmap (f oo g).

  Parameter other : Type.

End KNOT_INPUT__HERED_PROP_OTH.

Module Type KNOT__HERED_PROP_OTH.
  Declare Module KI : KNOT_INPUT__HERED_PROP_OTH.
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
    unsquash (squash (n,x')) = (n, fmap (approx n) x').


  (* Definitions of the "ageable" operations *)
  Axiom knot_level : forall (k:knot),
    level k = fst (unsquash k).
   
  Axiom knot_age1 : forall (k:knot),
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

  (* Convenience lemmas, provable from the above interface *)
  Axiom fmap_fmap : forall A B C (f:B->C) (g:A->B) x,
    fmap f (fmap g x) = fmap (f oo g) x.

  Axiom fmap_id' : forall A (f:A->A),
    (forall x, f x = x) ->
    fmap f = id (F A).

  Axiom unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Implicit Arguments unsquash_inj.
  
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
End KNOT__HERED_PROP_OTH.


Module Type KNOT_INPUT__HERED_PROP.

  Parameter F : Type -> Type.
  Parameter fmap : forall {A B}, (A->B) -> F A -> F B.

  Axiom fmap_id : forall A, fmap (id A) = id (F A).
  Axiom fmap_comp : forall A B C (f:B->C) (g:A->B),
    fmap f oo fmap g = fmap (f oo g).

End KNOT_INPUT__HERED_PROP.

Module Type KNOT__HERED_PROP.
  Declare Module KI : KNOT_INPUT__HERED_PROP.
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
    unsquash (squash (n,x')) = (n, fmap (approx n) x').
  
  (* Definitions of the "ageable" operations *)
  Axiom knot_level : forall (k:knot),
    level k = fst (unsquash k).
   
  Axiom knot_age1 : forall (k:knot),
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

  (* Convenience lemmas, provable from the above interface *)
  Axiom fmap_fmap : forall A B C (f:B->C) (g:A->B) x,
    fmap f (fmap g x) = fmap (f oo g) x.

  Axiom fmap_id' : forall A (f:A->A),
    (forall x, f x = x) ->
    fmap f = id (F A).

  Axiom unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.
  Implicit Arguments unsquash_inj.
  
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

End KNOT__HERED_PROP.


Module Knot_HeredPropOthRel (KI':KNOT_INPUT__HERED_PROP_OTH_REL)
  : KNOT__HERED_PROP_OTH_REL with Module KI:=KI'.

  Module KI:=KI'.

  Module Input.
    Definition F (A B:Type) := KI.F B.
    Definition bimap {A B C D} (s:A -> B) (f:C -> D) (x:F B C) : F A D :=
      KI.fmap f x.

    Lemma bimap_id : forall A B, bimap (id A) (id B) = id (F A B).
    Proof.
      intros; unfold bimap; extensionality.
      rewrite KI.fmap_id; auto.  
    Qed.

    Lemma bimap_comp : forall A B C D E F (f:B -> C) (g:A -> B) (s:F -> E) (t:E -> D),
      bimap s f oo bimap t g = bimap (t oo s) (f oo g).
    Proof.
      intros; unfold bimap; extensionality.
      rewrite <- KI.fmap_comp; auto.
    Qed.

    Definition other := KI.other.
    
    Definition Rel (A B:Type) := KI.Rel B.

    Lemma Rel_bimap : forall A B C D (f:A->B) (s:C->D) x y,
      Rel D A x y ->
      Rel C B (bimap s f x) (bimap s f y).
    Proof.
      unfold Rel, bimap; intros; subst; auto.
      apply KI.Rel_fmap; auto.
    Qed.
    
    Lemma Rel_refl : forall A B x, Rel A B x x.
    Proof.
      intros; apply KI.Rel_refl.
    Qed.
    Lemma Rel_trans : forall A B x y z,
      Rel A B x y -> Rel A B y z -> Rel A B x z.
    Proof.
      intros; eapply KI.Rel_trans; eauto.
    Qed.

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

  Module K := knot_full.KnotFull(Input).
  Module KL := knot_full.KnotFull_Lemmas(K).
  
  Definition knot := K.knot.
  Definition ageable_knot := K.ageable_knot.
  Existing Instance ageable_knot.

  Definition ag_knot_other := ag_prod knot KI.other ageable_knot.
  Existing Instance ag_knot_other.

  Definition expandR : relation (knot * KI.other) :=
    fun x y => K.knot_rel (fst x) (fst y) /\ KI.ORel (snd x) (snd y).

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
    rewrite K.knot_age1 in H.
    case_eq (K.unsquash yk); intros.
    rewrite H2 in H.
    rewrite H2 in H0.
    destruct n; try discriminate.
    inv H.
    destruct z as [zk zo].
    simpl in H0.
    case_eq (K.unsquash zk); intros.
    rewrite H in H0.
    destruct H0; subst n0.
    simpl in H1.
    exists (K.squash (n,f0),zo).
    split; simpl; auto.
    hnf; repeat rewrite K.unsquash_squash; split; auto.
    apply Input.Rel_bimap; auto.
    hnf; simpl.
    rewrite K.knot_age1.
    rewrite H.
    auto.

    destruct x as [xk xo].
    destruct y as [yk yo].
    destruct H.
    simpl in *.
    hnf in H0; simpl in H0.
    rewrite K.knot_age1 in H0.
    destruct z as [zk zo]; simpl in *.
    case_eq (K.unsquash zk); intros.
    rewrite H2 in H0.
    destruct n; try discriminate.
    inv H0.
    hnf in H.
    rewrite K.unsquash_squash in H.
    case_eq (K.unsquash xk); intros.
    rewrite H0 in H; destruct H; subst.
    destruct (KI.Rel_unfmap _ _ _ _ _ H3)
      as [z [? ?]].
    subst f0.
    exists (K.squash (S n0,z),xo).
    hnf; simpl.
    rewrite K.knot_age1.
    rewrite K.unsquash_squash.
    f_equal.
    f_equal.
    apply KL.unsquash_inj.
    rewrite K.unsquash_squash.
    rewrite H0.
    f_equal.
    rewrite KL.bimap_bimap.
    unfold Input.bimap.
    change (S n0) with (1 + n0).
    rewrite <- KL.approx_approx1.
    auto.
    split; simpl; auto.
    hnf.
    rewrite H2.
    rewrite K.unsquash_squash; split; auto.
    hnf.
    rewrite (KL.unsquash_approx H2).
    unfold Input.bimap.
    apply KI.Rel_fmap; auto.
  Qed.

  Definition expandM : @modality (knot * KI.other) ag_knot_other
    := exist _ expandR valid_rel_expandR.

  Lemma expandM_refl : reflexive _ expandM.
  Proof.
    repeat intro.
    split.
    hnf.
    destruct (K.unsquash (fst x)); split; auto.
    apply KI.Rel_refl.
    apply KI.ORel_refl.
  Qed.

  Lemma expandM_trans : transitive _ expandM.
  Proof.
    simpl; unfold expandR;
      repeat intro; intuition.
    unfold K.knot_rel in *.
    destruct (K.unsquash (fst x)).
    destruct (K.unsquash (fst y)).
    destruct (K.unsquash (fst z)).
    intuition.
    eapply KI.Rel_trans; eauto.
    eapply KI.ORel_trans; eauto.
  Qed.

  Hint Resolve expandM_refl expandM_trans.


  Definition assert := { p:pred (knot * KI.other) | boxy expandM p }.

  Lemma hered_hereditary : forall (p:knot*KI.other -> Prop),
    K.hered p <-> (hereditary age p /\ (forall x y, expandR x y -> p x -> p y)).
  Proof.
    intros; split; repeat intro.
    split; repeat intro.
    rewrite K.hered_spec in H.
    revert H1.
    destruct a; destruct a'.
    hnf in H0; simpl in H0.
    case_eq (age1 k); intros;
      rewrite H1 in H0; try discriminate.
    inv H0.
    apply (H k k0 k0 o0 o0).
    apply rt_step; auto.
    hnf.
    destruct (K.unsquash k0); split; auto.
    apply Input.Rel_refl.
    apply Input.ORel_refl.
    auto.

    rewrite K.hered_spec in H.
    destruct H0.
    destruct x as [xk xo].
    destruct y as [yk yo].
    simpl in *.
    revert H1; apply (H xk xk yk xo yo); auto.

    rewrite K.hered_spec; repeat intro.
    destruct H.
    cut (p (k',o)).
    apply H4.
    split; auto.
    revert H3.
    clear -H0 H; induction H0.
    apply H; hnf; simpl; auto.
    hnf in H0.
    unfold knot, ageable_knot.
    rewrite H0; auto.
    auto.
    intuition.
  Qed.

  Program Definition pred2predicate (p:assert) : K.predicate := p.
  Next Obligation.
    destruct p as [[p H1] H2]; simpl.
    hnf in H2.
    rewrite hered_hereditary; auto.
    split; auto.
    intros.
    change (p x) with
      (app_pred (exist (fun p => hereditary age p) p H1) x) in H0.
    rewrite <- H2 in H0.
    apply H0; auto.
  Qed.

  Program Definition predicate2pred (p:K.predicate) : assert := p.
  Next Obligation.
    destruct p as [p Hp]; simpl.
    simpl in H0.
    rewrite hered_hereditary in Hp.
    destruct Hp.
    eapply H1; eauto.
  Qed.
  Next Obligation.
    destruct p as [p Hp]; simpl.
    apply boxy_i; simpl.
    repeat intro.
    split.
    hnf.
    destruct (K.unsquash (fst x)); split; auto.
    apply Input.Rel_refl.
    apply KI.ORel_refl.
    intros.
    rewrite hered_hereditary in Hp.
    destruct Hp.
    eapply H2; eauto.
  Qed.

  Lemma p2p : forall p, pred2predicate (predicate2pred p) = p.
  Proof.
    intros.
    apply KL.pred_ext; intros.
    simpl; auto.
  Qed.

  Lemma exist_ext : forall A F (x y:@sig A F),
    proj1_sig x = proj1_sig y -> x = y.
  Proof.
    intros.
    destruct x; destruct y; simpl in *.
    subst x0.
    replace f0 with f by apply proof_irr; auto.
  Qed.

  Lemma p2p' : forall p, predicate2pred (pred2predicate p) = p.
  Proof.
    intros.
    apply exist_ext.
    apply pred_ext; hnf; simpl; auto.
  Qed.

  Definition squash (nf:(nat * KI.F assert)) : knot :=
    K.squash (fst nf, KI.fmap pred2predicate (snd nf)).

  Definition unsquash (k:knot) : (nat * KI.F assert) :=
    let (n,f) := K.unsquash k in
      (n, KI.fmap predicate2pred f).

  Program Definition approx (n:nat) (p:assert) : assert :=
    fun k => level (fst k) < n /\ p k.
  Next Obligation.
    simpl in *.
    rewrite K.knot_level.
    hnf in H.
    simpl in H.
    rewrite K.knot_age1 in H.
    unfold Input.F, Input.other in *.
    case_eq (K.unsquash a0); intros.
    rewrite H0 in H.
    destruct n0; try discriminate.
    rewrite K.knot_level in H1.
    rewrite H0 in H1.
    simpl in *.
    inv H.
    simpl.
    rewrite K.unsquash_squash.
    simpl.
    omega.
  Qed.
  Next Obligation.
    apply boxy_i; simpl.
    repeat intro.
    split.
    hnf; destruct (K.unsquash (fst x)); split; auto.
    apply Input.Rel_refl.
    apply KI.ORel_refl.
    simpl; intuition.
    destruct H.
    hnf in H.
    simpl in *.
    destruct w'.
    simpl.
    rewrite K.knot_level.
    simpl in H.
    rewrite K.knot_level in H1.
    destruct (K.unsquash a).
    destruct (K.unsquash k).
    destruct H; subst.
    auto.
    simpl in *.
    destruct p.
    simpl; simpl in H2.
    rewrite <- b0 in H2.
    eapply H2; auto.
  Qed.

  Lemma approx_spec : forall n p k,
    proj1_sig (approx n p) k = (level (fst k) < n /\ proj1_sig p k).
  Proof.
    intros; simpl; auto.
  Qed.

  Lemma fmap_fmap : forall A B C (f:B->C) (g:A->B) x,
    KI.fmap f (KI.fmap g x) = KI.fmap (f oo g) x.
  Proof.
    intros.
    rewrite <- KI.fmap_comp.
    auto.
  Qed.

  Lemma fmap_id' : forall A (f:A->A),
    (forall x, f x = x) ->
    KI.fmap f = id _.
  Proof.
    intros.
    replace f with (id A).
    apply KI.fmap_id.
    extensionality; auto.
  Qed.

  Lemma squash_unsquash : forall x,
    squash (unsquash x) = x.
  Proof.
    intros.
    unfold squash, unsquash.
    case_eq (K.unsquash x); simpl; intros.
    rewrite fmap_fmap.
    rewrite fmap_id'.
    unfold id.
    apply KL.unsquash_inj.
    rewrite K.unsquash_squash.
    rewrite H.
    f_equal.
    symmetry.
    apply (KL.unsquash_approx H).
    unfold compose; intros.
    apply p2p.
  Qed.

  Lemma unsquash_squash : forall n x',
    unsquash (squash (n,x')) = (n, KI.fmap (approx n) x').
  Proof.
    intros.
    unfold unsquash, squash.
    rewrite K.unsquash_squash; simpl.
    f_equal.
    unfold Input.bimap.
    repeat rewrite fmap_fmap.
    f_equal.
    unfold compose.
    extensionality p; simpl.
    apply exist_ext.
    apply pred_ext; hnf; simpl; intros.
    rewrite K.approx_spec in H.
    simpl in *.
    unfold unsquash.
    rewrite K.knot_level in H.
    rewrite K.knot_level.
    unfold Input.F, Input.other, knot in *.
    destruct (K.unsquash (fst a)); intros.
    simpl in *; auto.
    destruct (le_gt_dec n n0).
    elim H.
    split; auto.

    rewrite K.approx_spec; intuition.
    rewrite K.knot_level.
    rewrite K.knot_level in H0.
    unfold unsquash in *.
    unfold Input.F, Input.other, knot in *.
    simpl in *.
    destruct (K.unsquash (fst a)).
    simpl in *.
    destruct (le_gt_dec n n0); auto.
    hnf; omega.
  Qed.

  Lemma knot_age1 : forall (k:knot),
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.
  Proof.
    intro; simpl.
    rewrite K.knot_age1.
    unfold unsquash.
    destruct (K.unsquash k).
    destruct n; auto.
    unfold squash.
    f_equal.
    simpl.
    f_equal.
    f_equal.
    rewrite fmap_fmap.
    rewrite fmap_id'.
    auto.
    intro; unfold compose.
    apply p2p.
  Qed.

(*
  Lemma knot_unage : forall (k:knot),
    unage k =
    let (n,x) := unsquash k in squash (S n,x).
  Proof.
    intros; simpl.
    unfold unsquash, squash.
    rewrite K.knot_unage.
    destruct (K.unsquash k).
    simpl.
    do 2 f_equal.
    rewrite fmap_fmap.
    rewrite fmap_id'.
    auto.
    intro; unfold compose.
    apply p2p.
  Qed.
*)

  Lemma knot_level : forall (k:knot),
    level k = fst (unsquash k).
  Proof.
    intros.
    rewrite K.knot_level.
    unfold unsquash.
    destruct (K.unsquash k).
    auto.
  Qed.


  (* Lemmas *)

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
    Fp = KI.fmap (approx n) Fp.
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
  Implicit Arguments unsquash_approx [k n Fp].
  
  Lemma approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).
  Proof.
    intros; extensionality p.
    apply exist_ext.
    apply pred_ext; intros [k o]; simpl; intuition.
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    intros; extensionality p.
    apply exist_ext.
    apply pred_ext; intros [k o]; simpl; intuition.
  Qed.

 
  Definition knot_rel (k1 k2:knot) :=
    let (n,f) := unsquash k1 in
    let (n',f') := unsquash k2 in
    n = n' /\ KI.Rel assert f f'.

  Lemma expandM_spec : forall k k' o o',
    expandM (k,o) (k',o') = (knot_rel k k' /\ KI.ORel o o').
  Proof.
    intros; apply prop_ext; intuition.
    destruct H; simpl in *; auto.
    hnf in H; hnf; auto.
    unfold unsquash.
    destruct (K.unsquash k).
    destruct (K.unsquash k').
    intuition.
    hnf in H2; auto.
    apply KI.Rel_fmap; auto.
    destruct H; auto.
    split; simpl; auto.
    hnf in H0; hnf.
    unfold unsquash in H0.
    destruct (K.unsquash k).
    destruct (K.unsquash k').
    intuition; subst.
    hnf.
    change f with (id (KI.F K.predicate) f).
    rewrite <- KI.fmap_id.
    change f0 with (id (KI.F K.predicate) f0).
    rewrite <- KI.fmap_id.
    assert (id _ = pred2predicate oo predicate2pred).
    extensionality; unfold id, compose; rewrite p2p; auto.
    rewrite H.
    rewrite <- KI.fmap_comp.
    unfold compose.
    apply KI.Rel_fmap; auto.
  Qed.

End Knot_HeredPropOthRel.


Module Knot_HeredPropOth (KI':KNOT_INPUT__HERED_PROP_OTH)
  : KNOT__HERED_PROP_OTH with Module KI:=KI'.

  Module KI:=KI'.

  Module Input.
    Definition F (A B:Type) := KI.F B.
    Definition bimap {A B C D} (s:A -> B) (f:C -> D) (x:F B C) : F A D :=
      KI.fmap f x.

    Lemma bimap_id : forall A B, bimap (id A) (id B) = id (F A B).
    Proof.
      intros; unfold bimap; extensionality.
      rewrite KI.fmap_id; auto.  
    Qed.

    Lemma bimap_comp : forall A B C D E F (f:B -> C) (g:A -> B) (s:F -> E) (t:E -> D),
      bimap s f oo bimap t g = bimap (t oo s) (f oo g).
    Proof.
      intros; unfold bimap; extensionality.
      rewrite <- KI.fmap_comp; auto.
    Qed.

    Definition other := KI.other.
    
    Definition Rel A B := @eq (F A B).
    Lemma Rel_bimap : forall A B C D (f:A->B) (s:C->D) x y,
      Rel D A x y ->
      Rel C B (bimap s f x) (bimap s f y).
    Proof.
      unfold Rel, bimap; intuition; subst; auto.
    Qed.
    Lemma Rel_refl : forall A B x, Rel A B x x.
    Proof.
      intros; hnf; auto.
    Qed.

    Lemma Rel_trans : forall A B x y z,
      Rel A B x y -> Rel A B y z -> Rel A B x z.
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

  Module K := knot_full.KnotFull(Input).
  Module KL := knot_full.KnotFull_Lemmas(K).
  
  Definition knot := K.knot.
  Definition ageable_knot := K.ageable_knot.
  Existing Instance ageable_knot.

  Definition ag_knot_other := ag_prod knot KI.other ageable_knot.
  Existing Instance ag_knot_other.

  Lemma hered_hereditary : forall (p:knot*KI.other -> Prop),
    K.hered p <-> hereditary age p.
  Proof.
    intros; split; repeat intro.
    rewrite K.hered_spec in H.
    hnf in H0.
    simpl in H0.
    destruct a; destruct a'.
    simpl in *.
    case_eq (age1 k); intros.
    rewrite H2 in H0.
    inv H0.
    spec H k k0 k0.
    spec H o0 o0.
    spec H.
    apply rt_step; auto.
    spec H.
    hnf.
    destruct (K.unsquash k0); split; auto.
    hnf; auto.
    apply H; auto.
    hnf; auto.
    rewrite H2 in H0; discriminate.

    rewrite K.hered_spec; intros.
    assert (k' = k'').
    apply KL.unsquash_inj.
    hnf in H1.
    hnf in H2; subst o'.
    destruct (K.unsquash k').
    destruct (K.unsquash k'').
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
    unfold knot, ageable_knot in *.
    rewrite H0; auto.
    auto.
    eauto.
  Qed.

  Program Definition pred2predicate (p:pred (knot*KI.other)) : K.predicate := p.
  Next Obligation.
    destruct p as [p H]; simpl.
    rewrite hered_hereditary; auto.
  Qed.

  Program Definition predicate2pred (p:K.predicate) : pred (knot*KI.other) := p.
  Next Obligation.
    destruct p as [p Hp]; simpl.
    assert (hereditary age p).
    rewrite <- hered_hereditary; auto.
    eapply H1; eauto.
  Qed.

  Lemma p2p : forall p, pred2predicate (predicate2pred p) = p.
  Proof.
    intros.
    apply KL.pred_ext; intros.
    simpl; auto.
  Qed.

  Lemma p2p' : forall p, predicate2pred (pred2predicate p) = p.
  Proof.
    intros.
    apply pred_ext; hnf; simpl; auto.
  Qed.

  Definition squash (nf:(nat * KI.F (pred (knot*KI.other)))) : knot :=
    K.squash (fst nf, KI.fmap pred2predicate (snd nf)).

  Definition unsquash (k:knot) : (nat * KI.F (pred (knot*KI.other))) :=
    let (n,f) := K.unsquash k in
      (n, KI.fmap predicate2pred f).

  Program Definition approx (n:nat) (p:pred (knot*KI.other)) : pred (knot*KI.other) :=
    fun k => level (fst k) < n /\ p k.
  Next Obligation.
    simpl in *.
    rewrite K.knot_level.
    hnf in H.
    simpl in H.
    rewrite K.knot_age1 in H.
    unfold Input.F, Input.other in *.
    case_eq (K.unsquash a0); intros.
    rewrite H0 in H.
    destruct n0; try discriminate.
    rewrite K.knot_level in H1.
    rewrite H0 in H1.
    simpl in *.
    inv H.
    simpl.
    rewrite K.unsquash_squash.
    simpl.
    omega.
  Qed.

  Lemma approx_spec : forall n p k,
    approx n p k = (level (fst k) < n /\ p k).
  Proof.
    intros; simpl; auto.
  Qed.

  Lemma fmap_fmap : forall A B C (f:B->C) (g:A->B) x,
    KI.fmap f (KI.fmap g x) = KI.fmap (f oo g) x.
  Proof.
    intros.
    rewrite <- KI.fmap_comp.
    auto.
  Qed.

  Lemma fmap_id' : forall A (f:A->A),
    (forall x, f x = x) ->
    KI.fmap f = id _.
  Proof.
    intros.
    replace f with (id A).
    apply KI.fmap_id.
    extensionality; auto.
  Qed.

  Lemma squash_unsquash : forall x,
    squash (unsquash x) = x.
  Proof.
    intros.
    unfold squash, unsquash.
    case_eq (K.unsquash x); simpl; intros.
    rewrite fmap_fmap.
    rewrite fmap_id'.
    unfold id.
    apply KL.unsquash_inj.
    rewrite K.unsquash_squash.
    rewrite H.
    f_equal.
    symmetry.
    apply (KL.unsquash_approx H).
    unfold compose; intros.
    apply p2p.
  Qed.

  Lemma unsquash_squash : forall n x',
    unsquash (squash (n,x')) = (n, KI.fmap (approx n) x').
  Proof.
    intros.
    unfold unsquash, squash.
    rewrite K.unsquash_squash; simpl.
    f_equal.
    unfold Input.bimap.
    repeat rewrite fmap_fmap.
    f_equal.
    unfold compose.
    extensionality p; simpl.
    apply pred_ext; hnf; simpl; intros.
    rewrite K.approx_spec in H.
    simpl in *.
    unfold unsquash.
    rewrite K.knot_level in H.
    rewrite K.knot_level.
    unfold Input.F, Input.other, knot in *.
    destruct (K.unsquash (fst a)); intros.
    simpl in *; auto.
    destruct (le_gt_dec n n0).
    elim H.
    split; auto.

    rewrite K.approx_spec; intuition.
    rewrite K.knot_level.
    rewrite K.knot_level in H0.
    unfold unsquash in *.
    unfold Input.F, Input.other, knot in *.
    simpl in *.
    destruct (K.unsquash (fst a)).
    simpl in *.
    destruct (le_gt_dec n n0); auto.
    hnf; omega.
  Qed.

  Lemma knot_age1 : forall (k:knot),
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.
  Proof.
    intro; simpl.
    rewrite K.knot_age1.
    unfold unsquash.
    destruct (K.unsquash k).
    destruct n; auto.
    unfold squash.
    f_equal.
    simpl.
    f_equal.
    f_equal.
    rewrite fmap_fmap.
    rewrite fmap_id'.
    auto.
    intro; unfold compose.
    apply p2p.
  Qed.

(*
  Lemma knot_unage : forall (k:knot),
    unage k =
    let (n,x) := unsquash k in squash (S n,x).
  Proof.
    intros; simpl.
    unfold unsquash, squash.
    rewrite K.knot_unage.
    destruct (K.unsquash k).
    simpl.
    do 2 f_equal.
    rewrite fmap_fmap.
    rewrite fmap_id'.
    auto.
    intro; unfold compose.
    apply p2p.
  Qed.
*)

  Lemma knot_level : forall (k:knot),
    level k = fst (unsquash k).
  Proof.
    intros.
    rewrite K.knot_level.
    unfold unsquash.
    destruct (K.unsquash k).
    auto.
  Qed.


  (* Lemmas *)

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
    Fp = KI.fmap (approx n) Fp.
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
  Implicit Arguments unsquash_approx [k n Fp].
  
  Lemma approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).
  Proof.
    intros; extensionality p.
    apply pred_ext; intros [k o]; simpl; intuition.
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    intros; extensionality p.
    apply pred_ext; intros [k o]; simpl; intuition.
  Qed.

End Knot_HeredPropOth.



Module Knot_HeredProp (KI':KNOT_INPUT__HERED_PROP)
  : KNOT__HERED_PROP with Module KI:=KI'.

  Module KI:=KI'.

  Module Input.
    Definition F (A B:Type) := KI.F B.
    Definition bimap {A B C D} (s:A -> B) (f:C -> D) (x:F B C) : F A D :=
      KI.fmap f x.

    Lemma bimap_id : forall A B, bimap (id A) (id B) = id (F A B).
    Proof.
      intros; unfold bimap; extensionality.
      rewrite KI.fmap_id; auto.  
    Qed.

    Lemma bimap_comp : forall A B C D E F (f:B -> C) (g:A -> B) (s:F -> E) (t:E -> D),
      bimap s f oo bimap t g = bimap (t oo s) (f oo g).
    Proof.
      intros; unfold bimap; extensionality.
      rewrite <- KI.fmap_comp; auto.
    Qed.

    Definition other := unit.
    
    Definition Rel A B := @eq (F A B).
    Lemma Rel_bimap : forall A B C D (f:A->B) (s:C->D) x y,
      Rel D A x y ->
      Rel C B (bimap s f x) (bimap s f y).
    Proof.
      unfold Rel, bimap; intros; subst; auto.
    Qed.

    Lemma Rel_refl : forall A B x, Rel A B x x.
    Proof.
      intros; hnf; auto.
    Qed.

    Lemma Rel_trans : forall A B x y z,
      Rel A B x y -> Rel A B y z -> Rel A B x z.
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

  Module K := knot_full.KnotFull(Input).
  Module KL := knot_full.KnotFull_Lemmas(K).
  
  Definition knot := K.knot.
  Definition ageable_knot := K.ageable_knot.
  Existing Instance ageable_knot.

  Lemma hered_hereditary : forall (p:knot -> Prop),
    K.hered (fun ko => p (fst ko)) <-> hereditary age p.
  Proof.
    intros; split; repeat intro.
    rewrite K.hered_spec in H.
    hnf in H0.
    simpl in H0.
    spec H a a' a'.
    spec H tt tt.
    spec H.
    apply rt_step; auto.
    spec H.
    hnf.
    destruct (K.unsquash a'); split; auto.
    hnf; auto.
    apply H; auto.
    hnf; auto.

    rewrite K.hered_spec; intros.
    assert (k' = k'').
    apply KL.unsquash_inj.
    hnf in H1.
    destruct (K.unsquash k').
    destruct (K.unsquash k'').
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

  Program Definition pred2predicate (p:pred knot) : K.predicate :=
    fun x => p (fst x).
  Next Obligation.
    destruct p as [p H]; simpl.
    rewrite hered_hereditary; auto.
  Qed.

  Program Definition predicate2pred (p:K.predicate) : pred knot :=
    fun x => p (x,tt).
  Next Obligation.
    destruct p as [p Hp]; simpl.
    assert (hereditary age (fun x => p (x,tt))).
    rewrite <- hered_hereditary; auto.
    replace (fun ko:K.knot*Input.other => p (fst ko,tt)) with p.
    auto.
    extensionality.
    destruct x.
    destruct o.
    simpl; auto.
    eapply H1; eauto.
  Qed.

  Lemma p2p : forall p, pred2predicate (predicate2pred p) = p.
  Proof.
    intros.
    apply KL.pred_ext; intros.
    simpl.
    destruct x.
    destruct o.
    simpl; auto.
  Qed.

  Lemma p2p' : forall p, predicate2pred (pred2predicate p) = p.
  Proof.
    intros.
    apply pred_ext; hnf; simpl; auto.
  Qed.

  Definition squash (nf:(nat * KI.F (pred knot))) : knot :=
    K.squash (fst nf, KI.fmap pred2predicate (snd nf)).

  Definition unsquash (k:knot) : (nat * KI.F (pred knot)) :=
    let (n,f) := K.unsquash k in
      (n, KI.fmap predicate2pred f).

  Program Definition approx (n:nat) (p:pred knot) : pred knot :=
    fun k => level k < n /\ p k.
  Next Obligation.
    simpl in *.
    hnf in H.
    simpl in H.
    rewrite K.knot_age1 in H.
    unfold Input.F, Input.other in *.
    case_eq (K.unsquash a); intros.
    rewrite H0 in H.
    destruct n0; try discriminate.
    unfold unsquash in *.
    rewrite K.knot_level in H1.
    rewrite H0 in H1.
    simpl in *.
    inv H.
    rewrite K.knot_level.
    rewrite K.unsquash_squash.
    simpl.
    omega.
  Qed.

  Lemma approx_spec : forall n p k,
    approx n p k = (level k < n /\ p k).
  Proof.
    intros; simpl; auto.
  Qed.

  Lemma fmap_fmap : forall A B C (f:B->C) (g:A->B) x,
    KI.fmap f (KI.fmap g x) = KI.fmap (f oo g) x.
  Proof.
    intros.
    rewrite <- KI.fmap_comp.
    auto.
  Qed.

  Lemma fmap_id' : forall A (f:A->A),
    (forall x, f x = x) ->
    KI.fmap f = id _.
  Proof.
    intros.
    replace f with (id A).
    apply KI.fmap_id.
    extensionality; auto.
  Qed.

  Lemma squash_unsquash : forall x,
    squash (unsquash x) = x.
  Proof.
    intros.
    unfold squash, unsquash.
    case_eq (K.unsquash x); simpl; intros.
    rewrite fmap_fmap.
    rewrite fmap_id'.
    unfold id.
    apply KL.unsquash_inj.
    rewrite K.unsquash_squash.
    rewrite H.
    f_equal.
    symmetry.
    apply (KL.unsquash_approx H).
    unfold compose; intros.
    apply p2p.
  Qed.

  Lemma unsquash_squash : forall n x',
    unsquash (squash (n,x')) = (n, KI.fmap (approx n) x').
  Proof.
    intros.
    unfold unsquash, squash.
    rewrite K.unsquash_squash; simpl.
    f_equal.
    unfold Input.bimap.
    repeat rewrite fmap_fmap.
    f_equal.
    unfold compose.
    extensionality p; simpl.
    apply pred_ext; hnf; simpl; intros.
    rewrite K.approx_spec in H.
    simpl in H.
    destruct (le_gt_dec n (@level K.knot K.ageable_knot a)); auto.
    inv H.

    rewrite K.approx_spec; intuition.
    simpl.
    destruct (le_gt_dec n (@level K.knot K.ageable_knot a)); auto.
    simpl in *.
    rewrite K.knot_level in H0.
    rewrite K.knot_level in l.
    hnf; omega.
  Qed.

  Lemma knot_age1 : forall (k:knot),
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.
  Proof.
    intro; simpl.
    rewrite K.knot_age1.
    unfold unsquash.
    destruct (K.unsquash k).
    destruct n; auto.
    unfold squash.
    f_equal.
    simpl.
    f_equal.
    f_equal.
    rewrite fmap_fmap.
    rewrite fmap_id'.
    auto.
    intro; unfold compose.
    apply p2p.
  Qed.

(*
  Lemma knot_unage : forall (k:knot),
    unage k =
    let (n,x) := unsquash k in squash (S n,x).
  Proof.
    intros; simpl.
    unfold unsquash, squash.
    rewrite K.knot_unage.
    destruct (K.unsquash k).
    simpl.
    do 2 f_equal.
    rewrite fmap_fmap.
    rewrite fmap_id'.
    auto.
    intro; unfold compose.
    apply p2p.
  Qed.
*)

  Lemma knot_level : forall (k:knot),
    level k = fst (unsquash k).
  Proof.
    unfold unsquash; intros.
    rewrite K.knot_level.
    destruct (K.unsquash k); auto.
  Qed.


  (* Lemmas *)

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
    Fp = KI.fmap (approx n) Fp.
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
  Implicit Arguments unsquash_approx [k n Fp].
  
  Lemma approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).
  Proof.
    intros; extensionality p.
    apply pred_ext; intros k; simpl; intuition.
  Qed.

  Lemma approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.
  Proof.
    intros; extensionality p.
    apply pred_ext; intros k; simpl; intuition.
  Qed.

End Knot_HeredProp.


