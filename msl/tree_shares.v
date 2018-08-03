(*
 * Copyright (c) 2009-2016, Andrew Appel, Robert Dockins,
    Aquinas Hobor, and Le Xuan Bach
 *
 *)

Require Import VST.msl.base.
Require Import VST.msl.eq_dec.
Require Import VST.msl.sepalg.
Require Import VST.msl.boolean_alg.

Require Import Recdef.
Require Import NPeano.
Require Import Omega.
Require Import Coq.Arith.Max.

(** This module implements a share model
    via binary trees with boolean-labeled leaves.

    The development is complicated somewhat by the
    fact the ordering used defines multiple isomorphic
    representations of a share.  We must therefore chose
    one to be a canonical representation of the equivalence
    class in order to get strong antisymmetry
    (i.e., antisymmetry up to identity).

    The canonical tree is the one that contains no nonleaf
    full or empty subtrees. A full subtree has all
    leaves labeled with true, whereas an empty subtree
    has all leaves labeled with false.  Canonical trees
    always exists and are unique.  Furthermore, they
    can be straightforwardly calculated.

    Tree union and intersection may generate noncanonical
    trees, so the result must be canonicalized.  However,
    split always generates canonical trees when given a
    canonical tree, as does complement.
 **)

Module Share <: SHARE_MODEL.
  (* Definition of the trees and operations on them *)

  Inductive ShareTree : Set :=
  | Leaf : bool -> ShareTree
  | Node : ShareTree -> ShareTree -> ShareTree
  .

  Fixpoint nonFullTree (x:ShareTree) : Prop :=
   match x with
   | Leaf b   => b = false
   | Node l r => nonFullTree l \/ nonFullTree r
   end.

  Fixpoint nonEmptyTree (x:ShareTree) : Prop :=
   match x with
   | Leaf b   => b = true
   | Node l r => nonEmptyTree l \/ nonEmptyTree r
   end.

  Fixpoint canonicalTree (x:ShareTree) : Prop :=
   match x with
   | Leaf _   => True
   | Node l r => nonFullTree x /\ nonEmptyTree x /\
                 canonicalTree l /\ canonicalTree r
   end.

  Fixpoint union_tree (x y:ShareTree) { struct x } : ShareTree :=
    match x with
    | Leaf true  => Leaf true
    | Leaf false => y
    | Node l1 r1 =>
       match y with
       | Leaf true  => Leaf true
       | Leaf false => x
       | Node l2 r2 =>
            Node (union_tree l1 l2) (union_tree r1 r2)
       end
    end.

  Fixpoint intersect_tree (x y:ShareTree) { struct x } : ShareTree :=
    match x with
    | Leaf false => Leaf false
    | Leaf true  => y
    | Node l1 r1 =>
       match y with
       | Leaf false => Leaf false
       | Leaf true  => x
       | Node l2 r2 =>
            Node (intersect_tree l1 l2) (intersect_tree r1 r2)
       end
    end.

  Fixpoint comp_tree (x:ShareTree) : ShareTree :=
    match x with
    | Leaf b => Leaf (negb b)
    | Node l r => Node (comp_tree l) (comp_tree r)
    end.

  Fixpoint mkCanon (x:ShareTree) : ShareTree :=
    match x with
    | Leaf b => Leaf b
    | Node l r =>
       let l' := mkCanon l in
       let r' := mkCanon r in
       match l', r' with
       | Leaf b1, Leaf b2 =>
          if bool_dec b1 b2
             then Leaf b1
             else Node l' r'
       | _, _ => Node l' r'
       end
    end.

  Fixpoint relativ_tree (z a:ShareTree) {struct z} : ShareTree :=
    match z with
    | Leaf true  => a
    | Leaf false => Leaf false
    | Node l r   => Node (relativ_tree l a) (relativ_tree r a)
    end.

  (* The ordering relation on trees, and its induced isomorphism. *)

  Inductive shareTreeOrd : ShareTree -> ShareTree -> Prop :=
  | Leaf_Ord : forall b1 b2, implb b1 b2 = true ->
       shareTreeOrd (Leaf b1) (Leaf b2)
  | LeafNode_Ord : forall b l r,
       shareTreeOrd (Node (Leaf b) (Leaf b)) (Node l r) ->
       shareTreeOrd (Leaf b) (Node l r)
  | NodeLeaf_Ord : forall b l r,
       shareTreeOrd (Node l r) (Node (Leaf b) (Leaf b)) ->
       shareTreeOrd (Node l r) (Leaf b)
  | Node_Ord : forall l1 l2 r1 r2,
       shareTreeOrd l1 l2 ->
       shareTreeOrd r1 r2 ->
       shareTreeOrd (Node l1 r1) (Node l2 r2)
  .
  Hint Constructors shareTreeOrd.

  Definition shareTreeEq (x y:ShareTree) :=
      shareTreeOrd x y /\ shareTreeOrd y x.
  Hint Unfold shareTreeEq.

  Ltac destruct_bool :=
    repeat (match goal with [ b:bool |- _ ] => destruct b end).

  Ltac invert_ord :=
    repeat (
    match goal with
    | [ H:shareTreeEq _ _ |- _ ] => destruct H
    | [ H:shareTreeOrd (Leaf _) (Leaf _) |- _ ] => inversion H; clear H
    | [ H:shareTreeOrd (Leaf _) (Node _ _) |- _ ] => inversion H; clear H
    | [ H:shareTreeOrd (Node _ _) (Leaf _) |- _ ] => inversion H; clear H
    | [ H:shareTreeOrd (Node _ _) (Node _ _) |- _ ] => inversion H; clear H
    end; subst).

  (* Utility lemmas about full and empty trees, and
     the top and bottom elements. *)

  Lemma nonEmpty_dec : forall x, {nonEmptyTree x}+{~nonEmptyTree x}.
  Proof.
    induction x; simpl; intros; invert_ord; destruct_bool; intuition.
  Defined.

  Lemma nonFull_dec : forall x, {nonFullTree x}+{~nonFullTree x}.
  Proof.
    induction x; simpl; intros; invert_ord; destruct_bool; intuition.
  Defined.

  Lemma geTrueFull : forall x,
      shareTreeOrd (Leaf true) x -> ~nonFullTree x.
  Proof.
    induction x; simpl; intros; invert_ord; destruct_bool; intuition.
  Qed.

  Lemma leFalseEmpty : forall x,
      shareTreeOrd x (Leaf false) -> ~nonEmptyTree x.
  Proof.
    induction x; simpl; intros; invert_ord; destruct_bool; intuition.
  Qed.

  Lemma emptyLeFalse : forall x,
    ~nonEmptyTree x  -> shareTreeOrd x (Leaf false).
  Proof.
    induction x; simpl; intros; invert_ord; destruct_bool; intuition.
  Qed.

  Lemma fullGeTrue : forall x,
    ~nonFullTree x -> shareTreeOrd (Leaf true) x.
  Proof.
    induction x; simpl; intros; invert_ord; destruct_bool; intuition.
  Qed.

  Lemma falseLeaf_bottom : forall x,
    shareTreeOrd (Leaf false) x.
  Proof.
    induction x; auto.
  Qed.

  Lemma trueLeaf_top : forall x,
    shareTreeOrd x (Leaf true).
  Proof.
    induction x; destruct_bool; auto.
  Qed.

  Hint Resolve geTrueFull leFalseEmpty emptyLeFalse fullGeTrue
     falseLeaf_bottom trueLeaf_top.

  Lemma eqFalseLeaf_empty : forall x,
    shareTreeEq (Leaf false) x -> ~nonEmptyTree x.
  Proof.
    induction x; simpl; intros; invert_ord; destruct_bool; intuition.
  Qed.

  Lemma eqTrueLeaf_full : forall x,
    shareTreeEq (Leaf true) x ->
    ~nonFullTree x.
  Proof.
    induction x; simpl; intros; invert_ord; destruct_bool; intuition.
  Qed.

  Lemma emptyTree_canonical_falseLeaf : forall x,
    ~nonEmptyTree x ->
    canonicalTree x ->
    x = Leaf false.
  Proof.
    induction x; simpl; intros; invert_ord; destruct_bool; intuition.
  Qed.

  Lemma fullTree_canonical_trueLeaf : forall x,
    ~nonFullTree x ->
    canonicalTree x ->
    x = Leaf true.
  Proof.
    induction x; simpl; intros; invert_ord; destruct_bool; intuition.
  Qed.

  Hint Resolve eqFalseLeaf_empty eqTrueLeaf_full emptyTree_canonical_falseLeaf
    fullTree_canonical_trueLeaf.

  (* Show that shareTreeOrd is a preorder (reflexive and transitive). *)

  Lemma shareTreeOrd_refl : forall x,
    shareTreeOrd x x.
  Proof.
    induction x; simpl; intros; invert_ord; destruct_bool; intuition.
  Qed.

  Lemma shareTreeOrd_trans_leaf : forall x1 b x3,
    shareTreeOrd x1 (Leaf b) ->
    shareTreeOrd (Leaf b) x3 ->
    shareTreeOrd x1 x3.
  Proof.
    intro x1; induction x1; simpl; intros; invert_ord; destruct_bool; intuition.
    inv H0; invert_ord; destruct_bool; intuition eauto.
    discriminate.
    inv H0; invert_ord; destruct_bool; intuition eauto.
  Qed.

  Lemma shareTreeOrd_trans : forall x1 x2 x3,
    shareTreeOrd x1 x2 -> shareTreeOrd x2 x3 -> shareTreeOrd x1 x3.
  Proof.
    intros x1 x2; revert x1; induction x2; simpl; intros.
    apply shareTreeOrd_trans_leaf with b; auto.
    inv H; inv H0; invert_ord; eauto.
  Qed.

  (* Show that shareTreeEq is an equivalance relation. *)

  Lemma shareTreeEq_refl : forall x,
    shareTreeEq x x.
  Proof. unfold shareTreeEq; intuition; apply shareTreeOrd_refl. Qed.

  Lemma shareTreeEq_sym : forall x y,
    shareTreeEq x y ->
    shareTreeEq y x.
  Proof. unfold shareTreeEq; intuition. Qed.

  Lemma shareTreeEq_trans : forall x y z,
    shareTreeEq x y ->
    shareTreeEq y z ->
    shareTreeEq x z.
  Proof.
    unfold shareTreeEq; intuition;
      apply shareTreeOrd_trans with y; auto.
  Qed.

  (* Show that mkCanon generates canonical trees that are
     equivalant to the original. *)

  Lemma mkCanon_correct : forall x,
    canonicalTree (mkCanon x).
  Proof.
    induction x; simpl; intros; auto.
    case_eq (mkCanon x1); intros.
    case_eq (mkCanon x2); intros.
    case_eq (bool_dec b b0); intros; simpl; auto.
    destruct_bool; intuition.
    elim n; auto.
    rewrite H0 in IHx2.
    simpl in *; intuition.
    rewrite H in IHx1.
    simpl in *; intuition.
  Qed.

  Lemma mkCanon_eq : forall x,
    shareTreeEq x (mkCanon x).
  Proof.
    induction x; simpl; intros; auto.
    split; apply shareTreeOrd_refl.
    case_eq (mkCanon x1); intros; rewrite H in IHx1; destruct IHx1;
    case_eq (mkCanon x2); intros; rewrite H2 in IHx2; destruct IHx2;
      red.
    destruct (bool_dec b b0); subst; intuition; repeat econstructor; eauto.
    split; repeat econstructor; auto.
    split; repeat econstructor; auto.
    split; repeat econstructor; auto.
  Qed.

  Lemma mkCanon_test : forall x y,
    mkCanon x = mkCanon y ->
    shareTreeEq x y.
  Proof.
    intros.
    apply shareTreeEq_trans with (mkCanon x).
    apply mkCanon_eq.
    rewrite H.
    apply shareTreeEq_sym.
    apply mkCanon_eq.
  Qed.

  Lemma mkCanon_nonEmpty : forall x,
    nonEmptyTree x -> nonEmptyTree (mkCanon x).
  Proof.
    induction x; simpl; intros; auto.
    destruct H; [ apply IHx1 in H | apply IHx2 in H ];
      clear IHx1 IHx2.
    destruct (mkCanon x1); destruct (mkCanon x2); simpl in *; auto.
    destruct (bool_dec b b0); subst; intuition; repeat econstructor; eauto.
    destruct (mkCanon x1); destruct (mkCanon x2); simpl in *; auto.
    destruct (bool_dec b b0); subst; intuition; simpl; auto.
  Qed.

  Hint Resolve mkCanon_nonEmpty mkCanon_correct mkCanon_eq.

  (* Show that union and intersection are the LUB and GLB
     for the lattice, respectively. *)

  Lemma union_commute : forall x y,
    union_tree x y = union_tree y x.
  Proof.
    intro x; induction x; destruct y; simpl; intros; auto.
    destruct b; destruct b0; simpl; auto.
    rewrite IHx1.
    rewrite IHx2.
    auto.
  Qed.

  Lemma intersect_commute : forall x y,
    intersect_tree x y = intersect_tree y x.
  Proof.
    intro x; induction x; destruct y; simpl; intros; auto.
    destruct b; destruct b0; simpl; auto.
    rewrite IHx1.
    rewrite IHx2.
    auto.
  Qed.

  Lemma union_upper_bound : forall x y,
    shareTreeOrd x (union_tree x y).
  Proof.
    intro x; induction x; simpl; intros.
    destruct b.
    apply trueLeaf_top.
    apply falseLeaf_bottom.
    destruct y; simpl.
    destruct b.
    apply trueLeaf_top.
    apply shareTreeOrd_refl.
    apply Node_Ord; auto.
  Qed.

  Lemma intersection_lower_bound: forall x y,
    shareTreeOrd (intersect_tree x y) x.
  Proof.
    intro x; induction x; simpl; intros.
    destruct b.
    apply trueLeaf_top.
    apply falseLeaf_bottom.
    destruct y; simpl.
    destruct b.
    apply shareTreeOrd_refl.
    apply falseLeaf_bottom.
    apply Node_Ord; auto.
  Qed.

  Lemma union_least_bound : forall x y z,
    shareTreeOrd x z ->
    shareTreeOrd y z ->
    shareTreeOrd (union_tree x y) z.
  Proof.
    induction x; simpl; intros; invert_ord; try destruct_bool; auto.
    destruct y; invert_ord; try destruct_bool; auto.
    destruct z; invert_ord; try destruct_bool;
      repeat econstructor; auto.
  Qed.

  Lemma intersection_greatest_bound : forall x y z,
    shareTreeOrd z x ->
    shareTreeOrd z y ->
    shareTreeOrd z (intersect_tree x y).
  Proof.
    induction x; simpl; intros; invert_ord; destruct_bool; auto.
    destruct y; invert_ord; try destruct_bool; auto.
    destruct z; invert_ord; try destruct_bool;
      repeat econstructor; auto.
  Qed.

  (* Now prove a few other utility lemmas about
     union and intersection. *)

  Lemma union_idem : forall x,
    x = union_tree x x.
  Proof.
    induction x; simpl; intros.
    destruct b; simpl; auto.
    congruence.
  Qed.

  Lemma intersect_idem : forall x,
     x = intersect_tree x x.
  Proof.
    induction x; simpl; intros.
    destruct b; simpl; auto.
    congruence.
  Qed.

  Lemma union_absorb : forall x y,
     x = union_tree x (intersect_tree x y).
  Proof.
    intro x; induction x; simpl; intros.
    destruct b; auto.
    destruct y; auto.
    destruct b; auto.
    repeat rewrite <- union_idem; auto.
    rewrite <- IHx1.
    rewrite <- IHx2.
    auto.
  Qed.

  Lemma intersect_absorb : forall x y,
     x = intersect_tree x (union_tree x y).
  Proof.
    intro x; induction x; simpl; intros.
    destruct b; auto.
    destruct y; auto.
    destruct b; auto.
    repeat rewrite <- intersect_idem; auto.
    rewrite <- IHx1.
    rewrite <- IHx2.
    auto.
  Qed.

  (* Demonstrate that intersection distributes over
     union and vice-versa. *)

  Lemma intersect_distrib : forall x y z,
    intersect_tree x (union_tree y z) =
    union_tree (intersect_tree x y) (intersect_tree x z).
  Proof.
    induction x; simpl; intros; try destruct_bool; simpl; auto.
    case_eq (union_tree y z); intros.

    destruct y; destruct z; destruct_bool; simpl in *; try discriminate; auto.
    repeat rewrite <- union_idem; auto.
    repeat rewrite <- union_absorb; auto.
    repeat (rewrite union_commute; rewrite <- union_absorb); auto.

    destruct y; destruct z; destruct_bool; try discriminate; simpl in *.
    congruence.
    congruence.
    rewrite <- IHx1.
    rewrite <- IHx2.
    congruence.
  Qed.

  Lemma union_distrib : forall x y z,
    union_tree x (intersect_tree y z) =
    intersect_tree (union_tree x y) (union_tree x z).
  Proof.
    induction x; simpl; intros; try destruct_bool; simpl; auto.
    case_eq (intersect_tree y z); intros.

    destruct y; destruct z; destruct_bool; simpl in *; try discriminate; auto.
    repeat rewrite <- intersect_idem; auto.
    repeat rewrite <- intersect_absorb; auto.
    repeat (rewrite intersect_commute; rewrite <- intersect_absorb); auto.

    destruct y; destruct z; destruct_bool; try discriminate; simpl in *.
    congruence.
    congruence.
    rewrite <- IHx1.
    rewrite <- IHx2.
    congruence.
  Qed.

  (* Demonstrate that union and intersection are
     congruences WRT the shareTreeEq relation. *)

  Lemma Node_Eq : forall x x' y y',
    shareTreeEq x x' ->
    shareTreeEq y y' ->
    shareTreeEq (Node x y) (Node x' y').
  Proof.
    unfold shareTreeEq; intuition; econstructor; auto.
  Qed.

  Lemma intersect_cong0 : forall y x x',
    shareTreeOrd x x' ->
    shareTreeOrd
      (intersect_tree x  y)
      (intersect_tree x' y).
  Proof.
    induction y; simpl; intros.
    rewrite (intersect_commute x (Leaf b)).
    rewrite (intersect_commute x' (Leaf b)).
    revert b x' H; induction x; simpl; intros; destruct_bool;
      solve [ auto | apply falseLeaf_bottom ].

    induction H; simpl in *; intros; destruct_bool; simpl in *; try discriminate;
      solve [ apply shareTreeOrd_refl
            | apply falseLeaf_bottom
            | invert_ord; repeat econstructor; auto
            ].
  Qed.

  Lemma union_cong0 : forall y x x',
    shareTreeOrd x x' ->
    shareTreeOrd
      (union_tree x  y)
      (union_tree x' y).
  Proof.
    induction y; simpl; intros.
    rewrite (union_commute x (Leaf b)).

    rewrite (union_commute x' (Leaf b)).
    revert b x' H; induction x; simpl; intros; destruct_bool;
      solve [ auto | apply trueLeaf_top ].

    induction H; simpl in *; intros; destruct_bool; simpl in *; try discriminate;
      solve [ apply shareTreeOrd_refl
            | apply trueLeaf_top
            | invert_ord; repeat econstructor; auto
            ].
  Qed.

  Lemma intersect_cong1 : forall x x' y,
    shareTreeEq x x' ->
    shareTreeEq
      (intersect_tree x  y)
      (intersect_tree x' y).
  Proof.
    unfold shareTreeEq; intuition; apply intersect_cong0; auto.
  Qed.

  Lemma union_cong1 : forall x x' y,
    shareTreeEq x x' ->
    shareTreeEq
      (union_tree x  y)
      (union_tree x' y).
  Proof.
    unfold shareTreeEq; intuition; apply union_cong0; auto.
  Qed.

  Lemma intersect_cong : forall x x' y y',
    shareTreeEq x x' ->
    shareTreeEq y y' ->
    shareTreeEq
      (intersect_tree x y)
      (intersect_tree x' y').

  Proof.
    intros.
    apply shareTreeEq_trans with (intersect_tree x' y).
    apply intersect_cong1; auto.
    rewrite (intersect_commute x' y).
    rewrite (intersect_commute x' y').
    apply intersect_cong1; auto.
  Qed.

  Lemma union_cong : forall x x' y y',
    shareTreeEq x x' ->
    shareTreeEq y y' ->
    shareTreeEq
      (union_tree x y)
      (union_tree x' y').
  Proof.
    intros.
    apply shareTreeEq_trans with (union_tree x' y).
    apply union_cong1; auto.
    rewrite (union_commute x' y).
    rewrite (union_commute x' y').
    apply union_cong1; auto.
  Qed.

  Lemma comp_cong0 : forall x x',
    shareTreeOrd x x' ->
    shareTreeOrd (comp_tree x') (comp_tree x).
  Proof.
    induction x; simpl.
    induction x'; simpl; intros; invert_ord; destruct_bool;
      repeat econstructor; solve [ auto ].

    simpl; intros.
    inversion H; clear H; subst; invert_ord; destruct_bool; simpl.
    apply falseLeaf_bottom.
    repeat econstructor.
    apply (IHx1 (Leaf false)); auto.
    apply (IHx2 (Leaf false)); auto.
    repeat econstructor.
    apply IHx1; auto.
    apply IHx2; auto.
  Qed.

  Lemma comp_cong : forall x x',
    shareTreeEq x x' ->
    shareTreeEq (comp_tree x') (comp_tree x).
  Proof.
    unfold shareTreeEq; intuition;
     apply comp_cong0; auto.
  Qed.

  Lemma tree_comp1 : forall x,
     shareTreeOrd (Leaf true) (union_tree x (comp_tree x)).
  Proof.
    induction x; simpl; intros.
    destruct b; apply shareTreeOrd_refl.
    apply LeafNode_Ord; apply Node_Ord; auto.
  Qed.

  Lemma tree_comp2 : forall x,
    shareTreeOrd (intersect_tree x (comp_tree x)) (Leaf false).
  Proof.
    induction x; simpl; intros.
    destruct b; apply shareTreeOrd_refl.
    apply NodeLeaf_Ord; apply Node_Ord; auto.
  Qed.

  (* Show that two isomorphic canonical trees are identical. *)
  Lemma canonicalUnique : forall c1 c2,
    shareTreeEq c1 c2 ->
    canonicalTree c1 ->
    canonicalTree c2 ->
    c1 = c2.
  Proof.
    intro c1; induction c1; simpl; intros; destruct H.
    destruct c2; invert_ord; destruct_bool; simpl in *; auto.
    intuition.
    elim (geTrueFull c2_1); auto.
    elim (geTrueFull c2_1); auto.
    elim (geTrueFull c2_2); auto.
    elim (geTrueFull c2_2); auto.
    intuition.
    elim (leFalseEmpty c2_1); auto.
    elim (leFalseEmpty c2_2); auto.
    elim (leFalseEmpty c2_1); auto.
    elim (leFalseEmpty c2_2); auto.
    destruct c2; invert_ord; destruct_bool; simpl in *; auto.
    replace c2_1 with c1_1.
    replace c2_2 with c1_2; auto.
    intuition.
    intuition.
  Qed.

  Lemma mkCanon_test2 : forall x y,
    shareTreeEq x y ->
    mkCanon x = mkCanon y.
  Proof.
    intros; apply canonicalUnique; auto.
    apply shareTreeEq_trans with x; auto.
    apply shareTreeEq_sym; auto.
    apply shareTreeEq_trans with y; auto.
  Qed.

  (* Some basic facts about the relativization operation:
     It is injective when a is nonempty; a number of facts
     about nonemptyness, nonfullness and canonical trees;
     it commutes with union, intersection, mkCanon; and
     it is an associative operation.
   *)

  Lemma relativ_inv : forall a x y,
    nonEmptyTree a ->
    shareTreeOrd (relativ_tree a x) (relativ_tree a y) ->
    shareTreeOrd x y.
  Proof.
    induction a; simpl; intros.
    destruct b; auto.
    invert_ord; auto; try discriminate.
    invert_ord; destruct H; auto.
  Qed.

  Lemma relativ_empty : forall a x,
    nonEmptyTree a -> nonEmptyTree x ->
    nonEmptyTree (relativ_tree a x).
  Proof.
    induction a; simpl; intros; destruct_bool; try discriminate; intuition.
  Qed.

  Lemma relativ_empty1 : forall a x,
    nonEmptyTree (relativ_tree a x) ->
    nonEmptyTree a.
  Proof.
    induction a; simpl; intros; auto.
    destruct b; try discriminate; auto.
    intuition; eauto.
  Qed.

  Lemma relativ_empty2 : forall a x,
    nonEmptyTree (relativ_tree a x) ->
    nonEmptyTree x.
  Proof.
    induction a; simpl; intros; auto.
    destruct b; simpl in *; auto.
    discriminate.
    intuition; eauto.
  Qed.

  Lemma relativ_full1 : forall a x,
    nonFullTree a ->
    nonFullTree (relativ_tree a x).
  Proof.
    induction a; simpl; intros; destruct_bool; try discriminate; intuition.
  Qed.

  Lemma relativ_full2 : forall a x,
    nonFullTree x ->
    nonFullTree (relativ_tree a x).
  Proof.
    induction a; simpl; intros; destruct_bool; try discriminate; simpl; intuition.
  Qed.

  Lemma relativ_full : forall a,
    relativ_tree a (Leaf true) = a.
  Proof.
    induction a; simpl; intros; auto.
    destruct b; auto.
    rewrite IHa1; rewrite IHa2; auto.
  Qed.

  Hint Resolve relativ_empty relativ_empty1 relativ_empty2
    relativ_full relativ_full1 relativ_full2 relativ_inv.

  Lemma relativ_almost_canon : forall a x,
    canonicalTree a ->
    canonicalTree x ->
    nonEmptyTree x ->
    canonicalTree (relativ_tree a x).
  Proof.
    induction a; simpl; intros; destruct_bool; auto.
    intuition auto.
  Qed.

  Lemma relativ_cong : forall a x y,
    shareTreeOrd x y ->
    shareTreeOrd (relativ_tree a x) (relativ_tree a y).
  Proof.
    induction a; simpl; intros; auto.
    destruct b; repeat econstructor; auto.
  Qed.

  Lemma relativ_canon_commute : forall a x,
    canonicalTree a ->
    nonEmptyTree x ->
    mkCanon (relativ_tree a x) =
    relativ_tree a (mkCanon x).
  Proof.
    intros; apply canonicalUnique.
    2: apply mkCanon_correct.
    2: apply relativ_almost_canon; auto.
    apply shareTreeEq_trans with (relativ_tree a x).
    apply shareTreeEq_sym; auto.
    destruct (mkCanon_eq x).
    split; apply relativ_cong; auto.
  Qed.

  Lemma relativ_intersect : forall a x y,
    relativ_tree a (intersect_tree x y) =
    intersect_tree (relativ_tree a x) (relativ_tree a y).
  Proof.
    induction a; simpl; intros; auto.
    destruct b; simpl; auto.
    rewrite IHa1; rewrite IHa2; auto.
  Qed.

  Lemma relativ_union : forall a x y,
    relativ_tree a (union_tree x y) =
    union_tree (relativ_tree a x) (relativ_tree a y).
  Proof.
    induction a; simpl; intros; auto.
    destruct b; simpl; auto.
    rewrite IHa1; rewrite IHa2; auto.
  Qed.

  Lemma relativ_assoc : forall x y z,
    relativ_tree x (relativ_tree y z) =
    relativ_tree (relativ_tree x y) z.
  Proof.
    induction x; simpl; intros.
    destruct b; auto.
    rewrite IHx1.
    rewrite IHx2.
    auto.
  Qed.

  (* Here we have an unfortunate detour to develop a theory
     of many-hole contexts, which allows us to prove
     that relativization is injective on the left. *)

  Inductive Sctx : Set :=
  | NodeB : Sctx -> Sctx -> Sctx
  | NodeR : ShareTree -> Sctx -> Sctx
  | NodeL : Sctx -> ShareTree -> Sctx
  | Hole : Sctx
  .

  Fixpoint Sctx_app (c1 c2:Sctx) {struct c1} : Sctx :=
  match c1 with
  | NodeB l r => NodeB (Sctx_app l c2) (Sctx_app r c2)
  | NodeR l r => NodeR l (Sctx_app r c2)
  | NodeL l r => NodeL (Sctx_app l c2) r
  | Hole      => c2
  end.

  Fixpoint fill (c:Sctx) (x:ShareTree) {struct c} : ShareTree :=
  match c with
  | NodeR l r => Node l (fill r x)
  | NodeL l r => Node (fill l x) r
  | NodeB l r => Node (fill l x) (fill r x)
  | Hole      => x
  end.

  Lemma fill_app : forall c1 c2 x,
    fill c1 (fill c2 x) = fill (Sctx_app c1 c2) x.
  Proof.
    induction c1; simpl; intros.
    rewrite <- IHc1_1.
    rewrite <- IHc1_2.
    auto.
    rewrite IHc1; auto.
    rewrite IHc1; auto.
    auto.
  Qed.

  Lemma fill_id : forall x c,
    fill c x = x -> c = Hole.
  Proof.
    induction x; simpl; intros.
    destruct c; simpl in *; auto; discriminate.
    destruct c; auto; simpl in *.
    inversion H.
    replace (fill c1 (Node x1 x2))
      with (fill (Sctx_app c1 (NodeL Hole x2)) x1) in H1.
    generalize (IHx1 _ H1).
    destruct c1; simpl; intros; discriminate.
    rewrite <- fill_app; simpl; auto.
    inversion H.
    replace (fill c (Node x1 x2)) with
      (fill (Sctx_app c (NodeR x1 Hole)) x2) in H2.
    generalize (IHx2 _ H2).
    destruct c; simpl; intros; discriminate.
    rewrite <- fill_app; simpl; auto.
    inversion H.
    replace (fill c (Node x1 x2)) with
      (fill (Sctx_app c (NodeL Hole x2)) x1) in H1.
    generalize (IHx1 _ H1).
    destruct c; simpl; intros; discriminate.
    rewrite <- fill_app; simpl; auto.
  Qed.

  Definition to_Sctx (a:ShareTree) : nonEmptyTree a -> Sctx.
   revert a.
    refine (fix f (a:ShareTree)  {struct a} : nonEmptyTree a -> Sctx :=
           match a as a' return nonEmptyTree a' -> Sctx with
           | Leaf true => fun H => Hole
           | Leaf false => fun H => False_rec _ _
           | Node l r => fun H =>
              match nonEmpty_dec l, nonEmpty_dec r with
              | left  Hl, left Hr => NodeB (f l Hl) (f r Hr)
              | left  Hl, right _  => NodeL (f l Hl) r
              | right _ , left  Hr => NodeR l (f r Hr)
              | right Hl, right Hr => False_rec _ _
              end
           end).
    simpl in H; discriminate.
    simpl in H; intuition.
  Defined.

  Lemma relativ_to_Sctx : forall a x H,
    relativ_tree a x = fill (to_Sctx a H) x.
  Proof.
    induction a; simpl.
    destruct b; intros; try discriminate.
    simpl; auto.
    intros.
    destruct (nonEmpty_dec a1); destruct (nonEmpty_dec a2); simpl.
    rewrite <- IHa1; rewrite <- IHa2; auto.
    rewrite <- IHa1; auto.
    replace (relativ_tree a2 x) with a2; auto.
    clear -n0.
    induction a2; simpl.
    destruct b; simpl in *; auto.
    elim n0; auto.
    rewrite <- IHa2_1.
    rewrite <- IHa2_2; auto.
    intro; apply n0; simpl; auto.
    intro; apply n0; simpl; auto.
    rewrite <- IHa2.
    replace (relativ_tree a1 x) with a1; auto.
    clear -n.
    induction a1; simpl.
    destruct b; simpl in *; auto.
    elim n; auto.
    rewrite <- IHa1_1.
    rewrite <- IHa1_2; auto.
    intro; apply n; simpl; auto.
    intro; apply n; simpl; auto.
    elimtype False; intuition.
  Qed.

  Lemma relativ_stupid1 : forall x y a,
    nonEmptyTree x ->
    x = relativ_tree a (Node x y) ->
    False.
  Proof.
    intros.
    assert (nonEmptyTree a).
    apply relativ_empty1 with (Node x y).
    rewrite <- H0; auto.
    rewrite (relativ_to_Sctx a (Node x y) H1) in H0.
    replace (fill (to_Sctx a H1) (Node x y))
       with (fill (Sctx_app (to_Sctx a H1) (NodeL Hole y)) x) in H0.
    symmetry in H0.
    generalize (fill_id _ _ H0).
    destruct (to_Sctx a H1); simpl; intros; discriminate.
    rewrite <- fill_app; auto.
  Qed.

  Lemma relativ_stupid2 : forall x y a,
    nonEmptyTree y ->
    y = relativ_tree a (Node x y) ->
    False.
  Proof.
    intros.
    assert (nonEmptyTree a).
    apply relativ_empty1 with (Node x y).
    rewrite <- H0; auto.
    rewrite (relativ_to_Sctx a (Node x y) H1) in H0.
    replace (fill (to_Sctx a H1) (Node x y))
       with (fill (Sctx_app (to_Sctx a H1) (NodeR x  Hole)) y) in H0.
    symmetry in H0.
    generalize (fill_id _ _ H0).
    destruct (to_Sctx a H1); simpl; intros; discriminate.
    rewrite <- fill_app; auto.
  Qed.

  Lemma relativ_stupid3 : forall a1 a2 x,
    nonEmptyTree x ->
    relativ_tree (Node a1 a2) x = x ->
    False.
  Proof.
    intros.
    assert (nonEmptyTree (Node a1 a2)).
    rewrite <- H0 in H.
    simpl in H.
    destruct H.
    left; apply relativ_empty1 with x; auto.
    right; apply relativ_empty1 with x; auto.
    rewrite (relativ_to_Sctx (Node a1 a2) x H1) in H0.
    generalize (fill_id _ _ H0).
    simpl.
    destruct (nonEmpty_dec a1); destruct (nonEmpty_dec a2); intros; try discriminate.
    clear H0 H2.
    simpl in H1; destruct H1; auto.
  Qed.

  (* detour finished.  now we can prove the result of interest,
     which is that relativization is injective on the left
   *)
  Lemma relativ_inv2 : forall a1 a2 x,
    nonEmptyTree x ->
    relativ_tree a1 x = relativ_tree a2 x ->
    a1 = a2.
  Proof.
    induction a1; intros.
    destruct b; simpl in *.
    revert a2 H0.
    induction x; simpl in *.
    subst b; simpl; intros.
    destruct a2; simpl in *.
    destruct b; auto.
    discriminate.

    intros.
    destruct a2; simpl in *.
    destruct b; auto.
    discriminate.
    injection H0; intros.
    destruct H.
    elim relativ_stupid1 with x1 x2 a2_1; auto.
    elim relativ_stupid2 with x1 x2 a2_2; auto.

    destruct a2; simpl in *.
    destruct b; auto.
    subst x; simpl in H; discriminate.
    discriminate.

    simpl in *.
    destruct a2; simpl in *.
    destruct b; try discriminate.
    elimtype False; clear -H H0.
    revert H0.
    intros.
    apply (relativ_stupid3 _ _ _ H H0).

    injection H0; intros.
    rewrite IHa1_1 with a2_1 x; auto.
    rewrite IHa1_2 with a2_2 x; auto.
  Qed.

  (* Define the subset type canonTree and show that it has
     decidable equality. *)

  Definition canonTree :=  { t:ShareTree | canonicalTree t }.

  Lemma shareTree_dec_eq : forall x y:ShareTree, {x=y}+{x<>y}.
  Proof. decide equality; apply bool_dec. Defined.

  Lemma canonTree_eq : forall x y:canonTree, proj1_sig x = proj1_sig y -> x = y.
  Proof.
    intros.
    destruct x as [x Hx].
    destruct y as [y Hy].
    simpl in *.
    subst y.
    replace Hy with Hx by apply proof_irr; auto.
  Qed.

  Lemma canonTree_eq_dec : forall x y:canonTree, {x=y}+{x<>y}.
  Proof.
    intros.
    destruct x as [x Hx].
    destruct y as [y Hy].
    destruct (shareTree_dec_eq x y); [ left | right ].
    apply canonTree_eq; simpl; auto.
    red; intros.
    injection H.
    auto.
  Defined.

  Instance EqDec_canonTree : EqDec canonTree := canonTree_eq_dec.

  (* Show that complement preserves canonical trees *)

  Lemma comp_tree_inv : forall t, comp_tree (comp_tree t) = t.
  Proof.
    induction t; simpl; intros; try destruct_bool; auto.
    rewrite IHt1; rewrite IHt2; auto.
  Qed.

  Lemma comp_full_empty : forall x,
    nonFullTree x -> nonEmptyTree (comp_tree x).
  Proof.
    intro x; induction x; simpl; intros; destruct_bool; intuition.
  Qed.

  Lemma comp_empty_full : forall x,
    nonEmptyTree x -> nonFullTree (comp_tree x).
  Proof.
    intro x; induction x; simpl; intros; destruct_bool; intuition.
  Qed.

  Hint Resolve comp_full_empty comp_empty_full.

  Lemma comp_canonical : forall x,
    canonicalTree x -> canonicalTree (comp_tree x).
  Proof.
    intro x; induction x; simpl; intros; intuition.
  Qed.

  (*** Begin Module Signature Definitions and lemmas ***)

  (* Here we show that canonical share trees form a boolean algrbra.  These
     proofs mainly involve showing that the results above commute in the proper
     ways with mkCanon. *)
  Module BA <: BOOLEAN_ALGEBRA.
    Definition t := canonTree.
    Definition Ord (x y:canonTree) := shareTreeOrd (proj1_sig x) (proj1_sig y).

    Definition lub (x y:canonTree) : canonTree :=
      exist (fun t => canonicalTree t)
      (mkCanon (union_tree (proj1_sig x) (proj1_sig y)))
      (mkCanon_correct _).

    Definition glb (x y:canonTree) : canonTree :=
      exist (fun t => canonicalTree t)
      (mkCanon (intersect_tree (proj1_sig x) (proj1_sig y)))
      (mkCanon_correct _).

    Definition top : canonTree := exist (fun t => canonicalTree t) (Leaf true) I.
    Definition bot : canonTree := exist (fun t => canonicalTree t) (Leaf false) I.

    Definition comp (x:canonTree) : canonTree :=
      exist (fun t => canonicalTree t) (comp_tree (proj1_sig x))
      (comp_canonical _ (proj2_sig x)).

    Lemma ord_refl : forall x, Ord x x.
    Proof.
      intros [x Hx]; unfold Ord; simpl.
      apply shareTreeOrd_refl.
    Qed.

    Lemma ord_trans : forall x y z, Ord x y -> Ord y z -> Ord x z.
    Proof.
      intros [x Hx] [y Hy] [z Hz]; unfold Ord; simpl; intros.
      apply shareTreeOrd_trans with y; auto.
    Qed.

    Lemma ord_antisym : forall x y, Ord x y -> Ord y x -> x = y.
    Proof.
      intros [x Hx] [y Hy]; unfold Ord; simpl; intros.
      apply canonTree_eq; simpl.
      apply canonicalUnique; try split; auto.
    Qed.

    Lemma lub_upper1 : forall x y, Ord x (lub x y).
    Proof.
      intros [x Hx] [y Hy]; unfold Ord; simpl; intros.
      destruct (mkCanon_eq (union_tree x y)).
      apply shareTreeOrd_trans with (union_tree x y); auto.
      apply union_upper_bound.
    Qed.

    Lemma lub_upper2 : forall x y, Ord y (lub x y).
    Proof.
      intros [x Hx] [y Hy]; unfold Ord; simpl; intros.
      destruct (mkCanon_eq (union_tree x y)).
      apply shareTreeOrd_trans with (union_tree x y); auto.
      rewrite union_commute.
      apply union_upper_bound.
    Qed.

    Lemma lub_least : forall x y z,
      Ord x z -> Ord y z -> Ord (lub x y) z.
    Proof.
      intros [x Hx] [y Hy] [z Hz]; unfold Ord; simpl; intros.
      destruct (mkCanon_eq (union_tree x y)).
      apply shareTreeOrd_trans with (union_tree x y); auto.
      apply union_least_bound; auto.
    Qed.

    Lemma glb_lower1 : forall x y, Ord (glb x y) x.
    Proof.
      intros [x Hx] [y Hy]; unfold Ord; simpl; intros.
      destruct (mkCanon_eq (intersect_tree x y)).
      apply shareTreeOrd_trans with (intersect_tree x y); auto.
      apply intersection_lower_bound.
    Qed.

    Lemma glb_lower2 : forall x y, Ord (glb x y) y.
    Proof.
      intros [x Hx] [y Hy]; unfold Ord; simpl; intros.
      destruct (mkCanon_eq (intersect_tree x y)).
      apply shareTreeOrd_trans with (intersect_tree x y); auto.
      rewrite intersect_commute.
      apply intersection_lower_bound.
    Qed.

    Lemma glb_greatest : forall x y z,
      Ord z x -> Ord z y -> Ord z (glb x y).
    Proof.
      intros [x Hx] [y Hy] [z Hz]; unfold Ord; simpl; intros.
      destruct (mkCanon_eq (intersect_tree x y)).
      apply shareTreeOrd_trans with (intersect_tree x y); auto.
      apply intersection_greatest_bound; auto.
    Qed.

    Lemma top_correct : forall x, Ord x top.
    Proof.
      intros [x Hx]; unfold Ord; simpl; auto.
    Qed.

    Lemma bot_correct : forall x, Ord bot x.
    Proof.
      intros [x Hx]; unfold Ord; simpl; auto.
    Qed.

    Lemma comp1 : forall x, lub x (comp x) = top.
    Proof.
      intros [x Hx]; simpl.
      apply canonTree_eq; simpl.
      apply fullTree_canonical_trueLeaf.
      2: apply mkCanon_correct.
      apply geTrueFull.
      apply shareTreeOrd_trans with (union_tree x (comp_tree x)).
      2: destruct (mkCanon_eq (union_tree x (comp_tree x))); auto.
      apply tree_comp1.
    Qed.

    Lemma comp2 : forall x, glb x (comp x) = bot.
    Proof.
      intros [x Hx]; simpl.
      apply canonTree_eq; simpl.
      apply emptyTree_canonical_falseLeaf.
      2: apply mkCanon_correct.
      apply leFalseEmpty.
      apply shareTreeOrd_trans with (intersect_tree x (comp_tree x)).
      destruct (mkCanon_eq (intersect_tree x (comp_tree x))); auto.
      apply tree_comp2.
    Qed.

    Lemma nontrivial : top <> bot.
    Proof. discriminate. Qed.

    Lemma distrib1 : forall x y z,
      glb x (lub y z) = lub (glb x y) (glb x z).
    Proof.
      intros [x Hx] [y Hy] [z Hz]; unfold glb, lub.
      apply canonTree_eq; simpl.
      apply canonicalUnique;
        try apply mkCanon_correct.
      apply shareTreeEq_trans with
        (intersect_tree x (mkCanon (union_tree y z))).
      apply shareTreeEq_sym.
      apply mkCanon_eq.
      apply shareTreeEq_trans with
        (union_tree (mkCanon (intersect_tree x y)) (mkCanon (intersect_tree x z))).
      2: apply mkCanon_eq.
      apply shareTreeEq_trans with
        (intersect_tree x (union_tree y z)).
      apply intersect_cong.
      apply shareTreeEq_refl.
      apply shareTreeEq_sym.
      apply mkCanon_eq.
      apply shareTreeEq_trans with
        (union_tree (intersect_tree x y) (intersect_tree x z)).
      rewrite intersect_distrib.
      apply shareTreeEq_refl.
      apply union_cong.
      apply mkCanon_eq.
      apply mkCanon_eq.
    Qed.

  End BA.

  Module BAF := BA_Facts BA.
  Include BAF.

  (* Now, we prove the axioms about relativization.
     Again, this mostly involves packing and unpacking
     the canonTree type and pushing around mkCanon.
   *)

    Definition rel (a x:t) : t.
      case_eq (proj1_sig x); intros.
      destruct b.
      exact a.
      exact (exist (fun t => canonicalTree t) (Leaf false) I).
      refine (exist _ (relativ_tree (proj1_sig a) (proj1_sig x)) _).
      apply relativ_almost_canon.
      apply (proj2_sig a).
      apply (proj2_sig x).
      destruct x; simpl in *; subst; simpl in *; intuition.
    Defined.

    Lemma relativ_tree_empty : forall a x,
      nonEmptyTree a -> nonEmptyTree x ->
      nonEmptyTree (relativ_tree a x).
    Proof.
      induction a; simpl; intros.
      destruct b; auto.
      intuition; eauto.
    Qed.

    Lemma relativ_tree_nonid : forall a x1 x2,
      nonEmptyTree a ->
      a = relativ_tree a (Node x1 x2) ->
      False.
    Proof.
      induction a; simpl; intros; try destruct_bool; try discriminate.
      injection H0; clear H0; intros.
      intuition; eauto.
    Qed.

    Lemma rel_classification : forall a x,
      { x = bot /\ rel a x = bot } +
      { x <> bot /\ proj1_sig (rel a x) = relativ_tree (proj1_sig a) (proj1_sig x)
        /\ (a = bot <-> rel a x = bot) }.
    Proof.
      intros [a ?] [x ?].
      simpl.
      destruct x; try destruct_bool; simpl.
      right; split.
      red; intros.
      discriminate H.
      split.
      rewrite relativ_full; auto.
      split; intros.
      injection H; clear H; intros.
      subst a.
      apply canonTree_eq; simpl; auto.
      apply canonTree_eq; simpl.
      injection H; auto.
      left; split; auto.
      apply canonTree_eq; auto.
      right; split.
      red; intros; discriminate.
      split; auto.
      split; intros.
      apply canonTree_eq; simpl; auto.
      injection H; clear H; intros.
      rewrite H; auto.
      injection H; clear H; intros.
      apply canonTree_eq; simpl; auto.
      destruct a; simpl in *; destruct_bool; auto; try discriminate.
    Defined.

    Lemma rel_inj_r : forall a1 a2 x, x <> bot -> rel a1 x = rel a2 x -> a1 = a2.
    Proof.
      intros.
      apply canonTree_eq.
      destruct (rel_classification a1 x); intuition.
      destruct (rel_classification a2 x); intuition.
      apply relativ_inv2 with (proj1_sig x); auto.
      destruct x; simpl.
      destruct x; simpl.
      destruct b; auto.
      elim H; simpl.
      apply canonTree_eq; auto.
      generalize c; simpl; intuition.
      rewrite <- H3.
      rewrite <- H7.
      rewrite H0.
      auto.
    Qed.

    Lemma rel_inj_l : forall a x y, a <> bot -> rel a x = rel a y -> x = y.
    Proof.
      intros.
      apply canonTree_eq.
      destruct a as [a ?]; destruct x as [x ?]; destruct y as [y ?]; simpl.
      assert (nonEmptyTree a).
      destruct a; simpl in *.
      destruct b; auto.
      elim H; apply canonTree_eq; simpl; auto.
      decompose [and] c; auto.
      unfold rel in *; simpl in *.
      destruct x; destruct y;
        destruct_bool; auto;
        injection H0; clear H0; try congruence; intros.

      elim (relativ_tree_nonid a y1 y2); auto.
      simpl in c1; decompose [and] c1.
      generalize (relativ_tree_empty a (Node y1 y2) H1 H4).
      rewrite <- H0; simpl; intros; discriminate.
      elim (relativ_tree_nonid a x1 x2); auto.
      simpl in c0; decompose [and] c0.
      generalize (relativ_tree_empty a (Node x1 x2) H1 H4).
      rewrite H0; simpl; intros; discriminate.
      apply canonicalUnique; auto.
      split; apply relativ_inv with a; auto; rewrite H0; apply shareTreeOrd_refl.
    Qed.

    Lemma rel_assoc : forall x y z, rel x (rel y z) = rel (rel x y) z.
    Proof.
      intros.
      apply canonTree_eq.
      destruct (rel_classification x (rel y z)); intuition.
      rewrite H0.
      destruct (rel_classification (rel x y) z); intuition.
      rewrite H1.
      simpl; auto.
      destruct (rel_classification x y); intuition.
      rewrite H7; auto.
      rewrite H3.
      rewrite H7.
      rewrite <- relativ_assoc.
      destruct (rel_classification y z); intuition.

      rewrite H1.
      destruct (rel_classification y z); intuition.
      destruct (rel_classification (rel x y) z); intuition.
      rewrite H9.
      destruct (rel_classification x y); intuition.
      rewrite H13.
      rewrite H5.
      apply relativ_assoc.
    Qed.

    Lemma rel_bot1 : forall a, rel a bot = bot.
    Proof.
      intros [a ?]; auto.
    Qed.

    Lemma rel_bot2 : forall x, rel bot x = bot.
    Proof.
      intros e.
      destruct (rel_classification bot e); intuition.
    Qed.

    Lemma rel_top1 : forall a, rel a top = a.
    Proof.
      intros a.
      destruct (rel_classification a top); intuition.
    Qed.

    Lemma rel_top2 : forall x, rel top x = x.
    Proof.
      intro x.
      destruct (rel_classification top x); intuition.
      congruence.
      apply canonTree_eq.
      rewrite H1.
      simpl; auto.
    Qed.

    Lemma rel_preserves_glb : forall a x y, rel a (glb x y) = glb (rel a x) (rel a y).
    Proof.
      intros a x y.
      destruct (rel_classification a x); intuition.
      rewrite H0.
      rewrite H.
      rewrite glb_commute.
      rewrite glb_bot.
      rewrite rel_bot1.
      rewrite glb_commute.
      rewrite glb_bot.
      auto.
      destruct (rel_classification a y); intuition.
      rewrite H4.
      rewrite H2.
      rewrite glb_bot.
      rewrite glb_bot.
      apply rel_bot1.
      apply canonTree_eq.
      simpl.
      rewrite H1.
      rewrite H5.
      rewrite <- relativ_intersect.
      destruct (rel_classification a (glb x y)); intuition.
      rewrite H8.
      simpl.
      injection H6; intros.
      apply (mkCanon_test2 (Leaf false)).
      apply shareTreeEq_trans with (relativ_tree (proj1_sig a) (Leaf false)).
      split.
      apply falseLeaf_bottom.
      apply emptyLeFalse.
      intro G.
      generalize (relativ_empty2 _ _ G); auto.
      simpl; intros; discriminate.
      generalize (mkCanon_test _ (Leaf false) H9).
      unfold shareTreeEq; intuition; apply relativ_cong; auto.
      rewrite H9.
      simpl.
      rewrite relativ_canon_commute; auto.
      destruct a; auto.
      destruct (nonEmpty_dec (intersect_tree (proj1_sig x) (proj1_sig y))); auto.
      elim H6.
      apply canonTree_eq; simpl.
      symmetry.
      apply (mkCanon_test2 (Leaf false)).
      split.
      apply falseLeaf_bottom.
      apply emptyLeFalse; auto.
    Qed.

    Lemma rel_preserves_lub : forall a x y, rel a (lub x y) = lub (rel a x) (rel a y).
    Proof.
      intros a x y.
      destruct (rel_classification a x); intuition.
      rewrite H0.
      rewrite H.
      rewrite lub_commute.
      rewrite lub_bot.
      rewrite lub_commute.
      rewrite lub_bot.
      auto.
      destruct (rel_classification a y); intuition.
      rewrite H4.
      rewrite H2.
      rewrite lub_bot.
      rewrite lub_bot.
      auto.

      apply canonTree_eq.
      simpl.
      rewrite H1.
      rewrite H5.
      rewrite <- relativ_union.
      destruct (rel_classification a (lub x y)); intuition.
      rewrite H8.
      simpl.
      injection H6; intros.
      apply (mkCanon_test2 (Leaf false)).
      apply shareTreeEq_trans with (relativ_tree (proj1_sig a) (Leaf false)).
      split.
      apply falseLeaf_bottom.
      apply emptyLeFalse.
      intro G.
      generalize (relativ_empty2 _ _ G).
      simpl; intros; discriminate.
      generalize (mkCanon_test _ (Leaf false) H9).
      unfold shareTreeEq; intuition; apply relativ_cong; auto.
      rewrite H9.
      simpl.
      rewrite relativ_canon_commute; auto.
      destruct a; auto.
      destruct (nonEmpty_dec (union_tree (proj1_sig x) (proj1_sig y))); intros; auto.
      elim H6.
      apply canonTree_eq; simpl.
      symmetry.
      apply (mkCanon_test2 (Leaf false)).
      split.
      apply falseLeaf_bottom.
      apply emptyLeFalse; auto.
    Qed.

  (* Axioms about splittability. These follow easily from relativization.
   *)

    Definition leftTree : canonTree.
      exists (Node (Leaf true) (Leaf false)).
      simpl; intuition.
    Defined.

    Definition rightTree : canonTree.
      exists (Node (Leaf false) (Leaf true)).
      simpl; intuition.
    Defined.

    Definition split (x:canonTree) := (rel x leftTree, rel x rightTree).

    Lemma split_disjoint : forall x1 x2 x,
      split x = (x1, x2) -> glb x1 x2 = bot.
    Proof.
      unfold split; intros.
      inv H.
      rewrite <- rel_preserves_glb.
      replace (glb leftTree rightTree) with bot.
      apply rel_bot1.
      apply canonTree_eq; simpl; auto.
    Qed.

    Lemma split_together : forall x1 x2 x,
      split x = (x1, x2) -> lub x1 x2 = x.
    Proof.
      unfold split; intros.
      inv H.
      rewrite <- rel_preserves_lub.
      replace (lub leftTree rightTree) with top.
      apply rel_top1.
      apply canonTree_eq; simpl; auto.
    Qed.

    Lemma split_nontrivial : forall x1 x2 x,
      split x = (x1, x2) ->
        (x1 = bot \/ x2 = bot) ->
        x = bot.
    Proof.
      unfold split; intros.
      inv H; destruct H0.
      destruct (canonTree_eq_dec x bot); auto.
      replace bot with (rel x bot) in H.
      apply rel_inj_l in H; auto.
      inv H.
      apply rel_bot1.
      destruct (canonTree_eq_dec x bot); auto.
      replace bot with (rel x bot) in H.
      apply rel_inj_l in H; auto.
      inv H.
      apply rel_bot1.
    Qed.

    (* Token Factory definitions and proofs.
       We specify token factories and tokens
       inductively on trees, which makes
       the proofs fairly straightforward.
     *)

    Inductive isTokenFactory' : ShareTree -> nat -> Prop :=
      | isTokFac_0 : isTokenFactory' (Leaf true) O
      | isTokFac_S_true : forall t n,
          isTokenFactory' t (S n) ->
          isTokenFactory' (Node (Leaf true) t) (S n)
      | isTokFac_S_false : forall t n,
          isTokenFactory' t n ->
          isTokenFactory' (Node (Leaf false) t) (S n).

    Inductive isToken' : ShareTree -> nat -> Prop :=
      | isTok_0 : isToken' (Leaf false) O
      | isTok_S_true : forall t n,
          isToken' t n ->
          isToken' (Node (Leaf true) t) (S n)
      | isTok_S_false : forall t n,
          isToken' t (S n) ->
          isToken' (Node (Leaf false) t) (S n).

    Definition isTokenFactory (x:t) (n:nat) := isTokenFactory' (proj1_sig x) n.
    Definition isToken (x:t) (n:nat) := isToken' (proj1_sig x) n.

    Lemma isTokenFactory_canon : forall n fac,
      isTokenFactory' fac n -> canonicalTree fac.
    Proof.
      intros n fac H; induction H; simpl; intuition.
      right; destruct t0; simpl in *; auto.
      inv H.
      intuition.
      right; destruct t0; simpl in *; auto.
      inv H; auto.
      intuition.
    Qed.

    Lemma isToken_canon : forall n tok,
      isToken' tok n -> canonicalTree tok.
    Proof.
      intros n tok H; induction H; simpl; intuition.
      right; destruct t0; simpl in *; auto.
      inv H; auto.
      intuition.
      right; destruct t0; simpl in *; auto.
      inv H.
      intuition.
    Qed.


    Fixpoint split_tok1 (n:nat) (x:ShareTree) {struct x} : ShareTree :=
      match x with
      | Node (Leaf true)  t2 =>
          match n with
          | O    => Node (Leaf true) (Leaf false)
          | S n' => Node (Leaf true) (split_tok1 n' t2)
          end
      | Node (Leaf false) t2 => Node (Leaf false) (split_tok1 n t2)
      | _ => Leaf false
      end.

    Fixpoint split_tok2 (n:nat) (x:ShareTree) {struct x} : ShareTree :=
      match x with
      | Node (Leaf true)  t2 =>
          match n with
          | O    => Node (Leaf false) t2
          | S n' => Node (Leaf false) (split_tok2 n' t2)
          end
      | Node (Leaf false) t2 => Node (Leaf false) (split_tok2 n t2)
      | _ => x
      end.

    Lemma split_tok_lub : forall tok n,
      shareTreeEq tok (union_tree (split_tok1 n tok) (split_tok2 n tok)).
    Proof.
      induction tok; simpl; intros.
      destruct b; auto.
      destruct tok1; simpl.
      destruct b.
      destruct n; simpl; auto.
      apply Node_Eq; auto.
      apply shareTreeEq_refl.
      apply Node_Eq; auto.
      apply Node_Eq; auto.
      apply Node_Eq; auto.
      apply Node_Eq; auto.
      apply shareTreeEq_refl.
      apply shareTreeEq_refl.
      apply shareTreeEq_refl.
    Qed.

    Lemma split_tok_glb : forall tok n,
      shareTreeOrd (intersect_tree (split_tok1 n tok) (split_tok2 n tok)) (Leaf false).
    Proof.
      induction tok; simpl; intros; auto.
      destruct tok1; simpl; auto.
      destruct b; simpl; auto.
      destruct n; simpl.
      constructor; auto.
      constructor; auto.
    Qed.

    Lemma split_tok1_correct : forall tok n m,
      isToken' tok m ->
      gt m n ->
      isToken' (split_tok1 n tok) (S n).
    Proof.
      intros tok n m H; revert n; induction H; intros.
      inv H; simpl.
      simpl.
      destruct n0.
      inv H0.
      constructor.
      constructor.
      constructor.
      constructor.
      constructor.
      apply IHisToken'.
      omega.
      simpl.
      constructor.
      apply IHisToken'.
      auto.
    Qed.

    Lemma split_tok2_correct : forall tok n m,
      isToken' tok m ->
      gt m n ->
      isToken' (mkCanon (split_tok2 n tok)) (m - (S n)).
    Proof.
      intros tok n m H; revert n; induction H; intros.
      simpl.
      constructor.
      simpl.
      destruct n0.
      simpl.
      replace (mkCanon t0) with t0.
      inv H; simpl.
      constructor.
      constructor; auto.
      constructor; auto.
      constructor.
      constructor; auto.
      apply canonicalUnique.
      apply mkCanon_eq.
      apply isToken_canon with n; auto.
      apply mkCanon_correct.
      simpl.
      case_eq (mkCanon (split_tok2 n0 t0)); intros.
      destruct b.
      elimtype False.
      clear - H H1.
      revert n0 H H1.
      induction t0; simpl; intros.
      inv H.
      discriminate.
      inv H.
      destruct n0.
      simpl in H1.
      destruct (mkCanon t0_2); try discriminate.
      destruct b; discriminate.
      simpl in H1.
      destruct (mkCanon (split_tok2 n0 t0_2)); try discriminate.
      destruct b; discriminate.
      simpl in H1.
      destruct (mkCanon (split_tok2 n0 t0_2)); try discriminate.
      destruct b; discriminate.
      specialize ( IHisToken' n0).
      spec IHisToken'; [ omega | ].
      rewrite H1 in IHisToken'.
      inv IHisToken'.
      constructor.
      specialize ( IHisToken' n0).
      spec IHisToken'.
      omega.
      rewrite H1 in IHisToken'.
      inversion IHisToken'.
      subst.
      constructor; auto.
      rewrite H5; auto.
      constructor.
      subst; rewrite H5; auto.
      specialize ( IHisToken' n0 H0).
      simpl split_tok2.
      inversion IHisToken'.
      simpl minus.
      simpl.
      rewrite <- H2.
      rewrite <- H3.
      constructor.
      simpl.
      rewrite <- H1.
      rewrite <- H2.
      constructor.
      rewrite H1.
      rewrite H2.
      auto.
      simpl.
      rewrite <- H1.
      rewrite <- H2.
      constructor.
      rewrite H1.
      rewrite H2.
      auto.
    Qed.

    Definition split_token (n:nat) (tok:t) : t * t :=
      match n with
      | O => (bot,tok)
      | S n' =>
        (exist (fun x => canonicalTree x) (mkCanon (split_tok1 n' (proj1_sig tok))) (mkCanon_correct _)
        ,exist (fun x => canonicalTree x) (mkCanon (split_tok2 n' (proj1_sig tok))) (mkCanon_correct _)
        )
      end.

    Lemma Eq_Ord : forall x y,
      shareTreeEq x y -> shareTreeOrd x y.
    Proof.
      unfold shareTreeEq; intuition.
    Qed.

    Lemma split_token_correct : forall n1 n2 tok tok1 tok2,
      isToken tok (n1+n2) ->
      split_token n1 tok = (tok1,tok2) ->
        isToken tok1 n1 /\
        isToken tok2 n2 /\
        join tok1 tok2 tok.
    Proof.
      intros.
      destruct tok as [tok Ht0].
      destruct tok1 as [tok1 Ht1].
      destruct tok2 as [tok2 Ht2].
      unfold isToken in *.
      simpl in *.
      unfold split_token in H0.
      simpl in H0.
      destruct n1; inv H0; simpl; intuition.
      constructor.
      hnf; split; simpl.
      unfold glb; simpl.
      unfold BA.glb; simpl.
      apply canonTree_eq; simpl; auto.
      unfold lub; simpl.
      unfold BA.lub; simpl.
      apply canonTree_eq; simpl; auto.
      symmetry; apply canonicalUnique; auto.
      assert (isToken' (split_tok1 n1 tok) (S n1)).
      eapply split_tok1_correct; eauto.
      omega.
      replace (mkCanon (split_tok1 n1 tok))
        with (split_tok1 n1 tok); auto.
      apply canonicalUnique; auto.
      eapply isToken_canon; eauto.
      replace n2 with ((S n1 + n2) - S n1)%nat by omega.
      eapply split_tok2_correct; auto.
      omega.
      hnf; simpl; split.
      unfold glb; unfold BA.glb; simpl.
      apply canonTree_eq; simpl.
      change (Leaf false) with (mkCanon (Leaf false)).
      apply mkCanon_test2.
      split.
      apply shareTreeOrd_trans with
        (intersect_tree (split_tok1 n1 tok) (split_tok2 n1 tok)).
      apply Eq_Ord.
      apply intersect_cong.
      apply shareTreeEq_sym.
      apply mkCanon_eq.
      apply shareTreeEq_sym.
      apply mkCanon_eq.
      apply split_tok_glb.
      apply falseLeaf_bottom.
      apply canonTree_eq; simpl.
      pattern tok at 3.
      replace tok with (mkCanon tok).
      apply mkCanon_test2.
      apply shareTreeEq_trans with
        (union_tree (split_tok1 n1 tok) (split_tok2 n1 tok)).
      apply union_cong.
      apply shareTreeEq_sym.
      apply mkCanon_eq.
      apply shareTreeEq_sym.
      apply mkCanon_eq.
      apply shareTreeEq_sym.
      apply split_tok_lub.
      symmetry.
      apply canonicalUnique; auto.
    Qed.

    Fixpoint new_fac (n:nat) {struct n} : ShareTree :=
      match n with
      | O => Node (Leaf false) (Leaf true)
      | S n' => Node (Leaf false) (new_fac n')
      end.

    Fixpoint create_tok1 (n:nat) (x:ShareTree) {struct x} : ShareTree :=
      match x with
      | Node (Leaf true)  t2 =>
          match n with
          | O    => Node (Leaf false) t2
          | S n' => Node (Leaf false) (create_tok1 n' t2)
          end
      | Node (Leaf false) t2 => Node (Leaf false) (create_tok1 n t2)
      | Leaf true => new_fac n
      | _  => x
      end.

    Fixpoint create_tok2 (n:nat) (x:ShareTree) {struct x} : ShareTree :=
      match x with
      | Node (Leaf true)  t2 =>
          match n with
          | O    => Node (Leaf true) (Leaf false)
          | S n' => Node (Leaf true) (create_tok2 n' t2)
          end
      | Node (Leaf false) t2 => Node (Leaf false) (create_tok2 n t2)
      | Leaf true => comp_tree (new_fac n)
      | _ => Leaf false
      end.

    Lemma create_tok1_correct : forall fac m n,
      isTokenFactory' fac n ->
      isTokenFactory' (create_tok1 m fac) (S m + n).
    Proof.
      induction fac; simpl; intros.
      inv H.
      induction m; simpl.
      constructor; constructor.
      constructor; auto.
      inv H; simpl.
      destruct m.
      constructor; simpl; auto.
      constructor; simpl.
      apply (IHfac2 m) in H3; auto.
      constructor; simpl.
      apply (IHfac2 m) in H3; auto.
      replace (m + S n0)%nat with (S m + n0)%nat by omega; auto.
    Qed.

    Lemma create_tok2_correct : forall fac m n,
      isTokenFactory' fac n ->
      isToken' (create_tok2 m fac) (S m).
    Proof.
      induction fac; intros.
      inv H.
      simpl.
      induction m; simpl; auto.
      constructor; constructor.
      constructor; auto.
      inv H; simpl.
      destruct m.
      constructor; constructor.
      constructor.
      apply (IHfac2 m) in H3; auto.
      constructor.
      apply (IHfac2 m) in H3; auto.
    Qed.

    Lemma create_tok_lub : forall fac n,
      shareTreeEq fac (union_tree (create_tok1 n fac) (create_tok2 n fac)).
    Proof.
      induction fac; simpl; intros; auto.
      induction n; simpl.
      destruct b; simpl; auto.
      destruct b; simpl; auto.
      apply shareTreeEq_trans with (Node (Leaf true) (Leaf true)).
      split; do 3 constructor; auto.
      apply Node_Eq; auto.
      destruct fac1; simpl.
      destruct b; simpl.
      destruct n; simpl.
      apply Node_Eq; auto.
      rewrite union_commute; simpl; auto.
      apply shareTreeEq_refl.
      apply Node_Eq; auto.
      apply Node_Eq; auto.
      apply shareTreeEq_refl.
    Qed.

    Lemma create_tok_glb : forall fac n,
      shareTreeOrd (intersect_tree (create_tok1 n fac) (create_tok2 n fac)) (Leaf false).
    Proof.
      induction fac; simpl; intros; auto.
      destruct b; simpl; auto.
      induction n; simpl; auto.
      destruct fac1; simpl; auto.
      destruct b; simpl; auto.
      destruct n; simpl; auto.
      do 2 constructor; auto.
      rewrite intersect_commute; simpl; auto.
    Qed.

    Definition create_token (n:nat) (fac:t) : t*t :=
      match n with
      | O => (fac,bot)
      | S n' =>
         (exist (fun x => canonicalTree x) (mkCanon (create_tok1 n' (proj1_sig fac))) (mkCanon_correct _),
          exist (fun x => canonicalTree x) (mkCanon (create_tok2 n' (proj1_sig fac))) (mkCanon_correct _))
      end.

    Lemma create_token_correct : forall fac fac' tok x n,
      create_token n fac = (fac',tok) ->
      isTokenFactory fac x ->
         isTokenFactory fac' (n+x) /\
        isToken tok n /\
        join fac' tok fac.
    Proof.
      intros; destruct n; simpl in H; inv H; simpl; intuition.
      hnf; constructor.
      split; [ apply glb_bot | apply lub_bot ].
      hnf; simpl.
      destruct fac as [fac H]; simpl.
      assert (isTokenFactory' (create_tok1 n fac) (S (n+x))).
      apply create_tok1_correct; auto.
      replace (mkCanon (create_tok1 n fac)) with (create_tok1 n fac); auto.
      apply canonicalUnique; auto.
      eapply isTokenFactory_canon; eauto.
      hnf.
      destruct fac as [fac H]; simpl.
      assert (isToken' (create_tok2 n fac) (S n)).
      eapply create_tok2_correct; eauto.
      replace (mkCanon (create_tok2 n fac)) with (create_tok2 n fac); auto.
      apply canonicalUnique; auto.
      eapply isToken_canon; eauto.
      split.
      apply canonTree_eq; simpl.
      change (Leaf false) with (mkCanon (Leaf false)).
      apply mkCanon_test2.
      split; auto.
      apply shareTreeOrd_trans with
        (intersect_tree (create_tok1 n (proj1_sig fac))
          (create_tok2 n (proj1_sig fac))).
      apply Eq_Ord.
      apply intersect_cong; apply shareTreeEq_sym; auto.
      apply create_tok_glb.
      apply canonTree_eq; simpl.
      destruct fac; simpl.
      pattern x0 at 3.
      replace x0 with (mkCanon x0).
      apply mkCanon_test2.
      apply shareTreeEq_trans with
        (union_tree (create_tok1 n x0) (create_tok2 n x0)).
      apply union_cong; apply shareTreeEq_sym; auto.
      apply shareTreeEq_sym.
      apply create_tok_lub.
      symmetry.
      apply canonicalUnique; auto.
    Qed.

    Local Open Scope nat_scope.

    Lemma fac_tok_classification : forall fac n,
      isTokenFactory' fac n ->
      forall tok m,
        isToken' tok m ->
        shareTreeOrd (intersect_tree fac tok) (Leaf false) ->
         ( n = m -> shareTreeEq (union_tree tok fac) (Leaf true)) /\
         ( n < m -> False ) /\
         ( n > m -> shareTreeEq (union_tree tok fac) (Leaf true) -> False).
    Proof.
      intros fac n H; induction H; simpl; intuition.
      subst m; inv H.
      simpl; auto.
      inv H.
      inv H1.
      invert_ord; discriminate.
      invert_ord.
      clear -H2 H7.
      revert n H2 H7; induction t0; simpl; intros.
      inv H2.
      inv H2.
      invert_ord; discriminate.
      invert_ord.
      eapply IHt0_2; eauto.
      subst m.
      inv H0.
      invert_ord; discriminate.
      invert_ord.
      simpl.
      destruct (IHisTokenFactory' _ _ H4 H7)
        as [? [? ?]].
      apply shareTreeEq_trans with (Node (Leaf true) (Leaf true)); auto.
      apply Node_Eq; auto.
      inv H0.
      inv H2.
      invert_ord; discriminate.
      invert_ord.
      destruct (IHisTokenFactory' _ _ H3 H8)
        as [? [? ?]].
      apply H1; auto.
      rewrite union_commute in H3.
      simpl in H3.
      destruct tok; try destruct b;
        invert_ord; try discriminate.
      inv H0.
      clear -H H11.
      revert n H H11; induction t0; simpl; intros.
      inv H.
      inv H; invert_ord; eauto.
      discriminate.
      inv H0; invert_ord; try discriminate.
      destruct (IHisTokenFactory' _ _ H7 H10)
        as [? [? ?]].
      apply H6; auto.
      split; auto.
      rewrite union_commute; auto.
      subst m.
      inv H0; invert_ord; try discriminate.
      simpl.
      destruct (IHisTokenFactory' _ _ H4 H7)
        as [? [? ?]].
      apply shareTreeEq_trans with (Node (Leaf true) (Leaf true)); auto.
      apply Node_Eq; auto.
      simpl.
      destruct(IHisTokenFactory' _ _ H4 H7)
        as [? [? ?]].
      elim H1; auto.
      destruct tok; try destruct b; invert_ord; try discriminate.
      inv H0.
      inv H0.
      inv H2.
      inv H0.
      destruct (IHisTokenFactory' _ _ H6 H8)
        as [? [? ?]].
      elim H1; omega.
      destruct (IHisTokenFactory' _ _ H6 H8)
        as [? [? ?]].
      elim H1; omega.
      rewrite union_commute in H3; simpl in H3.
      inv H0; invert_ord; try discriminate.
      destruct (IHisTokenFactory' _ _ H4 H10)
        as [? [? ?]].
      elim H7; [omega |].
      rewrite union_commute; auto.
    Qed.

    Lemma token_nonbot : forall tok n,
      isToken' tok n ->
      n > 0 ->
      shareTreeOrd tok (Leaf false) ->
      False.
    Proof.
      intros tok n H; induction H; intros;
        invert_ord; try discriminate; eauto.
      inv H.
    Qed.

    Lemma tokens_nonfull : forall tok1 n,
      isToken' tok1 n ->
      forall tok2 m,
        isToken' tok2 m ->
        shareTreeOrd (Leaf true) (union_tree tok1 tok2) ->
        False.
    Proof.
      intros tok1 n H; induction H; simpl; intros.
      induction H; invert_ord; try discriminate; auto.
      inv H0; invert_ord; eauto.
      clear -H H6.
      induction H; invert_ord; try discriminate; auto.
      inv H0; invert_ord; eauto.
      clear -H H6.
      induction H; invert_ord; try discriminate; auto.
    Qed.

    Lemma tokenFactory_nonbot : forall fac n,
      isTokenFactory' fac n ->
      shareTreeOrd fac (Leaf false) ->
      False.
    Proof.
      intros fac n H; induction H; intros;
        invert_ord; try discriminate; eauto.
    Qed.

    Lemma absorbToken : forall fac fac' tok x n,
      isTokenFactory fac' (n+x) ->
      isToken tok n ->
      join fac' tok fac ->
      isTokenFactory fac x.
    Proof.
      intros.
      destruct fac as [fac ?].
      destruct fac' as [fac' ?].
      destruct tok as [tok ?].
      unfold isToken, isTokenFactory in *.
      simpl in *.
      destruct H1; simpl in *.
      inv H1.
      inv H2.
      clear c c0 c1.
      assert (shareTreeOrd (intersect_tree fac' tok) (Leaf false)).
      rewrite <- H4.
      apply Eq_Ord; auto.
      clear H4.
      revert tok x n H H0 H1; induction fac'; simpl; intros.
      inv H.
      replace x with O by omega.
      constructor.
      inv H0.
      replace (mkCanon (Node fac'1 fac'2)) with
        (Node fac'1 fac'2); auto.
      apply canonicalUnique; auto.
      eapply isTokenFactory_canon; eauto.
      rewrite intersect_commute in H1.
      simpl in H1.
      inv H.
      invert_ord; discriminate.
      simpl.
      case_eq (mkCanon (union_tree fac'2 t0)); intros.
      destruct b.
      invert_ord.
      destruct x.
      constructor.
      destruct (fac_tok_classification fac'2 (n0+S x)) with t0 n0
        as [? [? ?]]; auto.
      elim H5; [omega|].
      apply mkCanon_test; simpl; auto.
      rewrite union_commute; auto.
      change (Leaf false) with (mkCanon (Leaf false)) in H.
      apply mkCanon_test in H.
      destruct H.
      assert (shareTreeOrd fac'2 (Leaf false)).
      apply shareTreeOrd_trans with (union_tree fac'2 t0); auto.
      apply union_upper_bound.
      elim (tokenFactory_nonbot fac'2 (n0+x)); auto.
      destruct x.
      elimtype False.
      invert_ord.
      destruct (fac_tok_classification fac'2 (n0+0)) with t0 n0
        as [? [? ?]]; auto.
      spec H0; [ omega |].
      apply mkCanon_test2 in H0.
      rewrite union_commute in H0.
      rewrite H in H0.
      discriminate.
      constructor.
      rewrite <- H.
      eapply IHfac'2; eauto.
      invert_ord; auto.
      rewrite intersect_commute in H1.
      simpl in H1.
      invert_ord.
      inv H.
      simpl.
      case_eq (mkCanon (union_tree fac'2 t0)); intros.
      destruct b.
      destruct x.
      constructor.
      destruct (fac_tok_classification fac'2 (S (n0+S x))) with t0 (S n0)
        as [? [? ?]]; auto.
      elim H5; [ omega |].
      apply mkCanon_test.
      rewrite union_commute.
      rewrite H.
      auto.
      change (Leaf false) with (mkCanon (Leaf false)) in H.
      apply mkCanon_test in H.
      destruct H.
      assert (shareTreeOrd fac'2 (Leaf false)).
      apply shareTreeOrd_trans with (union_tree fac'2 t0); auto.
      apply union_upper_bound.
      elim (tokenFactory_nonbot fac'2 (S (n0+x))); auto.
      destruct x.
      elimtype False.
      destruct (fac_tok_classification fac'2 (S (n0 + 0))) with t0 (S n0)
        as [? [? ?]]; auto.
      spec H0; [ omega |].
      apply mkCanon_test2 in H0.
      rewrite union_commute in H0; rewrite H in H0.
      discriminate.
      constructor.
      rewrite <- H.
      eapply IHfac'2; eauto.
      invert_ord; auto.
      simpl.
      destruct x.
      elimtype False.
      destruct (fac_tok_classification fac'2 (n0 + 0)) with t0 (S n0)
        as [? [? ?]]; auto.
      elim H0; omega.
      case_eq (mkCanon (union_tree fac'2 t0)); intros.
      destruct b.
      constructor.
      rewrite <- H.
      eapply IHfac'2; eauto.
      replace (S n0 + x) with (n0 + S x) by omega; auto.
      change (Leaf false) with (mkCanon (Leaf false)) in H.
      apply mkCanon_test in H.
      destruct H.
      assert (shareTreeOrd fac'2 (Leaf false)).
      apply shareTreeOrd_trans with (union_tree fac'2 t0); auto.
      apply union_upper_bound.
      elim (tokenFactory_nonbot fac'2 (n0 + S x)); auto.
      constructor.
      rewrite <- H.
      eapply IHfac'2; eauto.
      replace (S n0 + x) with (n0 + S x) by omega; auto.
    Qed.

    Lemma mergeToken : forall tok1 n1 tok2 n2 tok',
      isToken tok1 n1 ->
      isToken tok2 n2 ->
      join tok1 tok2 tok' ->
      isToken tok' (n1+n2).
    Proof.
      intros.
      destruct tok1 as [tok1 ?].
      destruct tok2 as [tok2 ?].
      destruct tok' as [tok' ?].
      unfold isToken in *; simpl in *.
      destruct H1.
      inv H1; inv H2.
      clear c c0 c1.
      change (Leaf false) with (mkCanon (Leaf false)) in H4.
      apply mkCanon_test in H4.
      destruct H4.
      clear H2.
      revert tok2 n2 H0 H1.
      induction H; simpl; intros; invert_ord.
      replace (mkCanon tok2) with tok2; auto.
      apply canonicalUnique; auto.
      eapply isToken_canon; eauto.
      induction H0; simpl; intros; invert_ord; try discriminate.
      replace (mkCanon t0) with t0.
      inv H; simpl.
      do 2 constructor.
      do 2 constructor.
      replace (n0+0) with n0 by omega; auto.
      constructor.
      constructor.
      replace (n0+0) with n0 by omega; auto.
      apply canonicalUnique; auto.
      eapply isToken_canon; eauto.
      case_eq (mkCanon (union_tree t0 t1)); intros.
      destruct b.
      change (Leaf true) with (mkCanon (Leaf true)) in H1.
      apply mkCanon_test in H1.
      destruct H1.
      elim (tokens_nonfull _ _ H _ _ H0); auto.
      change (Leaf false) with (mkCanon (Leaf false)) in H1.
      apply mkCanon_test in H1.
      destruct H1.
      assert (shareTreeOrd t1 (Leaf false)).
      apply shareTreeOrd_trans with (union_tree t0 t1); auto.
      rewrite union_commute.
      apply union_upper_bound.
      elim (token_nonbot t1 (S n0)); auto.
      omega.
      constructor.
      rewrite <- H1.
      apply IHisToken'; auto.
      inv H0.
      simpl.
      replace (mkCanon t0) with t0.
      inv H.
      do 2 constructor.
      replace (n+0) with n by omega; auto.
      do 2 constructor.
      replace (n+0) with n by omega; auto.
      apply canonicalUnique; auto.
      eapply isToken_canon; eauto.
      invert_ord.
      simpl.
      case_eq (mkCanon (union_tree t0 t1)); intros.
      destruct b.
      change (Leaf true) with (mkCanon (Leaf true)) in H0.
      apply mkCanon_test in H0.
      destruct H0.
      elim (tokens_nonfull _ _ H _ _ H2); auto.
      constructor.
      rewrite <- H0.
      replace (n + S n0) with (S n + n0) by omega.
      apply IHisToken'; auto.
      constructor.
      rewrite <- H0.
      replace (n + S n0) with (S n + n0) by omega.
      apply IHisToken'; auto.
      invert_ord.
      simpl.
      case_eq (mkCanon (union_tree t0 t1)); intros.
      destruct b.
      change (Leaf true) with (mkCanon (Leaf true)) in H0.
      apply mkCanon_test in H0.
      destruct H0.
      elim (tokens_nonfull _ _ H _ _ H2); auto.
      rewrite <- H0.
      apply IHisToken'; auto.
      constructor.
      rewrite <- H0.
      apply IHisToken'; auto.
    Qed.

    Lemma factoryOverlap : forall f1 f2 n1 n2,
      isTokenFactory f1 n1 -> isTokenFactory f2 n2 -> glb f1 f2 <> bot.
    Proof.
      repeat intro.
      destruct f1 as [f1 ?].
      destruct f2 as [f2 ?].
      inv H1; hnf in H, H0.
      simpl in *.
      change (Leaf false) with (mkCanon (Leaf false)) in H3.
      apply mkCanon_test in H3.
      destruct H3.
      clear c c0 H2.
      revert f2 n2 H0 H1.
      induction H; simpl; intros.
      induction H0; simpl; invert_ord; try discriminate; auto.
      inv H0; invert_ord; try discriminate; eauto.
      inv H0; invert_ord; try discriminate; eauto.
      clear -H H6.
      induction H; simpl; invert_ord; try discriminate; auto.
    Qed.

    Lemma fullFactory : forall x, isTokenFactory x 0 <-> x = top.
    Proof.
      intros [x ?].
      unfold isTokenFactory; simpl.
      split; intro H; inv H.
      apply canonTree_eq; auto.
      constructor.
    Qed.

    Lemma identityToken : forall x, isToken x 0 <-> x = bot.
    Proof.
      intros [x ?].
      unfold isToken; simpl.
      split; intro H; inv H.
      apply canonTree_eq; auto.
      constructor.
    Qed.

    Lemma nonidentityToken : forall x n, (n > 0)%nat -> isToken x n -> x <> bot.
    Proof.
      repeat intro.
      destruct x as [x ?].
      inv H1.
      hnf in H0; simpl in H0.
      inv H0; inv H.
    Qed.

    Lemma nonidentityFactory : forall x n, isTokenFactory x n -> x <> bot.
    Proof.
      repeat intro.
      destruct x as [x ?].
      inv H0.
      hnf in H.
      simpl in *.
      inv H.
    Qed.

    Instance EqDec_share : EqDec t := EqDec_canonTree.

(* Credits for the next part of this file:
  Specification of "unrel" operator by Andrew W. Appel and Robert Dockins
  Definition of "unrel", and all the proofs about it, by Le Xuan Bach
*)

   Program Definition tree_decompose (ct : canonTree) :(canonTree * canonTree) :=
     let (t, pf) := ct in
     match t with
     |Leaf b => (Leaf b, Leaf b)
     |Node t1 t2 => (t1 ,t2)
     end.
   Next Obligation.
    destruct pf. tauto.
   Defined.
   Next Obligation.
    destruct pf. tauto.
   Defined.

   Instance decompose_tree : decomposible t :=
     Decomposible tree_decompose.

  Fixpoint tree_heightP (t : ShareTree) : nat :=
   match t with
   | Leaf b  => 0
   | Node l r => (max (tree_heightP l) (tree_heightP r)) + 1
  end.

  Definition tree_height (t : canonTree) := tree_heightP (proj1_sig t).
  Definition tree_height_zero (t : canonTree) : {tree_height t = 0} + {tree_height t <> 0}.
    destruct t. destruct x.
    left. reflexivity.
    right. unfold tree_height. simpl. intro. rewrite plus_comm in H. inversion H.
  Defined.
  Instance tree_heightable : heightable t :=
    Heightable tree_height tree_height_zero.

  Function unrel (t1 : t) (t2 : t) {measure tree_height t1} : t :=
   match t1 with
    | exist _ (Leaf b) _ => t2
    | _ => let (ltr1, rtr1) := decompose t1 in
           let (ltr2, rtr2) := decompose t2 in
              match ltr1 with
               | exist _ (Leaf true) _ => ltr2
               | exist _ (Leaf false) _ => unrel rtr1 rtr2
               | _ => unrel ltr1 ltr2
              end
   end.
Proof.
 intros.
 clear -teq1.
 inv teq1.
 destruct c as [? [? [? ?]]].
 simpl. unfold tree_height.
 simpl.
 omega.

 intros.
 clear -teq1.
 inv teq1.
 destruct c as [? [? [? ?]]].
 unfold tree_height. simpl.
 remember (max (tree_heightP s1) (tree_heightP s2) + 1).
 assert (n1 <= max n1 (tree_heightP s0)).
   apply le_max_l.
 omega.
Set Warnings "-funind-cannot-build-inversion,-funind-cannot-define-graph".
 Defined.
Set Warnings "+funind-cannot-build-inversion,+funind-cannot-define-graph".

Lemma canonTree_Leaf : forall b, canonicalTree (Leaf b).
Proof.
  intros.
  constructor.
Qed.

Lemma mkCanon_identity : forall t, canonicalTree t -> mkCanon t = t.
Proof.
  induction t0;intros.
  compute;trivial.
  simpl.
  simpl in H.
  destruct H as [? [? [? ?]]].
  specialize ( IHt0_1 H1).
  specialize ( IHt0_2 H2).
  rewrite IHt0_1.
  rewrite IHt0_2.
  icase t0_1;icase t0_2.
  icase (bool_dec b b0).
  subst.
  elimtype False.
  icase b0;compute in  H;compute in H0; firstorder.
Qed.

Lemma identity_tree: identity (exist (fun t0 => canonicalTree t0) (Leaf false) (canonTree_Leaf _)).
Proof.
  unfold identity,join,BAF.Join_ba.
  intros.
  destruct H.
  unfold BAF.lub in H0.
  inv H0.
  destruct a.
  apply exist_ext.
  simpl.
  symmetry.
  apply mkCanon_identity.
  trivial.
Qed.

Lemma nonEmpty_nonidentity: forall x c,nonEmptyTree x -> nonidentity (exist _ x c).
Proof.
  intros.
  icase x.
  icase b.
  intro.
  specialize ( H0 (exist (fun t0 => canonicalTree t0) (Leaf false) (canonTree_Leaf _))
          (exist (fun t0 => canonicalTree t0) (Leaf true) (canonTree_Leaf _))).
  detach H0.
  inv H0.
  unfold join,BAF.Join_ba.
  split;apply exist_ext;compute;trivial.
  intro.
  unfold identity in H0.
  specialize ( H0 (exist (fun t0 => canonicalTree t0) (Leaf false) (canonTree_Leaf _))
          (exist (fun t : ShareTree => canonicalTree t) (Node x1 x2) c)).
  detach H0.
  inv H0.
  apply join_comm.
  unfold join.
  unfold BAF.Join_ba,BAF.glb,BAF.lub.
  split;apply exist_ext;simpl;trivial.
  generalize (mkCanon_identity _ c);intro.
  simpl in H0.
  trivial.
Qed.

Lemma unrel_rel: forall x sh,
    nonidentity x -> unrel x (rel x sh) = sh.
Proof.
  intro.
  destruct x.
  induction x;intros.
  rewrite unrel_equation.
  icase b.
  assert (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf true) c = top).
   unfold top.
   apply exist_ext.
   trivial.
  rewrite H0.
  apply rel_top2.

  elimtype False.
  apply H.
  assert (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf false) c =
                 core (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf false) c)).
  simpl.
  unfold BAF.bot.
  apply exist_ext;trivial.
  rewrite H0.
  apply core_identity.

  rewrite unrel_equation.
  destruct c as [? [? [? ?]]].
  assert (decompose (exist _ (Node x1 x2)
          (conj n (conj n0 (conj c c0)))) =
          (exist (fun t0 : ShareTree => canonicalTree t0) x1 c,
           exist (fun t0 : ShareTree => canonicalTree t0) x2 c0)).
    simpl;trivial.
  unfold decompose,decompose_tree in *.
  rewrite H0;clear H0.
  assert (decompose (rel (exist (fun t0 : ShareTree => canonicalTree t0) (Node x1 x2)
         (conj n (conj n0 (conj c c0)))) sh) =
         (rel (exist _ x1 c) sh, rel (exist _ x2 c0) sh)).
   generalize (rel_classification);intro.
   specialize ( X (exist (fun t0 : ShareTree => canonicalTree t0) (Node x1 x2)
          (conj n (conj n0 (conj c c0)))) sh).
   icase X.
   destruct a;subst sh.
   clear.
   simpl.
   apply injective_projections;simpl;symmetry;
   apply rel_bot1.

   destruct a.
   destruct H1.
   unfold decompose.
   remember (rel (exist (fun t0 : ShareTree => canonicalTree t0) (Node x1 x2)
            (conj n (conj n0 (conj c c0)))) sh).
   destruct t0.
   simpl in H1.
   icase x.
   destruct c1 as [? [? [? ?]]].
   inv H1.
   apply injective_projections;simpl;
   destruct sh;
   icase x;unfold rel;simpl;try apply exist_ext;trivial.
   icase b.
   apply exist_ext.
   icase x1.
   icase b.
   apply exist_ext.
   icase x2.
  unfold decompose,decompose_tree in *.
  rewrite H0;clear H0.
  icase x1.
  icase b.
   assert (exist _ (Leaf true) c = top).
   unfold top.
   apply exist_ext.
   trivial.
  rewrite H0.
  apply rel_top2.
  apply IHx2.
  apply nonEmpty_nonidentity.
  icase n0.
  apply IHx1.
  apply nonEmpty_nonidentity.
  clear - c.
  destruct c as [_ [? _]].
  trivial.
Qed.

Definition Lsh  : Share.t := fst (Share.split Share.top).
Definition Rsh  : Share.t := snd (Share.split Share.top).

Definition splice (a b: t) : t := Share.lub (rel Lsh a) (rel Rsh b).

Lemma mkCanon_Leaf : forall b , mkCanon (Leaf b) = Leaf b.
Proof.
  intros.
  icase b.
Qed.

 Lemma mkCanon_double : forall t, mkCanon (mkCanon t) = mkCanon t.
 Proof.
    intros.
    generalize (mkCanon_correct t0);intro.
    generalize (mkCanon_identity _ H);intro.
    trivial.
 Qed.

 Lemma mkCanon_split : forall t1 t2 t1' t2', mkCanon (Node t1 t2) = Node t1' t2' ->
                                            mkCanon t1 = t1' /\ mkCanon t2 = t2'.
 Proof.
    intros.
    inv H.
    icase (mkCanon t1);icase (mkCanon t2);
    try icase (bool_dec b b0);inversion H1;auto.
 Qed.

 Lemma mkCanon_Leaf_split : forall t1 t2 b, Leaf b = mkCanon (Node t1 t2) ->
                                           mkCanon t1 = Leaf b /\ mkCanon t2 = Leaf b.
  Proof.
    intros.
    inv H.
    icase (mkCanon t1);icase (mkCanon t2).
    icase (bool_dec b0 b1);inversion H1;subst.
    tauto.
  Qed.

 Lemma mkCanon_union : forall t1 t2, mkCanon (union_tree (mkCanon t1) (mkCanon t2)) =
                                      mkCanon (union_tree t1 t2).
 Proof.
    intros.
    assert (exists n, n >= max (tree_heightP t1) (tree_heightP t2)).
      exists (max (tree_heightP t1) (tree_heightP t2));omega.
    destruct H.
    revert H.
    revert t2 t1.
    induction x;intros.
      icase t1;icase t2.
      remember (tree_heightP (Node t2_1 t2_2)).
      icase n.
      inversion Heqn.
      destruct (max (tree_heightP t2_1) (tree_heightP t2_2));elimtype False ;omega.
      inversion H.
      inversion H.
      destruct (max (tree_heightP t1_1) (tree_heightP t1_2));inversion H1.
      inversion H.
      destruct (max (tree_heightP t1_1) (tree_heightP t1_2));
      destruct (max (tree_heightP t2_1) (tree_heightP t2_2));
      inversion H1.
    icase t1;icase t2.
    replace (mkCanon (Leaf b)) with (Leaf b) by apply mkCanon_Leaf.
    icase b.
    unfold union_tree.
    apply mkCanon_double.
    replace (mkCanon (Leaf b)) with (Leaf b) by apply mkCanon_Leaf.
    replace (union_tree (mkCanon (Node t1_1 t1_2)) (Leaf b))
    with (union_tree(Leaf b)(mkCanon (Node t1_1 t1_2)))
    by apply union_commute.
    replace (union_tree ( (Node t1_1 t1_2)) (Leaf b))
    with (union_tree(Leaf b)(Node t1_1 t1_2))
    by apply union_commute.
    icase b.
    unfold union_tree.
    apply mkCanon_double.

    assert (x >= max (tree_heightP t1_1) (tree_heightP t2_1)).
      simpl in H.
      replace (max (tree_heightP t1_1) (tree_heightP t1_2) + 1)
      with (S (max (tree_heightP t1_1) (tree_heightP t1_2)))
      in H by omega.
      replace (max (tree_heightP t2_1) (tree_heightP t2_2) + 1)
      with (S (max (tree_heightP t2_1) (tree_heightP t2_2)))
      in H by omega.
      generalize (succ_max_distr ((max (tree_heightP t1_1) (tree_heightP t1_2)))
      ((max (tree_heightP t2_1) (tree_heightP t2_2))));intro.
      rewrite<- H0 in H;clear H0.
      assert (x >= max (max (tree_heightP t1_1) (tree_heightP t1_2))
         (max (tree_heightP t2_1) (tree_heightP t2_2))) by omega.
      assert (max (max (tree_heightP t1_1) (tree_heightP t1_2))
       (max (tree_heightP t2_1) (tree_heightP t2_2)) >= max (tree_heightP t1_1) (tree_heightP t1_2)).
       apply le_max_l.
      assert (max (max (tree_heightP t1_1) (tree_heightP t1_2))
       (max (tree_heightP t2_1) (tree_heightP t2_2)) >= max (tree_heightP t2_1) (tree_heightP t2_2)).
       apply le_max_r.
      assert (max (tree_heightP t1_1) (tree_heightP t1_2) >= tree_heightP t1_1).
       apply le_max_l.
      assert (max (tree_heightP t2_1) (tree_heightP t2_2) >= tree_heightP t2_1).
       apply le_max_l.
      apply max_lub;omega.
    assert (x >= max (tree_heightP t1_2) (tree_heightP t2_2)).
      simpl in H.
      replace (max (tree_heightP t1_1) (tree_heightP t1_2) + 1)
      with (S (max (tree_heightP t1_1) (tree_heightP t1_2)))
      in H by omega.
      replace (max (tree_heightP t2_1) (tree_heightP t2_2) + 1)
      with (S (max (tree_heightP t2_1) (tree_heightP t2_2)))
      in H by omega.
      generalize (succ_max_distr ((max (tree_heightP t1_1) (tree_heightP t1_2)))
      ((max (tree_heightP t2_1) (tree_heightP t2_2))));intro.
      rewrite<- H1 in H;clear H1.
      assert (x >= max (max (tree_heightP t1_1) (tree_heightP t1_2))
         (max (tree_heightP t2_1) (tree_heightP t2_2))) by omega.
      assert (max (max (tree_heightP t1_1) (tree_heightP t1_2))
       (max (tree_heightP t2_1) (tree_heightP t2_2)) >= max (tree_heightP t1_1) (tree_heightP t1_2)).
       apply le_max_l.
      assert (max (max (tree_heightP t1_1) (tree_heightP t1_2))
       (max (tree_heightP t2_1) (tree_heightP t2_2)) >= max (tree_heightP t2_1) (tree_heightP t2_2)).
       apply le_max_r.
      assert (max (tree_heightP t1_1) (tree_heightP t1_2) >= tree_heightP t1_2).
       apply le_max_r.
      assert (max (tree_heightP t2_1) (tree_heightP t2_2) >= tree_heightP t2_2).
       apply le_max_r.
      apply max_lub;omega.
    generalize (IHx _ _ H0);intro.
    generalize (IHx _ _ H1);intro.
    remember (mkCanon (Node t1_1 t1_2));
    remember (mkCanon (Node t2_1 t2_2)).
    icase s;icase s0.
    generalize (mkCanon_Leaf_split _ _ _ Heqs);intro.
    generalize (mkCanon_Leaf_split _ _ _ Heqs0);intro.
    destruct H4 as [H41 H42].
    destruct H5 as [H51 H52].
    rewrite H41 in *.
    rewrite H51 in *.
    rewrite H42 in *.
    rewrite H52 in *.
    simpl.
    rewrite<-  H2.
    rewrite<- H3.
    simpl.
    icase b.
    generalize (mkCanon_Leaf b0);intro.
    rewrite H4.
    icase (bool_dec b0 b0);trivial.
    firstorder.


    generalize (mkCanon_Leaf_split _ _ _ Heqs);intro.
    symmetry in Heqs0.
    generalize (mkCanon_split _ _ _ _ Heqs0);intro.
    destruct H4 as [H41 H42].
    destruct H5 as [H51 H52].
    rewrite H41 in *.
    rewrite H42 in *.
    rewrite<- H51 in *.
    rewrite<- H52 in *.
    simpl.
    rewrite<-H2.
    rewrite<-H3.
    icase b.

    generalize (mkCanon_Leaf_split _ _ _ Heqs0);intro.
    symmetry in Heqs.
    generalize (mkCanon_split _ _ _ _ Heqs);intro.
    destruct H4 as [H41 H42].
    destruct H5 as [H51 H52].
    rewrite H41 in *.
    rewrite H42 in *.
    rewrite<- H51 in *.
    rewrite<- H52 in *.
    replace (union_tree (Node (mkCanon t1_1) (mkCanon t1_2)) (Leaf b))
    with (union_tree (Leaf b) (Node (mkCanon t1_1) (mkCanon t1_2)))
    by apply union_commute.
    replace (union_tree (mkCanon t1_1) (Leaf b))
    with (union_tree (Leaf b)(mkCanon t1_1)) in H2
    by apply union_commute.
    replace (union_tree (mkCanon t1_2) (Leaf b))
    with (union_tree (Leaf b)(mkCanon t1_2)) in H3
    by apply union_commute.
    simpl.
    rewrite<-H2.
    rewrite<-H3.
    icase b.

    symmetry in Heqs, Heqs0.
    generalize (mkCanon_split _ _ _ _ Heqs);intro.
    generalize (mkCanon_split _ _ _ _ Heqs0);intro.
    destruct H4 as [H41 H42].
    destruct H5 as [H51 H52].
    rewrite<-H41 in *.
    rewrite<- H42 in *.
    rewrite<-H51 in *.
    rewrite<-H52 in *.
    simpl.
    rewrite H2.
    rewrite H3.
    trivial.
 Qed.

 Lemma splice_rewrite: forall a b, splice a b =
      exist (fun t0 => canonicalTree t0) (mkCanon (Node (proj1_sig a) (proj1_sig b))) (mkCanon_correct _).
 Proof.
  intros.
  unfold splice.
  unfold lub,Lsh,Rsh.
  unfold split,fst,snd.
  assert (rel top leftTree = leftTree) by apply rel_top2.
  rewrite H;clear H.
  assert (rel top rightTree = rightTree) by apply rel_top2.
  rewrite H;clear H.
  assert (proj1_sig (rel leftTree a) = mkCanon (Node (proj1_sig a) (Leaf false))).
    destruct a;
    unfold leftTree.
    simpl.
    generalize (rel_classification);intro.
    specialize ( X (exist (fun t0 : ShareTree => canonicalTree t0)
        (Node (Leaf true) (Leaf false))
          (conj (or_intror (true = false) (Logic.eq_refl false))
           (conj (or_introl (false = true) (Logic.eq_refl true)) (conj I I))))
     (exist (fun t0 : ShareTree => canonicalTree t0) x c)).
    icase X.
    destruct a.
    inv H.
    rewrite H0.
    compute;trivial.
    destruct a.
    destruct H0.
    rewrite H0.
    simpl.
    generalize (mkCanon_identity _ c);intro.
    rewrite H2.
    icase x.
    icase b0.
  rewrite H.
  assert (proj1_sig (rel rightTree b) = mkCanon (Node (Leaf false) (proj1_sig b))).
    destruct b;
    unfold rightTree.
    simpl.
    generalize (rel_classification);intro.
    specialize ( X (exist (fun t0 : ShareTree => canonicalTree t0)
        (Node (Leaf false) (Leaf true))
         (conj (or_introl (true = false) (Logic.eq_refl false))
           (conj (or_intror (false = true) (Logic.eq_refl true)) (conj I I))))
     (exist (fun t0 : ShareTree => canonicalTree t0) x c)).
    icase X.
    destruct a0.
    inv H0.
    rewrite H1.
    compute;trivial.
    destruct a0.
    destruct H1.
    rewrite H1.
    simpl.
    generalize (mkCanon_identity _ c);intro.
    rewrite H3.
    icase x.
    icase b.
  rewrite H0.
  apply exist_ext.
  rewrite mkCanon_union.
  f_equal.
  rewrite union_commute.
  simpl.
  rewrite union_commute.
  simpl.
  trivial.
 Qed.

 Lemma canonTree_check: forall x y, canonicalTree x -> canonicalTree y ->
                       (exists b, x = Leaf b /\ y = Leaf b) \/ (canonicalTree (Node x y)).
 Proof.
  intros.
  icase x.
  icase y.
  icase b;icase b0.
  left;exists true;auto.
  right;compute;tauto.
  right;compute;tauto.
  left;exists false;auto.
  right.
  firstorder.
  right.
  firstorder.
 Qed.

 Lemma unrel_splice_L:
  forall a b, unrel Lsh (splice a b) = a.
 Proof.
  intros.
  generalize (splice_rewrite a b);intro.
  rewrite H;clear H.
  unfold Lsh,fst,split.
  assert (rel top leftTree = leftTree) by apply rel_top2.
  rewrite H;clear H.
  unfold leftTree.
  rewrite unrel_equation.
  assert  (decompose
          (exist (fun t0 : ShareTree => canonicalTree t0)
          (Node (Leaf true) (Leaf false))
          (conj (or_intror (true = false) (Logic.eq_refl false))
             (conj (or_introl (false = true) (Logic.eq_refl true)) (conj I I))))=
          (top,bot)).
   compute;apply injective_projections;apply exist_ext;trivial.
  unfold decompose,decompose_tree in *.
  rewrite H;clear H.
  assert  (decompose ((exist (fun t0 : ShareTree => canonicalTree t0)
          (mkCanon (Node (proj1_sig a) (proj1_sig b)))
          (mkCanon_correct (Node (proj1_sig a) (proj1_sig b))))) = (a,b)).
    destruct a,b.
    unfold proj1_sig.
    generalize (canonTree_check _ _ c c0);intro.
    icase H.
    destruct H as [? [? ?]];subst.
    icase x1;unfold decompose;apply injective_projections;
     simpl;  apply exist_ext;simpl;trivial.
    assert ((exist (fun t0 : ShareTree => canonicalTree t0) (mkCanon (Node x x0))
           (mkCanon_correct (Node x x0))) = exist (fun t0 => canonicalTree t0) (Node x x0) H).
      apply exist_ext.
      apply mkCanon_identity.
      trivial.
    rewrite H0.
    unfold decompose.
    destruct H as [? [? [? ?]]].
    apply injective_projections;simpl;apply exist_ext;trivial.
    unfold decompose,decompose_tree in *.
    rewrite H.
    unfold top;simpl.
    trivial.
 Qed.

 Lemma unrel_splice_R:
  forall a b, unrel Rsh (splice a b) = b.
 Proof.
  intros.
  generalize (splice_rewrite a b);intro.
  rewrite H;clear H.
  unfold Rsh,snd,split.
  assert (rel top rightTree = rightTree) by apply rel_top2.
  rewrite H;clear H.
  unfold rightTree.
  rewrite unrel_equation.
  assert  (decompose
          (exist (fun t0 : ShareTree => canonicalTree t0)
          (Node (Leaf false) (Leaf true))
           (conj (or_introl (true = false) (Logic.eq_refl false))
             (conj (or_intror (false = true) (Logic.eq_refl true)) (conj I I)))) =
          (bot,top)).
   compute;apply injective_projections;apply exist_ext;trivial.
  unfold decompose,decompose_tree in *.
  rewrite H;clear H.
  assert  (decompose ((exist (fun t0 : ShareTree => canonicalTree t0)
          (mkCanon (Node (proj1_sig a) (proj1_sig b)))
          (mkCanon_correct (Node (proj1_sig a) (proj1_sig b))))) = (a,b)).
    destruct a,b.
    unfold proj1_sig.
    generalize (canonTree_check _ _ c c0);intro.
    icase H.
    destruct H as [? [? ?]];subst.
    icase x1;unfold decompose;apply injective_projections;
    simpl; apply exist_ext;simpl;trivial.
    assert ((exist (fun t0 : ShareTree => canonicalTree t0) (mkCanon (Node x x0))
           (mkCanon_correct (Node x x0))) = exist (fun t0 => canonicalTree t0) (Node x x0) H).
      apply exist_ext.
      apply mkCanon_identity.
      trivial.
    rewrite H0.
    unfold decompose.
    destruct H as [? [? [? ?]]].
    apply injective_projections;simpl;apply exist_ext;trivial.
  unfold decompose,decompose_tree in *.
  rewrite H.
  unfold bot;simpl.
  reflexivity.
 Qed.

Lemma contains_Lsh_e:
   forall sh,
       join_sub Lsh sh -> unrel Lsh sh = top.
Proof.
 intros.
 destruct H.
 destruct H.
 subst.
 unfold Lsh,fst in *.
 simpl in *.
 assert (rel top leftTree = leftTree) by apply rel_top2.
 rewrite H0 in *;clear H0.
 unfold leftTree in *.
 rewrite unrel_equation.
 assert (CT: canonicalTree (Node (Leaf true) (Leaf false))).
  repeat split. right; reflexivity. left; reflexivity.
 assert (@decompose t _
        (exist (fun t0 : ShareTree => canonicalTree t0)
        (Node (Leaf true) (Leaf false))
          (conj (or_intror eq_refl) (conj (or_introl eq_refl) (conj I I))))
         = (top,bot)).
   compute;apply injective_projections;apply exist_ext;trivial.
 simpl nonFullTree in H0; simpl nonEmptyTree in H0.
 rewrite H0. clear H0.
 destruct x.
 icase x.
 icase b.
 simpl.
 destruct (mkCanon_correct (Node (Leaf true) (Leaf false))) as [? [? [? ?]]].
 unfold top.  apply exist_ext;trivial.
 destruct c as [? [? [? ?]]].
 assert (decompose
       (BAF.lub
          (exist (fun t0 : ShareTree => canonicalTree t0)
             (Node (Leaf true) (Leaf false))
             (conj (or_intror eq_refl) (conj (or_introl eq_refl) (conj I I))))
          (exist (fun t0 : ShareTree => canonicalTree t0) (Node x1 x2)
             (conj n (conj n0 (conj c c0))))) =
        (top, exist (fun t0 : ShareTree => canonicalTree t0) x2 c0)).
   unfold BAF.lub.
   unfold proj1_sig.
   assert (union_tree (Node (Leaf true) (Leaf false)) (Node x1 x2) = Node (Leaf true) x2).
     unfold union_tree;trivial.
   rewrite H0;clear H0.
   icase x2.
   icase b;
   simpl.
   apply injective_projections;apply exist_ext;trivial.
   destruct (mkCanon_correct (Node (Leaf true) (Leaf false))) as [? [? [? ?]]].
   apply injective_projections;apply exist_ext;trivial.
   assert (canonicalTree (Node (Leaf true) (Node x2_1 x2_2) )).
    destruct c0 as [? [? [? ?]]];
    firstorder.
   assert (exist (fun t0 : ShareTree => canonicalTree t0)
     (mkCanon (Node (Leaf true) (Node x2_1 x2_2)))
     (mkCanon_correct (Node (Leaf true) (Node x2_1 x2_2)))=
          (exist (fun t0 : ShareTree => canonicalTree t0) (Node (Leaf true) (Node x2_1 x2_2)) H0)).
    apply exist_ext.
    simpl.
    destruct c0 as [? [? [? ?]]].
    generalize (mkCanon_identity x2_1 c0);intro.
    generalize (mkCanon_identity x2_2 c1);intro.
    rewrite H1;rewrite H2.
    icase x2_1;icase x2_2.
    icase b;icase b0;
    simpl;
    elimtype False;firstorder.
  rewrite H1.
  simpl.
  destruct H0 as [? [? [? ?]]].
  apply injective_projections;apply exist_ext;trivial.
  change BAF.lub with lub in H0.
  simpl nonFullTree in H0|-*; simpl nonEmptyTree in H0|-*.
 rewrite H0.
 unfold bot.
 rewrite unrel_equation.
 unfold top.
 trivial.
Qed.

 Lemma contains_Rsh_e: forall sh,
       join_sub Rsh sh ->
       unrel Rsh sh = top.
 Proof.
  intros.
  destruct H.
  destruct H.
  subst.
  unfold Rsh,snd in *.
  simpl in *.
  assert (rel top rightTree = rightTree) by apply rel_top2.
  rewrite H0 in *;clear H0.
  unfold rightTree in *.
  rewrite unrel_equation.
  assert (decompose
        (exist (fun t0 : ShareTree => canonicalTree t0)
        (Node (Leaf false) (Leaf true))
         (conj (or_introl (true = false) (Logic.eq_refl false))
            (conj (or_intror (false = true) (Logic.eq_refl true)) (conj I I))))
         = (bot,top)).
   compute;apply injective_projections;apply exist_ext;trivial.
  unfold decompose,decompose_tree in *.
  rewrite H0;clear H0.
  destruct x.
  icase x.
  icase b.
  simpl.
  destruct (mkCanon_correct (Node (Leaf false) (Leaf true))) as [? [? [? ?]]].
  rewrite unrel_equation.
  unfold top.
  apply exist_ext;trivial.
  destruct c as [? [? [? ?]]].
  assert (decompose
        (BAF.lub
        (exist (fun t0 : ShareTree => canonicalTree t0)
        (Node (Leaf false) (Leaf true))
       (conj (or_introl (true = false) (Logic.eq_refl false))
                (conj (or_intror (false = true) (Logic.eq_refl true))
                   (conj I I))))
        (exist (fun t0 : ShareTree => canonicalTree t0) (Node x1 x2)
        (conj n (conj n0 (conj c c0))))) =
        (exist (fun t0 : ShareTree => canonicalTree t0) x1 c, top)).
   unfold BAF.lub.
   unfold proj1_sig.
   assert (union_tree (Node (Leaf false) (Leaf true)) (Node x1 x2) = Node x1 (Leaf true)).
     unfold union_tree;trivial.
   rewrite H0;clear H0.
   icase x1.
   icase b;
   simpl.
   apply injective_projections;apply exist_ext;trivial.
   destruct (mkCanon_correct (Node (Leaf false) (Leaf true))) as [? [? [? ?]]].
   apply injective_projections;apply exist_ext;trivial.
   assert (canonicalTree (Node (Node x1_1 x1_2) (Leaf true))).
    destruct c as [? [? [? ?]]];
    firstorder.
   assert (exist (fun t0 : ShareTree => canonicalTree t0)
          (mkCanon (Node (Node x1_1 x1_2) (Leaf true)))
          (mkCanon_correct (Node (Node x1_1 x1_2) (Leaf true))) =
          (exist (fun t0 : ShareTree => canonicalTree t0) (Node (Node x1_1 x1_2) (Leaf true)) H0)).
    apply exist_ext.
    simpl.
    destruct c as [? [? [? ?]]].
    generalize (mkCanon_identity x1_1 c);intro.
    generalize (mkCanon_identity x1_2 c1);intro.
    rewrite H1;rewrite H2.
    icase x1_1;icase x1_2.
    icase b;icase b0;
    simpl;
    elimtype False;firstorder.
  rewrite H1.
  simpl.
  destruct H0 as [? [? [? ?]]].
  apply injective_projections;apply exist_ext;trivial.
 unfold decompose,decompose_tree in *.
 rewrite H0.
 unfold bot.
 rewrite unrel_equation.
 unfold top.
 trivial.
Qed.


(*START HERE*)
  Fixpoint fullTreeP (t : ShareTree) (d  : nat): Prop :=
   match t with
    | Leaf b => d = 0
    | Node l r => (d > 0) /\ (fullTreeP l (d - 1)) /\ (fullTreeP r (d - 1))
   end.

  Definition fullTree (t : ShareTree) : Prop :=
   fullTreeP t (tree_heightP t).

  Fixpoint mkFull (d : nat)  (t : ShareTree) : option ShareTree :=
   match d with
    |0 => match t with
          |Leaf b => Some (Leaf b)
          |Node l r => None
          end
    |S n => match t with
            |Leaf b => match (mkFull n (Leaf b)) with
                       | Some t => Some (Node t t)
                       |_ => None
                       end
            |Node l r => match (mkFull n l, mkFull n r) with
                         | (Some t1, Some t2) => Some (Node t1 t2)
                         |_ => None
                         end
             end
   end.

  Fixpoint tree_round_leftP (n : nat) (t : ShareTree) : option ShareTree :=
    match n with
    | 0 => None
    | 1 => match t with
           | Node (Leaf b1) (Leaf b2) => Some (Leaf b1)
           |_=> None
           end
    | S n' => match t with
              | Leaf b => Some (Leaf b)
              | Node t1 t2 => match (tree_round_leftP n' t1, tree_round_leftP n' t2) with
                              | (Some t1', Some t2') => Some (Node t1' t2')
                              | _ => None
                              end
              end
    end.

   Definition tree_round_left (n : nat) (t : canonTree) : option canonTree:=
    match mkFull n (proj1_sig t) with
    | Some t' => match tree_round_leftP n t' with
                  | Some t'' => Some (exist (fun t => canonicalTree t) (mkCanon t'') (mkCanon_correct _))
                  | None => None
                  end
     | None => None
     end.
   Instance  roundableL_tree : roundableLeft t :=
    RoundableLeft tree_round_left.

   Fixpoint tree_round_rightP (n : nat) (t : ShareTree) : option ShareTree :=
    match n with
    | 0 => None
    | 1 => match t with
           | Node (Leaf b1) (Leaf b2) => Some (Leaf b2)
           |_=> None
           end
    | S n' => match t with
              | Leaf b => Some (Leaf b)
              | Node t1 t2 => match (tree_round_rightP n' t1, tree_round_rightP n' t2) with
                              | (Some t1', Some t2') => Some (Node t1' t2')
                              | _ => None
                              end
              end
    end.

   Definition tree_round_right (n : nat) (t : canonTree) : option canonTree:=
    match mkFull n (proj1_sig t) with
    | Some t' => match tree_round_rightP n t' with
                  | Some t'' => Some (exist (fun t => canonicalTree t) (mkCanon t'') (mkCanon_correct _))
                  | None => None
                  end
     | None => None
     end.
  Instance  roundableR_tree : roundableRight t :=
   RoundableRight tree_round_right.

   Fixpoint tree_avgP (t1 t2 : ShareTree) : option ShareTree :=
    match (t1,t2) with
    |(Leaf b1, Leaf b2) => Some (Node (Leaf b1) (Leaf b2))
    |(Node t11 t12, Node t21 t22) => match (tree_avgP t11 t21, tree_avgP t12 t22) with
                                     |(Some t1', Some t2') => Some (Node t1' t2')
                                     |_ => None
                                     end
    |_ => None
    end.

   Definition tree_avg (n : nat) (t1 t2 : canonTree) : option canonTree :=
    match n with
    |0 => None
    |S n' => match (mkFull n' (proj1_sig t1), mkFull n' (proj1_sig t2)) with
             |(Some t1', Some t2') => match (tree_avgP t1' t2') with
                                      |Some t' => Some (exist (fun t => canonicalTree t) (mkCanon t') (mkCanon_correct _))
                                      |None => None
                                      end
             |_ => None
             end
    end.
   Instance avgable_tree : avgable t :=
     Avgable tree_avg.

  Lemma compose_canon1 : forall b1 b2,b1 <> b2 -> canonicalTree (Leaf b1) ->
                                                  canonicalTree (Leaf b2) ->
                                                  canonicalTree (Node (Leaf b1) (Leaf b2)).
  Proof.
   intros;
   try icase b1;try icase b2;compute in *;tauto.
  Qed.

  Lemma compose_canon2 : forall b t1 t2, canonicalTree (Leaf b) ->
                                         canonicalTree (Node t1 t2)->
                                         canonicalTree (Node (Leaf b) (Node t1 t2)).
  Proof.
   intros.
   simpl;
   firstorder.
  Qed.

  Lemma compose_canon3 : forall t1 t2 b, canonicalTree (Node t1 t2)->
                                         canonicalTree (Leaf b) ->
                                         canonicalTree (Node (Node t1 t2) (Leaf b) ).
  Proof.
   intros;
   simpl;
   firstorder.
  Qed.

  Lemma compose_canon4 : forall t1 t2 t3 t4, canonicalTree (Node t1 t2) ->
                                             canonicalTree (Node t3 t4) ->
                                             canonicalTree (Node (Node t1 t2) (Node t3 t4)).
  Proof.
   intros;
   simpl;
   firstorder.
  Qed.

   Definition recompose (tt : (canonTree*canonTree)): canonTree :=
   let (t1, t2) := tt in
   let (x1, c1) := t1 in
   let (x2, c2) := t2 in
   match x1 as s return (canonicalTree s -> canonTree) with
   | Leaf b1 =>
       fun c3 : canonicalTree (Leaf b1) =>
       match x2 as s return (canonicalTree s -> canonTree) with
       | Leaf b2 =>
           fun c4 : canonicalTree (Leaf b2) =>
           match bool_dec b1 b2 with
           | left e =>
               let H :=
                 eq_rec b1
                   (fun b3 : bool => canonicalTree (Leaf b3) -> canonTree)
                   (fun _ : canonicalTree (Leaf b1) =>
                    exist (fun t : ShareTree => canonicalTree t) (Leaf b1) c3)
                   b2 e in
               H c4
           | right n =>
               exist (fun t : ShareTree => canonicalTree t)
                 (Node (Leaf b1) (Leaf b2)) (compose_canon1 b1 b2 n c3 c4)
           end
       | Node x21 x22 =>
           fun c4 : canonicalTree (Node x21 x22) =>
           exist (fun t : ShareTree => canonicalTree t)
                (Node (Leaf b1) (Node x21 x22)) (compose_canon2 b1 x21 x22 c3 c4)
       end c2
   | Node x11 x12 =>
       fun c3 : canonicalTree (Node x11 x12) =>
       match x2 as s return (canonicalTree s -> canonTree) with
       | Leaf b2 =>
           fun c4 : canonicalTree (Leaf b2) =>
           exist (fun t : ShareTree => canonicalTree t)
             (Node (Node x11 x12) (Leaf b2)) (compose_canon3 x11 x12 b2 c3 c4)
       | Node x21 x22 =>
           fun c4 : canonicalTree (Node x21 x22) =>
           exist (fun t : ShareTree => canonicalTree t)
             (Node (Node x11 x12) (Node x21 x22))
             (compose_canon4 x11 x12 x21 x22 c3 c4)
       end c2
   end c1.

(*End Definition*)


  Lemma tree_height_diff : forall t1 t2, height t1 <> height t2 -> t1 <> t2.
  Proof.
    intros.
    intro H1;apply H.
    rewrite H1;trivial.
  Qed.

  Lemma fullTreeP_subL : forall n t1 t2, fullTreeP (Node t1 t2) (S n) -> fullTreeP t1 n.
   Proof.
    intros.
    simpl in H.
    destruct H as [_ [? _]].
    replace (n-0) with n in * by omega.
    trivial.
   Qed.

  Lemma fullTreeP_subR : forall n t1 t2, fullTreeP (Node t1 t2) (S n) -> fullTreeP t2 n.
   Proof.
    intros.
    simpl in H.
    destruct H as [_ [_ ?]].
    replace (n-0) with n in * by omega.
    trivial.
   Qed.

  Lemma fullTreeP_height : forall n t, fullTreeP t n -> tree_heightP t = n.
   Proof.
    induction n;intros.
    destruct t0;inversion H.
    simpl;trivial.
    inversion H0.
    destruct t0.
    inversion H.
    simpl in H.
    destruct H as [_ [? ?]].
    replace (n-0) with n in * by omega.
    simpl.
    generalize (IHn t0_1 H);intro.
    generalize (IHn t0_2 H0);intro.
    rewrite H1.
    rewrite H2.
    rewrite max_l; omega.
  Qed.

  Lemma fullTreeP_combine : forall t1 t2 n, fullTreeP t1 n -> fullTreeP t2 n ->
                                          fullTreeP (Node t1 t2) (S n).
  Proof.
   intros.
   simpl.
   split.
   omega.
   split;
   replace (n-0) with n in * by omega;
   trivial.
  Qed.

  Lemma fullTree_double : forall t, fullTree t -> fullTree (Node t t).
  Proof.
   intros.
   unfold fullTree in *.
   remember (tree_heightP (Node t0 t0)).
   icase n.
   simpl in  Heqn.
   rewrite max_l in Heqn; trivial.
   destruct (tree_heightP t0);
   inversion Heqn.
   apply fullTreeP_combine;
   simpl in Heqn;
   rewrite max_l in Heqn;trivial;
   assert (n = tree_heightP t0) by omega;
   rewrite H0;
   trivial.
  Qed.

  Lemma fullTree_sub : forall t1 t2, fullTree (Node t1 t2) <->
                                      (fullTree t1 /\ fullTree t2 /\ tree_heightP t1 = tree_heightP t2).
  Proof.
    intros.
    split.
    intros.
    unfold fullTree in *.
    remember (tree_heightP (Node t1 t2)).
    icase n.
    simpl in Heqn.
    destruct ( max (tree_heightP t1) (tree_heightP t2));
    inversion Heqn.
    generalize (fullTreeP_subL n t1 t2 H);intro.
    generalize (fullTreeP_subR n t1 t2 H);intro.
    assert (tree_heightP t1 = n /\ tree_heightP t2 = n).
    generalize (fullTreeP_height n t1 H0);intro.
    generalize (fullTreeP_height n t2 H1);intro.
    tauto.
    destruct H2.
    rewrite H2.
    rewrite H3.
    tauto.
    intro.
    destruct H as [? [? ?]].
    unfold fullTree in *.
    simpl in *.
    rewrite H1 in *.
    split.
    destruct (max (tree_heightP t2) (tree_heightP t2));omega.
    rewrite max_l;trivial.
    replace (tree_heightP t2 + 1 - 1) with (tree_heightP t2) in * by omega.
    tauto.
  Qed.

  Lemma mkFull_height : forall n t t', mkFull n t = Some t' -> tree_heightP t' = n.
  Proof.
    induction n;intros.
    simpl in H.
    destruct t0;inversion H.
    trivial.
    destruct t0;inversion H.
    remember (mkFull n (Leaf b)).
    destruct o.
    symmetry in Heqo.
    specialize ( IHn (Leaf b) s Heqo).
    inversion H1.
    simpl.
    rewrite max_l;trivial.
    omega.
    inversion H1.
    remember (mkFull n t0_1).
    destruct o.
    remember (mkFull n t0_2).
    destruct o.
    symmetry in Heqo.
    symmetry in Heqo0.
    generalize (IHn t0_1 s Heqo);intro.
    generalize (IHn t0_2 s0 Heqo0);intro.
    inversion H1.
    simpl.
    rewrite H0.
    rewrite H2.
    rewrite max_l;trivial.
    omega.
    inversion H1.
    inversion H1.
  Qed.

  Lemma mkFull_correct : forall n t t', mkFull n t = Some t' -> fullTree t'.
  Proof.
   induction n;intros.
   destruct t0;inversion H.
   compute.
   trivial.
   destruct t0.
   simpl in H.
   remember (mkFull n (Leaf b)).
   destruct o.
   symmetry in Heqo.
   specialize ( IHn (Leaf b) s Heqo).
   inversion H.
   apply fullTree_double;trivial.
   inversion H.
   simpl in H.
   remember (mkFull n t0_1).
   destruct o.
   symmetry in Heqo.
   remember (mkFull n t0_2).
   destruct o.
   symmetry in Heqo0.
   generalize (IHn t0_1 s Heqo);intro.
   generalize (IHn t0_2 s0 Heqo0);intro.
   inversion H.
   generalize (fullTree_sub s s0);intro.
   destruct H2.
   apply H4.
   generalize (mkFull_height n t0_1 s Heqo);intro.
   generalize (mkFull_height n t0_2 s0 Heqo0);intro.
   split;trivial.
   split;trivial.
   congruence.
   inversion H.
   inversion H.
  Qed.

  Lemma mkFull_mkCanon : forall n t t', mkFull n t = Some t' ->
                                        mkCanon t = mkCanon t'.
  Proof.
   induction n;intros;
   icase t0;icase t';
   inv H;trivial.

   icase (mkFull n (Leaf b)).
   remember (mkFull n (Leaf b)).
   icase o.
   symmetry in Heqo.
   inv H1.
   generalize (IHn _ _ Heqo);intro.
   simpl.
   rewrite<- H.
   simpl.
   icase b.
   icase (mkFull n t0_1);
   icase (mkFull n t0_2).
   remember (mkFull n t0_1);
   remember (mkFull n t0_2).
   icase o;icase o0.
   symmetry in Heqo, Heqo0.
   inv H1.
   generalize (IHn _ _ Heqo);intro H1.
   generalize (IHn _ _ Heqo0);intro H2.
   simpl.
   rewrite H1,H2.
   trivial.
  Qed.

  Lemma mkFull_split : forall n t1 t2 t1' t2',
                       mkFull (S n) (Node t1 t2) = Some (Node t1' t2') <->
                       (mkFull n t1 = Some t1' /\ mkFull n t2 = Some t2').
  Proof.
    intros.
    simpl.
    split;
    remember (mkFull n t1);
    remember (mkFull n t2);
    icase o;icase o0;intros.
    inv H;tauto.
    destruct H as [H1 H2];inv H1; inv H2;trivial.
    destruct H as [H1 H2];inv H1;inv H2.
    destruct H as [H1 H2];inv H1;inv H2.
    destruct H as [H1 H2];inv H1;inv H2.
  Qed.

  Lemma mkFull_mkCanon_simpl : forall n t1 t2, mkFull (S n) (mkCanon (Node t1 t2)) =
                                       mkFull (S n) (Node (mkCanon t1) (mkCanon t2)).
  Proof.
    intros.
    simpl.
    icase (mkCanon t1);icase (mkCanon t2).
    icase (bool_dec b b0);subst;trivial.
    icase (mkFull n (Leaf b0)).
  Qed.

  Lemma mkFull_None : forall n t, n < tree_heightP t -> mkFull n t = None.
  Proof.
   induction n;intros;
   icase t0.
   inversion H.
   inversion H.
   simpl in H.
   assert (n < max (tree_heightP t0_1) (tree_heightP t0_2)) by omega.
   generalize (Nat.max_lt_iff);intro.
   specialize ( H1 (tree_heightP t0_1) (tree_heightP t0_2) n).
   destruct H1 as [? _].
   specialize ( H1 H0).
   destruct H1.
   specialize ( IHn t0_1 H1).
   simpl.
   rewrite IHn;
   trivial.
   specialize ( IHn t0_2 H1).
   simpl;rewrite IHn.
   icase (mkFull n t0_1);trivial.
  Qed.

  Lemma mkFull_Some : forall n t, n >= tree_heightP t -> exists t', mkFull n t = Some t'.
  Proof.
    induction n;intros;
    icase t0.
    exists (Leaf b).
    compute;trivial.
    inversion H.
    elimtype False;omega.
    assert (n >= tree_heightP (Leaf b)).
      compute;omega.
    specialize ( IHn (Leaf b) H0).
    destruct IHn.
    simpl.
    rewrite H1.
    exists (Node x x).
    trivial.
    simpl in H.
    assert (n >= max (tree_heightP t0_1) (tree_heightP t0_2)) by omega.
    generalize (le_max_l (tree_heightP t0_1) (tree_heightP t0_2));intro.
    generalize (le_max_r (tree_heightP t0_1) (tree_heightP t0_2));intro.
    assert (n >= tree_heightP t0_1) by omega.
    assert (n >= tree_heightP t0_2) by omega.
    generalize (IHn _ H3);intro.
    generalize (IHn _ H4);intro.
    destruct H5.
    destruct H6.
    simpl.
    rewrite H5.
    rewrite H6.
    exists (Node x x0);trivial.
  Qed.

  Lemma mkCanon_eq_split : forall t1 t2 t1' t2', mkCanon (Node t1 t2) = mkCanon (Node t1' t2')
                                                -> mkCanon t1 = mkCanon t1' /\ mkCanon t2 = mkCanon t2'.
  Proof.
    intros.
    simpl in H.
    icase (mkCanon t1);icase (mkCanon t2);
    icase (mkCanon t1');icase (mkCanon t2');
    try icase (bool_dec b b0);try icase (bool_dec b1 b2);inversion H;try subst;auto;
    try icase (bool_dec b0 b1).
  Qed.

  Lemma mkCanon_simpl : forall t1 t2, mkCanon (Node (mkCanon t1) (mkCanon t2)) = mkCanon (Node t1 t2).
  Proof.
    intros.
    simpl.
    generalize (mkCanon_double t1);intro.
    rewrite H.
    generalize (mkCanon_double t2);intro.
    rewrite H0.
    icase (mkCanon t1);icase (mkCanon t2).
  Qed.

  Lemma mkCanon_height : forall t t', mkCanon t = t' ->  tree_heightP t' <= tree_heightP t.
  Proof.
   induction t0;intros.
   generalize (mkCanon_Leaf b);intro.
   rewrite H in H0.
   rewrite H0.
   omega.

   icase t'.
   symmetry in H.
   generalize (mkCanon_Leaf_split _ _ _ H);intro.
   simpl.
   omega.
   generalize (mkCanon_split _ _ _ _ H);intro.
   destruct H0 as [? ?].
   specialize ( IHt0_1 t'1 H0).
   specialize (IHt0_2 t'2 H1).
   simpl.
   assert (max (tree_heightP t'1) (tree_heightP t'2) <= max (tree_heightP t0_1) (tree_heightP t0_2) ).
    generalize (le_max_l (tree_heightP t0_1) (tree_heightP t0_2));intro.
    generalize (le_max_r (tree_heightP t0_1) (tree_heightP t0_2));intro.
    apply max_lub;omega.
   omega.
  Qed.

  Lemma mkCanon_rewrite : forall t, exists t1, exists t2, mkCanon t = mkCanon (Node t1 t2).
  Proof.
   intros.
   icase t0.
   exists (Leaf b);
   exists (Leaf b).
   icase b.

   exists t0_1;exists t0_2;trivial.
  Qed.

  Lemma canonTree_rewrite1 : forall (t' : canonTree), exists t1, exists t2,
                            t' = (exist (fun t => canonicalTree t)
                           (mkCanon (Node t1 t2))
                           (mkCanon_correct _)).
  Proof.
   intros.
   destruct t' as [x c].
   icase x.
   exists (Leaf b);exists (Leaf b).
   apply exist_ext.
   icase b.
   exists x1;
   exists x2.
   apply exist_ext.
   symmetry.
   apply mkCanon_identity.
   trivial.
   Qed.

  Lemma canonTree_rewrite2: forall (t : canonTree), t =
        exist (fun t => canonicalTree t) (mkCanon (proj1_sig t)) (mkCanon_correct _).
  Proof.
   intros.
   destruct t0 as [x c].
   apply exist_ext;simpl;trivial.
   generalize (mkCanon_identity x c);intro.
   congruence.
  Qed.

  Lemma mkCanon_height_split : forall n t11 t12 t21 t22,
        max (tree_heightP (mkCanon (Node t11 t12)))
            (tree_heightP (mkCanon (Node t21 t22))) < S (S n) ->
        max (tree_heightP (mkCanon t11))
            (tree_heightP (mkCanon t21)) < S n /\
        max (tree_heightP (mkCanon t12))
            (tree_heightP (mkCanon t22)) < S n.
  Proof.
   intros.
   remember (mkCanon (Node t11 t12));
   remember (mkCanon (Node t21 t22)).
   icase s;icase s0.
   generalize (mkCanon_Leaf_split _ _ _ Heqs);intro H1.
   generalize (mkCanon_Leaf_split _ _ _ Heqs0);intro H2.
   destruct H1 as [H11 H12];
   destruct H2 as [H21 H22].
   rewrite H11,H12,H21,H22.
   simpl.
   omega.

   symmetry in Heqs0.
   generalize (mkCanon_Leaf_split _ _ _ Heqs);intro H1.
   generalize (mkCanon_split _ _ _ _ Heqs0);intro H2.
   destruct H1 as [H11 H12].
   destruct H2 as [H21 H22].
   rewrite H11,H12,H21,H22.
   simpl in H.
   assert (max (tree_heightP s0_1) (tree_heightP s0_2) < S n) by omega.
   simpl.
   generalize (le_max_l (tree_heightP s0_1) (tree_heightP s0_2));intro H31.
   generalize (le_max_r (tree_heightP s0_1) (tree_heightP s0_2));intro H32.
   omega.

   symmetry in Heqs.
   generalize (mkCanon_split _ _ _ _ Heqs);intro H1.
   generalize (mkCanon_Leaf_split _ _ _ Heqs0);intro H2.
   destruct H1 as [H11 H12].
   destruct H2 as [H21 H22].
   rewrite H11,H12,H21,H22.
   replace (max (tree_heightP (Node s1 s2)) (tree_heightP (Leaf b)))
   with (max (tree_heightP (Leaf b)) (tree_heightP (Node s1 s2)) ) in H
   by apply max_comm.
   replace (max (tree_heightP s1) (tree_heightP (Leaf b)))
   with (max (tree_heightP (Leaf b)) (tree_heightP s1))
   by apply max_comm.
   replace (max (tree_heightP s2) (tree_heightP (Leaf b)))
   with (max (tree_heightP (Leaf b)) (tree_heightP s2))
   by apply max_comm.
   simpl in H.
   simpl.
   assert (max (tree_heightP s1) (tree_heightP s2) < S n) by omega.
   simpl.
   generalize (le_max_l (tree_heightP s1) (tree_heightP s2));intro H31.
   generalize (le_max_r (tree_heightP s1) (tree_heightP s2));intro H32.
   omega.

   symmetry in Heqs,Heqs0.
   generalize (mkCanon_split _ _ _ _ Heqs);intro H1.
   generalize (mkCanon_split _ _ _ _ Heqs0);intro H2.
   destruct H1 as [H11 H12].
   destruct H2 as [H21 H22].
   rewrite H11,H12,H21,H22.
   simpl in H.
   generalize (plus_max_distr_r (max (tree_heightP s1) (tree_heightP s2))
                                (max (tree_heightP s0_1) (tree_heightP s0_2))
                                 1);
   intro H3.
   rewrite H3 in H.
   assert (max (max (tree_heightP s1) (tree_heightP s2))
               (max (tree_heightP s0_1) (tree_heightP s0_2)) < S n) by omega.
   generalize (le_max_r (max (tree_heightP s1) (tree_heightP s2))
                        (max (tree_heightP s0_1) (tree_heightP s0_2)));intro H4.
   generalize (le_max_l (max (tree_heightP s1) (tree_heightP s2))
                        (max (tree_heightP s0_1) (tree_heightP s0_2)));intro H5.
   generalize (le_max_r (tree_heightP s1) (tree_heightP s2));intro H6.
   generalize (le_max_l (tree_heightP s1) (tree_heightP s2));intro H7.
   generalize (le_max_r (tree_heightP s0_1) (tree_heightP s0_2));intro H8.
   generalize (le_max_l (tree_heightP s0_1) (tree_heightP s0_2));intro H9.
   assert (tree_heightP s1 <= n) by omega.
   assert (tree_heightP s2 <= n) by omega.
   assert (tree_heightP s0_1 <= n) by omega.
   assert (tree_heightP s0_2 <= n) by omega.
   generalize (max_lub _ _ _ H1 H10);intro H14.
   generalize (max_lub _ _ _ H2 H13);intro H15.
   omega.
  Qed.

  Lemma mkCanon_diff : forall t11 t12 t21 t22,
                       mkCanon (Node t11 t12) <> mkCanon (Node t21 t22) ->
                       mkCanon t11 <> mkCanon t21 \/
                       mkCanon t12 <> mkCanon t22.
  Proof.
   intros.
   generalize (shareTree_dec_eq (mkCanon t11) (mkCanon t21));intro H1.
   destruct H1.
   right.
   intro H1;apply H.
   simpl.
   rewrite e,H1;trivial.

   left;trivial.
  Qed.

  Lemma canonTree_proof_irr: forall t1 t2 c1 c2, t1 = t2 -> exist (fun t => canonicalTree t) t1 c1 =
                                                            exist (fun t => canonicalTree t) t2 c2.
  Proof.
   intros.
   apply exist_ext;trivial.
  Qed.

  Lemma canonTree_combine : forall t1 t2, canonicalTree t1 ->
                                          canonicalTree t2 ->
                                          max (tree_heightP t1) (tree_heightP t2) > 0 ->
                                          canonicalTree (Node t1 t2).
  Proof.
    intros.
    generalize (max_dec (tree_heightP t1) (tree_heightP t2));intro H2.
    destruct H2.
    rewrite e in H1.
    icase t1.
    inv H1.
    simpl in *.
    tauto.
    rewrite e in H1.
    icase t2.
    inv H1.
    simpl in *.
    tauto.
  Qed.

  Lemma mkCanon_intersect : forall t1 t2, mkCanon (intersect_tree (mkCanon t1) (mkCanon t2)) =
                                          mkCanon (intersect_tree t1 t2).
  Proof.
    intros.
    assert (exists n, n >= max (tree_heightP t1) (tree_heightP t2)).
      exists (max (tree_heightP t1) (tree_heightP t2));omega.
    destruct H.
    revert H.
    revert t2 t1.
    induction x;intros.
      icase t1;icase t2.
      remember (tree_heightP (Node t2_1 t2_2)).
      icase n.
      inversion Heqn.
      destruct (max (tree_heightP t2_1) (tree_heightP t2_2));elimtype False ;omega.
      inversion H.
      inversion H.
      destruct (max (tree_heightP t1_1) (tree_heightP t1_2));inversion H1.
      inversion H.
      destruct (max (tree_heightP t1_1) (tree_heightP t1_2));
      destruct (max (tree_heightP t2_1) (tree_heightP t2_2));
      inversion H1.
    icase t1;icase t2.
    replace (mkCanon (Leaf b)) with (Leaf b) by apply mkCanon_Leaf.
    icase b.
    unfold intersect_tree.
    apply mkCanon_double.
    replace (mkCanon (Leaf b)) with (Leaf b) by apply mkCanon_Leaf.
    replace (intersect_tree (mkCanon (Node t1_1 t1_2)) (Leaf b))
    with (intersect_tree(Leaf b)(mkCanon (Node t1_1 t1_2)))
    by apply intersect_commute.
    replace (intersect_tree ( (Node t1_1 t1_2)) (Leaf b))
    with (intersect_tree(Leaf b)(Node t1_1 t1_2))
    by apply intersect_commute.
    icase b.
    unfold intersect_tree.
    apply mkCanon_double.

    assert (x >= max (tree_heightP t1_1) (tree_heightP t2_1)).
      simpl in H.
      replace (max (tree_heightP t1_1) (tree_heightP t1_2) + 1)
      with (S (max (tree_heightP t1_1) (tree_heightP t1_2)))
      in H by omega.
      replace (max (tree_heightP t2_1) (tree_heightP t2_2) + 1)
      with (S (max (tree_heightP t2_1) (tree_heightP t2_2)))
      in H by omega.
      generalize (succ_max_distr ((max (tree_heightP t1_1) (tree_heightP t1_2)))
      ((max (tree_heightP t2_1) (tree_heightP t2_2))));intro.
      rewrite<- H0 in H;clear H0.
      assert (x >= max (max (tree_heightP t1_1) (tree_heightP t1_2))
         (max (tree_heightP t2_1) (tree_heightP t2_2))) by omega.
      assert (max (max (tree_heightP t1_1) (tree_heightP t1_2))
       (max (tree_heightP t2_1) (tree_heightP t2_2)) >= max (tree_heightP t1_1) (tree_heightP t1_2)).
       apply le_max_l.
      assert (max (max (tree_heightP t1_1) (tree_heightP t1_2))
       (max (tree_heightP t2_1) (tree_heightP t2_2)) >= max (tree_heightP t2_1) (tree_heightP t2_2)).
       apply le_max_r.
      assert (max (tree_heightP t1_1) (tree_heightP t1_2) >= tree_heightP t1_1).
       apply le_max_l.
      assert (max (tree_heightP t2_1) (tree_heightP t2_2) >= tree_heightP t2_1).
       apply le_max_l.
      apply max_lub;omega.
    assert (x >= max (tree_heightP t1_2) (tree_heightP t2_2)).
      simpl in H.
      replace (max (tree_heightP t1_1) (tree_heightP t1_2) + 1)
      with (S (max (tree_heightP t1_1) (tree_heightP t1_2)))
      in H by omega.
      replace (max (tree_heightP t2_1) (tree_heightP t2_2) + 1)
      with (S (max (tree_heightP t2_1) (tree_heightP t2_2)))
      in H by omega.
      generalize (succ_max_distr ((max (tree_heightP t1_1) (tree_heightP t1_2)))
      ((max (tree_heightP t2_1) (tree_heightP t2_2))));intro.
      rewrite<- H1 in H;clear H1.
      assert (x >= max (max (tree_heightP t1_1) (tree_heightP t1_2))
         (max (tree_heightP t2_1) (tree_heightP t2_2))) by omega.
      assert (max (max (tree_heightP t1_1) (tree_heightP t1_2))
       (max (tree_heightP t2_1) (tree_heightP t2_2)) >= max (tree_heightP t1_1) (tree_heightP t1_2)).
       apply le_max_l.
      assert (max (max (tree_heightP t1_1) (tree_heightP t1_2))
       (max (tree_heightP t2_1) (tree_heightP t2_2)) >= max (tree_heightP t2_1) (tree_heightP t2_2)).
       apply le_max_r.
      assert (max (tree_heightP t1_1) (tree_heightP t1_2) >= tree_heightP t1_2).
       apply le_max_r.
      assert (max (tree_heightP t2_1) (tree_heightP t2_2) >= tree_heightP t2_2).
       apply le_max_r.
      apply max_lub;omega.
    generalize (IHx _ _ H0);intro.
    generalize (IHx _ _ H1);intro.
    remember (mkCanon (Node t1_1 t1_2));
    remember (mkCanon (Node t2_1 t2_2)).
    icase s;icase s0.
    generalize (mkCanon_Leaf_split _ _ _ Heqs);intro.
    generalize (mkCanon_Leaf_split _ _ _ Heqs0);intro.
    destruct H4 as [H41 H42].
    destruct H5 as [H51 H52].
    rewrite H41 in *.
    rewrite H51 in *.
    rewrite H42 in *.
    rewrite H52 in *.
    simpl.
    rewrite<-  H2.
    rewrite<- H3.
    simpl.
    icase b.
    generalize (mkCanon_Leaf b0);intro.
    rewrite H4.
    icase (bool_dec b0 b0);trivial.
    firstorder.


    generalize (mkCanon_Leaf_split _ _ _ Heqs);intro.
    symmetry in Heqs0.
    generalize (mkCanon_split _ _ _ _ Heqs0);intro.
    destruct H4 as [H41 H42].
    destruct H5 as [H51 H52].
    rewrite H41 in *.
    rewrite H42 in *.
    rewrite<- H51 in *.
    rewrite<- H52 in *.
    simpl.
    rewrite<-H2.
    rewrite<-H3.
    icase b.

    generalize (mkCanon_Leaf_split _ _ _ Heqs0);intro.
    symmetry in Heqs.
    generalize (mkCanon_split _ _ _ _ Heqs);intro.
    destruct H4 as [H41 H42].
    destruct H5 as [H51 H52].
    rewrite H41 in *.
    rewrite H42 in *.
    rewrite<- H51 in *.
    rewrite<- H52 in *.
    replace (intersect_tree (Node (mkCanon t1_1) (mkCanon t1_2)) (Leaf b))
    with (intersect_tree (Leaf b) (Node (mkCanon t1_1) (mkCanon t1_2)))
    by apply intersect_commute.
    replace (intersect_tree (mkCanon t1_1) (Leaf b))
    with (intersect_tree (Leaf b)(mkCanon t1_1)) in H2
    by apply intersect_commute.
    replace (intersect_tree (mkCanon t1_2) (Leaf b))
    with (intersect_tree (Leaf b)(mkCanon t1_2)) in H3
    by apply intersect_commute.
    simpl.
    rewrite<-H2.
    rewrite<-H3.
    icase b.

    symmetry in Heqs, Heqs0.
    generalize (mkCanon_split _ _ _ _ Heqs);intro.
    generalize (mkCanon_split _ _ _ _ Heqs0);intro.
    destruct H4 as [H41 H42].
    destruct H5 as [H51 H52].
    rewrite<-H41 in *.
    rewrite<- H42 in *.
    rewrite<-H51 in *.
    rewrite<-H52 in *.
    simpl.
    rewrite H2.
    rewrite H3.
    trivial.
  Qed.

  Lemma mkCanon_join_split : forall t11 t12 t21 t22 t31 t32,
                     join (exist (fun t => canonicalTree t)(mkCanon (Node t11 t12)) (mkCanon_correct _))
                          (exist (fun t => canonicalTree t)(mkCanon (Node t21 t22)) (mkCanon_correct _))
                          (exist (fun t => canonicalTree t)(mkCanon (Node t31 t32)) (mkCanon_correct _))->
                     join (exist (fun t => canonicalTree t)(mkCanon t11) (mkCanon_correct _))
                          (exist (fun t => canonicalTree t)(mkCanon t21) (mkCanon_correct _))
                          (exist (fun t => canonicalTree t)(mkCanon t31) (mkCanon_correct _))/\
                     join (exist (fun t => canonicalTree t)(mkCanon t12) (mkCanon_correct _))
                          (exist (fun t => canonicalTree t)(mkCanon t22) (mkCanon_correct _))
                          (exist (fun t => canonicalTree t)(mkCanon t32) (mkCanon_correct _)).
  Proof.
    intros.
    red in H. hnf in H.
    destruct H. split; red; hnf;
    inversion H;
    inversion H0;
    split;
    unfold BAF.glb, BAF.lub;
    apply exist_ext;
    simpl.

    clear - H2.
    assert (Leaf false = mkCanon (Node (Leaf false) (Leaf false))).
      compute;auto.
    rewrite H in H2.
    generalize (mkCanon_intersect ((Node t11 t12)) ((Node t21 t22)));intro.
    inversion H0.
    rewrite H3 in H2.
    generalize (mkCanon_eq_split _ _ _ _ H2);intro.
    destruct H1 as [? _].
    assert (mkCanon (Leaf false) = Leaf false).
      compute;auto.
    rewrite H4 in H1.
    generalize (mkCanon_intersect t11 t21);intro.
    rewrite H5.
    trivial.

    clear - H3.
    generalize (mkCanon_union((Node t11 t12)) ((Node t21 t22)));intro.
    inversion H.
    rewrite H1 in H3.
    generalize (mkCanon_eq_split _ _ _ _ H3);intro.
    destruct H0 as [? _].
    generalize (mkCanon_union t11 t21);intro.
    rewrite H2.
    trivial.

    clear - H2.
    assert (Leaf false = mkCanon (Node (Leaf false) (Leaf false))).
      compute;auto.
    rewrite H in H2.
    generalize (mkCanon_intersect ((Node t11 t12)) ((Node t21 t22)));intro.
    inversion H0.
    rewrite H3 in H2.
    generalize (mkCanon_eq_split _ _ _ _ H2);intro.
    destruct H1 as [_ ?].
    assert (mkCanon (Leaf false) = Leaf false).
      compute;auto.
    rewrite H4 in H1.
    generalize (mkCanon_intersect t12 t22);intro.
    rewrite H5.
    trivial.

    clear - H3.
    generalize (mkCanon_union((Node t11 t12)) ((Node t21 t22)));intro.
    inversion H.
    rewrite H1 in H3.
    generalize (mkCanon_eq_split _ _ _ _ H3);intro.
    destruct H0 as [_ ?].
    generalize (mkCanon_union t12 t22);intro.
    rewrite H2.
    trivial.
  Qed.

  Lemma mkCanon_join_combine : forall t11 t12 t21 t22 t31 t32,
                     join (exist (fun t => canonicalTree t)(mkCanon t11) (mkCanon_correct _))
                          (exist (fun t => canonicalTree t)(mkCanon t21) (mkCanon_correct _))
                          (exist (fun t => canonicalTree t)(mkCanon t31) (mkCanon_correct _))->
                     join (exist (fun t => canonicalTree t)(mkCanon t12) (mkCanon_correct _))
                          (exist (fun t => canonicalTree t)(mkCanon t22) (mkCanon_correct _))
                          (exist (fun t => canonicalTree t)(mkCanon t32) (mkCanon_correct _))->
                     join (exist (fun t => canonicalTree t)(mkCanon (Node t11 t12)) (mkCanon_correct _))
                          (exist (fun t => canonicalTree t)(mkCanon (Node t21 t22)) (mkCanon_correct _))
                          (exist (fun t => canonicalTree t)(mkCanon (Node t31 t32)) (mkCanon_correct _)).
  Proof.
    intros.
    hnf in *.
    destruct H as [H11 H12].
    destruct H0 as [H21 H22].
    unfold BAF.glb, BAF.lub in *.
    inv H11;inv H12;inv H21;inv H22.
    split;
    apply exist_ext.

    generalize (mkCanon_intersect t11 t21);intro H31.
    generalize (mkCanon_intersect t12 t22);intro H32.
    generalize (mkCanon_intersect (Node t11 t12) (Node t21 t22));intro H33.
    rewrite H31 in H0;clear H31.
    rewrite H32 in H2;clear H32.
    simpl;simpl in H33;
    rewrite H33;clear H33.
    rewrite H0.
    rewrite H2.
    icase (bool_dec false false).
    firstorder.

    generalize (mkCanon_union t11 t21);intro H31.
    generalize (mkCanon_union t12 t22);intro H32.
    generalize (mkCanon_union (Node t11 t12) (Node t21 t22));intro H33.
    rewrite H31 in H1;clear H31.
    rewrite H32 in H3;clear H32.
    simpl;simpl in H33;
    rewrite H33;clear H33.
    rewrite H1.
    rewrite H3.
    trivial.
  Qed.

  Lemma mkCanon_mkFull_split : forall n t1 t2 t1' t2', mkFull (S n) (mkCanon (Node t1 t2)) =
                                                 Some (Node t1' t2') <->
                                                 mkFull n (mkCanon t1) = Some t1' /\
                                                 mkFull n (mkCanon t2) = Some t2'.
  Proof.
    intros;
    remember (mkCanon (Node t1 t2));
    icase s.
    generalize (mkCanon_Leaf_split _ _ _ Heqs);intro H1.
    destruct H1 as [H1 H2].
    rewrite H1,H2.
    simpl.
    icase (mkFull n (Leaf b));
    split;intro H;inv H;auto;
    inv H0;inv H3;auto.

    symmetry in Heqs.
    generalize (mkCanon_split _ _ _ _ Heqs);intro H.
    destruct H as [H1 H2].
    rewrite H1,H2.
    apply mkFull_split.
  Qed.
  (*L20*)
  Lemma tree_round_left_zero : forall t, roundL 0 t = None.
  Proof.
   simpl.
   intros.
   unfold tree_round_left.
   icase (mkFull 0 (proj1_sig t0)).
  Qed.

  Lemma tree_round_left_combine: forall n t1 t2 t1' t2',
                                roundL n (exist (fun t => canonicalTree t)(mkCanon t1) (mkCanon_correct _))
                                = Some (exist (fun t => canonicalTree t)(mkCanon t1') (mkCanon_correct _)) ->
                                roundL n (exist (fun t => canonicalTree t)(mkCanon t2) (mkCanon_correct _))
                                = Some (exist (fun t => canonicalTree t)(mkCanon t2') (mkCanon_correct _))->
                                roundL (S n) (exist (fun t => canonicalTree t)(mkCanon (Node t1 t2)) (mkCanon_correct _))
                                = Some (exist (fun t => canonicalTree t)(mkCanon (Node t1' t2')) (mkCanon_correct _)).
  Proof.
    unfold roundL,roundableL_tree.
    intros ? ? ? ? ? H1 H2.
    unfold tree_round_left in *.
    unfold proj1_sig in *.
    remember (mkFull n (mkCanon t1)) as o1;
    remember (mkFull n (mkCanon t2)) as o2.
    icase o1;icase o2.
    symmetry in Heqo1,Heqo2.
    generalize (mkCanon_mkFull_split n t1 t2 s s0);intro H.
    destruct H as [_ H].
    detach H;auto.
    rewrite H.
    simpl.
    icase n.
    icase (tree_round_leftP (S n) s);
    icase (tree_round_leftP (S n) s0).
    inv H1;inv H2.
    f_equal;apply exist_ext.
    rewrite<- H1.
    rewrite<- H3.
    trivial.
  Qed.

  Lemma tree_round_left_split : forall n t1 t2 t1' t2',
                                roundL (S (S n)) (exist (fun t => canonicalTree t)(mkCanon (Node t1 t2)) (mkCanon_correct _))
                                = Some (exist (fun t => canonicalTree t)(mkCanon (Node t1' t2')) (mkCanon_correct _)) ->
                                roundL (S n) (exist (fun t => canonicalTree t)(mkCanon t1) (mkCanon_correct _))
                                = Some (exist (fun t => canonicalTree t)(mkCanon t1') (mkCanon_correct _)) /\
                                roundL (S n) (exist (fun t => canonicalTree t)(mkCanon t2) (mkCanon_correct _))
                                = Some (exist (fun t => canonicalTree t)(mkCanon t2') (mkCanon_correct _)).
  Proof.
    unfold roundL,roundableL_tree.
    intros ? ? ? ? ? H.
    unfold tree_round_left in *.
    unfold proj1_sig in *.
    remember (mkFull (S (S n)) (mkCanon (Node t1 t2))) as o.
    icase o.
    symmetry in Heqo.
    icase s;
    remember (S n) as nk.
    icase (mkCanon (Node t1 t2)).
    simpl in Heqo; icase (mkFull nk (Leaf b0)).
    simpl in Heqo;icase (mkFull nk s1);
    icase (mkFull nk s2).
    generalize (mkCanon_mkFull_split nk t1 t2 s1 s2);intro H1.
    destruct H1 as [H1 _].
    detach H1;trivial.
    destruct H1 as [H1 H2].
    rewrite H1,H2.
    simpl in H.
    rewrite Heqnk in *.
    icase (tree_round_leftP (S n) s1);
    icase (tree_round_leftP (S n) s2).
    inv H.
    generalize (mkCanon_eq_split _ _ _ _ H3);intro H.
    destruct H as [H4 H5].
    split;f_equal;apply exist_ext;trivial.
  Qed.

  Lemma tree_round_left_Leaf : forall b n,
  roundL (S n) (exist (fun t => canonicalTree t)(Leaf b) (canonTree_Leaf _))
  = Some (exist (fun t => canonicalTree t)(Leaf b) (canonTree_Leaf _)).
  Proof.
    unfold roundL,roundableL_tree.
    induction n.
    unfold tree_round_left.
    simpl.
    f_equal.
    apply exist_ext.
    trivial.

    generalize (canonTree_proof_irr (Leaf b) (mkCanon (Leaf b))
               (canonTree_Leaf _) (mkCanon_correct _));
    intro H.
    detach H.
    rewrite H in IHn.
    generalize (tree_round_left_combine _ _ _ _ _ IHn IHn);intro H1.
    generalize (canonTree_proof_irr (Leaf b) (mkCanon (Node (Leaf b) (Leaf b)))
               (canonTree_Leaf _) (mkCanon_correct _));
    intro H2.
    detach H2.
    rewrite H2;trivial.
    icase b.
    icase b.
  Qed.
  (*L15*)
  Lemma tree_round_left_identity : forall n t, height t < n ->
                                               roundL n t = Some t.
  Proof.
   unfold roundL,roundableL_tree.
   intros.
   assert (H1 : n > height t0) by omega.
   clear H;rename H1 into H.
   revert H;revert t0.
   induction n;intros;unfold height;simpl in *; unfold tree_height in *.
   inversion H;icase t0.
   destruct t0 as [x c].
   icase x.
   generalize (canonTree_proof_irr (Leaf b) (Leaf b) c (canonTree_Leaf _));intro H1.
   detach H1;trivial.
   rewrite H1.
   apply tree_round_left_Leaf.

   simpl in H.
   assert ( n > tree_heightP x1 /\ n > tree_heightP x2).
     generalize (le_max_l (tree_heightP x1) (tree_heightP x2)).
     generalize (le_max_r (tree_heightP x1) (tree_heightP x2)).
     intros.
     omega.
   destruct H0 as [H1 H2].
   copy c.
   simpl in c.
   destruct c as [H3 [H4 [H5 H6]]].
   generalize (IHn (exist (fun t => canonicalTree t) x1 H5) H1);intro.
   generalize (IHn (exist (fun t => canonicalTree t) x2 H6) H2);intro.
   generalize (canonTree_proof_irr x1 (mkCanon x1) H5 (mkCanon_correct _));intro H8.
   detach H8.
   generalize (canonTree_proof_irr x2 (mkCanon x2) H6 (mkCanon_correct _));intro H9.
   detach H9.
   generalize (canonTree_proof_irr (Node x1 x2) (mkCanon (Node x1 x2)) c0 (mkCanon_correct _));intro H10.
   detach H10.
   rewrite H8,H9,H10 in *.
   apply tree_round_left_combine;trivial.
   symmetry; apply mkCanon_identity;trivial.
   symmetry; apply mkCanon_identity;trivial.
   symmetry; apply mkCanon_identity;trivial.
  Qed.

  Lemma tree_round_left_one : forall t1 t2 t c,
   roundL 1 (exist (fun t => canonicalTree t)(Node t1 t2) c) = Some t ->
   exists b1,exists b2, t1 = Leaf b1 /\ t2 = Leaf b2 /\
   t = (exist (fun t => canonicalTree t)(Leaf b1) (canonTree_Leaf _)).
  Proof.
   unfold roundL,roundableL_tree.
   intros.
   icase t1;icase t2.
   exists b;exists b0.
   compute in H.
   inv H.
   split;trivial.
   split;trivial.
   apply exist_ext.
   trivial.
  Qed.
  (*L14*)
  Lemma tree_round_left_join : forall n t1 t2 t3 t1' t2' t3',
    join t1 t2 t3 ->
    roundL n t1 = Some t1' ->
    roundL n t2 = Some t2' ->
    roundL n t3 = Some t3' ->
    join t1' t2' t3'.
   Proof.
    unfold roundL,roundableL_tree.
    induction n;intros.
    destruct t1.
    unfold tree_round_left in H0.
    simpl in H0.
    icase x.

    icase n.

    destruct t1 as [t1 ?];
    destruct t2 as [t2 ?];
    destruct t3 as [t3 ?].
    icase t1;icase t2;icase t3.
    inv H.
    inv H3.
    inv H4.
    inv H0.
    inv H1.
    inv H2.
    icase b;icase b0;icase b1;
    compute;split;apply exist_ext;trivial.

    generalize (tree_round_left_one _ _ _ _ H2);intro H3.
    destruct H3 as [b31 [b32 [H31 [H32 H33]]]];subst.
    destruct H as [_ H].
    elimtype False;clear-H.
    inv H.
    icase b.

   generalize (tree_round_left_one _ _ _ _ H1);intro H3.
   destruct H3 as [b31 [b32 [H31 [H32 H33]]]];subst.
   destruct H as [H3 H4].
   elimtype False;clear-H3 H4 c0.
   inv H3.
   inv H4.
   generalize (mkCanon_identity _ c0);intro.
   icase b;
   congruence.

   generalize (tree_round_left_one _ _ _ _ H1);intro H3.
   destruct H3 as [b31 [b32 [H31 [H32 H33]]]];subst.
   generalize (tree_round_left_one _ _ _ _ H2);intro H4.
   destruct H4 as [b41 [b42 [H41 [H42 H43]]]];subst.
   generalize (tree_round_left_Leaf b 0);intro H5.
   assert (canonTree_Leaf b = c) by apply proof_irr.
   rewrite H3 in H5;clear H3.
   unfold roundL,roundableL_tree in *.
   rewrite H5 in H0;clear H5.
   inv H0.
   icase b;
   inv H;
   inv H3.
   icase (bool_dec b31 b32).
   inv H4.
   split.
   unfold BAF.glb.
   apply exist_ext.
   simpl.
   trivial.
   unfold BAF.lub.
   apply exist_ext.
   simpl.
   trivial.

   generalize (tree_round_left_one _ _ _ _ H0);intro H3.
   destruct H3 as [b31 [b32 [H31 [H32 H33]]]];subst.
   elimtype False;clear -H c.
   destruct H as [H1 H2].
   inv H1;inv H2.
   generalize (mkCanon_identity _ c);intro.
   icase b;congruence.

   generalize (tree_round_left_one _ _ _ _ H0);intro H3.
   destruct H3 as [b31 [b32 [H31 [H32 H33]]]];subst.
   generalize (tree_round_left_one _ _ _ _ H2);intro H4.
   destruct H4 as [b41 [b42 [H41 [H42 H43]]]];subst.
   generalize (tree_round_left_Leaf b 0);intro.
   assert (canonTree_Leaf b = c0) by apply proof_irr.
   rewrite H4 in H3;clear H4.
   unfold roundL,roundableL_tree in *.
   rewrite H3 in H1;clear H3.
   inv H1.
   icase b;
   inv H;
   inv H3;
   inv H4.
   icase (bool_dec b31 b32).
   inv H3.
   split.
   unfold BAF.glb.
   apply exist_ext.
   simpl.
   icase b41;trivial.
   unfold BAF.lub.
   apply exist_ext.
   simpl.
   icase b41;
   trivial.

   generalize (tree_round_left_one _ _ _ _ H0);intro H3.
   destruct H3 as [b31 [b32 [H31 [H32 H33]]]];subst.
   generalize (tree_round_left_one _ _ _ _ H1);intro H4.
   destruct H4 as [b41 [b42 [H41 [H42 H43]]]];subst.
   generalize (tree_round_left_Leaf b 0);intro.
   assert (canonTree_Leaf b = c1) by apply proof_irr.
   rewrite H4 in H3;clear H4.
   unfold roundL,roundableL_tree in *.
   rewrite H3 in H2;clear H3.
   inv H2.
   icase b;
   inv H;
   inv H2;inv H3;
   icase b31;icase b41;icase b32;icase b42;inv H4;inv H2;
   split;
   unfold BAF.glb, BAF.lub;
   apply exist_ext;
   simpl;trivial.

   generalize (tree_round_left_one _ _ _ _ H0);intro H3.
   destruct H3 as [b31 [b32 [H31 [H32 H33]]]];subst.
   generalize (tree_round_left_one _ _ _ _ H1);intro H4.
   destruct H4 as [b41 [b42 [H41 [H42 H43]]]];subst.
   generalize (tree_round_left_one _ _ _ _ H2);intro H5.
   destruct H5 as [b51 [b52 [H51 [H52 H53]]]];subst.
   inv H;
   inv H2;inv H3;
   icase b31;icase b41;icase b32;icase b42;inv H4;inv H2;
   split;
   unfold BAF.glb, BAF.lub;
   apply exist_ext;
   simpl;trivial.

   generalize (canonTree_rewrite1 t1);intro H3;
   generalize (canonTree_rewrite1 t2);intro H4;
   generalize (canonTree_rewrite1 t3);intro H5;
   generalize (canonTree_rewrite1 t1');intro H6;
   generalize (canonTree_rewrite1 t2');intro H7;
   generalize (canonTree_rewrite1 t3');intro H8;
   destruct H3 as [? [? ?]];
   destruct H4 as [? [? ?]];
   destruct H5 as [? [? ?]];
   destruct H6 as [? [? ?]];
   destruct H7 as [? [? ?]];
   destruct H8 as [? [? ?]].
   subst.

   generalize (tree_round_left_split _ _ _ _ _ H0);intro H01.
   generalize (tree_round_left_split _ _ _ _ _ H1);intro H11.
   generalize (tree_round_left_split _ _ _ _ _ H2);intro H21.
   destruct H01 as [H01 H02].
   destruct H11 as [H11 H12].
   destruct H21 as [H21 H22].
   generalize (mkCanon_join_split _ _ _ _ _ _ H);intro H3.
   destruct H3 as [H31 H32].
   generalize (IHn _ _ _ _ _ _ H31 H01 H11 H21);intro H41.
   generalize (IHn _ _ _ _ _ _ H32 H02 H12 H22);intro H42.
   apply mkCanon_join_combine;trivial.
  Qed.
  (*L16*)
  Lemma tree_round_left_None : forall n t,
   n < height t ->
   roundL n t = None.
  Proof.
   unfold roundL,roundableL_tree in *.
   intros.
   unfold tree_round_left.
   generalize (mkFull_None _ _ H);intro.
   rewrite H0.
   trivial.
  Qed.
  (*L17*)
  Lemma tree_round_left_decrease : forall n t,
   S n = height t ->
   exists t', roundL (S n) t = Some t' /\ height t' <= n.
  Proof.
  unfold roundL,roundableL_tree in *.
  unfold height;simpl.
  intro.
  induction n;intros;
  destruct t0;
  icase x.
  icase x1;icase x2;unfold tree_height in *;inversion H.
  exists (exist (fun t => canonicalTree t) (Leaf b) (canonTree_Leaf _)).
  compute;split;try omega;try f_equal;try apply exist_ext;trivial.
  elimtype False;omega.
  elimtype False;clear -H1.
  assert (0 = max (max (tree_heightP x1_1) (tree_heightP x1_2) + 1) 0) by omega;
  clear H1.
  generalize (max_0_r (max (tree_heightP x1_1) (tree_heightP x1_2) + 1));intro.
  rewrite H0 in H;clear H0.
  omega.
  elimtype False;clear -H1.
  assert (0 = max (max (tree_heightP x1_1) (tree_heightP x1_2) + 1)
       (max (tree_heightP x2_1) (tree_heightP x2_2) + 1)) by omega;
  clear H1.
  generalize (plus_max_distr_r (max (tree_heightP x1_1) (tree_heightP x1_2))
                               (max (tree_heightP x2_1) (tree_heightP x2_2)) 1);intro.
  rewrite H0 in H;omega.

  remember (S n) as nk.
  unfold tree_height in H.
  simpl in H.
  assert (nk = max (tree_heightP x1) (tree_heightP x2)) by omega;clear H.
  generalize (lt_dec (tree_heightP x1) (tree_heightP x2) );intro H.
  destruct H.

  assert (nk = tree_heightP x2).
    assert (tree_heightP x1 <= tree_heightP x2 ) by omega.
    generalize (max_r _ _ H);intro.
    congruence.
  rewrite<- H in l.
  copy c.
  simpl in c;destruct c as [? [? [? ?]]].
  generalize (IHn (exist (fun t => canonicalTree t) x2 H4) H);intro H21.
  generalize (tree_round_left_identity _ (exist (fun t => canonicalTree t) x1 H3) l);intro H11.
  destruct H21 as [? [H21 H22]].
  destruct x.
  assert (tree_round_left nk (exist (fun t : ShareTree => canonicalTree t) x2 H4)=
          tree_round_left nk (exist (fun t => canonicalTree t) (mkCanon x2) (mkCanon_correct _))).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ H4);intro H23;
    rewrite H23;
    trivial.
  rewrite H5 in H21;clear H5.
  assert (exist (fun t : ShareTree => canonicalTree t) x c =
          exist (fun t => canonicalTree t) (mkCanon x) (mkCanon_correct _)).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ c);intro H23;
    rewrite H23;
    trivial.
  rewrite H5 in H21;clear H5.
  assert (exist (fun t : ShareTree => canonicalTree t) x1 H3 =
          exist (fun t => canonicalTree t) (mkCanon x1) (mkCanon_correct _)).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ H3);intro H13;
    rewrite H13;
    trivial.
  rewrite H5 in H11;clear H5.
  assert (tree_round_left (S nk) (exist (fun t0 : ShareTree => canonicalTree t0) (Node x1 x2) c0) =
          tree_round_left (S nk) (exist (fun t => canonicalTree t) (mkCanon (Node x1 x2)) (mkCanon_correct _))).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ c0);intro H33;
    simpl in H33;
    rewrite H33;
    trivial.
  rewrite H5;clear H5.
  generalize (tree_round_left_combine _ _ _ _ _ H11 H21);intro.
  unfold roundL,roundableL_tree in *.
  rewrite H5;clear H5.
  exists (exist (fun t0 : ShareTree => canonicalTree t0) (mkCanon (Node x1 x))
          (mkCanon_correct (Node x1 x))).
  split;trivial;subst nk.
  clear -H22 l.
  assert (tree_heightP x1 <= n) by omega;clear l.
  unfold tree_height in *;simpl in *.
  assert (tree_heightP (Node x1 x) <= S n).
   generalize (max_lub _ _ _ H H22);intro.
   simpl.
   omega.
  assert (mkCanon (Node x1 x) = mkCanon (Node x1 x)) by trivial.
  generalize (mkCanon_height _ _ H1);intro.
  simpl in *.
  omega.

  assert (tree_heightP x1 = tree_heightP x2 \/ tree_heightP x1 > tree_heightP x2).
  omega.
  destruct H.

  rewrite<- H in H0.
  generalize (max_idempotent (tree_heightP x1));intro.
  rewrite H1 in H0.
  rewrite<- H0 in H.
  clear n0 H1.
  assert (tree_round_left (S nk) (exist (fun t => canonicalTree t) (Node x1 x2) c) =
          tree_round_left (S nk) (exist (fun t => canonicalTree t) (mkCanon (Node x1 x2)) (mkCanon_correct _))).
    simpl.
    f_equal.
    apply exist_ext.
    generalize (mkCanon_identity _ c);intro.
    rewrite<-H1.
    trivial.
  rewrite H1;clear H1.
  copy c.
  simpl in c.
  destruct c as [? [? [? ?]]].
  generalize (IHn (exist (fun t => canonicalTree t) x1 H3) H0);intro H5.
  generalize (IHn (exist (fun t => canonicalTree t) x2 H4) H);intro H6.
  destruct H5 as [? [H11 H12]].
  destruct H6 as [? [H21 H22]].
  assert (tree_round_left nk (exist (fun t : ShareTree => canonicalTree t) x1 H3)=
          tree_round_left nk (exist (fun t => canonicalTree t) (mkCanon x1) (mkCanon_correct _))).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ H3);intro H13;
    rewrite H13;
    trivial.
  rewrite H5 in H11;clear H5.
  assert (tree_round_left nk (exist (fun t : ShareTree => canonicalTree t) x2 H4)=
          tree_round_left nk (exist (fun t => canonicalTree t) (mkCanon x2) (mkCanon_correct _))).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ H4);intro H23;
    rewrite H23;
    trivial.
  rewrite H5 in H21;clear H5.
  destruct x.
  assert (exist (fun t : ShareTree => canonicalTree t) x c =
          exist (fun t => canonicalTree t) (mkCanon x) (mkCanon_correct _)).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ c);intro H13;
    rewrite H13;
    trivial.
  rewrite H5 in H11;clear H5.
  destruct x0.
  assert (exist (fun t : ShareTree => canonicalTree t) x0 c1 =
          exist (fun t => canonicalTree t) (mkCanon x0) (mkCanon_correct _)).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ c1);intro H23;
    rewrite H23;
    trivial.
  rewrite H5 in H21;clear H5.
  generalize (tree_round_left_combine _ _ _ _ _ H11 H21);intro.
  unfold roundL,roundableL_tree in *.
  rewrite H5.
  exists (exist (fun t0 : ShareTree => canonicalTree t0) (mkCanon (Node x x0))
         (mkCanon_correct (Node x x0))).
  split;trivial.
  clear - H12 H22 Heqnk.
  unfold tree_height in *.
  simpl in *.
  subst nk.
  assert (tree_heightP (Node x x0) <= S n).
   generalize (max_lub _ _ _ H12 H22);intro.
   simpl.
   omega.
  assert (mkCanon (Node x x0) = mkCanon (Node x x0)) by trivial.
  generalize (mkCanon_height _ _ H0);intro.
  simpl in *.
  omega.

  assert (nk = tree_heightP x1).
    assert (tree_heightP x2 <= tree_heightP x1 ) by omega.
    generalize (max_l _ _ H1);intro.
    congruence.
  rewrite<- H1 in H.
  copy c.
  simpl in c;destruct c as [? [? [? ?]]].
  generalize (IHn (exist (fun t => canonicalTree t) x1 H4) H1);intro H11.
  generalize (tree_round_left_identity _ (exist (fun t => canonicalTree t) x2 H5) H);intro H21.
  destruct H11 as [? [H11 H12]].
  destruct x.
  assert (tree_round_left nk (exist (fun t : ShareTree => canonicalTree t) x1 H4)=
          tree_round_left nk (exist (fun t => canonicalTree t) (mkCanon x1) (mkCanon_correct _))).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ H4);intro H13;
    rewrite H13;
    trivial.
  rewrite H6 in H11;clear H6.
  assert (exist (fun t : ShareTree => canonicalTree t) x c =
          exist (fun t => canonicalTree t) (mkCanon x) (mkCanon_correct _)).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ c);intro H13;
    rewrite H13;
    trivial.
  rewrite H6 in H11;clear H6.
  assert (exist (fun t : ShareTree => canonicalTree t) x2 H5 =
          exist (fun t => canonicalTree t) (mkCanon x2) (mkCanon_correct _)).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ H5);intro H23;
    rewrite H23;
    trivial.
  rewrite H6 in H21;clear H6.
  assert (tree_round_left (S nk) (exist (fun t0 : ShareTree => canonicalTree t0) (Node x1 x2) c0) =
          tree_round_left (S nk) (exist (fun t => canonicalTree t) (mkCanon (Node x1 x2)) (mkCanon_correct _))).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ c0);intro H33;
    simpl in H33;
    rewrite H33;
    trivial.
  rewrite H6;clear H6.
  generalize (tree_round_left_combine _ _ _ _ _ H11 H21);intro.
  unfold roundL,roundableL_tree in *.
  rewrite H6;clear H6.
  exists (exist (fun t0 : ShareTree => canonicalTree t0) (mkCanon (Node x x2))
          (mkCanon_correct (Node x x2))).
  split;trivial;subst nk.
  clear -H12 H.
  assert (tree_heightP x2 <= n) by omega;clear H.
  unfold tree_height in *;simpl in *.
  assert (tree_heightP (Node x x2) <= S n).
   generalize (max_lub _ _ _ H12 H0);intro.
   simpl.
   omega.
  assert (mkCanon (Node x x2) = mkCanon (Node x x2)) by trivial.
  generalize (mkCanon_height _ _ H1);intro.
  simpl in *.
  omega.
  Qed.
  (*L18*)
  Lemma tree_round_left_Some : forall n t,
   height t <= S n ->
   exists t', roundL (S n) t = Some t'.
  Proof.
   unfold roundL,roundableL_tree in *.
   unfold height;simpl.
   intros.
   inv H.
   symmetry in H1.
   copy H1.
   apply tree_round_left_decrease in H1.
   destruct H1 as [? [? ?]].
   exists x.
   rewrite<- H0.
   trivial.

   assert (H2 : tree_height t0 < S n) by omega.
   apply tree_round_left_identity in H2.
   exists t0.
   trivial.
  Qed.
  (*L19*)
  Lemma tree_round_left_height_compare : forall t t' n,
   roundL n t = Some t' ->
   height t' < n.
  Proof.
   unfold roundL,roundableL_tree in *.
   unfold height;simpl.
   intros.
   destruct n.
   destruct t0.
   compute in H.
   icase x.
   assert (H1 := le_lt_dec (tree_height t0) (S n)).
   destruct H1.
   inv l.
   symmetry in H1.
   copy H1.
   apply tree_round_left_decrease in H1.
   destruct H1 as [? [? ?]].
   unfold roundL,roundableL_tree in *.
   rewrite H in H1.
   inv H1.
   simpl in *.
   omega.
   assert (H2 : tree_height t0 < S n) by omega.
   apply tree_round_left_identity in H2.
   unfold roundL,roundableL_tree in *.
   rewrite H in H2.
   inv H2.
   omega.
   apply tree_round_left_None in l.
   unfold roundL,roundableL_tree in *.
   rewrite H in l.
   inv l.
  Qed.

  Lemma tree_round_right_combine : forall n t1 t2 t1' t2',
                                roundR n (exist (fun t => canonicalTree t)(mkCanon t1) (mkCanon_correct _))
                                = Some (exist (fun t => canonicalTree t)(mkCanon t1') (mkCanon_correct _)) ->
                                roundR n (exist (fun t => canonicalTree t)(mkCanon t2) (mkCanon_correct _))
                                = Some (exist (fun t => canonicalTree t)(mkCanon t2') (mkCanon_correct _))->
                                roundR (S n) (exist (fun t => canonicalTree t)(mkCanon (Node t1 t2)) (mkCanon_correct _))
                                = Some (exist (fun t => canonicalTree t)(mkCanon (Node t1' t2')) (mkCanon_correct _)).
  Proof.
    unfold roundR,roundableR_tree in *.
    intros ? ? ? ? ? H1 H2.
    unfold tree_round_right in *.
    unfold proj1_sig in *.
    remember (mkFull n (mkCanon t1)) as o1;
    remember (mkFull n (mkCanon t2)) as o2.
    icase o1;icase o2.
    symmetry in Heqo1,Heqo2.
    generalize (mkCanon_mkFull_split n t1 t2 s s0);intro H.
    destruct H as [_ H].
    detach H;auto.
    rewrite H.
    simpl.
    icase n.
    icase (tree_round_rightP (S n) s);
    icase (tree_round_rightP (S n) s0).
    inv H1;inv H2.
    f_equal;apply exist_ext.
    rewrite<- H1.
    rewrite<- H3.
    trivial.
  Qed.

  Lemma tree_round_right_split : forall n t1 t2 t1' t2',
                                roundR (S (S n)) (exist (fun t => canonicalTree t)(mkCanon (Node t1 t2)) (mkCanon_correct _))
                                = Some (exist (fun t => canonicalTree t)(mkCanon (Node t1' t2')) (mkCanon_correct _)) ->
                                roundR (S n) (exist (fun t => canonicalTree t)(mkCanon t1) (mkCanon_correct _))
                                = Some (exist (fun t => canonicalTree t)(mkCanon t1') (mkCanon_correct _)) /\
                                roundR (S n) (exist (fun t => canonicalTree t)(mkCanon t2) (mkCanon_correct _))
                                = Some (exist (fun t => canonicalTree t)(mkCanon t2') (mkCanon_correct _)).
  Proof.
    unfold roundR,roundableR_tree in *.
    intros ? ? ? ? ? H.
    unfold tree_round_right in *.
    unfold proj1_sig in *.
    remember (mkFull (S (S n)) (mkCanon (Node t1 t2))) as o.
    icase o.
    symmetry in Heqo.
    icase s;
    remember (S n) as nk.
    icase (mkCanon (Node t1 t2)).
    simpl in Heqo; icase (mkFull nk (Leaf b0)).
    simpl in Heqo;icase (mkFull nk s1);
    icase (mkFull nk s2).
    generalize (mkCanon_mkFull_split nk t1 t2 s1 s2);intro H1.
    destruct H1 as [H1 _].
    detach H1;trivial.
    destruct H1 as [H1 H2].
    rewrite H1,H2.
    simpl in H.
    rewrite Heqnk in *.
    icase (tree_round_rightP (S n) s1);
    icase (tree_round_rightP (S n) s2).
    inv H.
    generalize (mkCanon_eq_split _ _ _ _ H3);intro H.
    destruct H as [H4 H5].
    split;f_equal;apply exist_ext;trivial.
  Qed.

  Lemma tree_round_right_Leaf : forall b n,
   roundR (S n) (exist (fun t => canonicalTree t)(Leaf b) (canonTree_Leaf _))
   = Some (exist (fun t => canonicalTree t)(Leaf b) (canonTree_Leaf _)).
  Proof.
    unfold roundR,roundableR_tree in *.
    induction n.
    unfold tree_round_right.
    simpl.
    f_equal.
    apply exist_ext.
    trivial.

    generalize (canonTree_proof_irr (Leaf b) (mkCanon (Leaf b))
               (canonTree_Leaf _) (mkCanon_correct _));
    intro H.
    detach H.
    rewrite H in IHn.
    generalize (tree_round_right_combine _ _ _ _ _ IHn IHn);intro H1.
    generalize (canonTree_proof_irr (Leaf b) (mkCanon (Node (Leaf b) (Leaf b)))
               (canonTree_Leaf _) (mkCanon_correct _));
    intro H2.
    detach H2.
    rewrite H2;trivial.
    icase b.
    icase b.
  Qed.
  (*L22*)
  Lemma tree_round_right_identity : forall n t,
   height t < n ->
   roundR n t = Some t.
  Proof.
   unfold roundR,roundableR_tree in *.
   simpl.
   intros.
   assert ( H1 : n > tree_height t0) by omega.
   clear H;rename H1 into H.
   revert H;revert t0.
   induction n;intros;unfold tree_height in *.
   inversion H;icase t0.
   destruct t0 as [x c].
   icase x.
   generalize (canonTree_proof_irr (Leaf b) (Leaf b) c (canonTree_Leaf _));intro H1.
   detach H1;trivial.
   rewrite H1.
   apply tree_round_right_Leaf.

   simpl in H.
   assert ( n > tree_heightP x1 /\ n > tree_heightP x2).
     generalize (le_max_l (tree_heightP x1) (tree_heightP x2)).
     generalize (le_max_r (tree_heightP x1) (tree_heightP x2)).
     intros.
     omega.
   destruct H0 as [H1 H2].
   copy c.
   simpl in c.
   destruct c as [H3 [H4 [H5 H6]]].
   generalize (IHn (exist (fun t => canonicalTree t) x1 H5) H1);intro.
   generalize (IHn (exist (fun t => canonicalTree t) x2 H6) H2);intro.
   generalize (canonTree_proof_irr x1 (mkCanon x1) H5 (mkCanon_correct _));intro H8.
   detach H8.
   generalize (canonTree_proof_irr x2 (mkCanon x2) H6 (mkCanon_correct _));intro H9.
   detach H9.
   generalize (canonTree_proof_irr (Node x1 x2) (mkCanon (Node x1 x2)) c0 (mkCanon_correct _));intro H10.
   detach H10.
   rewrite H8,H9,H10 in *.
   apply tree_round_right_combine;trivial.
   symmetry; apply mkCanon_identity;trivial.
   symmetry; apply mkCanon_identity;trivial.
   symmetry; apply mkCanon_identity;trivial.
  Qed.

  Lemma tree_round_right_one : forall t1 t2 t c,
   roundR 1 (exist (fun t => canonicalTree t)(Node t1 t2) c) = Some t ->
   exists b1,exists b2, t1 = Leaf b1 /\ t2 = Leaf b2 /\
   t = (exist (fun t => canonicalTree t)(Leaf b2) (canonTree_Leaf _)).
  Proof.
   unfold roundR,roundableR_tree in *.
   intros.
   icase t1;icase t2.
   exists b;exists b0.
   compute in H.
   inv H.
   split;trivial.
   split;trivial.
   apply exist_ext.
   trivial.
  Qed.
  (*L21*)
  Lemma tree_round_right_join : forall n t1 t2 t3 t1' t2' t3',
    join t1 t2 t3 ->
    roundR n t1 = Some t1' ->
    roundR n t2 = Some t2' ->
    roundR n t3 = Some t3' ->
    join t1' t2' t3'.
  Proof.
    unfold roundR,roundableR_tree in *.
    induction n;intros.
    destruct t1.
    unfold tree_round_right in H0.
    simpl in H0.
    icase x.

    icase n.

    destruct t1 as [t1 ?];
    destruct t2 as [t2 ?];
    destruct t3 as [t3 ?].
    icase t1;icase t2;icase t3.
    inv H.
    inv H3.
    inv H4.
    inv H0.
    inv H1.
    inv H2.
    icase b;icase b0;icase b1;
    compute;split;apply exist_ext;trivial.

    generalize (tree_round_right_one _ _ _ _ H2);intro H3.
    destruct H3 as [b31 [b32 [H31 [H32 H33]]]];subst.
    destruct H as [_ H].
    elimtype False;clear-H.
    inv H.
    icase b.

   generalize (tree_round_right_one _ _ _ _ H1);intro H3.
   destruct H3 as [b31 [b32 [H31 [H32 H33]]]];subst.
   destruct H as [H3 H4].
   elimtype False;clear-H3 H4 c0.
   inv H3.
   inv H4.
   generalize (mkCanon_identity _ c0);intro.
   icase b;
   congruence.

   generalize (tree_round_right_one _ _ _ _ H1);intro H3.
   destruct H3 as [b31 [b32 [H31 [H32 H33]]]];subst.
   generalize (tree_round_right_one _ _ _ _ H2);intro H4.
   destruct H4 as [b41 [b42 [H41 [H42 H43]]]];subst.
   generalize (tree_round_right_Leaf b 0);intro H5.
   assert (canonTree_Leaf b = c) by apply proof_irr.
   rewrite H3 in H5;clear H3.
   unfold roundR,roundableR_tree in *.
   rewrite H5 in H0;clear H5.
   inv H0.
   icase b;
   inv H;
   inv H3.
   icase (bool_dec b31 b32).
   inv H4.
   split.
   unfold BAF.glb.
   apply exist_ext.
   simpl.
   trivial.
   unfold BAF.lub.
   apply exist_ext.
   simpl.
   trivial.

   generalize (tree_round_right_one _ _ _ _ H0);intro H3.
   destruct H3 as [b31 [b32 [H31 [H32 H33]]]];subst.
   elimtype False;clear -H c.
   destruct H as [H1 H2].
   inv H1;inv H2.
   generalize (mkCanon_identity _ c);intro.
   icase b;congruence.

   generalize (tree_round_right_one _ _ _ _ H0);intro H3.
   destruct H3 as [b31 [b32 [H31 [H32 H33]]]];subst.
   generalize (tree_round_right_one _ _ _ _ H2);intro H4.
   destruct H4 as [b41 [b42 [H41 [H42 H43]]]];subst.
   generalize (tree_round_right_Leaf b 0);intro.
   assert (canonTree_Leaf b = c0) by apply proof_irr.
   rewrite H4 in H3;clear H4.
   unfold roundR,roundableR_tree in *.
   rewrite H3 in H1;clear H3.
   inv H1.
   icase b;
   inv H;
   inv H3;
   inv H4.
   icase (bool_dec b31 b32).
   inv H3.
   split.
   unfold BAF.glb.
   apply exist_ext.
   simpl.
   icase b42.
   unfold BAF.lub.
   apply exist_ext.
   simpl.
   icase b42.


   generalize (tree_round_right_one _ _ _ _ H0);intro H3.
   destruct H3 as [b31 [b32 [H31 [H32 H33]]]];subst.
   generalize (tree_round_right_one _ _ _ _ H1);intro H4.
   destruct H4 as [b41 [b42 [H41 [H42 H43]]]];subst.
   generalize (tree_round_right_Leaf b 0);intro.
   assert (canonTree_Leaf b = c1) by apply proof_irr.
   rewrite H4 in H3;clear H4.
   unfold roundR,roundableR_tree in *.
   rewrite H3 in H2;clear H3.
   inv H2.
   icase b;
   inv H;
   inv H2;inv H3;
   icase b31;icase b41;icase b32;icase b42;inv H4;inv H2;
   split;
   unfold BAF.glb, BAF.lub;
   apply exist_ext;
   simpl;trivial.

   generalize (tree_round_right_one _ _ _ _ H0);intro H3.
   destruct H3 as [b31 [b32 [H31 [H32 H33]]]];subst.
   generalize (tree_round_right_one _ _ _ _ H1);intro H4.
   destruct H4 as [b41 [b42 [H41 [H42 H43]]]];subst.
   generalize (tree_round_right_one _ _ _ _ H2);intro H5.
   destruct H5 as [b51 [b52 [H51 [H52 H53]]]];subst.
   inv H;
   inv H2;inv H3;
   icase b31;icase b41;icase b32;icase b42;inv H4;inv H2;
   split;
   unfold BAF.glb, BAF.lub;
   apply exist_ext;
   simpl;trivial.

   generalize (canonTree_rewrite1 t1);intro H3;
   generalize (canonTree_rewrite1 t2);intro H4;
   generalize (canonTree_rewrite1 t3);intro H5;
   generalize (canonTree_rewrite1 t1');intro H6;
   generalize (canonTree_rewrite1 t2');intro H7;
   generalize (canonTree_rewrite1 t3');intro H8;
   destruct H3 as [? [? ?]];
   destruct H4 as [? [? ?]];
   destruct H5 as [? [? ?]];
   destruct H6 as [? [? ?]];
   destruct H7 as [? [? ?]];
   destruct H8 as [? [? ?]].
   subst.

   generalize (tree_round_right_split _ _ _ _ _ H0);intro H01.
   generalize (tree_round_right_split _ _ _ _ _ H1);intro H11.
   generalize (tree_round_right_split _ _ _ _ _ H2);intro H21.
   destruct H01 as [H01 H02].
   destruct H11 as [H11 H12].
   destruct H21 as [H21 H22].
   generalize (mkCanon_join_split _ _ _ _ _ _ H);intro H3.
   destruct H3 as [H31 H32].
   generalize (IHn _ _ _ _ _ _ H31 H01 H11 H21);intro H41.
   generalize (IHn _ _ _ _ _ _ H32 H02 H12 H22);intro H42.
   apply mkCanon_join_combine;trivial.
  Qed.
  (*L23*)
  Lemma tree_round_right_None : forall n t,
   n < height t ->
   roundR n t = None.
  Proof.
   unfold roundR,roundableR_tree in *.
   unfold height;simpl.
   intros.
   unfold tree_round_right.
   generalize (mkFull_None _ _ H);intro.
   rewrite H0.
   trivial.
  Qed.
  (*L24*)
  Lemma tree_round_right_decrease : forall n t,
   S n = height t ->
   exists t', roundR (S n) t = Some t' /\ height t' <= n.
  Proof.
  unfold roundR,roundableR_tree in *.
  unfold height;simpl.
  induction n;intros;
  destruct t0;
  icase x.
  icase x1;icase x2;unfold tree_height in *;inversion H.
  exists (exist (fun t => canonicalTree t) (Leaf b0) (canonTree_Leaf _)).
  compute;split;try omega;try f_equal;try apply exist_ext;trivial.
  elimtype False;omega.
  elimtype False;clear -H1.
  assert (0 = max (max (tree_heightP x1_1) (tree_heightP x1_2) + 1) 0) by omega;
  clear H1.
  generalize (max_0_r (max (tree_heightP x1_1) (tree_heightP x1_2) + 1));intro.
  rewrite H0 in H;clear H0.
  omega.
  elimtype False;clear -H1.
  assert (0 = max (max (tree_heightP x1_1) (tree_heightP x1_2) + 1)
       (max (tree_heightP x2_1) (tree_heightP x2_2) + 1)) by omega;
  clear H1.
  generalize (plus_max_distr_r (max (tree_heightP x1_1) (tree_heightP x1_2))
                               (max (tree_heightP x2_1) (tree_heightP x2_2)) 1);intro.
  rewrite H0 in H;omega.

  remember (S n) as nk.
  unfold tree_height in H.
  simpl in H.
  assert (nk = max (tree_heightP x1) (tree_heightP x2)) by omega;clear H.
  generalize (lt_dec (tree_heightP x1) (tree_heightP x2) );intro H.
  destruct H.

  assert (nk = tree_heightP x2).
    assert (tree_heightP x1 <= tree_heightP x2 ) by omega.
    generalize (max_r _ _ H);intro.
    congruence.
  rewrite<- H in l.
  copy c.
  simpl in c;destruct c as [? [? [? ?]]].
  generalize (IHn (exist (fun t => canonicalTree t) x2 H4) H);intro H21.
  generalize (tree_round_right_identity _ (exist (fun t => canonicalTree t) x1 H3) l);intro H11.
  destruct H21 as [? [H21 H22]].
  destruct x.
  assert (tree_round_right nk (exist (fun t : ShareTree => canonicalTree t) x2 H4)=
          tree_round_right nk (exist (fun t => canonicalTree t) (mkCanon x2) (mkCanon_correct _))).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ H4);intro H23;
    rewrite H23;
    trivial.
  rewrite H5 in H21;clear H5.
  assert (exist (fun t : ShareTree => canonicalTree t) x c =
          exist (fun t => canonicalTree t) (mkCanon x) (mkCanon_correct _)).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ c);intro H23;
    rewrite H23;
    trivial.
  rewrite H5 in H21;clear H5.
  assert (exist (fun t : ShareTree => canonicalTree t) x1 H3 =
          exist (fun t => canonicalTree t) (mkCanon x1) (mkCanon_correct _)).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ H3);intro H13;
    rewrite H13;
    trivial.
  rewrite H5 in H11;clear H5.
  assert (tree_round_right (S nk) (exist (fun t0 : ShareTree => canonicalTree t0) (Node x1 x2) c0) =
          tree_round_right (S nk) (exist (fun t => canonicalTree t) (mkCanon (Node x1 x2)) (mkCanon_correct _))).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ c0);intro H33;
    simpl in H33;
    rewrite H33;
    trivial.
  rewrite H5;clear H5.
  generalize (tree_round_right_combine _ _ _ _ _ H11 H21);intro.
  unfold roundR,roundableR_tree in *.
  rewrite H5;clear H5.
  exists (exist (fun t0 : ShareTree => canonicalTree t0) (mkCanon (Node x1 x))
          (mkCanon_correct (Node x1 x))).
  split;trivial;subst nk.
  clear -H22 l.
  assert (tree_heightP x1 <= n) by omega;clear l.
  unfold tree_height in *;simpl in *.
  assert (tree_heightP (Node x1 x) <= S n).
   generalize (max_lub _ _ _ H H22);intro.
   simpl.
   omega.
  assert (mkCanon (Node x1 x) = mkCanon (Node x1 x)) by trivial.
  generalize (mkCanon_height _ _ H1);intro.
  simpl in *.
  omega.

  assert (tree_heightP x1 = tree_heightP x2 \/ tree_heightP x1 > tree_heightP x2).
  omega.
  destruct H.

  rewrite<- H in H0.
  generalize (max_idempotent (tree_heightP x1));intro.
  rewrite H1 in H0.
  rewrite<- H0 in H.
  clear n0 H1.
  assert (tree_round_right (S nk) (exist (fun t => canonicalTree t) (Node x1 x2) c) =
          tree_round_right (S nk) (exist (fun t => canonicalTree t) (mkCanon (Node x1 x2)) (mkCanon_correct _))).
    simpl.
    f_equal.
    apply exist_ext.
    generalize (mkCanon_identity _ c);intro.
    rewrite<-H1.
    trivial.
  rewrite H1;clear H1.
  copy c.
  simpl in c.
  destruct c as [? [? [? ?]]].
  generalize (IHn (exist (fun t => canonicalTree t) x1 H3) H0);intro H5.
  generalize (IHn (exist (fun t => canonicalTree t) x2 H4) H);intro H6.
  destruct H5 as [? [H11 H12]].
  destruct H6 as [? [H21 H22]].
  assert (tree_round_right nk (exist (fun t : ShareTree => canonicalTree t) x1 H3)=
          tree_round_right nk (exist (fun t => canonicalTree t) (mkCanon x1) (mkCanon_correct _))).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ H3);intro H13;
    rewrite H13;
    trivial.
  rewrite H5 in H11;clear H5.
  assert (tree_round_right nk (exist (fun t : ShareTree => canonicalTree t) x2 H4)=
          tree_round_right nk (exist (fun t => canonicalTree t) (mkCanon x2) (mkCanon_correct _))).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ H4);intro H23;
    rewrite H23;
    trivial.
  rewrite H5 in H21;clear H5.
  destruct x.
  assert (exist (fun t : ShareTree => canonicalTree t) x c =
          exist (fun t => canonicalTree t) (mkCanon x) (mkCanon_correct _)).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ c);intro H13;
    rewrite H13;
    trivial.
  rewrite H5 in H11;clear H5.
  destruct x0.
  assert (exist (fun t : ShareTree => canonicalTree t) x0 c1 =
          exist (fun t => canonicalTree t) (mkCanon x0) (mkCanon_correct _)).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ c1);intro H23;
    rewrite H23;
    trivial.
  rewrite H5 in H21;clear H5.
  generalize (tree_round_right_combine _ _ _ _ _ H11 H21);intro.
  unfold roundR,roundableR_tree in *.
  rewrite H5.
  exists (exist (fun t0 : ShareTree => canonicalTree t0) (mkCanon (Node x x0))
         (mkCanon_correct (Node x x0))).
  split;trivial.
  clear - H12 H22 Heqnk.
  unfold tree_height in *.
  simpl in *.
  subst nk.
  assert (tree_heightP (Node x x0) <= S n).
   generalize (max_lub _ _ _ H12 H22);intro.
   simpl.
   omega.
  assert (mkCanon (Node x x0) = mkCanon (Node x x0)) by trivial.
  generalize (mkCanon_height _ _ H0);intro.
  simpl in *.
  omega.

  assert (nk = tree_heightP x1).
    assert (tree_heightP x2 <= tree_heightP x1 ) by omega.
    generalize (max_l _ _ H1);intro.
    congruence.
  rewrite<- H1 in H.
  copy c.
  simpl in c;destruct c as [? [? [? ?]]].
  generalize (IHn (exist (fun t => canonicalTree t) x1 H4) H1);intro H11.
  generalize (tree_round_right_identity _ (exist (fun t => canonicalTree t) x2 H5) H);intro H21.
  destruct H11 as [? [H11 H12]].
  destruct x.
  assert (tree_round_right nk (exist (fun t : ShareTree => canonicalTree t) x1 H4)=
          tree_round_right nk (exist (fun t => canonicalTree t) (mkCanon x1) (mkCanon_correct _))).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ H4);intro H13;
    rewrite H13;
    trivial.
  rewrite H6 in H11;clear H6.
  assert (exist (fun t : ShareTree => canonicalTree t) x c =
          exist (fun t => canonicalTree t) (mkCanon x) (mkCanon_correct _)).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ c);intro H13;
    rewrite H13;
    trivial.
  rewrite H6 in H11;clear H6.
  assert (exist (fun t : ShareTree => canonicalTree t) x2 H5 =
          exist (fun t => canonicalTree t) (mkCanon x2) (mkCanon_correct _)).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ H5);intro H23;
    rewrite H23;
    trivial.
  rewrite H6 in H21;clear H6.
  assert (tree_round_right (S nk) (exist (fun t0 : ShareTree => canonicalTree t0) (Node x1 x2) c0) =
          tree_round_right (S nk) (exist (fun t => canonicalTree t) (mkCanon (Node x1 x2)) (mkCanon_correct _))).
    simpl;
    f_equal;
    apply exist_ext;
    generalize (mkCanon_identity _ c0);intro H33;
    simpl in H33;
    rewrite H33;
    trivial.
  rewrite H6;clear H6.
  generalize (tree_round_right_combine _ _ _ _ _ H11 H21);intro.
  unfold roundR,roundableR_tree in *.
  rewrite H6;clear H6.
  exists (exist (fun t0 : ShareTree => canonicalTree t0) (mkCanon (Node x x2))
          (mkCanon_correct (Node x x2))).
  split;trivial;subst nk.
  clear -H12 H.
  assert (tree_heightP x2 <= n) by omega;clear H.
  unfold tree_height in *;simpl in *.
  assert (tree_heightP (Node x x2) <= S n).
   generalize (max_lub _ _ _ H12 H0);intro.
   simpl.
   omega.
  assert (mkCanon (Node x x2) = mkCanon (Node x x2)) by trivial.
  generalize (mkCanon_height _ _ H1);intro.
  simpl in *.
  omega.
 Qed.
 (*L25*)
 Lemma tree_round_right_Some : forall n t,
   height t <= S n ->
   exists t', roundR (S n) t = Some t'.
  Proof.
   unfold roundR,roundableR_tree in *.
   unfold height;simpl.
   intros.
   inv H.
   symmetry in H1.
   copy H1.
   apply tree_round_right_decrease in H1.
   destruct H1 as [? [? ?]].
   exists x.
   rewrite<- H0.
   trivial.

   assert (H2 : tree_height t0 < S n) by omega.
   apply tree_round_right_identity in H2.
   exists t0.
   trivial.
  Qed.
  (*L26*)
  Lemma tree_round_right_height_compare : forall t t' n,
   roundR n t = Some t' ->
   height t' < n.
  Proof.
   unfold roundR,roundableR_tree in *.
   unfold height;simpl.
   intros.
   destruct n.
   destruct t0.
   compute in H.
   icase x.
   assert (H1 := le_lt_dec (tree_height t0) (S n)).
   destruct H1.
   inv l.
   symmetry in H1.
   copy H1.
   apply tree_round_right_decrease in H1.
   destruct H1 as [? [? ?]].
   unfold roundR,roundableR_tree in *.
   rewrite H in H1.
   inv H1.
   simpl in *.
   omega.
   assert (H2 : tree_height t0 < S n) by omega.
   apply tree_round_right_identity in H2.
   unfold roundR,roundableR_tree in *.
   rewrite H in H2.
   inv H2.
   omega.
   apply tree_round_right_None in l.
   unfold roundR,roundableR_tree in *.
   rewrite H in l.
   inv l.
  Qed.

 (*L27*)
  Lemma tree_round_right_zero : forall t, roundR 0 t = None.
  Proof.
   simpl.
   intros.
   unfold tree_round_right.
   icase (mkFull 0 (proj1_sig t0)).
  Qed.

 Lemma tree_avg_Leaf : forall n b c,
  avg (S n) (exist (fun t => canonicalTree t)(Leaf b) c)
  (exist (fun t => canonicalTree t)(Leaf b) c)
  = Some (exist (fun t => canonicalTree t)(Leaf b) c).
  Proof.
   unfold avg,avgable_tree in *.
   induction n ;intros.
   simpl.
   f_equal;apply exist_ext.
   icase b.
   simpl in *.
   specialize ( IHn b c).
   icase (mkFull n (Leaf b)).
   simpl.
   icase (tree_avgP s s).
   f_equal;apply exist_ext.
   inv IHn.
   simpl.
   rewrite H0.
   icase b.
  Qed.

  (*L29*)
  Lemma tree_avg_identity : forall n t,
   height t < n ->
   avg n t t = Some t.
  Proof.
    unfold avg,avgable_tree in *.
    unfold height;simpl.
    induction n;intros;
    destruct t0;
    unfold tree_height in *.
    inv H.
    icase x.
    apply tree_avg_Leaf.
    simpl in H.
    assert (tree_heightP x1 < n /\ tree_heightP x2 < n).
      assert (max (tree_heightP x1) (tree_heightP x2) < n) by omega.
      generalize (le_max_l (tree_heightP x1) (tree_heightP x2));intro.
      generalize (le_max_r (tree_heightP x1) (tree_heightP x2));intro.
      split;omega.
    destruct H0 as [? ?].
    copy c.
    simpl in c0.
    destruct c0 as [? [? [? ?]]].
    generalize (IHn (exist (fun t => canonicalTree t) x1 c0) H0);intro.
    generalize (IHn (exist (fun t => canonicalTree t) x2 c1) H1);intro.
    clear - H2 H3.
    icase n.
    simpl in H2,H3;simpl.
    icase (mkFull n x1);
    icase (mkFull n x2).
    simpl.
    icase (tree_avgP s s);
    icase (tree_avgP s0 s0).
    inv H2;inv H3.
    apply f_equal.
    apply exist_ext.
    simpl.
    icase (mkCanon s1);
    icase (mkCanon s2).
    icase b; icase b0;simpl in *.
    elimtype False; firstorder.
    elimtype False; firstorder.
  Qed.

  (*L30*)
  Lemma tree_avg_None : forall n t1 t2,
   n <= max (height t1) (height t2) ->
   avg n t1 t2 = None.
  Proof.
   unfold avg,avgable_tree in *.
   unfold height;simpl.
   intros.
   icase n.
   assert (n < tree_height t1 \/n < tree_height t2).
    assert (n < max (tree_height t1) (tree_height t2)) by omega.
    apply Nat.max_lt_iff.
    trivial.
   destruct t1;destruct t2;
   simpl;destruct H0;
   unfold tree_height in *;
   simpl in *.
   generalize (mkFull_None _ _ H0);intro.
   rewrite H1.
   trivial.
   generalize (mkFull_None _ _ H0);intro.
   rewrite H1.
   icase (mkFull n x).
  Qed.

  Lemma tree_avg_split : forall n t11 t12 t21 t22 t31 t32,
                         avg (S (S n)) (exist (fun t => canonicalTree t) (mkCanon (Node t11 t12)) (mkCanon_correct _))
                                            (exist (fun t => canonicalTree t) (mkCanon (Node t21 t22)) (mkCanon_correct _))
                                     = Some (exist (fun t => canonicalTree t) (mkCanon (Node t31 t32)) (mkCanon_correct _))->
                         avg (S n )    (exist (fun t => canonicalTree t) (mkCanon t11) (mkCanon_correct _))
                                            (exist (fun t => canonicalTree t) (mkCanon t21) (mkCanon_correct _))
                                     = Some (exist (fun t => canonicalTree t) (mkCanon t31) (mkCanon_correct _)) /\
                         avg (S n )    (exist (fun t => canonicalTree t) (mkCanon t12) (mkCanon_correct _))
                                            (exist (fun t => canonicalTree t) (mkCanon t22) (mkCanon_correct _))
                                     = Some (exist (fun t => canonicalTree t) (mkCanon t32) (mkCanon_correct _)).
  Proof.
    unfold avg,avgable_tree in *.
    intros.
    simpl in *.
    remember (mkCanon (Node t11 t12));
    remember (mkCanon (Node t21 t22));
    simpl in Heqs,Heqs0;
    rewrite<- Heqs in H;
    rewrite<-Heqs0 in H;
    icase s;icase s0.

    generalize (mkCanon_Leaf_split _ _ _ Heqs);intro H1.
    generalize (mkCanon_Leaf_split _ _ _ Heqs0);intro H2.
    destruct H1 as [H11 H12];
    destruct H2 as [H21 H22];
    rewrite H11,H12,H21,H22 in *.
    icase (mkFull n (Leaf b));
    icase (mkFull n (Leaf b0)).
    simpl in H.
    icase (tree_avgP s s0).
    inv H.
    generalize (mkCanon_eq_split _ _ _ _ H1);intro H3.
    destruct H3 as [H31 H32].
    split;f_equal;apply exist_ext;trivial.

    symmetry in Heqs0;
    generalize (mkCanon_Leaf_split _ _ _ Heqs);intro H1;
    generalize (mkCanon_split _ _ _ _ Heqs0);intro H2.
    destruct H1 as [H11 H12];
    destruct H2 as [H21 H22].
    rewrite H11,H12,H21,H22 in *.
    icase (mkFull n (Leaf b));
    icase (mkFull n s0_1);
    icase (mkFull n s0_2).
    simpl in H.
    icase (tree_avgP s s0);
    icase (tree_avgP s s1).
    inv H.
    generalize (mkCanon_eq_split _ _ _ _ H1);intro H3.
    destruct H3 as [H31 H32].
    split;f_equal;apply exist_ext;trivial.

    symmetry in Heqs;
    generalize (mkCanon_split _ _ _ _ Heqs);intro H1;
    generalize (mkCanon_Leaf_split _ _ _ Heqs0);intro H2.
    destruct H1 as [H11 H12];
    destruct H2 as [H21 H22].
    rewrite H11,H12,H21,H22 in *.
    icase (mkFull n s1);
    icase (mkFull n s2);
    icase (mkFull n (Leaf b)).
    simpl in H.
    icase (tree_avgP s s3);
    icase (tree_avgP s0 s3).
    inv H.
    generalize (mkCanon_eq_split _ _ _ _ H1);intro H3.
    destruct H3 as [H31 H32].
    split;f_equal;apply exist_ext;trivial.

    symmetry in Heqs,Heqs0;
    generalize (mkCanon_split _ _ _ _ Heqs);intro H1;
    generalize (mkCanon_split _ _ _ _ Heqs0);intro H2.
    destruct H1 as [H11 H12];
    destruct H2 as [H21 H22].
    rewrite H11,H12,H21,H22 in *.
    icase (mkFull n s1);
    icase (mkFull n s2);
    icase (mkFull n s0_1);
    icase (mkFull n s0_2).
    simpl in H.
    icase (tree_avgP s s3);
    icase (tree_avgP s0 s4).
    inv H.
    generalize (mkCanon_eq_split _ _ _ _ H1);intro H3.
    destruct H3 as [H31 H32].
    split;f_equal;apply exist_ext;trivial.
  Qed.

  Lemma tree_avg_combine : forall n t11 t12 t21 t22 t31 t32,
                           avg n (exist (fun t => canonicalTree t) (mkCanon t11) (mkCanon_correct _))
                                            (exist (fun t => canonicalTree t) (mkCanon t21) (mkCanon_correct _))
                                     = Some (exist (fun t => canonicalTree t) (mkCanon t31) (mkCanon_correct _)) ->
                           avg n (exist (fun t => canonicalTree t) (mkCanon t12) (mkCanon_correct _))
                                            (exist (fun t => canonicalTree t) (mkCanon t22) (mkCanon_correct _))
                                     = Some (exist (fun t => canonicalTree t) (mkCanon t32) (mkCanon_correct _)) ->
                           avg (S n) (exist (fun t => canonicalTree t) (mkCanon (Node t11 t12)) (mkCanon_correct _))
                                            (exist (fun t => canonicalTree t) (mkCanon (Node t21 t22)) (mkCanon_correct _))
                                     = Some (exist (fun t => canonicalTree t) (mkCanon (Node t31 t32)) (mkCanon_correct _)).
   Proof.
    unfold avg,avgable_tree in *.
    intros ? ? ? ? ? ? ? H1 H2.
    icase n.
    simpl in *.
    remember (mkCanon (Node t11 t12));
    remember (mkCanon (Node t21 t22));
    simpl in Heqs,Heqs0;
    rewrite<- Heqs;
    rewrite<- Heqs0;
    icase s;icase s0.

    generalize (mkCanon_Leaf_split _ _ _ Heqs);intro H11;
    generalize (mkCanon_Leaf_split _ _ _ Heqs0);intro H21.
    destruct H11 as [H11 H12];
    destruct H21 as [H21 H22].
    rewrite H11,H12,H21,H22 in *.
    icase (mkFull n (Leaf b));
    icase (mkFull n (Leaf b0)).
    simpl.
    icase (tree_avgP s s0).
    inv H1;inv H2.
    f_equal;apply exist_ext.
    simpl.
    rewrite<-H0;rewrite<-H1;trivial.

    symmetry in Heqs0;
    generalize (mkCanon_Leaf_split _ _ _ Heqs);intro H11;
    generalize (mkCanon_split _ _ _ _ Heqs0);intro H21.
    destruct H11 as [H11 H12];
    destruct H21 as [H21 H22].
    rewrite H11,H12,H21,H22 in *.
    icase (mkFull n (Leaf b));
    icase (mkFull n s0_1);
    icase (mkFull n s0_2).
    simpl.
    icase (tree_avgP s s0);
    icase (tree_avgP s s1).
    inv H1;inv H2.
    f_equal;apply exist_ext.
    rewrite<-H0;rewrite<-H1;trivial.

    symmetry in Heqs;
    generalize (mkCanon_split _ _ _ _ Heqs);intro H11;
    generalize (mkCanon_Leaf_split _ _ _ Heqs0);intro H21.
    destruct H11 as [H11 H12];
    destruct H21 as [H21 H22].
    rewrite H11,H12,H21,H22 in *.
    icase (mkFull n s1);
    icase (mkFull n s2);
    icase (mkFull n (Leaf b)).
    simpl.
    icase (tree_avgP s s3);
    icase (tree_avgP s0 s3).
    inv H1;inv H2.
    f_equal;apply exist_ext.
    rewrite<- H0;rewrite<- H1;trivial.

    symmetry in Heqs,Heqs0;
    generalize (mkCanon_split _ _ _ _ Heqs);intro H11;
    generalize (mkCanon_split _ _ _ _ Heqs0);intro H21.
    destruct H11 as [H11 H12];
    destruct H21 as [H21 H22].
    rewrite H11,H12,H21,H22 in *.
    icase (mkFull n s1);
    icase (mkFull n s2);
    icase (mkFull n s0_1);
    icase (mkFull n s0_2).
    simpl.
    icase (tree_avgP s s3);
    icase (tree_avgP s0 s4).
    inv H1;inv H2.
    f_equal;apply exist_ext.
    rewrite<- H0;rewrite<- H1;trivial.
  Qed.
  (*L31*)
  Lemma tree_avg_round2avg : forall n t1 t2 t3,
   roundL n t3 = Some t1 ->
   roundR n t3 = Some t2 ->
   avg n t1 t2 = Some t3.
  Proof.
    simpl in *.
    induction n;intros ? ? ? H1 H2.
    destruct t3 as [x3 c3].
    icase x3.

    destruct t1 as [x1 c1];
    destruct t2 as [x2 c2];
    destruct t3 as [x3 c3].
    icase n.
    icase x3.
    inv H1;inv H2.
    simpl.
    apply f_equal;apply exist_ext.
    icase b.
    icase x3_1;icase x3_2.
    icase x1;icase x2.
    inv H1;inv H2.
    simpl.
    apply f_equal;apply exist_ext.
    icase b1;icase b2;compute in c3.
    elimtype False.
    destruct c3 as [c3 ?].
    destruct c3;
    inv H0.
    destruct c3 as [? [c3 ?]].
    destruct c3;
    inv H1.

    generalize (mkCanon_identity _ c3);intro H31.
    generalize (mkCanon_rewrite x3);intro H32.
    destruct H32 as [x31 [x32 H32]].
    rewrite H32 in H31.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c3 H31);intro H33.
    generalize (mkCanon_identity _ c1);intro H11.
    generalize (mkCanon_rewrite x1);intro H12.
    destruct H12 as [x11 [x12 H12]].
    rewrite H12 in H11.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c1 H11);intro H13.
    generalize (mkCanon_identity _ c2);intro H21.
    generalize (mkCanon_rewrite x2);intro H22.
    destruct H22 as [x21 [x22 H22]].
    rewrite H22 in H21.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c2 H21);intro H23.
    rewrite<- H33 in H1,H2.
    rewrite<- H13 in H1.
    rewrite<- H23 in H2.
    generalize (tree_round_left_split _ _ _ _ _ H1);intro H14.
    generalize (tree_round_right_split _ _ _ _ _ H2);intro H24.
    destruct H14 as [H14 H15];
    destruct H24 as [H24 H25].
    generalize (IHn _ _ _ H14 H24);intro H34.
    generalize (IHn _ _ _ H15 H25);intro H35.
    generalize (tree_avg_combine _ _ _ _ _ _ _ H34 H35);intro H36.
    rewrite H13 in H36.
    rewrite H23 in H36.
    rewrite H33 in H36.
    trivial.
   Qed.
  (*L32*)
  Lemma tree_avg_avg2round : forall n t1 t2 t3,
   avg n t1 t2 = Some t3 ->
   roundL n t3 = Some t1 /\
   roundR n t3 = Some t2.
  Proof.
    simpl.
    induction n;intros.
    inv H.

    destruct t1 as [x1 c1];
    destruct t2 as [x2 c2];
    destruct t3 as [x3 c3].
    icase n.
    icase x1;
    icase x2;
    icase x3.
    inv H.
    icase (bool_dec b b0).
    inv H1.
    unfold tree_round_left;
    unfold tree_round_right;
    simpl.
    try subst.
    split;apply f_equal;apply exist_ext;trivial.
    unfold tree_avg in H.
    simpl in H.
    inv H.
    icase (bool_dec b b0).
    inv H1.
    unfold tree_round_left;
    unfold tree_round_right;
    simpl.
    split;apply f_equal;apply exist_ext;trivial.

    generalize (mkCanon_identity _ c1);intro H11;
    generalize (mkCanon_identity _ c2);intro H21.
    generalize (mkCanon_identity _ c3);intro H31.
    generalize (mkCanon_rewrite x1);intro H12.
    generalize (mkCanon_rewrite x2);intro H22.
    generalize (mkCanon_rewrite x3);intro H32.
    destruct H12 as [x11 [x12 H12]].
    destruct H22 as [x21 [x22 H22]].
    destruct H32 as [x31 [x32 H32]].
    rewrite H12 in H11.
    rewrite H22 in H21.
    rewrite H32 in H31.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c1 H11);intro H13.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c2 H21);intro H23.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c3 H31);intro H33.
    rewrite<-H13 in *.
    rewrite<-H23 in *.
    rewrite<-H33 in *.
    generalize (tree_avg_split _ _ _ _ _ _ _ H);intro H34.
    destruct H34 as [H34 H35].
    generalize (IHn _ _ _ H34);intro H36.
    destruct H36 as [H36 H37].
    generalize (IHn _ _ _ H35);intro H38.
    destruct H38 as [H38 H39].
    split.
    apply tree_round_left_combine;trivial.
    apply tree_round_right_combine;trivial.
  Qed.
  (*L33*)
  Lemma tree_avg_join : forall n t11 t12 t13 t21 t22 t23 t31 t32 t33,
   avg n t11 t12 =  Some t13 ->
   avg n t21 t22 = Some t23 ->
   avg n t31 t32 = Some t33 ->
   join t11 t21 t31 ->
   join t12 t22 t32 ->
   join t13 t23 t33.
  Proof.
    simpl.
    induction n;
    intros ? ? ? ? ? ? ? ? ? H1 H2 H3 H4 H5.
    inv H1.

    destruct t11 as [x11 c11];
    destruct t12 as [x12 c12];
    destruct t13 as [x13 c13];
    destruct t21 as [x21 c21];
    destruct t22 as [x22 c22];
    destruct t23 as [x23 c23];
    destruct t31 as [x31 c31];
    destruct t32 as [x32 c32];
    destruct t33 as [x33 c33].
    icase n.

    icase x11;icase x12;
    icase x21;icase x22;
    icase x31;icase x32.
    unfold tree_avg in *;simpl in *.
    inv H1;inv H2;inv H3.
    destruct H4 as [H41 H42];
    destruct H5 as [H51 H52].
    split;
    unfold BAF.glb, BAF.lub in *;simpl in *;
    inv H41;inv H42;inv H51;inv H52;
    apply exist_ext.
    icase b;icase b0;icase b1;icase b2.
    icase b;icase b0;icase b1;icase b2;icase b3;icase b4.

    generalize (mkCanon_identity _ c11);intro H11.
    generalize (mkCanon_identity _ c12);intro H12.
    generalize (mkCanon_identity _ c13);intro H13.
    generalize (mkCanon_identity _ c21);intro H21.
    generalize (mkCanon_identity _ c22);intro H22.
    generalize (mkCanon_identity _ c23);intro H23.
    generalize (mkCanon_identity _ c31);intro H31.
    generalize (mkCanon_identity _ c32);intro H32.
    generalize (mkCanon_identity _ c33);intro H33.
    generalize (mkCanon_rewrite x11);intro H14;
    destruct H14 as [x111 [x112 H14]].
    generalize (mkCanon_rewrite x12);intro H15;
    destruct H15 as [x121 [x122 H15]].
    generalize (mkCanon_rewrite x13);intro H16;
    destruct H16 as [x131 [x132 H16]].
    generalize (mkCanon_rewrite x21);intro H24;
    destruct H24 as [x211 [x212 H24]].
    generalize (mkCanon_rewrite x22);intro H25;
    destruct H25 as [x221 [x222 H25]].
    generalize (mkCanon_rewrite x23);intro H26;
    destruct H26 as [x231 [x232 H26]].
    generalize (mkCanon_rewrite x31);intro H34;
    destruct H34 as [x311 [x312 H34]].
    generalize (mkCanon_rewrite x32);intro H35;
    destruct H35 as [x321 [x322 H35]].
    generalize (mkCanon_rewrite x33);intro H36;
    destruct H36 as [x331 [x332 H36]].
    rewrite H14 in H11.
    rewrite H15 in H12.
    rewrite H16 in H13.
    rewrite H24 in H21.
    rewrite H25 in H22.
    rewrite H26 in H23.
    rewrite H34 in H31.
    rewrite H35 in H32.
    rewrite H36 in H33.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c11 H11);intro H111.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c12 H12);intro H121.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c13 H13);intro H131.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c21 H21);intro H211.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c22 H22);intro H221.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c23 H23);intro H231.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c31 H31);intro H311.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c32 H32);intro H321.
    generalize (canonTree_proof_irr _ _ (mkCanon_correct _) c33 H33);intro H331.
    rewrite<-H111 in *.
    rewrite<-H121 in *.
    rewrite<-H131 in *.
    rewrite<-H211 in *.
    rewrite<-H221 in *.
    rewrite<-H231 in *.
    rewrite<-H311 in *.
    rewrite<-H321 in *.
    rewrite<-H331 in *.

    generalize (tree_avg_split _ _ _ _ _ _ _ H1);intro H6.
    generalize (tree_avg_split _ _ _ _ _ _ _ H2);intro H7.
    generalize (tree_avg_split _ _ _ _ _ _ _ H3);intro H8.
    destruct H6 as [H61 H62].
    destruct H7 as [H71 H72].
    destruct H8 as [H81 H82].
    generalize (mkCanon_join_split _ _ _ _ _ _ H4);intro H9.
    generalize (mkCanon_join_split _ _ _ _ _ _ H5);intro H10.
    destruct H9 as [H91 H92].
    destruct H10 as [H101 H102].
    generalize (IHn _ _ _ _ _ _ _ _ _ H61 H71 H81 H91 H101);intro Hr1.
    generalize (IHn _ _ _ _ _ _ _ _ _ H62 H72 H82 H92 H102);intro Hr2.
    apply mkCanon_join_combine;trivial.
  Qed.

  Lemma tree_avg_increase : forall n t1 t2,
   t1 <> t2 -> max (height t1) (height t2) < n ->
   exists t3, avg n t1 t2 = Some t3 /\ height t3 = n.
  Proof.
   simpl.
   induction n;intros.
   inv H0.

   unfold tree_height in H0.
   icase n.
   destruct t1 as [x1 c1];
   destruct t2 as [x2 c2].
   simpl in H0.
   assert (max (tree_heightP x1) (tree_heightP x2) = 0) by omega.
   generalize (le_max_l (tree_heightP x1) (tree_heightP x2));intro H2.
   generalize (le_max_r (tree_heightP x1) (tree_heightP x2));intro H3.
   assert (tree_heightP x1 = 0) by omega.
   assert (tree_heightP x2 = 0) by omega.
   icase x1;icase x2.
   simpl.
   assert (b<> b0).
   intro;apply H.
   rewrite H6;apply exist_ext;trivial.
   icase b;icase b0;simpl.
   try (elimtype False; tauto). (*useless in Coq.8.6 but required in Coq.8.6 *)
   exists (exist (fun t0 : ShareTree => canonicalTree t0)
          (Node (Leaf true) (Leaf false))
          (mkCanon_correct (Node (Leaf true) (Leaf false)))).
   split;trivial.
   exists (exist (fun t0 : ShareTree => canonicalTree t0)
          (Node (Leaf false) (Leaf true))
          (mkCanon_correct (Node (Leaf false) (Leaf true)))).
   split;trivial.
   try (elimtype False; tauto). (*useless in Coq.8.6 but required in Coq.8.6 *)
   inv H5;inv H4;elimtype False;omega.
   inv H5;inv H4;elimtype False;omega.
   inv H5;inv H4;elimtype False;omega.

   generalize (canonTree_rewrite1 t1);intro H3.
   generalize (canonTree_rewrite1 t2);intro H4.
   destruct H3 as [t11 [t12 H3]].
   destruct H4 as [t21 [t22 H4]].
   rewrite H3,H4 in *.
   generalize (mkCanon_height_split _ _ _ _ _ H0);intro H5.
   destruct H5 as [H5 H6].
   assert (mkCanon (Node t11 t12) <> mkCanon (Node t21 t22)).
     intro;apply H.
     apply exist_ext;trivial.
   generalize (mkCanon_diff _ _ _ _ H1);intro H7.

   generalize (shareTree_dec_eq (mkCanon t11) (mkCanon t21));intro H8.
   destruct H8.

   assert (mkCanon t12 <> mkCanon t22).
     destruct H7.
     tauto.
     trivial.
   assert (tree_heightP (mkCanon t11) < S n).
     generalize (le_max_l (tree_heightP (mkCanon t11)) (tree_heightP (mkCanon t21)));intro.
     omega.
   generalize (tree_avg_identity (S n)
              (exist (fun t => canonicalTree t) (mkCanon t11) (mkCanon_correct _)) H8);
   intro H9.
   assert (exist (fun t => canonicalTree t) (mkCanon t12) (mkCanon_correct _) <>
           exist (fun t => canonicalTree t) (mkCanon t22) (mkCanon_correct _)).
     intro H10;apply H2;inv H10;trivial.
   generalize (IHn _ _ H10 H6);intro H11.
   destruct H11 as [ t3 [H11 H12]].
   generalize (canonTree_rewrite2 t3);intro H13.
   rewrite H13 in H11.
   assert ((exist (fun t : ShareTree => canonicalTree t) (mkCanon t11) (mkCanon_correct t11)) =
           (exist (fun t : ShareTree => canonicalTree t) (mkCanon t21) (mkCanon_correct t21))).
     apply canonTree_proof_irr.
     trivial.
   rewrite H14 in H9 at 2.
   generalize (tree_avg_combine _ _ _ _ _ _ _ H9 H11);intro H15.
   unfold avg, avgable_tree in H15.
   rewrite H15.
   exists (exist (fun t4 : ShareTree => canonicalTree t4)
          (mkCanon (Node t11 (proj1_sig t3)))
          (mkCanon_correct (Node t11 (proj1_sig t3)))).
   split;trivial.
   destruct t3 as [x3 c3].
   unfold proj1_sig in *.
   assert (mkCanon (Node t11 x3) = Node (mkCanon t11) x3).
      clear - c3 H12.
      unfold tree_height in H12;simpl in H12.
      simpl.
      generalize (mkCanon_identity _ c3);intro.
      rewrite H.
      icase (mkCanon t11).
      icase x3.
   clear -H8 H12 H16.
   unfold tree_height,proj1_sig in *.
   rewrite H16.
   simpl.
   replace (max (tree_heightP (mkCanon t11)) (tree_heightP x3) + 1) with
   (S (max (tree_heightP (mkCanon t11)) (tree_heightP x3))) by omega.
   f_equal.
   assert (tree_heightP (mkCanon t11) <= tree_heightP x3 ) by omega.
   rewrite<- H12.
   apply max_r;trivial.

   generalize (shareTree_dec_eq (mkCanon t12) (mkCanon t22));intro H8.
   unfold proj1_sig in *.
   destruct H8.
   assert (exist (fun t => canonicalTree t) (mkCanon t11) (mkCanon_correct _) <>
           exist (fun t => canonicalTree t) (mkCanon t21) (mkCanon_correct _)).
     intro H8;apply n0;inv H8;trivial.
   generalize (IHn _ _ H2 H5);intro H8.
   destruct H8 as [t3 [H8 H9]].
   rewrite e in H6.
   assert (tree_heightP (mkCanon t22) < S n).
     generalize (le_max_r (tree_heightP (mkCanon t22))
                          (tree_heightP (mkCanon t22)));intro.
     omega.
   generalize (tree_avg_identity (S n) (exist (fun t => canonicalTree t)
              (mkCanon t22) (mkCanon_correct _)) H10);intro H11.
   assert (exist (fun t : ShareTree => canonicalTree t) (mkCanon t12) (mkCanon_correct t12) =
           exist (fun t : ShareTree => canonicalTree t) (mkCanon t22) (mkCanon_correct t22)).
     apply canonTree_proof_irr;trivial.
   rewrite<- H12 in H11 at 1.
   generalize (canonTree_rewrite2 t3);intro H13.
   rewrite H13 in H8.
   generalize (tree_avg_combine _ _ _ _ _ _ _ H8 H11);intro H14.
   unfold avg,avgable_tree in H14.
   rewrite H14.
   exists (exist (fun t4 : ShareTree => canonicalTree t4)
          (mkCanon (Node (proj1_sig t3) t22))
          (mkCanon_correct (Node (proj1_sig t3) t22))).
   split;trivial.
   destruct t3 as [x3 c3].
   unfold tree_height,proj1_sig in *.
   clear - H9 H10 c3.
   assert (mkCanon (Node x3 t22) = Node x3 (mkCanon t22)).
   simpl.
   generalize (mkCanon_identity _ c3);intro H.
   rewrite H.
   icase x3.
   rewrite H.
   simpl.
   assert (max (tree_heightP x3) (tree_heightP (mkCanon t22)) + 1 =
           S (max (tree_heightP x3) (tree_heightP (mkCanon t22)))) by omega.
   rewrite H0;f_equal.
   rewrite<- H9 in *.
   assert (tree_heightP (mkCanon t22) <= tree_heightP x3) by omega.
   apply max_l;trivial.

   assert (exist (fun t => canonicalTree t) (mkCanon t11) (mkCanon_correct _) <>
           exist (fun t => canonicalTree t) (mkCanon t21) (mkCanon_correct _)).
    intro H8;apply n0;inv H8;trivial.
   assert (exist (fun t => canonicalTree t) (mkCanon t12) (mkCanon_correct _) <>
           exist (fun t => canonicalTree t) (mkCanon t22) (mkCanon_correct _)).
    intro H8;apply n1;inv H8;trivial.
   generalize (IHn _ _ H2 H5);intro H9.
   destruct H9 as [t3 [H9 H10]].
   generalize (IHn _ _ H8 H6);intro H11.
   destruct H11 as [t4 [H11 H12]].
   generalize (canonTree_rewrite2 t3);intro H13.
   generalize (canonTree_rewrite2 t4);intro H14.
   rewrite H13 in H9.
   rewrite H14 in H11.
   generalize (tree_avg_combine _ _ _ _ _ _ _ H9 H11);intro H15.
   unfold avg,avgable_tree in H15.
   rewrite H15.
   exists (exist (fun t5 : ShareTree => canonicalTree t5)
          (mkCanon (Node (proj1_sig t3) (proj1_sig t4)))
          (mkCanon_correct (Node (proj1_sig t3) (proj1_sig t4)))).
   split;trivial.
   destruct t3 as [x3 c3];
   destruct t4 as [x4 c4].
   unfold tree_height,proj1_sig in *.
   clear -c3 c4 H10 H12.
   simpl.
   generalize (mkCanon_identity _ c3);intro H1.
   generalize (mkCanon_identity _ c4);intro H2.
   rewrite H1,H2.
   icase x3;icase x4.
   simpl in *;clear -H10 H12.
   rewrite H10,H12.
   generalize (max_idempotent (S n));intro H.
   rewrite H.
   omega.
  Qed.

  (*L34*)
  Lemma tree_avg_ex: forall n t1 t2,
   height t1 < n ->
   height t2 < n ->
   exists t3, avg n t1 t2 = Some t3.
  Proof.
   simpl;intros.
   assert (H1 := eq_dec t1 t2).
   destruct H1 as [H1|H1].
   subst t2.
   exists t1.
   apply tree_avg_identity.
   trivial.
   assert (H2 : max (height t1) (height t2) < n).
    apply Nat.max_lub_lt;trivial.
   assert (H3 := tree_avg_increase _ _ _ H1 H2).
   destruct H3 as [t3 [H3 H4]].
   exists t3.
   trivial.
  Qed.

  (*L35*)
  Lemma avg_share_correct: forall n s,
   (height s <= S n)%nat ->
   exists s', exists s'',
    roundL (S n) s = Some s' /\
    roundR (S n) s = Some s'' /\
    avg (S n) s' s'' = Some s.
  Proof.
   intros.
   copy H.
   apply tree_round_left_Some in H.
   apply tree_round_right_Some in H0.
   destruct H as [t1 H].
   destruct H0 as [t2 H0].
   exists t1.
   exists t2.
   split;trivial.
   split;trivial.
   apply tree_avg_round2avg;trivial.
  Qed.

  (*L5*)
  Lemma decompose_recompose: forall t,
        decompose (recompose t) = t.
  Proof.
    intros.
    destruct t0 as [t1 t2].
    destruct t1 as [x1 c1];
    destruct t2 as [x2 c2].
    icase x1;icase x2;
    simpl.
    icase (bool_dec b b0);
    try subst b0;
    unfold decompose;
    simpl.
    f_equal;
    apply exist_ext;
    trivial.

    destruct (compose_canon1 b b0 n c1 c2) as [? [? [? ?]]];
    f_equal;
    apply exist_ext;
    trivial.

    destruct (compose_canon2 b x2_1 x2_2 c1 c2) as [? [? [? ?]]];
    f_equal;
    apply exist_ext;trivial.

    destruct (compose_canon3 x1_1 x1_2 b c1 c2) as [? [? [? ?]]];
    f_equal;
    apply exist_ext;trivial.

    destruct (compose_canon4 x1_1 x1_2 x2_1 x2_2 c1 c2) as [? [? [? ?]]];
    f_equal;
    apply exist_ext;trivial.
  Qed.
  (*L6*)
  Lemma recompose_decompose: forall t,
        recompose(decompose t) = t.
  Proof.
    intros.
    destruct t0 as [x c].
    icase x.
    simpl.
    icase b.

    simpl in *.
    destruct c as [? [? [? ?]]].
    unfold recompose.
    icase x1;
    icase x2.
    icase (bool_dec b b0);try subst b0;
    simpl;
    apply exist_ext;trivial.
    icase b;elimtype False;firstorder.

    f_equal;
    apply proof_irr.

    f_equal;
    apply proof_irr.

    f_equal;
    apply proof_irr.
 Qed.


 Lemma decompose_rewrite : forall t t1 t2, decompose t = (t1 ,t2)
       <-> t = exist (fun t => canonicalTree t)
              (mkCanon (Node (proj1_sig t1) (proj1_sig t2))) (mkCanon_correct _).
 Proof.
  intros.
  destruct t0 as [x c];
  destruct t1 as [x1 c1];
  destruct t2 as [x2 c2].
  icase x.

  simpl.
  split;intros; inv H;
  generalize (mkCanon_identity _ c1);intro;
  generalize (mkCanon_identity _ c2);intro.
  apply exist_ext.
  rewrite H.
  icase b.

  f_equal;
  apply exist_ext;
  rewrite H in H1;rewrite H0 in H1;
  icase x1;icase x2;
  icase b0;icase b1.

  split;intro;
  try apply exist_ext;
  simpl in H,c;
  destruct c as [? [? [? ?]]];
  inv H;
  simpl;
  generalize (mkCanon_identity _ c1);intro;
  generalize (mkCanon_identity _ c2);intro.
  rewrite H;rewrite H0.
  icase x1;icase x2.
  icase b;icase b0.
  elimtype False;firstorder.
  elimtype False;firstorder.
  f_equal;apply exist_ext;
  rewrite H in H1;rewrite H0 in H1;
  icase x1;icase x2;try icase b;try icase b0;inv H1;auto.
 Qed.
 (*L4*)
 Lemma decompose_height : forall n t1 t2 t3,
  height t1 = S n ->
  decompose t1 = (t2, t3) ->
  height t2 <= n /\ height t3 <= n.
  Proof.
    unfold height;simpl.
    intros.
    destruct t1 as [x1 c1];
    destruct t2 as [x2 c2];
    destruct t3 as [x3 c3].
    icase x1.
    simpl in H0.
    destruct c1 as [? [? [? ?]]].
    inv H0.
    unfold tree_height in *;simpl in *.
    assert (max (tree_heightP x2) (tree_heightP x3) <= n) by omega.
    generalize (max_lub_l _ _ _ H0);intro.
    generalize (max_lub_r _ _ _ H0);intro.
    tauto.
  Qed.
 (*L7*)
 Lemma decompose_join : forall t1 t11 t12 t2 t21 t22 t3 t31 t32,
    decompose t1 = (t11, t12) ->
    decompose t2 = (t21, t22) ->
    decompose t3 = (t31, t32) ->
    (join t1 t2 t3 <->
    (join t11 t21 t31 /\ join t12 t22 t32)).
 Proof.
   intros ? ? ? ? ? ? ? ? ? H1 H2 H3.
   generalize (decompose_rewrite t1 t11 t12);intro H11.
   generalize (decompose_rewrite t2 t21 t22);intro H21.
   generalize (decompose_rewrite t3 t31 t32);intro H31.
   destruct H11 as [H11 _];
   destruct H21 as [H21 _];
   destruct H31 as [H31 _].
   specialize ( H11 H1);
   specialize ( H21 H2);
   specialize ( H31 H3).
   generalize (canonTree_rewrite2 t11);intro H12;
   generalize (canonTree_rewrite2 t12);intro H13;
   generalize (canonTree_rewrite2 t21);intro H22;
   generalize (canonTree_rewrite2 t22);intro H23;
   generalize (canonTree_rewrite2 t31);intro H32;
   generalize (canonTree_rewrite2 t32);intro H33.
   rewrite H12,H13,H22,H23,H32,H33,H11,H21,H31.
   clear.

   split;intro.
   apply mkCanon_join_split;trivial.
   destruct H as [H1 H2].
   apply mkCanon_join_combine;trivial.
  Qed.

  Lemma is_height_zero : forall t, {height t = 0} + {height t <> 0}.
  Proof.
   unfold height;simpl.
   intros.
   destruct t0 as [x c].
   unfold tree_height in *.
   icase x.
   right.
   simpl.
   omega.
  Defined.


(*START THE MEASUREMENT FOR BLACK NODES*)

Fixpoint countBLeafST (n : nat) (s : ShareTree) : nat :=
 match (n,s) with
 | (0,Leaf true) => 1
 | (0,Leaf false) => 0
 | (0, Node s1 s2) => 0
 | (S n', Leaf true) => (countBLeafST n' (Leaf true)) + (countBLeafST n' (Leaf true))
 | (S n', Leaf false) => 0
 | (S n', Node s1 s2) => (countBLeafST n' s1) + (countBLeafST n' s2)
 end.

Definition countBLeafCT (n : nat) (s : canonTree) : nat :=
  countBLeafST n (proj1_sig s).
(*L11*)
Lemma decompose_height_le : forall n s s1 s2,
 decompose s = (s1,s2) ->
 height s <= S n ->
 height s1 <= n /\ height s2 <= n.
Proof.
  unfold height;simpl.
  intros.
  destruct s as [s pf];
  destruct s1 as [s1 pf1];
  destruct s2 as [s2 pf2].
  icase s;
  simpl in H;
  destruct pf;
  inv H;
  unfold tree_height in *;simpl in *.
  omega.
  assert (max (tree_heightP s1) (tree_heightP s2) <= n) by omega.
  generalize (max_lub_l _ _ _ H);intro.
  generalize (max_lub_r _ _ _ H);intro.
  tauto.
Qed.
(*12*)
Lemma decompose_le: forall s1 s2 s11 s12 s21 s22,
 (s1 <= s2)%ba ->
 decompose s1 = (s11,s12) ->
 decompose s2 = (s21,s22) ->
 (s11 <= s21)%ba /\ (s12 <= s22)%ba.
Proof.
 intros.
 destruct s1 as [s1 pf1];
 destruct s2 as [s2 pf2].
 unfold Ord in H;simpl in H.
 icase s1;icase s2;inv H0;inv H1;unfold Ord;
 simpl in pf1,pf2;
 destruct pf1;
 destruct pf2;simpl.
 icase b;icase b0;inv H.
 inversion H;subst.
 inversion H2;subst.
 tauto.
 inversion H;subst.
 inversion H1;subst.
 tauto.
 inversion H;subst.
 tauto.
Qed.
(*L13*)
Lemma decompose_diff: forall s1 s2 s11 s12 s21 s22,
 s1 <> s2 ->
 decompose s1 = (s11,s12) ->
 decompose s2 = (s21,s22) ->
 s11 <> s21 \/ s12 <> s22.
Proof.
 intros.
 assert (H2 := canonTree_eq_dec s11 s21).
 destruct H2 as [H2|H2].
 subst s11.
 assert (H2 := canonTree_eq_dec s12 s22).
 destruct H2 as [H2|H2].
 subst s12.
 elimtype False.
 apply H.
 rewrite<- H1 in H0.
 assert (H2 : recompose (decompose s1) = recompose (decompose s2)).
   f_equal.
   trivial.
 repeat rewrite recompose_decompose in H2.
 trivial.
 right;trivial.
 left;trivial.
Qed.

(*L36*)
Lemma countBLeafCT_decompose : forall n s s1 s2,
 decompose s = (s1,s2) ->
 countBLeafCT (S n) s = countBLeafCT n s1 + countBLeafCT n s2.
Proof.
  destruct s as [s pf].
  icase s;intros.
  simpl in H.
  inv H.
  unfold countBLeafCT;simpl.
  icase b.
  icase n;compute;omega.
  simpl in H.
  simpl in pf.
  destruct pf as [H1 [H2 [H3 H4]]].
  inv H.
  unfold countBLeafCT;simpl.
  trivial.
Qed.

(*L37*)
Lemma countBLeafCT_le : forall n s1 s2,
  (s1 <= s2)%ba -> countBLeafCT n s1 <= countBLeafCT n s2.
Proof.
  induction n;intros.
  destruct s1 as [s1 pf1];
  destruct s2 as [s2 pf2].
  unfold countBLeafCT;simpl.
  icase s1;icase s2;
  try icase b;try icase b0;inv H.
  compute in H2.
  inversion H2.
  inv H2.
  simpl in pf2.
  destruct pf2 as [H6 [H7 [H8 H9]]].
  assert (H10 := top_correct (exist (fun t => canonicalTree t) s2_1 H8)).
  assert (H11 : (top <= exist (fun t => canonicalTree t) s2_1 H8)%ba) by auto.
  assert (H12 := ord_antisym _ _ H10 H11).
  unfold top in H12;inv H12.
  assert (H13 := top_correct (exist (fun t => canonicalTree t) s2_2 H9)).
  assert (H14 : (top <= exist (fun t => canonicalTree t) s2_2 H9)%ba) by auto.
  assert (H15 := ord_antisym _ _ H13 H14).
  unfold top in H15;inv H15.
  destruct H6 as [H6|H6];inv H6.
  (*INDUCTIVE CASE*)
  remember (decompose s1) as ds1;
  remember (decompose s2) as ds2;
  destruct ds1 as [s11 s12];
  destruct ds2 as [s21 s22];
  symmetry in Heqds1, Heqds2.
  apply decompose_le with (s11:=s11) (s12:=s12) (s21:=s21) (s22:=s22) in H;trivial.
  destruct H as [H1 H2].
  assert (H3 := IHn _ _ H1).
  assert (H4 := IHn _ _ H2).
  rewrite countBLeafCT_decompose with (s1:=s11) (s2:=s12);trivial.
  rewrite countBLeafCT_decompose with (s1:=s21) (s2:=s22);trivial.
  omega.
Qed.
(*L38*)
Lemma countBLeafCT_lt : forall n s1 s2,
  (s1 <= s2)%ba ->
   s1 <> s2 ->
   height s2 <= n ->
   countBLeafCT n s1 < countBLeafCT n s2.
Proof.
  unfold height;simpl.
  induction n;intros.
  destruct s1 as [s1 pf1];
  destruct s2 as [s2 pf2];
  unfold countBLeafCT;simpl.
  icase s1.
  icase b.
  elimtype False.
  apply H0.
  apply ord_antisym.
  apply H.
  apply top_correct.
  icase s2.
  icase b.
  elimtype False.
  apply H0.
  f_equal.
  apply proof_irr.
  elimtype False.
  unfold tree_height in H1.
  simpl in H1.
  omega.
  icase s2.
  icase b.
  assert (exist (fun t : ShareTree => canonicalTree t) (Node s1_1 s1_2) pf1 = bot).
    apply ord_antisym.
    apply H.
    apply bot_correct.
  inv H2.
  elimtype False.
  unfold tree_height in H1.
  simpl in H1.
  omega.
  (*INDUCTIVE CASE*)
  remember (decompose s1) as ds1;
  remember (decompose s2) as ds2;
  destruct ds1 as [s11 s12];
  destruct ds2 as [s21 s22];
  symmetry in Heqds1,Heqds2.
  rewrite countBLeafCT_decompose with (s1:=s11) (s2:=s12);trivial.
  rewrite countBLeafCT_decompose with (s1:=s21) (s2:=s22);trivial.
  apply decompose_height_le with (s1:=s21) (s2:=s22) in H1;trivial.
  destruct H1 as [H1 H2].
  apply decompose_le with (s11:=s11) (s12:=s12) (s21:=s21) (s22:=s22) in H;trivial.
  destruct H as [H3 H4].
  apply decompose_diff with (s11:=s11) (s12:=s12) (s21:=s21) (s22:=s22) in H0;trivial.
  destruct H0 as [H0|H0].
  specialize ( IHn s11 s21 H3 H0 H1).
  assert (H5 := countBLeafCT_le n _ _ H4).
  omega.
  specialize ( IHn s12 s22 H4 H0 H2).
  assert (H5 := countBLeafCT_le n _ _ H3).
  omega.
Qed.


Fixpoint power (base : nat) (exp : nat) : nat :=
 match exp with
 | 0 => 1
 | S n => base * (power base n)
 end.

(*L39*)
Lemma countBLeafCT_limit: forall n s, countBLeafCT n s <= power 2 n.
Proof.
 induction n;intros.
 simpl;
 destruct s as [s pf];unfold countBLeafCT;simpl;
 icase s.
 icase b.
 (*INDUCTIVE CASE*)
 remember (decompose s) as ds;
 destruct ds as [s1 s2];
 symmetry in Heqds.
 rewrite countBLeafCT_decompose with (s1:=s1) (s2:=s2);trivial.
 simpl.
 assert (H1 := IHn s1).
 assert (H2 := IHn s2).
 omega.
Qed.

(*L40*)
Lemma countBLeafCT_bot: forall n, countBLeafCT n bot = 0.
Proof.
 induction n.
 assert (H1 := countBLeafCT_lt 0 bot top).
 spec H1.
 apply bot_correct.
 spec H1.
 intro.
 inv H.
 spec H1.
 compute;omega.
 assert (H2 := countBLeafCT_limit 0 top).
 simpl in H2.
 omega.
 assert (decompose bot = (bot,bot)).
  tauto.
 apply countBLeafCT_decompose with (n := n) in H .
 rewrite IHn in H.
 omega.
Qed.

(*L41*)
Lemma countBLeafCT_top: forall n, countBLeafCT n top = power 2 n.
Proof.
 induction n.
 assert (H1 := countBLeafCT_lt 0 bot top).
 spec H1.
 apply bot_correct.
 spec H1.
 intro.
 inv H.
 spec H1.
 compute;omega.
 assert (H2 := countBLeafCT_limit 0 top).
 simpl in H2.
 rewrite countBLeafCT_bot in H1.
 simpl.
 omega.
 assert (H : decompose top = (top,top)) by auto.
 apply countBLeafCT_decompose with (n:=n) in H.
 rewrite IHn in H.
 simpl.
 omega.
Qed.

(*L42*)
Lemma countBLeafCT_positive : forall s n,
 height s <= n -> bot <> s ->
 0 < countBLeafCT n s.
Proof.
 intros.
 replace 0 with (countBLeafCT n bot) by apply countBLeafCT_bot.
 apply countBLeafCT_lt.
 apply bot_correct.
 apply H0.
 apply H.
Qed.

(*L43*)
Lemma countBLeafCT_mono_le: forall n1 n2 s,
 n1 <= n2 ->
 countBLeafCT n1 s <= countBLeafCT n2 s .
Proof.
 induction n1.
 destruct s as [s pf];intros.
 destruct s.
 icase b.
 replace (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf true) pf) with top.
 repeat rewrite countBLeafCT_top.
 simpl.
 induction n2.
 simpl;omega.
 simpl.
 spec IHn2.
 omega.
 omega.
 unfold top.
 f_equal;apply proof_irr.
 icase n2;compute.
 compute;omega.
 (*INDUCTIVE CASE*)
 intros.
 icase n2.
 inv H.
 assert (H1 : n1 <= n2) by omega.
 remember (decompose s) as ds.
 destruct ds as [s1 s2].
 symmetry in Heqds.
 assert (H2 := countBLeafCT_decompose n1 _ _ _ Heqds).
 assert (H3 := countBLeafCT_decompose n2 _ _ _ Heqds).
 assert (H4 := IHn1 n2 s1).
 assert (H5 := IHn1 n2 s2).
 omega.
Qed.

(*L44*)
Lemma countBLeafCT_mono_diff: forall n1 n2 s1 s2,
 n1 <= n2 ->
 (s1 <= s2)%ba ->
 countBLeafCT n1 s2 - countBLeafCT n1 s1 <= countBLeafCT n2 s2 - countBLeafCT n2 s1.
Proof.
 induction n1;intros.
 destruct s1 as [s1 pf1];
 destruct s2 as [s2 pf2].
 icase s1;icase s2.
 icase b;icase b0.
 replace (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf true) pf1) with top.
 replace (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf true) pf2) with top.
 omega.
 unfold top;f_equal;apply proof_irr.
 unfold top;f_equal;apply proof_irr.
 replace (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf false) pf2) with bot.
 repeat rewrite countBLeafCT_bot.
 simpl.
 omega.
 unfold bot;f_equal;apply proof_irr.
 simpl.
 replace (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf true) pf2) with top.
 replace (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf false) pf1) with bot.
 rewrite countBLeafCT_bot.
 rewrite countBLeafCT_top.
 induction n2.
 simpl;omega.
 spec IHn2.
 omega.
 simpl;omega.
 unfold bot;f_equal;apply proof_irr.
 unfold top;f_equal;apply proof_irr.
 simpl.
 omega.
 icase b.
 simpl.
 omega.
 simpl.
 omega.
 icase b.
 simpl.
 replace (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf true) pf2) with top.
 assert (H1 : countBLeafCT n2 (exist (fun t0 : ShareTree => canonicalTree t0) (Node s1_1 s1_2) pf1) < countBLeafCT n2 top).
   apply countBLeafCT_lt.
   apply top_correct.
   intro.
   inv H1.
   compute;omega.
 remember (countBLeafCT n2
       (exist (fun t0 : ShareTree => canonicalTree t0) (Node s1_1 s1_2) pf1)) as n0.
 omega.
 unfold top;f_equal;apply proof_irr.
 simpl.
 omega.
 simpl.
 omega.
 (*INDUCTIVE CASE*)
 icase n2.
 inv H.
 assert (H1 : n1 <= n2).
 omega.
 remember (decompose s1) as ds1.
 destruct ds1 as [s11 s12].
 symmetry in Heqds1.
 remember (decompose s2) as ds2.
 destruct ds2 as [s21 s22].
 symmetry in Heqds2.
 apply decompose_le with (s11:=s11) (s12:=s12) (s21:=s21) (s22:=s22) in H0;trivial.
 destruct H0 as [H2 H3].
 assert (H4 := IHn1 n2 s11 s21 H1 H2).
 assert (H5 := IHn1 n2 s12 s22 H1 H3).
 rewrite countBLeafCT_decompose with (s1:=s21) (s2:=s22);trivial.
 rewrite countBLeafCT_decompose with (s1:=s11) (s2:=s12);trivial.
 rewrite countBLeafCT_decompose with (s1:=s21) (s2:=s22);trivial.
 rewrite countBLeafCT_decompose with (s1:=s11) (s2:=s12);trivial.
 assert (H6 := countBLeafCT_le n2 _ _ H2).
 assert (H7 := countBLeafCT_le n2 _ _ H3).
 omega.
Qed.

(*L45*)
Lemma countBLeafCT_mono_lt: forall n1 n2 s,
 n1 < n2 ->
 0 < countBLeafCT n1 s ->
 countBLeafCT n1 s < countBLeafCT n2 s .
Proof.
 induction n1;intros.
 icase n2.
 inv H.
 destruct s as [s pf].
 icase s.
 icase b.
 replace (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf true) pf) with top.
 repeat rewrite countBLeafCT_top.
 induction n2.
 compute;omega.
 spec IHn2.
 omega.
 simpl in *;omega.
 unfold top;f_equal;apply proof_irr.
 inv H0.
 (*INDUCTIVE CASE*)
 icase n2.
 inv H.
 assert ( H1 : n1 < n2) by omega.
 remember (decompose s) as ds;
 destruct ds as [s1 s2];
 symmetry in Heqds.
 repeat rewrite countBLeafCT_decompose with (s1:=s1)(s2:=s2);trivial.
 assert (H2 : 0 < countBLeafCT n1 s1 \/ 0 < countBLeafCT n1 s2).
  apply countBLeafCT_decompose with (n:=n1) in Heqds.
  omega.
 destruct H2 as [H2|H2].
 specialize ( IHn1 n2 s1 H1 H2).
 assert (H3 : n1 <= n2) by omega.
 apply countBLeafCT_mono_le with (s:=s2) in H3.
 omega.
 specialize ( IHn1 n2 s2 H1 H2).
 assert (H3 : n1 <= n2) by omega.
 apply countBLeafCT_mono_le with (s:=s1) in H3.
 omega.
Qed.

(*Borrow those two lemmas from to_formula*)
 Lemma bot_join: forall t1 t2,
   join bot t1 t2 ->  t1 = t2.
 Proof.
  intros.
  destruct H.
  rewrite lub_commute in H0. rewrite lub_bot in H0. trivial.
 Qed.

 Lemma join_top : forall t1 t2, join top t1 t2 -> t1 = bot /\ t2 = top.
 Proof.
   intros. destruct H.
   rewrite glb_commute, glb_top in H.
   rewrite lub_commute, lub_top in H0. split; auto.
 Qed.

 Lemma tree_height_0: forall s, height s = 0 -> s = top \/ s = bot.
 Proof.
  unfold height;simpl.
  intros.
  destruct s as [s pf].
  icase s.
  icase b.
  left;unfold top;f_equal;apply proof_irr.
  right;unfold bot;f_equal;apply proof_irr.
  unfold tree_height in H.
  simpl in H.
  elimtype False;omega.
 Qed.

 (*L55*)
 Lemma tree_height_glb_limit: forall n s1 s2,
  height s1 <= n ->
  height s2 <= n ->
  height (glb s1 s2) <= n.
Proof.
 unfold height;simpl.
 induction n;intros.
 inv H;inv H0.
 rewrite H2.
 apply tree_height_0 in H1.
 apply tree_height_0 in H2.
 destruct H1;destruct H2;subst;compute;omega.
 destruct s1 as [s1 pf1].
 icase s1.
 icase b.
 rewrite glb_commute.
 replace (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf true) pf1) with top.
 rewrite glb_top.
 trivial.
 unfold top;f_equal;apply proof_irr.
 destruct s2 as [s2 pf2].
 icase s2.
 icase b.
 replace (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf true) pf2) with top.
 rewrite glb_top.
 trivial.
 unfold top;f_equal;apply proof_irr.
 unfold tree_height,glb,proj1_sig.
 simpl in pf1,pf2.
 destruct pf1 as [? [? [? ?]]].
 destruct pf2 as [? [? [? ?]]].
 assert (H1 := IHn (exist (fun t => canonicalTree t) s1_1 c)(exist (fun t => canonicalTree t) s2_1 c1)).
 assert (H2 := IHn (exist (fun t => canonicalTree t) s1_2 c0)(exist (fun t => canonicalTree t) s2_2 c2)).
 unfold tree_height,proj1_sig in *.
 simpl in H,H0,H1,H2.
 spec H1.
 assert (Help := le_max_l (tree_heightP s1_1) (tree_heightP s1_2));clear -H Help;omega.
 spec H1.
 assert (Help := le_max_l (tree_heightP s2_1) (tree_heightP s2_2));clear -H0 Help;omega.
 spec H2.
 assert (Help := le_max_r (tree_heightP s1_1) (tree_heightP s1_2));clear -H Help;omega.
 spec H2.
 assert (Help := le_max_r (tree_heightP s2_1) (tree_heightP s2_2));clear -H0 Help;omega.
 simpl.
 icase (mkCanon (intersect_tree s1_1 s2_1));
 icase (mkCanon (intersect_tree s1_2 s2_2)).
 icase b;icase b0;compute;omega.
 simpl in *;omega.
 simpl in *.
 rewrite max_0_r.
 omega.
 simpl in *.
 assert (H3 := max_lub _ _ _ H1 H2).
 omega.
Qed.

 (*L57*)
 Lemma height_glb1 : forall s1 s2,
  height s1 <= tree_height s2->
  height (glb s1 s2) <= height s2.
 Proof.
  unfold tree_height;simpl.
  intros.
  apply tree_height_glb_limit.
  trivial.
  unfold height;simpl.
  omega.
 Qed.

 (*L54*)
 Lemma tree_height_lub_limit: forall n s1 s2,
  height s1 <= n ->
  height s2 <= n ->
  height (lub s1 s2) <= n.
 Proof.
  unfold height;simpl.
  induction n;intros.
  inv H;inv H0.
  apply tree_height_0 in H1.
  apply tree_height_0 in H2.
  destruct H1;destruct H2;subst;compute;omega.
  destruct s1 as [s1 pf1].
  icase s1.
  icase b.
  replace (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf false) pf1) with bot.
  rewrite lub_commute.
  rewrite lub_bot.
  trivial.
  unfold bot;f_equal;apply proof_irr.
  destruct s2 as [s2 pf2].
  icase s2.
  icase b.
  replace (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf false) pf2) with bot.
  rewrite lub_bot.
  trivial.
  unfold bot;f_equal;apply proof_irr.
  simpl in pf1,pf2.
  destruct pf1 as [? [? [? ?]]].
  destruct pf2 as [? [? [? ?]]].
  assert (H1 := IHn (exist (fun t => canonicalTree t) s1_1 c)(exist (fun t => canonicalTree t) s2_1 c1)).
  assert (H2 := IHn (exist (fun t => canonicalTree t) s1_2 c0)(exist (fun t => canonicalTree t) s2_2 c2)).
  unfold tree_height,proj1_sig in *;simpl in *.
  spec H1.
  assert (Help := le_max_l (tree_heightP s1_1) (tree_heightP s1_2));clear -H Help;omega.
  spec H1.
  assert (Help := le_max_l (tree_heightP s2_1) (tree_heightP s2_2));clear -H0 Help;omega.
  spec H2.
  assert (Help := le_max_r (tree_heightP s1_1) (tree_heightP s1_2));clear -H Help;omega.
  spec H2.
  assert (Help := le_max_r (tree_heightP s2_1) (tree_heightP s2_2));clear -H0 Help;omega.
  icase (mkCanon (union_tree s1_1 s2_1));
  icase (mkCanon (union_tree s1_2 s2_2)).
  icase b;icase b0;compute;omega.
  simpl in *;omega.
  simpl in *.
  rewrite max_0_r.
  omega.
  simpl in *.
  assert (H3 := max_lub _ _ _ H1 H2).
  omega.
 Qed.

 (*L56*)
 Lemma height_lub1 : forall s1 s2,
  height s1 <= height s2->
  height (lub s1 s2) <= height s2.
 Proof.
  unfold height;simpl.
  intros.
  apply tree_height_lub_limit.
  trivial.
  unfold height;simpl.
  omega.
 Qed.
 (*L58*)
 Lemma height_comp: forall s, height (comp s)= height s.
 Proof.
  unfold height;simpl.
  intro s.
  destruct s as [s pf].
  induction s;unfold tree_height;simpl.
  trivial.
  f_equal.
  simpl in pf.
  destruct pf as [? [? [? ?]]].
  specialize ( IHs1 H1).
  specialize ( IHs2 H2).
  unfold tree_height in *;simpl in *.
  congruence.
 Qed.

 (*L46*)
 Lemma countBLeafCT_join_le: forall n s1 s2 s3,
  join s1 s2 s3 ->
  countBLeafCT n s1 + countBLeafCT n s2 <= countBLeafCT n s3.
 Proof.
  induction n;intros.
  destruct s1 as [s1 pf1];
  destruct s2 as [s2 pf2];
  destruct s3 as [s3 pf3].
  icase s1;icase s2;icase s3.
  icase b.
  replace (exist (fun t : ShareTree => canonicalTree t) (Leaf true) pf1) with top in H.
  apply join_top in H.
  destruct H.
  rewrite H;rewrite H0.
  compute.
  omega.
  unfold top;f_equal;apply proof_irr.
  replace (exist (fun t : ShareTree => canonicalTree t) (Leaf false) pf1) with bot in H.
  apply bot_join in H.
  rewrite H.
  simpl.
  omega.
  unfold bot;f_equal;apply proof_irr.
  elimtype False.
  destruct H as [H1 H2].
  assert (tree_height (exist (fun t : ShareTree => canonicalTree t) (Leaf b) pf1) <= 0) by (compute;omega).
  assert (tree_height (exist (fun t : ShareTree => canonicalTree t) (Leaf b0) pf2) <= 0) by (compute;omega).
  assert (H3 := tree_height_lub_limit _ _ _ H H0).
  rewrite H2 in H3.
  clear - H3.
  unfold height in H3;simpl in H3;unfold tree_height,proj1_sig in H3.
  simpl in H3.
  omega.
  unfold countBLeafCT;simpl.
  icase b.
  replace (exist (fun t : ShareTree => canonicalTree t) (Leaf true) pf1) with top in H.
  destruct H.
  rewrite glb_commute in H.
  rewrite glb_top in H.
  inv H.
  unfold top;f_equal;apply proof_irr.
  omega.
  icase b.
  replace (exist (fun t : ShareTree => canonicalTree t) (Leaf true) pf1) with top in H.
  destruct H.
  rewrite glb_commute in H.
  rewrite glb_top in H.
  inv H.
  unfold top;f_equal;apply proof_irr.
  apply join_comm in H.
  icase b.
  replace (exist (fun t : ShareTree => canonicalTree t) (Leaf true) pf2) with top in H.
  destruct H.
  rewrite glb_commute in H.
  rewrite glb_top in H.
  inv H.
  unfold top;f_equal;apply proof_irr.
  replace (exist (fun t : ShareTree => canonicalTree t) (Leaf false) pf2) with bot in H.
  apply bot_join in H.
  rewrite H.
  unfold countBLeafCT,proj1_sig;simpl.
  omega.
  unfold bot;f_equal;apply proof_irr.
  apply join_comm in H.
  icase b.
  replace (exist (fun t : ShareTree => canonicalTree t) (Leaf true) pf2) with top in H.
  destruct H.
  rewrite glb_commute in H.
  rewrite glb_top in H.
  inv H.
  unfold top;f_equal;apply proof_irr.
  compute.
  omega.
  (*INDUCTIVE CASE*)
  remember (decompose s1) as ds1;
  remember (decompose s2) as ds2;
  remember (decompose s3) as ds3;
  destruct ds1 as [s11 s12];
  destruct ds2 as [s21 s22];
  destruct ds3 as [s31 s32];
  symmetry in Heqds1,Heqds2,Heqds3.
  rewrite countBLeafCT_decompose with (s1:=s11) (s2:=s12);trivial.
  rewrite countBLeafCT_decompose with (s1:=s21) (s2:=s22);trivial.
  rewrite countBLeafCT_decompose with (s1:=s31) (s2:=s32);trivial.
  rewrite decompose_join with (t11:=s11) (t12:=s12) (t21:=s21) (t22:=s22) (t31:=s31) (t32:=s32)in H;trivial.
  destruct H as [H1 H2].
  assert (H4 := IHn _ _ _ H1).
  assert (H5 := IHn _ _ _ H2).
  omega.
 Qed.

(*L47*)
Lemma countBLeafCT_join_eq: forall n s1 s2 s3,
 join s1 s2 s3 ->
 height s1 <= n ->
 height s2 <= n ->
 countBLeafCT n s1 + countBLeafCT n s2 = countBLeafCT n s3.
Proof.
 unfold height;simpl.
 induction n;intros.
 inversion H0.
 inversion H1.
 rewrite H3.
 apply tree_height_0 in H3.
 destruct H3 as [H3|H3];subst.
 apply join_top in H.
 destruct H;subst.
 compute;omega.
 apply bot_join in H;subst.
 compute.
 omega.
 (*INDUCTIVE CASE*)
 remember (decompose s1) as ds1;
 remember (decompose s2) as ds2;
 remember (decompose s3) as ds3;
 destruct ds1 as [s11 s12];
 destruct ds2 as [s21 s22];
 destruct ds3 as [s31 s32];
 symmetry in Heqds1,Heqds2,Heqds3.
 apply decompose_height_le with (s1:= s11) (s2:=s12)in H0;trivial.
 apply decompose_height_le with (s1:= s21) (s2:=s22)in H1;trivial.
 destruct H0 as [H2 H3];
 destruct H1 as [H4 H5].
 rewrite countBLeafCT_decompose with (s1:=s11) (s2:=s12);trivial.
 rewrite countBLeafCT_decompose with (s1:=s21) (s2:=s22);trivial.
 rewrite countBLeafCT_decompose with (s1:=s31) (s2:=s32);trivial.
 rewrite decompose_join with (t11:=s11) (t12:=s12) (t21:=s21) (t22:=s22) (t31:=s31) (t32:=s32)in H;trivial.
 destruct H as [H6 H7].
 assert (H8 := IHn _ _ _ H6 H2 H4).
 assert (H9 := IHn _ _ _ H7 H3 H5).
 omega.
Qed.

Definition share_metric (n : nat) (s : canonTree) : nat :=
 match n with
 | 0 => 0
 | S n => match le_dec (height s) n with
          | left _ => countBLeafCT n s + 1
          | right _ => 0
         end
 end.
 (*L48*)
 Lemma share_metric_nerr : forall s n,
  height s < n ->
  0 < share_metric n s.
 Proof.
  intros.
  icase n.
  inv H.
  simpl.
  icase (le_dec (tree_height s) n).
  omega.
  unfold height in H;simpl in H.
  omega.
 Qed.

 (*L49*)
 Lemma share_metric_err  : forall s n,
  n <= height s ->
  share_metric n s = 0.
 Proof.
  intros.
  icase n.
  simpl.
  icase (le_dec (tree_height s) n).
  unfold height in H;simpl in H.
  elimtype False;omega.
 Qed.
 (*L50*)
 Lemma share_metric_height_monotonic : forall s n1 n2,
  n1<=n2 ->
  share_metric n1 s <= share_metric n2 s.
 Proof.
  intros.
  icase n1.
  simpl.
  omega.
  icase n2.
  inv H.
  assert (H1 : n1 <= n2) by omega.
  simpl.
  icase (le_dec (tree_height s) n1);
  icase (le_dec (tree_height s) n2).
  assert (H2 := countBLeafCT_mono_le _ _ s H1).
  omega.
  omega.
  omega.
 Qed.
 (*L51*)
 Lemma share_metric_lub : forall s s' n,
  ~(s'<=s)%ba->
  0 < share_metric n s ->
  0 < share_metric n (lub s s') ->
  (share_metric n s<share_metric n (lub s s')).
 Proof.
  intros.
  icase n.
  simpl.
  icase (le_dec (tree_height s) n);
  icase (le_dec (tree_height (lub s s')) n).
  assert (H2 := lub_upper1 s s').
  assert (H3 : s <> lub s s').
   intro.
   apply H.
   rewrite H3.
   apply lub_upper2.
  assert (H4 := countBLeafCT_lt _ _ _ H2 H3 l0).
  omega.
  simpl in H1.
  revert H1.
  icase (le_dec (tree_height (lub s s')) n);intro.
  inv H1.
 Qed.
 (*L52*)
 Lemma share_metric_glb : forall s s' n,
  ~(s<=s')%ba->
  0 < share_metric n s ->
  0 < share_metric n (glb s s') ->
 (share_metric n (glb s s') < share_metric n s)%nat.
 Proof.
  intros.
  icase n.
  simpl.
  icase (le_dec (tree_height (glb s s')) n);
  icase (le_dec (tree_height s) n).
  assert (H2 := glb_lower1 s s').
  assert (H3 : glb s s' <> s).
   intro H3.
   apply H.
   rewrite<- H3.
   apply glb_lower2.
  assert (H4 := countBLeafCT_lt _ _ _ H2 H3 l0).
  omega.
  simpl in H0.
  revert H0.
  icase (le_dec (tree_height s) n).
  intro.
  inv H0.
 Qed.

 (*L53*)
 Lemma share_metric_dif_monotonic: forall s1 s2 n n0,
 (s1<=s2)%ba -> n<=n0 ->
  height s1 < n ->
  height s2 < n ->
 (share_metric n s2 - share_metric n s1 <=
  share_metric n0 s2 - share_metric n0 s1).
 Proof.
  intros.
  icase n.
  inv H1.
  icase n0.
  inv H0.
  assert (H3 : n <= n0) by omega.
  simpl.
  icase (le_dec (tree_height s1) n);
  icase (le_dec (tree_height s2) n);
  icase (le_dec (tree_height s1) n0);
  icase (le_dec (tree_height s2) n0);
  simpl;try omega.
  assert (H4 := countBLeafCT_mono_diff _ _ _ _ H3 H).
  omega.
  unfold height in *;simpl in *.
  omega.
  unfold height in *;simpl in *.
  omega.
 Qed.

 Lemma shareTreeOrd_dec: forall t1 t2 : ShareTree,
  {shareTreeOrd t1 t2} + {~shareTreeOrd t1 t2}.
 Proof with try tauto.
  induction t1;intros.
  icase b. induction t2.
  icase b. right. repeat intro.
  inv H. inv H2.
  destruct IHt2_1. destruct IHt2_2.
  left. apply LeafNode_Ord;apply Node_Ord...
  right. intro. inv H. inv H2...
  right. intro. inv H. inv H2...
  icase t2. icase b.
  specialize ( IHt1_1 (Leaf false)).
  specialize ( IHt1_2 (Leaf false)).
  destruct IHt1_1. destruct IHt1_2.
  left. apply NodeLeaf_Ord;apply Node_Ord...
  right. intro. inv H. inv H1...
  right. intro. inv H. inv H1...
  specialize ( IHt1_1 t2_1). specialize ( IHt1_2 t2_2).
  destruct IHt1_1. destruct IHt1_2.
  left. apply Node_Ord...
  right. intro. inv H...
  right. intro. inv H...
 Defined.

(*L0*)
 Lemma leq_dec : forall (x y : t), {(x <= y)%ba} + {~ (x <= y)%ba}.
 Proof.
  intros. unfold Ord.
  apply shareTreeOrd_dec.
 Defined.

(*L1*)
 Lemma height_top : height top = 0.
 Proof.
  tauto.
 Qed.
(*L2*)
 Lemma height_bot: height bot = 0.
 Proof.
  tauto.
 Qed.
(*L3*)
 Lemma height_zero_eq: forall t,
  height t = 0 -> {t = top} + {t = bot}.
 Proof.
  intros.
  destruct t0.
  icase x.
  icase b.
  left.
  unfold top.
  f_equal.
  apply proof_irr.
  right.
  unfold bot.
  f_equal.
  apply proof_irr.
  simpl in H.
  unfold tree_height in H.
  simpl in H.
  elimtype False.
  omega.
 Defined.
(*D10*)
 Definition add (x y : canonTree) : option canonTree :=
  match eq_dec (glb x y) bot with
  | left _ => Some (lub x y)
  | right _ => None
  end.
(*L8*)
 Lemma add_join : forall t1 t2 t3,
  add t1 t2 = Some t3 <-> join t1 t2 t3.
 Proof.
  intros.
  unfold add.
  icase (eq_dec (glb t1 t2) bot).
  split;intros.
  split;auto.
  inv H;auto.
  f_equal.
  destruct H;auto.
  split;intros.
  inv H.
  destruct H;tauto.
 Qed.
(*D11*)
 Definition sub (x y : canonTree) : option canonTree :=
  match eq_dec (glb x y) y with
  | left _ => Some (glb x (comp y))
  | right _ => None
  end.
(*L9*)
 Lemma sub_join : forall t1 t2 t3,
  sub t1 t2 = Some t3 <-> join t2 t3 t1.
 Proof.
  intros.
  unfold sub.
  icase (eq_dec (glb t1 t2) t2).
  split;intros.
  inversion H.
  split.
  rewrite glb_commute.
  rewrite glb_assoc.
  replace (glb (comp t2) t2) with (glb t2 (comp t2)) by apply glb_commute.
  rewrite comp2.
  apply glb_bot.
  rewrite distrib2.
  replace (lub (comp t2) t2) with (lub t2 (comp t2)) by apply lub_commute.
  rewrite comp1.
  rewrite glb_top.
  rewrite<- e.
  rewrite lub_commute.
  apply lub_absorb.
  f_equal.
  destruct H.
  rewrite <- H0.
  rewrite glb_commute.
  rewrite distrib1.
  rewrite glb_commute.
  rewrite comp2.
  rewrite lub_commute.
  rewrite lub_bot.
  rewrite glb_commute in H.
  assert (H1 : lub (glb t3 t2) (glb t3 (comp t2)) = glb t3 (comp t2)).
  rewrite H.
  rewrite lub_commute.
  rewrite lub_bot.
  trivial.
  rewrite<- distrib1 in H1.
  rewrite comp1 in H1.
  rewrite glb_top in H1.
  rewrite H1 at 2.
  rewrite glb_commute.
  trivial.
  split;intros.
  inv H.
  destruct H.
  elimtype False;apply n.
  rewrite<- H0.
  rewrite glb_commute.
  rewrite distrib1.
  rewrite H.
  rewrite lub_bot.
  apply glb_idem.
 Qed.
 (*L10*)
 Lemma decompose_share_height_no_increase: forall sh sh' sh'' ,
  decompose sh = (sh',sh'')->
  height sh' <= height sh /\ height sh'' <= height sh.
Proof.
 simpl.
 intros.
 remember (tree_height sh) as n.
 icase n.
 symmetry in Heqn.
 apply height_zero_eq in Heqn.
 icase Heqn;subst;
 inv H;compute;omega.
 symmetry in Heqn.
 assert (H1 := decompose_height _ _ _ _ Heqn H).
 simpl in *.
 omega.
Qed.


Lemma tree_top_rewrite : forall c,
 exist _ (Leaf true) c = top.
Proof.
 intros.
 unfold top. f_equal. apply proof_irr.
Qed.

Lemma tree_bot_rewrite : forall c,
 exist _ (Leaf false) c = bot.
Proof.
 intros.
 unfold bot.
 f_equal. apply proof_irr.
Qed.

Lemma tree_basic_rewrite : forall b c,
exist _ (Leaf b) c = top \/ exist _ (Leaf b) c = bot.
Proof.
 intros. icase b.
 left;apply tree_top_rewrite.
 right;apply tree_bot_rewrite.
Qed.

Lemma tree_case_rewrite : forall t,
(t = top \/ t = bot) \/ exists t1 t2 c, t = exist _ (Node t1 t2) c.
Proof.
 intros.
 destruct t0.
 destruct x. left;apply tree_basic_rewrite.
 right. exists x1. exists x2. exists c.
 trivial.
Qed.

Lemma decompose_basic: forall b c c1 c2,
 decompose (exist _ (Leaf b) c) = (exist _ (Leaf b) c1,exist _ (Leaf b) c2).
Proof.
 intros.
 unfold decompose,decompose_tree.
 simpl. f_equal. f_equal. apply proof_irr.
 f_equal. apply proof_irr.
Qed.

Lemma decompose_top: decompose top = (top,top).
Proof.
 apply decompose_basic.
Qed.

Lemma decompose_bot: decompose bot = (bot,bot).
Proof.
 apply decompose_basic.
Qed.

Lemma decompose_Node: forall t1 t2 c c1 c2,
 decompose (exist _ (Node t1 t2) c) = (exist _ t1 c1, exist _ t2 c2).
Proof.
 intros.
 unfold decompose. unfold decompose_tree.
 unfold tree_decompose.
 destruct c as [? [? [? ?]]].
 f_equal. f_equal. apply proof_irr.
 f_equal. apply proof_irr.
Qed.

Lemma identity_bot: forall s, identity s <-> s = bot.
Proof.
 repeat intro. split;intros.
 specialize ( H bot s).
 symmetry. apply H.
 split. apply glb_bot.
 apply lub_bot.
 subst. repeat intro. destruct H.
 rewrite lub_commute in H0.
 rewrite lub_bot in H0. trivial.
Qed.

Lemma tree_proof_replace: forall (t : ShareTree) c1 c2,
 exist (fun t => canonicalTree t) t c1 = exist _ t c2.
Proof.
 intros. f_equal. apply proof_irr.
Qed.

Lemma top_unrel: forall a,
 unrel top a = a.
Proof.
 intros.
 rewrite unrel_equation.
 unfold top. trivial.
Qed.

Lemma bot_unrel: forall a,
 unrel bot a = a.
Proof.
 intros.
 rewrite unrel_equation.
 unfold bot. trivial.
Qed.

  Lemma mkCanon_lub : forall t11 t12 t21 t22 t31 t32,
                     lub (exist _ (mkCanon (Node t11 t12)) (mkCanon_correct _))
                         (exist _ (mkCanon (Node t21 t22)) (mkCanon_correct _)) =
                         (exist _ (mkCanon (Node t31 t32)) (mkCanon_correct _))<->
                     lub (exist _ (mkCanon t11) (mkCanon_correct _))
                         (exist _ (mkCanon t21) (mkCanon_correct _)) =
                         (exist _ (mkCanon t31) (mkCanon_correct _))/\
                     lub (exist _ (mkCanon t12) (mkCanon_correct _))
                         (exist _ (mkCanon t22) (mkCanon_correct _)) =
                         (exist _ (mkCanon t32) (mkCanon_correct _)).
  Proof.
    intros.
    unfold BAF.lub.
    split;intros.
    simpl. inversion H.
    generalize (mkCanon_union((Node t11 t12)) ((Node t21 t22)));intro.
    inversion H0. rewrite H1 in H3.
    generalize (mkCanon_eq_split _ _ _ _ H3);intro.
    destruct H2 as [? ?].
    split;apply exist_ext;rewrite mkCanon_union;congruence.

    apply exist_ext.
    destruct H. inversion H. inversion H0.
    generalize (mkCanon_union (Node t11 t12) (Node t21 t22));intro.
    rewrite mkCanon_union in H2.
    rewrite mkCanon_union in H3. simpl.
    simpl in H1;rewrite H1.
    rewrite H2. rewrite H3.
    trivial.
  Qed.

  Lemma mkCanon_glb : forall t11 t12 t21 t22 t31 t32,
                     glb (exist _ (mkCanon (Node t11 t12)) (mkCanon_correct _))
                         (exist _ (mkCanon (Node t21 t22)) (mkCanon_correct _)) =
                         (exist _ (mkCanon (Node t31 t32)) (mkCanon_correct _))<->
                     glb (exist _ (mkCanon t11) (mkCanon_correct _))
                         (exist _ (mkCanon t21) (mkCanon_correct _)) =
                         (exist _ (mkCanon t31) (mkCanon_correct _))/\
                     glb (exist _ (mkCanon t12) (mkCanon_correct _))
                         (exist _ (mkCanon t22) (mkCanon_correct _)) =
                         (exist _ (mkCanon t32) (mkCanon_correct _)).
  Proof.
    intros.
    unfold BAF.lub.
    split;intros.
    simpl. inversion H.
    generalize (mkCanon_intersect((Node t11 t12)) ((Node t21 t22)));intro.
    inversion H0. rewrite H1 in H3.
    generalize (mkCanon_eq_split _ _ _ _ H3);intro.
    destruct H2 as [? ?].
    split;apply exist_ext; simpl; rewrite mkCanon_intersect;congruence.

    apply exist_ext.
    destruct H. inversion H. inversion H0.
    generalize (mkCanon_intersect (Node t11 t12) (Node t21 t22));intro.
    rewrite mkCanon_intersect in H2.
    rewrite mkCanon_intersect in H3. simpl.
    simpl in H1;rewrite H1.
    rewrite H2. rewrite H3.
    trivial.
  Qed.


Lemma decompose_lub: forall t1 t11 t12 t2 t21 t22 t3 t31 t32,
 decompose t1 = (t11,t12) ->
 decompose t2 = (t21,t22) ->
 decompose t3 = (t31,t32) ->
 (lub t1 t2 = t3 <-> (lub t11 t21 = t31 /\ lub t12 t22 = t32)).
Proof.
   intros ? ? ? ? ? ? ? ? ? H1 H2 H3.
   generalize (decompose_rewrite t1 t11 t12);intro H11.
   generalize (decompose_rewrite t2 t21 t22);intro H21.
   generalize (decompose_rewrite t3 t31 t32);intro H31.
   destruct H11 as [H11 _];
   destruct H21 as [H21 _];
   destruct H31 as [H31 _].
   specialize ( H11 H1);
   specialize ( H21 H2);
   specialize ( H31 H3).
   generalize (canonTree_rewrite2 t11);intro H12;
   generalize (canonTree_rewrite2 t12);intro H13;
   generalize (canonTree_rewrite2 t21);intro H22;
   generalize (canonTree_rewrite2 t22);intro H23;
   generalize (canonTree_rewrite2 t31);intro H32;
   generalize (canonTree_rewrite2 t32);intro H33.
   rewrite H12,H13,H22,H23,H32,H33,H11,H21,H31.
   apply mkCanon_lub.
Qed.

Lemma decompose_glb: forall t1 t11 t12 t2 t21 t22 t3 t31 t32,
 decompose t1 = (t11,t12) ->
 decompose t2 = (t21,t22) ->
 decompose t3 = (t31,t32) ->
 (glb t1 t2 = t3 <-> (glb t11 t21 = t31 /\ glb t12 t22 = t32)).
Proof.
   intros ? ? ? ? ? ? ? ? ? H1 H2 H3.
   generalize (decompose_rewrite t1 t11 t12);intro H11.
   generalize (decompose_rewrite t2 t21 t22);intro H21.
   generalize (decompose_rewrite t3 t31 t32);intro H31.
   destruct H11 as [H11 _];
   destruct H21 as [H21 _];
   destruct H31 as [H31 _].
   specialize ( H11 H1);
   specialize ( H21 H2);
   specialize ( H31 H3).
   generalize (canonTree_rewrite2 t11);intro H12;
   generalize (canonTree_rewrite2 t12);intro H13;
   generalize (canonTree_rewrite2 t21);intro H22;
   generalize (canonTree_rewrite2 t22);intro H23;
   generalize (canonTree_rewrite2 t31);intro H32;
   generalize (canonTree_rewrite2 t32);intro H33.
   rewrite H12,H13,H22,H23,H32,H33,H11,H21,H31.
   apply mkCanon_glb.
Qed.

Lemma unrel_right_obmit: forall a a1 a2 t1 t2 c c1,
 t1 <> Leaf false ->
 decompose a = (a1,a2) ->
 unrel (exist _ (Node t1 t2) c) a = unrel (exist _ t1 c1) a1.
Proof.
 intros.
 rewrite unrel_equation.
 simpl. destruct c as [? [? [? ?]]].
 replace (tree_decompose a) with (decompose a) by trivial.
 rewrite H0.
 icase t1. icase b. try tauto.
 repeat f_equal. apply proof_irr.
Qed.

Lemma unrel_left_obmit: forall a a1 a2 t c c',
 decompose a = (a1,a2) ->
 unrel (exist _ (Node (Leaf false) t) c) a =
 unrel (exist _ t c') a2.
Proof.
 intros.
 rewrite unrel_equation.
 simpl. destruct c as [? [? [? ?]]].
 replace (tree_decompose a) with (decompose a) by trivial.
 rewrite H.
 repeat f_equal.
 apply proof_irr.
Qed.

Lemma unrel_lub: forall a b1 b2,
 unrel a (lub b1 b2) = lub (unrel a b1) (unrel a b2).
Proof.
 intro a.
 destruct a.
 induction x;intros;rewrite unrel_equation.
 generalize (tree_basic_rewrite b c);intro.
 destruct H;rewrite H.
 repeat rewrite top_unrel. trivial.
 repeat rewrite bot_unrel. trivial.
 destruct c as [? [? [? ?]]].
 rewrite decompose_Node with (c1:=c) (c2:=c0).
 remember (lub b1 b2) as b3.
 symmetry in Heqb3.
 remember (decompose b1); remember (decompose b2);remember (decompose b3).
 destruct p; destruct p0; destruct p1.
 symmetry in Heqp,Heqp0,Heqp1.
 eapply decompose_lub in Heqb3.
 2: apply Heqp.
 2: apply Heqp0.
 2: apply Heqp1.
 destruct Heqb3;subst.
 icase x1. icase b.
 rewrite unrel_right_obmit with (c1:=c)(a1:=t0)(a2:=t1);trivial.
 rewrite unrel_right_obmit with (c1:=c) (a1:=t2) (a2:=t3);trivial.
 intro. inversion H. intro. inversion H.
 rewrite unrel_left_obmit with (c':=c0)(a1:=t0)(a2:=t1);trivial.
 rewrite unrel_left_obmit with (c':=c0)(a1:=t2)(a2:=t3);trivial.
 rewrite unrel_right_obmit with (c1:=c) (a1:=t0) (a2:=t1);trivial.
 rewrite unrel_right_obmit with (c1:=c) (a1:=t2) (a2:=t3);trivial.
 intro. inversion H.
 intro. inversion H.
Qed.

Lemma unrel_glb: forall a b1 b2,
 unrel a (glb b1 b2) = glb (unrel a b1) (unrel a b2).
Proof.
 intro a.
 destruct a.
 induction x;intros;rewrite unrel_equation.
 generalize (tree_basic_rewrite b c);intro.
 destruct H;rewrite H.
 repeat rewrite top_unrel. trivial.
 repeat rewrite bot_unrel. trivial.
 destruct c as [? [? [? ?]]].
 rewrite decompose_Node with (c1:=c) (c2:=c0).
 remember (glb b1 b2) as b3.
 symmetry in Heqb3.
 remember (decompose b1); remember (decompose b2);remember (decompose b3).
 destruct p; destruct p0; destruct p1.
 symmetry in Heqp,Heqp0,Heqp1.
 eapply decompose_glb in Heqb3.
 2: apply Heqp.
 2: apply Heqp0.
 2: apply Heqp1.
 destruct Heqb3;subst.
 icase x1. icase b.
 rewrite unrel_right_obmit with (c1:=c)(a1:=t0)(a2:=t1);trivial.
 rewrite unrel_right_obmit with (c1:=c) (a1:=t2) (a2:=t3);trivial.
 intro. inversion H. intro. inversion H.
 rewrite unrel_left_obmit with (c':=c0)(a1:=t0)(a2:=t1);trivial.
 rewrite unrel_left_obmit with (c':=c0)(a1:=t2)(a2:=t3);trivial.
 rewrite unrel_right_obmit with (c1:=c) (a1:=t0) (a2:=t1);trivial.
 rewrite unrel_right_obmit with (c1:=c) (a1:=t2) (a2:=t3);trivial.
 intro. inversion H.
 intro. inversion H.
Qed.

Lemma unrel_bot: forall a,
 unrel a bot = bot.
Proof.
 intros.
 destruct a. induction x. trivial.
 destruct c as [? [? [? ?]]].
 rewrite unrel_equation.
 rewrite decompose_Node with (c1:=c) (c2:=c0).
 rewrite decompose_bot.
 icase x1. icase b.
Qed.

Lemma unrel_top: forall a,
 unrel a top = top.
Proof.
 intros.
 destruct a. induction x. trivial.
 destruct c as [? [? [? ?]]].
 rewrite unrel_equation.
 rewrite decompose_Node with (c1:=c) (c2:=c0).
 rewrite decompose_top.
 icase x1. icase b.
Qed.

Lemma unrel_join: forall x a b c,
 join a b c ->
 join (unrel x a) (unrel x b) (unrel x c).
Proof.
 intros.
 destruct H.
 split. rewrite<- unrel_glb.
 rewrite H. apply unrel_bot.
 rewrite<- unrel_lub. f_equal. trivial.
Qed.

Lemma unrel_disjoint: forall a a',
 a <> bot ->
 glb a a' = bot ->
 unrel a a' = bot.
Proof.
 intro a.
 destruct a. induction x;intros.
 icase b. rewrite tree_top_rewrite in *.
 rewrite glb_commute in H0.
 rewrite glb_top in H0. subst.
 apply top_unrel.
 rewrite tree_bot_rewrite in *. tauto.

 rewrite unrel_equation.
 destruct c as [? [? [? ?]]].
 rewrite decompose_Node with (c1:=c)(c2:=c0).
 remember (decompose a').
 icase p. symmetry in Heqp.
 generalize (decompose_Node x1 x2 (conj n (conj n0 (conj c c0))) c c0);intro.
 generalize decompose_bot;intro.
 generalize (decompose_glb _ _ _ _ _ _ _ _ _ H1 Heqp H2);intro.
 rewrite H3 in H0.
 destruct H0.
 icase x1. icase b.
 rewrite tree_top_rewrite in H0.
 rewrite glb_commute in H0.
 rewrite glb_top in H0. trivial.
 apply IHx2;trivial.
 destruct n0. inversion n0.
 icase x2. icase b.
 apply IHx1;trivial.
 intro.
 inversion H5.
Qed.

Lemma decompose_height_zero: forall s sL sR,
  decompose s = (sL,sR) ->
  height s = 0 ->
  sL = s /\ sR = s.
Proof with try tauto.
 intros.
 apply height_zero_eq in H0.
 destruct H0;subst.
 rewrite decompose_top in H. inv H...
 rewrite decompose_bot in H. inv H...
Qed.

Lemma decompose_equal: forall a b aL aR bL bR,
 decompose a = (aL,aR) ->
 decompose b = (bL,bR) ->
 (a = b <-> aL = bL /\ aR = bR).
Proof with auto.
  intros.
  assert (forall x y, x = y <-> join bot x y).
   intros;split;intro. subst.
   split.
   rewrite glb_commute.
   apply glb_bot.
   rewrite lub_commute.
   apply lub_bot.
   apply bot_join...
  repeat rewrite H1.
  generalize (decompose_bot);intro.
  apply decompose_join...
Qed.

Lemma decompose_nonzero: forall sL sR s,
 decompose s = (sL,sR) ->
 (s <> bot <-> sL <> bot \/ sR <> bot).
Proof.
  intros.
  destruct s.
  icase x.
  rewrite decompose_basic  with (c1:=c) (c2:=c)in H.
  inv H. icase b;tauto.
  destruct c as [? [? [? ?]]].
  rewrite decompose_Node with (c1 :=c) (c2:=c0)in H.
  inv H.
  split;intros.
  destruct n0.
  left. repeat intro. inv H0. inv n0.
  right. repeat intro. inv H0. inv n0.
  intro. inv H0.
Qed.

Lemma tree_avg_equal: forall sL sR sL' sR' s n,
 avg n sL sR = Some s ->
 avg n sL' sR' = Some s ->
 sL = sL' /\ sR = sR'.
Proof.
 intros.
 apply tree_avg_avg2round in H.
 apply tree_avg_avg2round in H0.
 destruct H. destruct H0.
 split;congruence.
Qed.

Lemma tree_avg_bot: forall n,
 avg (S n) bot bot = Some bot.
Proof.
 intros.
 apply tree_avg_identity.
 compute. omega.
Qed.

Lemma tree_avg_zero: forall sL sR s n,
  avg n sL sR = Some s ->
  (s = bot <-> sL = bot /\ sR = bot).
Proof with try tauto.
 intros.
 icase n.
 split;intros.
 subst s.
 apply tree_avg_equal with bot (S n)...
 apply tree_avg_bot.
 destruct H0;subst.
 rewrite tree_avg_bot in H. inv H...
Qed.

Lemma tree_avg_nonzero: forall sL sR s n,
  avg n sL sR = Some s ->
  (s <> bot <-> sL <> bot \/ sR <> bot).
Proof with try tauto.
  intros.
  split;repeat intro. icase n.
  destruct (eq_dec sL bot)... subst.
  destruct (eq_dec sR bot)... subst.
  apply tree_avg_zero in H...
  apply tree_avg_zero in H...
Qed.

Lemma tree_avg_bound: forall sL sR s n,
  avg n sL sR = Some s -> (height s <= n)%nat.
Proof with try tauto;try omega.
  intros. icase n.
  apply tree_avg_avg2round in H.
  destruct H.
  destruct (le_dec (height s) (S n))...
  rewrite tree_round_left_None in H...
  inv H.
Qed.

Lemma Lsh_recompose: Lsh = recompose (top, bot).
Proof.
 compute;f_equal.
 apply proof_irr.
Qed.

Lemma Rsh_recompose: Rsh = recompose (bot,top).
Proof.
 compute;f_equal.
 apply proof_irr.
Qed.

Lemma decompose_Rsh: forall sh,
 unrel Rsh sh = snd (decompose sh).
Proof.
 intros. unfold Rsh. simpl.
 rewrite unrel_equation.
 unfold rel;simpl.
 destruct (tree_decompose sh);simpl.
 rewrite unrel_equation. trivial.
Qed.

Lemma decompose_Lsh: forall sh,
 unrel Lsh sh = fst (decompose sh).
Proof.
 intros. unfold Lsh. simpl.
 rewrite unrel_equation.
 unfold rel;simpl.
 destruct (tree_decompose sh);simpl.
 auto.
Qed.

Lemma rel_Lsh: forall sh,
rel Lsh sh = recompose (sh,bot).
Proof.
 intros. destruct sh.
 unfold Lsh. simpl.
 rewrite rel_top2.
 icase x;simpl.
 icase b;simpl.
 compute. f_equal. apply proof_irr.
 compute. f_equal. apply proof_irr.
 compute. f_equal. apply proof_irr.
Qed.

Lemma rel_Rsh: forall sh,
rel Rsh sh = recompose (bot,sh).
 intros. destruct sh.
 unfold Rsh. simpl.
 rewrite rel_top2.
 icase x;simpl.
 icase b;simpl.
 compute. f_equal. apply proof_irr.
 compute. f_equal. apply proof_irr.
Qed.

Lemma lub_rel_recompose: forall sh1 sh2,
lub (rel Lsh sh1) (rel Rsh sh2) = recompose (sh1,sh2).
Proof.
 intros.
 rewrite rel_Lsh, rel_Rsh.
 erewrite decompose_lub;eauto.
 rewrite decompose_recompose. f_equal.
 rewrite decompose_recompose. f_equal.
 rewrite decompose_recompose.
 rewrite lub_bot.
 rewrite lub_commute.
 rewrite lub_bot;trivial.
Qed.

End Share.


