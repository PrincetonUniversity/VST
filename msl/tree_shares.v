(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require Import msl.eq_dec.
Require Import msl.sepalg.
Require Import msl.boolean_alg.
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

Module Share : SHARE_MODEL.
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
  Qed.

  Lemma nonFull_dec : forall x, {nonFullTree x}+{~nonFullTree x}.
  Proof.
    induction x; simpl; intros; invert_ord; destruct_bool; intuition.
  Qed.

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

  Inductive ctx : Set :=
  | NodeB : ctx -> ctx -> ctx
  | NodeR : ShareTree -> ctx -> ctx
  | NodeL : ctx -> ShareTree -> ctx
  | Hole : ctx
  .

  Fixpoint ctx_app (c1 c2:ctx) {struct c1} : ctx :=
  match c1 with
  | NodeB l r => NodeB (ctx_app l c2) (ctx_app r c2)
  | NodeR l r => NodeR l (ctx_app r c2)
  | NodeL l r => NodeL (ctx_app l c2) r
  | Hole      => c2
  end.

  Fixpoint fill (c:ctx) (x:ShareTree) {struct c} : ShareTree := 
  match c with
  | NodeR l r => Node l (fill r x)
  | NodeL l r => Node (fill l x) r
  | NodeB l r => Node (fill l x) (fill r x)
  | Hole      => x
  end.

  Lemma fill_app : forall c1 c2 x,
    fill c1 (fill c2 x) = fill (ctx_app c1 c2) x.
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
      with (fill (ctx_app c1 (NodeL Hole x2)) x1) in H1.
    generalize (IHx1 _ H1).
    destruct c1; simpl; intros; discriminate.
    rewrite <- fill_app; simpl; auto.
    inversion H.
    replace (fill c (Node x1 x2)) with
      (fill (ctx_app c (NodeR x1 Hole)) x2) in H2.
    generalize (IHx2 _ H2).
    destruct c; simpl; intros; discriminate.
    rewrite <- fill_app; simpl; auto.
    inversion H.
    replace (fill c (Node x1 x2)) with
      (fill (ctx_app c (NodeL Hole x2)) x1) in H1.
    generalize (IHx1 _ H1).
    destruct c; simpl; intros; discriminate.
    rewrite <- fill_app; simpl; auto.
  Qed.

  Definition to_ctx (a:ShareTree) : nonEmptyTree a -> ctx.
   revert a.
    refine (fix f (a:ShareTree)  {struct a} : nonEmptyTree a -> ctx :=
           match a as a' return nonEmptyTree a' -> ctx with
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

  Lemma relativ_to_ctx : forall a x H,
    relativ_tree a x = fill (to_ctx a H) x.
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
    rewrite (relativ_to_ctx a (Node x y) H1) in H0.
    replace (fill (to_ctx a H1) (Node x y))
       with (fill (ctx_app (to_ctx a H1) (NodeL Hole y)) x) in H0.
    symmetry in H0.
    generalize (fill_id _ _ H0).
    destruct (to_ctx a H1); simpl; intros; discriminate.
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
    rewrite (relativ_to_ctx a (Node x y) H1) in H0.
    replace (fill (to_ctx a H1) (Node x y))
       with (fill (ctx_app (to_ctx a H1) (NodeR x  Hole)) y) in H0.
    symmetry in H0.
    generalize (fill_id _ _ H0).
    destruct (to_ctx a H1); simpl; intros; discriminate.
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
    rewrite (relativ_to_ctx (Node a1 a2) x H1) in H0.
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
  Proof. decide equality; apply bool_dec. Qed.

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
  Qed.

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
    Qed.

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
      spec IHisToken' n0.
      spec IHisToken'; [ omega | ].
      rewrite H1 in IHisToken'.
      inv IHisToken'.
      constructor.
      spec IHisToken' n0.
      spec IHisToken'.
      omega.
      rewrite H1 in IHisToken'.
      inversion IHisToken'.
      subst.
      constructor; auto.
      rewrite H5; auto.
      constructor.
      subst; rewrite H5; auto.
      spec IHisToken' n0 H0.
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
        (exist (fun x => canonicalTree x) (mkCanon (split_tok1 n' (projT1 tok))) (mkCanon_correct _)
        ,exist (fun x => canonicalTree x) (mkCanon (split_tok2 n' (projT1 tok))) (mkCanon_correct _)
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

    Open Local Scope nat_scope.

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
  
   Definition decompose (t : canonTree) :(canonTree * canonTree) :=
     let (x, c) := t in
      match x as s return (canonicalTree s -> (canonTree * canonTree)) with
      | Leaf b =>
          fun c0 : canonicalTree (Leaf b) =>
         (exist (fun t0 : ShareTree => canonicalTree t0) (Leaf b) c0,
          exist (fun t0 : ShareTree => canonicalTree t0) (Leaf b) c0)
      | Node x1 x2 =>
       fun c0 : canonicalTree (Node x1 x2) =>
         match c0 with
         | conj _ (conj _ (conj c1 c2)) =>
             (exist (fun t0 : ShareTree => canonicalTree t0) x1 c1,
              exist (fun t0 : ShareTree => canonicalTree t0) x2 c2)
         end
      end c.

  Fixpoint tree_heightP (t : ShareTree) : nat :=
   match t with 
   | Leaf b  => 0
   | Node l r => (max (tree_heightP l) (tree_heightP r)) + 1
  end.

  Definition tree_height (t : canonTree) := tree_heightP (proj1_sig t).

  Function unrel (t1 : t) (t2 : t) {measure tree_height t1} : t :=
   match t1 with
    | exist (Leaf b) _ => t2
    | _ => let (ltr1, rtr1) := decompose t1 in
           let (ltr2, rtr2) := decompose t2 in
              match ltr1 with  
               | exist (Leaf true) _ => ltr2
               | exist (Leaf false) _ => unrel rtr1 rtr2
               | _ => unrel ltr1 ltr2
              end
   end.
 intros.
 clear -teq1.
 inv teq1.
 destruct c.
 destruct a.
 destruct a.
 inv H0.
 unfold tree_height.
 simpl.
 omega.
 
 intros.
 clear -teq1.
 inv teq1.
 destruct c as [? [? [? ?]]].
 inv H0.
 unfold tree_height.
 simpl.
 remember (max (tree_heightP s1) (tree_heightP s2) + 1).
 assert (n1 <= max n1 (tree_heightP s0)).
   apply le_max_l.
 omega.
 Defined.

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
  spec IHt0_1 H1.
  spec IHt0_2 H2.
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
  spec H0 (exist (fun t0 => canonicalTree t0) (Leaf false) (canonTree_Leaf _))
          (exist (fun t0 => canonicalTree t0) (Leaf true) (canonTree_Leaf _)).
  detach H0.
  inv H0.
  unfold join,BAF.Join_ba.
  split;apply exist_ext;compute;trivial.
  intro.
  unfold identity in H0.
  spec H0 (exist (fun t0 => canonicalTree t0) (Leaf false) (canonTree_Leaf _))
          (exist (fun t : ShareTree => canonicalTree t) (Node x1 x2) c).
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
  rewrite H0;clear H0.
  assert (decompose (rel (exist (fun t0 : ShareTree => canonicalTree t0) (Node x1 x2)
         (conj n (conj n0 (conj c c0)))) sh) = 
         (rel (exist _ x1 c) sh, rel (exist _ x2 c0) sh)).
   generalize (rel_classification);intro.
   spec X (exist (fun t0 : ShareTree => canonicalTree t0) (Node x1 x2)
          (conj n (conj n0 (conj c c0)))) sh.
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
    spec X (exist (fun t0 : ShareTree => canonicalTree t0)
        (Node (Leaf true) (Leaf false))  
          (conj (or_intror (true = false) (Logic.eq_refl false))
           (conj (or_introl (false = true) (Logic.eq_refl true)) (conj I I))))
     (exist (fun t0 : ShareTree => canonicalTree t0) x c).
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
    spec X (exist (fun t0 : ShareTree => canonicalTree t0)
        (Node (Leaf false) (Leaf true))
         (conj (or_introl (true = false) (Logic.eq_refl false))
           (conj (or_intror (false = true) (Logic.eq_refl true)) (conj I I))))
     (exist (fun t0 : ShareTree => canonicalTree t0) x c).
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
  rewrite H.
  unfold bot;simpl.
  reflexivity.
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
 rewrite H0.
 unfold bot.
 rewrite unrel_equation.
 unfold top.
 trivial.
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
 assert (decompose
        (exist (fun t0 : ShareTree => canonicalTree t0)
        (Node (Leaf true) (Leaf false))
          (conj (or_intror eq_refl) (conj (or_introl eq_refl) (conj I I))))
         = (top,bot)).
   compute;apply injective_projections;apply exist_ext;trivial.
 rewrite H0;clear H0.
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
 rewrite H0.
 unfold bot.
 rewrite unrel_equation.
 unfold top.
 trivial.
Qed.

(*  END of the Le Xuan Bach contribution: definition and proofs about unrel *)

End Share.














