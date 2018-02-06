Require Import Perm.
Require Import FunctionalExtensionality.
Require Import VFA.SearchTree.

Arguments E {V}.
Arguments T {V} _ _ _ _.

Section TREES.

Variable V : Type.
Variable default: V.

Fixpoint pushdown_left (a: tree V) (bc: tree V) : tree V :=
 match bc with
 | E => a
 | T b y vy c => T (pushdown_left a b) y vy c
 end.

Fixpoint delete (x: key) (s: tree V) : tree V :=
 match s with
 | E => E
 | T a y v' b => if  x <? y then T (delete x a) y v' b
                        else if y <? x then T a y v' (delete x b)
                        else pushdown_left a b
 end.

End TREES.

Arguments insert {V} x v s.
Arguments lookup {V} default x t.
Arguments pushdown_left {V} a bc.
Arguments delete {V} x s.

Section PARTIAL_TREES.

Variable V : Type.
Variable default: V.

Inductive partial_tree : Type :=
 | H : partial_tree
 | L : partial_tree -> key -> V -> tree V -> partial_tree
 | R : tree V -> key -> V -> partial_tree -> partial_tree.

Fixpoint partial_tree_tree (pt: partial_tree): tree V -> tree V :=
  match pt with
  | H => fun t => t
  | L ptl k v t2 => fun t => T (partial_tree_tree ptl t) k v t2
  | R t1 k v pt2 => fun t => T t1 k v (partial_tree_tree pt2 t)
  end.

Fixpoint partial_tree_partial_tree (pt: partial_tree): partial_tree -> partial_tree :=
  match pt with
  | H => fun pt0 => pt0
  | L ptl k v t2 => fun pt0 => L (partial_tree_partial_tree ptl pt0) k v t2
  | R t1 k v pt2 => fun pt0 => R t1 k v (partial_tree_partial_tree pt2 pt0)
  end.

Lemma partial_tree_partial_tree_tree: forall pt1 pt2,
  partial_tree_tree (partial_tree_partial_tree pt1 pt2) = Basics.compose (partial_tree_tree pt1) (partial_tree_tree pt2).
Proof.
  intros.
  extensionality t.
  unfold Basics.compose.
  induction pt1.
  + reflexivity.
  + simpl.
    rewrite IHpt1; auto.
  + simpl.
    rewrite IHpt1; auto.
Qed.

End PARTIAL_TREES.

Arguments H {V}.
Arguments L {V} _ _ _ _.
Arguments R {V} _ _ _ _.
Arguments partial_tree_tree {V} _ _.
Arguments partial_tree_partial_tree {V} _ _.
