(* Copyright 2006, 2008 Andrew W. Appel, Robert Dockins and Xavier Leroy
 * This file is part of the List-machine Benchmark.
 * The List-machine Benchmark is licensed under GPLv3; see LICENSE.
 *)

(*** Library of finite maps indexed by positive binary integers ***)

Require Export ZArith.
Require Import Bool.

Lemma peq: forall (n1 n2: positive), {n1=n2}+{n1<>n2}.
Proof.
  decide equality.
Defined.

Section MAPS.

Variable A: Type.
Variable Aeq: forall (x y: A), {x=y} + {x<>y}.

Inductive map: Type :=
  | Leaf: map
  | Node: map -> option A -> map -> map.

Lemma map_eq:
  forall (m1 m2: map), {m1=m2} + {m1<>m2}.
Proof.
  assert (forall (o1 o2: option A), {o1=o2}+{o1<>o2}). decide equality.
  decide equality.
Defined.

Definition empty := Leaf.

Fixpoint is_empty (m:map) :=
  match m with
  | Leaf => true
  | _ => false
  end.

Fixpoint get (m: map) (i: positive) {struct i} : option A :=
  match m with
  | Leaf => None
  | Node l o r =>
      match i with
      | xH => o
      | xO ii => get l ii
      | xI ii => get r ii
      end
  end.

Fixpoint unset (m:map) (i:positive) { struct i } : map :=
  match m with
  | Leaf => Leaf
  | Node l o r =>
     match i with
     | xH => Node l None r
     | xO ii => Node (unset l ii) o r
     | xI ii => Node l o (unset r ii)
     end
  end.

Fixpoint set (m: map) (i: positive) (v: A) {struct i} : map :=
  match m with
  | Leaf =>
      match i with
      | xH => Node Leaf (Some v) Leaf
      | xO ii => Node (set Leaf ii v) None Leaf
      | xI ii => Node Leaf None (set Leaf ii v)
      end
  | Node l o r =>
      match i with
      | xH => Node l (Some v) r
      | xO ii => Node (set l ii v) o r
      | xI ii => Node l o (set r ii v)
      end
  end.

Lemma get_empty:
  forall (n: positive), get empty n = None.
Proof.
  induction n; simpl; auto.
Qed.

Lemma get_set_same:
  forall (n: positive) (m: map) (x: A),
  get (set m n x) n = Some x.
Proof.
  induction n; destruct m; intros; simpl; auto.
Qed.

Remark get_leaf:
  forall (n: positive), get Leaf n = None.
Proof get_empty.

Lemma get_set_other:
  forall (n1 n2: positive) (m: map) (x: A),
  n1 <> n2 -> get (set m n1 x) n2 = get m n2.
Proof.
  induction n1; intros; destruct n2; destruct m; simpl;
  try rewrite <- (get_leaf n2); auto; try apply IHn1; try congruence.
Qed.

Lemma get_set:
  forall (m: map) (n1 n2: positive) (x: A),
  get (set m n1 x) n2 =
  if peq n1 n2 then Some x else get m n2.
Proof.
  intros. case (peq n1 n2); intro.
  subst n2. apply get_set_same.
  apply get_set_other; auto.
Qed.

Lemma unset_same : forall m v,
   get (unset m v) v = None.

  intros m; induction m; intros;
    destruct v; simpl; auto.
 Qed.

Lemma unset_other : forall m v v',
   v <> v' ->
   get (unset m v) v' = get m v'.

   intros m; induction m; intros;
       destruct v; simpl; auto.
   destruct v'; simpl; auto.
   apply IHm2; congruence.
   destruct v'; simpl; auto.
   apply IHm1; congruence.
   destruct v'; simpl; auto.
   contradiction H; auto.
  Qed.


End MAPS.

Notation "a # b" := (get _ a b) (at level 1).
Notation "a # b <- c" := (set _ a b c) (at level 1, b at next level).

Section FORALL2.

Variables A B: Type.
Variable pred: A -> option B -> bool.

Definition pred_opt (x: option A) (y: option B) :=
  match x with
  | None => true
  | Some z => pred z y
  end.

Fixpoint map_forall2 (m1: map A) (m2: map B) {struct m1}: bool :=
  match m1, m2 with
  | Leaf, _ => true
  | Node l1 o1 r1, Leaf =>
      map_forall2 l1 (Leaf B) && pred_opt o1 None && map_forall2 r1 (Leaf B)
  | Node l1 o1 r1, Node l2 o2 r2 =>
      map_forall2 l1 l2 && pred_opt o1 o2 && map_forall2 r1 r2
  end.

Fixpoint map_forall2' (m1: map A) (m2: map B) {struct m2}: bool :=
  match m1, m2 with
  | Leaf, _ => true
  | Node l1 o1 r1, Leaf =>
      map_forall2 l1 (Leaf B) && pred_opt o1 None && map_forall2 r1 (Leaf B)
  | Node l1 o1 r1, Node l2 o2 r2 =>
      map_forall2' l1 l2 && pred_opt o1 o2 && map_forall2' r1 r2
  end.

Lemma map_forall2_eq : forall (m1:map A) (m2:map B),
  map_forall2 m1 m2 = map_forall2' m1 m2.

  intro m1; induction m1; intro m2; destruct m2; simpl; intuition.
  rewrite IHm1_1.
  rewrite IHm1_2.
  auto.
 Qed.

Lemma map_forall2_correct:
  forall m1 m2 i x,
  map_forall2 m1 m2 = true ->
  m1#i = Some x -> pred x m2#i = true.
Proof.
  induction m1; simpl; intros until x.
  rewrite get_leaf. congruence.
  destruct m2;
  intro C; elim (andb_prop _ _ C); intros C1 C2;
  elim (andb_prop _ _ C1); intros C3 C4; clear C; clear C1;
  destruct i; simpl.
  rewrite <- (get_leaf B i). auto.
  rewrite <- (get_leaf B i). auto.
  intro. subst o. exact C4.
  auto.
  auto.
  intro. subst o. exact C4.
Qed.

Lemma map_forall2_complete:
  forall m1 m2,
  (forall i x, m1#i = Some x -> pred x m2#i = true) ->
  map_forall2 m1 m2 = true.
Proof.
  induction m1; intros; simpl.
  auto.
  destruct m2.
  rewrite IHm1_1. rewrite IHm1_2. rewrite <- (get_leaf B 1).
  unfold pred_opt. destruct o. rewrite H. reflexivity. reflexivity.
  reflexivity.
  intros. rewrite get_leaf. rewrite <- (get_leaf B (xI i)). apply H. assumption.
  intros. rewrite get_leaf. rewrite <- (get_leaf B (xO i)). apply H. assumption.
  rewrite IHm1_1. rewrite IHm1_2.
  unfold pred_opt. destruct o. change o0 with (get B (Node B m2_1 o0 m2_2) 1).
  rewrite H. reflexivity. reflexivity.
  reflexivity.
  intros. change (m2_2#i) with (get B (Node B m2_1 o0 m2_2) (xI i)). apply H. assumption.
  intros. change (m2_1#i) with (get B (Node B m2_1 o0 m2_2) (xO i)). apply H. assumption.
Qed.

End FORALL2.

Definition map_fmap (A B:Type) (f:A->B) : map A -> map B :=
  fix map_fmap (m:map A) : map B :=
  match m with
  | Leaf => Leaf _
  | Node m1 o m2 =>
       let x := match o with
                | None => None
                | Some x => Some (f x)
                end in
       Node _ (map_fmap m1) x (map_fmap m2)
  end.

Lemma fmap_none : forall A B (m:map A) (f:A->B) x,
  m#x = None ->
  (map_fmap A B f m)#x = None.

  intros A B m f; induction m; simpl; intros;
    destruct x; simpl in *; try discriminate; auto.
  destruct o; simpl; auto.
  discriminate.
 Qed.

Lemma fmap_none2 : forall A B (m:map A) (f:A->B) x,
  (map_fmap A B f m)#x = None ->
  m#x = None.

  intros A B m f; induction m; simpl; intros;
    destruct x; simpl in *; try discriminate; auto.
  destruct o; simpl; auto.
  discriminate.
 Qed.

Lemma fmap_eqn : forall A B (m:map A) (f:A->B) x a,
  m#x = Some a ->
  (map_fmap A B f m)#x = Some (f a).

  intros A B m f; induction m; simpl; intros;
    destruct x; simpl in *; try discriminate.
  apply IHm2; auto.
  apply IHm1; auto.
  destruct o; simpl.
  congruence.
  discriminate.
 Qed.

Lemma fmap_eqn2 : forall A B (m:map A) (f:A->B) x b,
  (map_fmap A B f m)#x = Some b ->
  exists a, m#x = Some a /\ f a = b.

  intros A B m f; induction m; simpl; intros;
    destruct x; simpl in *; try discriminate.
  apply IHm2; auto.
  apply IHm1; auto.
  destruct o; simpl.
  exists a; intuition.
  congruence.
  discriminate.
 Qed.

Lemma fmap_update : forall A B (m:map A) (f:A->B) x a,
  (map_fmap A B f (m#x <- a)) =
  (map_fmap A B f m)#x <- (f a).

  intros A B m f; induction m; simpl; intros.
  induction x; simpl in *.
  rewrite IHx; auto.
  rewrite IHx; auto.
  auto.

  destruct x; destruct o; simpl; auto.
  rewrite IHm2; auto.
  rewrite IHm2; auto.
  rewrite IHm1; auto.
  rewrite IHm1; auto.
 Qed.

Lemma fmap_unset : forall A B (m:map A) (f:A->B) x,
   (map_fmap A B f (unset A m x)) =
   unset B (map_fmap A B f m) x.

  intros A B m f; induction m; simpl; intros.
  destruct x; simpl; auto.

  destruct x; destruct o; simpl; auto.
  rewrite IHm2; auto.
  rewrite IHm2; auto.
  rewrite IHm1; auto.
  rewrite IHm1; auto.
 Qed.

Definition map_fold_index'
   (A B:Type)
   (f:positive -> A -> B)
   (c:B -> B -> B) :
   B -> (positive -> positive) -> (map A) -> B :=

   fix fold (z:B) (g:positive -> positive) (M:map A) { struct M } : B :=

  match M with
  | Leaf => z
  | Node l None r =>
     fold (fold z (fun x => g (xI x)) r) (fun x => g (xO x)) l
  | Node l (Some x) r =>
     fold (c (f (g xH) x) (fold z (fun x => g (xI x)) r)) (fun x => g (xO x)) l
  end.

Definition map_fold_index
   (A B:Type)
   (f:positive -> A -> B)
   (c:B -> B -> B)
   (z:B) (M:map A) : B :=
  map_fold_index' A B f c z (fun x => x) M.

Section map_fold_index.
  Variables A B:Type.
  Variable f:positive -> A -> B.
  Variable c:B -> B -> B.
  Variable u:B.

  Hypothesis Hassoc : forall x y z:B,
     c x (c y z) = c (c x y) z.
  Hypothesis Hunit_left : forall x, c u x = x.

  Lemma map_fold_index_lift_z : forall
     (m:map A) (g:positive -> positive) (z:B),

     map_fold_index' A B f c z g m =
     c (map_fold_index' A B f c u g m) z.

     intro m; induction m; simpl; intros.
     rewrite Hunit_left; auto.
     destruct o; simpl.
     symmetry.
     rewrite IHm1.
     rewrite <- Hassoc.
     rewrite <- Hassoc.
     symmetry.
     rewrite IHm1.
     rewrite IHm2.
     auto.
     symmetry.
     rewrite IHm1.
     rewrite <- Hassoc.
     symmetry.
     rewrite IHm1.
     rewrite IHm2.
     auto.
    Qed.

  Lemma map_fold_index_lookup' : forall
     (m:map A) (g:positive -> positive) (z:B) v x,

     m#v = Some x -> exists l, exists r,
       map_fold_index' A B f c z g m =
         c l (c (f (g v) x) r).

     intro m; induction m; simpl; intros.
     destruct v; simpl in H; discriminate.

     destruct v; destruct o; simpl in H |- *.

     rewrite map_fold_index_lift_z.
     rewrite Hassoc.
     destruct (IHm2 (fun x => g (xI x)) z v x) as [l' [r' ?]]; intuition.
     rewrite <- Hassoc.
     exists (c (c (map_fold_index' A B f c u (fun x => g (xO x)) m1) (f (g xH) a)) l').
     exists r'.
     rewrite H0.
     rewrite <- Hassoc.
     rewrite <- Hassoc.
     auto.

     rewrite map_fold_index_lift_z.
     destruct (IHm2 (fun x => g (xI x)) z v x) as [l' [r' ?]]; intuition.
     exists (c (map_fold_index' A B f c u (fun x => g (xO x)) m1) l').
     exists r'.
     rewrite H0.
     rewrite <- Hassoc.
     auto.

     rewrite map_fold_index_lift_z.
     destruct (IHm1 (fun x => g (xO x)) u v x) as [l' [r' ?]]; intuition.
     exists l'.
     rewrite H0.
     rewrite <- Hassoc.
     rewrite <- Hassoc.
     exists (c r' (c (f (g xH) a) (map_fold_index' A B f c z (fun x => g (xI x)) m2))).
     auto.

     rewrite map_fold_index_lift_z.
     destruct (IHm1 (fun x => g (xO x)) u v x) as [l' [r' ?]]; intuition.
     exists l'.
     rewrite H0.
     rewrite <- Hassoc.
     rewrite <- Hassoc.
     exists (c r' (map_fold_index' A B f c z (fun x => g (xI x)) m2)).
     auto.

     replace a with x; [ | congruence ].
     rewrite map_fold_index_lift_z.
     exists (map_fold_index' A B f c u (fun x => g (xO x)) m1).
     exists (map_fold_index' A B f c z (fun x => g (xI x)) m2).
     auto.

     discriminate.
    Qed.

  Lemma map_fold_index_lookup : forall
     (m:map A) (z:B) v x,

     m#v = Some x -> exists l, exists r,
       map_fold_index A B f c z m = c l (c (f v x) r).

     unfold map_fold_index; intros.
     apply (map_fold_index_lookup' m (fun x => x)); auto.
    Qed.
End map_fold_index.
