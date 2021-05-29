(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** This file extended to canonical (extensional) PTrees by Andrew Appel *)

(** Applicative finite maps are the main data structure used in this
  project.  A finite map associates data to keys.  The two main operations
  are [set k d m], which returns a map identical to [m] except that [d]
  is associated to [k], and [get k m] which returns the data associated
  to key [k] in map [m].  In this library, we distinguish two kinds of maps:
- Trees: the [get] operation returns an option type, either [None]
  if no data is associated to the key, or [Some d] otherwise.
- Maps: the [get] operation always returns a data.  If no data was explicitly
  associated with the key, a default data provided at map initialization time
  is returned.

  In this library, we provide efficient implementations of trees and
  maps whose keys range over the type [positive] of binary positive
  integers or any type that can be injected into [positive].  The
  implementation is based on radix-2 search trees (uncompressed
  Patricia trees) and guarantees logarithmic-time operations.  An
  inefficient implementation of maps as functions is also provided.
*)

Require Import Equivalence EquivDec.
Require Import compcert.lib.Coqlib.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Set Implicit Arguments.

(** * The abstract signatures of trees *)

Module Type TREE.
  Parameter elt: Type.
  Parameter elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Parameter t: Type -> Type.
  Parameter empty: forall (A: Type), t A.
  Parameter get: forall (A: Type), elt -> t A -> option A.
  Parameter set: forall (A: Type), elt -> A -> t A -> t A.
  Parameter remove: forall (A: Type), elt -> t A -> t A.

  (** The ``good variables'' properties for trees, expressing
    commutations between [get], [set] and [remove]. *)
  Axiom gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Axiom gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Axiom gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Axiom gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  (* We could implement the following, but it's not needed for the moment.
  Hypothesis gsident:
    forall (A: Type) (i: elt) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Hypothesis grident:
    forall (A: Type) (i: elt) (m: t A) (v: A),
    get i m = None -> remove i m = m.
  *)
  Axiom grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Axiom gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Axiom grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.

  (** Extensional equality between trees. *)
  Parameter beq: forall (A: Type), (A -> A -> bool) -> t A -> t A -> bool.
  Axiom beq_correct:
    forall (A: Type) (eqA: A -> A -> bool) (t1 t2: t A),
    beq eqA t1 t2 = true <->
    (forall (x: elt),
     match get x t1, get x t2 with
     | None, None => True
     | Some y1, Some y2 => eqA y1 y2 = true
     | _, _ => False
    end).

  (** Applying a function to all data of a tree. *)
  Parameter map:
    forall (A B: Type), (elt -> A -> B) -> t A -> t B.
  Axiom gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).

  (** Same as [map], but the function does not receive the [elt] argument. *)
  Parameter map1:
    forall (A B: Type), (A -> B) -> t A -> t B.
  Axiom gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).

  (** Applying a function pairwise to all data of two trees. *)
  Parameter combine:
    forall (A B C: Type), (option A -> option B -> option C) -> t A -> t B -> t C.
  Axiom gcombine:
    forall (A B C: Type) (f: option A -> option B -> option C),
    f None None = None ->
    forall (m1: t A) (m2: t B) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).

  (** Enumerating the bindings of a tree. *)
  Parameter elements:
    forall (A: Type), t A -> list (elt * A).
  Axiom elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Axiom elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Axiom elements_keys_norepet:
    forall (A: Type) (m: t A),
    list_norepet (List.map (@fst elt A) (elements m)).
  Axiom elements_extensional:
    forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
  Axiom elements_remove:
    forall (A: Type) i v (m: t A),
    get i m = Some v ->
    exists l1 l2, elements m = l1 ++ (i,v) :: l2 /\ elements (remove i m) = l1 ++ l2.

  (** Folding a function over all bindings of a tree. *)
  Parameter fold:
    forall (A B: Type), (B -> elt -> A -> B) -> t A -> B -> B.
  Axiom fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  (** Same as [fold], but the function does not receive the [elt] argument. *)
  Parameter fold1:
    forall (A B: Type), (B -> A -> B) -> t A -> B -> B.
  Axiom fold1_spec:
    forall (A B: Type) (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.
End TREE.

(** * The abstract signatures of maps *)

Module Type MAP.
  Parameter elt: Type.
  Parameter elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Parameter t: Type -> Type.
  Parameter init: forall (A: Type), A -> t A.
  Parameter get: forall (A: Type), elt -> t A -> A.
  Parameter set: forall (A: Type), elt -> A -> t A -> t A.
  Axiom gi:
    forall (A: Type) (i: elt) (x: A), get i (init x) = x.
  Axiom gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = x.
  Axiom gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Axiom gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Axiom gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Parameter map: forall (A B: Type), (A -> B) -> t A -> t B.
  Axiom gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
End MAP.

(** * An implementation of trees over type [positive] *)

Module PTree <: TREE.
  Definition elt := positive.
  Definition elt_eq := peq.

  Inductive tree' (A: Type) : Type := 
  | Node001: tree' A -> tree' A
  | Node010: A -> tree' A
  | Node011: A -> tree' A -> tree' A
  | Node100: tree' A -> tree' A
  | Node101: tree' A -> tree' A ->tree' A
  | Node110: tree' A -> A -> tree' A
  | Node111: tree' A -> A -> tree' A -> tree' A.

  Inductive tree (A: Type) : Type := 
  | Empty : tree A
  | Nodes: tree' A -> tree A.

  Arguments Node001 {A} _.
  Arguments Node010 {A} _.
  Arguments Node011 {A} _ _.
  Arguments Node100 {A} _.
  Arguments Node101 {A} _ _.
  Arguments Node110 {A} _ _.
  Arguments Node111 {A} _ _ _.

  Arguments Empty {A}.
  Arguments Nodes {A} _.

  Scheme tree'_ind := Induction for tree' Sort Prop.

  Definition t := tree.

  Definition empty (A : Type) := (Empty : t A).

  Fixpoint get' {A} (p: positive) (m: tree' A) : option A :=
  match p, m with
  | xH, Node001 _ => None
  | xH, Node010 x => Some x
  | xH, Node011 x _ => Some x
  | xH, Node100 _ => None
  | xH, Node101 _ _ => None
  | xH, Node110 _ x => Some x
  | xH, Node111 _ x _ => Some x
  | xO q, Node001 _ => None
  | xO q, Node010 _ => None
  | xO q, Node011 _ _ => None
  | xO q, Node100 m' => get' q m'
  | xO q, Node101 m' _ => get' q m'
  | xO q, Node110 m' _ => get' q m'
  | xO q, Node111 m' _ _ => get' q m'
  | xI q, Node001 m' => get' q m'
  | xI q, Node010 _ => None
  | xI q, Node011 _ m' => get' q m'
  | xI q, Node100 m' => None
  | xI q, Node101 _ m' => get' q m'
  | xI q, Node110 _ _ => None
  | xI q, Node111 _ _ m' => get' q m'
end.
 
  Definition get {A} (p: positive) (m: t A) : option A :=
  match m with
  | Empty => None
  | Nodes m' => get' p m'
  end.

  Fixpoint set0 {A} (p: positive) (x: A) : tree' A :=
  match p with
  | xH => Node010 x
  | xO q => Node100 (set0 q x)
  | xI q => Node001 (set0 q x)
  end.

  Fixpoint set' {A} (p: positive) (x: A) (m: tree' A) : tree' A :=
  match p, m with
  | xH, Node001 r => Node011 x r
  | xH, Node010 _ => Node010 x
  | xH, Node011 _ r => Node011 x r
  | xH, Node100 l => Node110 l x
  | xH, Node101 l r => Node111 l x r
  | xH, Node110 l _ => Node110 l x
  | xH, Node111 l _ r => Node111 l x r
  | xO q, Node001 r => Node101 (set0 q x) r
  | xO q, Node010 y => Node110 (set0 q x) y
  | xO q, Node011 y r => Node111 (set0 q x) y r
  | xO q, Node100 l => Node100 (set' q x l)
  | xO q, Node101 l r => Node101 (set' q x l) r
  | xO q, Node110 l y => Node110 (set' q x l) y
  | xO q, Node111 l y r => Node111 (set' q x l) y r
  | xI q, Node001 r => Node001 (set' q x r)
  | xI q, Node010 y => Node011 y (set0 q x)
  | xI q, Node011 y r => Node011 y (set' q x r)
  | xI q, Node100 l => Node101 l (set0 q x)
  | xI q, Node101 l r => Node101 l (set' q x r)
  | xI q, Node110 l y => Node111 l y (set0 q x)
  | xI q, Node111 l y r => Node111 l y (set' q x r)
  end.

  Definition set {A} (p: positive) (x: A) (m: t A) : t A :=
  match m with
  | Empty => Nodes (set0 p x)
  | Nodes m' => Nodes (set' p x m')
  end.

  Fixpoint rem' {A} (p: positive) (m: tree' A) : tree A :=
  match p, m with
  | xH, Node001 r => Nodes m
  | xH, Node010 _ => Empty
  | xH, Node011 _ r => Nodes (Node001 r)
  | xH, Node100 l => Nodes m
  | xH, Node101 l r => Nodes m
  | xH, Node110 l _ => Nodes (Node100 l)
  | xH, Node111 l _ r => Nodes (Node101 l r)
  | xO q, Node001 r => Nodes m
  | xO q, Node010 y => Nodes m
  | xO q, Node011 y r => Nodes m
  | xO q, Node100 l => match rem' q l with Empty => Empty
                                       | Nodes m' => Nodes (Node100 m')
                                     end
  | xO q, Node101 l r => match rem' q l with Empty => Nodes(Node001 r)
                                       | Nodes m' => Nodes (Node101 m' r)
                                     end
  | xO q, Node110 l y => match rem' q l with Empty => Nodes(Node010 y)
                                       | Nodes m' => Nodes (Node110 m' y)
                                     end
  | xO q, Node111 l y r => match rem' q l with Empty => Nodes(Node011 y r)
                                       | Nodes m' => Nodes (Node111 m' y r)
                                     end
  | xI q, Node001 r => match rem' q r with Empty => Empty
                                       | Nodes m' => Nodes (Node001 m')
                                     end
  | xI q, Node010 y => Nodes m
  | xI q, Node011 y r => match rem' q r with Empty => Nodes(Node010 y)
                                       | Nodes m' => Nodes (Node011 y m')
                                     end
  | xI q, Node100 l => Nodes m
  | xI q, Node101 l r => match rem' q r with Empty => Nodes(Node100 l)
                                       | Nodes m' => Nodes (Node101 l m')
                                     end
  | xI q, Node110 l y => Nodes m
  | xI q, Node111 l y r => match rem' q r with Empty => Nodes(Node110 l y)
                                       | Nodes m' => Nodes (Node111 l y m')
                                     end
  end.

  Definition remove {A} (p: positive) (m: t A) : t A :=
  match m with
  | Empty => m
  | Nodes m' => rem' p m'
  end.

  Theorem gempty:
    forall (A: Type) (i: positive), get i (empty A) = None.
  Proof. intros. destruct i; simpl; reflexivity. Qed.

  Lemma gss0: forall {A} p (x: A), get' p (set0 p x) = Some x.
  Proof. induction p; simpl; auto. Qed.

  Lemma gso0: forall {A} p q (x: A), p<>q -> get' p (set0 q x) = None.
  Proof.
   induction p; destruct q; simpl; intros; auto.
   apply IHp. congruence.
   apply IHp; congruence.
   congruence.
  Qed.

  Theorem gss:
    forall (A: Type) (i: positive) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof.
   intros.
   destruct m as [|m]; simpl.
   - apply gss0.
   - revert m; induction i; destruct m; simpl; intros; auto; try apply gss0.
  Qed.

  Theorem gso:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
  intros.
  destruct m as [|m]; simpl.
  apply gso0; auto.
  revert m j H; induction i; destruct j,m; simpl; intros; auto;
  try (apply IHi; congruence);
  try (apply gso0; congruence);
  try congruence.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    get i (set j x m) = if peq i j then Some x else get i m.
  Proof.
    intros.
    destruct (peq i j); [ rewrite e; apply gss | apply gso; auto ].
  Qed.

  Theorem gsident:
    forall (A: Type) (i: positive) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof.
    destruct m as [|m]; intros. inv H.
    revert m H; induction i; simpl; intros; destruct m; try congruence;
    f_equal; simpl in IHi; f_equal; apply IHi in H; injection H as H; auto.
  Qed.

  Theorem set2:
    forall (A: Type) (i: elt) (m: t A) (v1 v2: A),
    set i v2 (set i v1 m) = set i v2 m.
  Proof.
    intros. destruct m as [|m]; simpl; f_equal.
    induction i; simpl; f_equal; auto.
    revert m; induction i; destruct m; simpl; f_equal; auto;
    clear; induction i; simpl; f_equal; auto.
  Qed.

  Theorem grs:
    forall (A: Type) (i: positive) (m: t A), get i (remove i m) = None.
  Proof.
  unfold remove.
  destruct m as [ |m]. apply gempty.
  unfold get.
  destruct (rem' i m) eqn:?H; auto.
  rename t0 into m'.
  revert m m' H.
  induction i; destruct m; simpl; intros; auto; try solve [inv H; auto];
  match type of H with match ?A with _ => _ end = _ => destruct A eqn:?H; inv H end; eauto.
  Qed.

  Lemma Nodes_inj: forall {A} (m1 m2: tree' A), Nodes m1 = Nodes m2 -> m1=m2.
  Proof. intros. congruence. Qed.

  Lemma gro_aux:
    forall {A} p q (m: tree' A), p<>q -> rem' q m = Empty -> None = get' p m.
  Proof.
  induction p; destruct q,m; simpl; intros; auto;
  try match type of H0 with match ?A with _ => _ end = _ => destruct A eqn:?H; inv H0; eauto end;
  try (assert (H3: p<>q) by congruence; apply (IHp _ _ H3 H1)); try discriminate.
  congruence.
  Qed.

  Theorem gro:
    forall (A: Type) (i j: positive) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
  intros A p q ? ?.
  destruct m as [|m].
  simpl. reflexivity.
  unfold get, remove.
  destruct (rem' q m) as [|m'] eqn:?H.
  -
  symmetry.
  revert q m H H0; induction p; destruct q, m; simpl; intros; auto;
  try match type of H0 with match ?A with _ => _ end = _ => destruct A eqn:?H; inv H0; eauto end;
  try (eapply IHp; try eassumption; auto; congruence);
  try discriminate.
  congruence.
  -
  revert q H m m' H0; induction p; destruct q,m; simpl; intros; auto;
  try match type of H0 with match ?A with _ => _ end = _ => destruct A eqn:?H; inv H0; eauto end;
  try (assert (H3: p<>q) by congruence; eauto);
  try apply Nodes_inj in H0; subst; auto;
  try solve [eapply gro_aux; eassumption];
  try discriminate;
  try congruence.
  Unshelve. all: apply xH.
  Qed.

  Theorem grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros. destruct (elt_eq i j). subst j. apply grs. apply gro; auto.
  Qed.

  Definition getleft' {A} (m: tree' A) : t A :=
  match m with
  | Node100 l => Nodes l
  | Node101 l _ => Nodes l
  | Node110 l _ => Nodes l
  | Node111 l _ _ => Nodes l
  | _ => Empty
  end.

  Definition getright' {A} (m: tree' A) : t A :=
  match m with
  | Node001 r => Nodes r
  | Node101 _ r => Nodes r
  | Node011 _ r => Nodes r
  | Node111 _ _ r => Nodes r
  | _ => Empty
  end.

  Definition getleft {A} (m: tree A) : t A :=
  match m with Empty => Empty | Nodes m' => getleft' m' end.

  Definition getright {A} (m: tree A) : t A :=
  match m with Empty => Empty | Nodes m' => getright' m' end.

  Definition Node {A} l o r : t A := 
    match l,o,r with
    | Empty, None, Empty => Empty
    | Empty, None, Nodes r' => Nodes (Node001 r')
    | Empty, Some x, Empty => Nodes (Node010 x)
    | Empty, Some x, Nodes r' => Nodes (Node011 x r')
    | Nodes l', None, Empty => Nodes (Node100 l')
    | Nodes l', None, Nodes r' => Nodes (Node101 l' r')
    | Nodes l', Some x, Empty => Nodes (Node110 l' x)
    | Nodes l', Some x, Nodes r' => Nodes (Node111 l' x r')
    end.

  Lemma asNode: forall {A} (m: t A),
    m = Node (getleft m) (get xH m) (getright m).
  Proof. destruct m as [|[]]; reflexivity. Qed.

  Lemma get_xO_Node: forall {A} i l (x: option A) r,
    get (xO i) (Node l x r) = get i l.
  Proof. intros. destruct l, x, r; auto. Qed.

  Lemma get_xI_Node: forall {A} i l (x: option A) r,
    get (xI i) (Node l x r) = get i r.
  Proof. intros. destruct l, x, r; auto. Qed.

  Lemma get_xH_Node: forall {A} l (x: option A) r,
    get xH (Node l x r) = x.
  Proof. intros. destruct l, x, r; auto. Qed.

  Definition equivalent {A} (m1 m2: t A) : Prop :=
    forall i, get i m1 = get i m2.

  Lemma Nodes_not_Empty:
  forall {A} (m: tree' A), ~ (equivalent (Nodes m) Empty).
  Proof.
  intros.
  induction m; simpl; intro; try (apply IHm; intro);
  try (specialize (H xH); discriminate).
  apply (H (xI i)).
  apply (H (xO i)).
  apply IHm1; intro.
  apply (H (xO i)).
  Qed.

  Lemma tree'_not_empty:
   forall {A} (m: tree' A), exists i, exists x, get' i m = Some x.
  Proof.
   induction m; simpl;
   try destruct IHm as [p [x H]].
   exists (xI p), x; apply H.
   exists xH, a; reflexivity.
   exists xH, a; reflexivity.
   exists (xO p), x; apply H.
   destruct IHm1 as [p [x H]]; exists (xO p), x; apply H.
   exists xH, a; reflexivity.
   exists xH, a; reflexivity.
  Qed.

  Lemma extensionality: 
    forall (A : Type) (m1 m2: t A), 
      equivalent m1 m2 ->    m1=m2.
  Proof.
  intro.
  destruct m1 as [|m1], m2 as [|m2]; simpl; intros; auto.
  -
  exfalso.
  apply (@Nodes_not_Empty _ m2).
  intro. symmetry; auto.
  -
  exfalso.
  apply (@Nodes_not_Empty _ m1); auto.
  -
  f_equal.
  assert (forall p, get' p m1 = get' p m2).
  apply H.
  clear H. rename H0 into H.
  revert m2 H; induction m1; destruct m2; simpl; intros;
  try (specialize (H xH); discriminate).
  f_equal; apply IHm1; intro; apply (H (xI p)).
  exfalso. destruct (tree'_not_empty m1) as [q [x H0]]. specialize (H (xI q)). simpl in H. congruence.
  exfalso. destruct (tree'_not_empty m2_1) as [q [x H0]]. specialize (H (xO q)). simpl in H. congruence.
  f_equal. specialize (H xH); simpl in H; congruence.
  exfalso. destruct (tree'_not_empty m2) as [q [x H0]]. specialize (H (xI q)). simpl in H. congruence.
  exfalso. destruct (tree'_not_empty m2) as [q [x H0]]. specialize (H (xO q)). simpl in H. congruence.
  exfalso. destruct (tree'_not_empty m2_1) as [q [x H0]]. specialize (H (xO q)). simpl in H. congruence.
  exfalso. destruct (tree'_not_empty m1) as [q [x H0]]. specialize (H (xI q)). simpl in H. congruence.
  f_equal. specialize (H xH); simpl in H; congruence. apply IHm1. intro p. apply (H (xI p)).
  exfalso. destruct (tree'_not_empty m1) as [q [x H0]]. specialize (H (xI q)). simpl in H. congruence.
  exfalso. destruct (tree'_not_empty m2_1) as [q [x H0]]. specialize (H (xO q)). simpl in H. congruence.
  exfalso. destruct (tree'_not_empty m1) as [q [x H0]]. specialize (H (xO q)). simpl in H. congruence.
  f_equal; apply IHm1; intro p. apply (H (xO p)).
  exfalso. destruct (tree'_not_empty m2_2) as [q [x H0]]. specialize (H (xI q)). simpl in H. congruence.
  exfalso. destruct (tree'_not_empty m1_1) as [q [x H0]]. specialize (H (xO q)). simpl in H. congruence.
  exfalso. destruct (tree'_not_empty m1_2) as [q [x H0]]. specialize (H (xI q)). simpl in H. congruence.
  f_equal. apply IHm1_1; intro p; apply (H (xO p)). apply IHm1_2; intro p; apply (H (xI p)).
  exfalso. destruct (tree'_not_empty m1) as [q [x H0]]. specialize (H (xO q)). simpl in H. congruence.
  exfalso. destruct (tree'_not_empty m1) as [q [x H0]]. specialize (H (xO q)). simpl in H. congruence.
  f_equal.  apply IHm1. intro p. apply (H (xO p)). specialize (H xH); simpl in H; congruence. 
  exfalso. destruct (tree'_not_empty m2_2) as [q [x H0]]. specialize (H (xI q)). simpl in H. congruence.
  exfalso. destruct (tree'_not_empty m1_2) as [q [x H0]]. specialize (H (xI q)). simpl in H. congruence.
  exfalso. destruct (tree'_not_empty m1_1) as [q [x H0]]. specialize (H (xO q)). simpl in H. congruence.
  exfalso. destruct (tree'_not_empty m1_2) as [q [x H0]]. specialize (H (xI q)). simpl in H. congruence.
  f_equal. apply IHm1_1. intro p; apply (H (xO p)). specialize (H xH); simpl in H; congruence. apply IHm1_2; intro p; apply (H (xI p)).
  Qed.

  Section BOOLEAN_EQUALITY.

    Variable A: Type.
    Variable beqA: A -> A -> bool.

    Definition bempty (m: t A) : bool :=
      match m with
      | Empty => true
      | Nodes _ => false
      end.

    Fixpoint beq' (m1 m2: tree' A) {struct m1} : bool :=
    match m1, m2 with
    | Node001 r1, Node001 r2 => beq' r1 r2
    | Node010 x1, Node010 x2 => beqA x1 x2
    | Node011 x1 r1, Node011 x2 r2 => beqA x1 x2 && beq' r1 r2
    | Node100 l1, Node100 l2 => beq' l1 l2
    | Node101 l1 r1, Node101 l2 r2 => beq' l1 l2 && beq' r1 r2
    | Node110 l1 x1, Node110 l2 x2 => beqA x1 x2 && beq' l1 l2
    | Node111 l1 x1 r1, Node111 l2 x2 r2  => beqA x1 x2 && beq' l1 l2 && beq' r1 r2
    | _, _ => false
    end.

    Definition beq (m1 m2: t A) : bool :=
    match m1, m2 with
    | Empty, Empty => true
    | Nodes m1', Nodes m2' => beq' m1' m2'
    | _, _ => false
    end.

    Lemma bempty_correct:
      forall m, bempty m = true <-> (forall x, get x m = None).
    Proof.
      intros.
      pose proof (@extensionality A m Empty).
      split; intros.
      destruct m; inv H0. reflexivity.
      rewrite H. reflexivity.
      intro i; apply H0.
    Qed.

    Lemma beq_correct':
      (forall x y, beqA x y = true <-> x=y) ->
      forall m1 m2,
      beq m1 m2 = true <-> m1 = m2.
     Proof.
      intro H.
      destruct m1 as [|m1]; destruct m2 as [|m2]; simpl.
       tauto.
       split; intros; discriminate.  
       split; intros; discriminate.  
       revert m2; induction m1; destruct m2; simpl; intros;
       try solve [split; intro; discriminate];
       rewrite ?andb_true_iff, ?H; clear H;
       rewrite ?IHm1, ?IHm1_1, ?IHm1_2; clear;
       split; intro H; decompose [and] H; repeat split; try congruence.
     Qed.

    Lemma beq_correct:
      forall m1 m2,
      beq m1 m2 = true <->
      (forall (x: elt),
       match get x m1, get x m2 with
       | None, None => True
       | Some y1, Some y2 => beqA y1 y2 = true
       | _, _ => False
       end).
    Proof.
     intros.
      destruct m1 as [|m1]; destruct m2 as [|m2]; simpl.
     - tauto.
     - split; [intro; discriminate |]; intro.
       destruct (tree'_not_empty m2) as [i [x H0]]; specialize (H i); rewrite H0 in H; contradiction.
     - split; [intro; discriminate |]; intro.
       destruct (tree'_not_empty m1) as [i [x H0]]; specialize (H i); rewrite H0 in H; contradiction.
    -
      revert m2; induction m1; destruct m2; simpl; intros.
  all: try (split; intro; [discriminate |]; contradiction (H xH)).
  all: try (split; intro; [discriminate |];
     destruct (tree'_not_empty m1) as [i [x H0]];
     specialize (H (xO i)); simpl in H; rewrite H0 in H; contradiction).
  all: try (split; intro; [discriminate |];
     destruct (tree'_not_empty m2) as [i [x H0]];
     specialize (H (xO i)); simpl in H; rewrite H0 in H; contradiction).
  all: try (split; intro; [discriminate |];
     destruct (tree'_not_empty m2) as [i [x H0]];
     specialize (H (xI i)); simpl in H; rewrite H0 in H; contradiction).
  all: try (split; intro; [discriminate |];
     destruct (tree'_not_empty m1_1) as [i [x H0]];
     specialize (H (xO i)); simpl in H; rewrite H0 in H; contradiction).
  all: try (split; intro; [discriminate |];
     destruct (tree'_not_empty m1_2) as [i [x H0]];
     specialize (H (xI i)); simpl in H; rewrite H0 in H; contradiction).
  all: try (split; intro; [discriminate |];
     destruct (tree'_not_empty m2_1) as [i [x H0]];
     specialize (H (xO i)); simpl in H; rewrite H0 in H; contradiction).
  all: try (split; intro; [discriminate |];
     destruct (tree'_not_empty m2_2) as [i [x H0]];
     specialize (H (xI i)); simpl in H; rewrite H0 in H; contradiction).
  all: try (split; intro; [discriminate |];
     destruct (tree'_not_empty m1) as [i [x H0]];
     specialize (H (xI i)); simpl in H; rewrite H0 in H; contradiction).
  all: try (rewrite IHm1; clear IHm1);
        try (rewrite IHm1_1; clear IHm1_1);
        try (rewrite IHm1_2; clear IHm1_2).
  all: try solve [ split; intros;
   [ destruct x; simpl; auto; try apply H 
   | try apply (H (xI x)); try apply (H (xO x))]].
  +
   split.
   intros H [x|x|]; simpl; auto.
   intros. apply (H xH).
  + rewrite andb_true_iff.
   split.
   intros [? ?].
   rewrite IHm1 in H0; clear IHm1.
   intros [x|x|]; simpl; auto. apply (H0 x).
   intro H. split. apply (H xH). rewrite IHm1. 
   intro x; apply (H (xI x)).
  + rewrite andb_true_iff.
   rewrite IHm1_1; clear IHm1_1.
   rewrite IHm1_2; clear IHm1_2.
   split.
   intros [? ?] [x|x|]. apply (H0 x). apply (H x). apply I.
   intros H; split; intro x. apply (H (xO x)). apply (H (xI x)).
  + rewrite andb_true_iff.
   rewrite IHm1; clear IHm1.
   split.
   intros [? ?] [x|x|]. apply I. apply (H0 x). apply H.
   intros H; split; intros. apply (H xH). apply (H (xO x)).
  + rewrite !andb_true_iff.
   rewrite IHm1_1; clear IHm1_1.
   rewrite IHm1_2; clear IHm1_2.
   split.
   intros [[? ?] ?] [x|x|]. apply (H1 x). apply (H0 x). apply H.
   intros H; split; [split|]; intros. apply (H xH). apply (H (xO x)). apply (H (xI x)).
  Qed.

  End BOOLEAN_EQUALITY.

  Fixpoint prev_append (i j: positive) {struct i} : positive :=
    match i with
      | xH => j
      | xI i' => prev_append i' (xI j)
      | xO i' => prev_append i' (xO j)
    end.

  Definition prev (i: positive) : positive :=
    prev_append i xH.

  Lemma prev_append_prev i j:
    prev (prev_append i j) = prev_append j i.
  Proof.
    revert j. unfold prev.
    induction i as [i IH|i IH|]. 3: reflexivity.
    intros j. simpl. rewrite IH. reflexivity.
    intros j. simpl. rewrite IH. reflexivity.
  Qed.

  Lemma prev_involutive i :
    prev (prev i) = i.
  Proof (prev_append_prev i xH).

  Lemma prev_append_inj i j j' :
    prev_append i j = prev_append i j' -> j = j'.
  Proof.
    revert j j'.
    induction i as [i Hi|i Hi|]; intros j j' H; auto;
    specialize (Hi _ _ H); congruence.
  Qed.

    Fixpoint xmap (A B : Type) (f : positive -> A -> B) (m : tree' A) (i : positive)
             {struct m} : tree' B :=
      match m with
      | Node001 r => Node001 (xmap f r (xI i))
      | Node010 x => Node010 (f (prev i) x)
      | Node011 x r => Node011 (f (prev i) x) (xmap f r (xI i))
      | Node100 l => Node100 (xmap f l (xO i))
      | Node101 l r => Node101 (xmap f l (xO i)) (xmap f r (xI i))
      | Node110 l x => Node110 (xmap f l (xO i)) (f (prev i) x)
      | Node111 l x r => Node111 (xmap f l (xO i)) (f (prev i) x) (xmap f r (xI i))
      end.

  Definition map (A B : Type) (f : positive -> A -> B) m :=
      match m with
      | Empty => Empty
      | Nodes m => Nodes (xmap f m xH)
      end.

    Lemma xgmap:
      forall (A B: Type) (f: positive -> A -> B) (i j : positive) (m: tree' A),
      get' i (xmap f m j) = option_map (f (prev (prev_append i j))) (get' i m).
    Proof.
      induction i; intros; destruct m; simpl; auto.
    Qed.

  Theorem gmap:
    forall (A B: Type) (f: positive -> A -> B) (i: positive) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    intros A B f i m.
    destruct m as [|m].
    reflexivity.
    unfold get, map.
    rewrite xgmap. repeat f_equal. exact (prev_involutive i).
  Qed.

  Fixpoint map1' (A B: Type) (f: A -> B) (m: tree' A) {struct m} : tree' B :=
    match m with
      | Node001 r => Node001 (map1' f r)
      | Node010 x => Node010 (f x)
      | Node011 x r => Node011 (f x) (map1' f r)
      | Node100 l => Node100 (map1' f l)
      | Node101 l r => Node101 (map1' f l) (map1' f r)
      | Node110 l x => Node110 (map1' f l) (f x)
      | Node111 l x r => Node111 (map1' f l) (f x) (map1' f r)
      end.

  Definition map1 (A B: Type) (f: A -> B) (m: t A) : t B :=
    match m with
    | Empty => Empty
    | Nodes m => Nodes (map1' f m)
    end.

  Theorem gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).
  Proof.
    intros.
    destruct m as [|m]. 
    reflexivity.
    unfold get, map1.
    revert i; induction m; destruct i; simpl; intros; auto.
  Qed.

  Fixpoint filter1' (A: Type) (pred: A -> bool) (m: tree' A) {struct m} : t A :=
    match m with
      | Node001 r => match filter1' pred r with
                                  | Empty => Empty 
                                  | Nodes r' => Nodes (Node001 r')
                                  end
      | Node010 x => if pred x then Nodes m else Empty
      | Node011 x r => match pred x, filter1' pred r with
                               | false, Empty => Empty
                               | false, Nodes r' => Nodes (Node001 r')
                               | true, Empty => Nodes (Node010 x)
                               | true, Nodes r' => Nodes (Node011 x r')
                               end
      | Node100 l => match filter1' pred l with
                                  | Empty => Empty 
                                  | Nodes l' => Nodes (Node100 l')
                                  end
      | Node101 l r => match filter1' pred l, filter1' pred r with
                           | Empty, Empty => Empty
                           | Empty, Nodes r' => Nodes (Node001 r')
                           | Nodes l', Empty => Nodes (Node100 l')
                           | Nodes l', Nodes r' => Nodes (Node101 l' r')
                           end
      | Node110 l x => match pred x, filter1' pred l with
                               | false, Empty => Empty
                               | false, Nodes l' => Nodes (Node100 l')
                               | true, Empty => Nodes (Node010 x)
                               | true, Nodes l' => Nodes (Node110 l' x)
                               end
      | Node111 l x r => match filter1' pred l, pred x, filter1' pred r with
                               | Empty, false, Empty => Empty
                               | Empty, false, Nodes r' => Nodes (Node001 r')
                               | Empty, true, Empty => Nodes (Node010 x)
                               | Empty, true, Nodes r' => Nodes (Node011 x r')
                               | Nodes l', false, Empty => Nodes (Node100 l')
                               | Nodes l', false, Nodes r' => Nodes (Node101 l' r')
                               | Nodes l', true, Empty => Nodes (Node110 l' x)
                               | Nodes l', true, Nodes r' => Nodes (Node111 l' x r')
                               end
      end.

  Definition filter1 (A: Type) (pred: A -> bool) (m: t A) : t A :=
  match m with Empty => Empty | Nodes m' => filter1' pred m' end.

  Lemma filter1'_Empty_get:
   forall {A} pred (m: tree' A) a i, 
     filter1' pred m = Empty -> get' i m = Some a -> pred a = false.
  Proof.
   induction m; destruct i; simpl; intros;
   repeat match goal with H: match ?A with _ => _ end = _  |- _  => 
        destruct A eqn:?; inv H end.
   all: try (inv H0; auto).
   all: try solve [eapply IHm; eauto]; try discriminate.
   all: try solve [eapply IHm1; eauto]; try discriminate.
   all: try solve [eapply IHm2; eauto]; try discriminate.
  Qed.

  Theorem gfilter1:
    forall (A: Type) (pred: A -> bool) (i: elt) (m: t A),
    get i (filter1 pred m) =
    match get i m with None => None | Some x => if pred x then Some x else None end.
  Proof.
    intros until m.
    destruct m as [|m]. reflexivity.
    unfold get, filter1.
    destruct (filter1' pred m) as [|m'] eqn:?H.
   -
    destruct (get' i m) eqn:?H; auto.
    rewrite (filter1'_Empty_get _ _ _ H H0); auto.
  -
   revert i m' H; induction m; destruct i; simpl; intros.
    all: repeat match goal with H: match ?A with _ => _ end = _  |- _  => 
      destruct A eqn:?; inv H end; auto.
    all: match goal with |- _ = match ?A with _ => _ end =>
      destruct A eqn:H; auto 
    end.
    all: rewrite ?(filter1'_Empty_get _ _ _ Heqt0 H); auto.
    all: rewrite ?(filter1'_Empty_get _ _ _ Heqt1 H); auto.
  Qed.

  Section COMBINE.

  Fixpoint xcombine' {A B} (f: A -> option B) (m : tree' A) {struct m} : t B :=
      match m with
      | Node001 r => match xcombine' f r with
                                  | Empty => Empty
                                  | Nodes r' => Nodes (Node001 r')
                                  end
      | Node010 x => match f x with
                                   | None => Empty
                                   | Some y => Nodes (Node010 y)
                                   end
      | Node011 x r => match f x, xcombine' f r with
                                     | None, Empty => Empty
                                     | None, Nodes r' => Nodes (Node001 r')
                                     | Some y, Empty => Nodes (Node010 y)
                                     | Some y, Nodes r' => Nodes (Node011 y r')
                                     end
     | Node100 l => match xcombine' f l with
                                  | Empty => Empty
                                  | Nodes l' => Nodes (Node100 l')
                                  end
      | Node101 l r => match xcombine' f l, xcombine' f r with
                                     | Empty, Empty => Empty
                                     | Empty, Nodes r' => Nodes (Node001 r')
                                     | Nodes l', Empty => Nodes (Node100 l')
                                     | Nodes l', Nodes r' => Nodes (Node101 l' r')
                                     end
      | Node110 l x => match xcombine' f l, f x with
                                     | Empty, None => Empty
                                     | Empty, Some y => Nodes (Node010 y)
                                     | Nodes l', None => Nodes (Node100 l')
                                     | Nodes l', Some y => Nodes (Node110 l' y)
                                     end
      | Node111 l x r => match xcombine' f l, f x, xcombine' f r with
                                     | Empty, None, Empty => Empty
                                     | Empty, None, Nodes r' => Nodes (Node001 r')
                                     | Empty, Some y, Empty => Nodes (Node010 y)
                                     | Empty, Some y, Nodes r' => Nodes (Node011 y r')
                                     | Nodes l', None, Empty => Nodes (Node100 l')
                                     | Nodes l', None, Nodes r' => Nodes (Node101 l' r')
                                     | Nodes l', Some y, Empty => Nodes (Node110 l' y)
                                     | Nodes l', Some y, Nodes r' => Nodes (Node111 l' y r')
                                      end
      end.
 
  Lemma xgcombine' :
          forall A B (f: A -> option B),
          forall (m: tree' A) (i : positive),
          get i (xcombine' f m) = 
          match get' i m with None => None | Some x => f x end.
    Proof.
      unfold get.
      induction m; destruct i; intros; simpl;
      repeat match goal with |- context [xcombine' ?f ?m] =>
          destruct (xcombine' f m) eqn:?H; auto
      end;
      match goal with |- context [?f ?a] =>
         destruct (f a) eqn:?H; auto
      end.
    Qed.

  Definition xcombine {A B} (f: A -> option B) (m : t A) : t B :=
  match m with Empty => Empty | Nodes m' => xcombine' f m' end.

  Lemma xgcombine :
          forall A B (f: A -> option B),
          forall (m: tree A) (i : positive),
          get i (xcombine f m) = 
          match get i m with None => None | Some x => f x end.
  Proof.
   intros.
   destruct m as [|m].
   reflexivity.
   apply xgcombine'.
   Qed.

  Variables A B C: Type.
  Variable f: option A -> option B -> option C.
  Hypothesis f_none_none: f None None = None.

  Definition xcombine'_l := xcombine' (fun a => f (Some a) None).
  Definition xcombine_l := xcombine (fun a => f (Some a) None).
  Definition xcombine_r := xcombine (fun b => f None (Some b)).

  Fixpoint combine' (m1: tree' A) (m2: t B) {struct m1} : t C :=
    match m2 with
    | Empty => xcombine'_l m1
    | Nodes m2' => 
   let y := get' xH m2' in
    match m1 with 
      | Node001 r =>
           Node (xcombine_r (getleft' m2')) (f None y) (combine' r (getright' m2'))
      | Node010 x => 
           Node (xcombine_r (getleft' m2')) (f (Some x) y) (xcombine_r (getright' m2'))
      | Node011 x r =>
           Node (xcombine_r (getleft' m2')) (f (Some x) y) (combine' r (getright' m2'))
      | Node100 l => 
            Node (combine' l (getleft' m2')) (f None y) (xcombine_r (getright' m2'))
      | Node101 l r =>
            Node (combine' l (getleft' m2')) (f None y) (combine' r (getright' m2'))
      | Node110 l x =>
            Node (combine' l (getleft' m2')) (f (Some x) y) (xcombine_r (getright' m2'))
      | Node111 l x r =>
            Node (combine' l (getleft' m2')) (f (Some x) y) (combine' r (getright' m2'))
      end
    end.

  Definition combine (m1: t A) (m2: t B) : t C :=
  match m1 with Empty => xcombine_r m2 | Nodes m1' => combine' m1' m2 end.

  Lemma combine'_Empty: 
   forall m, combine' m Empty = xcombine'_l m.
  Proof. induction m; simpl; auto. Qed.

 Lemma combine_equation: 
  forall l1 x1 r1 l2 x2 r2,
    combine (Node l1 x1 r1) (Node l2 x2 r2) = 
    Node (combine l1 l2) (f x1 x2) (combine r1 r2).
 Proof.
  intros.
  unfold combine at 1.
  unfold Node at 1.
  destruct l1, x1, r1, l2, x2, r2; simpl; 
   rewrite ?f_none_none, ?combine'_Empty; auto.
 Qed.

  Theorem gcombine:
      forall (m1: t A) (m2: t B) (i: positive),
      get i (combine m1 m2) = f (get i m1) (get i m2).
  Proof.
    intros.
    revert m1 m2; induction i; intros.
  -
    rewrite (asNode m1) at 2.  rewrite get_xI_Node.
    rewrite (asNode m2) at 2.  rewrite get_xI_Node.
    rewrite <- IHi; clear IHi.
    rewrite (asNode m1) at 1.
    rewrite (asNode m2) at 1.
    rewrite combine_equation. rewrite get_xI_Node. auto.
  -
    rewrite (asNode m1) at 2.  rewrite get_xO_Node.
    rewrite (asNode m2) at 2.  rewrite get_xO_Node.
    rewrite <- IHi; clear IHi.
    rewrite (asNode m1) at 1.
    rewrite (asNode m2) at 1.
    rewrite combine_equation. rewrite get_xO_Node. auto.
  -
    rewrite (asNode m1) at 1.
    rewrite (asNode m2) at 1.
    rewrite combine_equation. rewrite get_xH_Node. auto.
 Qed.

  End COMBINE.

  Lemma xcombine_lr :
    forall (A B: Type) (f g : option A -> option A -> option B) (m : t A),
    (forall (i j : option A), f i j = g j i) ->
    xcombine_l f m = xcombine_r g m.
    Proof.
      intros. unfold xcombine_l, xcombine_r. f_equal.
      apply FunctionalExtensionality.functional_extensionality; intro x.
      apply H.
    Qed.

  Theorem combine_commut:
    forall (A B: Type) (f g: option A -> option A -> option B)
    (f_none_none: f None None = None),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Proof.
    intros.
    apply extensionality. red. intro.
    rewrite !gcombine; auto.
    rewrite <- H; auto.
 Qed.
    
    Fixpoint xelements (A : Type) (m : tree' A) (i : positive)
                       (k: list (positive * A)) {struct m}
                       : list (positive * A) :=
      match m with
      | Node001 r => xelements r (xI i) k
      | Node010 x => (prev i, x) :: k
      | Node011 x r => (prev i, x) :: xelements r (xI i) k
      | Node100 l => xelements l (xO i) k
      | Node101 l r => xelements l (xO i) (xelements r (xI i) k)
      | Node110 l x => xelements l (xO i) ((prev i, x)::k)
      | Node111 l x r => xelements l (xO i) ((prev i, x):: (xelements r (xI i) k))
      end.

  Definition elements (A: Type) (m : t A) := 
   match m with Empty => nil | Nodes m' => xelements m' xH nil end.

  Remark xelements_append:
    forall A (m: tree' A) i k1 k2,
    xelements m i (k1 ++ k2) = xelements m i k1 ++ k2.
  Proof.
    induction m; intros; simpl; auto.
  - f_equal; auto.
  - rewrite <- IHm1. f_equal. apply IHm2.
  - rewrite <- IHm. simpl. auto.
  - rewrite <- IHm1. simpl. f_equal. f_equal. auto.
  Qed.

  Remark xelements_append':
    forall A (m: tree' A) i k,
    xelements m i k = xelements m i nil ++ k.
  Proof.
    intros.
    rewrite <- (app_nil_l k). rewrite xelements_append. auto.
  Qed.

  Remark xelements_cons:
    forall A (m: tree' A) i y k,
    xelements m i (y::k) = xelements m i (y::nil) ++ k.
  Proof.
    intros.
    change (y::k) with ((y::nil)++k). apply xelements_append.
  Qed.

    Lemma xelements_incl:
      forall (A: Type) (m: tree' A) (i : positive) k x,
      In x k -> In x (xelements m i k).
    Proof.
      induction m; intros; simpl; auto.
      apply IHm. simpl; auto.
      apply IHm1. right. apply IHm2. auto.
    Qed.

    Lemma xelements_correct:
      forall (A: Type) (m: tree' A) (i j : positive) (v: A) k,
      get' i m = Some v -> In (prev (prev_append i j), v) (xelements m j k).
    Proof.
      induction m; destruct i; intros;
      try apply (IHm _ _ _ _ H); 
      try solve [inv H; simpl; auto].
      -  simpl. rewrite xelements_append'.
         apply in_app; right; auto.
      - simpl. inv H. rewrite xelements_cons.
          apply in_app; left; auto.
          apply xelements_incl. left; auto.
     - simpl. simpl in H. rewrite xelements_cons.
          apply in_app; right. auto.
     - inv H. simpl. rewrite xelements_cons.
          apply in_app; left.
          apply xelements_incl. left; auto.
    Qed.

  Theorem elements_correct:
    forall (A: Type) (m: t A) (i: positive) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    intros A m i v H.
    destruct m as [|m]. inv H.
    generalize (xelements_correct m i xH nil H). rewrite prev_append_prev. exact id.
  Qed.

  Lemma in_xelements:
    forall (A: Type) (m: tree' A) (i k: positive) (v: A) ,
    In (k, v) (xelements m i nil) ->
    exists j, k = prev (prev_append j i) /\ get' j m = Some v.
  Proof.
    induction m; simpl; intros.
  - apply IHm in H.  destruct H as [j [? ?]].  exists (xI j). simpl; auto.
  - destruct H; inv H. exists xH; simpl; auto.
  - destruct H. inv H. exists xH; simpl; auto. apply IHm in H. destruct H as [j [? ?]]. exists (xI j); simpl; auto.
  - apply IHm in H. destruct H as [j [? ?]]. exists (xO j); simpl; auto.
  - rewrite xelements_append' in H.
     apply in_app in H.
     destruct H.
     apply IHm1 in H. destruct H as [j [? ?]]. exists (xO j); split; auto.
     apply IHm2 in H. destruct H as [j [? ?]]. exists (xI j); split; auto.
  - rewrite xelements_append' in H.
     apply in_app in H.
     destruct H.
     apply IHm in H. destruct H as [j [? ?]]. exists (xO j); split; auto.
     destruct H; inv H. exists xH; simpl; auto.
  - rewrite xelements_cons in H.
     rewrite xelements_append' in H.
     rewrite !in_app in H.
     destruct H as [[?|?]|?].
     apply IHm1 in H. destruct H as [j [? ?]]. exists (xO j); split; auto.
     destruct H; inv H; exists xH; simpl; auto.
     apply IHm2 in H. destruct H as [j [? ?]]. exists (xI j); split; auto.
  Qed.

  Theorem elements_complete:
    forall (A: Type) (m: t A) (i: positive) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Proof.
    intros.
    destruct m as [|m]. inv H. apply in_xelements in H.
    destruct H as [j [? ?]]. subst. rewrite prev_append_prev. simpl. auto.
  Qed.

  Definition xkeys (A: Type) (m: tree' A) (i: positive) :=
    List.map (@fst positive A) (xelements m i nil).

  Lemma in_xkeys:
    forall (A: Type) (m: tree' A) (i k: positive),
    In k (xkeys m i) ->
    (exists j, k = prev (prev_append j i)).
  Proof.
    unfold xkeys; intros.
    apply (list_in_map_inv) in H. destruct H as ((j, v) & -> & H).
    exploit in_xelements; eauto. intros (k & P & Q). exists k; auto.
  Qed.

  Lemma xelements_keys_norepet:
    forall (A: Type) (m: tree' A) (i: positive),
    list_norepet (xkeys m i).
  Proof.
    intro.
    assert (NOTIN1: forall (m: tree' A) i, ~ In (prev i) (xkeys m (xO i))). {
          intros. intro. apply in_xkeys in H. destruct H as [j EQ].
          rewrite prev_append_prev in EQ. simpl in EQ. apply prev_append_inj in EQ. discriminate. }
    assert (NOTIN2: forall (m: tree' A) i, ~ In (prev i) (xkeys m (xI i))). {
          intros. intro. apply in_xkeys in H. destruct H as [j EQ].
          rewrite prev_append_prev in EQ. simpl in EQ. apply prev_append_inj in EQ. discriminate. }
    assert (DISJ: forall (m1 m2: tree' A) i x, In x (xkeys m1 (xO i)) -> In x (xkeys m2 (xI i)) -> False).
    { intros.
       apply in_xkeys in H; destruct H as [j1 EQ1].
       apply in_xkeys in H0; destruct H0 as [j2 EQ2].
      rewrite prev_append_prev in *. simpl in *. rewrite EQ2 in EQ1. apply prev_append_inj in EQ1. discriminate. }
    unfold xkeys.
    induction m; simpl; intros; auto.
  - constructor. intro H; inv H. constructor.
  - constructor; auto.
      apply NOTIN2.
  - rewrite xelements_append'.
     rewrite List.map_app.
     apply list_norepet_app. split; [|split]; auto.
     intros j j0 ? ? ?; subst j0.
     eapply DISJ; eauto.
  - rewrite xelements_append'.
     rewrite List.map_app.
     apply list_norepet_app. split; [|split]; auto.
     constructor; auto. constructor.
     intros j j0 ? ? ?; subst j0.
     destruct H0; inv H0. simpl in H.
     apply NOTIN1 in H; auto.
  - rewrite xelements_append'.
     rewrite List.map_app.
     apply list_norepet_app. split; [|split]; auto.
     simpl.
     constructor; auto.
     eapply NOTIN2; auto.
     intros j j0 ? ? ?; subst j0.
     simpl in H0. destruct H0. subst. eapply NOTIN1; eauto.
     eapply DISJ; eauto.
  Qed.

  Theorem elements_keys_norepet:
    forall (A: Type) (m: t A),
    list_norepet (List.map (@fst elt A) (elements m)).
  Proof.
    intros.
    destruct m as [|m]. constructor.
    apply (xelements_keys_norepet m xH).
  Qed.

  Theorem elements_canonical_order':
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i, option_rel R (get i m) (get i n)) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
  Proof.
    intros until n.
    destruct n as [|n], m as [|m].
    - intros; constructor.
    - intros. destruct (tree'_not_empty m) as [i [x H0]]. specialize (H i); unfold get in H; rewrite H0 in H; inv H.
    - intros. destruct (tree'_not_empty n) as [i [x H0]]. specialize (H i); unfold get in H; rewrite H0 in H; inv H.
    -
    unfold elements. generalize 1%positive. revert m n.
    induction m; destruct n; intros;
    try solve [specialize (H xH); inv H].
    all: try solve [destruct (tree'_not_empty m) as [i [x H0]]; specialize (H (xI i)); simpl in H; rewrite H0 in H; inv H].
    all: try solve [destruct (tree'_not_empty n) as [i [x H0]]; specialize (H (xI i)); simpl in H; rewrite H0 in H; inv H].
    all: try solve [destruct (tree'_not_empty m) as [i [x H0]]; specialize (H (xO i)); simpl in H; rewrite H0 in H; inv H].
    all: try solve [destruct (tree'_not_empty n) as [i [x H0]]; specialize (H (xO i)); simpl in H; rewrite H0 in H; inv H].
    all: try solve [destruct (tree'_not_empty n1) as [i [x H0]]; specialize (H (xO i)); simpl in H; rewrite H0 in H; inv H].
    all: try solve [destruct (tree'_not_empty n2) as [i [x H0]]; specialize (H (xI i)); simpl in H; rewrite H0 in H; inv H].
    all: try solve [destruct (tree'_not_empty m1) as [i [x H0]]; specialize (H (xO i)); simpl in H; rewrite H0 in H; inv H].
    all: try solve [destruct (tree'_not_empty m2) as [i [x H0]]; specialize (H (xI i)); simpl in H; rewrite H0 in H; inv H].
    + apply (IHm n (xI p)). intro i. apply (H (xI i)).
    + simpl. specialize (H xH); simpl in H. inv H. constructor. split. auto. auto. constructor.
    + simpl; constructor. split. auto. simpl. specialize (H xH); simpl in H. inv H; auto. apply (IHm n (xI p)). intro. apply (H (xI i)).
    + apply (IHm n (xO p)). intro i. apply (H (xO i)).
    + simpl. rewrite !(xelements_append' _ _ (xelements _ _ _)). apply list_forall2_app.
        apply (IHm1 _ (xO p)). intro. apply (H (xO i)).
        apply (IHm2 _ (xI p)). intro. apply (H (xI i)).
    + simpl. rewrite !(xelements_append' _ _ (_ :: _)). apply list_forall2_app.
         apply (IHm n (xO p)). intro i. apply (H (xO i)).
         simpl. constructor. split. auto. specialize (H xH). simpl in H. inv H; auto. constructor.
    + simpl.
        rewrite !(xelements_cons _ _ _ (xelements _ _ _)).
        rewrite !(xelements_append' _ _ (_::_)).
        repeat apply list_forall2_app. 
         apply (IHm1 n1 (xO p)). intro i. apply (H (xO i)).
        constructor. split; auto. specialize (H xH). simpl in H. inv H; auto.
        constructor.
         apply (IHm2 _ (xI p)). intro i. apply (H (xI i)).
  Qed.

  Theorem elements_canonical_order:
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
    (forall i x, get i m = Some x -> exists y, get i n = Some y /\ R x y) ->
    (forall i y, get i n = Some y -> exists x, get i m = Some x /\ R x y) ->
    list_forall2
      (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
      (elements m) (elements n).
  Proof.
    intros. apply elements_canonical_order'.
    intros. destruct (get i m) as [x|] eqn:GM.
    exploit H; eauto. intros (y & P & Q). rewrite P; constructor; auto.
    destruct (get i n) as [y|] eqn:GN.
    exploit H0; eauto. intros (x & P & Q). congruence.
    constructor.
  Qed.

  Theorem elements_extensional:
    forall (A: Type) (m n: t A),
    (forall i, get i m = get i n) ->
    elements m = elements n.
  Proof.
    intros.
    exploit (@elements_canonical_order' _ _ (fun (x y: A) => x = y) m n).
    intros. rewrite H. destruct (get i n); constructor; auto.
    induction 1. auto. destruct a1 as [a2 a3]; destruct b1 as [b2 b3]; simpl in *.
    destruct H0. congruence.
  Qed.

  Definition elements' (A: Type) (m : t A) (i: positive) := 
   match m with Empty => nil | Nodes m' => xelements m' i nil end.

  Lemma xelements_remove:
    forall (A: Type) v (m: tree' A) i j,
    get' i m = Some v ->
    exists l1 l2,
    xelements m j nil = l1 ++ (prev (prev_append i j), v) :: l2
    /\ elements' (rem' i m) j = l1 ++ l2.
  Proof.
    induction m; destruct i; intros; try discriminate.
  - destruct (IHm i (xI j) H) as [l1 [l2 [? ?]]]. do 2 eexists; split; eauto.
     simpl. destruct (rem' i m); simpl in *; auto.
  - simpl in H; inv H. exists nil, nil. split; simpl; auto.
  - destruct (IHm i (xI j) H) as [l1 [l2 [? ?]]]. exists ((prev j,a)::l1), l2.
      simpl; split. f_equal. auto. destruct (rem' i m); simpl in *; f_equal; auto.
  - simpl in H; inv H. exists nil. eexists.  simpl; auto.
  - destruct (IHm i (xO j) H) as [l1 [l2 [? ?]]]. do 2 eexists; split; eauto.
     simpl. destruct (rem' i m); simpl in *; auto.
  -  destruct (IHm2 i (xI j) H) as [l1 [l2 [? ?]]].
      simpl. exists (xelements m1 j~0 l1), l2.
      split.
      rewrite xelements_append'. rewrite (xelements_append' _ _ l1).
      rewrite <- app_assoc. f_equal. auto.
      destruct (rem' i m2); simpl in *; auto.
      rewrite (xelements_append' _ _ l1).
      rewrite <- app_assoc. rewrite <- H1; auto. rewrite app_nil_r. auto.
      rewrite xelements_append'.
      rewrite (xelements_append' _ _ l1).
      rewrite <- app_assoc. f_equal. auto. 
  - destruct (IHm1 i (xO j) H) as [l1 [l2 [? ?]]].
      simpl. exists l1, (l2 ++ xelements m2 j~1 nil).
      split. rewrite xelements_append'.
      rewrite H0.  rewrite <- app_assoc. f_equal.
      destruct (rem' i m1); simpl in *; auto. rewrite app_assoc, <- H1. auto.
      rewrite app_assoc, <- H1. rewrite <- xelements_append'. auto.
  - destruct (IHm i (xO j) H) as [l1 [l2 [? ?]]].
     simpl. exists l1. eexists. split.
     rewrite xelements_append', H0. rewrite <- app_assoc.
     f_equal. simpl. f_equal. rewrite app_assoc. rewrite <- H1.
     destruct (rem' i m); simpl; auto. rewrite <- xelements_append'; auto.
  - simpl in *. inv H. do 2 eexists. split. 
     rewrite xelements_append'. reflexivity.
     rewrite app_nil_r; auto.
  - destruct (IHm2 i (xI j) H) as [l1 [l2 [? ?]]].
     simpl. do 2 eexists. split. rewrite H0.
     rewrite xelements_append'.
     rewrite <- app_assoc. f_equal. change (?a::?b++?c) with ((a::b)++c).
     reflexivity.
     rewrite <- app_assoc. simpl. rewrite <- H1.
     destruct (rem' i m2); simpl; rewrite <- xelements_append; auto.
  - destruct (IHm1 i (xO j) H) as [l1 [l2 [? ?]]].
     simpl. do 2 eexists. split.
     rewrite xelements_append'. rewrite H0.
     rewrite <- app_assoc. f_equal. simpl. f_equal.
     rewrite app_assoc. rewrite <- H1.
     destruct (rem' i m1); simpl; auto. rewrite <- xelements_append; auto.
  - inv H. do 2 eexists. simpl.
     rewrite xelements_cons.
     rewrite (xelements_append' _ _ (xelements _ _ _)). 
     rewrite (xelements_append' _ _ (_ :: _)). rewrite <- app_assoc. 
     simpl. split. f_equal. f_equal.
  Qed.

  Theorem elements_remove:
    forall (A: Type) i v (m: t A),
    get i m = Some v ->
    exists l1 l2, elements m = l1 ++ (i,v) :: l2 /\ elements (remove i m) = l1 ++ l2.
  Proof.
    intros.
    destruct m as [|m]. inv H.
    apply xelements_remove with (j:=xH) in H.
     destruct H as [l1 [l2 [? ?]]].
    rewrite prev_append_prev in H. eauto.
  Qed.

  Fixpoint xfold (A B: Type) (f: B -> positive -> A -> B)
                 (i: positive) (m: tree' A) (v: B) {struct m} : B :=
    match m with
    | Node001 r => xfold f (xI i) r v
    | Node010 x => f v (prev i) x
    | Node011 x r => xfold f (xI i) r (f v (prev i) x)
    | Node100 l => xfold f (xO i) l v
    | Node101 l r => xfold f (xI i) r (xfold f (xO i) l v)
    | Node110 l x => f (xfold f (xO i) l v) (prev i) x
    | Node111 l x r => xfold f (xI i) r (f (xfold f (xO i) l v) (prev i) x)
    end.

  Definition fold (A B : Type) (f: B -> positive -> A -> B) (m: t A) (v: B) :=
   match m with Empty => v | Nodes m' => xfold f xH m' v end.

  Lemma xfold_xelements:
    forall (A B: Type) (f: B -> positive -> A -> B) m i v l,
    List.fold_left (fun a p => f a (fst p) (snd p)) l (xfold f i m v) =
    List.fold_left (fun a p => f a (fst p) (snd p)) (xelements m i l) v.
  Proof.
    induction m; intros; simpl; auto.
    rewrite <- IHm1, <- IHm2; auto.
    rewrite <- IHm; auto.
    rewrite <- IHm1. simpl. rewrite <- IHm2; auto.
  Qed.

  Theorem fold_spec:
    forall (A B: Type) (f: B -> positive -> A -> B) (v: B) (m: t A),
    fold f m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros.
    destruct m as [|m]. simpl. auto.
     unfold fold, elements. rewrite <- xfold_xelements. auto.
  Qed.

  Fixpoint xfold1 {A B: Type} (f: B -> A -> B) (m: tree' A) (v: B) {struct m} : B :=
    match m with
    | Node001 r => xfold1 f r v
    | Node010 x => f v x
    | Node011 x r => xfold1 f r (f v x)
    | Node100 l => xfold1 f l v
    | Node101 l r => xfold1 f r (xfold1 f l v)
    | Node110 l x => f (xfold1 f l v) x
    | Node111 l x r => xfold1 f r (f (xfold1 f l v) x)
    end.


  Definition fold1 (A B: Type) (f: B -> A -> B) (m: t A) (v: B) : B :=
    match m with Empty => v | Nodes m' => xfold1 f m' v end.

  Lemma xfold1_xelements:
    forall (A B: Type) (f: B -> A -> B) m i v l,
    List.fold_left (fun a p => f a (snd p)) l (xfold1 f m v) =
    List.fold_left (fun a p => f a (snd p)) (xelements m i l) v.
  Proof.
    induction m; simpl; intros; auto.
    rewrite <- IHm1. rewrite <- IHm2. auto.
    rewrite <- IHm. auto. 
    rewrite <- IHm1. simpl. rewrite <- IHm2. auto.
  Qed.

  Theorem fold1_spec:
    forall (A B: Type) (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.
  Proof.
    intros. destruct m as [|m]. reflexivity.
    apply xfold1_xelements with (l := @nil (positive * A)).
  Qed.

  Arguments empty A : simpl never.
  Arguments get {A} p m : simpl never.
  Arguments set {A} p x m : simpl never.
  Arguments remove {A} p m : simpl never.

End PTree.

(** * An implementation of maps over type [positive] *)

Module PMap <: MAP.
  Definition elt := positive.
  Definition elt_eq := peq.

  Definition t (A : Type) : Type := (A * PTree.t A)%type.

  Definition init (A : Type) (x : A) :=
    (x, PTree.empty A).

  Definition get (A : Type) (i : positive) (m : t A) :=
    match PTree.get i (snd m) with
    | Some x => x
    | None => fst m
    end.

  Definition set (A : Type) (i : positive) (x : A) (m : t A) :=
    (fst m, PTree.set i x (snd m)).

  Theorem gi:
    forall (A: Type) (i: positive) (x: A), get i (init x) = x.
  Proof.
    intros. unfold init. unfold get. simpl. auto.
  Qed.

  Theorem gss:
    forall (A: Type) (i: positive) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite PTree.gss. auto.
  Qed.

  Theorem gso:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get. unfold set. simpl. rewrite PTree.gso; auto.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: positive) (x: A) (m: t A),
    get i (set j x m) = if peq i j then x else get i m.
  Proof.
    intros. destruct (peq i j).
     rewrite e. apply gss. auto.
     apply gso. auto.
  Qed.

  Theorem gsident:
    forall (A: Type) (i j: positive) (m: t A),
    get j (set i (get i m) m) = get j m.
  Proof.
    intros. destruct (peq i j).
     rewrite e. rewrite gss. auto.
     rewrite gso; auto.
  Qed.

  Definition map (A B : Type) (f : A -> B) (m : t A) : t B :=
    (f (fst m), PTree.map1 f (snd m)).

  Theorem gmap:
    forall (A B: Type) (f: A -> B) (i: positive) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold map. unfold get. simpl. rewrite PTree.gmap1.
    unfold option_map. destruct (PTree.get i (snd m)); auto.
  Qed.

  Theorem set2:
    forall (A: Type) (i: elt) (x y: A) (m: t A),
    set i y (set i x m) = set i y m.
  Proof.
    intros. unfold set. simpl. decEq. apply PTree.set2.
  Qed.

  Arguments init A : simpl never.
  Arguments get {A} i m : simpl never.
  Arguments set {A} i x m : simpl never.

End PMap.

(** * An implementation of maps over any type that injects into type [positive] *)

Module Type INDEXED_TYPE.
  Parameter t: Type.
  Parameter index: t -> positive.
  Axiom index_inj: forall (x y: t), index x = index y -> x = y.
  Parameter eq: forall (x y: t), {x = y} + {x <> y}.
End INDEXED_TYPE.

Module IMap(X: INDEXED_TYPE).

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t : Type -> Type := PMap.t.
  Definition init (A: Type) (x: A) := PMap.init x.
  Definition get (A: Type) (i: X.t) (m: t A) := PMap.get (X.index i) m.
  Definition set (A: Type) (i: X.t) (v: A) (m: t A) := PMap.set (X.index i) v m.
  Definition map (A B: Type) (f: A -> B) (m: t A) : t B := PMap.map f m.

  Lemma gi:
    forall (A: Type) (x: A) (i: X.t), get i (init x) = x.
  Proof.
    intros. unfold get, init. apply PMap.gi.
  Qed.

  Lemma gss:
    forall (A: Type) (i: X.t) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros. unfold get, set. apply PMap.gss.
  Qed.

  Lemma gso:
    forall (A: Type) (i j: X.t) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. unfold get, set. apply PMap.gso.
    red. intro. apply H. apply X.index_inj; auto.
  Qed.

  Lemma gsspec:
    forall (A: Type) (i j: X.t) (x: A) (m: t A),
    get i (set j x m) = if X.eq i j then x else get i m.
  Proof.
    intros. unfold get, set.
    rewrite PMap.gsspec.
    case (X.eq i j); intro.
    subst j. rewrite peq_true. reflexivity.
    rewrite peq_false. reflexivity.
    red; intro. elim n. apply X.index_inj; auto.
  Qed.

  Lemma gmap:
    forall (A B: Type) (f: A -> B) (i: X.t) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold map, get. apply PMap.gmap.
  Qed.

  Lemma set2:
    forall (A: Type) (i: elt) (x y: A) (m: t A),
    set i y (set i x m) = set i y m.
  Proof.
    intros. unfold set. apply PMap.set2.
  Qed.

End IMap.

Module ZIndexed.
  Definition t := Z.
  Definition index (z: Z): positive :=
    match z with
    | Z0 => xH
    | Zpos p => xO p
    | Zneg p => xI p
    end.
  Lemma index_inj: forall (x y: Z), index x = index y -> x = y.
  Proof.
    unfold index; destruct x; destruct y; intros;
    try discriminate; try reflexivity.
    congruence.
    congruence.
  Qed.
  Definition eq := zeq.
End ZIndexed.

Module ZMap := IMap(ZIndexed).

Module NIndexed.
  Definition t := N.
  Definition index (n: N): positive :=
    match n with
    | N0 => xH
    | Npos p => xO p
    end.
  Lemma index_inj: forall (x y: N), index x = index y -> x = y.
  Proof.
    unfold index; destruct x; destruct y; intros;
    try discriminate; try reflexivity.
    congruence.
  Qed.
  Lemma eq: forall (x y: N), {x = y} + {x <> y}.
  Proof.
    decide equality. apply peq.
  Qed.
End NIndexed.

Module NMap := IMap(NIndexed).

(** * An implementation of maps over any type with decidable equality *)

Module Type EQUALITY_TYPE.
  Parameter t: Type.
  Parameter eq: forall (x y: t), {x = y} + {x <> y}.
End EQUALITY_TYPE.

Module EMap(X: EQUALITY_TYPE) <: MAP.

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t (A: Type) := X.t -> A.
  Definition init (A: Type) (v: A) := fun (_: X.t) => v.
  Definition get (A: Type) (x: X.t) (m: t A) := m x.
  Definition set (A: Type) (x: X.t) (v: A) (m: t A) :=
    fun (y: X.t) => if X.eq y x then v else m y.
  Lemma gi:
    forall (A: Type) (i: elt) (x: A), init x i = x.
  Proof.
    intros. reflexivity.
  Qed.
  Lemma gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), (set i x m) i = x.
  Proof.
    intros. unfold set. case (X.eq i i); intro.
    reflexivity. tauto.
  Qed.
  Lemma gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> (set j x m) i = m i.
  Proof.
    intros. unfold set. case (X.eq i j); intro.
    congruence. reflexivity.
  Qed.
  Lemma gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Proof.
    intros. unfold get, set, elt_eq. reflexivity.
  Qed.
  Lemma gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Proof.
    intros. unfold get, set. case (X.eq j i); intro.
    congruence. reflexivity.
  Qed.
  Definition map (A B: Type) (f: A -> B) (m: t A) :=
    fun (x: X.t) => f(m x).
  Lemma gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros. unfold get, map. reflexivity.
  Qed.
End EMap.

(** * A partial implementation of trees over any type that injects into type [positive] *)

Module ITree(X: INDEXED_TYPE).

  Definition elt := X.t.
  Definition elt_eq := X.eq.
  Definition t : Type -> Type := PTree.t.

  Definition empty (A: Type): t A := PTree.empty A.
  Definition get (A: Type) (k: elt) (m: t A): option A := PTree.get (X.index k) m.
  Definition set (A: Type) (k: elt) (v: A) (m: t A): t A := PTree.set (X.index k) v m.
  Definition remove (A: Type) (k: elt) (m: t A): t A := PTree.remove (X.index k) m.

  Theorem gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Proof.
    intros. apply PTree.gempty.
  Qed.
  Theorem gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof.
    intros. apply PTree.gss.
  Qed.
  Theorem gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros. apply PTree.gso. red; intros; elim H; apply X.index_inj; auto.
  Qed.
  Theorem gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Proof.
    intros. destruct (elt_eq i j). subst j; apply gss. apply gso; auto.
  Qed.
  Theorem grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Proof.
    intros. apply PTree.grs.
  Qed.
  Theorem gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
    intros. apply PTree.gro. red; intros; elim H; apply X.index_inj; auto.
  Qed.
  Theorem grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros. destruct (elt_eq i j). subst j; apply grs. apply gro; auto.
  Qed.

  Definition beq: forall (A: Type), (A -> A -> bool) -> t A -> t A -> bool := PTree.beq.
  Theorem beq_sound:
    forall (A: Type) (eqA: A -> A -> bool) (t1 t2: t A),
    beq eqA t1 t2 = true ->
    forall (x: elt),
     match get x t1, get x t2 with
     | None, None => True
     | Some y1, Some y2 => eqA y1 y2 = true
     | _, _ => False
    end.
  Proof.
    unfold beq, get. intros. rewrite PTree.beq_correct in H. apply H.
  Qed.

  Definition combine: forall (A B C: Type), (option A -> option B -> option C) -> t A -> t B -> t C := PTree.combine.
  Theorem gcombine:
    forall (A B C: Type) (f: option A -> option B -> option C),
    f None None = None ->
    forall (m1: t A) (m2: t B) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).
  Proof.
    intros. apply PTree.gcombine. auto.
  Qed.
End ITree.

Module ZTree := ITree(ZIndexed).

(** * Additional properties over trees *)

Module Tree_Properties(T: TREE).

(** Two induction principles over [fold]. *)

Section TREE_FOLD_IND.

Variables V A: Type.
Variable f: A -> T.elt -> V -> A.
Variable P: T.t V -> A -> Type.
Variable init: A.
Variable m_final: T.t V.

Hypothesis H_base:
  forall m,
  (forall k, T.get k m = None) ->
  P m init.

Hypothesis H_rec:
  forall m a k v,
  T.get k m = Some v -> T.get k m_final = Some v ->
  P (T.remove k m) a -> P m (f a k v).

Let f' (p : T.elt * V) (a: A) := f a (fst p) (snd p).

Let P' (l: list (T.elt * V)) (a: A) : Type :=
  forall m, (forall k v, In (k, v) l <-> T.get k m = Some v) -> P m a.

Let H_base':
  P' nil init.
Proof.
  intros m EQV. apply H_base.
  intros. destruct (T.get k m) as [v|] eqn:G; auto.
  apply EQV in G. contradiction.
Qed.

Let H_rec':
  forall k v l a,
  ~In k (List.map fst l) ->
  T.get k m_final = Some v ->
  P' l a ->
  P' ((k, v) :: l) (f a k v).
Proof.
  unfold P'; intros k v l a NOTIN FINAL HR m EQV.
  set (m0 := T.remove k m).
  apply H_rec.
- apply EQV. simpl; auto.
- auto.
- apply HR. intros k' v'. rewrite T.grspec. split; intros; destruct (T.elt_eq k' k).
  + subst k'. elim NOTIN. change k with (fst (k, v')). apply List.in_map; auto.
  + apply EQV. simpl; auto.
  + congruence.
  + apply EQV in H. simpl in H. intuition congruence.
Qed.

Lemma fold_ind_aux:
  forall l,
  (forall k v, In (k, v) l -> T.get k m_final = Some v) ->
  list_norepet (List.map fst l) ->
  P' l (List.fold_right f' init l).
Proof.
  induction l as [ | [k v] l ]; simpl; intros FINAL NOREPET.
- apply H_base'.
- apply H_rec'.
  + inv NOREPET. auto.
  + apply FINAL. auto.
  + apply IHl. auto. inv NOREPET; auto.
Defined.

Theorem fold_ind:
  P m_final (T.fold f m_final init).
Proof.
  intros.
  set (l' := List.rev (T.elements m_final)).
  assert (P' l' (List.fold_right f' init l')).
  { apply fold_ind_aux.
    intros. apply T.elements_complete. apply List.in_rev. auto.
    unfold l'; rewrite List.map_rev. apply list_norepet_rev. apply T.elements_keys_norepet. }
  unfold l', f' in X; rewrite fold_left_rev_right in X.
  rewrite T.fold_spec. apply X.
  intros; simpl. rewrite <- List.in_rev.
  split. apply T.elements_complete. apply T.elements_correct.
Defined.

End TREE_FOLD_IND.

Section TREE_FOLD_REC.

Variables V A: Type.
Variable f: A -> T.elt -> V -> A.
Variable P: T.t V -> A -> Prop.
Variable init: A.
Variable m_final: T.t V.

Hypothesis P_compat:
  forall m m' a,
  (forall x, T.get x m = T.get x m') ->
  P m a -> P m' a.

Hypothesis H_base:
  P (T.empty _) init.

Hypothesis H_rec:
  forall m a k v,
  T.get k m = None -> T.get k m_final = Some v -> P m a -> P (T.set k v m) (f a k v).

Theorem fold_rec:
  P m_final (T.fold f m_final init).
Proof.
  apply fold_ind. 
- intros. apply P_compat with (T.empty V); auto.
  + intros. rewrite T.gempty. auto.
- intros. apply P_compat with (T.set k v (T.remove k m)).
  + intros. rewrite T.gsspec, T.grspec. destruct (T.elt_eq x k); auto. congruence.
  + apply H_rec; auto. apply T.grs.
Qed.

End TREE_FOLD_REC.

(** A nonnegative measure over trees *)

Section MEASURE.

Variable V: Type.

Definition cardinal (x: T.t V) : nat := List.length (T.elements x).

Theorem cardinal_remove:
  forall x m y, T.get x m = Some y -> (cardinal (T.remove x m) < cardinal m)%nat.
Proof.
  unfold cardinal; intros.
  exploit T.elements_remove; eauto. intros (l1 & l2 & P & Q).
  rewrite P, Q. rewrite ! app_length. simpl. lia.
Qed.

Theorem cardinal_set:
  forall x m y, T.get x m = None -> (cardinal m < cardinal (T.set x y m))%nat.
Proof.
  intros. set (m' := T.set x y m).
  replace (cardinal m) with (cardinal (T.remove x m')).
  apply cardinal_remove with y. unfold m'; apply T.gss.
  unfold cardinal. f_equal. apply T.elements_extensional.
  intros. unfold m'. rewrite T.grspec, T.gsspec.
  destruct (T.elt_eq i x); auto. congruence.
Qed.

End MEASURE.

(** Forall and exists *)

Section FORALL_EXISTS.

Variable A: Type.

Definition for_all (m: T.t A) (f: T.elt -> A -> bool) : bool :=
  T.fold (fun b x a => b && f x a) m true.

Lemma for_all_correct:
  forall m f,
  for_all m f = true <-> (forall x a, T.get x m = Some a -> f x a = true).
Proof.
  intros m0 f.
  unfold for_all. apply fold_rec; intros.
- (* Extensionality *)
  rewrite H0. split; intros. rewrite <- H in H2; auto. rewrite H in H2; auto.
- (* Base case *)
  split; intros. rewrite T.gempty in H0; congruence. auto.
- (* Inductive case *)
  split; intros.
  destruct (andb_prop _ _ H2). rewrite T.gsspec in H3. destruct (T.elt_eq x k).
  inv H3. auto.
  apply H1; auto.
  apply andb_true_intro. split.
  rewrite H1. intros. apply H2. rewrite T.gso; auto. congruence.
  apply H2. apply T.gss.
Qed.

Definition exists_ (m: T.t A) (f: T.elt -> A -> bool) : bool :=
  T.fold (fun b x a => b || f x a) m false.

Lemma exists_correct:
  forall m f,
  exists_ m f = true <-> (exists x a, T.get x m = Some a /\ f x a = true).
Proof.
  intros m0 f.
  unfold exists_. apply fold_rec; intros.
- (* Extensionality *)
  rewrite H0. split; intros (x0 & a0 & P & Q); exists x0; exists a0; split; auto; congruence.
- (* Base case *)
  split; intros. congruence. destruct H as (x & a & P & Q). rewrite T.gempty in P; congruence.
- (* Inductive case *)
  split; intros.
  destruct (orb_true_elim _ _ H2).
  rewrite H1 in e. destruct e as (x1 & a1 & P & Q).
  exists x1; exists a1; split; auto. rewrite T.gso; auto. congruence.
  exists k; exists v; split; auto. apply T.gss.
  destruct H2 as (x1 & a1 & P & Q). apply orb_true_intro.
  rewrite T.gsspec in P. destruct (T.elt_eq x1 k).
  inv P. right; auto.
  left. apply H1. exists x1; exists a1; auto.
Qed.

Remark exists_for_all:
  forall m f,
  exists_ m f = negb (for_all m (fun x a => negb (f x a))).
Proof.
  intros. unfold exists_, for_all. rewrite ! T.fold_spec.
  change false with (negb true). generalize (T.elements m) true.
  induction l; simpl; intros.
  auto.
  rewrite <- IHl. f_equal.
  destruct b; destruct (f (fst a) (snd a)); reflexivity.
Qed.

Remark for_all_exists:
  forall m f,
  for_all m f = negb (exists_ m (fun x a => negb (f x a))).
Proof.
  intros. unfold exists_, for_all. rewrite ! T.fold_spec.
  change true with (negb false). generalize (T.elements m) false.
  induction l; simpl; intros.
  auto.
  rewrite <- IHl. f_equal.
  destruct b; destruct (f (fst a) (snd a)); reflexivity.
Qed.

Lemma for_all_false:
  forall m f,
  for_all m f = false <-> (exists x a, T.get x m = Some a /\ f x a = false).
Proof.
  intros. rewrite for_all_exists.
  rewrite negb_false_iff. rewrite exists_correct.
  split; intros (x & a & P & Q); exists x; exists a; split; auto.
  rewrite negb_true_iff in Q. auto.
  rewrite Q; auto.
Qed.

Lemma exists_false:
  forall m f,
  exists_ m f = false <-> (forall x a, T.get x m = Some a -> f x a = false).
Proof.
  intros. rewrite exists_for_all.
  rewrite negb_false_iff. rewrite for_all_correct.
  split; intros. apply H in H0. rewrite negb_true_iff in H0. auto. rewrite H; auto.
Qed.

End FORALL_EXISTS.

(** More about [beq] *)

Section BOOLEAN_EQUALITY.

Variable A: Type.
Variable beqA: A -> A -> bool.

Theorem beq_false:
  forall m1 m2,
  T.beq beqA m1 m2 = false <->
  exists x, match T.get x m1, T.get x m2 with
            | None, None => False
            | Some a1, Some a2 => beqA a1 a2 = false
            | _, _ => True
            end.
Proof.
  intros; split; intros.
- (* beq = false -> existence *)
  set (p1 := fun x a1 => match T.get x m2 with None => false | Some a2 => beqA a1 a2 end).
  set (p2 := fun x a2 => match T.get x m1 with None => false | Some a1 => beqA a1 a2 end).
  destruct (for_all m1 p1) eqn:F1; [destruct (for_all m2 p2) eqn:F2 | idtac].
  + cut (T.beq beqA m1 m2 = true). congruence.
    rewrite for_all_correct in *. rewrite T.beq_correct; intros.
    destruct (T.get x m1) as [a1|] eqn:X1.
    generalize (F1 _ _ X1). unfold p1. destruct (T.get x m2); congruence.
    destruct (T.get x m2) as [a2|] eqn:X2; auto.
    generalize (F2 _ _ X2). unfold p2. rewrite X1. congruence.
  + rewrite for_all_false in F2. destruct F2 as (x & a & P & Q).
    exists x. rewrite P. unfold p2 in Q. destruct (T.get x m1); auto.
  + rewrite for_all_false in F1. destruct F1 as (x & a & P & Q).
    exists x. rewrite P. unfold p1 in Q. destruct (T.get x m2); auto.
- (* existence -> beq = false *)
  destruct H as [x P].
  destruct (T.beq beqA m1 m2) eqn:E; auto.
  rewrite T.beq_correct in E.
  generalize (E x). destruct (T.get x m1); destruct (T.get x m2); tauto || congruence.
Qed.

End BOOLEAN_EQUALITY.

(** Extensional equality between trees *)

Section EXTENSIONAL_EQUALITY.

Variable A: Type.
Variable eqA: A -> A -> Prop.
Hypothesis eqAeq: Equivalence eqA.

Definition Equal (m1 m2: T.t A) : Prop :=
  forall x, match T.get x m1, T.get x m2 with
                | None, None => True
                | Some a1, Some a2 => a1 === a2
                | _, _ => False
            end.

Lemma Equal_refl: forall m, Equal m m.
Proof.
  intros; red; intros. destruct (T.get x m); auto. reflexivity.
Qed.

Lemma Equal_sym: forall m1 m2, Equal m1 m2 -> Equal m2 m1.
Proof.
  intros; red; intros. generalize (H x). destruct (T.get x m1); destruct (T.get x m2); auto. intros; symmetry; auto.
Qed.

Lemma Equal_trans: forall m1 m2 m3, Equal m1 m2 -> Equal m2 m3 -> Equal m1 m3.
Proof.
  intros; red; intros. generalize (H x) (H0 x).
  destruct (T.get x m1); destruct (T.get x m2); try tauto;
  destruct (T.get x m3); try tauto.
  intros. transitivity a0; auto.
Qed.

Instance Equal_Equivalence : Equivalence Equal := {
  Equivalence_Reflexive := Equal_refl;
  Equivalence_Symmetric := Equal_sym;
  Equivalence_Transitive := Equal_trans
}.

Hypothesis eqAdec: EqDec A eqA.

Program Definition Equal_dec (m1 m2: T.t A) : { m1 === m2 } + { m1 =/= m2 } :=
  match T.beq (fun a1 a2 => proj_sumbool (a1 == a2)) m1 m2 with
  | true => left _
  | false => right _
  end.
Next Obligation.
  rename Heq_anonymous into B.
  symmetry in B. rewrite T.beq_correct in B.
  red; intros. generalize (B x).
  destruct (T.get x m1); destruct (T.get x m2); auto.
  intros. eapply proj_sumbool_true; eauto.
Qed.
Next Obligation.
  assert (T.beq (fun a1 a2 => proj_sumbool (a1 == a2)) m1 m2 = true).
  apply T.beq_correct; intros.
  generalize (H x).
  destruct (T.get x m1); destruct (T.get x m2); try tauto.
  intros. apply proj_sumbool_is_true; auto.
  unfold equiv, complement in H0. congruence.
Qed.

Instance Equal_EqDec : EqDec (T.t A) Equal := Equal_dec.

End EXTENSIONAL_EQUALITY.

(** Creating a tree from a list of (key, value) pairs. *)

Section OF_LIST.

Variable A: Type.

Let f := fun (m: T.t A) (k_v: T.elt * A) => T.set (fst k_v) (snd k_v) m.

Definition of_list (l: list (T.elt * A)) : T.t A :=
  List.fold_left f l (T.empty _).

Lemma in_of_list:
  forall l k v, T.get k (of_list l) = Some v -> In (k, v) l.
Proof.
  assert (REC: forall k v l m,
           T.get k (fold_left f l m) = Some v -> In (k, v) l \/ T.get k m = Some v).
  { induction l as [ | [k1 v1] l]; simpl; intros.
  - tauto.
  - apply IHl in H. unfold f in H. simpl in H. rewrite T.gsspec in H.
    destruct H; auto.
    destruct (T.elt_eq k k1). inv H. auto. auto.
  }
  intros. apply REC in H. rewrite T.gempty in H. intuition congruence.
Qed.

Lemma of_list_dom:
  forall l k, In k (map fst l) -> exists v, T.get k (of_list l) = Some v.
Proof.
  assert (REC: forall k l m,
            In k (map fst l) \/ (exists v, T.get k m = Some v) ->
            exists v, T.get k (fold_left f l m) = Some v).
  { induction l as [ | [k1 v1] l]; simpl; intros.
  - tauto.
  - apply IHl. unfold f; rewrite T.gsspec. simpl. destruct (T.elt_eq k k1).
    right; econstructor; eauto.
    intuition congruence.
  }
  intros. apply REC. auto.
Qed.

Remark of_list_unchanged:
  forall k l m, ~In k (map fst l) -> T.get k (List.fold_left f l m) = T.get k m.
Proof.
  induction l as [ | [k1 v1] l]; simpl; intros.
- auto.
- rewrite IHl by tauto. unfold f; apply T.gso; intuition auto.
Qed.

Lemma of_list_unique:
  forall k v l1 l2,
  ~In k (map fst l2) -> T.get k (of_list (l1 ++ (k, v) :: l2)) = Some v.
Proof.
  intros. unfold of_list. rewrite fold_left_app. simpl.
  rewrite of_list_unchanged by auto. unfold f; apply T.gss.
Qed.

Lemma of_list_norepet:
  forall l k v, list_norepet (map fst l) -> In (k, v) l -> T.get k (of_list l) = Some v.
Proof.
  assert (REC: forall k v l m,
            list_norepet (map fst l) ->
            In (k, v) l ->
            T.get k (fold_left f l m) = Some v).
  { induction l as [ | [k1 v1] l]; simpl; intros.
    contradiction.
    inv H. destruct H0.
    inv H. rewrite of_list_unchanged by auto. apply T.gss.
    apply IHl; auto.
  }
  intros; apply REC; auto.
Qed.

Lemma of_list_elements:
  forall m k, T.get k (of_list (T.elements m)) = T.get k m.
Proof.
  intros. destruct (T.get k m) as [v|] eqn:M.
- apply of_list_norepet. apply T.elements_keys_norepet. apply T.elements_correct; auto.
- destruct (T.get k (of_list (T.elements m))) as [v|] eqn:M'; auto.
  apply in_of_list in M'. apply T.elements_complete in M'. congruence.
Qed.

End OF_LIST.

Lemma of_list_related:
  forall (A B: Type) (R: A -> B -> Prop) k l1 l2,
  list_forall2 (fun ka kb => fst ka = fst kb /\ R (snd ka) (snd kb)) l1 l2 ->
  option_rel R (T.get k (of_list l1)) (T.get k (of_list l2)).
Proof.
  intros until k. unfold of_list.
  set (R' := fun ka kb => fst ka = fst kb /\ R (snd ka) (snd kb)).
  set (fa := fun (m : T.t A) (k_v : T.elt * A) => T.set (fst k_v) (snd k_v) m).
  set (fb := fun (m : T.t B) (k_v : T.elt * B) => T.set (fst k_v) (snd k_v) m).
  assert (REC: forall l1 l2, list_forall2 R' l1 l2 ->
               forall m1 m2, option_rel R (T.get k m1) (T.get k m2) ->
               option_rel R (T.get k (fold_left fa l1 m1)) (T.get k (fold_left fb l2 m2))).
  { induction 1; intros; simpl.
  - auto.
  - apply IHlist_forall2. unfold fa, fb. rewrite ! T.gsspec.
    destruct H as [E F]. rewrite E. destruct (T.elt_eq k (fst b1)).
    constructor; auto.
    auto. }
  intros. apply REC; auto. rewrite ! T.gempty. constructor.
Qed.

End Tree_Properties.

Module PTree_Properties := Tree_Properties(PTree).

(** * Useful notations *)

Notation "a ! b" := (PTree.get b a) (at level 1).
Notation "a !! b" := (PMap.get b a) (at level 1).
