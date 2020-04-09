(* Definitions and lemmas used in list solver *)

Require Import VST.floyd.base2.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.entailer.
Require Import VST.floyd.field_compat.
Require Import Lia.
Import ListNotations.

(** This file provides a almost-complete solver for list with concatenation.
  Its core symbols include:
    Zlength
    Znth
    Zrepeat
    app
    sublist
    map.
  And it also interprets these symbols by convernting to core symbols:
    list_repeat (Z.to_nat _)
    nil
    cons
    upd_Znth. *)

(** * Zlength_solve *)
(** Zlength_solve is a tactic that solves linear arithmetic about length of lists. *)

(* Auxilary lemmas for Zlength_solve. *)
Lemma repeat_list_repeat : forall {A : Type} (n : nat) (x : A),
  repeat x n = list_repeat n x.
Proof. intros. induction n; simpl; try f_equal; auto. Qed.

Definition Zrepeat {A : Type} (x : A) (n : Z) : list A :=
  repeat x (Z.to_nat n).

Lemma Zlength_Zrepeat : forall (A : Type) (x : A) (n : Z),
  0 <= n ->
  Zlength (Zrepeat x n) = n.
Proof. intros *. unfold Zrepeat. rewrite repeat_list_repeat. apply @Zlength_list_repeat. Qed.

Lemma Zlength_firstn : forall (A : Type) n (l : list A),
  Zlength (firstn n l) = Z.min (Z.max (Z.of_nat n) 0) (Zlength l).
Proof.
  induction n; intros.
  - simpl. rewrite Zlength_nil.
    pose proof (Zlength_nonneg l). lia.
  - destruct l; simpl.
    + rewrite Zlength_nil. lia.
    + rewrite !Zlength_cons.
      rewrite IHn.
      pose proof (Zlength_nonneg l). lia.
Qed.

Lemma Zlength_firstn_to_nat : forall (A : Type) n (l : list A),
  Zlength (firstn (Z.to_nat n) l) = Z.min (Z.max n 0) (Zlength l).
Proof.
  intros.
  rewrite Zlength_firstn.
  lia.
Qed.

Lemma Zlength_skipn : forall (A : Type) n (l : list A),
  Zlength (skipn n l) = Z.max (Zlength l - (Z.max (Z.of_nat n) 0)) 0.
Proof.
  induction n; intros.
  - simpl.
    pose proof (Zlength_nonneg l). lia.
  - destruct l; simpl.
    + rewrite Zlength_nil. lia.
    + rewrite !Zlength_cons.
      rewrite IHn.
      pose proof (Zlength_nonneg l). lia.
Qed.

Lemma Zlength_skipn_to_nat : forall (A : Type) n (l : list A),
  Zlength (skipn (Z.to_nat n) l) = Z.max (Zlength l - (Z.max n 0)) 0.
Proof.
  intros.
  rewrite Zlength_skipn.
  lia.
Qed.

Lemma Zlength_sublist2 : forall (A : Type) lo hi (l : list A),
  Zlength (sublist lo hi l) = Z.max (Z.min hi (Zlength l) - Z.max lo 0) 0.
Proof.
  intros.
  unfold sublist.
  rewrite Zlength_skipn_to_nat, Zlength_firstn_to_nat.
  lia.
Qed.

Lemma Zlength_upd_Znth : forall (A : Type) i l (x : A),
  Zlength (upd_Znth i l x) = Zlength l
  \/ Zlength (upd_Znth i l x) = Zlength l + 1. (* TODO *)
Proof.
  intros.
  unfold upd_Znth. rewrite Zlength_app, Zlength_cons.
  rewrite !Zlength_sublist2.
  pose proof (Zlength_nonneg l). lia.
Qed.

(** * list_form *)
Lemma Zrepeat_fold : forall (A : Type) (x : A) (n : Z),
  list_repeat (Z.to_nat n) x = Zrepeat x n.
Proof. intros *. rewrite <- repeat_list_repeat. auto. Qed.

Lemma cons_Zrepeat_1_app : forall (A : Type) (x : A) (al : list A),
  x :: al = Zrepeat x 1 ++ al.
Proof. auto. Qed.

Lemma upd_Znth_unfold : forall (A : Type) (n : Z) (al : list A) (x : A),
  upd_Znth n al x = sublist 0 n al ++ [x] ++ sublist (n+1) (Zlength al) al.
Proof. auto. Qed.

(** * Znth_solve *)
(** Znth_solve is a tactic that simplifies and solves proof goal related to terms headed by Znth. *)

(* Auxilary lemmas for Znth_solve. *)
Lemma Znth_Zrepeat : forall (A : Type) (d : Inhabitant A) (i n : Z) (x : A),
  0 <= i < n ->
  Znth i (Zrepeat x n) = x.
Proof. intros. unfold Zrepeat. rewrite repeat_list_repeat. apply Znth_list_repeat_inrange; auto. Qed.

(** * list extentionality *)
(* To prove equality between two lists, a convenient way is to apply extentionality
  and prove their length are equal and each corresponding entries are equal.
  It is convenient because then we can use Znth_solve to solve it. *)

Lemma nth_eq_ext : forall (A : Type) (default : A) (al bl : list A),
  length al = length bl ->
  (forall (i : nat), (0 <= i < length al)%nat -> nth i al default = nth i bl default) ->
  al = bl.
Proof.
  intros. generalize dependent bl.
  induction al; intros;
    destruct bl; try discriminate; auto.
  f_equal.
  - apply (H0 0%nat). simpl. lia.
  - apply IHal.
    + simpl in H. lia.
    + intros. apply (H0 (S i)). simpl. lia.
Qed.

Lemma Znth_eq_ext : forall {A : Type} {d : Inhabitant A} (al bl : list A),
  Zlength al = Zlength bl ->
  (forall (i : Z), 0 <= i < Zlength al -> Znth i al = Znth i bl) ->
  al = bl.
Proof.
  intros. rewrite !Zlength_correct in *. apply nth_eq_ext with d.
  - lia.
  - intros. rewrite  <- (Nat2Z.id i).
    specialize (H0 (Z.of_nat i) ltac:(lia)).
    rewrite !nth_Znth by (rewrite !Zlength_correct in *; lia).
    apply H0.
Qed.
