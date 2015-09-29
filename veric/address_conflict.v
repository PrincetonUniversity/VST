(* This file is developed by Qinxiang Cao, Aquinas Hobor and Shengyi Wang in 2015. *)

Require Import Coqlib.
Require Import Values.
Require Import Integers.
Require Import Floats.
Require Import Memory.

Require Import msl.eq_dec.
Require Import sepcomp.Address.

Lemma range_overlap_spec: forall l1 n1 l2 n2,
  n1 > 0 ->
  n2 > 0 ->
  (range_overlap l1 n1 l2 n2 <-> adr_range l1 n1 l2 \/ adr_range l2 n2 l1).
Proof.
  intros.
  unfold range_overlap, adr_range.
  destruct l1, l2.
  split; intros.
  + destruct H1 as [[? ?] [[? ?] [? ?]]].
    subst.
    destruct (zle z z0); [left | right].
    - split; auto.
      omega.
    - split; auto.
      omega.
  + destruct H1 as [[? ?] | [? ?]].
    - exists (b0, z0). repeat split; auto; omega.
    - exists (b, z). repeat split; auto; omega.
Qed.

Lemma range_overlap_comm: forall l1 n1 l2 n2, range_overlap l1 n1 l2 n2 -> range_overlap l2 n2 l1 n1.
Proof.
  unfold range_overlap.
  intros.
  destruct H as [l ?].
  exists l.
  tauto.
Qed.

Lemma range_overlap_non_zero: forall l1 n1 l2 n2, range_overlap l1 n1 l2 n2 -> n1 > 0 /\ n2 > 0.
Proof.
  unfold range_overlap.
  intros.
  destruct H as [l [? ?]].
  apply adr_range_non_zero in H.
  apply adr_range_non_zero in H0.
  auto.
Qed.

