Require Import stdpp.namespaces.
Require Export VST.veric.invariants.
Require Import VST.msl.ghost_seplog.
Require Import VST.msl.sepalg_generators.
Require Import VST.veric.compcert_rmaps.
Require Import VST.concurrency.conclib.
Require Export VST.concurrency.ghostsI.
Require Import VST.veric.bi.
Require Import VST.msl.sepalg.
Require Import List.

Definition inv (N : namespace) P := EX i : iname, !!(N = nroot .@ (Pos.of_nat (S i))) && invariant i P.

Global Instance agree_persistent g P : Persistent (agree g P : mpred).
Proof.
  apply core_persistent; auto.
Qed.

Global Instance inv_persistent N P : Persistent (inv N P).
Proof.
  apply _.
Qed.

Global Instance inv_affine N P : Affine (inv N P).
Proof.
  apply _.
Qed.

Lemma invariant_dup : forall N P, inv N P = (inv N P * inv N P)%logic.
Proof.
  intros; apply pred_ext; rewrite <- (bi.persistent_sep_dup (inv N P)); auto.
Qed.

Lemma agree_join : forall g P1 P2, agree g P1 * agree g P2 |-- (|> P1 -* |> P2) * agree g P1.
Proof.
  constructor; apply agree_join.
Qed.

Lemma agree_join2 : forall g P1 P2, agree g P1 * agree g P2 |-- (|> P1 -* |> P2) * agree g P2.
Proof.
  constructor; apply agree_join2.
Qed.

Global Instance into_inv_inv N P : IntoInv (inv N P) N := {}.

Lemma inv_nonexpansive : forall N, nonexpansive (inv N).
Proof.
  intros; unfold inv.
  apply @exists_nonexpansive; intros i.
  apply @conj_nonexpansive, invariant_nonexpansive.
  apply const_nonexpansive.
Qed.

Lemma inv_nonexpansive2 : forall N f, nonexpansive f ->
  nonexpansive (fun a => inv N (f a)).
Proof.
  intros; unfold inv.
  apply @exists_nonexpansive; intros i.
  apply @conj_nonexpansive, invariant_nonexpansive2, H.
  apply const_nonexpansive.
Qed.
