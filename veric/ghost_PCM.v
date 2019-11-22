Require Export VST.msl.msl_standard.
Require Export VST.veric.base.
Require Export VST.veric.shares.
Require Import VST.msl.ghost.
Require Import VST.veric.ghosts.

(* external ghost state *)

Definition ext_PCM Z : Ghost := ref_PCM (exclusive_PCM Z).

Lemma valid_ext : forall {Z} (ora : Z), @valid (ext_PCM _) (Some (Tsh, Some ora), None).
Proof.
  intros; simpl; split; auto.
  apply Share.nontrivial.
Qed.

Definition ext_ghost {Z} (ora : Z) : {g : Ghost & {a : G | valid a}} :=
  existT _ (ext_PCM _) (exist _ _ (valid_ext ora)).

Lemma valid_ext_ref : forall {Z} (ora : Z), @valid (ext_PCM _) (None, Some (Some ora)).
Proof.
  intros; simpl; split; auto.
  eexists (Some (_, _)); constructor.
Qed.

Definition ext_ref {Z} (ora : Z) : {g : Ghost & {a : G | valid a}} :=
  existT _ (ext_PCM _) (exist _ _ (valid_ext_ref ora)).

Lemma valid_ext_both : forall {Z} (ora : Z), @valid (ext_PCM _) (Some (Tsh, Some ora), Some (Some ora)).
Proof.
  intros; simpl; split; auto.
  - apply Share.nontrivial.
  - exists None; constructor.
Qed.

Definition ext_both {Z} (ora : Z) : {g : Ghost & {a : G | ghost.valid a}} :=
  existT _ (ext_PCM _) (exist _ _ (valid_ext_both ora)).
