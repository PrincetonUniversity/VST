Require Import compcert.common.AST.
Require Import compcert.common.Memdata.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

(* LKSIZE should match sizeof(semax_conc.tlock).  *)
Definition LKSIZE:= (2 * size_chunk Mptr)%Z.
Definition LKSIZE_nat:= Z.to_nat LKSIZE.

Lemma LKSIZE_pos : (0 < LKSIZE)%Z.
Proof.
  unfold LKSIZE.
  pose proof (size_chunk_pos Mptr); lia.
Qed.

Lemma LKSIZE_int : (size_chunk Mint32 < LKSIZE)%Z.
Proof.
  unfold LKSIZE; simpl.
  rewrite size_chunk_Mptr; destruct Archi.ptr64; lia.
Qed.

Lemma LKSIZE_long : (size_chunk Mint64 <= LKSIZE)%Z.
Proof.
  unfold LKSIZE; simpl.
  rewrite size_chunk_Mptr; destruct Archi.ptr64; lia.
Qed.

Ltac lkomega := pose proof LKSIZE_pos; pose proof LKSIZE_int; pose proof LKSIZE_long; simpl in *; lia.
