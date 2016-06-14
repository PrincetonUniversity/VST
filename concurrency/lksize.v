Require Import compcert.common.AST.
Require Import compcert.common.Memdata.
Require Import Coq.ZArith.ZArith.

Definition LKCHUNK:= Mint32.
Definition LKSIZE:= align_chunk LKCHUNK.
Definition LKSIZE_nat:= Z.to_nat LKSIZE.