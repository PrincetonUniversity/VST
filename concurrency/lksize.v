Require Import compcert.common.AST.
Require Import compcert.common.Memdata.
Require Import Coq.ZArith.ZArith.

(* LKSIZE should match sizeof(semax_conc.tlock).  *)
Definition LKSIZE:= 8%Z.
Definition LKSIZE_nat:= Z.to_nat LKSIZE.
