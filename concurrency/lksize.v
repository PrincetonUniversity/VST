Require Import compcert.common.AST.
Require Import compcert.common.Memdata.
Require Import Coq.ZArith.ZArith.

(* LKSIZE should be of the size of the struct we use for locks, which
happens to be equivalent to an array of 4 pointers, here *)
Definition LKSIZE:= (4 * 4)%Z.
Definition LKSIZE_nat:= Z.to_nat LKSIZE.
