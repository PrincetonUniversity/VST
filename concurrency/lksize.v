Require Import compcert.common.AST.
Require Import compcert.common.Memdata.
Require Import Coq.ZArith.ZArith.

(* LKSIZE should be of the size of the struct we use for locks, which
is sometimes equivalent to an array of 4 pointers. For now, we keep it
equal to 1 (i.e. 4 bytes), but ideally it would be arbitrary. *)
Definition LKSIZE:= 4%Z.
Definition LKSIZE_nat:= Z.to_nat LKSIZE.
