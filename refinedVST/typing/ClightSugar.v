Require Import compcert.cfrontend.Clight.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.typing.annotations.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".

Inductive expr_annot :=
  | ExprAnnot_annot  {A} (a : A)
  | ExprAnnot_assert (n : nat).

Definition Sannot (e : expr_annot) := Sskip.
#[global] Arguments Sannot : simpl never.
Global Typeclasses Opaque Sannot.

Definition Sloop (n : nat) s1 s2 := Sloop s1 s2.
#[global] Arguments Sloop : simpl never.
Global Typeclasses Opaque Sloop.

Definition Swhile (n : nat) e s := Sloop n (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.

(* always-stuck statement *)
Definition Sstuck := Sset (BinPos.Pos.of_nat 1) (Ederef (Econst_long Integers.Int64.zero (Ctypes.Tpointer Ctypes.Tvoid Ctypes.noattr)) Ctypes.Tvoid).

Definition Sassert (e : expr) := Sifthenelse e Sskip Sstuck.
#[global] Arguments Sassert : simpl never.
Global Typeclasses Opaque Sassert.
