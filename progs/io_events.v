Require Import VST.floyd.proofauto.
Require Import ITree.ITree.

Inductive IO_event : Type -> Type :=
| ERead : IO_event int
| EWrite (c : int) : IO_event unit.

Definition read : itree IO_event int := embed ERead.

Definition write (c : int) : itree IO_event unit := embed (EWrite c).

Definition IO_itree := itree IO_event unit.
