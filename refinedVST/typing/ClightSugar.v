Require Import compcert.cfrontend.Clight.
Require Import VST.typing.annotations.

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
