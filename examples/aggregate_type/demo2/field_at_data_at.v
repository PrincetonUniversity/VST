Require Import AggregateType.demo2.expr.
Require Import AggregateType.demo2.prod_lemmas.
Require Import AggregateType.demo2.type_rec_functions.
Require Import AggregateType.demo2.path_rec_functions.

Section FieldAtDataAt.

Context {cs: compspecs}.

Definition field_at (t: type) (nf: list ident) (v: reptype (nested_field_type t nf)) (p: val) : Pred := data_at_rec (nested_field_type t nf) v (offset_val (nested_field_offset t nf) p).

Definition data_at (t: type) (v: reptype t) (p: val) : Pred := field_at t nil v p.

Definition field_address (t: type) (nf: list ident) (p: val) : val := offset_val (nested_field_offset t nf) p.

End FieldAtDataAt.
