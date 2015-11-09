Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.type_induction.
Require Export floyd.fieldlist.
Require Export floyd.compact_prod_sum.

Definition proj_struct (i : ident) (m : members) {A: ident * type -> Type} (v: compact_prod (map A m)) (d: A (i, field_type i m)): A (i, field_type i m) :=
  proj_compact_prod (i, field_type i m) m v d member_dec.

Definition proj_union (i : ident) (m : members) {A: ident * type -> Type} (v: compact_sum (map A m)) (d: A (i, field_type i m)): A (i, field_type i m) :=
  proj_compact_sum (i, field_type i m) m v d member_dec.

Definition members_union_inj {m: members} {A} (v: compact_sum (map A m)) (it: ident * type): Prop :=
  compact_sum_inj v it member_dec.

