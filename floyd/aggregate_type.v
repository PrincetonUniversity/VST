Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.type_induction.
Require Export floyd.fieldlist.
Require Export floyd.compact_prod_sum.
Require Export floyd.sublist.

Definition proj_struct (i : ident) (m : members) {A: ident * type -> Type} (v: compact_prod (map A m)) (d: A (i, field_type i m)): A (i, field_type i m) :=
  proj_compact_prod (i, field_type i m) m v d member_dec.

Definition proj_union (i : ident) (m : members) {A: ident * type -> Type} (v: compact_sum (map A m)) (d: A (i, field_type i m)): A (i, field_type i m) :=
  proj_compact_sum (i, field_type i m) m v d member_dec.

Definition members_union_inj {m: members} {A} (v: compact_sum (map A m)) (it: ident * type): Prop :=
  compact_sum_inj v it member_dec.

Definition upd_sublist {X: Type} (lo hi: Z) (l: list X) (l0: list X) : list X :=
  firstn (Z.to_nat lo) l ++ l0 ++ skipn (Z.to_nat hi) l.

(* We should use the following two definition in replace_refill lemmas in the future. And avoid using compact prod/sum directly. *)

Definition upd_struct (i : ident) (m : members) {A: ident * type -> Type} (v: compact_prod (map A m)) (v0: A (i, field_type i m)): compact_prod (map A m) :=
  compact_prod_upd _ v (i, field_type i m) v0 member_dec.

Definition upd_union (i : ident) (m : members) {A: ident * type -> Type} (v: compact_sum (map A m)) (v0: A (i, field_type i m)): compact_sum (map A m) :=
  compact_sum_upd _ v (i, field_type i m) v0 member_dec.