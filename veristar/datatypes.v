Require Import ZArith List.
Require Import veristar.variables.

(** datatypes.v:
Datatypes used throughout the development *)

Definition var : Type := Ident.t.

(** expr:
Program expressions *)

Inductive expr := Nil | Var : var -> expr.

(** pn_atom:
Pure (heap-independent) atoms *)

Inductive pn_atom := Equ : expr -> expr -> pn_atom | Nequ : expr -> expr -> pn_atom.

(** space_atom:
Spatial atoms are either next pointers or acyclic list segments. *)

Inductive space_atom :=
| Next : expr -> expr -> space_atom
| Lseg : expr -> expr -> space_atom.

(** assertion:
An assertion is composed of a list of pure atoms [pi], and a list of spatial
atoms [sigma].  [sigma] is interpreted as the _spatial_ conjunction of the
atoms, whereas [pi] asserts the conjunction of its pure atoms. *)

Inductive assertion : Type :=
  Assertion : forall (pi : list pn_atom) (sigma : list space_atom), assertion.

(** entailment:
An entailment is just a pair of assertions. Entailments are interpreted as:
In all models (pairs of heaps [h] and stacks [s]), the interpretation of the
assertion on the left implies the interpretation of the assertion on the right. *)

Inductive entailment : Type :=
  Entailment : assertion -> assertion -> entailment.

(** Various substitution functions:
 *)

Definition subst_var (i: var) (t: expr) (j: var) :=
  if Ident.eq_dec i j then t else Var j.

Definition subst_expr (i: var) (t: expr) (t': expr) :=
  match t' with
    | Nil => Nil
    | Var j => if Ident.eq_dec i j then t else t'
  end.

Definition subst_pn (i: var) (t: expr) (a: pn_atom) :=
 match a with
   | Equ t1 t2 => Equ (subst_expr i t t1) (subst_expr i t t2)
   | Nequ t1 t2 => Nequ (subst_expr i t t1) (subst_expr i t t2)
 end.

Definition subst_pns (i: var) (t: expr) (pa: list pn_atom)
  : list pn_atom := map (subst_pn i t) pa.

Definition subst_space (i: var) (t: expr) (a: space_atom) :=
  match a with
    | Next t1 t2 => Next (subst_expr i t t1) (subst_expr i t t2)
    | Lseg t1 t2 => Lseg (subst_expr i t t1) (subst_expr i t t2)
  end.

Definition subst_spaces (i: var) (t: expr)
  : list space_atom -> list space_atom := map (subst_space i t).

Definition subst_assertion (i: var) (e: expr) (a: assertion) :=
 match a with Assertion pi sigma =>
   Assertion (subst_pns i e pi) (subst_spaces i e sigma)
 end.
