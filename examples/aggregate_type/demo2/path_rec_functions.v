Require Import AggregateType.demo2.expr.
Require Import AggregateType.demo2.prod_lemmas.

Section PathRecFunctions.

Context {cs: compspecs}.

Definition gfield_type (t: type) (f: ident) : type :=
  match t with
  | Tstruct id => field_type f (co_members (get_co id))
  | _ => Tint (* default return value *)
  end.

Definition gfield_offset (t: type) (f: ident) : Z :=
  match t with
  | Tstruct id => field_offset cenv_cs f (co_members (get_co id))
  | _ => 0 (* default return value *)
  end.

Fixpoint nested_field_type (t: type) (nf: list ident) : type :=
  match nf with
  | nil => t
  | f :: nf0 => gfield_type (nested_field_type t nf0) f
  end.

Fixpoint nested_field_offset (t: type) (nf: list ident) : Z :=
  match nf with
  | nil => 0
  | f :: nf0 => nested_field_offset t nf0 + gfield_offset (nested_field_type t nf0) f
  end.

Definition legal_field (t: type) (f: ident) :=
  match t, f with
  | Tstruct id, i => in_members f (co_members (get_co id))
  | _, _ => False
  end.

Fixpoint legal_nested_field (t: type) (nf: list ident) : Prop :=
  match nf with
  | nil => True
  | f :: nf0 => legal_nested_field t nf0 /\ legal_field (nested_field_type t nf0) f
  end.

Require Import AggregateType.demo2.type_rec_functions.

Definition proj_struct (f : ident) (m: members)
  (v: reptype_members m): reptype (field_type f m) :=
  proj_list_prod (f, field_type f m) m v (default_val _) member_dec.

Definition proj_gfield_reptype (t: type) (f: ident)
  (v: reptype t): reptype (gfield_type t f) :=
  match t as t_PAT
    return (REPTYPE t_PAT -> reptype (gfield_type t_PAT f))
  with
  | Tstruct id => fun v => proj_struct f (co_members (get_co id)) v
  | _ => fun _ => Vundef
  end (unfold_reptype v).

Fixpoint proj_reptype (t: type) (nf: list ident)
  (v: reptype t) : reptype (nested_field_type t nf) :=
  match nf as nf_PAT
    return reptype (nested_field_type t nf_PAT)
  with
  | nil => v
  | f :: nf0 => proj_gfield_reptype _ f (proj_reptype t nf0 v)
  end.

Definition upd_struct (f : ident) (m: members) (v: reptype_members m) (v0: reptype (field_type f m)) : reptype_members m :=
  upd_list_prod _ v (f, field_type f m) v0 member_dec.

Definition upd_gfield_reptype t f (v: reptype t) (v0: reptype (gfield_type t f)) : reptype t :=
  fold_reptype
   (match t return (REPTYPE t -> reptype (gfield_type t f) -> REPTYPE t)
    with
    | Tstruct id =>
        fun v v0 => upd_struct f (co_members (get_co id)) v v0
    | _ => fun v _ => v
    end (unfold_reptype v) v0).

Fixpoint upd_reptype (t: type) (nf: list ident) (v: reptype t) (v0: reptype (nested_field_type t nf)): reptype t :=
  match nf as nf_PAT
    return reptype (nested_field_type t nf_PAT) -> reptype t
  with
  | nil => fun v0 => v0
  | gf :: gfs0 => fun v0 => upd_reptype t gfs0 v (upd_gfield_reptype _ gf (proj_reptype t gfs0 v) v0)
  end v0.

End PathRecFunctions.
