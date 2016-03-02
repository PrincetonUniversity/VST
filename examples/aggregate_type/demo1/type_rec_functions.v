Require Import AggregateType.demo1.expr.

Fixpoint reptype (t: type): Type :=
  match t with
  | Tint => val
  | Tstruct _ fs => reptype_fieldlist fs
  end
with reptype_fieldlist (fs: fieldlist) : Type :=
  match fs with
  | Fnil => unit
  | Fcons (_, t) fs_tl => prod (reptype t) (reptype_fieldlist fs_tl)
  end.

Fixpoint default_val (t: type): reptype t :=
  match t as t_PAT return reptype t_PAT with
  | Tint => Vundef
  | Tstruct _ fs => default_val_fieldlist fs
  end
with default_val_fieldlist (fs: fieldlist) : reptype_fieldlist fs :=
  match fs as fs_PAT return reptype_fieldlist fs_PAT with
  | Fnil => tt
  | Fcons (_, t) fs_tl => (default_val t, default_val_fieldlist fs_tl)
  end.

Open Scope logic.

Definition at_offset (P: val -> Pred) (z: Z): val -> Pred :=
 fun v => P (offset_val z v).

Fixpoint data_at_rec (t: type) (v: reptype t) : val -> Pred :=
  match t as t_PAT return reptype t_PAT -> val -> Pred with
  | Tint => fun v =>
      fun p => mapsto p v
  | Tstruct _ fs => fun v =>
      data_at_rec_fieldlist fs v fs
  end v
with data_at_rec_fieldlist (fs: fieldlist) (v: reptype_fieldlist fs) (full_fs: fieldlist) : val -> Pred :=
  match fs as fs_PAT return reptype_fieldlist fs_PAT -> val -> Pred with
  | Fnil => fun v =>
      emp
  | Fcons (id, t) fs_tl => fun v: (reptype t * reptype_fieldlist fs_tl)%type =>
      at_offset (data_at_rec t (fst v)) (field_offset id full_fs) *
      data_at_rec_fieldlist fs_tl (snd v) full_fs
  end v.

