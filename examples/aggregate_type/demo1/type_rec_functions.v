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

Fixpoint data_at_rec (t: type)
  (v: reptype t) : val -> Pred :=
  match t as t_PAT
  return reptype t_PAT -> val -> Pred with
  | Tint => fun v p =>
      mapsto p v
  | Tstruct _ fs => fun v p =>
      data_at_rec_fieldlist fs v fs p
  end v
with data_at_rec_fieldlist (fs: fieldlist)
 (v: reptype_fieldlist fs) (full_fs: fieldlist): val -> Pred :=
  match fs as fs_PAT
  return reptype_fieldlist fs_PAT -> val -> Pred with
  | Fnil => fun v p =>
      emp
  | Fcons (id, t) fs_tl => fun v p=>
      data_at_rec t (fst v)
        (offset_val (field_offset id full_fs) p)*
      data_at_rec_fieldlist fs_tl (snd v) full_fs p
  end v.

Fixpoint nested_pred (atom_pred: type -> Prop) (t: type): Prop :=
  match t with
  | Tint => atom_pred t
  | Tstruct _ fs => atom_pred t /\ nested_pred_fieldlist atom_pred fs
  end
with nested_pred_fieldlist (atom_pred: type -> Prop) (fs: fieldlist): Prop :=
  match fs with
  | Fnil => True
  | Fcons (i0, t0) fs0 => nested_pred atom_pred t0 /\ nested_pred_fieldlist atom_pred fs0
  end.

Lemma nested_pred_atom_pred: forall atom_pred t, nested_pred atom_pred t -> atom_pred t.
Proof.
  intros.
  destruct t; simpl in H; tauto.
Qed.

Definition legal_type: type -> Prop :=
  nested_pred
   (fun t => match t with
             | Tint => True
             | Tstruct _ fs => members_no_replicate fs
             end).
