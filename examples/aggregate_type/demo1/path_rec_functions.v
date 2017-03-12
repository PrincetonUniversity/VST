Require Import AggregateType.demo1.expr.

Definition gfield_type (t: type) (f: ident) : type :=
  match t with
  | Tstruct _ fs => field_type f fs
  | _ => Tint (* default return value *)
  end.

Definition gfield_offset (t: type) (f: ident) : Z :=
  match t with
  | Tstruct _ fs => field_offset f fs
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
  | Tstruct _ fs, i => in_members f fs
  | _, _ => False
  end.

Fixpoint legal_nested_field (t: type) (nf: list ident) : Prop :=
  match nf with
  | nil => True
  | f :: nf0 => legal_nested_field t nf0 /\ legal_field (nested_field_type t nf0) f
  end.

Require Import AggregateType.demo1.type_rec_functions.

Fixpoint proj_struct (f : ident) (fs : fieldlist)
  (v: reptype_fieldlist fs): reptype (field_type f fs) :=
  match fs as fs_PAT
    return reptype_fieldlist fs_PAT -> reptype (field_type f fs_PAT) with
  | Fnil => fun _ => Vundef (* default return value *)
  | Fcons (f', t) fs_tl =>
      fun v =>
      if ident_eq f f' as b
        return reptype (if b then t else (field_type f fs_tl))
      then fst v
      else proj_struct f fs_tl (snd v)
  end v.

Definition proj_gfield_reptype (t: type) (f: ident)
  (v: reptype t): reptype (gfield_type t f) :=
  match t as t_PAT
    return (reptype t_PAT -> reptype (gfield_type t_PAT f))
  with
  | Tstruct _ fs => fun v => proj_struct f fs v
  | _ => fun _ => Vundef
  end v.

Fixpoint proj_reptype (t: type) (nf: list ident)
  (v: reptype t) : reptype (nested_field_type t nf) :=
  match nf as nf_PAT
    return reptype (nested_field_type t nf_PAT)
  with
  | nil => v
  | f :: nf0 => proj_gfield_reptype _ f (proj_reptype t nf0 v)
  end.

Fixpoint upd_struct (f : ident) (fs : fieldlist) (v: reptype_fieldlist fs) (v0: reptype (field_type f fs)) : reptype_fieldlist fs :=
  match fs as fs_PAT return (reptype_fieldlist fs_PAT -> reptype (field_type f fs_PAT) -> reptype_fieldlist fs_PAT) with
  | Fnil => fun _ _ => tt (* default return value *)
  | Fcons (f', t) fs_tl =>
      fun v: reptype t * reptype_fieldlist fs_tl =>
      if ident_eq f f' as b return reptype (if b then t else (field_type f fs_tl)) -> reptype t * reptype_fieldlist fs_tl
      then fun v0 => (v0, snd v)
      else fun v0 => (fst v, upd_struct f fs_tl (snd v) v0)
  end v v0.

Definition upd_gfield_reptype t f (v: reptype t) (v0: reptype (gfield_type t f)) : reptype t :=
  match t return (reptype t -> reptype (gfield_type t f) -> reptype t)
  with
  | Tstruct _ fs =>
      fun v v0 => upd_struct f fs v v0
  | _ => fun v _ => v
  end v v0.

Fixpoint upd_reptype (t: type) (nf: list ident) (v: reptype t) (v0: reptype (nested_field_type t nf)): reptype t :=
  match nf as nf_PAT
    return reptype (nested_field_type t nf_PAT) -> reptype t
  with
  | nil => fun v0 => v0
  | gf :: gfs0 => fun v0 => upd_reptype t gfs0 v (upd_gfield_reptype _ gf (proj_reptype t gfs0 v) v0)
  end v0.

Lemma nested_pred_nested_field_type: forall t nf atom_pred,
  nested_pred atom_pred t ->
  legal_nested_field t nf ->
  nested_pred atom_pred (nested_field_type t nf).
Proof.
  intros.
  induction nf as [| i nf]; simpl in *; auto.
  destruct H0.
  specialize (IHnf H0).
  clear H0 H.
  destruct (nested_field_type t nf); [inversion H1 |].
  simpl in *.

  destruct IHnf as [_ ?].
  induction fs as [| [i0 t0] fs0]; [inversion H1 |].
  simpl.
  destruct (ident_eq i i0).
  + destruct H; auto.
  + simpl in H1; destruct H; tauto.
Qed.

Lemma legal_type_nested_field_type: forall t nf,
  legal_type t ->
  legal_nested_field t nf ->
  legal_type (nested_field_type t nf).
Proof.
  intros. apply nested_pred_nested_field_type; auto.
Qed.

Lemma proj_upd_gfield_reptype_hit: forall t i v u,
  legal_field t i ->
  proj_gfield_reptype t i (upd_gfield_reptype t i u v) = v.
Proof.
  intros.
  destruct t; [inversion H |].
  simpl in *.
  induction fs as [| [i0 t0] fs0]; [inversion H |].
  simpl in *.
  destruct (ident_eq i i0); auto.
  apply IHfs0; tauto.
Qed.

Lemma proj_upd_gfield_reptype_miss: forall t i0 i1 v u,
  i0 <> i1 ->
  proj_gfield_reptype t i1 (upd_gfield_reptype t i0 u v) = proj_gfield_reptype t i1 u.
Proof.
  intros.
  destruct t; [auto |].
  simpl in *.
  rename i1 into i2, i0 into i1.
  induction fs as [| [i0 t0] fs0]; auto.
  simpl in *.
  destruct (ident_eq i2 i0), (ident_eq i1 i0).
  + congruence.
  + auto.
  + auto.
  + apply IHfs0; tauto.
Qed.

