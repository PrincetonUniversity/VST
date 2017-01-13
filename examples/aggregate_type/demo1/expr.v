Require Export compcert.lib.Coqlib.
Require Export msl.seplog.
Require Export msl.log_normalize.
Require Export msl.ramification_lemmas.
Require Export Coq.Logic.JMeq.

Parameter ident: Type.
Parameter ident_eq: forall (a b: ident), {a = b} + {a <> b}.
Parameter val: Type.
Parameter Vundef: val.

Inductive type: Type :=
| Tint: type
| Tstruct: forall (id: ident) (fs: fieldlist), type
with fieldlist: Type :=
| Fnil: fieldlist
| Fcons: forall (hd: ident * type) (tl: fieldlist), fieldlist.

Parameter sizeof: forall (t: type), Z.

Fixpoint in_members (id: ident) (fs: fieldlist) : Prop :=
  match fs with
  | Fnil => False
  | Fcons (id', t) fs_tl => (id = id') \/ in_members id fs_tl
  end.

Fixpoint field_type (id: ident) (fs: fieldlist) : type :=
  match fs with
  | Fnil => Tint (* default return value *)
  | Fcons (id', t) fs_tl =>
      if ident_eq id id'
      then t
      else field_type id fs_tl
  end.

Fixpoint field_offset (id: ident) (fs: fieldlist) : Z :=
  match fs with
  | Fnil => 0 (* default return value *)
  | Fcons (id', t) fs_tl =>
      if ident_eq id id'
      then 0
      else field_offset id fs_tl + sizeof t
  end.

Fixpoint members_no_replicate (fs: fieldlist): Prop :=
  match fs with
  | Fnil => True
  | Fcons (i, t) fs_tl =>
      ~ in_members i fs_tl /\ members_no_replicate fs_tl
  end.

Parameter Pred: Type.
Parameter NPred: NatDed Pred.
Parameter SPred: SepLog Pred.
Parameter CPred: ClassicalSep Pred.
Parameter CSLPred: CorableSepLog Pred.

Parameter mapsto: val -> val -> Pred.
Parameter offset_val: Z -> val -> val.

Axiom offset_offset_val: forall ofs1 ofs2 p, offset_val ofs2 (offset_val ofs1 p) = offset_val (ofs1 + ofs2) p.
(*
Fixpoint sizeof (t: type): Z :=
  match t with
  | Tint => 1
  | Tstruct _ fs => sizeof_fieldlist fs
  end
with sizeof_fieldlist (fs: fieldlist) : Z :=
  match fs with
  | Fnil => 0
  | Fcons (_, t) fs_tl => sizeof t + sizeof_fieldlist fs_tl
  end.

*)