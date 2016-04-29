Require Import compcert.lib.Maps.
Require Export compcert.lib.Coqlib.
Require Export msl.seplog.
Require Export msl.log_normalize.
Require Export msl.ramification_lemmas.

Definition ident: Type := positive.
Parameter ident_eq: forall (a b: ident), {a = b} + {a <> b}.
Parameter val: Type.
Parameter Vundef: val.

Inductive type: Type :=
| Tint: type
| Tstruct: forall (id: ident), type.

Definition members : Type := list (ident * type).

Record composite : Type := {
  co_members: members;
  co_rank: nat
}.

Definition composite_env : Type := PTree.t composite.

Parameter sizeof: forall (env: composite_env) (t: type), Z.

Fixpoint in_members (id: ident) (fs: members) : Prop :=
  match fs with
  | nil => False
  | cons (id', t) fs_tl => (id = id') \/ in_members id fs_tl
  end.

Fixpoint field_type (id: ident) (fs: members) : type :=
  match fs with
  | nil => Tint (* default return value *)
  | cons (id', t) fs_tl =>
      if ident_eq id id'
      then t
      else field_type id fs_tl
  end.

Fixpoint field_offset (env: composite_env) (id: ident) (fs: members) : Z :=
  match fs with
  | nil => 0 (* default return value *)
  | cons (id', t) fs_tl =>
      if ident_eq id id'
      then 0
      else field_offset env id fs_tl + sizeof env t
  end.

Definition complete_type (env: composite_env) (t: type) : bool :=
  match t with
  | Tint => true
  | Tstruct id =>
      match env!id with Some co => true | None => false end
  end.

Fixpoint complete_members (env: composite_env) (m: members) : bool :=
  match m with
  | nil => true
  | (id, t) :: m' => complete_type env t && complete_members env m'
  end.

Definition rank_type (env: composite_env) (t: type) : nat :=
  match t with
  | Tstruct id =>
      match env!id with
      | None => O
      | Some co => S (co_rank co)
      end
  | _ => O
  end.

Fixpoint rank_members (env: composite_env) (m: members) : nat :=
  match m with
  | nil => 0%nat
  | (id, t) :: m => Peano.max (rank_type env t) (rank_members env m)
  end.

Record composite_consistent (env: composite_env) (co: composite) : Prop := {
  co_consistent_complete:
     complete_members env (co_members co) = true;
  co_consistent_rank:
     co_rank co = rank_members env (co_members co)
}.

Definition composite_env_consistent (env: composite_env) : Prop :=
  forall id co, env!id = Some co -> composite_consistent env co.

Class compspecs := mkcompspecs {
  cenv_cs : composite_env;
  cenv_consistent: composite_env_consistent cenv_cs
(*  cenv_legal_alignas: composite_env_legal_alignas cenv_cs; *)
(*  cenv_legal_fieldlist: composite_env_legal_fieldlist cenv_cs *)
}.

Existing Class composite_env.
Existing Instance cenv_cs.

Definition type_eq: forall (t1 t2: type), {t1 = t2} + {t1 <> t2}.
Proof.
  destruct t1, t2; [left | right | right |]; try congruence.
  destruct (ident_eq id id0); [left | right]; congruence.
Defined.

Definition member_dec: forall (it0 it1: ident * type), {it0 = it1} + {it0 <> it1}.
  intros.
  destruct it0, it1.
  destruct (ident_eq i i0), (type_eq t t0); [left | right | right | right]; congruence.
Defined.

Definition co_default: composite := (Build_composite nil 0).

Definition get_co {cenv: compspecs} id :=
  match cenv_cs ! id with
  | Some co => co
  | _ => co_default
  end.

Parameter Pred: Type.
Parameter NPred: NatDed Pred.
Parameter SPred: SepLog Pred.
Parameter CPred: ClassicalSep Pred.
Parameter CSLPred: CorableSepLog Pred.

Parameter mapsto: val -> val -> Pred.
Parameter offset_val: Z -> val -> val.

