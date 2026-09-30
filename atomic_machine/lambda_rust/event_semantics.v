(**
  Single-threaded lambda-Rust semantics for the atomic machine.

  Sequentially consistent operations are exposed through [lr_external].
  Pure computation, non-atomic accesses, allocation, and deallocation are
  handled by [lr_step]; [Fork] by [lr_spawn].
*)

From Stdlib Require Import ZArith Lia List Bool.
From stdpp Require Import base gmap list.

Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.common.

Import ListNotations.
Open Scope Z_scope.
Open Scope lambda_rust_loc_scope.

Set Default Proof Using "Type".

(** The reader/writer state is maintained separately by the atomic machine. *)
Definition lr_mem : Type := gmap loc val.
Definition lr_layout : Type := unit.

#[global] Instance lr_memory :
    @Memory loc val _ _ lr_mem lr_layout :=
  {| load := fun m l _ => m !! l;

     store := fun m l _ v =>
       match m !! l with
       | Some _ => Some (<[l := v]> m)
       | None => None
       end;

     layout_to_locs := fun l _ => [l] |}.

Local Notation lr_mem_ev := (@mem_ev loc).

Definition lr_read_event (l : loc) : lr_mem_ev :=
  VST.atomic_machine.atomic_machine.Read l.

Definition lr_write_event (l : loc) : lr_mem_ev :=
  VST.atomic_machine.atomic_machine.Write l.

Definition lr_alloc_event (l : loc) : lr_mem_ev :=
  VST.atomic_machine.atomic_machine.Alloc l.

Definition lr_free_event (l : loc) : lr_mem_ev :=
  VST.atomic_machine.atomic_machine.Free l.

(** The locations in the half-open range starting at [l] with length [n]. *)
Fixpoint lr_locs (l : loc) (n : nat) : list loc :=
  match n with
  | O => []
  | S n => l :: lr_locs (l +ₗ 1)%L n
  end.

Definition lr_alloc_events (l : loc) (n : nat) : list lr_mem_ev :=
  map lr_alloc_event (lr_locs l n).

Definition lr_free_events (l : loc) (n : nat) : list lr_mem_ev :=
  map lr_free_event (lr_locs l n).

Definition lr_val_eq
    (m : lr_mem) (v_cur v_exp : val) : Prop :=
  match v_exp, v_cur with
  | LitV l_exp, LitV l_cur => lit_eq m l_exp l_cur
  | _, _ => False
  end.

Definition lr_val_neq
    (m : lr_mem) (v_cur v_exp : val) : Prop :=
  match v_exp, v_cur with
  | LitV l_exp, LitV l_cur => lit_neq m l_exp l_cur
  | _, _ => False
  end.

(** Head steps that do not belong to the machine's SC atomic interface. *)
Inductive lr_head_step
    : expr -> lr_mem -> list lr_mem_ev -> expr -> lr_mem -> Prop :=
| LRBinOpS op l1 l2 l' m :
    bin_op_eval m op l1 l2 l' ->
    lr_head_step
      (BinOp op (Lit l1) (Lit l2)) m []
      (Lit l') m
| LRBetaS f xl e e' el m :
    Forall (fun ei => is_Some (to_val ei)) el ->
    Closed (cons_binder f (app_binder xl [])) e ->
    subst_l (f :: xl) (Rec f xl e :: el) e = Some e' ->
    lr_head_step
      (App (Rec f xl e) el) m []
      e' m
| LRReadNaS l v m :
    m !! l = Some v ->
    lr_head_step
      (Read Na1Ord (Lit (LitLoc l))) m [lr_read_event l]
      (of_val v) m
| LRWriteNaS l e v v' m :
    to_val e = Some v ->
    m !! l = Some v' ->
    lr_head_step
      (Write Na1Ord (Lit (LitLoc l)) e) m [lr_write_event l]
      (Lit LitPoison) (<[l := v]> m)
| LRAllocS n l m :
    0 < n ->
    (forall z, m !! (l +ₗ z)%L = None) ->
    lr_head_step
      (Alloc (Lit (LitInt n))) m
      (lr_alloc_events l (Z.to_nat n))
      (Lit (LitLoc l))
      (init_mem (LitV LitPoison) l (Z.to_nat n) m)
| LRFreeS n l m :
    0 < n ->
    (forall z,
        is_Some (m !! (l +ₗ z)%L) <-> 0 <= z < n) ->
    lr_head_step
      (Free (Lit (LitInt n)) (Lit (LitLoc l))) m
      (lr_free_events l (Z.to_nat n))
      (Lit LitPoison) (free_mem l (Z.to_nat n) m)
| LRCaseS i el e m :
    0 <= i ->
    el !! Z.to_nat i = Some e ->
    lr_head_step
      (Case (Lit (LitInt i)) el) m []
      e m.

(** Evaluation-context closure of [lr_head_step]. *)
Inductive lr_step
    : expr -> lr_mem -> list lr_mem_ev -> expr -> lr_mem -> Prop :=
| LREctxStep K e1 m1 T e2 m2 :
    lr_head_step e1 m1 T e2 m2 ->
    lr_step
      (fill K e1) m1 T
      (fill K e2) m2.

Local Notation lr_atomic_op := (@atomic_op loc val lr_layout).

Definition lr_result_expr (ov : option val) : expr :=
  match ov with
  | Some v => of_val v
  | None => stuck_term
  end.

(** SC operations at the head of an evaluation context. *)
Inductive lr_head_external
    : expr -> lr_atomic_op -> (option val -> expr) -> Prop :=
| LRReadScE l :
    lr_head_external
      (Read ScOrd (Lit (LitLoc l)))
      (ALoad tt l) lr_result_expr
| LRWriteScE l e v :
    to_val e = Some v ->
    lr_head_external
      (Write ScOrd (Lit (LitLoc l)) e)
      (AStore tt l v) (fun _ => Lit LitPoison)
| LRCasE l e1 lit1 e2 lit2 :
    to_val e1 = Some (LitV lit1) ->
    to_val e2 = Some (LitV lit2) ->
    lr_head_external
      (CAS (Lit (LitLoc l)) e1 e2)
      (ACAS tt l (LitV lit1) (LitV lit2)) lr_result_expr.

(** Evaluation-context closure of [lr_head_external]. *)
Inductive lr_external
    : expr -> lr_atomic_op -> (option val -> expr) -> Prop :=
| LREctxExternal K e op k :
    lr_head_external e op k ->
    lr_external
      (fill K e) op
      (fun ov => fill K (k ov)).

(** [Fork] at the head of an evaluation context: the parent continues
    with [LitPoison], as in the reference [ForkS]. *)
Inductive lr_spawn : expr -> expr -> expr -> Prop :=
| LRSpawn K e :
    lr_spawn (fill K (Fork e)) (fill K (Lit LitPoison)) e.

(** A thread has terminated once it is a value. *)
Definition lr_final (e : expr) : Prop := is_Some (to_val e).

#[global] Instance lr_language :
    @sqlang loc val _ _ lr_mem lr_layout lr_memory :=
  {| sqlang_thrd_st := expr;
     sqlang_true_val := LitV (lit_of_bool true);
     sqlang_false_val := LitV (lit_of_bool false);
     sqlang_step := lr_step;
     sqlang_at_external := lr_external;
     sqlang_spawn := lr_spawn;
     sqlang_final := lr_final;
     sqlang_ValEq := lr_val_eq;
     sqlang_ValNEq := lr_val_neq |}.
