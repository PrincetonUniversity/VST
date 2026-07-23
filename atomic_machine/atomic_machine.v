(** *

    This file implements a generic sequentially consistent concurrent semantics,
    lifting a sequential semantics to a sequentially consistent concurrent
    machine with a lambda-Rust-style reader/writer race detector (the `rw_map`)
    and SC atomic operations.

    A machine configuration is <<(tp, m, μ)>> where [tp] is a thread pool,
    [m] a CompCert memory, and [μ] a reader/writer state map.  A thread
    performs a sequential step in two phases: [Core_Try] runs a single thread
    step and "reserve permissions" by updating the "rw_map" and emits a trace of
    "on-going" memory events. If a thread has on-going events, it can only
    execute [Core_Commit] to finish the memory events, and release the reserve.
    Data-race is modeled by failure to reserve in [μ].

 *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import List.
Import ListNotations.

Require Import stdpp.gmap.

(** ** Reader/writer states

    The state of one memory byte, as in lambda-Rust: [Rst n] means [n]
    threads are between Try and Commit of a step that reads the byte;
    [Wst] means some thread is mid-step on a write to it. *)


Section RWMap.

Context {Loc : Type}.
Context {LocEqDec : EqDecision Loc}.
Context {LocCountable : @Countable Loc _}.

Inductive rw_state : Type :=
| Rst (n : nat)
| Wst.

Variant mem_ev : Type :=
| Read (l : Loc)
| Write (l : Loc)
| Alloc (l : Loc)
| Free (l : Loc).

Definition rw_map := gmap Loc rw_state.

Implicit Types (μ : rw_map) (oμ : option rw_map) (l : Loc)
   (ev : mem_ev) (evs : list mem_ev).

Definition initial_rw : rw_map := ∅.

Definition rsv_Alloc μ l : option rw_map :=
  match μ !! l with
  | None => Some $ <[l := Rst 0]> μ
  | _ => None
  end.

(* can't free right now because a subsequent fin_Read needs the location to be define *)
Definition rsv_Free μ : option rw_map :=
   mret μ.

Definition rsv_Write μ l : option rw_map :=
  st ← μ !! l;
  match st with
  | Rst O => Some $ <[l := Wst]> μ
  | _ => None
  end.

Definition rsv_Read μ l : option rw_map :=
  st ← μ !! l;
  match st with
  | Rst n => Some $ <[l := Rst (S n)]> μ
  | _ => None
  end.

Definition fin_Alloc μ : option rw_map := mret μ.

Definition fin_Free μ l : option rw_map :=
  match μ !! l with
  | Some _ => Some $ delete l μ
  | _ => None
  end.

Definition fin_Write μ l : option rw_map :=
  st ← μ !! l;
  match st with
  | Wst => Some $ <[l := Rst O]> μ
  | _ => None
  end.

Definition fin_Read μ l : option rw_map :=
  st ← μ !! l;
  match st with
  | Rst (S n) => Some $ <[l := Rst n]> μ
  | _ => None
  end.

Lemma rsv_Write_fin_Write μ l :
  (μ' ← rsv_Write μ l;
   fin_Write μ' l) = Some μ.
Proof. Admitted.

Lemma rsv_Read_fin_Read μ l :
  (μ' ← rsv_Read μ l;
   fin_Read μ' l) = Some μ.
Proof. Admitted.

Definition rsv_ev ev oμ : option rw_map :=
  μ ← oμ;
  match ev with
  | Read l => rsv_Read μ l
  | Write l => rsv_Write μ l
  | Alloc l => rsv_Alloc μ l
  | Free l => rsv_Free μ
  end.

Definition fin_ev ev oμ : option rw_map :=
  μ ← oμ;
  match ev with
  | Read l => fin_Read μ l
  | Write l => fin_Write μ l
  | Alloc _ => fin_Alloc μ
  | Free l => fin_Free μ l
  end.

(* for memory events, "reserve permission" by updating rw_map *)
Definition rsv evs μ : option rw_map :=
  foldr rsv_ev (Some μ) evs.

(* some memory events release permission after completion. *)
Definition fin evs μ : option rw_map :=
  foldr fin_ev (Some μ) evs.

End RWMap.


Section Memory.
  Class MemMixin {Loc Val : Type} {LocEqDec : EqDecision Loc} {LocCountable : Countable Loc} {Mem : Type} {Layout : Type} : Type := {
    load : Mem -> Loc -> Layout -> option Val;
    store : Mem -> Loc -> Layout -> Val -> option Mem;
    layout_to_locs : Loc -> Layout -> list Loc
  }.

End Memory.

Section AtomicMachine.

Context {Loc Val Mem Layout : Type}.
Context {LocEqDec : EqDecision Loc}.
Context {LocCountable : @Countable Loc _}.

Local Notation mem_ev := (mem_ev(Loc:=Loc)).
Local Notation rw_map := (rw_map(Loc:=Loc)).

Inductive atomic_op : Type :=
| ALoad : Layout -> Loc -> atomic_op
| AStore : Layout -> Loc -> Val -> atomic_op
| ACAS : Layout -> Loc -> Val (* expected val *) ->
        Val (* new val*) -> atomic_op.

(** The type of return value of an atomic operation.
    Loads returns the value read; stores returns nothing; CAS returns a boolean represented in the language's value type. *)
Definition atomic_ret_ty (op : atomic_op) : Type :=
  match op with
  | ALoad _ _ => Val
  | AStore _ _ _ => unit
  | ACAS _ _ _ _ => Val
  end.

(** An atomic request packages an operation with a continuation whose input
    is indexed by that operation.
    TODO can we get rid of the sigma type? *)
Definition atomic_call (C : Type) : Type :=
  { op : atomic_op & atomic_ret_ty op -> C }.

Definition load_call {C : Type} (ly : Layout) (l : Loc) (K : Val -> C)
    : atomic_call C :=
  existT (ALoad ly l) K.

Definition store_call {C : Type}
    (ly : Layout) (l : Loc) (v : Val) (K : unit -> C) : atomic_call C :=
  existT (AStore ly l v) K.

Definition cas_call {C : Type}
    (ly : Layout) (l : Loc) (v_exp v_new : Val) (K : Val -> C)
    : atomic_call C :=
  existT (ACAS ly l v_exp v_new) K.

Class sqlang {MemMixinInst : @MemMixin Loc Val _ _ Mem Layout} : Type := {
  (* thread local state *)
  sqlang_thrd_st : Type;
  (* events emitted by the underlying sequential semantics *)
  sqlang_ev : Type;
  sqlang_true_val : Val;
  sqlang_false_val : Val;
  sqlang_step :
    sqlang_thrd_st -> Mem -> list sqlang_ev -> sqlang_thrd_st -> Mem -> Prop;
  sqlang_into_evs : list sqlang_ev -> list mem_ev;

  sqlang_at_external :
    sqlang_thrd_st -> option (atomic_call sqlang_thrd_st);

  (** Value (in)equality for CAS *)
  sqlang_ValEq : Mem -> Val -> Val -> Prop;
  sqlang_ValNEq : Mem -> Val -> Val -> Prop;
}.

Context {MemMixinInst : @MemMixin Loc Val _ _ Mem Layout}.
Context {L : sqlang}.

Local Notation C := sqlang_thrd_st.
Local Notation E := sqlang_ev.
Local Notation into_evs := sqlang_into_evs.
Local Notation at_external := sqlang_at_external.
Local Notation Vtrue := sqlang_true_val.
Local Notation Vfalse := sqlang_false_val.
Local Notation ValEq := sqlang_ValEq.
Local Notation ValNEq := sqlang_ValNEq.

Implicit Types (μ : rw_map) (oμ : option rw_map) (l : Loc)
   (ev : mem_ev) (evs : list mem_ev) (ly : Layout).

Inductive tstate : Type :=
| Running (c : C) (T : list E)
| StuckState.

Definition tpool := gmap nat tstate.

(** No non-atomic write in progress anywhere in ls. *)
Definition readable μ (ls : list Loc) : Prop :=
  Forall (fun l => μ !! l <> Some Wst) ls.

(** No non-atomic access at all in ls. *)
Definition writable μ (ls : list Loc) : Prop :=
  Forall (fun l => μ !! l = Some (Rst 0)) ls.

Inductive at_step : tpool -> Mem -> rw_map -> tpool -> Mem -> rw_map -> Prop :=

| Core_Try : forall tp m μ i c T c' m' μ'
    (Hget : tp !! i = Some (Running c []))
    (Hstep : sqlang_step c m T c' m')
    (Hreserve : rsv (into_evs T) μ = Some μ'),
    at_step tp m μ (<[i := Running c' T]> tp) m' μ'
  
| Core_Commit : forall tp m μ i c T μ'
    (Hget : tp !! i = Some (Running c T))
    (Hne : T <> [])
    (Hcommit : fin (into_evs T) μ = Some μ'),
    at_step tp m μ (<[i := Running c []]> tp) m μ'

| SC_Read : forall tp m μ i c ly l v (K : Val -> C)
    (Hget : tp !! i = Some (Running c []))
    (Hext : at_external c = Some (load_call ly l K))
    (Hmu : readable μ (layout_to_locs l ly))
    (Hload : load m l ly = Some v),
    at_step tp m μ (<[i := Running (K v) [] ]> tp) m μ

| SC_Write : forall tp m μ i c ly l v m' (K : unit -> C)
    (Hget : tp !! i = Some (Running c []))
    (Hext : at_external c = Some (store_call ly l v K))
    (Hmu : writable μ (layout_to_locs l ly))
    (Hstore : store m l ly v = Some m'),
    at_step tp m μ (<[i := Running (K ()) []]> tp) m' μ

| SC_Cas_Suc : forall tp m μ i c ly l v_exp v_new v_cur m' (K : Val -> C)
    (Hget : tp !! i = Some (Running c []))
    (Hext : at_external c = Some (cas_call ly l v_exp v_new K))
    (Hmu : writable μ (layout_to_locs l ly))
    (Hload : load m l ly = Some v_cur)
    (Heq : ValEq m v_cur v_exp)
    (Hstore : store m l ly v_new = Some m'),
    at_step tp m μ (<[i := Running (K Vtrue) []]> tp) m' μ

| SC_Cas_Fail : forall tp m μ i c ly l v_exp v_new v_cur (K : Val -> C)
    (Hget : tp !! i = Some (Running c []))
    (Hext : at_external c = Some (cas_call ly l v_exp v_new K))
    (Hmu : readable μ (layout_to_locs l ly))
    (Hload : load m l ly = Some v_cur)
    (Hneq : ValNEq m v_cur v_exp),
    at_step tp m μ (<[i := Running (K Vfalse) []]> tp) m μ

(** comparison succeeded, but can't write new value because reserve fails. *)
| SC_Cas_Stuck : forall tp m μ i c ly l v_exp v_new v_cur (K : Val -> C)
    (Hget : tp !! i = Some (Running c []))
    (Hext : at_external c = Some (cas_call ly l v_exp v_new K))
    (Hload : load m l ly = Some v_cur)
    (Heq : ValEq m v_cur v_exp)
    (Ho : ~ writable μ (layout_to_locs l ly)),
    at_step tp m μ (<[i := StuckState]> tp) m μ.

End AtomicMachine.
