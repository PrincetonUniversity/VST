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

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import List.
Import ListNotations.

Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.event_semantics.
Require Import stdpp.gmap.
Import Address Values.

(** ** Reader/writer states

    The state of one memory byte, as in lambda-Rust: [Rst n] means [n]
    threads are between Try and Commit of a step that reads the byte;
    [Wst] means some thread is mid-step on a write to it. *)

Section AtomicMachine.
  
Notation Loc := (address)%type.

Inductive rw_state : Type :=
| Rst (n : nat)
| Wst.

Print event_semantics.mem_event.
Variant mem_ev : Type :=
| Read (l : Loc)
| Write (l : Loc)
| Alloc (l : Loc)
| Free (l : Loc).

Definition rw_map := gmap address rw_state.

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

(** ** Atomic operations

    How the underlying language phrases atomic operations as external
    calls is a parameter of the machine ([decode_atomic] below); this is
    their common shape.  Each operation carries the [memory_chunk] it
    accesses. *)

Inductive atomic_op : Type :=
| ALoad (chunk : memory_chunk) l
| AStore (chunk : memory_chunk) l (v : val)
| ACAS (chunk : memory_chunk) l (v_exp v_new : val).

(* The thread local state *)
Context {C : Type}.

(** The single-threaded input semantics. *)
Variable sem : @EvSem C.

Variable into_evs : list mem_event -> list mem_ev.

(** Recognizes the external calls that are this machine's atomic
    operations; all other external calls are outside the machine's scope
    (no rule applies). *)
Variable decode_atomic : external_function -> list val -> option atomic_op.

(** Value (in)equality for CAS, relative to a memory.  In C both are
    deterministic and mutually exclusive (see [c_ValEq]/[c_ValNEq] below);
    in lambda-Rust comparisons involving dangling pointers make them
    overlap, which is what forces the explicit SC_Cas_Stuck rule. *)
Variable ValEq ValNEq : mem -> val -> val -> Prop.

(** ** Thread pools *)

Inductive tstate : Type :=
| Running (c : C) (T : list mem_event)
| StuckState.

Definition tpool := nat -> option tstate.

Definition upd_tp (tp : tpool) (i : nat) (st : tstate) : tpool :=
  fun j => if Nat.eq_dec j i then Some st else tp j.

Definition initial_tp (c : C) : tpool :=
  fun i => if Nat.eq_dec i O then Some (Running c []) else None.

(** [μ] conditions on the byte range of an atomic access *)

(** No non-atomic write in progress anywhere in the range (paper: μ(l) = Rst n). *)
Definition readable μ l (len : Z) : Prop :=
  forall o : Z, Z.le l.2 o /\ Z.lt o (l.2 + len) -> μ !! (l.1, o) <> Some Wst.

(** No non-atomic access at all in progress in the range (paper: μ(l) = Rst 0). *)
Definition writable μ l (len : Z) : Prop :=
  forall o : Z, Z.le (snd l) o /\ Z.lt o (snd l + len) -> μ !! (fst l, o) = Some (Rst 0).

(** ** The machine *)

Inductive step : tpool -> mem -> rw_map -> tpool -> mem -> rw_map -> Prop :=

| Core_Try : forall tp m μ i c T c' m' μ'
    (Hget : tp i = Some (Running c []))
    (Hstep : ev_step sem c m T c' m')
    (Hreserve : rsv (into_evs T) μ = Some μ'),
    step tp m μ (upd_tp tp i (Running c' T)) m' μ'

| Core_Commit : forall tp m μ i c T μ'
    (Hget : tp i = Some (Running c T))
    (Hne : T <> [])
    (Hcommit : fin (into_evs T) μ = Some μ'),
    step tp m μ (upd_tp tp i (Running c [])) m μ'

| SC_Read : forall tp m μ i c ef args chunk l v c'
    (Hget : tp i = Some (Running c []))
    (Hext : at_external sem c m = Some (ef, args))
    (Hdec : decode_atomic ef args = Some (ALoad chunk l))
    (Hmu : readable μ l (size_chunk chunk))
    (Hload : Mem.load chunk m l.1 l.2 = Some v)
    (Hret : after_external sem (Some v) c m = Some c'),
    step tp m μ (upd_tp tp i (Running c' [])) m μ

| SC_Write : forall tp m μ i c ef args chunk l v m' c'
    (Hget : tp i = Some (Running c []))
    (Hext : at_external sem c m = Some (ef, args))
    (Hdec : decode_atomic ef args = Some (AStore chunk l v))
    (Hmu : writable μ l (size_chunk chunk))
    (Hstore : Mem.store chunk m l.1 l.2 v = Some m')
    (Hret : after_external sem None c m' = Some c'),
    step tp m μ (upd_tp tp i (Running c' [])) m' μ

| SC_Cas_Suc : forall tp m μ i c ef args chunk l v_exp v_new v_cur m' c'
    (Hget : tp i = Some (Running c []))
    (Hext : at_external sem c m = Some (ef, args))
    (Hdec : decode_atomic ef args = Some (ACAS chunk l v_exp v_new))
    (Hmu : writable μ l (size_chunk chunk))
    (Hload : Mem.load chunk m l.1 l.2 = Some v_cur)
    (Heq : ValEq m v_cur v_exp)
    (Hstore : Mem.store chunk m l.1 l.2 v_new = Some m')
    (Hret : after_external sem (Some Vtrue) c m' = Some c'),
    step tp m μ (upd_tp tp i (Running c' [])) m' μ

| SC_Cas_Fail : forall tp m μ i c ef args chunk l v_exp v_new v_cur c'
    (Hget : tp i = Some (Running c []))
    (Hext : at_external sem c m = Some (ef, args))
    (Hdec : decode_atomic ef args = Some (ACAS chunk l v_exp v_new))
    (Hmu : readable μ l (size_chunk chunk))
    (Hload : Mem.load chunk m l.1 l.2 = Some v_cur)
    (Hneq : ValNEq m v_cur v_exp)
    (Hret : after_external sem (Some Vfalse) c m = Some c'),
    step tp m μ (upd_tp tp i (Running c' [])) m μ
(* SC_Cas_Stuck is vacuous in CompCert, but non-trivial in lambda-Rust. *)
| SC_Cas_Stuck : forall tp m μ i c ef args chunk l v_exp v_new v_cur (o : Z)
    (Hget : tp i = Some (Running c []))
    (Hext : at_external sem c m = Some (ef, args))
    (Hdec : decode_atomic ef args = Some (ACAS chunk l v_exp v_new))
    (Hload : Mem.load chunk m l.1 l.2 = Some v_cur)
    (Heq : ValEq m v_cur v_exp)
    (Ho : Z.le l.2 o /\ Z.lt o (l.2 + size_chunk chunk))
    (Hmu : μ !! (l.1, o) <> Some (Rst 0)),
    step tp m μ (upd_tp tp i StuckState) m μ.

End AtomicMachine.

(** ** Sample C instantiation of the parameters

    Atomics are word-sized here for concreteness; a real Clight
    instantiation would read the chunk off the external function's
    signature. *)

Section ClightAtomicMachine.

Definition c_decode_atomic (ef : external_function) (args : list val)
  : option atomic_op :=
  match ef, args with
  | EF_external "atomic_load" _, [Vptr b ofs] =>
      Some (ALoad Mint32 (b, (Ptrofs.unsigned ofs)))
  | EF_external "atomic_store" _, [Vptr b ofs; v] =>
      Some (AStore Mint32 (b, (Ptrofs.unsigned ofs)) v)
  | EF_external "atomic_CAS" _, [Vptr b ofs; v_exp; v_new] =>
      Some (ACAS Mint32 (b, (Ptrofs.unsigned ofs)) v_exp v_new)
  | _, _ => None
  end.

(** In C, value comparison is deterministic ([c_ValEq] and [c_ValNEq] are
    mutually exclusive), so SC_Cas_Fail and SC_Cas_Stuck never overlap; a
    comparison that CompCert leaves undefined (e.g. on [Vundef]) satisfies
    neither, and the CAS is stuck with no rule applying. *)

Definition c_ValEq (m : mem) (v1 v2 : val) : Prop :=
  Val.cmpu_bool (Mem.valid_pointer m) Ceq v1 v2 = Some true.

Definition c_ValNEq (m : mem) (v1 v2 : val) : Prop :=
  Val.cmpu_bool (Mem.valid_pointer m) Ceq v1 v2 = Some false.

(* TODO is this sound? *)
Definition memval_value (mv : memval) : val :=
  match mv with
  | Fragment v _ _ => v
  | _ => Vundef
  end.

(* general over Read and Write *)
Definition into_bytes
    (mk_ev : address -> mem_ev) (b : block) (ofs : Z)
    (bytes : list memval) : list mem_ev :=
  foldr
    (fun byte k ofs =>
       mk_ev (b, ofs)  :: k (Z.add ofs 1))
    (fun _ => []) bytes ofs.

(* general over Alloc and Free *)
Definition into_range
    (mk_ev : address -> mem_ev) (b : block) (ofs : Z) (len : nat) : list mem_ev :=
  flat_map
    (fun i => [mk_ev (b, Z.add ofs (Z.of_nat i))])
    (seq 0 len).

Definition into_Allocs (b : block) (lo hi : Z) : list mem_ev :=
  into_range Alloc b lo (Z.to_nat (hi - lo)).

Definition into_Frees (r : block * Z * Z) : list mem_ev :=
  let '(b, lo, hi) := r in
  into_range Free b lo (Z.to_nat (hi - lo)).

(** Translate one event from [event_semantics]. *)
Definition into_ev (ev : mem_event) : list mem_ev :=
  match ev with
  | event_semantics.Read b ofs _ bytes => into_bytes Read b ofs bytes
  | event_semantics.Write b ofs bytes => into_bytes Write b ofs bytes
  | event_semantics.Alloc b lo hi =>
      into_Allocs b lo hi
  | event_semantics.Free ranges =>
      flat_map into_Frees ranges
  end.

(** Translate a trace in event_semantics into AtomicMachine events. *)
Definition into_evs (T : list mem_event) : list mem_ev :=
  flat_map into_ev T.

End ClightAtomicMachine.
