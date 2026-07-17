(** * Generic-SC: the lambda-Rust-Generic machine over an event semantics

    This file implements the "lambda-Rust-Generic" (Generic-SC) rules from
    the paper, lifting a sequential event semantics ([EvSem], from
    VST.sepcomp.event_semantics) to a sequentially consistent concurrent
    machine with a lambda-Rust-style reader/writer race detector and SC
    atomic operations.

    A machine configuration is <<(tp, m, μ)>> where [tp] is a thread pool,
    [m] a CompCert memory, and [μ] a reader/writer state map.  A thread
    performs a sequential step in two phases: [Core_Try] runs the underlying
    [ev_step], _reserves_ the footprint of the step's event trace in [μ], and
    installs the trace in the thread pool; [Core_Commit] releases the reserve.
    A reserve that overlaps with another thread's outstanding reserve is
    unsatisfiable, so a racing thread is stuck between another thread's Try
    and Commit -- exactly the lambda-Rust view of non-atomic accesses as
    spanning two steps.  Atomic operations ([SC_Read], [SC_Write], the CAS
    rules) execute in a single machine step and merely check [μ].

    ** Deviations from the rules as written in the paper

    1. Memory is updated at [Core_Try], not at [Core_Commit]; there is no
       [interp]/replay.  The paper notes that for race-free programs the
       choice is immaterial and picks Commit only to align with lambda-Rust.
       Over CompCert memories the Commit choice is in fact not well-defined:
       [Mem.alloc] deterministically returns the current [nextblock], so if
       two threads Try (each recording an [Alloc] of the same fresh block)
       before either Commits, the second Commit cannot replay its trace --
       its recorded block is already taken.  Deferred replay would thus make
       perfectly race-free allocations stuck.  Race detection is unaffected
       by the change, since it lives entirely in [μ], whose reserves still
       span the Try-Commit window.

    2. [reserve]/[commit] fold [incrRW]/[decrRW] over the events of a trace in
       order.  Consequently, overlapping accesses within one trace must be
       accepted by the per-event reader/writer transitions themselves.

    3. Locations are bytes: [μ : block -> Z -> RWState], total, with
       untouched (in particular unallocated) bytes sitting at [Rst 0] --
       the counterpart of absence from the paper's partial map.  Events and
       atomic operations cover byte ranges, and atomics check every byte of
       their chunk's footprint.

    4. The paper lists [AllocEv]/[FreeEv] but only sketches [incrRW] for
       reads.  Here both count as writes: a [Free] racing with a read is a
       race, so the freed range is reserveed; an [Alloc] reserves its entire
       block (following [cur_perm] in event_semantics.v, which also ignores
       the [lo]/[hi] bounds), which is vacuous for other threads -- the
       block is fresh -- but keeps dead bytes uniformly at [Rst 0].

    5. There are no explicit continuations: the paper's
       [at_external(op, vs, K)] becomes [at_external] returning an external
       function plus arguments, decoded by the [decode_atomic] parameter,
       and [K[[v]]] becomes [after_external].  N.B. the paper's remark that
       "RetKind = Unit for atomic read, and RetKind = Val for atomic write"
       has the two swapped; here a read returns [Some v], a write returns
       [None] (unit), and CAS returns [Some Vtrue]/[Some Vfalse].

    6. The paper's SC-Cas-Suc does not update the memory, so a successful
       CAS would never store [v_new]; here it does ([Mem.store]).

    7. The paper's SC-Cas-Fail requires [n > 0], under which a failing CAS
       with no concurrent readers would be stuck; here it only requires
       that no non-atomic write be in progress (any [Rst n]).  The [n > 0]
       looks like a copy-paste from SC-Cas-Stuck.

    8. The core-state type [C] has no distinguished stuck state, so thread
       pool entries are [Running c T] or [StuckState], and SC_Cas_Stuck
       moves the thread to [StuckState].  Its side condition is generalized
       from "[Rst n], [n > 0]" to "some byte of the footprint is not
       [Rst 0]": a would-succeed CAS during a non-atomic _write_ is equally
       a race, and this way it is reported by the same rule rather than by
       implicit stuckness.  (The rule must exist at all because [ValEq] and
       [ValNEq] may overlap -- lambda-Rust's [lit_eq] is nondeterministic --
       and safety must not be able to escape through SC_Cas-Fail when the
       racy success branch is also enabled.)

    9. [ValEq]/[ValNEq] and [decode_atomic] are parameters of the machine,
       instantiated per language; sample C instantiations are given at the
       end of the file.  Atomic operations carry a [memory_chunk], since a
       CompCert memory access needs one (the paper's abstract locations
       hold whole values).

    10. As in the paper's Generic-SC figure (and unlike APM), there is no
        scheduler: the stepping thread is chosen nondeterministically.  The
        figure has no spawn/halt rules, so none are given here either. *)

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
