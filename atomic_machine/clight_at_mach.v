(** The atomic-machine language interface instantiated with Clight's event
    semantics. *)

Require Import compcert.lib.Integers.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.

From Stdlib Require Import Strings.String.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.BinInt.
Import ListNotations.

Require Import VST.sepcomp.event_semantics.
Set Warnings "-custom-entry-overridden".
Require Import VST.veric.Clight_evsem.
Set Warnings "custom-entry-overridden".
Require Import atomic_machine.atomic_machine.

Import Address Values.

Section ClightInstantiation.

(** Clight-specialized atomic-machine types. *)
Local Notation clight_mem_ev := (@mem_ev address).

(** THe memory chunk (size of data) is hardcoded for each function name. *)
Definition clight_decode_atomic (ef : external_function) (args : list val)
    : option (@atomic_op address val memory_chunk) :=
  match ef, args with
  | EF_external "atomic_load" _, [Vptr b ofs] =>
      Some (ALoad Mint32 (b, Ptrofs.unsigned ofs))
  | EF_external "atomic_store" _, [Vptr b ofs; v] =>
      Some (AStore Mint32 (b, Ptrofs.unsigned ofs) v)
  | EF_external "atomic_CAS" _, [Vptr b ofs; v_exp; v_new] =>
      Some (ACAS Mint32 (b, Ptrofs.unsigned ofs) v_exp v_new)
  | _, _ => None
  end.

Definition clight_ValEq (m : mem) (v1 v2 : val) : Prop :=
  Val.cmpu_bool (Mem.valid_pointer m) Ceq v1 v2 = Some true.

Definition clight_ValNEq (m : mem) (v1 v2 : val) : Prop :=
  Val.cmpu_bool (Mem.valid_pointer m) Ceq v1 v2 = Some false.

Local Definition byte_addresses
    (l : address) (len : nat) : list address :=
  let '(b, ofs) := l in
  map (fun i => (b, ofs + Z.of_nat i)) (seq 0 len).

Local Definition into_bytes
    (mk_ev : address -> clight_mem_ev) (b : block) (ofs : Z)
    (bytes : list memval) : list clight_mem_ev :=
  map mk_ev (byte_addresses (b, ofs) (length bytes)).

Local Definition into_range
    (mk_ev : address -> clight_mem_ev)
    (b : block) (ofs : Z) (len : nat) : list clight_mem_ev :=
  map mk_ev (byte_addresses (b, ofs) len).

Local Definition into_alloc (b : block) (lo hi : Z)
    : list clight_mem_ev :=
  into_range Alloc b lo (Z.to_nat (hi - lo)).

Local Definition into_free_range (r : block * Z * Z)
    : list clight_mem_ev :=
  let '(b, lo, hi) := r in
  into_range Free b lo (Z.to_nat (hi - lo)).

(** Expand each evsem event into byte-granular atomic-machine events. *)
Definition clight_into_ev (ev : mem_event) : list clight_mem_ev :=
  match ev with
  | event_semantics.Read b ofs _ bytes => into_bytes Read b ofs bytes
  | event_semantics.Write b ofs bytes => into_bytes Write b ofs bytes
  | event_semantics.Alloc b lo hi => into_alloc b lo hi
  | event_semantics.Free ranges => flat_map into_free_range ranges
  end.

Definition clight_into_evs (trace : list mem_event) : list clight_mem_ev :=
  flat_map clight_into_ev trace.

(** Similar to compcert at_external, but also computes the continuation after
    each atomic operation.
 *)
Definition clight_at_external
    (c : Clight_core.CC_core)
    : option (@atomic_call address val memory_chunk Clight_core.CC_core) :=
  match c with
  | Clight_core.Callstate (Ctypes.External ef _ _ _) args k =>
      match clight_decode_atomic ef args with
      | Some (ALoad ly l) =>
          Some (load_call ly l (fun v => Clight_core.Returnstate v k))
      | Some (AStore ly l v) =>
          Some (store_call ly l v
                  (fun _ : unit => Clight_core.Returnstate Vundef k))
      | Some (ACAS ly l v_exp v_new) =>
          Some (cas_call ly l v_exp v_new
                  (fun v => Clight_core.Returnstate v k))
      | None => None
      end
  | _ => None
  end.

#[local] Instance clight_mem_mixin :
    MemMixin (Loc := address) (Val := val)
      (Mem := mem) (Layout := memory_chunk) :=
  {| load := fun m l chunk =>
       let '(b, ofs) := l in Mem.load chunk m b ofs;
     store := fun m l chunk v => 
       let '(b, ofs) := l in Mem.store chunk m b ofs v;
     layout_to_locs := fun l chunk =>
       byte_addresses l (size_chunk_nat chunk) |}.

Definition Clight_language (ge : Clight.genv)
    : @sqlang address val mem memory_chunk :=
  {| sqlang_thrd_st := Clight_core.CC_core;
     sqlang_ev := event_semantics.mem_event;
     sqlang_true_val := Values.Vtrue;
     sqlang_false_val := Values.Vfalse;
     sqlang_step := event_semantics.ev_step (Clight_evsem.CLC_evsem ge);
     sqlang_into_evs := clight_into_evs;
     sqlang_at_external := clight_at_external;
     sqlang_ValEq := clight_ValEq;
     sqlang_ValNEq := clight_ValNEq |}.

(** shorthands. *)
Definition Clight_tstate (ge : Clight.genv) := tstate (Clight_language ge).
Definition Clight_tpool (ge : Clight.genv) := tpool (Clight_language ge).
Definition Clight_step (ge : Clight.genv) := step (Clight_language ge).

End ClightInstantiation.
