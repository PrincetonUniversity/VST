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
Require Import VST.veric.val_lemmas.
Set Warnings "custom-entry-overridden".
Require Import VST.atomic_machine.atomic_machine.

Import Address Values.

Section ClightInstantiation.

  (** Clight-specialized atomic-machine types. *)
  Local Notation clight_mem_ev := (@mem_ev address).
  Local Notation clight_atomic_op :=
    (@atomic_op address val memory_chunk).

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

  (** Atomic external calls and their post-call continuations. *)
  Inductive clight_external
      : Clight_core.CC_core -> clight_atomic_op ->
        (option val -> Clight_core.CC_core) -> Prop :=
  | ClightExternalLoad sg tyargs tyret cc b ofs k :
      clight_external
        (Clight_core.Callstate
          (Ctypes.External (EF_external "atomic_load" sg)
            tyargs tyret cc)
          [Vptr b ofs] k)
        (ALoad Mint32 (b, Ptrofs.unsigned ofs))
        (fun ov => Clight_core.Returnstate (force_val ov) k)
  | ClightExternalStore sg tyargs tyret cc b ofs v k :
      clight_external
        (Clight_core.Callstate
          (Ctypes.External (EF_external "atomic_store" sg)
            tyargs tyret cc)
          [Vptr b ofs; v] k)
        (AStore Mint32 (b, Ptrofs.unsigned ofs) v)
        (fun _ => Clight_core.Returnstate Vundef k)
  | ClightExternalCas sg tyargs tyret cc b ofs v_exp v_new k :
      clight_external
        (Clight_core.Callstate
          (Ctypes.External (EF_external "atomic_CAS" sg)
            tyargs tyret cc)
          [Vptr b ofs; v_exp; v_new] k)
        (ACAS Mint32 (b, Ptrofs.unsigned ofs) v_exp v_new)
        (fun ov => Clight_core.Returnstate (force_val ov) k).

  #[global] Instance clight_mem_mixin :
      Memory (Loc := address) (Val := val)
        (Mem := mem) (Layout := memory_chunk) :=
    {| load := fun m l chunk =>
        let '(b, ofs) := l in Mem.load chunk m b ofs;
      store := fun m l chunk v => 
        let '(b, ofs) := l in Mem.store chunk m b ofs v;
      layout_to_locs := fun l chunk =>
        byte_addresses l (size_chunk_nat chunk) |}.

  (* event_semantics.ev_step but events are turned into mem_ev *)
  Inductive ev_step_with_mem_ev
      (evsem_inst : @event_semantics.EvSem Clight_core.CC_core) :
      Clight_core.CC_core -> mem -> list clight_mem_ev ->
      Clight_core.CC_core -> mem -> Prop :=
  | ev_step_with_mem_ev_intro c m T c' m' :
      event_semantics.ev_step evsem_inst c m T c' m' ->
      ev_step_with_mem_ev evsem_inst c m (clight_into_evs T) c' m'.

  #[global] Instance Clight_language (ge : Clight.genv)
      : @sqlang address val _ _ mem memory_chunk clight_mem_mixin :=
    {| sqlang_thrd_st := Clight_core.CC_core;
      sqlang_true_val := Values.Vtrue;
      sqlang_false_val := Values.Vfalse;
      sqlang_step := ev_step_with_mem_ev (Clight_evsem.CLC_evsem ge);
      sqlang_at_external := clight_external;
      sqlang_ValEq := clight_ValEq;
      sqlang_ValNEq := clight_ValNEq |}.

End ClightInstantiation.
