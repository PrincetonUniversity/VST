(** The atomic-machine language interface instantiated with Clight's event
    semantics. *)

Require Import compcert.lib.Integers.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.

From Stdlib Require Import Strings.String.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.BinInt.
From Stdlib Require Import Classical_Prop.
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
    (@atomic_op address val memory_chunk Clight_core.CC_core).

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
  Inductive clight_external (ge : Clight.genv)
      : Clight_core.CC_core -> clight_atomic_op ->
        (option val -> Clight_core.CC_core) -> Prop :=
  | ClightExternalLoad sg tyargs tyret cc b ofs k :
      clight_external ge
        (Clight_core.Callstate
          (Ctypes.External (EF_external "atomic_load" sg)
            tyargs tyret cc)
          [Vptr b ofs] k)
        (ALoad Mint32 (b, Ptrofs.unsigned ofs))
        (fun ov => Clight_core.Returnstate (force_val ov) k)
  | ClightExternalStore sg tyargs tyret cc b ofs v k :
      clight_external ge
        (Clight_core.Callstate
          (Ctypes.External (EF_external "atomic_store" sg)
            tyargs tyret cc)
          [Vptr b ofs; v] k)
        (AStore Mint32 (b, Ptrofs.unsigned ofs) v)
        (fun _ => Clight_core.Returnstate Vundef k)
  | ClightExternalCas sg tyargs tyret cc b ofs v_exp v_new k :
      clight_external ge
        (Clight_core.Callstate
          (Ctypes.External (EF_external "atomic_CAS" sg)
            tyargs tyret cc)
          [Vptr b ofs; v_exp; v_new] k)
        (ACAS Mint32 (b, Ptrofs.unsigned ofs) v_exp v_new)
        (fun ov => Clight_core.Returnstate (force_val ov) k)
  | ClightExternalSpawn sg tyargs tyret cc fptr arg k c_new :
      Clight_core.cl_initial_core ge fptr [arg] = Some c_new ->
      clight_external ge
        (Clight_core.Callstate
          (Ctypes.External (EF_external "spawn" sg) tyargs tyret cc)
          [fptr; arg] k)
        (ASpawn c_new) (fun _ => Clight_core.Returnstate Vundef k).

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

  Lemma clight_step_not_final ge c m T c' m' :
    ev_step_with_mem_ev (Clight_evsem.CLC_evsem ge) c m T c' m' ->
    Clight_core.cl_halted c = None.
  Proof.
    intros Hstep. destruct Hstep as [c m T c' m' Hev].
    pose proof (Clight_evsem.CLC_evstep_ax1 ge _ _ _ _ _ Hev) as Hcore.
    inversion Hcore; reflexivity.
  Qed.

  Lemma clight_external_not_final ge c op k :
    clight_external ge c op k -> Clight_core.cl_halted c = None.
  Proof. destruct 1; reflexivity. Qed.

  Lemma clight_step_external_disjoint ge c m T c' m' op k :
    ev_step_with_mem_ev (Clight_evsem.CLC_evsem ge) c m T c' m' ->
    clight_external ge c op k -> False.
  Proof.
    intros Hstep Hext. destruct Hstep as [c m T c' m' Hev].
    pose proof (Clight_evsem.CLC_evstep_ax1 ge _ _ _ _ _ Hev) as Hcore.
    pose proof (Clight_core.cl_corestep_not_at_external ge _ _ _ _ Hcore) as Hnoext.
    inversion Hext; subst; discriminate Hnoext.
  Qed.

  Lemma clight_external_det ge c op1 k1 op2 k2 :
    clight_external ge c op1 k1 -> clight_external ge c op2 k2 ->
    op2 = op1 /\ forall ov, k2 ov = k1 ov.
  Proof.
    intros H1 H2. destruct H1; inversion H2; subst; try discriminate.
    all: split; [congruence | intros ov; reflexivity].
  Qed.

  #[global] Instance Clight_language (ge : Clight.genv)
      : @sqlang address val _ _ mem memory_chunk Clight_core.CC_core.
  Proof.
    refine {| sqlang_memory := clight_mem_mixin;
      sqlang_thrd_st := Clight_core.CC_core;
      sqlang_true_val := Values.Vtrue;
      sqlang_false_val := Values.Vfalse;
      sqlang_step := ev_step_with_mem_ev (Clight_evsem.CLC_evsem ge);
      sqlang_expr_to_thrd_st := id;
      sqlang_at_external := clight_external ge;
      sqlang_is_final := Clight_core.cl_halted;
      sqlang_ValEq := clight_ValEq;
      sqlang_ValNEq := clight_ValNEq |}.
    - intros c m. destruct (Clight_core.cl_halted c) as [v|] eqn:Hfinal.
      + have Hnoext : ~ (exists op k, clight_external ge c op k).
        { intros (op & k & Hext). apply clight_external_not_final in Hext. congruence. }
        have Hnostep : ~ (exists T c' m',
          ev_step_with_mem_ev (Clight_evsem.CLC_evsem ge) c m T c' m').
        { intros (T & c' & m' & Hstep). apply clight_step_not_final in Hstep. congruence. }
        exists SqValue. split; first by exists v.
        intros []; cbn; rewrite /is_Some; naive_solver.
      + destruct (classic (exists T c' m',
          ev_step_with_mem_ev (Clight_evsem.CLC_evsem ge) c m T c' m')) as [Hstep | Hnostep].
        * have Hnoext : ~ (exists op k, clight_external ge c op k).
          { intros (op & k & Hext). destruct Hstep as (T & c' & m' & Hstep).
            by eapply clight_step_external_disjoint. }
          exists SqStep. split; first exact Hstep.
          intros []; cbn; rewrite /is_Some; naive_solver.
        * destruct (classic (exists op k, clight_external ge c op k)) as [Hext | Hnoext].
          -- exists SqExternal. split; first exact Hext.
             intros []; cbn; rewrite /is_Some; naive_solver.
          -- exists SqStuck. split.
             ++ split; first done. done.
             ++ intros []; cbn; rewrite /is_Some; naive_solver.
    - apply clight_external_det.
  Defined.

End ClightInstantiation.
