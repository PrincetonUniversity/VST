Require Import compcert.lib.Axioms.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import concurrency.mem_obs_eq.
Require Import concurrency.dry_context.
Require Import concurrency.fineConc_safe.
Require Import Coqlib.
Require Import msl.Coqlib2.


Import dry_context SEM mySchedule DryMachine DryMachine.ThreadPool.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

(** ** Safety for X86-SC semantics *)
Module X86Safe.
  Import Asm Asm_coop event_semantics FineConcSafe Events.

  Definition sc_init f arg := initial_core x86_sc_semantics the_ge f arg.
  
  Notation sc_safe := (X86SC.fsafe the_ge).

  (*TODO: This will be very similar (what an irony) to
  similar_threadPool, but now we need a more invloved relation on
  cores that says that things may be more defined. Do we have one? *)
  
  Inductive erasePool (tpf:FineConc.machine_state) (tpsc:X86SC.machine_state) : Prop :=
  | ErasePool:
        num_threads tpf = ErasedMachine.ThreadPool.num_threads tpsc ->
        (forall i (pffi: containsThread tpf i)
           (pfsci: ErasedMachine.ThreadPool.containsThread tpsc i),
            getThreadC pffi = ErasedMachine.ThreadPool.getThreadC pfsci) ->
        erasePool tpf tpsc.

  (** The initial state of X86SC is an erasure of the initial state of
  the FineConc machine *)
  Lemma init_erasure:
    forall f arg U tpsc tpf
      (HinitSC: sc_init f arg = Some (U, [::], tpsc))
      (HinitF: tpf_init f arg = Some (U, [::], tpf)),
      erasePool tpf tpsc.
  Proof.
    intros.
    unfold sc_init, tpf_init in *.
    simpl in *. unfold X86SC.init_machine, FineConc.init_machine in *.
    unfold init_mach, ErasedMachine.init_mach in *.
    simpl in *.
    destruct (Asm_initial_core the_ge f arg); try discriminate.
    destruct init_perm; try discriminate.
    inv HinitSC. inv HinitF.
    unfold initial_machine, ErasedMachine.initial_machine.
    simpl.
    econstructor; simpl; eauto.
  Qed.
    
  (** Erasure from FineConc to X86-SC.*)
  Conjecture x86sc_erasure:
    forall sched f arg U tpsc tpf m trace
      (Hmem: init_mem = Some m)
      (HinitSC: sc_init f arg = Some (U, [::], tpsc))
      (HinitF: tpf_init f arg = Some (U, [::], tpf))
      (HsafeF: fsafe tpf m sched trace (size sched).+1),
      sc_safe tpsc (diluteMem m) sched trace (size sched).+1.

  (** Competing Events *)
  
  Definition competes (ev1 ev2 : machine_event) : Prop :=
    thread_id ev1 <> thread_id ev2 /\
    location ev1 = location ev2 /\
    (is_internal ev1 ->
     is_internal ev2 ->
     action ev1 = Some Write \/ action ev2 = Some Write) /\
    (is_external ev1 \/ is_external ev2 ->
     action ev1 = Some Mklock \/ action ev1 = Some Freelock
     \/ action ev2 = Some Mklock \/ action ev2 = Some Freelock).

  (** Spinlock well synchronized*)
  Definition spinlock_synchronized (tr : X86SC.event_trace) :=
    forall i j ev1 ev2,
      i < j ->
      List.nth_error tr i = Some ev1 ->
      List.nth_error tr j = Some ev2 ->
      competes ev1 ev2 ->
      exists u v eu ev,
        i < u < v < j /\
        List.nth_error tr u = Some eu /\
        List.nth_error tr v = Some ev /\
        action eu = Some Release /\ action ev = Some Acquire /\
        location eu = location ev.

  (** Spinlock clean *)
  Definition spinlock_clean (tr : X86SC.event_trace) :=
    forall i j evi evj,
      i < j ->
      List.nth_error tr i = Some evi ->
      List.nth_error tr j = Some evj ->
      action evi = Some Mklock ->
      (~ exists u evu, i < u < j /\ List.nth_error tr u = Some evu /\
                  action evu = Some Freelock /\ location evu = location evi) ->
      location evj = location evi ->
      action evj <> Some Write /\ action evj <> Some Read.
  
End X86Safe.

  
  



