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
  
  Parameter erasePool : FineConc.machine_state -> X86SC.machine_state -> Prop.
  (** Erasure from FineConc to X86-SC.*)
  Conjecture x86sc_erasure:
    forall sched f arg U tpsc tpf m trace
      (Hmem: init_mem = Some m)
      (HinitSC: sc_init f arg = Some (U, [::], tpsc))
      (HinitF: tpf_init f arg = Some (U, [::], tpf))
      (HsafeF: fsafe tpf m sched trace (size sched).+1),
      sc_safe tpsc (diluteMem m) sched trace (size sched).+1.

  (** Competing Events *)
  
  (* Definition compete (ev1 ev2 : machine_event) (tr : event_trace) : Prop := *)
  (*   exists n m, *)
  (*     List.nth_error tr n = Some ev1 /\ *)
  (*     List.nth_error tr m = Some ev2 /\ *)
  (*     thread_id ev1 <> thread_id ev2 /\ *)
      
End X86Safe.

  
  



