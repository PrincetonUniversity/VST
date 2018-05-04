Require Import compcert.common.Memory.


Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Export VST.concurrency.threadPool.
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.HybridMachineSig.
Require Import VST.concurrency.juicy_machine. Import Concur.
Require Import VST.concurrency.HybridMachine. Import Concur.
(*Require Import VST.concurrency.HybridMachine_lemmas. *)
Require Import VST.concurrency.lksize.
Require Import VST.concurrency.permissions.

Require Import VST.concurrency.TheSchedule.

(*Semantics*)
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clightnew_coop.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.ClightSemantincsForMachines.

Module THE_JUICY_MACHINE.

  Module JuicyMachine := HybridMachineSig.
  Export JuicyMachine.

  Section THE_JUICY_MACHINE.

  Context {ge : genv}.
  Instance JSem : Semantics := ClightSem ge.
  Definition JMachineSem := MachineSemantics(HybridMachine := HybridCoarseMachine.HybridCoarseMachine(machineSig := JuicyMachineShell)).
  Definition jstate := ThreadPool.t(resources := LocksAndResources)(ThreadPool := OrdinalPool.OrdinalThreadPool).
  Definition jmachine_state := MachState(resources := LocksAndResources)(ThreadPool := OrdinalPool.OrdinalThreadPool).

  Import threadPool.ThreadPool.

  (* safety with ghost updates *)
  Definition tp_update (tp : jstate) phi tp' phi' :=
    level phi' = level phi /\ resource_at phi' = resource_at phi /\
    join_all tp' phi' /\
    exists (Hiff : forall t, containsThread tp' t <-> containsThread tp t),
      (forall t (cnt : containsThread tp t), getThreadC cnt = getThreadC (proj2 (Hiff _) cnt) /\
         level (getThreadR cnt) = level (getThreadR (proj2 (Hiff _) cnt)) /\
         resource_at (getThreadR cnt) = resource_at (getThreadR (proj2 (Hiff _) cnt))) /\
      lockGuts tp' = lockGuts tp /\ lockSet tp' = lockSet tp /\
      lockRes tp' = lockRes tp /\ latestThread tp'= latestThread tp.

  Lemma tp_update_refl : forall tp phi, join_all tp phi -> tp_update tp phi tp phi.
  Proof.
    repeat split; auto.
    unshelve eexists; [reflexivity|].
    split; auto; intros.
    replace (proj2 _ _) with cnt by apply proof_irr; auto.
  Qed.

  Definition tp_bupd P (tp : jstate) := (exists phi, join_all tp phi) /\
  forall phi, join_all tp phi ->
    forall c : ghost,
     joins (ghost_of phi) (ghost_fmap (approx (level phi)) (approx (level phi)) (Some (initial_world.ext_ghost tt, NoneP) :: c)) ->
     exists b : ghost,
       joins b (ghost_fmap (approx (level phi)) (approx (level phi)) (Some (initial_world.ext_ghost tt, NoneP) :: c)) /\
       exists phi' tp', tp_update tp phi tp' phi' /\ ghost_of phi' = b /\ P tp'.

  Existing Instance JuicyMachineShell.
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  Existing Instance HybridMachineSig.HybridCoarseMachine.scheduler.

  Inductive jm_csafe (st : jmachine_state) (m : mem) : nat -> Prop :=
  | Safe_0 : jm_csafe st m 0
  | HaltedSafe : forall n : nat,
                 is_true (ssrbool.isSome (halted_machine st)) ->
                 jm_csafe st m n
  | CoreSafe : forall tr' (tp' : jstate) (m' : mem) (n : nat)
               (Hstep : MachStep(Sem := JSem) st m (fst (fst st), tr', tp') m')
               (Hsafe : tp_bupd (fun tp' => jm_csafe (fst (fst st), tr', tp') m' n) tp'),
               jm_csafe st m (S n)
  | AngelSafe : forall tr' (tp' : jstate) (m' : mem) (n : nat)
                (Hstep : MachStep(Sem := JSem) st m
                  (schedSkip (fst (fst st)), tr', tp') m')
                (Hsafe : forall U'',
                 tp_bupd (fun tp' => jm_csafe (U'', tr', tp') m' n) tp'),
                jm_csafe st m (S n).

  End THE_JUICY_MACHINE.

  Arguments jstate : clear implicits.

End THE_JUICY_MACHINE.
