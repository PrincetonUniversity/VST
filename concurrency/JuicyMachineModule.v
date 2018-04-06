Require Import compcert.common.Memory.


Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
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
  Module SCH:= THESCH.
  Module SEM:= ClightSEM.
  Import SCH SEM.

  (* JuicyMachineShell : Semantics -> ConcurrentSemanticsSig *)
  Module JSEM := JuicyMachineShell SEM.
  (* CoarseMachine : Schedule -> ConcurrentSemanticsSig -> ConcurrentSemantics *)
  Module JuicyMachine := CoarseMachine SCH JSEM.
  Notation JMachineSem:= JuicyMachine.MachineSemantics.
  Notation jstate:= JuicyMachine.SIG.ThreadPool.t.
  Notation jmachine_state:= JuicyMachine.MachState.
  Module JTP:=JuicyMachine.SIG.ThreadPool.
  Import JSEM.JuicyMachineLemmas.

  (* safety with ghost updates *)
  Definition tp_update tp phi tp' phi' :=
    level phi' = level phi /\ resource_at phi' = resource_at phi /\
    JSEM.join_all tp' phi' /\
    exists (Hiff : forall t, JTP.containsThread tp' t <-> JTP.containsThread tp t),
      (forall t (cnt : JTP.containsThread tp t), JTP.getThreadC cnt = JTP.getThreadC (proj2 (Hiff _) cnt) /\
         level (JTP.getThreadR cnt) = level (JTP.getThreadR (proj2 (Hiff _) cnt)) /\
         resource_at (JTP.getThreadR cnt) = resource_at (JTP.getThreadR (proj2 (Hiff _) cnt))) /\
      JTP.lockGuts tp' = JTP.lockGuts tp /\ JTP.lockSet tp' = JTP.lockSet tp /\
      JTP.lockRes tp' = JTP.lockRes tp /\ JTP.latestThread tp'= JTP.latestThread tp.

  Lemma tp_update_refl : forall tp phi, JSEM.join_all tp phi -> tp_update tp phi tp phi.
  Proof.
    repeat split; auto.
    unshelve eexists; [reflexivity|].
    split; auto; intros.
    replace (proj2 _ _) with cnt by apply proof_irr; auto.
  Qed.

  Definition tp_bupd P (tp : jstate) := (exists phi, JSEM.join_all tp phi) /\
  forall phi, JSEM.join_all tp phi ->
    forall c : ghost,
     joins (ghost_of phi) (ghost_fmap (approx (level phi)) (approx (level phi)) c) ->
     exists b : ghost,
       joins b (ghost_fmap (approx (level phi)) (approx (level phi)) c) /\
       exists phi' tp', tp_update tp phi tp' phi' /\ ghost_of phi' = b /\ P tp'.

  Inductive jm_csafe (ge : SEM.G) (st : jmachine_state) (m : mem) : nat -> Prop :=
  | Safe_0 : jm_csafe ge st m 0
  | HaltedSafe : forall n : nat,
                 is_true (ssrbool.isSome (JuicyMachine.halted st)) ->
                 jm_csafe ge st m n
  | CoreSafe : forall (tp' : jstate) (m' : mem) (n : nat)
               (Hstep : JuicyMachine.MachStep ge st m (fst (fst st), nil, tp') m')
               (Hsafe : tp_bupd (fun tp' => jm_csafe ge (fst (fst st), nil, tp') m' n) tp'),
               jm_csafe ge st m (S n)
  | AngelSafe : forall (tp' : jstate) (m' : mem) (n : nat)
                (Hstep : JuicyMachine.MachStep ge st m
                  (SCH.schedSkip (fst (fst st)), nil, tp') m')
                (Hsafe : forall U'' : JuicyMachine.Sch,
                 tp_bupd (fun tp' => jm_csafe ge (U'', nil, tp') m' n) tp'),
                jm_csafe ge st m (S n).

End THE_JUICY_MACHINE.
