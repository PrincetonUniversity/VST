Require Import compcert.common.Memory.

Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Export VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.juicy.juicy_machine. Import Concur.
(*Require Import VST.concurrency.common.HybridMachine. Import Concur. *)
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.common.permissions.

(*Semantics*)
Require Import VST.veric.Clightcore_coop.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.common.ClightSemanticsForMachines.

Module THE_JUICY_MACHINE.

  Module JuicyMachine := HybridMachineSig.
  Export JuicyMachine.

  Section THE_JUICY_MACHINE.

  Context {ge : Clight.genv}.
  Instance JSem : Semantics := ClightSem ge.
  Context {Σ : gFunctors}.
  Definition JMachineSem := MachineSemantics(HybridMachine := HybridCoarseMachine.HybridCoarseMachine(machineSig:=JuicyMachineShell(Σ := Σ))).
  Definition jstate := ThreadPool.t(resources := LocksAndResources)(ThreadPool := OrdinalPool.OrdinalThreadPool).
  Definition jmachine_state := MachState(resources := LocksAndResources)(ThreadPool := OrdinalPool.OrdinalThreadPool).

  Import threadPool.ThreadPool.

  (* safety with ghost updates? *)
  Definition tp_update (tp : jstate) (phi : rmap) tp' phi' :=
    join_all tp' phi' /\
    exists (Hiff : forall t, containsThread tp' t <-> containsThread tp t),
      (forall t (cnt : containsThread tp t), getThreadC cnt = getThreadC (proj2 (Hiff _) cnt)) /\
      lockGuts tp' = lockGuts tp /\ lockSet tp' = lockSet tp /\
      lockRes tp' = lockRes tp /\ latestThread tp'= latestThread tp /\ extraRes tp' = extraRes tp.

  Lemma tp_update_refl : forall tp phi, join_all tp phi -> tp_update tp phi tp phi.
  Proof.
    repeat split; auto.
    unshelve eexists; [reflexivity|].
    split; auto; intros.
    replace (proj2 _ _) with cnt by apply proof_irr; auto.
  Qed.

  Print bupd.
  Definition tp_bupd P (tp : jstate) :=
  (* Without this initial condition, a thread pool could be vacuously safe by being inconsistent
     with itself or the external environment. Since we want juicy safety to imply dry safety,
     we need to rule out the vacuous case. *)
  (exists phi, join_all tp phi) /\
  (* should we provide a level? *)
  forall phi, join_all tp phi ->
    forall c, valid(A := resource_map.rmapUR _ _) (phi ⋅ c) ->
     exists phi', valid(A := resource_map.rmapUR _ _) (phi' ⋅ c) /\
       exists tp', tp_update tp phi tp' phi' /\ P tp'.

(*  Definition tp_update_weak (tp tp' : jstate) :=
    exists (Hiff : forall t, containsThread tp' t <-> containsThread tp t),
      (forall t (cnt : containsThread tp t), getThreadC cnt = getThreadC (proj2 (Hiff _) cnt) /\
         level (getThreadR cnt) = level (getThreadR (proj2 (Hiff _) cnt))) /\
      lockGuts tp' = lockGuts tp /\ lockSet tp' = lockSet tp /\
      lockRes tp' = lockRes tp /\ latestThread tp'= latestThread tp.

  Lemma tp_update_weak_refl : forall tp, tp_update_weak tp tp.
  Proof.
    unshelve eexists; [reflexivity|].
    split; auto; intros.
    replace (proj2 _ _) with cnt by apply proof_irr; auto.
  Qed.

  (* This is the intuitive definition, but it's dubious from a DRF perspective, since it allows
     threads to transfer writable permissions without a synchronization operation.
     We might instead need to treat each thread as already holding whatever resources it's going
     to extract from invariants. Not sure how that will work. *)
(*  Definition tp_fupd P (tp : jstate) := app_pred invariants.wsat (extraRes tp) /\
    (tp_level_is 0 tp \/
     tp_bupd (fun tp1 => exists phi tp2, join_all tp1 phi /\ join_all tp2 phi /\
       tp_update_weak tp1 tp2 /\ app_pred invariants.wsat (extraRes tp2) /\ P tp2) tp). *)

  (* Try 2: each thread holds the resources it's going to use from the wsat, while extraRes holds the
     shared ghost state. So a fupd really is just a kind of bupd. *)
Definition tp_fupd P (tp : jstate) := exists i (cnti : containsThread tp i),
  exists m r w, join m r (getThreadR cnti) /\ join r (extraRes tp) w /\
    app_pred (invariants.wsat * invariants.ghost_set invariants.g_en Ensembles.Full_set)%pred w /\
    (tp_level_is 0 tp \/
     tp_bupd (fun tp2 => exists (cnti2 : containsThread tp2 i) m2 r2 w2, join m2 r2 (getThreadR cnti2) /\
       join r2 (extraRes tp2) w2 /\ app_pred (invariants.wsat * invariants.ghost_set invariants.g_en Ensembles.Full_set)%pred w2 /\ P tp2) tp).

  (* Try 3: actually, getThreadR gives the resources the current assertion holds on, so we'd need
     an extraRes for each thread. But this doesn't solve the fundamental problem: how do we know
     how to distribute the contents of invariants? *)
*)

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

  Inductive jm_ctrace (st : jmachine_state) (m : mem) : event_trace -> nat -> Prop :=
  | Trace_0 : jm_ctrace st m nil 0
  | HaltedTrace : forall n : nat,
                 is_true (ssrbool.isSome (halted_machine st)) ->
                 jm_ctrace st m nil n
  | CoreTrace : forall tr (tp' : jstate) (m' : mem) tr' (n : nat)
               (Hstep : MachStep(Sem := JSem) st m (fst (fst st), snd (fst st) ++ tr, tp') m')
               (Hsafe : tp_bupd (fun tp' => jm_ctrace (fst (fst st), snd (fst st) ++ tr, tp') m' tr' n) tp'),
               jm_ctrace st m (tr ++ tr') (S n)
  | AngelTrace : forall tr (tp' : jstate) (m' : mem) tr' (n : nat)
                (Hstep : MachStep(Sem := JSem) st m
                  (schedSkip (fst (fst st)), snd (fst st) ++ tr, tp') m')
                (Hsafe : forall U'',
                 tp_bupd (fun tp' => jm_ctrace (U'', snd (fst st) ++ tr, tp') m' tr' n) tp'),
                jm_ctrace st m (tr ++ tr') (S n).

  End THE_JUICY_MACHINE.

  Arguments jstate : clear implicits.

End THE_JUICY_MACHINE.
