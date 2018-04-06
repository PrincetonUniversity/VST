From mathcomp.ssreflect Require Import ssreflect seq ssrbool.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.

Require Import VST.msl.Axioms.
Require Import Coq.ZArith.ZArith.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.event_semantics.
Require Export VST.concurrency.semantics.
Require Import VST.concurrency.threadPool. Export threadPool.

Require Import VST.concurrency.machine_semantics.
Require Import VST.concurrency.permissions.
Require Import VST.concurrency.bounded_maps.
Require Import VST.concurrency.addressFiniteMap.

Require Import VST.concurrency.scheduler.
Require Import Coq.Program.Program.

Require Import VST.concurrency.safety.

Require Import VST.concurrency.coinductive_safety.



Notation EXIT :=
  (EF_external "EXIT" (mksignature (AST.Tint::nil) None)).

Notation CREATE_SIG := (mksignature (AST.Tint::AST.Tint::nil) None cc_default).
Notation CREATE := (EF_external "spawn" CREATE_SIG).

Notation READ :=
  (EF_external "READ"
               (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint) cc_default)).
Notation WRITE :=
  (EF_external "WRITE"
               (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint) cc_default)).

Notation MKLOCK :=
  (EF_external "makelock" (mksignature (AST.Tint::nil) None cc_default)).
Notation FREE_LOCK :=
  (EF_external "freelock" (mksignature (AST.Tint::nil) None cc_default)).

Notation LOCK_SIG := (mksignature (AST.Tint::nil) None cc_default).
Notation LOCK := (EF_external "acquire" LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) None cc_default).
Notation UNLOCK := (EF_external "release" UNLOCK_SIG).


  Section Events.
    Definition evRes := (access_map * access_map)%type.
    Definition evDelta := (delta_map * delta_map)%type.
    
    Inductive sync_event : Type :=
    | release : address (*-> option (evRes * evDelta)*) -> option evRes -> sync_event
    | acquire : address (*-> option (evRextes * evDelta)*) -> option evDelta -> sync_event
    | mklock :  address -> sync_event
    | freelock : address -> sync_event
    | spawn : address -> option (evRes * evDelta) -> option evDelta -> sync_event
    | failacq: address -> sync_event.
    
    Inductive machine_event : Type :=
    | internal: nat -> mem_event -> machine_event
    | external : nat -> sync_event -> machine_event.
  End Events.

Section HybridMachineSig.

  
  Variable Resources: Resources_rec.
  Notation res:= (recres Resources).
  Notation lock_info:= (reclock_info Resources).

  Variable Sem: Semantics_rec.
  Notation C:= (semC Sem).
  Notation G:= (semG Sem).
  
  Variable ThreadPool : ThredPool_rec Resources Sem.
  Notation thread_pool := (t_ ThreadPool).
  Notation containsThread := (@containsThread_ _ _ ThreadPool).
  Notation getThreadC:= (@getThreadC_ _ _ ThreadPool).
  Notation getThreadR:= (getThreadR_ ThreadPool).
  Notation lockGuts:= (lockGuts_ ThreadPool).
  Notation lockSet:= (lockSet_ ThreadPool).
  Notation lockRes:= (lockRes_ ThreadPool).
  Notation addThread:= (addThread_ ThreadPool).
  Notation updThreadC:= (@updThreadC_ _ _ ThreadPool).
  Notation updThreadR:= (updThreadR_ ThreadPool).
  Notation updThread:= (updThread_ ThreadPool).
  Notation updLockSet:= (updLockSet_ ThreadPool).
  Notation remLockSet:= (remLockSet_ ThreadPool).
  Notation latestThread:= (latestThread_ ThreadPool).
  Notation lr_valid:= (lr_valid_ ThreadPool).
  Notation find_thread:= (find_thread_ ThreadPool).

  Local Notation ctl := (@ctl C).
  (** Memories*)

  Record MachineSig_rec := {
  richMem: Type
  ; dryMem: richMem -> mem
  ; diluteMem : mem -> mem

  (** Environment and Threadwise semantics *)
  (** These values come from SEM *)

  (** The thread pool respects the memory*)
  ; mem_compatible: thread_pool -> mem -> Prop
  ; invariant: thread_pool -> Prop

  (** Step relations *)
  ; threadStep:
    G -> forall {tid0 ms m},
      containsThread ms tid0 -> mem_compatible ms m ->
      thread_pool -> mem -> seq mem_event -> Prop
  ;  threadStep_equal_run:
    forall g i tp m cnt cmpt tp' m' tr,
      @threadStep g i tp m cnt cmpt tp' m' tr ->
      forall (j: nat),
        (exists cntj q, (@getThreadC) j tp cntj = Krun q) <->
        (exists cntj' q', @getThreadC j tp' cntj' = Krun q')
  ; syncStep:
    bool -> (* if it's a Coarse machine. Temp solution to propagating changes. *)
    G -> forall {tid0 ms m},
      containsThread ms tid0 -> mem_compatible ms m ->
      thread_pool -> mem -> sync_event -> Prop

  ;  syncstep_equal_run:
    forall b g i tp m cnt cmpt tp' m' tr,
      @syncStep b g i tp m cnt cmpt tp' m' tr ->
      forall j,
        (exists cntj q, @getThreadC j tp cntj = Krun q) <->
        (exists cntj' q', @getThreadC j tp' cntj' = Krun q')

  ;  syncstep_not_running:
    forall b g i tp m cnt cmpt tp' m' tr,
      @syncStep b g i tp m cnt cmpt tp' m' tr ->
      forall cntj q, ~ @getThreadC i tp cntj = Krun q

  ; threadHalted:
    forall {tid0 ms},
      containsThread ms tid0 -> Prop

  ;  threadHalt_update:
    forall i j, i <> j ->
      forall tp cnt cnti c' cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j (@updThreadC i tp cnti c') cnt') 

  ;  syncstep_equal_halted:
    forall b g i tp m cnti cmpt tp' m' tr,
      @syncStep b g i tp m cnti cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j tp' cnt')

  ;  threadStep_not_unhalts:
    forall g i tp m cnt cmpt tp' m' tr,
      @threadStep g i tp m cnt cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) ->
        (@threadHalted j tp' cnt') 


  (*Parameter initial_machine: C -> thread_pool.*)

  ; init_mach : option res  -> G -> mem -> val -> list val -> option (thread_pool * option mem)}.

End HybridMachineSig.


Section HybridMachine.

  
  Variable Resources: Resources_rec.
  Notation res:= (recres Resources).
  Notation lock_info:= (reclock_info Resources).

  Variable Sem: Semantics_rec.
  Notation C:= (semC Sem).
  Notation G:= (semG Sem).
  
  Variable ThreadPool : ThredPool_rec Resources Sem.
  Notation thread_pool := (t ThreadPool).
  Notation containsThread := (@containsThread _ _ ThreadPool).
  Notation getThreadC:= (@getThreadC _ _ ThreadPool).
  Notation getThreadR:= (getThreadR ThreadPool).
  Notation lockGuts:= (lockGuts ThreadPool).
  Notation lockSet:= (lockSet ThreadPool).
  Notation lockRes:= (lockRes ThreadPool).
  Notation addThread:= (addThread ThreadPool).
  Notation updThreadC:= (@updThreadC _ _ ThreadPool).
  Notation updThreadR:= (updThreadR ThreadPool).
  Notation updThread:= (updThread ThreadPool).
  Notation updLockSet:= (updLockSet ThreadPool).
  Notation remLockSet:= (remLockSet ThreadPool).
  Notation latestThread:= (latestThread ThreadPool).
  Notation lr_valid:= (lr_valid ThreadPool).
  Notation find_thread:= (find_thread ThreadPool).

  Variable MachineSig: MachineSig_rec Resources Sem ThreadPool.
  
  Notation event_trace := (seq machine_event).
  Notation schedule := (seq nat).
  Notation t:= (@t_ _ _ ThreadPool).
  
  Definition MachState : Type:= (schedule * event_trace * t)%type.

  
  Record HybridMachine_rec:=
    {
      MachineSemantics: schedule -> option res ->
                        CoreSemantics G MachState mem
      ; initial_schedule: forall genv m main vals U U' p c tr m' n,
          initial_core (MachineSemantics U p) n genv m main vals = Some ((U',tr,c),m') ->
          U' = U /\ tr = nil
    }.
End HybridMachine.


Section HybridCoarseMachine.
  
(* Module CoarseMachine (SCH:Scheduler)(SIG : ConcurrentMachineSig with Module ThreadPool.TID:=SCH.TID with Module Events.TID :=SCH.TID) <: ConcurrentMachine with Module SCH:= SCH with Module TP:= SIG.ThreadPool  with Module SIG:= SIG. *)

  Variable Resources: Resources_rec.
  Notation res:= (recres Resources).
  Notation lock_info:= (reclock_info Resources).

  Variable Sem_rec: Semantics_rec.
  Notation C:= (semC Sem_rec).
  Notation G:= (semG Sem_rec).
  Notation Sem:= (semSem Sem_rec).
  
  Variable ThreadPool : ThredPool_rec Resources Sem_rec.
  Notation thread_pool := (t_ ThreadPool).
  Notation containsThread := (@containsThread _ _ ThreadPool).
  Notation getThreadC:= (@getThreadC _ _ ThreadPool).
  Notation getThreadR:= (getThreadR ThreadPool).
  Notation lockGuts:= (lockGuts ThreadPool).
  Notation lockSet:= (lockSet ThreadPool).
  Notation lockRes:= (lockRes ThreadPool).
  Notation addThread:= (addThread ThreadPool).
  Notation updThreadC:= (@updThreadC _ _ ThreadPool).
  Notation updThreadR:= (updThreadR ThreadPool).
  Notation updThread:= (updThread ThreadPool).
  Notation updLockSet:= (updLockSet ThreadPool).
  Notation remLockSet:= (remLockSet ThreadPool).
  Notation latestThread:= (latestThread ThreadPool).
  Notation lr_valid:= (lr_valid ThreadPool).
  Notation find_thread:= (find_thread ThreadPool).

  Variable MachineSig: MachineSig_rec Resources Sem_rec ThreadPool.
  
  Notation event_trace := (seq machine_event).
  Notation schedule := (seq nat).
  Notation t:= (@t _ _ ThreadPool).

  Variable HybridMachine : (HybridMachine_rec _ _ ThreadPool).
  Notation invariant := (@invariant _ _ _ MachineSig).
  Notation mem_compatible := (@mem_compatible _ _ _ MachineSig).
  Notation threadStep := (@threadStep _ _ _ MachineSig).
  Notation syncStep := (@syncStep _ _ _ MachineSig).
  Notation threadHalted := (@threadHalted _ _ _ MachineSig).
  Notation init_mach := (@init_mach _ _ _ MachineSig).

  (*Schedule*)
  Notation Sch:=(seq nat).
  Definition schedPeek sch: option nat:=
    match sch with
      nil => None
    | cons hd tl => Some hd
    end.
  
  Definition schedSkip sch: (seq nat):= List.tl sch.
  Notation machine_state := thread_pool.

  (** Resume and Suspend: threads running must be preceded by a Resume
     and followed by Suspend.  This functions wrap the state to
     indicate it's ready to take a syncronisation step or resume
     running. (This keeps the invariant that at most one thread is not
     at_external) *)

  Inductive start_thread' genv: forall (m: mem) {tid0} {ms:machine_state},
      containsThread_ _ ms tid0 -> machine_state -> mem -> Prop:=
  | StartThread: forall m tid0 ms ms' c_new om vf arg
                    (ctn: containsThread_ _ ms tid0)
                    (Hcode: getThreadC_ _ ctn = Kinit vf arg)
                    (Hinitial: initial_core Sem tid0
                                            genv m vf (arg::nil) = Some (c_new, om))
                    (Hinv: invariant ms)
                    (Hms': updThreadC_ _ ctn (Krun c_new)  = ms'),
      start_thread' genv m ctn ms' (option_proj m om).
  Definition start_thread genv: forall m {tid0 ms},
      containsThread_ _ ms tid0 -> machine_state -> mem -> Prop:=
    @start_thread' genv.
  Inductive resume_thread' ge: forall (m: mem) {tid0} {ms:machine_state},
      containsThread_ _ ms tid0 -> machine_state -> Prop:=
  | ResumeThread: forall m tid0 ms ms' c c' X
                    (ctn: containsThread_ _ ms tid0)
                    (Hat_external: at_external Sem ge c m = Some X)
                    (Hafter_external: after_external Sem ge None c = Some c')
                    (Hcode: getThreadC_ _ ctn = Kresume c Vundef)
                    (Hinv: invariant ms)
                    (Hms': updThreadC_ _ ctn (Krun c')  = ms'),
      resume_thread' ge m ctn ms'.
  Definition resume_thread ge: forall m {tid0 ms},
      containsThread_ _ ms tid0 -> machine_state -> Prop:=
    @resume_thread' ge.

  Inductive suspend_thread' ge: forall m {tid0} {ms:machine_state},
      containsThread_ _ ms tid0 -> machine_state -> Prop:=
  | SuspendThread: forall m tid0 ms ms' c X
                     (ctn: containsThread_ _ ms tid0)
                     (Hcode: getThreadC_ _ ctn = Krun c)
                     (Hat_external: at_external Sem ge c m = Some X)
                     (Hinv: invariant ms)
                     (Hms': updThreadC_ _ ctn (Kblocked c) = ms'),
      suspend_thread' ge m ctn ms'.
  Definition suspend_thread ge: forall (m: mem) {tid0 ms},
      containsThread_ _ ms tid0 -> machine_state -> Prop:=
    @suspend_thread' ge.

  Inductive machine_step {genv:G}:
    Sch -> event_trace -> machine_state -> mem -> Sch ->
    event_trace -> machine_state -> mem -> Prop :=
  | start_step:
      forall tid U ms ms' m m'
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread_ _ ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: start_thread genv m Htid ms' m'),
        machine_step U [::] ms m U [::] ms' m'
  | resume_step:
      forall tid U ms ms' m
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread_ _ ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: resume_thread genv m Htid ms'),
        machine_step U [::] ms m U [::] ms' m
  | thread_step:
      forall tid U ms ms' m m' ev
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread_ _  ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: threadStep genv Htid Hcmpt ms' m' ev),
        machine_step U [::] ms m U [::] ms' m'
  | suspend_step:
      forall tid U U' ms ms' m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread_ _  ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep:suspend_thread genv m Htid ms'),
        machine_step U [::] ms m U' [::] ms' m
  | sync_step:
      forall tid U U' ms ms' m m' ev
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread_ _  ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: syncStep true genv Htid Hcmpt ms' m' ev),
        machine_step U [::] ms m  U' [::] ms' m'
  | halted_step:
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread_ _  ms tid)
        (Hcmpt: mem_compatible ms m)
        (Hinv: invariant ms)
        (Hhalted: threadHalted Htid),
        machine_step U [::] ms m  U' [::] ms m
  | schedfail :
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (Htid: ~ containsThread_ _  ms tid)
        (Hinv: invariant ms)
        (HschedS: schedSkip U = U'),        (*Schedule Forward*)
        machine_step U [::] ms m U' [::] ms m.

  (*Lemma to deal with the trivial trace*)
  Lemma trace_nil: forall ge U tr st m U' tr' st' m',
      @machine_step ge U tr st m U' tr' st' m' ->
  tr = nil /\ tr' = nil.
  Proof. move=> ge U tr st m U' tr' st' m' ms; inversion ms; intuition. Qed.

  (*The new semantics bellow makes internal (thread) and external (machine) steps explicit*)
  Inductive internal_step {genv:G}:
    Sch -> machine_state -> mem -> machine_state -> mem -> Prop :=
  | thread_step':
      forall tid U ms ms' m m' ev
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread_ _  ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: threadStep genv Htid Hcmpt ms' m' ev),
        internal_step U ms m ms' m'.

  Inductive external_step  {genv:G}:
    Sch -> event_trace -> machine_state -> mem -> Sch ->
    event_trace -> machine_state -> mem -> Prop :=
  | start_state': forall tid U ms ms' m m'
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread_ _  ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: start_thread genv m Htid ms' m'),
        external_step U [::] ms m U [::] ms' m'
  | resume_step':
      forall tid U ms ms' m
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread_ _  ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: resume_thread genv m Htid ms'),
        external_step U [::] ms m U [::] ms' m
  | suspend_step':
      forall tid U U' ms ms' m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread_ _  ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep:suspend_thread genv m Htid ms'),
        external_step U [::] ms m U' [::] ms' m
  | sync_step':
      forall tid U U' ms ms' m m' ev
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread_ _  ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: syncStep true genv Htid Hcmpt ms' m' ev),
        external_step U [::] ms m  U' [::] ms' m'
  | halted_step':
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread_ _  ms tid)
        (Hcmpt: mem_compatible ms m)
        (Hinv: invariant ms)
        (Hhalted: threadHalted Htid),
        external_step U [::] ms m  U' [::] ms m
  | schedfail':
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (Htid: ~ containsThread_ _  ms tid)
        (Hinv: invariant ms)
        (HschedS: schedSkip U = U'),        (*Schedule Forward*)
        external_step U [::] ms m U' [::] ms m.
  (*Symmetry*)
  (* These steps are basically the same: *)
  Lemma step_equivalence1: forall ge U tr st m U' tr' st' m',
    @machine_step ge U tr st m U' tr' st' m' ->
    (U=U' /\ tr = tr' /\  @internal_step ge U st m st' m') \/
    @external_step ge U tr st m U' nil st' m'.
  Proof.
    move=> ge U tr st m U' tr' st' m' ms.
    inversion ms;
      first[ solve [ left; repeat split=>//; econstructor; eauto] |
             solve[right; econstructor; eauto]].
  Qed.
  Lemma step_equivalence2: forall ge U st m st' m',
      @internal_step ge U st m st' m' ->
      @machine_step ge U nil st m U nil st' m'.
  Proof. move=>  ge U st m st' m' istp.
         inversion istp; solve [econstructor; eauto].
  Qed.
   Lemma step_equivalence3: forall ge U tr st m U' tr' st' m',
      @external_step ge U tr st m U' tr' st' m' ->
      @machine_step ge U tr st m U' tr' st' m'.
   Proof. move=>  ge U tr st m U' nil st' m' estp.
          inversion estp;
          [
              solve[econstructor 1 ; eauto]|
              solve[econstructor 2 ; eauto]|
              solve[econstructor 4 ; eauto]|
              solve[econstructor 5 ; eauto]|
              solve[econstructor 6 ; eauto]|
              solve[econstructor 7 ; eauto]].
   Qed.

  Notation MachState:= (@MachState _ _ ThreadPool).

  Definition MachStep G (c:MachState) (m:mem)
             (c' :MachState) (m':mem) :=
    @machine_step G (fst (fst c)) (snd (fst c)) (snd c)  m
                  (fst (fst c')) (snd (fst c')) (snd c')  m'.

  Definition at_external (ge: G) (st : MachState) (m: mem)
    : option (external_function * list val) := None.

  Definition after_external (ge: G) (ov : option val) (st : MachState) :
    option (MachState) := None.

  (*not clear what the value of halted should be*)
  (*Nick: IMO, the machine should be halted when the schedule is empty.
            The value is probably unimportant? *)
  (*Santiago: I belive empty schedule should "diverge". After all that's *)
  Definition halted (st : MachState) : option val :=
    match schedPeek (fst (fst st)) with
    | Some _ => None
    | _ => Some Vundef
    end.

  (*Lemma halted_al_schedules: forall st,
      halted st ->*)


  Definition init_machine (U:schedule) (r : option res) the_ge (m: mem)
             (f : val) (args : list val)
    : option (MachState * option mem) :=
    match init_mach r the_ge m f args with
    | None => None
    | Some (c, om) => Some ((U, [::], c), om)
    end.

  Program Definition MachineCoreSemantics (U:schedule) (r : option res):
    CoreSemantics G MachState mem.
  intros.
  apply (@Build_CoreSemantics _ MachState _
                              (fun n => init_machine U r)
                              at_external
                              after_external
                              halted
                              MachStep
        );
    unfold at_external, halted; try reflexivity.
  intros. inversion H; subst; rewrite HschedN; reflexivity.
  auto.
  Defined.

  Definition init_machine' (r : option res) the_ge m
             (f : val) (args : list val)
    : option (machine_state * option mem) :=
    init_mach r the_ge m f args.

  (*This is not used anymore:
   * find_thread
   * running_thread *)
  Definition find_runnin (c:@ctl C): bool :=
    match c with
    | Krun _ => true
    | _ => false
    end.
  Definition running_thread: machine_state -> option nat:=
    fun st => find_thread_ _ st find_runnin.

    Definition unique_Krun tp i :=
     forall j cnti q,
       @getThreadC_ _ _ _ j tp cnti = Krun q ->
       ~ @threadHalted j tp cnti  ->
       eq_nat_dec i j.


  Program Definition new_MachineSemantics (U:schedule) (r : option res):
    @ConcurSemantics G nat schedule event_trace machine_state mem.
  apply (@Build_ConcurSemantics _ nat schedule event_trace  machine_state _
                              (init_machine' r)
                              (fun U st => halted (U, nil, st))
                              (fun ge U st m st' m' =>
                                 @internal_step ge U st m
                                                st' m'
                              )
                              (fun ge U (tr:event_trace) st m U' tr' st' m' =>
                                 @external_step ge U tr st m
                                                U' tr' st' m'
                              )
                              unique_Krun
                              (*fun A => running_thread A*))
         ;
    unfold at_external, halted; try reflexivity.
  - intros. inversion H; subst; rewrite HschedN; reflexivity.
  - intros. inversion H; subst; rewrite HschedN; reflexivity.
  Defined.

(*
  Definition MachineSemantics:= MachineSemantics'.*)
  Lemma hybrid_initial_schedule: forall genv m main vals U U' p c tr om n,
      initial_core (MachineCoreSemantics U p) n genv m main vals = Some ((U',tr,c),om) ->
      U' = U /\ tr = nil.
        simpl. unfold init_machine. intros.
        destruct (init_mach p genv m main vals) as [[? ?]|]; try solve[inversion H].
        inversion H; subst; split; auto.
  Qed.

  Lemma corestep_empty_trace: forall genv U tr tr' c m c' m' U',
      MachStep genv (U,tr,c) m (U', tr', c') m' ->
      tr = nil /\ tr' = nil.
  Proof.
    intros.
    inversion H; subst; simpl in *; auto.
  Qed.

  (** Schedule safety of the coarse-grained machine*)
  Inductive csafe (ge : G) (st : MachState) (m : mem) : nat -> Prop :=
  | Safe_0: csafe ge st m 0
  | HaltedSafe: forall n, halted st -> csafe ge st m n
  | CoreSafe : forall tp' m' n
                 (Hstep: MachStep ge st m (fst (fst st),[::],tp') m')
                 (Hsafe: csafe ge (fst (fst st),[::],tp') m' n),
      csafe ge st m (S n)
  | AngelSafe: forall tp' m' n
                 (Hstep: MachStep ge st m (schedSkip (fst (fst st)),[::],tp') m')
                 (Hsafe: forall U'', csafe ge (U'',[::],tp') m' n),
      csafe ge st m (S n).

End HybridCoarseMachine.

(*Module Events <: EventSig
   with Module TID:=NatTID.

 Module TID := NatTID.
 Import TID event_semantics.

 (** Synchronization Events.  The release/acquire cases include the
footprints of permissions moved  when applicable*)
 Definition evRes := (access_map * access_map)%type.
 Definition evDelta := (delta_map * delta_map)%type.

 Inductive sync_event : Type :=
 | release : address (*-> option (evRes * evDelta)*) -> option evRes -> sync_event
 | acquire : address -> option evDelta (*option (evRes * evDelta) -> option evRes*)  -> sync_event
 | mklock :  address -> sync_event
 | freelock : address -> sync_event
 | spawn : address -> option (evRes * evDelta) -> option evDelta -> sync_event
 | failacq: address -> sync_event.

 (** Machine Events *)
  Inductive machine_event : Type :=
  | internal: TID.tid -> mem_event -> machine_event
  | external : TID.tid -> sync_event -> machine_event.

  Definition thread_id ev : tid :=
    match ev with
    | internal i _ => i
    | external i _ => i
    end.

  Inductive act : Type :=
  | Read : act
  | Write : act
  | Alloc : act
  | Free : act
  | Release : act
  | Acquire : act
  | Mklock : act
  | Freelock : act
  | Failacq : act
  | Spawn : act.

  Definition is_internal ev :=
    match ev with
    | internal _ _ => true
    | _ => false
    end.

  Definition is_external ev :=
    match ev with
    | external _ _ => true
    | _ => false
    end.

  Definition action ev : act :=
    match ev with
    | internal _ mev =>
      match mev with
      | event_semantics.Write _ _ _ => Write
      | event_semantics.Read _ _ _ _ => Read
      | event_semantics.Alloc _ _ _ => Alloc
      | event_semantics.Free _ => Free
      end
    | external _ sev =>
      match sev with
      | release _ _ => Release
      | acquire _ _ => Acquire
      | mklock _ => Mklock
      | freelock _ => Freelock
      | failacq _ => Failacq
      | spawn _ _ _ => Spawn
      end
    end.

  Definition location ev : option (address*nat) :=
    match ev with
    | internal _ mev =>
      match mev with
      | event_semantics.Write b ofs vs => Some ((b, ofs), length vs)
      | event_semantics.Read b ofs _ vs => Some ((b, ofs), length vs)
      | _ => None
      end
    | external _ sev =>
      match sev with
      | release addr _ => Some (addr, lksize.LKSIZE_nat)
      | acquire addr _ => Some (addr, lksize.LKSIZE_nat)
      | mklock addr => Some (addr, lksize.LKSIZE_nat)
      | freelock addr => Some (addr, lksize.LKSIZE_nat)
      | spawn addr _ _ => Some (addr, lksize.LKSIZE_nat)
      | failacq addr => Some (addr, lksize.LKSIZE_nat)
      end
    end.

End Events.*)
