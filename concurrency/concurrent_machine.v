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
  (EF_external "makelock" (mksignature (AST.Tptr::nil) None cc_default)).
Notation FREE_LOCK :=
  (EF_external "freelock" (mksignature (AST.Tptr::nil) None cc_default)).

Notation LOCK_SIG := (mksignature (AST.Tptr::nil) None cc_default).
Notation LOCK := (EF_external "acquire" LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tptr::nil) None cc_default).
Notation UNLOCK := (EF_external "release" UNLOCK_SIG).

Module Type EventSig.
  Declare Module TID: ThreadID.
  Import TID.

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
  | internal: TID.tid -> mem_event -> machine_event
  | external : TID.tid -> sync_event -> machine_event.

End EventSig.


Module Type ConcurrentMachineSig.
  Declare Module ThreadPool: ThreadPoolSig.
  Declare Module Events: EventSig.
  Import ThreadPool.
  Import Events.
  Import SEM.

  Notation thread_pool := ThreadPool.t.
  (** Memories*)
  Parameter richMem: Type.
  Parameter dryMem: richMem -> mem.
  Parameter diluteMem : mem -> mem.

  (** Environment and Threadwise semantics *)
  (** These values come from SEM *)

  (** The thread pool respects the memory*)
  Parameter mem_compatible: thread_pool -> mem -> Prop.
  Parameter invariant: thread_pool -> Prop.

  (** Step relations *)
  Parameter threadStep:
    G -> forall {tid0 ms m},
      containsThread ms tid0 -> mem_compatible ms m ->
      thread_pool -> mem -> seq mem_event -> Prop.
  Axiom threadStep_equal_run:
    forall g i tp m cnt cmpt tp' m' tr,
      @threadStep g i tp m cnt cmpt tp' m' tr ->
      forall j,
        (exists cntj q, @getThreadC j tp cntj = Krun q) <->
        (exists cntj' q', @getThreadC j tp' cntj' = Krun q').
  Parameter syncStep:
    bool -> (* if it's a Coarse machine. Temp solution to propagating changes. *)
    G -> forall {tid0 ms m},
      containsThread ms tid0 -> mem_compatible ms m ->
      thread_pool -> mem -> sync_event -> Prop.

  Axiom syncstep_equal_run:
    forall b g i tp m cnt cmpt tp' m' tr,
      @syncStep b g i tp m cnt cmpt tp' m' tr ->
      forall j,
        (exists cntj q, @getThreadC j tp cntj = Krun q) <->
        (exists cntj' q', @getThreadC j tp' cntj' = Krun q').

  Axiom syncstep_not_running:
    forall b g i tp m cnt cmpt tp' m' tr,
      @syncStep b g i tp m cnt cmpt tp' m' tr ->
      forall cntj q, ~ @getThreadC i tp cntj = Krun q.

  Parameter threadHalted:
    forall {tid0 ms},
      containsThread ms tid0 -> Prop.

  Axiom threadHalt_update:
    forall i j, i <> j ->
      forall tp cnt cnti c' cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j (@updThreadC i tp cnti c') cnt') .

  Axiom syncstep_equal_halted:
    forall b g i tp m cnti cmpt tp' m' tr,
      @syncStep b g i tp m cnti cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j tp' cnt').

  Axiom threadStep_not_unhalts:
    forall g i tp m cnt cmpt tp' m' tr,
      @threadStep g i tp m cnt cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) ->
        (@threadHalted j tp' cnt') .


  (*Parameter initial_machine: C -> thread_pool.*)

  Parameter init_mach : option RES.res  -> G -> mem -> val -> list val -> option (thread_pool * option mem).

End ConcurrentMachineSig.


Module Type ConcurrentMachine.
  Declare Module SCH: Scheduler.
  Declare Module TP: ThreadPoolSig.
  Declare Module SIG: ConcurrentMachineSig with Module ThreadPool:= TP.

  Import SCH.
  Import TP.
  Import SIG.Events.

  Notation event_trace := (seq machine_event).

  Definition MachState : Type:= (schedule * event_trace * t)%type.

  Parameter MachineSemantics: schedule -> option RES.res ->
                              CoreSemantics SIG.ThreadPool.SEM.G MachState mem.

  Axiom initial_schedule: forall genv m main vals U U' p c tr m' n,
      initial_core (MachineSemantics U p) n genv m main vals = Some ((U',tr,c), m') ->
      U' = U /\ tr = nil.
End ConcurrentMachine.

Module CoarseMachine (SCH:Scheduler)(SIG : ConcurrentMachineSig with Module ThreadPool.TID:=SCH.TID with Module Events.TID :=SCH.TID) <: ConcurrentMachine with Module SCH:= SCH with Module TP:= SIG.ThreadPool  with Module SIG:= SIG.
  Module SCH:=SCH.
  Module TP:=SIG.ThreadPool.
  Module SIG:=SIG.
  Import SCH SIG TID ThreadPool ThreadPool.SEM Events.

  Notation Sch:=schedule.
  Notation machine_state := ThreadPool.t.

  Notation event_trace := (seq machine_event).

  (** Resume and Suspend: threads running must be preceded by a Resume
     and followed by Suspend.  This functions wrap the state to
     indicate it's ready to take a syncronisation step or resume
     running. (This keeps the invariant that at most one thread is not
     at_external) *)

  Inductive start_thread' genv: forall  (m: mem) {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> mem -> Prop:=
  | StartThread: forall m tid0 ms ms' c_new om vf arg
                    (ctn: containsThread ms tid0)
                    (Hcode: getThreadC ctn = Kinit vf arg)
                    (Hinitial: initial_core Sem (tid2nat tid0)
                                            genv m vf (arg::nil) = Some (c_new, om))
                    (Hinv: invariant ms)
                    (Hms': updThreadC ctn (Krun c_new)  = ms'),
      start_thread' genv m ctn ms' (option_proj m om).
  Definition start_thread genv: forall (m: mem) {tid0 ms},
      containsThread ms tid0 -> machine_state -> mem -> Prop:=
    @start_thread' genv.
  Inductive resume_thread' ge: forall (m: mem) {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | ResumeThread: forall m tid0 ms ms' c c' X
                    (ctn: containsThread ms tid0)
                    (Hat_external: at_external Sem ge c m = Some X)
                    (Hafter_external: after_external Sem ge None c = Some c')
                    (Hcode: getThreadC ctn = Kresume c Vundef)
                    (Hinv: invariant ms)
                    (Hms': updThreadC ctn (Krun c')  = ms'),
      resume_thread' ge m ctn ms'.
  Definition resume_thread genv: forall m {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @resume_thread' genv.

  Inductive suspend_thread' ge: forall (m: mem) {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | SuspendThread: forall m tid0 ms ms' c X
                     (ctn: containsThread ms tid0)
                     (Hcode: getThreadC ctn = Krun c)
                     (Hat_external: at_external Sem ge c m = Some X)
                     (Hinv: invariant ms)
                     (Hms': updThreadC ctn (Kblocked c) = ms'),
      suspend_thread' ge m ctn ms'.
  Definition suspend_thread ge: forall m {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @suspend_thread' ge.

  Inductive machine_step {genv:G}:
    Sch -> event_trace -> machine_state -> mem -> Sch ->
    event_trace -> machine_state -> mem -> Prop :=
  | start_step:
      forall tid U ms ms' m m'
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: start_thread genv m Htid ms' m'),
        machine_step U [::] ms m U [::] ms' m'
  | resume_step:
      forall tid U ms ms' m
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: resume_thread genv m Htid ms'),
        machine_step U [::] ms m U [::] ms' m
  | thread_step:
      forall tid U ms ms' m m' ev
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: threadStep genv Htid Hcmpt ms' m' ev),
        machine_step U [::] ms m U [::] ms' m'
  | suspend_step:
      forall tid U U' ms ms' m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep:suspend_thread genv m Htid ms'),
        machine_step U [::] ms m U' [::] ms' m
  | sync_step:
      forall tid U U' ms ms' m m' ev
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: syncStep true genv Htid Hcmpt ms' m' ev),
        machine_step U [::] ms m  U' [::] ms' m'
  | halted_step:
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Hinv: invariant ms)
        (Hhalted: threadHalted Htid),
        machine_step U [::] ms m  U' [::] ms m
  | schedfail :
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (Htid: ~ containsThread ms tid)
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
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: threadStep genv Htid Hcmpt ms' m' ev),
        internal_step U ms m ms' m'.

  Inductive external_step  {genv:G}:
    Sch -> event_trace -> machine_state -> mem -> Sch ->
    event_trace -> machine_state -> mem -> Prop :=
  | start_state': forall tid U ms ms' m m'
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: start_thread genv m Htid ms' m'),
        external_step U [::] ms m U [::] ms' m'
  | resume_step':
      forall tid U ms ms' m
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: resume_thread genv m Htid ms'),
        external_step U [::] ms m U [::] ms' m
  | suspend_step':
      forall tid U U' ms ms' m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep:suspend_thread genv m Htid ms'),
        external_step U [::] ms m U' [::] ms' m
  | sync_step':
      forall tid U U' ms ms' m m' ev
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: syncStep true genv Htid Hcmpt ms' m' ev),
        external_step U [::] ms m  U' [::] ms' m'
  | halted_step':
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Hinv: invariant ms)
        (Hhalted: threadHalted Htid),
        external_step U [::] ms m  U' [::] ms m
  | schedfail':
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (Htid: ~ containsThread ms tid)
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
        inversion istp; try solve [econstructor; eauto].
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

  Definition MachState: Type := (Sch * event_trace * machine_state)%type.

  Definition MachStep ge (c:MachState) (m:mem)
             (c' :MachState) (m':mem) :=
    @machine_step ge (fst (fst c)) (snd (fst c)) (snd c)  m
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


  Definition init_machine (U:schedule) (r : option RES.res) the_ge
             (m: mem) (f : val) (args : list val)
    : option (MachState * option mem) :=
    match init_mach r the_ge m f args with
    | None => None
    | Some (c,m') => Some ((U, [::], c), m')
    end.

  Program Definition MachineSemantics (U:schedule) (r : option RES.res):
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

  Definition init_machine' (r : option RES.res) the_ge (m: mem)
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
  Definition running_thread: machine_state -> option tid:=
    fun st => find_thread st find_runnin.

    Definition unique_Krun tp i :=
     forall j cnti q,
       @getThreadC j tp cnti = Krun q ->
       ~ @threadHalted j tp cnti  ->
       eq_tid_dec i j.


  Program Definition new_MachineSemantics (U:schedule) (r : option RES.res):
    @ConcurSemantics G tid schedule event_trace machine_state mem.
  apply (@Build_ConcurSemantics _ tid schedule event_trace  machine_state _
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
  Lemma initial_schedule: forall genv m main vals U U' p c tr m' n,
      initial_core (MachineSemantics U p) n genv m main vals = Some ((U',tr,c),m') ->
      U' = U /\ tr = nil.
        simpl. unfold init_machine. intros.
        destruct (init_mach p genv m main vals) as [[? ?] |]; try solve[inversion H].
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
  Lemma csafe_monotone:
    forall n ge U tr tp m,
    csafe ge (U, tr, tp) m (S n) ->
    csafe ge (U, tr, tp) m (n) .
  Proof.
    induction n; [econstructor|].
    intros.
    inversion H; simpl in *; subst.
    - econstructor 2; auto.
    - econstructor 3; eauto.
    - econstructor 4; eauto.
  Qed.
  
  Lemma csafe_first_tid:
            forall n ge U U' tp m,
              csafe ge (U, nil, tp) m n ->
              schedPeek U = schedPeek U' -> 
              csafe ge (U', nil, tp) m n.
          Proof.
            induction n; subst.
            - constructor 1.
            - intros. inversion H; subst. 
              + econstructor 2; eauto.
                unfold halted in *; simpl in *.
                destruct (schedPeek U); try solve [inversion H1].
                rewrite <- H0; eauto.
              + econstructor 3; eauto; simpl in *.
                inversion Hstep; simpl in *; subst;
                 try  match goal with
                      | [ H: schedPeek ?U = Some _, H0: schedSkip U = U |- _ ] =>
                        symmetry in H0;
                          apply SCH.end_of_sch in H0;
                          rewrite HschedN in HschedS; inversion HschedS
                 end.
                * econstructor 1; simpl; eauto.
                  rewrite <- H0; eauto.
                * econstructor 2; simpl; eauto.
                  rewrite <- H0; eauto.
                * econstructor 3; simpl; eauto.
                  rewrite <- H0; eauto.
              + econstructor 4; eauto; simpl in *.
                inversion Hstep; simpl in *; subst;
                  try match goal with
                      | [ H: schedPeek ?U = Some _, H0: U  = schedSkip U |- _ ] =>
                        rewrite <- H0 in H;
                        apply SCH.end_of_sch in H0;
                          rewrite H in H0; inversion H0
                      end.
                * econstructor 4; subst; simpl in *; subst; eauto.
                  rewrite <- H0; eauto. 
                * econstructor 5; subst; simpl in *; subst; eauto.
                  rewrite <- H0; eauto. 
                * econstructor 6; subst; simpl in *; subst; eauto.
                  rewrite <- H0; eauto. 
                * econstructor 7; subst; simpl in *; subst; eauto.
                  rewrite <- H0; eauto. 
          Qed.

  Section new_safety.
  (** *I create a new type of safety that satisfies (forall n, safeN) -> safe and is preserved by simulations. *)

    Inductive sem_with_halt ge: MachState -> mem -> MachState -> mem -> Prop:=
    | halt_with_step st m: halted st -> sem_with_halt ge st m st m
    | step_with_halt st m st' m' : MachStep ge st m st' m' -> sem_with_halt ge st m st' m'.

  Definition new_state: Type:= seq machine_event * machine_state * mem.
  Definition mk_nstate (st:MachState) m:new_state:= (snd (fst st), snd st, m).
  Definition mk_ostate (st:new_state) U :MachState:= (U, fst (fst st), snd (fst st)).
  Definition new_step ge (st: new_state) U st' U': Prop:=
    sem_with_halt ge (mk_ostate st U) (snd st) (mk_ostate st' U') (snd st').

  (*Definition valid (st: MachState): Prop:=
    match (running_thread (snd st)), (schedPeek (fst (fst st))) with
    | _, None => True
    | None, _ => True
    | Some a, Some b => eq_tid_dec a b (* || containsThread_dec b (snd st) *)
    end.*)

  Section valid_schedule.

    Definition is_running tp i:=
      exists cnti q, @getThreadC i tp cnti = Krun q /\ ~ @threadHalted i tp cnti.

    Lemma unique_runing_not_running:
      forall tp i,
        unique_Krun tp i ->
        is_running tp i \/
        forall j, unique_Krun tp j.
    Proof.
      unfold unique_Krun, is_running.
      intros.
      destruct (Classical_Prop.classic
                  (exists (cnti : containsThread tp i) (q : C),
                      getThreadC cnti = Krun q /\ ~ threadHalted cnti))
        as [[cnti [q [KRUN Not_HALTED]]] | NO]; [left|right].
      + exists cnti, q; auto.
      + intros j j0 cnti q KRUN NOT_HALTED.
        specialize (H _ _ _ KRUN NOT_HALTED).
        destruct (eq_tid_dec i j0); try solve[inversion H].
        subst i.
        exfalso; apply NO.
        exists cnti, q; split; assumption.
    Qed.

    Corollary unique_runing_not_running':
      forall tp i,
        unique_Krun tp i ->
        ~ is_running tp i ->
        forall j, unique_Krun tp j.
    Proof.
      intros. destruct (unique_runing_not_running _ _ H).
      - contradict H0; assumption.
      - apply H1.
    Qed.

  Lemma no_running_one_running:
    forall tp,
      (forall j, unique_Krun tp j) ->
      forall i cnti c, unique_Krun (@updThreadC i tp cnti (Krun c)) i.
  Proof.
    unfold unique_Krun.
    intros.
    destruct (eq_tid_dec i j); auto; exfalso; eapply n.
    erewrite <- (gsoThreadCC _ (cntUpdateC' cnti0)) in H0; auto.
    eapply H with (j:=i) in H0.
    destruct (eq_tid_dec i j); inversion H0; assumption.
    intros HH; apply H1.
    eapply threadHalt_update in HH; eauto.
    Grab Existential Variables.
    assumption.
  Qed.
  Lemma one_running_no_running:
    forall tp i,
      (unique_Krun tp i) ->
      forall j cnti c, unique_Krun (@updThreadC i tp cnti (Kblocked c)) j.
  Proof.
    unfold unique_Krun.
    intros.
    destruct (eq_tid_dec i j0).
    - subst i.
      rewrite (gssThreadCC cnti0) in H0; inversion H0.
    - rewrite <- (gsoThreadCC n (cntUpdateC' cnti0)) in H0.
      eapply H with (j:=j0) in H0.
      exfalso; apply n;
      destruct (eq_tid_dec i j0); auto; inversion H0.
      intros HH; apply H1.
      eapply threadHalt_update in HH; eauto.
  Qed.

  Lemma no_running_no_running:
    forall tp,
      (forall h, unique_Krun tp h ) ->
      forall i j cnti c, unique_Krun (@updThreadC i tp cnti (Kblocked c)) j.
  Proof.
    unfold unique_Krun.
    intros.
    destruct (eq_tid_dec i j0).
    - subst i.
      rewrite (gssThreadCC cnti0) in H0; inversion H0.
    - rewrite <- (gsoThreadCC n (cntUpdateC' cnti0)) in H0.
      eapply H with (j:=j0) in H0.
      eassumption.
      intros HH; apply H1.
      eapply threadHalt_update in HH; eauto.
  Qed.

  End valid_schedule.

  Definition correct_schedule(st: MachState): Prop:=
    match schedPeek (fst (fst st)) with
    | Some i => unique_Krun (snd st) i
    | None => True
    end.

  Definition valid (st: MachState): Prop:=
    correct_schedule st.

  Definition bounded_mem (m: mem) := bounded_maps.bounded_map (snd (getMaxPerm m)) .

  Definition new_valid st U := correct_schedule (mk_ostate st U).
  Definition new_valid_bound st U :=
    correct_schedule (mk_ostate st U) /\ bounded_mem (snd st).
  Definition ksafe_new_step (ge : G) (st : MachState) (m : mem) : nat -> Prop :=
    ksafe _ _ (new_step ge) new_valid (mk_nstate st m) (fst (fst st)).
  Definition safe_new_step (ge : G) (st : MachState) (m : mem) : Prop :=
    safe _ _ (new_step ge) new_valid (mk_nstate st m) (fst (fst st)).
  Definition safe_new_step_bound (ge : G) (st : MachState) (m : mem) : Prop :=
    safe _ _ (new_step ge) new_valid_bound (mk_nstate st m) (fst (fst st)).

  (*Things that we must prove:*)
  Lemma sch_dec': forall (U U': Sch), {U = U'} + {U <> U'}.
  Proof. apply SCH.sch_dec. Qed.
  Lemma step_sch: forall {ge U tr tp m U' tr' tp' m'}, MachStep ge (U, tr, tp) m (U', tr', tp') m' -> U=U' \/ schedSkip(U)=U'.
  Proof.
    intros.
    inversion H;
      simpl in *;
      subst; first[left; reflexivity | right; reflexivity | idtac].
  Qed.
  Lemma step_trace: forall {ge U tr tp m U' tr' tp' m'}, MachStep ge (U, tr, tp) m (U', tr', tp') m' -> nil = tr'.
  Proof.
    intros.
    inversion H;
      simpl in *; auto.
  Qed.
  (*Most cases in this proof are similar. Should automate!*)
  Lemma step_sch_correct: forall {ge st m st' m'}, MachStep ge st m st' m'  -> correct_schedule st -> correct_schedule st'.
  Proof.
    unfold correct_schedule in *.
    intros.
    destruct st as [[a b] c]; destruct st' as [[a' b' ] c'].
    inversion H; subst; simpl in *.
    - inversion Htstep; subst.
      rewrite HschedN in H0; rewrite HschedN.
      eapply no_running_one_running.
      destruct (unique_runing_not_running _ _ H0) as [HH | HH]; auto.
      destruct HH as [cnt' [c' [KRUN NOT_HALTED]]].
      pose (@gLockSetCode tid0 c).
      replace cnt' with ctn in KRUN.
      + rewrite Hcode in KRUN; inversion KRUN.
      + eapply msl.Axioms.proof_irr.
    - inversion Htstep; subst.
      rewrite HschedN in H0; rewrite HschedN.
      eapply no_running_one_running.
      destruct (unique_runing_not_running _ _ H0) as [HH | HH]; auto.
      destruct HH as [cnt' [c' [KRUN NOT_HALTED]]].
      pose (@gLockSetCode tid0 c).
      replace cnt' with ctn in KRUN.
      + rewrite Hcode in KRUN; inversion KRUN.
      + eapply msl.Axioms.proof_irr.
    - subst.
      destruct (schedPeek a'); auto.
      intros j cntj q j_runs j_not_halted.
      inversion HschedN; subst tid0.
      assert (Htstep':=Htstep).
      apply threadStep_equal_run with (j:=j) in Htstep.
      assert (HH: exists (cntj : containsThread c' j) (q : C),
              getThreadC cntj = Krun q).
      { exists cntj, q; auto. }
      apply Htstep in HH; destruct HH as [cnt [q0 j_runs0]].
      eapply H0; eauto.
      intros HH; apply j_not_halted;
      eapply threadStep_not_unhalts; eauto.
    - destruct (schedPeek a') eqn:SCH'; auto.
      rewrite HschedN in H0.
      inversion Htstep; subst.
      eapply one_running_no_running in H0.
      destruct (unique_runing_not_running _ _ H0) as [HH | HH]; auto.
      destruct HH as [cnt' [c' [KRUN NOT_HALTED]]].
      erewrite gssThreadCC in KRUN. inversion KRUN.
    - subst.
      rewrite HschedN in H0.
      destruct (schedPeek (schedSkip a)) eqn:AAA; auto.
      unfold unique_Krun in H0.
      intros j cntj q j_runs j_not_halted.

      assert (Htstep':=Htstep).
      eapply syncstep_equal_run in Htstep'.
      assert (HH: exists (cntj : containsThread c' j) (q : C),
                 getThreadC cntj = Krun q).
      { exists cntj, q; auto. }
      apply Htstep' in HH; destruct HH as [cnt [q0 j_runs0]].

      destruct (eq_tid_dec tid0 j); subst.
      + exfalso; eapply
                 (syncstep_not_running _ _ _ _ _ _ _ _ _ _ Htstep).
        eapply j_runs0.
      + destruct (Classical_Prop.classic (threadHalted cnt)) as [halt | n_halt].
        * exfalso; apply j_not_halted.
          eapply (syncstep_equal_halted ) in Htstep; eauto.
          eapply Htstep; eassumption.
        * eapply H0 in j_runs0; eauto.
          exfalso; apply n; destruct (eq_tid_dec tid0 j); auto; inversion j_runs0.
    - destruct (schedPeek a') eqn:SCH'; auto.
      rewrite HschedN in H0.
      subst c'.
      destruct (unique_runing_not_running _ _ H0) as [HH | HH]; auto.
      intros j cnti q KRUN NOT_HALT.
      assert (HHH:= NOT_HALT).
      contradict HHH.
      specialize (H0 _ _ _ KRUN NOT_HALT).
      destruct (eq_tid_dec tid0 j); try solve[inversion H0].
      subst tid0.
      replace cnti with Htid; auto.
      eapply msl.Axioms.proof_irr.
    - destruct (schedPeek a') eqn:SCH'; auto.
      rewrite HschedN in H0.
      subst c'.
      intros j cnti q KRUN NOT_HALT.
      assert (HHH:= NOT_HALT).
      contradict HHH.
      specialize (H0 _ _ _ KRUN NOT_HALT).
      destruct (eq_tid_dec tid0 j); try solve[inversion H0].
      subst tid0.
      contradict Htid; assumption.
  Qed.

  Lemma step_valid: forall {ge st m st' m'},
      MachStep ge st m st' m'  ->
      valid st ->
      valid st'.
  Proof. intros ? ? ? ? ?; eapply step_sch_correct. Qed.

  Lemma step_new_valid: forall {ge st m st' m'},
      MachStep ge st m st' m'  ->
      new_valid (mk_nstate st m) (fst (fst st)) ->
      new_valid (mk_nstate st' m') (fst (fst st')).
  Proof. intros ? ? ? ? ? STEP VAL.
         eapply step_sch_correct; eauto.
  Qed.


  Lemma step_correct_schedule: forall {ge U tr tp m tr' tp' m'},
      MachStep ge (U, tr, tp) m (schedSkip U, tr', tp') m' ->
      correct_schedule (U, tr, tp) ->
      forall U'', correct_schedule (U'', tr', tp').
  Proof.
    unfold correct_schedule in *.
    intros ? ? ? ? ? ? ? ? ?.

    inversion H; subst; simpl in *;
    match goal with
    | [ H: schedPeek (schedSkip ?U) = Some _, H': U = schedSkip U  |- _ ] =>
      solve[rewrite <- H' in H; apply end_of_sch in H'; rewrite H' in H; inversion H]
    | _ => idtac
    end.
    - rewrite HschedN; intros.
      destruct (schedPeek U''); auto.
      inversion Htstep; subst.
      intros j cnti q KRUN NOT_HALT.
      unfold unique_Krun in H0.
      destruct (eq_tid_dec tid0 j).
      + subst tid0. rewrite gssThreadCC in KRUN; inversion KRUN.
      + erewrite <- (gsoThreadCC n (cntUpdateC' cnti))  in KRUN; eauto.
        eapply H0 in KRUN.
        destruct (eq_tid_dec tid0 j) as [e|e].
        * rewrite e in n; exfalso; apply n; auto.
        * inversion KRUN.
          intros HALT; eapply NOT_HALT.
          Set Printing Implicit.
          eapply threadHalt_update in HALT; eauto.
    - rewrite HschedN.
      intros. destruct (schedPeek U'') eqn:UUU; trivial.
      intros j cnti q KRUN NOT_HALT.
      assert (HH: exists (cntj : containsThread tp' j) (q : C),
                   getThreadC cntj = Krun q).
        { exists cnti, q; assumption. }
        eapply syncstep_equal_run in HH; eauto.
        destruct HH as [cntj [q0 KRUN']].

        assert (HH:=KRUN').
        eapply H0 in HH.

        assert (HH': ~ @threadHalted j tp cntj).
        { intros HH'. apply NOT_HALT.
          eapply syncstep_equal_halted in Htstep; eauto.
          eapply Htstep.
          exact HH'. }
        apply HH in HH'.

        destruct (eq_tid_dec tid0 j); try solve[ inversion HH'].
        subst.
        eapply syncstep_not_running in Htstep.
        exfalso; apply Htstep.
        eassumption.
    - rewrite HschedN. intros UNIQUE U''.
      destruct (schedPeek U'') eqn:UUU; trivial.
      intros j cnti q KRUN NOT_HALT.
      specialize (UNIQUE _ _ _ KRUN NOT_HALT).
      destruct (eq_tid_dec tid0 j); try solve[inversion UNIQUE]; subst tid0.
      exfalso; apply NOT_HALT.
      replace cnti with Htid by eapply msl.Axioms.proof_irr; auto.
    - rewrite HschedN. intros UNIQUE U''.
      destruct (schedPeek U'') eqn:UUU; trivial.
      intros j cnti q KRUN NOT_HALT.
      specialize (UNIQUE _ _ _ KRUN NOT_HALT).
      destruct (eq_tid_dec tid0 j); try solve[inversion UNIQUE]; subst tid0.
      exfalso; apply Htid.
      eassumption.
  Qed.

  Lemma step_sch_valid: forall {ge U tr tp m tr' tp' m'}, MachStep ge (U, tr, tp) m (schedSkip U, tr', tp') m' -> valid (U, tr, tp) -> forall U'', valid (U'', tr', tp').
  Proof. intros; eapply step_correct_schedule; eauto. Qed.

  Lemma step_sch_new_valid:
    forall {ge U tr tp m tr' tp' m'},
      MachStep ge (U, tr, tp) m (schedSkip U, tr', tp') m' ->
      new_valid (tr, tp, m) U ->
      forall U'', new_valid (tr', tp', m') U''.
  Proof. intros ? ? ? ? ? ? ? ? STEP VAL.
         eapply step_correct_schedule; eauto.

  Qed.


  Lemma safety_equivalence':
    forall ge st_ m,
      (forall U n, new_valid (nil, st_, m) U -> ksafe_new_step ge (U, nil, st_) m n) ->
      (forall U n, new_valid (nil, st_, m) U ->  csafe ge (U, nil, st_) m n).
  Proof.
    move=> ge st_ m KSF' U n VAL.
    assert (KSF: forall U, new_valid (nil, st_, m) U -> ksafe_new_step ge (U, nil, st_) m n) by (move=> U'' NV; apply: KSF'=>// ).
    clear KSF'.
    (* assert (VAL_: new_valid (nil, st_, m) U).
    { rewrite /new_valid /mk_ostate /=.
      split; auto. *)
    (*  by rewrite /new_valid /mk_ostate /= //. clear VAL.*)

    (*move: VAL_=> /(KSF _ n) KSF_new.*)
    move: st_ m KSF U VAL.
    induction n.
    - constructor.
    - move => st_ m KSF U nVAL.
      move: (nVAL) => /KSF => KSF_new.
      inversion KSF_new; subst.
      move: H0; rewrite /new_step /mk_nstate /= => STEP_halt.
      inversion STEP_halt.
      + subst; move: H6; rewrite /mk_ostate=> H6; apply: HaltedSafe=>//.
      + subst; move: H; rewrite /mk_ostate /= => H.
          assert (HH:=step_trace H); rewrite -HH in H.
        destruct (step_sch H).
        * subst U'; apply: (CoreSafe _ _ _ (snd (fst st')) (snd st')) =>/= //.
          { apply: IHn => //.
            - move => U'' nVAL'; rewrite /ksafe_new_step /mk_nstate => /=.
              destruct st' as [p m0]; destruct p=> /=. simpl in HH; rewrite -HH in H1.
              apply: H1=> //.
            - rewrite /new_valid /mk_ostate=> /=.
              apply: (step_new_valid H) =>//.
          }
        * subst U'. apply: (AngelSafe _ _ _ (snd (fst st')) (snd st'))=>//.
          move=>U''.
          { destruct st' as [[tr' tp'] m'] => /=; eapply IHn.
            - move => U0 nVAL0. rewrite /ksafe_new_step /mk_nstate=> /=.
              simpl in HH; rewrite -HH in H1.
              by apply: H1.
            - simpl in H.
              eapply (step_sch_new_valid H); eauto.
          }
  Qed.

  Lemma safety_equivalence:
    forall ge tp m,
      (forall U, new_valid (nil, tp, m) U) ->
      (forall n U, ksafe_new_step ge (U, nil, tp) m n) ->
      (forall n U, csafe ge (U, nil, tp) m n).
  Proof. by move => ? ? ? H ? ? ?; apply: safety_equivalence'; try apply: H. Qed.

  (** *I further create a different type of safety that discriminates non-determinism*)

  Definition explicit_safety ge (U:Sch) (st:machine_state) (m:mem): Prop:=
    exp_safety _ _ (fun U stm => halted (U, nil, fst stm))
                   (fun U stm stm' => @internal_step ge U (fst stm) (snd stm) (fst stm') (snd stm'))
                   (fun U stm U' stm' => @external_step ge U nil (fst stm) (snd stm) U' nil (fst stm') (snd stm'))
                   (fun U stm => @new_valid (nil,fst stm, snd stm) U) U (st,m).

  Definition explicit_safety_bounded ge (U:Sch) (st:machine_state) (m:mem): Prop:=
    exp_safety _ _ (fun U stm => halted (U, nil, fst stm))
                   (fun U stm stm' => @internal_step ge U (fst stm) (snd stm) (fst stm') (snd stm'))
                   (fun U stm U' stm' => @external_step ge U nil (fst stm) (snd stm) U' nil (fst stm') (snd stm'))
                   (fun U stm => @new_valid_bound (nil,fst stm, snd stm) U) U (st,m).

  (*CoInductive explicit_safety ge (U:Sch) (st:machine_state) (m:mem): Prop:=
  | halted_safety : halted (U, nil, st) -> explicit_safety ge U st m
  | internal_safety st' m': @internal_step ge U st m st' m' ->
                            (forall U', new_valid (nil, st', m') U' -> explicit_safety ge U' st' m') ->
                            explicit_safety ge U st m
  | external_safety U' st' m': @external_step ge U nil st m U' nil st' m' ->
                            (forall U', new_valid (nil, st', m') U' -> explicit_safety ge U' st' m') ->
                            explicit_safety ge U st m.*)

  (*BUT, this is basically the same safety!!! *)
  Lemma safety_equivalence21: forall ge st m,
      (forall U, new_valid (nil, st, m) U ->
             safe_new_step ge (U, nil, st) m) ->
      forall U, new_valid (nil, st, m) U ->
            explicit_safety ge U st m.
  Proof.
    move => ge.
    cofix.
    move =>  st m sns_all U /sns_all sns.
    inversion sns.
    move: H; rewrite /mk_nstate /= => stp.
    inversion stp; subst.
    - move: H6; rewrite /mk_ostate /= => hltd.
      eapply (halted_safety); simpl; assumption.
    - destruct st' as [[tr tp] m'].
      move: H H0; rewrite /mk_ostate /MachStep /= => HH.
      move: HH (HH)  => /trace_nil [] ? -> /step_equivalence1 [[] -> [] ? istp | estp] sns_all'.
      + eapply (internal_safety).
        instantiate (1:=(tp,m')); simpl. exact istp.
        eapply safety_equivalence21 => //.
      + eapply (external_safety).
        instantiate (1:=(tp,m')); simpl. exact estp.
        eapply safety_equivalence21 => //.
  Qed.

  Lemma safety_equivalence22: forall ge st m,
      (forall U, new_valid (nil, st, m) U ->
            explicit_safety ge U st m) ->
      (forall U, new_valid (nil, st, m) U ->
             safe_new_step ge (U, nil, st) m).
  Proof.
    move => ge.
    cofix.
    move =>  st m es_all U /es_all es.
    inversion es.
    - econstructor.
      + econstructor. rewrite /mk_nstate /mk_ostate /= //.
      + rewrite /mk_nstate /= => U'' VAL.
        apply: safety_equivalence22 => //.
    - econstructor.
      + econstructor 2.
        instantiate(1:=(@nil machine_event, fst y', snd y')).
        rewrite /mk_nstate /mk_ostate /MachStep /=.
        move: H => / step_equivalence2.
        instantiate(1:=U).
        simpl => //.
      + rewrite /mk_nstate /= => U'' VAL.
        destruct y';
        apply: safety_equivalence22 => //.
    - econstructor.
      + econstructor 2.
        instantiate(1:=(@nil machine_event, fst y' ,  snd y')).
        rewrite /mk_nstate /mk_ostate /MachStep /=.
        move: H => / step_equivalence3.
        instantiate(1:=x').
        simpl => //.
      + rewrite /mk_nstate /= => U'' VAL.
        destruct y';
        apply: safety_equivalence22 => //.
  Qed.
  Lemma safety_equivalence2: forall ge st m,
      (forall U, new_valid (nil, st, m) U ->
             safe_new_step ge (U, nil, st) m) <->
      (forall U, new_valid (nil, st, m) U ->
            explicit_safety ge U st m).
  Proof.
    move => ge st m; split;
           [apply: safety_equivalence21 | apply: safety_equivalence22].
  Qed.

  (** * AND another safety: explicift safety with stutter *)
  Section newer_semantics_with_stutter.
    Context {core_data: Type}
            {core_ord : core_data -> core_data -> Prop}
            (core_ord_wf : well_founded core_ord).


    Definition stutter_stepN_safety ge cd (U:Sch) (st:machine_state) (m:mem): Prop:=
    @exp_safetyN_stutter _ _ (fun U stm => halted (U, nil, fst stm))
                   (fun U stm stm' => @internal_step ge U (fst stm) (snd stm) (fst stm') (snd stm'))
                   (fun U stm U' stm' => @external_step ge U nil (fst stm) (snd stm) U' nil (fst stm') (snd stm'))
                   (fun U stm => @new_valid (nil,fst stm, snd stm) U)
                   core_data core_ord
                   cd U (st,m).

    Variable default: core_data.

    (*This lemma is not needed but it's cool
      How come the standard library doesn't have it!? *)
    Lemma weak_well_founded_induction:
      forall (A : Type) (R : A -> A -> Prop),
      (forall P, P \/ ~P) ->
        well_founded R ->
        forall P : A -> Prop,
          (forall x: A, ~ (exists y:A, R y x) -> P x) ->
          (forall x : A, (exists y : A, R y x /\ P y) -> P x) ->
          forall a : A, P a.
    Proof.
      move => A R EM WF P base ind a.
      specialize (WF a).
      induction WF.
      generalize (EM (exists y: A, R y x)) ; move => [[]y Ryx | is_base ].
      - by apply: ind; exists y; split; auto.
      - by apply: base.
    Qed.

    End newer_semantics_with_stutter.


  End new_safety.

  Lemma csafe_reduce:
    forall ge sched tp mem n m,
      csafe ge (sched, [::], tp) mem n ->
      m <= n ->
      csafe ge (sched, [::], tp) mem m.
  Proof.
    intros. generalize n mem tp sched H0 H.
    induction m.
    intros. constructor.
    intros.
    assert (exists n', n0 = S n').
    { clear - H1. induction H1. exists m; auto.
      destruct IHle. exists (S x); auto. }
    destruct H3 as [n' H3].
    subst.
    inversion H2.
    + constructor 2; auto.
    + econstructor 3; eauto.
      simpl. subst. eapply IHm.
      omega. simpl in Hsafe. instantiate (1:=n').
      Focus 2. simpl in Hsafe. eauto.
      omega.
    + econstructor 4; eauto.
      simpl. subst. intros. eapply IHm.
      omega. simpl in Hsafe. instantiate (1:=n').
      Focus 2. simpl in Hsafe. eauto.
      omega.
  Qed.

End CoarseMachine.

Module FineMachine (SCH:Scheduler)(SIG : ConcurrentMachineSig with Module ThreadPool.TID:=SCH.TID with Module Events.TID:=SCH.TID)<: ConcurrentMachine with Module SCH:= SCH with Module TP:= SIG.ThreadPool with Module SIG:= SIG.
  Module SCH:=SCH.
  Module TP:=SIG.ThreadPool.
  Module SIG:=SIG.
  Import SCH SIG TID ThreadPool ThreadPool.SEM Events.

  Notation Sch:=schedule.
  Notation machine_state := ThreadPool.t.
  Notation event_trace := (seq machine_event).

  Inductive start_thread' genv: forall (m: mem) {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> mem -> Prop:=
  | StartThread: forall m tid0 ms ms' c_new vf arg om
                   (ctn: containsThread ms tid0)
                   (Hcode: getThreadC ctn = Kinit vf arg)
                   (Hinitial: initial_core Sem (tid2nat tid0) genv m vf (arg::nil) = Some (c_new, om))
                   (Hinv: invariant ms)
                   (Hms': updThreadC ctn (Krun c_new)  = ms'),
      start_thread' genv m ctn ms' (option_proj m om).
  Definition start_thread genv: forall (m: mem) {tid0 ms},
      containsThread ms tid0 -> machine_state -> mem -> Prop:=
    @start_thread' genv.

  Inductive resume_thread' ge: forall (m: mem) {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | ResumeThread: forall m tid0 ms ms' c c' X
                    (ctn: containsThread ms tid0)
                    (Hat_external: at_external Sem ge c m = Some X)
                    (Hafter_external:
                       after_external Sem ge None c = Some c')
                    (Hcode: getThreadC ctn = Kresume c Vundef)
                    (Hinv: invariant ms)
                    (Hms': updThreadC ctn (Krun c')  = ms'),
      resume_thread' ge m ctn ms'.
  Definition resume_thread ge: forall (m: mem) {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @resume_thread' ge.

  Inductive suspend_thread' ge: forall (m: mem) {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | SuspendThread: forall m tid0 ms ms' c X
                     (ctn: containsThread ms tid0)
                     (Hcode: getThreadC ctn = Krun c)
                     (Hat_external: at_external Sem ge c m = Some X)
                     (Hinv: invariant ms)
                     (Hms': updThreadC ctn (Kblocked c) = ms'),
      suspend_thread' ge m ctn ms'.
  Definition suspend_thread ge: forall (m: mem) {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @suspend_thread' ge.

  Inductive machine_step {genv:G}:
    Sch -> event_trace -> machine_state -> mem -> Sch
    -> event_trace -> machine_state -> mem -> Prop :=
  | start_step:
      forall tid U U' ms ms' m m' tr
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: start_thread genv m Htid ms' m'),
        machine_step U tr ms m U' tr ms' m'
  | resume_step:
      forall tid U U' ms ms' m tr
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: resume_thread genv m Htid ms'),
        machine_step U tr ms m U' tr ms' m
  | thread_step:
      forall tid U U' ms ms' m m' ev tr
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: threadStep genv Htid Hcmpt ms' m' ev),
        machine_step U tr ms m U'
                     (tr ++ (List.map (fun mev => internal tid mev) ev))
                     ms' (diluteMem m')
  | suspend_step:
      forall tid U U' ms ms' m tr
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: suspend_thread genv m Htid ms'),
        machine_step U tr ms m U' tr ms' m
  | sync_step:
      forall tid U U' ms ms' m m' tr ev
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: syncStep false genv Htid Hcmpt ms' m' ev),
        machine_step U tr ms m U' (tr ++ [:: external tid ev]) ms' m'
  | halted_step:
      forall tid U U' ms m tr
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Hinv: invariant ms)
        (Hhalted: threadHalted Htid),
        machine_step U tr ms m U' tr ms m
  | schedfail :
      forall tid U U' ms m tr
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Hcmpt: mem_compatible ms m)
        (Hinv: invariant ms)
        (Htid: ~ containsThread ms tid),
        machine_step U tr ms m U' tr ms m.

  Definition MachState: Type := (Sch * event_trace * machine_state)%type.

  Definition MachStep G (c:MachState) (m:mem)
             (c' :MachState) (m':mem) :=
    @machine_step G (fst (fst c)) (snd (fst c)) (snd c)  m
                  (fst (fst c')) (snd (fst c')) (snd c')  m'.

  Definition at_external (ge: G) (st : MachState) (m: mem)
    : option (external_function * list val) := None.

  Definition after_external (ge: G) (ov : option val) (st : MachState) :
    option (MachState) := None.

  Definition halted (st : MachState) : option val :=
    match schedPeek (fst (fst st)) with
    | Some _ => None
    | _ => Some Vundef
    end.

  Definition init_machine (U:schedule) (p : option RES.res) the_ge (m: mem)
             (f : val) (args : list val) : option (MachState * option mem):=
    match init_mach p the_ge m f args with
    | None => None
    | Some (c, om) => Some ((U, [::],c), om)
    end.

  Program Definition MachineSemantics (U:schedule) (p : option RES.res):
    CoreSemantics G MachState mem.
  intros.
  apply (@Build_CoreSemantics _ MachState _
                              (fun _ => init_machine U p)
                              at_external
                              after_external
                              halted
                              MachStep
        );
    unfold at_external, halted; try reflexivity.
  intros. inversion H; subst; rewrite HschedN; reflexivity.
  auto.
  Defined.


  Lemma initial_schedule: forall genv m main vals U U' p c tr om n,
      initial_core (MachineSemantics U p) n genv m main vals =  Some ((U',tr,c), om) ->
      U' = U /\ tr = nil.
        simpl. unfold init_machine. intros.
        destruct (init_mach p genv m main vals) as [[? ?]|]; try solve[inversion H].
        inversion H; subst; split; auto.
  Qed.

  (** Schedule safety of the fine-grained machine*)
   Inductive fsafe (ge : SEM.G) (tp : thread_pool) (m : mem) (U : Sch)
    : nat -> Prop :=
  | Safe_0: fsafe ge tp m U 0
  | HaltedSafe : forall n tr, halted (U, tr, tp) -> fsafe ge tp m U n
  | StepSafe : forall (tp' : thread_pool) (m' : mem)
                 (tr tr': event_trace) n,
      MachStep ge (U, tr, tp) m (schedSkip U, tr', tp') m' ->
      fsafe ge tp' m' (schedSkip U) n ->
      fsafe ge tp m U (S n).

End FineMachine.

Module Events <: EventSig
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

End Events.