From mathcomp.ssreflect Require Import ssreflect seq ssrbool.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.
Require Import VST.concurrency.core_semantics.
Require Import VST.sepcomp.event_semantics.
Require Export VST.concurrency.semantics.
Require Import VST.concurrency.threadPool.

Require Import VST.concurrency.machine_semantics.
Require Import VST.concurrency.permissions.

Require Import VST.concurrency.addressFiniteMap.
Require Import Coq.Program.Program.

Require Import VST.concurrency.safety.
Require Import VST.concurrency.coinductive_safety.

Notation EXIT :=
  (EF_external "EXIT" (mksignature (AST.Tint::nil) None)).
Notation CREATE_SIG := (mksignature (AST.Tint::AST.Tint::nil) None cc_default).
Notation CREATE := (EF_external "spawn" CREATE_SIG).
Notation MKLOCK :=
  (EF_external "makelock" (mksignature (AST.Tptr::nil) None cc_default)).
Notation FREE_LOCK :=
  (EF_external "freelock" (mksignature (AST.Tptr::nil) None cc_default)).
Notation LOCK_SIG := (mksignature (AST.Tptr::nil) None cc_default).
Notation LOCK := (EF_external "acquire" LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tptr::nil) None cc_default).
Notation UNLOCK := (EF_external "release" UNLOCK_SIG).

Module Events.
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
  | internal: nat -> mem_event -> machine_event
  | external : nat -> sync_event -> machine_event.

  Definition thread_id ev : nat :=
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

Module HybridMachineSig.
  Import Events ThreadPool.


  (** Used to erase permissions of the machine when needed, e.g. fine
  machine erases max permissions, bare machine erases all permissions
  *)
  
  Class DiluteMem :=
    { diluteMem: mem -> mem;
      diluteMem_valid: forall m,
          forall b, Memory.Mem.valid_block (diluteMem m) b <-> Memory.Mem.valid_block m b
    }.
  
  Section HybridMachineSig.
    
    Variable n: nat.
    Context {resources: Resources}
            {Sem: Semantics}
            {ThreadPool : ThreadPool.ThreadPool}
            {DilMem : DiluteMem}.
    Definition thread_pool := ThreadPool.t.
    Definition C:= (semC).
    Definition G:= (semG).
    
    Local Notation ctl := (@ctl C).

    Class MachineSig :=
      {
        richMem: Type
        ; dryMem: richMem -> mem

        (** The thread pool respects the memory*)
        ; mem_compatible: thread_pool -> mem -> Prop
        ; invariant: thread_pool -> Prop

        ; install_perm: forall {ms m tid},
            mem_compatible ms m -> containsThread ms tid -> mem -> Prop
                                     
        (** Step relations *)
        ; threadStep:
            forall {tid0 ms m},
              containsThread ms tid0 -> mem_compatible ms m ->
              thread_pool -> mem -> seq mem_event -> Prop

        ;  threadStep_equal_run:
             forall i tp m cnt cmpt tp' m' tr,
               @threadStep i tp m cnt cmpt tp' m' tr ->
               forall (j: nat),
                 (exists cntj q, @getThreadC _ _ _ j tp cntj = Krun q) <->
                 (exists cntj' q', @getThreadC _ _ _ j tp' cntj' = Krun q')

        ; syncStep:
            bool -> (* if it's a Coarse machine. Temp solution to propagating changes. *)
            forall {tid0 ms m},
                containsThread ms tid0 -> mem_compatible ms m ->
                thread_pool -> mem -> sync_event -> Prop
                                                   
        ;  syncstep_equal_run:
             forall b i tp m cnt cmpt tp' m' tr,
               @syncStep b i tp m cnt cmpt tp' m' tr ->
               forall j,
                 (exists cntj q, @getThreadC _ _ _ j tp cntj = Krun q) <->
                 (exists cntj' q', @getThreadC _ _ _ j tp' cntj' = Krun q')
                   
        ;  syncstep_not_running:
             forall b i tp m cnt cmpt tp' m' tr,
               @syncStep b i tp m cnt cmpt tp' m' tr ->
               forall cntj q, ~ @getThreadC _ _ _ i tp cntj = Krun q
                                                            
        ; threadHalted:
            forall {tid0 ms},
              containsThread ms tid0 -> Prop
                                         
        ;  threadHalt_update:
             forall i j, i <> j ->
                    forall tp cnt cnti c' cnt',
                      (@threadHalted j tp cnt) <->
                      (@threadHalted j (@updThreadC _ _ _ i tp cnti c') cnt') 
                        
        ;  syncstep_equal_halted:
             forall b i tp m cnti cmpt tp' m' tr,
               @syncStep b i tp m cnti cmpt tp' m' tr ->
               forall j cnt cnt',
                 (@threadHalted j tp cnt) <->
                 (@threadHalted j tp' cnt')

(*        ;  threadStep_not_unhalts:
             forall g i tp m cnt cmpt tp' m' tr,
               @threadStep g i tp m cnt cmpt tp' m' tr ->
               forall j cnt cnt',
                 (@threadHalted j tp cnt) ->
                 (@threadHalted j tp' cnt') *)

        ; init_mach : option res -> mem -> thread_pool -> val -> list val -> Prop}.


    Context {machineSig: MachineSig}.

    Definition event_trace := (seq machine_event).
    Definition schedule := (seq nat).
    
    Definition MachState : Type:= (schedule * event_trace * t)%type.
  
    Definition schedPeek sch: option nat:=
      match sch with
        nil => None
      | cons hd tl => Some hd
      end.
  
  Definition schedSkip sch: (seq nat):= List.tl sch.
  Definition machine_state := thread_pool.

  (** Resume and Suspend: threads running must be preceded by a Resume
     and followed by Suspend.  This functions wrap the state to
     indicate it's ready to take a syncronisation step or resume
     running. (This keeps the invariant that at most one thread is not
     at_external) *)
  (*TODO: probably need to update the permissions for initial core too*)
   Inductive start_thread : forall (m: mem) {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> mem -> Prop:=
  | StartThread: forall m m' tid0 ms ms' c_new vf arg
                    (ctn: containsThread ms tid0)
                    (Hcode: getThreadC ctn = Kinit vf arg)
                    (Hcmpt: mem_compatible ms m)
                    (Hperm: install_perm Hcmpt ctn m')
                    (Hinitial: initial_core semSem tid0
                                            m' c_new vf (arg::nil))
                    (Hinv: invariant ms)
                    (Hms': updThreadC ctn (Krun c_new)  = ms'),
      start_thread m ctn ms' m.


   Inductive resume_thread' : forall (m: mem) {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | ResumeThread: forall m tid0 ms ms' c c' X m'
                    (ctn: containsThread ms tid0)
                    (Hcmpt: mem_compatible ms m)
                    (Hperm: install_perm Hcmpt ctn m')
                    (Hat_external: at_external semSem c m' = Some X)
                    (Hafter_external: after_external semSem None c m' = Some c')
                    (Hcode: getThreadC ctn = Kresume c Vundef)
                    (Hinv: invariant ms)
                    (Hms': updThreadC ctn (Krun c')  = ms'),
      resume_thread' m ctn ms'.
  Definition resume_thread: forall m {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @resume_thread'.

  Inductive suspend_thread': forall m {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | SuspendThread: forall m tid0 ms ms' c X m'
                     (ctn: containsThread ms tid0)
                     (Hcmpt: mem_compatible ms m)
                     (Hcode: getThreadC ctn = Krun c)
                     (Hperm: install_perm Hcmpt ctn m')
                     (Hat_external: at_external semSem c m'  = Some X)
                     (Hinv: invariant ms)
                     (Hms': updThreadC ctn (Kblocked c) = ms'),
      suspend_thread' m ctn ms'.
  Definition suspend_thread: forall (m: mem) {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @suspend_thread'.

    (** Provides control over scheduling. For example,
        for FineMach this is schedSkip, for CoarseMach this is just id *)
  Class Scheduler :=
    {yield: schedule -> schedule}.
  
  Context {scheduler : Scheduler}.

  Inductive machine_step:
    schedule -> event_trace -> machine_state -> mem -> schedule ->
    event_trace -> machine_state -> mem -> Prop :=
  | start_step:
        forall tid U ms ms' m m' tr
          (HschedN: schedPeek U = Some tid)
          (Htid: containsThread ms tid)
          (Htstep: start_thread m Htid ms' m'),
          machine_step U tr ms m (yield U) tr ms' m'
    | resume_step:
        forall tid U ms ms' m tr
          (HschedN: schedPeek U = Some tid)
          (Htid: containsThread ms tid)
          (Htstep: resume_thread m Htid ms'),
          machine_step U tr ms m (yield U) tr ms' m
    | thread_step:
        forall tid U ms ms' m m' ev tr
          (HschedN: schedPeek U = Some tid)
          (Htid: containsThread ms tid)
          (Hcmpt: mem_compatible ms m)
          (Htstep: threadStep Htid Hcmpt ms' m' ev),
          machine_step U tr ms m (yield U)
                       (tr ++ (List.map (fun mev => internal tid mev) ev)) ms' (diluteMem m')
    | suspend_step:
        forall tid U U' ms ms' m tr
          (HschedN: schedPeek U = Some tid)
          (HschedS: schedSkip U = U')        (*Schedule Forward*)
          (Htid: containsThread ms tid)
          (Htstep:suspend_thread m Htid ms'),
          machine_step U tr ms m U' tr ms' m
    | sync_step:
        forall tid U U' ms ms' m m' ev tr
          (HschedN: schedPeek U = Some tid)
          (HschedS: schedSkip U = U')        (*Schedule Forward*)
          (Htid: containsThread ms tid)
          (Hcmpt: mem_compatible ms m)
          (Htstep: syncStep true Htid Hcmpt ms' m' ev),
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
          (Htid: ~ containsThread ms tid)
          (Hinv: invariant ms)
          (Hcmpt: mem_compatible ms m)
          (HschedS: schedSkip U = U'),        (*Schedule Forward*)
          machine_step U tr ms m U' tr ms m.

    Definition MachStep (c:MachState) (m:mem)
               (c':MachState) (m':mem) :=
      @machine_step (fst (fst c)) (snd (fst c)) (snd c)  m
                    (fst (fst c')) (snd (fst c')) (snd c')  m'.

    Definition at_external_mach (st : MachState) (m: mem)
      : option (external_function * signature * list val) := None.
    
    Definition after_external_mach (ov : option val) (st : MachState) (m : mem) :
      option (MachState) := None.
    
    (*not clear what the value of halted should be*)
    (*Nick: IMO, the machine should be halted when the schedule is empty.
      The value is probably unimportant? *)
    (*Santiago: I belive empty schedule should "diverge". After all that's *)
    Definition halted_machine (st : MachState) : option val :=
      match schedPeek (fst (fst st)) with
      | Some _ => None
      | _ => Some Vundef
      end.

    Definition init_machine (U:schedule) (r : option res) (m: mem)
               (st : MachState) (f : val) (args : list val)
      : Prop :=
      match st with (U', [::], c) => U' = U /\ init_mach r m c f args | _ => False end.

    Program Definition MachineCoreSemantics (U:schedule) (r : option res):
      CoreSemantics MachState mem.
    intros.
    apply (@Build_CoreSemantics MachState _
                                (fun n => init_machine U r)
                                at_external_mach
                                after_external_mach
                                (fun st i => halted_machine st = Some (Vint i)) (* this is False *)
                                MachStep
          );
      unfold at_external_mach, halted_machine; try reflexivity.
    intros. inversion H; subst; rewrite HschedN; intro Hcontra; discriminate.
    Defined.

    Definition init_machine' (r : option res) (the_ge : semG) m
               (c : machine_state) (f : val) (args : list val) 
      : Prop :=
      init_mach r m c f args.
    
    Definition unique_Krun tp i :=
      forall j cnti q,
        @getThreadC _ _ _ j tp cnti = Krun q ->
        ~ @threadHalted _ j tp cnti  ->
        eq_nat_dec i j.

    (* XXX: Wrong? *)
    Lemma hybrid_initial_schedule: forall m main vals U p st n,
        initial_core (MachineCoreSemantics U p) n m st main vals ->
        exists c, st = (U, nil, c).
      simpl. destruct st as ((?, ?), ?); simpl; intros.
      destruct e; [|contradiction].
      destruct H; subst; eauto.
    Qed.

      (** The new semantics below makes internal (thread) and external (machine)
          steps explicit *)
      Inductive internal_step:
        schedule -> machine_state -> mem -> machine_state -> mem -> Prop :=
      | thread_step':
          forall tid U ms ms' m m' ev
            (HschedN: schedPeek U = Some tid)
            (Htid: containsThread ms tid)
            (Hcmpt: mem_compatible ms m)
            (Htstep: threadStep Htid Hcmpt ms' m' ev),
            internal_step U ms m ms' (diluteMem m').

      Inductive external_step:
        schedule -> event_trace -> machine_state -> mem -> schedule ->
        event_trace -> machine_state -> mem -> Prop :=
      | start_state': forall tid U ms ms' m m' tr
                        (HschedN: schedPeek U = Some tid)
                        (Htid: containsThread ms tid)
                        (Htstep: start_thread m Htid ms' m'),
          external_step U tr ms m (yield U) tr ms' m'
      | resume_step':
          forall tid U ms ms' m tr
            (HschedN: schedPeek U = Some tid)
            (Htid: containsThread  ms tid)
            (Htstep: resume_thread m Htid ms'),
            external_step U tr ms m (yield U) tr ms' m
      | suspend_step':
          forall tid U U' ms ms' m tr
            (HschedN: schedPeek U = Some tid)
            (HschedS: schedSkip U = U')        (*Schedule Forward*)
            (Htid: containsThread ms tid)
            (Htstep:suspend_thread m Htid ms'),
            external_step U tr ms m U' tr ms' m
      | sync_step':
          forall tid U U' ms ms' m m' ev tr
            (HschedN: schedPeek U = Some tid)
            (HschedS: schedSkip U = U')        (*Schedule Forward*)
            (Htid: containsThread ms tid)
            (Hcmpt: mem_compatible ms m)
            (Htstep: syncStep true Htid Hcmpt ms' m' ev),
            external_step U tr ms m  U' (tr ++ [:: external tid ev]) ms' m'
      | halted_step':
          forall tid U U' ms m tr
            (HschedN: schedPeek U = Some tid)
            (HschedS: schedSkip U = U')        (*Schedule Forward*)
            (Htid: containsThread ms tid)
            (Hcmpt: mem_compatible ms m)
            (Hinv: invariant ms)
            (Hhalted: threadHalted Htid),
            external_step U tr ms m  U' tr ms m
      | schedfail':
          forall tid U U' ms m tr
            (HschedN: schedPeek U = Some tid)
            (Htid: ~ containsThread ms tid)
            (Hinv: invariant ms)
            (Hcmpt: mem_compatible ms m)
            (HschedS: schedSkip U = U'),        (*Schedule Forward*)
            external_step U tr ms m U' tr ms m.

      (*Symmetry*)
      (* These steps are basically the same: *)
      Lemma step_equivalence1: forall U tr st m U' tr' st' m',
          @machine_step U tr st m U' tr' st' m' ->
          (U' = yield U /\ @internal_step U st m st' m') \/
          @external_step U tr st m U' tr' st' m'.
      Proof.
        move=> U tr st m U' tr' st' m' ms.
        inversion ms; simpl in *;
          try solve [ left; repeat split=>//; econstructor; eauto];
          try solve[right; subst; econstructor; eauto].
      Qed.

      Lemma step_equivalence2: forall U st m st' m' tr,
          @internal_step U st m st' m' ->
          exists tr',
            @machine_step U tr st m (yield U) tr' st' m'.
      Proof.
        move=>  U st m st' m' tr istp;
                 inversion istp; eexists; solve [econstructor; eauto].
      Qed.
      Lemma step_equivalence3: forall U tr st m U' tr' st' m',
          @external_step U tr st m U' tr' st' m' ->
          @machine_step U tr st m U' tr' st' m'.
      Proof. move=>  U tr st m U' nil st' m' estp.
             inversion estp;
               [
                 solve[econstructor 1 ; eauto]|
                 solve[econstructor 2 ; eauto]|
                 solve[econstructor 4 ; eauto]|
                 solve[econstructor 5 ; eauto]|
                 solve[econstructor 6 ; eauto]|
                 solve[econstructor 7 ; eauto]].
      Qed.

      Program Definition new_MachineSemantics (U:schedule) (r : option res):
        @ConcurSemantics G nat schedule event_trace machine_state mem.
      apply (@Build_ConcurSemantics _ nat schedule event_trace  machine_state _
                                    (init_machine' r)
                                    (fun U st => halted_machine (U, nil, st))
                                    (fun ge U st m st' m' =>
                                       @internal_step U st m
                                                      st' m'
                                    )
                                    (fun ge U (tr:event_trace) st m U' tr' st' m' =>
                                       @external_step U tr st m
                                                      U' tr' st' m'
                                    )
                                    unique_Krun)
      ;
      unfold at_external_mach, halted_machine; try reflexivity.
      - intros. inversion H; subst; rewrite HschedN; reflexivity.
      - intros. inversion H; subst; rewrite HschedN; reflexivity.
    Defined.

    (** The class of Hybrid Machines parameterized by:
        - Threadwise semantics
        - Scheduler granularity *)
    Class HybridMachine:=
      {
        MachineSemantics: schedule -> option res ->
                          CoreSemantics MachState mem
        ; ConcurMachineSemantics: schedule -> option res ->
                                  @ConcurSemantics G nat (seq.seq nat) event_trace t mem
        ; initial_schedule: forall m main vals U p st n,
            initial_core (MachineCoreSemantics U p) n m st main vals ->
            exists c, st = (U, nil, c) (*XXX:this seems wrong *)
      }.

  End HybridMachineSig.
  
  (** Definition of the Coarse-grain hybrid machine *)
  Module HybridCoarseMachine.
    Section HybridCoarseMachine.
      Variable n: nat.
      Context {resources: Resources}
              {Sem: Semantics}
              {ThreadPool : ThreadPool.ThreadPool}
              {machineSig: MachineSig}.

      Instance DilMem : DiluteMem :=
        {| diluteMem := id |}.
      intros.
      split; auto.
      Defined.
      
      Instance scheduler : Scheduler :=
        {| yield := fun x => x |}.

      Notation thread_pool := t.
      Notation C:= (semC).
      Notation G:= (semG).
      Local Notation ctl := (@ctl C).
      Notation machine_state := thread_pool.
      Notation schedule := (seq nat).
      Notation event_trace := (seq machine_event).

      Definition HybridCoarseMachine : HybridMachine:=
        @Build_HybridMachine resources Sem ThreadPool _ _ _
                             (MachineCoreSemantics)
                             (new_MachineSemantics)
                             (hybrid_initial_schedule).

      (** Schedule safety of the coarse-grained machine*)
      Inductive csafe (st : MachState) (m : mem) : nat -> Prop :=
      | Safe_0: csafe st m 0
      | HaltedSafe: forall n, halted_machine st -> csafe st m n
      | CoreSafe : forall tp' m' n tr
                     (Hstep: MachStep st m (fst (fst st),(snd (fst st)) ++ tr,tp') m')
                     (Hsafe: csafe (fst (fst st),(snd (fst st)) ++ tr,tp') m' n),
          csafe st m (S n)
      | AngelSafe: forall tp' m' n (tr: event_trace)
                     (Hstep: MachStep st m (schedSkip (fst (fst st)),(snd (fst st)) ++ tr,tp') m')
                     (Hsafe: forall U'', csafe (U'',(snd (fst st)) ++ tr,tp') m' n),
          csafe st m (S n).

      (* TODO: Make a new file with safety lemmas. *)
      Lemma csafe_reduce:
        forall sched tp mem n m,
          csafe (sched, [::], tp) mem n ->
          m <= n ->
          csafe (sched, [::], tp) mem m.
      Proof.
        Admitted.
      
    End HybridCoarseMachine.
  End HybridCoarseMachine.
  
  Module HybridFineMachine.
    Section HybridFineMachine.

      Variable n: nat.
      Context {resources: Resources}
              {Sem: Semantics}
              {ThreadPool : ThreadPool.ThreadPool}
              {machineSig: MachineSig}.

      Notation thread_pool := t.
      Notation C:= (semC).
      Notation G:= (semG).
      Local Notation ctl := (@ctl C).
      Notation machine_state := thread_pool.
      Notation schedule := (seq nat).  
      Notation event_trace := (seq machine_event).

      Context {dilMem : DiluteMem}.
      
      Instance scheduler : Scheduler :=
        {| yield := fun x => schedSkip x |}.

      Definition HybridFineMachine : HybridMachine:=
        @Build_HybridMachine resources Sem ThreadPool _ _ _
                             (MachineCoreSemantics)
                             (new_MachineSemantics)
                             (hybrid_initial_schedule).

      (** Schedule safety of the fine-grained machine*)
      Inductive fsafe (ge : G) (tp : thread_pool) (m : mem) (U : schedule)
        : nat -> Prop :=
      | Safe_0: fsafe ge tp m U 0
      | HaltedSafe : forall n tr, halted_machine (U, tr, tp) -> fsafe ge tp m U n
      | StepSafe : forall (tp' : thread_pool) (m' : mem)
                     (tr tr': event_trace) n,
          MachStep (U, tr, tp) m (schedSkip U, tr', tp') m' ->
          fsafe ge tp' m' (schedSkip U) n ->
          fsafe ge tp m U (S n).
    End HybridFineMachine.
End HybridFineMachine.

End HybridMachineSig.
