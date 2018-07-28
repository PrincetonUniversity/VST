(* Hybrid Machine Signature *)

(** Defines the structure of Hybrid Machines. Some notable definitions:
    - MachineSig: The definitions that make a machine possible. That includes
      The definition of thread_steps, synchronization steps and other 
      accounting steps (resume, suspend, halt)... It also includes lemmas 
      about the relations (e.g. syncstep_equal_halted doesn't change halted threads)
    - machine_step/MachStep: gathers all the posible steps of the hybrid machine in
      a single smallstep relation. Used to define a Core-semantics for the 
      HybridMachine.
    - internal_step/external_step: two smallstep relations that together cover
      all possible steps of the machine. [internal_step] covers all threadsteps and
      external_step covers all other steps (synchronizations and accounting)
    - new_MachineSemantics: builds a ConcurSemantics out of a MachineSig, by using 
      internal_step/external_step steps.
    - MachineCoreSemantics: defines a coresemantics for the machine, by using
      MachStep as a smallstep, and it's never at_external, after_external.
    - HybridMachine: wraps both definitions of Core-semantics and ConcurSemantics 
      in a record. The two semantics are identical, except concure-semantics
      distinguishes between internal/external_step.
 *)

(**
   This file also constructs the Coarse and Finegrained HybridMachines 
   - HybridCoarseMachine
   - HybridFineMachine
   
   Moreover, it defines a notion of csafe for HybridCoarseMachine. (TODO: can this
   be moved elsewhere? Is this not compatible with fineMachines?
*)


From mathcomp.ssreflect Require Import ssreflect seq ssrbool.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.
Require Import VST.concurrency.common.core_semantics.
Require Import VST.sepcomp.event_semantics.
Require Export VST.concurrency.common.semantics.
Require Import VST.concurrency.common.threadPool.

Require Import VST.concurrency.common.machine_semantics.
Require Import VST.concurrency.common.permissions.

Require Import VST.concurrency.common.addressFiniteMap.
Require Import Coq.Program.Program.

(*Require Import VST.concurrency.safety.
Require Import VST.concurrency.coinductive_safety.*)

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

  (* Santiago July 9: On consultation with Andrew and Lennart:
     Turns out all we need from the traces, is the content of the 
     observable locations (observable according to the delta_map, which is not in the trace)
     events now record:
     - delta_contents: is the memory, only with the contetns of "observable" memory
   *)

  (*  move this to  VST.concurrency.common.permissions*)
  Definition delta_content := (Maps.PTree.t (Z -> option memval)).
  Inductive sync_event : Type :=
  | release : address -> option delta_content -> sync_event
  | acquire : address -> option delta_content -> sync_event
  | mklock :  address -> sync_event
  | freelock : address -> sync_event
  | spawn : address -> option delta_content -> option delta_content -> sync_event
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
    
    Variable n: option nat.
    Context {resources: Resources}
            {Sem: Semantics}
            {ThreadPool : ThreadPool.ThreadPool}
            {DilMem : DiluteMem}.
    Definition thread_pool := ThreadPool.t.
    Definition C:= (@semC Sem).
    Definition G:= (@semG Sem).
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
        ; add_block: forall {ms m tid},
            mem_compatible ms m -> containsThread ms tid -> mem -> res
                                     
        (** Step relations *)
        ; threadStep:
            forall {tid0 ms m},
              containsThread ms tid0 -> mem_compatible ms m ->
              thread_pool -> mem -> seq mem_event -> Prop

        ; threadStep_at_Krun:
            forall i tp m cnt cmpt tp' m' tr,
              @threadStep i tp m cnt cmpt tp' m' tr ->
              (exists q, @getThreadC _ _ _ i tp cnt = Krun q)                                        
                                                    
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

        ; init_mach : option res -> mem -> thread_pool -> mem -> val -> list val -> Prop}.


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

   Inductive start_thread : forall (m: mem) {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> mem -> Prop:=
  | StartThread: forall m m' m_new tid0 ms ms' c_new vf arg
                    (ctn: containsThread ms tid0)
                    (Hcode: getThreadC ctn = Kinit vf arg)
                    (Hcmpt: mem_compatible ms m)
                    (Hperm: install_perm Hcmpt ctn m')
                    (Hinitial: initial_core semSem tid0
                                            m' c_new m_new vf (arg::nil))
                    (Hinv: invariant ms)
                    (Hms': updThread ctn (Krun c_new) (add_block Hcmpt ctn m_new) = ms'),
                    (* (Hcmpt': mem_compatible ms' m_new) *)
                    (* (Hinv': invariant ms')*)
      start_thread m ctn ms' m_new.

   (** Resume and Suspend: threads running must be preceded by a Resume
       and followed by Suspend.  This functions wrap the state to
       indicate it's ready to take a syncronisation step or resume
       running. (This keeps the invariant that at most one thread is not
       at_external) *)
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
    { isCoarse : bool;
      yield: schedule -> schedule}.
  Context {scheduler : Scheduler}.

  Inductive machine_step:
    schedule -> event_trace -> machine_state -> mem -> schedule ->
    event_trace -> machine_state -> mem -> Prop :=
  | start_step:
        forall tid U ms ms' m m' tr
          (HschedN: schedPeek U = Some tid)
          (Htid: containsThread ms tid)
          (Htstep: start_thread m Htid ms' m'),
          machine_step U tr ms m (yield U) tr ms' (diluteMem m')
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
          (Htstep: syncStep isCoarse Htid Hcmpt ms' m' ev),
          machine_step U tr ms m U' (tr ++ [:: external tid ev]) ms' m'
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
      : option (external_function * list val) := None.
    
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
               (st : MachState) (m': mem) (f : val) (args : list val)
      : Prop :=
      match st with (U', [::], c) => U' = U /\ init_mach r m c m' f args | _ => False end.

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

    Definition make_init_machine c r:= 
        mkPool (Krun c) r.
    Definition init_machine' (the_ge : semG) m
               c m' (f : val) (args : list val) 
      : option res -> Prop := fun op_r =>
                            if op_r is Some r then 
                              init_mach op_r m (make_init_machine c r) m' f args
                            else False.
    Definition init_machine'' (op_m: option mem)(op_r : option res)(m: mem)
               (tp : thread_pool) (m': mem) (f : val) (args : list val)
      : Prop :=
      op_m = Some m /\
      if op_r is Some r then 
        init_mach op_r m tp m' f args
      else False.
    
    Definition unique_Krun tp i :=
      forall j cnti q, 
        @getThreadC _ _ _ j tp cnti = Krun q ->
        eq_nat_dec i j.

    Lemma hybrid_initial_schedule: forall m m' main vals U p st n,
        initial_core (MachineCoreSemantics U p) n m st m' main vals ->
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
          external_step U tr ms m (yield U) tr ms' (diluteMem m')
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
            (Htstep: syncStep isCoarse Htid Hcmpt ms' m' ev),
            external_step U tr ms m  U' (tr ++ [:: external tid ev]) ms' m'
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
            @machine_step U tr st m (yield U) (tr ++ tr') st' m'.
      Proof.
        move=>  U st m st' m' tr istp;
                 inversion istp; eexists; solve [econstructor; eauto].
      Qed.
      Lemma step_equivalence3: forall U tr st m U' tr' st' m',
          @external_step U tr st m U' tr' st' m' ->
          exists tr1, tr' = tr ++ tr1 /\ @machine_step U tr st m U' tr' st' m'.
      Proof. move=>  U tr st m U' nil st' m' estp.
             inversion estp; do 2 eexists; try reflexivity; try solve [symmetry; apply List.app_nil_r];
               [
                 solve[econstructor 1 ; eauto]|
                 solve[econstructor 2 ; eauto]|
                 solve[econstructor 4 ; eauto]|
                 solve[econstructor 5 ; eauto]|
                 solve[econstructor 6 ; eauto]].
      Qed.

      Set Printing Implicit.
      Program Definition new_MachineSemantics (op_m:option Mem.mem):
        @ConcurSemantics G nat schedule event_trace machine_state mem res (*@semC Sem*).
      apply (@Build_ConcurSemantics _ nat schedule event_trace machine_state _ _ (*_*)
                                    (init_machine'' op_m)
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
        ; ConcurMachineSemantics: option mem ->
                                  @ConcurSemantics G nat (seq.seq nat) event_trace t mem res (*@semC Sem*)
        ; initial_schedule: forall m m' main vals U p st n,
            initial_core (MachineCoreSemantics U p) n m st m' main vals ->
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
        {| diluteMem := fun x => x |}.
      intros.
      split; auto.
      Defined.
      
      Instance scheduler : Scheduler :=
        {| isCoarse := true;
           yield := fun x => x |}.

      Notation thread_pool := t.
      Notation C:= (semC).
      Notation G:= (semG).
      Local Notation ctl := (@ctl C).
      Notation machine_state := thread_pool.
      Notation schedule := (seq nat).
      Notation event_trace := (seq machine_event).

      Definition HybridCoarseMachine : HybridMachine :=
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

      
      (** Schedule safety of the coarse-grained machine*)
      Inductive concur_safe U tp (m : mem) : nat -> Prop :=
      | concur_Safe_0: concur_safe U tp m 0
      | concur_HaltedSafe: forall n, halted_machine (U, nil, tp) -> concur_safe U tp m n
      | concur_Internal : forall tp' m' n
                     (Hstep: internal_step U tp m tp' m')
                     (Hsafe: concur_safe U tp' m' n),
          concur_safe U tp m (S n)
      | concur_External: forall tp' m' n (tr tr': event_trace)
                     (Hstep: external_step U tr tp m U tr' tp' m')
                     (Hsafe: concur_safe U tp' m' n),
          concur_safe U tp m (S n)
      | concur_External_Angel: forall tp' m' n (tr tr': event_trace)
                     (Hstep: external_step U tr tp m (schedSkip U) tr' tp' m')
                     (Hsafe: forall U'', concur_safe U'' tp' m' n),
          concur_safe U tp m (S n).
      
      (* TODO: Make a new file with safety lemmas. *)
      Lemma csafe_reduce:
        forall sched tp tr mem n m,
          csafe (sched, tr, tp) mem n ->
          m <= n ->
          csafe (sched, tr, tp) mem m.
      Proof.
        intros until 1; revert m.
        induction H; intros.
        - assert (m0 = 0) by omega; subst; constructor.
        - apply HaltedSafe; auto.
        - destruct m0; [constructor|].
          eapply CoreSafe; eauto.
          apply IHcsafe; omega.
        - destruct m0; [constructor|].
          eapply AngelSafe; eauto.
          intro; apply H; omega.
      Qed.

      Lemma schedSkip_id: forall U, schedSkip U = U -> U = nil.
      Proof.
        induction U; auto; simpl; intros.
        destruct U; try discriminate; simpl in *.
        inversion H; subst.
        specialize (IHU H2); discriminate.
      Qed.

      Lemma csafe_trace: forall n U tr tp m,
        csafe (U, tr, tp) m n ->
        forall tr', csafe (U, tr', tp) m n.
      Proof.
        induction n0; intros; [constructor|].
        inversion H; subst; [constructor; auto | inversion Hstep; subst; simpl in *; try inversion Htstep; subst; try (apply schedSkip_id in HschedS; subst);
          try discriminate | inversion Hstep; simpl in *; try inversion Htstep; try match goal with H : U = schedSkip U |- _ =>
          symmetry in H; apply schedSkip_id in H; subst end; try discriminate].
        - eapply CoreSafe; eauto.
          erewrite cats0.
          change U with (yield U) at 2.
          change m'0 with (diluteMem m'0) at 2.
          eapply start_step; eauto.
        - eapply CoreSafe, IHn0; eauto.
          erewrite cats0.
          change U with (yield U) at 2.
          change m' with (diluteMem m') at 2.
          eapply resume_step; eauto.
        - eapply CoreSafe; eauto.
          change U with (yield U) at 2.
          change m'0 with (diluteMem m'0) at 2.
          eapply thread_step; eauto.
        - eapply AngelSafe; [|intro; eapply IHn0; eauto].
          erewrite cats0.
          eapply suspend_step; eauto.
        - eapply AngelSafe; eauto.
          eapply sync_step; eauto.
        - subst.
          eapply AngelSafe; [|intro; eapply IHn0; eauto].
          erewrite cats0.
          eapply schedfail; eauto.
      Qed.

      Lemma csafe_concur_safe: forall U tr tp m n, csafe (U, tr, tp) m n -> concur_safe U tp m n.
      Proof.
        intros.
        remember (U, tr, tp) as st; revert dependent tp; revert U tr.
        induction H; intros; subst; simpl in *.
        - constructor.
        - constructor; auto.
        - apply step_equivalence1 in Hstep as [[]|].
          + eapply concur_Internal; eauto.
          + simpl in *.
            inversion H0; subst; try solve [apply schedSkip_id in HschedS; subst; constructor; auto];
              eapply concur_External; eauto.
        - apply step_equivalence1 in Hstep as [[]|].
          + simpl in *.
            apply schedSkip_id in H0; subst.
            constructor; auto.
          + simpl in *.
            eapply concur_External_Angel; eauto.
      Qed.

      Lemma concur_safe_csafe: forall U tr tp m n, concur_safe U tp m n -> csafe (U, tr, tp) m n.
      Proof.
        intros; revert tr.
        induction H; intro.
        - constructor.
        - constructor; auto.
        - eapply step_equivalence2 in Hstep as [].
          eapply CoreSafe; hnf; simpl; eauto.
        - inversion Hstep; subst; try solve [apply schedSkip_id in HschedS; subst; constructor; auto];
            eapply CoreSafe; hnf; simpl; eauto.
          + setoid_rewrite List.app_nil_r.
            rewrite <- H4 at 2.
            eapply start_step; eauto.
          + setoid_rewrite List.app_nil_r.
            rewrite <- H4 at 2.
            eapply resume_step; eauto.
        - inversion Hstep; subst;
            try solve [symmetry in H4; simpl in H4; apply schedSkip_id in H4; subst; constructor; auto];
            eapply AngelSafe; hnf; simpl; eauto.
          + setoid_rewrite List.app_nil_r.
            eapply suspend_step; eauto.
          + eapply sync_step; eauto.
          + setoid_rewrite List.app_nil_r.
            eapply schedfail; eauto.
      Qed.

      (** Trace of the coarse-grained machine*)
      (* Note that this does not replace csafe - csafe guarantees safety for any rearrangement
         of the schedule at synchronization points, while this fixes a particular schedule. *)
      (* Note also that ctrace does not specify the number of steps required to produce the trace. *)
      Inductive ctrace (st : MachState) (m : mem) : event_trace -> Prop :=
      | Trace_0: ctrace st m nil (* if a state has trace tr, it also has all prefixes of tr *)
      | Trace_Step : forall tp' m' U' tr tr'
                     (Hstep: MachStep st m (U',(snd (fst st)) ++ tr,tp') m')
                     (Hsafe: ctrace (U',(snd (fst st)) ++ tr,tp') m' tr'),
          ctrace st m (tr ++ tr').

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
        {| isCoarse := false;
           yield := fun x => schedSkip x |}.

      Definition HybridFineMachine : HybridMachine:=
        @Build_HybridMachine resources Sem ThreadPool _ _ _
                             (MachineCoreSemantics)
                             (new_MachineSemantics)
                             (hybrid_initial_schedule).

      (** Schedule safety of the fine-grained machine*)
      Inductive fsafe (tp : thread_pool) (m : mem) (U : schedule)
        : nat -> Prop :=
      | Safe_0: fsafe tp m U 0
      | HaltedSafe : forall n tr, halted_machine (U, tr, tp) -> fsafe tp m U n
      | StepSafe : forall (tp' : thread_pool) (m' : mem)
                     (tr tr': event_trace) n,
          MachStep (U, tr, tp) m (schedSkip U, tr', tp') m' ->
          fsafe tp' m' (schedSkip U) n ->
          fsafe tp m U (S n).

      (** Trace of the fine-grained machine*)
      Inductive ftrace (tp : thread_pool) (m : mem) (U : schedule)
        : event_trace -> Prop :=
      | Trace_0: ftrace tp m U nil
      | StepTrace : forall (tp' : thread_pool) (m' : mem)
                     (tr tr' tr'': event_trace),
          MachStep (U, tr, tp) m (schedSkip U, tr ++ tr', tp') m' ->
          ftrace tp' m' (schedSkip U) tr'' ->
          ftrace tp m U (tr' ++ tr'').
    End HybridFineMachine.
End HybridFineMachine.

End HybridMachineSig.
