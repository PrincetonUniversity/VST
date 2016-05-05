Require Import compcert.common.Memory.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.lib.Integers.
Require Import Coq.ZArith.ZArith.
Require Import sepcomp.semantics.

Load scheduler.

Require Import Coq.Program.Program.
Require Import ssreflect seq.

(* This module represents the arguments
   to build a CoreSemantics with 
   compcert mem. This is used by BOTH
   Juicy machine and dry machine. *)
Module Type Semantics.
  Parameter G: Type.
  Parameter C: Type.
  Definition M: Type:= mem.
  Parameter Sem: CoreSemantics G C M.
End Semantics.

Notation EXIT := 
  (EF_external "EXIT" (mksignature (AST.Tint::nil) None)). 

Notation CREATE_SIG := (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint) cc_default).
Notation CREATE := (EF_external "CREATE" CREATE_SIG).

Notation READ := 
  (EF_external "READ"
               (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint) cc_default)).
Notation WRITE := 
  (EF_external "WRITE"
               (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint) cc_default)).

Notation MKLOCK := 
  (EF_external "MKLOCK" (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default)).
Notation FREE_LOCK := 
  (EF_external "FREE_LOCK" (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default)).

Notation LOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default).
Notation LOCK := (EF_external "LOCK" LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default).
Notation UNLOCK := (EF_external "UNLOCK" UNLOCK_SIG).

Notation block  := Values.block.
Notation address:= (block * Z)%type.
Definition b_ofs2address b ofs : address:=
  (b, Int.intval ofs).

Inductive ctl {cT:Type} : Type :=
| Krun : cT -> ctl
| Kstop : cT -> ctl
| Kresume : cT -> ctl.

Definition EqDec: Type -> Type := 
  fun A : Type => forall a a' : A, {a = a'} + {a <> a'}.


Module Type ThreadPoolSig.
  Declare Module TID: ThreadID.
  Declare Module SEM: Semantics.
  
  Import TID.
  Import SEM.

  Parameter res : Type.
  Parameter LockPool : Type.
  Parameter t : Type.

  Parameter lpool : t -> LockPool.

  Local Notation ctl := (@ctl C).
  
  Parameter containsThread : t -> tid -> Prop.
  Parameter getThreadC : forall {tid tp}, containsThread tp tid -> ctl.
  Parameter getThreadR : forall {tid tp}, containsThread tp tid -> res.

  Parameter addThread : t -> C -> res -> t.
  Parameter updThreadC : forall {tid tp}, containsThread tp tid -> ctl -> t.
  Parameter updThreadR : forall {tid tp}, containsThread tp tid -> res -> t.
  Parameter updThread : forall {tid tp}, containsThread tp tid -> ctl -> res -> t.
  
  (*Proof Irrelevance of contains*)
  Axiom cnt_irr: forall t tid
                   (cnt1 cnt2: containsThread t tid),
      cnt1 = cnt2.
      
  (* Update properties*)
  Axiom cntUpdateC:
    forall {tid tid0 tp} c
      (cnt: containsThread tp tid),
      containsThread tp tid0->
      containsThread (updThreadC cnt c) tid0.
  Axiom cntUpdateC':
    forall {tid tid0 tp} c
      (cnt: containsThread tp tid),
      containsThread (updThreadC cnt c) tid0 -> 
      containsThread tp tid0. 

  Axiom getThreadUpdateC1:
    forall {tid tp} c
      (cnt: containsThread tp tid)
      (cnt': containsThread (updThreadC cnt c) tid),
      getThreadC cnt' = c.
  
  Axiom getThreadUpdateC2:
    forall {tid tid0 tp} c
      (cnt1: containsThread tp tid)
      (cnt2: containsThread tp tid0)
      (cnt3: containsThread (updThreadC cnt1 c) tid0),
      tid <> tid0 ->
      getThreadC cnt2 = getThreadC cnt3.

  (*Get thread Properties*)
  Axiom gssThreadCode :
    forall {tid tp} (cnt: containsThread tp tid) c' p'
      (cnt': containsThread (updThread cnt c' p') tid), getThreadC cnt' = c'.

  Axiom gssThreadRes:
    forall {tid tp} (cnt: containsThread tp tid) c' p'
      (cnt': containsThread (updThread cnt c' p') tid),
      getThreadR cnt' = p'.

  Axiom gsoThreadRes:
    forall {i j tp} (cnti: containsThread tp i)
            (cntj: containsThread tp j) (Hneq: i <> j) c' p'
            (cntj': containsThread (updThread cnti c' p') j),
    getThreadR cntj' = getThreadR cntj.
  
  Axiom gssThreadCC:
    forall {tid tp} (cnt: containsThread tp tid) c'
      (cnt': containsThread (updThreadC cnt c') tid),
      getThreadC cnt' = c'.

  Axiom gThreadCR:
    forall {i j tp} (cnti: containsThread tp i)
      (cntj: containsThread tp j) c'
      (cntj': containsThread (updThreadC cnti c') j),
      getThreadR cntj' = getThreadR cntj.
  
End ThreadPoolSig.

Module Type ConcurrentMachineSig.
  Declare Module ThreadPool: ThreadPoolSig.
  Import ThreadPool.
  Import SEM.

  Notation thread_pool := ThreadPool.t.
  (** Memories*)
  Parameter richMem: Type.
  Parameter dryMem: richMem -> M.
  
  (** Environment and Threadwise semantics *)
  (** These values come from SEM *)
  (*Parameter G: Type.
  Parameter Sem : CoreSemantics G C mem. *)

  (** The thread pool respects the memory*)
  Parameter mem_compatible: thread_pool -> mem -> Prop.
  Parameter invariant: thread_pool -> Prop.

  (** Step relations *)
  Parameter cstep:
    G -> forall {tid0 ms m},
      containsThread ms tid0 -> mem_compatible ms m -> thread_pool -> mem  -> Prop.

  Parameter conc_call:
    G -> forall {tid0 ms m},
      containsThread ms tid0 -> mem_compatible ms m -> thread_pool -> mem -> Prop.
  
  Parameter threadHalted:
    forall {tid0 ms},
      containsThread ms tid0 -> Prop.

  (*Parameter initial_machine: C -> thread_pool.*)
  
  Parameter init_mach : G -> val -> list val -> option thread_pool.
  
End ConcurrentMachineSig.


Module Type ConcurrentMachine.
  Declare Module SCH: Scheduler.
  Declare Module SIG: ConcurrentMachineSig.

  Import SCH.
  Import SIG.ThreadPool.

  Definition MachState : Type:= (schedule * t)%type.

  Parameter MachineSemantics: schedule -> CoreSemantics SIG.ThreadPool.SEM.G MachState SEM.M.

  Axiom initial_schedule: forall genv main vals U U' c,
      initial_core (MachineSemantics U) genv main vals = Some (U',c) ->
      U' = U.
End ConcurrentMachine.
  
Module CoarseMachine (SCH:Scheduler)(SIG : ConcurrentMachineSig with Module ThreadPool.TID:=SCH.TID) <: ConcurrentMachine with Module SCH:= SCH with Module SIG:= SIG.
  Module SCH:=SCH.
  Module SIG:=SIG.
  Import SCH SIG TID ThreadPool ThreadPool.SEM.
  
  Notation Sch:=schedule.
  Notation machine_state := ThreadPool.t.
  
  (** Resume and Suspend: threads running must be preceded by a Resume
     and followed by Suspend.  This functions wrap the state to
     indicate it's ready to take a syncronisation step or resume
     running. (This keeps the invariant that at most one thread is not
     at_external) *)
  
  Inductive resume_thread': forall {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | ResumeThread: forall tid0 ms ms' c
                    (ctn: containsThread ms tid0)
                    (Hcode: getThreadC ctn = Kresume c)
                    (Hinv: invariant ms)
                    (Hms': updThreadC ctn (Krun c)  = ms'),
      resume_thread' ctn ms'.
  Definition resume_thread: forall {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @resume_thread'.

  Inductive suspend_thread': forall {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | SuspendThread: forall tid0 ms ms' c ef sig args
                     (ctn: containsThread ms tid0)
                     (Hcode: getThreadC ctn = Krun c)
                     (Hat_external: at_external Sem c = Some (ef, sig, args))
                     (Hinv: invariant ms)
                     (Hms': updThreadC ctn (Kstop c) = ms'),
      suspend_thread' ctn ms'.
  Definition suspend_thread : forall {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @suspend_thread'.
  
  Inductive machine_step {genv:G}:
    Sch -> machine_state -> mem -> Sch -> machine_state -> mem -> Prop :=
  | resume_step:
      forall tid U ms ms' m
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: resume_thread Htid ms'),
        machine_step U ms m U ms' m
  | core_step:
      forall tid U ms ms' m m'
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: cstep genv Htid Hcmpt ms' m'),
        machine_step U ms m U ms' m'
  | suspend_step:
      forall tid U U' ms ms' m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep:suspend_thread Htid ms'),
        machine_step U ms m U' ms' m
  | conc_step:
      forall tid U U' ms ms' m m'
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: conc_call genv  Htid Hcmpt ms' m'),
        machine_step U ms m U' ms' m'           
  | step_halted:
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Hhalted: threadHalted Htid),
        machine_step U ms m U' ms m
  | schedfail :
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (Htid: ~ containsThread ms tid)
        (Hinv: invariant ms)
        (HschedS: schedSkip U = U'),        (*Schedule Forward*)
        machine_step U ms m U' ms m.

  Definition MachState: Type := (Sch * machine_state)%type.

  Definition MachStep G (c:MachState) (m:mem) (c' :MachState) (m':mem) :=
    @machine_step  G (fst c) (snd c) m (fst c') (snd c') m'.
  
  Definition at_external (st : MachState)
    : option (external_function * signature * list val) := None.
  
  Definition after_external (ov : option val) (st : MachState) :
    option (MachState) := None.

  (*not clear what the value of halted should be*)
  (*Nick: IMO, the machine should be halted when the schedule is empty.
            The value is probably unimportant? *)
  Definition halted (st : MachState) : option val :=
    match schedPeek (fst st) with
    | Some _ => None
    | _ => Some Vundef
    end.

  Definition init_machine (U:schedule) the_ge (f : val) (args : list val) : option MachState :=
    match init_mach the_ge f args with
    |None => None
    | Some c => Some (U, c)
    end.
  
  Program Definition MachineSemantics (U:schedule):
    CoreSemantics G MachState mem.
  intros.
  apply (@Build_CoreSemantics _ MachState _
                              (init_machine U)
                              at_external
                              after_external
                              halted
                              MachStep
        );
    unfold at_external, halted; try reflexivity.
  intros. inversion H; subst; rewrite HschedN; reflexivity.
  auto.
  Defined.
(*
  Definition MachineSemantics:= MachineSemantics'.*)
  Lemma initial_schedule: forall genv main vals U U' c,
      initial_core (MachineSemantics U) genv main vals = Some (U',c) ->
      U' = U.
        simpl. unfold init_machine. intros.
        destruct (init_mach genv main vals); try solve[inversion H].
        inversion H; reflexivity.
  Qed.
End CoarseMachine.

Module FineMachine  (SCH:Scheduler)(SIG : ConcurrentMachineSig with Module ThreadPool.TID:=SCH.TID) <: ConcurrentMachine with Module SCH:= SCH with Module SIG:= SIG.
  Module SCH:=SCH.
  Module SIG:=SIG.
  Import SCH SIG TID ThreadPool ThreadPool.SEM.
  
  Notation Sch:=schedule.
  Notation machine_state := ThreadPool.t.

  Inductive resume_thread': forall {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | ResumeThread: forall tid0 ms ms' c
                    (ctn: containsThread ms tid0)
                    (HC: getThreadC ctn = Kresume c)
                    (Hms': updThreadC ctn (Krun c)  = ms'),
      resume_thread' ctn ms'.
  Definition resume_thread: forall {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @resume_thread'.

  Inductive suspend_thread': forall {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | SuspendThread: forall tid0 ms ms' c ef sig args
                     (ctn: containsThread ms tid0)
                     (HC: getThreadC ctn = Krun c)
                     (Hat_external: at_external Sem c = Some (ef, sig, args))
                     (Hms': updThreadC ctn (Kstop c)  = ms'),
      suspend_thread' ctn ms'.
  Definition suspend_thread : forall {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @suspend_thread'.
  
  Inductive machine_step {genv:G}:
    Sch -> machine_state -> mem -> Sch -> machine_state -> mem -> Prop :=
  | resume_step:
      forall tid U U' ms ms' m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: resume_thread Htid ms'),
        machine_step U ms m U' ms' m
  | core_step:
      forall tid U U' ms ms' m m'
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: cstep genv Htid Hcmpt ms' m'),
        machine_step U ms m U' ms' m'
  | suspend_step:
      forall tid U U' ms ms' m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: suspend_thread Htid ms'),
        machine_step U ms m U' ms' m
  | conc_step:
      forall tid U U' ms ms' m m'
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: conc_call genv Htid Hcmpt ms' m'),
        machine_step U ms m U' ms' m'           
  | step_halted:
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Hhalted: threadHalted Htid),
        machine_step U ms m U' ms m
  | schedfail :
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: ~ containsThread ms tid),
        machine_step U ms m U' ms m.

  Definition MachState: Type := (Sch * machine_state)%type.

  Definition MachStep G (c:MachState) (m:mem) (c' :MachState) (m':mem) :=
    @machine_step G (fst c) (snd c) m (fst c') (snd c') m'.

  Definition at_external (st : MachState)
    : option (external_function * signature * list val) := None.
  
  Definition after_external (ov : option val) (st : MachState) :
    option (MachState) := None.
  
  (*not clear what the value of halted should be*)
  Definition halted (st : MachState) : option val := None.
  
  Definition init_machine (U:schedule) the_ge (f : val) (args : list val) : option MachState :=
    match init_mach the_ge f args with
    | None => None
    | Some c => Some (U, c)
    end.
  
  Program Definition MachineSemantics (U:schedule):
    CoreSemantics G MachState mem.
  intros.
  apply (@Build_CoreSemantics _ MachState _
                              (init_machine U)
                              at_external
                              after_external
                              halted
                              MachStep
        );
    unfold at_external, halted; try reflexivity.
  auto.
  Defined.


  Lemma initial_schedule: forall genv main vals U U' c,
      initial_core (MachineSemantics U) genv main vals = Some (U',c) ->
      U' = U.
        simpl. unfold init_machine. intros.
        destruct (init_mach genv main vals); try solve[inversion H].
        inversion H; reflexivity.
  Qed.
End FineMachine.