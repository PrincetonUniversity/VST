From mathcomp.ssreflect Require Import ssreflect seq ssrbool.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.lib.Integers.
Require Import Coq.ZArith.ZArith.
Require Import sepcomp.semantics.
Require Import sepcomp.event_semantics.
Require Import concurrency.permissions.
Require Import concurrency.addressFiniteMap.

Require Import concurrency.scheduler.
Require Import Coq.Program.Program.

Require Import concurrency.safety.

(* This module represents the arguments
   to build a CoreSemantics with 
   compcert mem. This is used by BOTH
   Juicy machine and dry machine. *)
Module Type Semantics.
  Parameter F V : Type.
  Parameter G: Type.
  Parameter C: Type.
  Parameter Sem: EvSem G C.
  Parameter getEnv : G -> Genv.t F V.
End Semantics.

Notation EXIT := 
  (EF_external "EXIT" (mksignature (AST.Tint::nil) None)). 

Notation CREATE_SIG := (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint) cc_default).
Notation CREATE := (EF_external "spawn" CREATE_SIG).

Notation READ := 
  (EF_external "READ"
               (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint) cc_default)).
Notation WRITE := 
  (EF_external "WRITE"
               (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint) cc_default)).

Notation MKLOCK := 
  (EF_external "makelock" (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default)).
Notation FREE_LOCK := 
  (EF_external "freelock" (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default)).

Notation LOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default).
Notation LOCK := (EF_external "acquire" LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default).
Notation UNLOCK := (EF_external "release" UNLOCK_SIG).

Notation block  := Values.block.

Definition b_ofs2address b ofs : address:=
  (b, Int.intval ofs).

Inductive ctl {cT:Type} : Type :=
| Krun : cT -> ctl
| Kblocked : cT -> ctl
| Kresume : cT -> val -> ctl (* Carries the return value. Probably a unit.*)
| Kinit : val -> val -> ctl. (* vals correspond to vf and arg respectively. *)

Definition EqDec: Type -> Type := 
  fun A : Type => forall a a' : A, {a = a'} + {a <> a'}.

Module Type Resources.
  Parameter res : Type.
  Parameter lock_info : Type.
End Resources.

Module Type ThreadPoolSig.
  Declare Module TID: ThreadID.
  Declare Module SEM: Semantics.
  Declare Module RES : Resources.
  
  Import TID.
  Import SEM.
  Import RES.

  Parameter t : Type.

  Local Notation ctl := (@ctl C).
  
  Parameter containsThread : t -> tid -> Prop.
  Parameter getThreadC : forall {tid tp}, containsThread tp tid -> ctl.
  Parameter getThreadR : forall {tid tp}, containsThread tp tid -> res.
  Parameter lockGuts : t -> AMap.t lock_info.  (* Gets the set of locks + their info    *)
  Parameter lockSet : t -> access_map.         (* Gets the permissions for the lock set *)
  Parameter lockRes : t -> address -> option lock_info.
  Parameter addThread : t -> val -> val -> res -> t. (*vals are function pointer and argument respectively. *)
  Parameter updThreadC : forall {tid tp}, containsThread tp tid -> ctl -> t.
  Parameter updThreadR : forall {tid tp}, containsThread tp tid -> res -> t.
  Parameter updThread : forall {tid tp}, containsThread tp tid -> ctl -> res -> t.
  Parameter updLockSet : t -> address -> lock_info -> t.
  Parameter remLockSet : t -> address -> t.
  Parameter latestThread : t -> tid.

  Parameter lr_valid : (address -> option lock_info) -> Prop.

  (* Decidability of containsThread *)
  Axiom containsThread_dec:
    forall i tp, {containsThread tp i} + { ~ containsThread tp i}.
  
  (*Proof Irrelevance of contains*)
  Axiom cnt_irr: forall t tid
                   (cnt1 cnt2: containsThread t tid),
      cnt1 = cnt2.

  (* Add Thread properties*)
  Axiom cntAdd:
    forall {j tp} vf arg p,
      containsThread tp j ->
      containsThread (addThread tp vf arg p) j.

  Axiom cntAdd':
    forall {j tp} vf arg p,
      containsThread (addThread tp vf arg p) j ->
      (containsThread tp j /\ j <> latestThread tp) \/ j = latestThread tp.
  
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

  Axiom cntUpdateR:
    forall {i j tp} r
      (cnti: containsThread tp i),
      containsThread tp j->
      containsThread (updThreadR cnti r) j.
  Axiom cntUpdateR':
    forall {i j tp} r
      (cnti: containsThread tp i),
      containsThread (updThreadR cnti r) j -> 
      containsThread tp j.
  
  Axiom cntUpdate:
    forall {i j tp} c p
      (cnti: containsThread tp i),
      containsThread tp j ->
      containsThread (updThread cnti c p) j.
  Axiom cntUpdate':
    forall {i j tp} c p
      (cnti: containsThread tp i),
      containsThread (updThread cnti c p) j ->
      containsThread tp j.

  Axiom cntUpdateL:
    forall {j tp} add lf,
      containsThread tp j ->
      containsThread (updLockSet tp add lf) j.
  Axiom cntRemoveL:
    forall {j tp} add,
      containsThread tp j ->
      containsThread (remLockSet tp add) j.

  Axiom cntUpdateL':
    forall {j tp} add lf,
      containsThread (updLockSet tp add lf) j ->
      containsThread tp j.
  Axiom cntRemoveL':
    forall {j tp} add,
      containsThread (remLockSet tp add) j ->
      containsThread tp j.

  (*Axiom gssLockPool:
    forall tp ls,
      lockSet (updLockSet tp ls) = ls.*) (*Will change*)

  Axiom gsoThreadLock:
    forall {i tp} c p (cnti: containsThread tp i),
      lockSet (updThread cnti c p) = lockSet tp.

  Axiom gsoThreadCLock:
    forall {i tp} c (cnti: containsThread tp i),
      lockSet (updThreadC cnti c) = lockSet tp.

  Axiom gsoThreadRLock:
    forall {i tp} p (cnti: containsThread tp i),
      lockSet (updThreadR cnti p) = lockSet tp.

  Axiom gsoAddLock:
    forall tp vf arg p,
      lockSet (addThread tp vf arg p) = lockSet tp.

  Axiom gssAddRes:
    forall {tp} vf arg pmap j
      (Heq: j = latestThread tp)
      (cnt': containsThread (addThread tp vf arg pmap) j),
      getThreadR cnt' = pmap.
   
  (*Get thread Properties*)
  Axiom gssThreadCode :
    forall {tid tp} (cnt: containsThread tp tid) c' p'
      (cnt': containsThread (updThread cnt c' p') tid),
      getThreadC cnt' = c'.

  Axiom gsoThreadCode :
    forall {i j tp} (Hneq: i <> j) (cnti: containsThread tp i)
      (cntj: containsThread tp j) c' p'
      (cntj': containsThread (updThread cnti c' p') j),
      getThreadC cntj' = getThreadC cntj.

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

  Axiom gsoThreadCC:
    forall {i j tp} (Hneq: i <> j) (cnti: containsThread tp i)
      (cntj: containsThread tp j) c'
      (cntj': containsThread (updThreadC cnti c') j),
      getThreadC cntj = getThreadC cntj'.

  Axiom getThreadCC:
    forall {tp} i j
      (cnti : containsThread tp i) (cntj : containsThread tp j)
      c' (cntj' : containsThread (updThreadC cnti c') j),
    getThreadC cntj' = if eq_tid_dec i j then c' else getThreadC cntj.

  Axiom gThreadCR:
    forall {i j tp} (cnti: containsThread tp i)
      (cntj: containsThread tp j) c'
      (cntj': containsThread (updThreadC cnti c') j),
      getThreadR cntj' = getThreadR cntj.

  Axiom gThreadRC:
    forall {i j tp} (cnti: containsThread tp i)
      (cntj: containsThread tp j) p
      (cntj': containsThread (updThreadR cnti p) j),
      getThreadC cntj' = getThreadC cntj.

  Axiom gsoThreadCLPool:
    forall {i tp} c (cnti: containsThread tp i) addr,
      lockRes (updThreadC cnti c) addr = lockRes tp addr.

  Axiom gsoThreadLPool:
    forall {i tp} c p (cnti: containsThread tp i) addr,
      lockRes (updThread cnti c p) addr = lockRes tp addr.

  Axiom gsoAddLPool:
    forall tp vf arg p (addr : address),
      lockRes (addThread tp vf arg p) addr = lockRes tp addr.
  
  Axiom gLockSetRes:
    forall {i tp} addr (res : lock_info) (cnti: containsThread tp i)
      (cnti': containsThread (updLockSet tp addr res) i),
      getThreadR cnti' = getThreadR cnti.

  Axiom gLockSetCode:
    forall {i tp} addr (res : lock_info) (cnti: containsThread tp i)
      (cnti': containsThread (updLockSet tp addr res) i),
      getThreadC cnti' = getThreadC cnti.

  Axiom gssLockRes:
    forall tp addr pmap,
      lockRes (updLockSet tp addr pmap) addr = Some pmap.

  Axiom gsoLockRes:
    forall tp addr addr' pmap
      (Hneq: addr <> addr'),
      lockRes (updLockSet tp addr pmap) addr' =
      lockRes tp addr'.

  Axiom gssLockSet:
    forall tp b ofs rmap ofs',
      (ofs <= ofs' < ofs + Z.of_nat lksize.LKSIZE_nat)%Z ->
      (Maps.PMap.get b (lockSet (updLockSet tp (b, ofs) rmap)) ofs') = Some Writable.
    
  Axiom gsoLockSet_1 :
    forall tp b ofs ofs'  pmap
      (Hofs: (ofs' < ofs)%Z \/ (ofs' >= ofs + (Z.of_nat lksize.LKSIZE_nat))%Z),
      (Maps.PMap.get b (lockSet (updLockSet tp (b,ofs) pmap))) ofs' =
      (Maps.PMap.get b (lockSet tp)) ofs'.
  Axiom gsoLockSet_2 :
    forall tp b b' ofs ofs' pmap,
      b <> b' -> 
      (Maps.PMap.get b' (lockSet (updLockSet tp (b,ofs) pmap))) ofs' =
      (Maps.PMap.get b' (lockSet tp)) ofs'.

  Axiom lockSet_updLockSet:
    forall tp i (pf: containsThread tp i) c pmap addr rmap,
      lockSet (updLockSet tp addr rmap) =
      lockSet (updLockSet (updThread pf c pmap) addr rmap).

  Axiom updThread_updThreadC_comm :
    forall tp i j c pmap' c'
      (Hneq: i <> j)
      (cnti : containsThread tp i)
      (cntj : containsThread tp j)
      (cnti': containsThread (updThread cntj c' pmap') i)
      (cntj': containsThread (updThreadC cnti c) j),
      updThreadC cnti' c = updThread cntj' c' pmap'.

 Axiom updThread_comm :
    forall tp i j c pmap c' pmap'
      (Hneq: i <> j)
      (cnti : containsThread tp i)
      (cntj : containsThread tp j)
      (cnti': containsThread (updThread cntj c' pmap') i)
      (cntj': containsThread (updThread cnti c pmap) j),
      updThread cnti' c pmap = updThread cntj' c' pmap'.

 Axiom add_updateC_comm:
   forall tp i vf arg pmap c'
     (cnti: containsThread tp i)
     (cnti': containsThread (addThread tp vf arg pmap) i),
     addThread (updThreadC cnti c') vf arg pmap =
     updThreadC cnti' c'.

 Axiom add_update_comm:
   forall tp i vf arg pmap c' pmap'
     (cnti: containsThread tp i)
     (cnti': containsThread (addThread tp vf arg pmap) i),
     addThread (updThread cnti c' pmap') vf arg pmap =
     updThread cnti' c' pmap'.

 Axiom updThread_lr_valid:
   forall tp i (cnti: containsThread tp i) c' m',
     lr_valid (lockRes tp) ->
     lr_valid (lockRes (updThread cnti c' m')).
   
End ThreadPoolSig.

Module Type EventSig.
  Declare Module TID: ThreadID.
  Import TID.
  
  Inductive sync_event : Type :=
  | release : address -> option (access_map * delta_map) -> sync_event
  | acquire : address -> option (access_map * delta_map) -> sync_event
  | mklock :  address -> sync_event
  | freelock : address -> sync_event
  | spawn : address -> sync_event
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

  Parameter syncStep:
    G -> forall {tid0 ms m},
      containsThread ms tid0 -> mem_compatible ms m ->
      thread_pool -> mem -> sync_event -> Prop.
  
  Parameter threadHalted:
    forall {tid0 ms},
      containsThread ms tid0 -> Prop.

  (*Parameter initial_machine: C -> thread_pool.*)
  
  Parameter init_mach : option RES.res  -> G -> val -> list val -> option thread_pool.
  
End ConcurrentMachineSig.


Module Type ConcurrentMachine.
  Declare Module SCH: Scheduler.
  Declare Module SIG: ConcurrentMachineSig.

  Import SCH.
  Import SIG.ThreadPool.
  Import SIG.Events.

  Notation event_trace := (seq machine_event).
  
  Definition MachState : Type:= (schedule * event_trace * t)%type.

  Parameter MachineSemantics: schedule -> option RES.res ->
                              CoreSemantics SIG.ThreadPool.SEM.G MachState mem.

  Axiom initial_schedule: forall genv main vals U U' p c tr,
      initial_core (MachineSemantics U p) genv main vals = Some (U',tr,c) ->
      U' = U /\ tr = nil.
End ConcurrentMachine.
  
Module CoarseMachine (SCH:Scheduler)(SIG : ConcurrentMachineSig with Module ThreadPool.TID:=SCH.TID with Module Events.TID :=SCH.TID) <: ConcurrentMachine with Module SCH:= SCH with Module SIG:= SIG.
  Module SCH:=SCH.
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

  Inductive start_thread' genv: forall {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | StartThread: forall tid0 ms ms' c_new vf arg
                    (ctn: containsThread ms tid0)
                    (Hcode: getThreadC ctn = Kinit vf arg)
                    (Hinitial: initial_core Sem genv vf (arg::nil) = Some c_new)
                    (Hinv: invariant ms)
                    (Hms': updThreadC ctn (Krun c_new)  = ms'),
      start_thread' genv ctn ms'.
  Definition start_thread genv: forall {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @start_thread' genv.
  Inductive resume_thread': forall {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | ResumeThread: forall tid0 ms ms' c c' X
                    (ctn: containsThread ms tid0)
                    (Hat_external: at_external Sem c = Some X)
                    (Hafter_external: after_external Sem
                                             (Some (Vint Int.zero)) c = Some c')
                    (Hcode: getThreadC ctn = Kresume c Vundef)
                    (Hinv: invariant ms)
                    (Hms': updThreadC ctn (Krun c')  = ms'),
      resume_thread' ctn ms'.
  Definition resume_thread: forall {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @resume_thread'.

  Inductive suspend_thread': forall {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | SuspendThread: forall tid0 ms ms' c X
                     (ctn: containsThread ms tid0)
                     (Hcode: getThreadC ctn = Krun c)
                     (Hat_external: at_external Sem c = Some X)
                     (Hinv: invariant ms)
                     (Hms': updThreadC ctn (Kblocked c) = ms'),
      suspend_thread' ctn ms'.
  Definition suspend_thread : forall {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @suspend_thread'.
  
  Inductive machine_step {genv:G}:
    Sch -> event_trace -> machine_state -> mem -> Sch ->
    event_trace -> machine_state -> mem -> Prop :=
  | start_step:
      forall tid U ms ms' m
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: start_thread genv Htid ms'),
        machine_step U [::] ms m U [::] ms' m
  | resume_step:
      forall tid U ms ms' m
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: resume_thread Htid ms'),
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
        (Htstep:suspend_thread Htid ms'),
        machine_step U [::] ms m U' [::] ms' m
  | sync_step:
      forall tid U U' ms ms' m m' ev 
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: syncStep genv Htid Hcmpt ms' m' ev),
        machine_step U [::] ms m  U' [::] ms' m'           
  | halted_step:
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Hhalted: threadHalted Htid),
        machine_step U [::] ms m  U' [::] ms m
  | schedfail :
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (Htid: ~ containsThread ms tid)
        (Hinv: invariant ms)
        (HschedS: schedSkip U = U'),        (*Schedule Forward*)
        machine_step U [::] ms m U' [::] ms m.

  Definition MachState: Type := (Sch * event_trace * machine_state)%type.

  Definition MachStep G (c:MachState) (m:mem)
             (c' :MachState) (m':mem) :=
    @machine_step G (fst (fst c)) (snd (fst c)) (snd c)  m
                  (fst (fst c')) (snd (fst c')) (snd c')  m'.
  
  Definition at_external (st : MachState)
    : option (external_function * signature * list val) := None.
  
  Definition after_external (ov : option val) (st : MachState) :
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

  Definition init_machine (U:schedule) (r : option RES.res) the_ge
             (f : val) (args : list val)
    : option MachState :=
    match init_mach r the_ge f args with
    | None => None
    | Some c => Some (U, [::], c)
    end.
  
  Program Definition MachineSemantics (U:schedule) (r : option RES.res):
    CoreSemantics G MachState mem.
  intros.
  apply (@Build_CoreSemantics _ MachState _
                              (init_machine U r)
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
  Lemma initial_schedule: forall genv main vals U U' p c tr,
      initial_core (MachineSemantics U p) genv main vals = Some (U',tr,c) ->
      U' = U /\ tr = nil.
        simpl. unfold init_machine. intros.
        destruct (init_mach p genv main vals); try solve[inversion H].
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

  Section new_safety.
  (** *I create a new type of safety that satisfies (forall n, safeN) -> safe and is preserved by simulations. *)
    
    Inductive sem_with_halt ge: MachState -> mem -> MachState -> mem -> Prop:=
    | halt_with_step st m: halted st -> sem_with_halt ge st m st m
    | step_with_halt st m st' m' : MachStep ge st m st' m' -> sem_with_halt ge st m st' m'.
    
  Definition new_state: Type:= seq machine_event * machine_state * mem.
  Definition mk_nstate (st:MachState) m:new_state:= (snd (fst st), snd st, m).
  Definition mk_ostate (st:new_state) U:MachState:= (U, fst (fst st), snd (fst st)).
  Definition new_step ge (st: new_state) U st' U': Prop:=
    sem_with_halt ge (mk_ostate st U) (snd st) (mk_ostate st' U') (snd st').
  (*This has to be filled in:*)
  Axiom valid: MachState -> bool.
  Definition new_valid st U := valid (mk_ostate st U). 
  Definition ksafe_new_step (ge : G) (st : MachState) (m : mem) : nat -> Prop :=
    ksafe _ _ (new_step ge) new_valid (mk_nstate st m) (fst (fst st)).
  Definition safe_new_step (ge : G) (st : MachState) (m : mem) : Prop :=
    safe _ _ (new_step ge) new_valid (mk_nstate st m) (fst (fst st)).

  (*Things that we must prove:*)
  Axiom sch_dec: forall (U U': Sch), {U = U'} + {U <> U'}.
  Axiom step_sch: forall {ge U tr tp m U' tr' tp' m'}, MachStep ge (U, tr, tp) m (U', tr', tp') m' -> {U=U'}+{schedSkip(U)=U'}.
  Axiom step_trace: forall {ge U tr tp m U' tr' tp' m'}, MachStep ge (U, tr, tp) m (U', tr', tp') m' -> nil = tr'. 
  Axiom step_valid: forall {ge st m st' m'}, MachStep ge st m st' m'  -> valid st -> valid st'. 
  Axiom step_sch_valid: forall {ge U tr tp m U' tr' tp' m'}, MachStep ge (U, tr, tp) m (U', tr', tp') m' -> U<>U' -> forall U'', valid (U'', tr', tp').
  Axiom skip_not_eq: forall U, U <> schedSkip U.
  Lemma safety_equivalence':
    forall ge st_ m,
      (forall U n, new_valid (nil, st_, m) U -> ksafe_new_step ge (U, nil, st_) m n) ->
      (forall U n, valid (U, nil, st_) ->  csafe ge (U, nil, st_) m n).
  Proof.
    move=> ge st_ m KSF' U n VAL.
    assert (KSF: forall U, new_valid (nil, st_, m) U -> ksafe_new_step ge (U, nil, st_) m n) by (move=> U'' NV; apply: KSF'=>// ).
    clear KSF'.
    assert (VAL_: new_valid (nil, st_, m) U) by rewrite /new_valid /mk_ostate /= //. clear VAL.
    (*move: VAL_=> /(KSF _ n) KSF_new.*)
    move: st_ m KSF U VAL_.
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
              apply: (step_valid H) =>//.
          }
        * subst U'. apply: (AngelSafe _ _ _ (snd (fst st')) (snd st'))=>//.
          move=>U''.
          { destruct st' as [[tr' tp'] m'] => /=; eapply IHn.
            - move => U0 nVAL0. rewrite /ksafe_new_step /mk_nstate=> /=.
              simpl in HH; rewrite -HH in H1.
              by apply: H1. 
            - rewrite /new_valid /mk_ostate=> /=. simpl in H.
              apply (step_sch_valid H).
                by apply: skip_not_eq.
          }
  Qed.
        
  Lemma safety_equivalence:
    forall ge tp m,
      (forall U, new_valid (nil, tp, m) U) ->
      (forall n U, ksafe_new_step ge (U, nil, tp) m n) ->
      (forall n U, csafe ge (U, nil, tp) m n).
  Proof. by move => ? ? ? H ? ? ?; apply: safety_equivalence'; try apply: H. Qed.
  
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

Module FineMachine  (SCH:Scheduler)(SIG : ConcurrentMachineSig with Module ThreadPool.TID:=SCH.TID with Module Events.TID:=SCH.TID)<: ConcurrentMachine with Module SCH:= SCH with Module SIG:= SIG.
  Module SCH:=SCH.
  Module SIG:=SIG.
  Import SCH SIG TID ThreadPool ThreadPool.SEM Events.
  
  Notation Sch:=schedule.
  Notation machine_state := ThreadPool.t.
  Notation event_trace := (seq machine_event).

  Inductive start_thread' genv: forall {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | StartThread: forall tid0 ms ms' c_new vf arg
                   (ctn: containsThread ms tid0)
                   (Hcode: getThreadC ctn = Kinit vf arg)
                   (Hinitial: initial_core Sem genv vf (arg::nil) = Some c_new)
                   (Hinv: invariant ms)
                   (Hms': updThreadC ctn (Krun c_new)  = ms'),
      start_thread' genv ctn ms'.
  Definition start_thread genv: forall {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @start_thread' genv.
  
  Inductive resume_thread': forall {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | ResumeThread: forall tid0 ms ms' c c' X
                    (ctn: containsThread ms tid0)
                    (Hat_external: at_external Sem c = Some X)
                    (Hafter_external:
                       after_external Sem
                                      (Some (Vint Int.zero)) c = Some c')
                    (Hcode: getThreadC ctn = Kresume c Vundef)
                    (Hinv: invariant ms)
                    (Hms': updThreadC ctn (Krun c')  = ms'),
      resume_thread' ctn ms'.
  Definition resume_thread: forall {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @resume_thread'.

  Inductive suspend_thread': forall {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | SuspendThread: forall tid0 ms ms' c X
                     (ctn: containsThread ms tid0)
                     (Hcode: getThreadC ctn = Krun c)
                     (Hat_external: at_external Sem c = Some X)
                     (Hinv: invariant ms)
                     (Hms': updThreadC ctn (Kblocked c) = ms'),
      suspend_thread' ctn ms'.
  Definition suspend_thread : forall {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @suspend_thread'.
  
  Inductive machine_step {genv:G}:
    Sch -> event_trace -> machine_state -> mem -> Sch
    -> event_trace -> machine_state -> mem -> Prop :=
  | start_step:
      forall tid U U' ms ms' m tr
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: start_thread genv Htid ms'),
        machine_step U tr ms m U' tr ms' m
  | resume_step:
      forall tid U U' ms ms' m tr
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: resume_thread Htid ms'),
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
        (Htstep: suspend_thread Htid ms'),
        machine_step U tr ms m U' tr ms' m
  | sync_step:
      forall tid U U' ms ms' m m' tr ev
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: syncStep genv Htid Hcmpt ms' m' ev),
        machine_step U tr ms m U' (tr ++ [:: external tid ev]) ms' m'           
  | halted_step:
      forall tid U U' ms m tr
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Hhalted: threadHalted Htid),
        machine_step U tr ms m U' tr ms m
  | schedfail :
      forall tid U U' ms m tr
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: ~ containsThread ms tid),
        machine_step U tr ms m U' tr ms m.

  Definition MachState: Type := (Sch * event_trace * machine_state)%type.

  Definition MachStep G (c:MachState) (m:mem)
             (c' :MachState) (m':mem) :=
    @machine_step G (fst (fst c)) (snd (fst c)) (snd c)  m
                  (fst (fst c')) (snd (fst c')) (snd c')  m'.

  Definition at_external (st : MachState)
    : option (external_function * signature * list val) := None.
  
  Definition after_external (ov : option val) (st : MachState) :
    option (MachState) := None.
  
  Definition halted (st : MachState) : option val :=
    match schedPeek (fst (fst st)) with
    | Some _ => None
    | _ => Some Vundef
    end.
  
  Definition init_machine (U:schedule) (p : option RES.res) the_ge
             (f : val) (args : list val) : option MachState :=
    match init_mach p the_ge f args with
    | None => None
    | Some c => Some (U, [::],c)
    end.
  
  Program Definition MachineSemantics (U:schedule) (p : option RES.res):
    CoreSemantics G MachState mem.
  intros.
  apply (@Build_CoreSemantics _ MachState _
                              (init_machine U p)
                              at_external
                              after_external
                              halted
                              MachStep
        );
    unfold at_external, halted; try reflexivity.
  intros. inversion H; subst; rewrite HschedN; reflexivity.
  auto.
  Defined.


  Lemma initial_schedule: forall genv main vals U U' p c tr,
      initial_core (MachineSemantics U p) genv main vals = Some (U',tr,c) ->
      U' = U /\ tr = nil.
        simpl. unfold init_machine. intros.
        destruct (init_mach p genv main vals); try solve[inversion H].
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
footprints of permissions moved to the thread when applicable*)
 Inductive sync_event : Type :=
  | release : address -> option (access_map * delta_map) -> sync_event
  | acquire : address -> option (access_map * delta_map) -> sync_event
  | mklock :  address -> sync_event
  | freelock : address -> sync_event
  | spawn : address -> sync_event
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
      | spawn _ => Spawn
      end
    end.
  
  Definition location ev : option (address*nat) :=
    match ev with
    | internal _ mev =>
      match mev with
      | event_semantics.Write b ofs vs => Some ((b, ofs), size vs)
      | event_semantics.Read b ofs _ vs => Some ((b, ofs), size vs)
      | _ => None
      end 
    | external _ sev =>
      match sev with
      | release addr _ => Some (addr, lksize.LKSIZE_nat)
      | acquire addr _ => Some (addr, lksize.LKSIZE_nat)
      | mklock addr => Some (addr, lksize.LKSIZE_nat)
      | freelock addr => Some (addr, lksize.LKSIZE_nat)
      | spawn addr => Some (addr, lksize.LKSIZE_nat)
      | failacq addr => Some (addr, lksize.LKSIZE_nat)
      end
    end.

  Definition resources ev : option (access_map * delta_map) :=
    match ev with
    | external _ mev =>
      match mev with
      | release _ res => res
      | acquire _ res => res
      | _ => None
      end
    | _ => None
    end.
  
End Events.