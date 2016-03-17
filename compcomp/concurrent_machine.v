Require Import Memory.
Require Import AST.     (*for typ*)
Require Import Values. (*for val*)
Require Import Globalenvs. 
Require Import Integers.
Require Import ZArith.
Require Import core_semantics.
Load Scheduler.

Require Import Program.
Require Import ssreflect Ssreflect.seq.


Add LoadPath "../compcomp" as compcomp.
Require Import permissions.

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

Module Type ConcurrentMachineSig (TID: ThreadID).
  Import TID.
  
  (*Memories*)
  Parameter richMem: Type.
  Parameter dryMem: richMem -> mem.
  
  (*CODE*)
  Parameter cT: Type.
  Parameter G: Type.
  Parameter Sem : CoreSemantics G cT mem. (* Not used, might remove. *)

  (*MACHINE VARIABLES*)
  Parameter machine_state: Type.
  Parameter containsThread: machine_state -> tid -> Prop.
  Parameter lp_id : tid. (*lock pool thread id*)


  (*INVARIANTS*)
  (*The state respects the memory*)
  Parameter mem_compatible: machine_state -> mem -> Prop.
  
  (*Steps*)
  Parameter cstep: G -> forall {tid0 ms m},
                         containsThread ms tid0 -> mem_compatible ms m -> machine_state -> mem  -> Prop.
  Parameter resume_thread: forall {tid0 ms},
                             containsThread ms tid0 -> machine_state -> Prop.
  Parameter suspend_thread: forall {tid0 ms},
                              containsThread ms tid0 -> machine_state -> Prop.
  Parameter conc_call: G ->  forall {tid0 ms m},
                              (nat -> delta_map) -> (*ANGEL! *)
                              containsThread ms tid0 -> mem_compatible ms m -> machine_state -> mem -> Prop.
  
  Parameter threadHalted: forall {tid0 ms},
                            containsThread ms tid0 -> Prop.

  Parameter init_core : G -> val -> list val -> option machine_state.
  
End ConcurrentMachineSig.


Module CoarseMachine (TID: ThreadID)(SCH:Scheduler TID)(SIG : ConcurrentMachineSig TID).
  Import TID.
  Import SIG.
  Import SCH.
  
  Notation Sch:=schedule.
  Inductive machine_step {aggelos: nat -> delta_map} {genv:G}:
    Sch -> machine_state -> mem -> Sch -> machine_state -> mem -> Prop :=
  | resume_step:
      forall tid U ms ms' m
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m),
        resume_thread Htid ms' ->
        machine_step U ms m U ms' m
  | core_step:
      forall tid U ms ms' m m'
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m),
        cstep genv Htid Hcmpt ms' m' ->
        machine_step U ms m U ms' m'
  | suspend_step:
      forall tid U U' ms ms' m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m),
        suspend_thread Htid ms' ->
        machine_step U ms m U' ms' m
  | conc_step:
      forall tid U U' ms ms' m m'
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Hconc: conc_call genv aggelos Htid Hcmpt ms' m'),
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
        (HschedS: schedSkip U = U'),        (*Schedule Forward*)
        machine_step U ms m U' ms m.

  Definition MachState: Type := (Sch * machine_state)%type.

  Definition MachStep (aggelos : nat -> delta_map) G (c:MachState) (m:mem) (c' :MachState) (m':mem) :=
    @machine_step aggelos G (fst c) (snd c) m (fst c') (snd c) m'.
    

    Definition at_external (st : MachState)
    : option (external_function * signature * list val) := None.
  
    Definition after_external (ov : option val) (st : MachState) :
      option (MachState) := None.

  (*not clear what the value of halted should be*)
  Definition halted (st : MachState) : option val := None.

  Variable U: Sch.
  Definition init_machine the_ge (f : val) (args : list val) : option MachState :=
    match init_core the_ge f args with
      |None => None
      | Some c => Some (U, c)
    end.
  
  Program Definition MachineSemantics (aggelos:nat -> delta_map) :
    CoreSemantics G MachState mem.
  intros.
  apply (@Build_CoreSemantics _ MachState _
                              init_machine 
                              at_external
                              after_external
                              halted
                              (MachStep aggelos)
        );
    unfold at_external, halted; try reflexivity.
  auto.
  Defined.
  
End CoarseMachine.

Module FineMachine (TID: ThreadID)(SCH:Scheduler TID)(SIG : ConcurrentMachineSig TID).
  Import TID.
  Import SIG.
  Import SCH.
  
  Notation Sch:=schedule.
  Inductive machine_step {aggelos : nat -> delta_map} {genv:G}:
    Sch -> machine_state -> mem -> Sch -> machine_state -> mem -> Prop :=
  | resume_step:
      forall tid U U' ms ms' m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m),
        resume_thread Htid ms' ->
        machine_step U ms m U' ms' m
  | core_step:
      forall tid U U' ms ms' m m'
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m),
        cstep genv Htid Hcmpt ms' m' ->
        machine_step U ms m U' ms' m'
  | suspend_step:
      forall tid U U' ms ms' m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m),
        suspend_thread Htid ms' ->
        machine_step U ms m U' ms' m
  | conc_step:
      forall tid U U' ms ms' m m'
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Hconc: conc_call genv aggelos Htid Hcmpt ms' m'),
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

    Definition MachStep aggelos G (c:MachState) (m:mem)  (c' :MachState) (m':mem) :=
      @machine_step aggelos G (fst c) (snd c) m (fst c') (snd c) m'.

    Definition at_external (st : MachState)
    : option (external_function * signature * list val) := None.
    
    Definition after_external (ov : option val) (st : MachState) :
      option (MachState) := None.
    
  (*not clear what the value of halted should be*)
    Definition halted (st : MachState) : option val := None.
    
    Variable U: Sch.
    Definition init_machine the_ge (f : val) (args : list val) : option MachState :=
      match init_core the_ge f args with
      | None => None
      | Some c => Some (U, c)
      end.
    
    Program Definition MachineSemantics (aggelos : nat -> delta_map):
      CoreSemantics G MachState mem.
    intros.
    apply (@Build_CoreSemantics _ MachState _
                                init_machine 
                              at_external
                              after_external
                              halted
                              (MachStep aggelos)
          );
      unfold at_external, halted; try reflexivity.
    auto.
    Defined.

End FineMachine.