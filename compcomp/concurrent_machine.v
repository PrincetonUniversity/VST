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


Notation EXIT := 
  (EF_external 1%positive (mksignature (AST.Tint::nil) None)). 

Notation CREATE_SIG := (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint)).
Notation CREATE := (EF_external 2%positive CREATE_SIG).

Notation READ := 
  (EF_external 3%positive 
               (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).
Notation WRITE := 
  (EF_external 4%positive 
               (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).

Notation MKLOCK := 
  (EF_external 5%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).
Notation FREE_LOCK := 
  (EF_external 6%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).

Notation LOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).
Notation LOCK := (EF_external 7%positive LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).
Notation UNLOCK := (EF_external 8%positive UNLOCK_SIG).


Notation access_map := (Maps.PMap.t (Z -> option permission)).
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
  Parameter Sem : CoreSemantics G cT richMem.

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
                              (nat -> access_map) -> (*ANGEL! *)
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
  Variable aggelos: nat -> access_map.
  Inductive machine_step {genv:G}: Sch -> machine_state -> mem -> Sch -> machine_state -> mem -> Prop :=
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
  Definition MachStep G (c:MachState) (m:mem)  (c' :MachState) (m':mem) :=
    @machine_step G (fst c) (snd c) m (fst c') (snd c) m'.

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
  
  Program Definition MachineSemantics: CoreSemantics G MachState mem.
  apply (@Build_CoreSemantics _ MachState _
                              init_machine 
                              at_external
                              after_external
                              halted
                              MachStep
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
  Variable aggelos: nat -> access_map.
  Inductive machine_step {genv:G}: Sch -> machine_state -> mem -> Sch -> machine_state -> mem -> Prop :=
  | resume_step:
      forall tid U U' ms ms' m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m),
        resume_thread Htid ms' ->
        machine_step U ms m U ms' m
  | core_step:
      forall tid U U' ms ms' m m'
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
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
  Definition MachStep G (c:MachState) (m:mem)  (c' :MachState) (m':mem) :=
    @machine_step G (fst c) (snd c) m (fst c') (snd c) m'.

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
  
  Program Definition MachineSemantics: CoreSemantics G MachState mem.
  apply (@Build_CoreSemantics _ MachState _
                              init_machine 
                              at_external
                              after_external
                              halted
                              MachStep
        );
    unfold at_external, halted; try reflexivity.
  auto.
  Defined.

End FineMachine.