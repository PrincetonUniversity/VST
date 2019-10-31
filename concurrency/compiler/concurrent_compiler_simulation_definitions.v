Require Import Omega.

Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.ExposedSimulations.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Require Import VST.concurrency.lib.tactics.
Require Import VST.concurrency.common.permissions. Import permissions.
Require Import VST.concurrency.common.semantics. 
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.CoreSemantics_sum.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.compiler.HybridMachine_simulation.

Require Import VST.concurrency.compiler.Clight_self_simulation.
Require Import VST.concurrency.compiler.Asm_self_simulation.
Require Import VST.concurrency.compiler.diagrams.
Require Import VST.concurrency.compiler.mem_equiv.
Require Import VST.concurrency.compiler.pair.


Require Import VST.concurrency.memsem_lemmas.
Import BinNums.
Import BinInt.
Import List.
Import Integers.
Import Ptrofs.
Import Basics.
Import FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.

Instance inject_delta_map_monotonic:
  Inject_Monotonic Events.inject_delta_map.
Proof.
  intros ??????.
Admitted.

(** *One thread simulation*)
Module Type ThreadSimulationArguments.

  Export X86Context.
  Parameter C_program: Clight.program.
  Parameter Asm_program: Asm.program.
  Definition Asm_g := (@the_ge Asm_program).
  Parameter Asm_genv_safe: Asm_core.safe_genv (@the_ge Asm_program).
    
End ThreadSimulationArguments.


Module ThreadSimulationDefinitions
       (CC_correct: CompCert_correctness)
       (Args: ThreadSimulationArguments).

  Import HybridMachineSig.
  Import DryHybridMachine.
  Import self_simulation.
  Export Args.

  (* Bellow are things taken from ThreadSimulation*)

  (* Assumption of compilation. *)
  Parameter compiled: 
    CC_correct.CompCert_compiler C_program = Some Asm_program.
  
  
    Notation sem_coresem Sem:=
    (semantics.csem (event_semantics.msem (@semSem Sem))).

    
    (** *C Semantics*)
    Definition Clight_g : Clight.genv := Clight.globalenv C_program.
    Definition CSem : Semantics := ClightSemanticsForMachines.ClightSem Clight_g.
    Definition CoreCSem:= (sem_coresem CSem).
    
    Definition Cself_simulation := clight_self_simulation Clight_g.
    Definition Clight_code_inject := self_simulation.code_inject _ _ Cself_simulation.
    Definition Clight_match := self_simulation.match_self Clight_code_inject.
    
    (** *Asm Semantics*)
    (*Import the Asm Hybrid Machine*)
    Definition Aself_simulation := Asm_self_simulation Asm_g.
    Definition Asm_code_inject := self_simulation.code_inject _ _ Aself_simulation.
    Definition Asm_match := self_simulation.match_self Asm_code_inject.

    
    (** *AsHybrid Semantics and Machine*)
    Definition AsmSem : Semantics := @X86Sem Asm_program Asm_genv_safe.
    Definition CoreAsmSem:= (sem_coresem AsmSem).

    
    (** The hybrid semantics*)
    Instance HybridSem h : Semantics := CoreSem_Sum h CSem AsmSem.
    Existing Instance dryResources.
    Notation TP h := (threadPool.OrdinalPool.OrdinalThreadPool
                        (resources:=dryResources)(Sem:=HybridSem h)).
    Existing Instance DryHybridMachineSig.
    Definition HybMachine h:=
      HybridMachineSig.HybridCoarseMachine.HybridCoarseMachine
        (ThreadPool:= TP h).
    Definition HybConcSem h:=
      HybridMachineSig.ConcurMachineSemantics(HybridMachine:=HybMachine h).
    Notation ThreadPool n :=
      (ThreadPool.t(Sem:= HybridSem n)).


    (** *Extracting index and match relation from CompCert*)
    Definition compiler_sim:= CC_correct.simpl_clight_semantic_preservation _ _ compiled.
    Definition compiler_index: Type:= InjindexX compiler_sim.
    Definition compiler_match (i:compiler_index) (j:meminj)
               (c1:  Smallstep.state (Smallstep.part_sem (Clight.semantics2 C_program)))
               (m1: mem)
               (c2: Smallstep.state (Asm.part_semantics Asm_g))
               (m2: mem): Prop
      := Injmatch_statesX compiler_sim i j
                          (Smallstep.set_mem c1 m1)
                          (Smallstep.set_mem c2 m2).

    (* Compiler match that holds under interference of other threads. *)
    Inductive compiler_match_padded:
      compiler_index -> meminj ->
      Smallstep.state (Smallstep.part_sem (Clight.semantics2 C_program)) ->
      mem -> Smallstep.state (Asm.part_semantics Asm_g) -> mem -> Prop
      :=
      | BuildCompilerMatch: forall cd j1 j2 j3 j s1 m1 s2 m2 s3 m3 s4 m4,
          Clight_match j1 s1 m1 s2 m2 ->
          compiler_match cd j2 s2 m2 s3 m3 ->
          Asm_match j3 s3 m3 s4 m4 ->
          compose_meminj (compose_meminj j1 j2) j3 = j ->
          compiler_match_padded cd j s1 m1 s4 m4.

    (* When the compiling thread is at Kresume the match is different:
     The memories have change according to the synchronization operation
     but the thread state has not resumed (taken the external step, according
     to the CompCert semantics). So, when the state is at Kresume the match
     states that there will be a match, when the states change:
     "When the source thread steps, the target thread will be able to step 
     and reestablish the match"
     This is also padded above and bellow as in compiler_match_padded.
     *)

    (* generalize None to option val and inject it. *)
    Inductive compiler_match_resume:
      compiler_index -> meminj ->
      Smallstep.state (Smallstep.part_sem (Clight.semantics2 C_program)) ->
      mem -> Smallstep.state (Asm.part_semantics Asm_g) -> mem -> Prop
      :=
      | BuildCompilerResumeMatch: forall cd j s2 m2 s3 m3,
          (forall s2', Smallstep.after_external
                    (Smallstep.part_sem (Clight.semantics2 C_program))
                    None s2 m2 = Some s2' ->
                  exists s3',
                    (Smallstep.after_external
                       (Asm.part_semantics Asm_g)
                       None s3 m3 = Some s3') /\
                    compiler_match cd j s2' (Smallstep.get_mem s2') s3' (Smallstep.get_mem s3')) ->
          compiler_match_resume  cd j s2 m2 s3 m3.
    
    Inductive compiler_match_resume_padded:
      compiler_index -> meminj -> Smallstep.state (Smallstep.part_sem (Clight.semantics2 C_program)) ->
      mem -> Smallstep.state (Asm.part_semantics Asm_g) -> mem -> Prop
      :=
      | BuildCompilerResumeMatchPadded:
          forall cd j1 j2 j3 j s1 m1 s2 m2 s3 m3 s4 m4,
            Clight_match j1 s1 m1 s2 m2 ->
            compiler_match_resume cd j2 s2 m2 s3 m3 ->
            Asm_match j3 s3 m3 s4 m4 ->
            compose_meminj (compose_meminj j1 j2) j3 = j ->
            compiler_match_resume_padded cd j s1 m1 s4 m4.
  
End ThreadSimulationDefinitions.



(*Useful stuff: *)

(* These make clean_cnt and clean proof stronger.*)
Ltac abstract_cnt:= abstract_proofs of (OrdinalPool.containsThread _ _).
Ltac abstract_permMapLt:= abstract_proofs of (permMapLt _ _).