
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import VST.concurrency.paco.src.paco.

Require Import VST.concurrency.common.HybridMachineSig.
Import HybridMachineSig.
Set Bullet Behavior "Strict Subproofs".
  
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.concurrent_compiler_safety.
Require Import VST.concurrency.compiler.safety_equivalence.
Require Import VST.concurrency.compiler.HybridMachine_simulation.
Require Import VST.concurrency.common.HybridMachine.
Require Import Omega.
            

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.

(*Concurrent_Safety*)
Module SafetyStatement (CC_correct: CompCert_correctness).
  (*Import the Clight Hybrid Machine*)
  Import ClightMachine.
  Import DMS.
  (*Import the Asm X86 Hybrid Machine*)
  Import X86Context.

  Definition Clight_init_state (p: Clight.program):=
    Clight.start_stack (Clight.globalenv p).

  Definition Asm_init_state (p: Asm.program):=
    Asm.start_stack (@the_ge p).

  Notation valid Sem:=
    (valid dryResources Sem OrdinalPool.OrdinalThreadPool).

    Definition ConcurrentCompilerSafety_statement:=
      forall (p : Clight.program) (tp : Asm.program),
        CC_correct.CompCert_compiler p = Some tp ->
        forall asm_genv_safety : Asm_core.safe_genv (@the_ge tp),
          let SemSource:= (ClightSemanticsForMachines.ClightSem (Clight.globalenv p)) in
          let SemTarget:= @X86Sem tp asm_genv_safety in
          concurrent_simulation_safety_preservation
            (Genv.init_mem (Ctypes.program_of_program p))
            (Genv.init_mem tp)
            (SemSource:= SemSource)
            (SourceThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemSource))
            (SourceMachineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
            (SemTarget :=  SemTarget)
            (TargetThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
            (TargetMachineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    .
    
End SafetyStatement.
