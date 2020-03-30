Require Import VST.concurrency.main_definitions.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_definitions.
Import Memory.Mem.

(*PROOFs*)
Require Import VST.concurrency.main_proofs.

Section MainTheorem.
         Context {CC_correct: CompCert_correctness}
          {Args: ThreadSimulationArguments}.
  (*Import CC_correct Args.
  Module Theorem_proofs:=Main CC_correct Args.
  Import Theorem_proofs. *)
  
  Section Temporary_to_see_inconsistency.
    (*Initial states are inconsistent.
      Here is how
     *)
  Import Clight.

      (* End of temporary exposition *)
  Goal True.
    idtac "Delete until here". auto. Qed.
  End Temporary_to_see_inconsistency.
  
  Notation CPM:=ThreadPool.t.
  Theorem top2bottom_correct:
      (* C program is proven to be safe in CSL*)
      forall (main:AST.ident), CSL_correct C_program main ->

      (* C program compiles to some assembly program*)
      CompCert_compiler C_program = Some Asm_program ->
        
      (* Static scheck initial memories *)
      check_initial_mems C_program Asm_program ->
      
      (* Statically checkable properties of ASM program *)
      forall (STATIC: static_validation Asm_program main),

      (* For all schedules, *)
      forall U : schedule,
        
      (*The asm program can be initialized with a memory and CPM state*)
      exists (tgt_m : mem) (tgt_cpm:CPM),
        @initial_state Asm_program STATIC tgt_cpm tgt_m /\
        
        (* The assembly language program 
         is correct  and well-synchronized  *)
        spinlock_safe U tgt_cpm tgt_m.
    Proof. eapply main_safety_clean. Qed.
End MainTheorem.
