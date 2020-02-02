Require Import VST.concurrency.main_definitions.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_definitions.
Import Memory.Mem.

(*PROOFs*)
Require Import VST.concurrency.main_proofs.

(*
Module CC_correct: CompCert_correctness.
  Axiom CompCert_compiler : Clight.program -> option Asm.program.
  Axiom simpl_clight_semantic_preservation :
    forall (p : Clight.program) (tp : Asm.program),
      CompCert_compiler p = Some tp ->
      ExposedSimulations.fsim_properties_inj_relaxed (Clight.semantics2 p) (Asm.semantics tp)
                                             Clight.get_mem Asm.get_mem.

End CC_correct.

Module ProgramArgs: ThreadSimulationArguments.

  Parameter C_program: Clight.program.
  Parameter Asm_program: Asm.program.
  Definition Asm_g := (@x86_context.X86Context.the_ge Asm_program).
  Parameter Asm_genv_safe: Asm_core.safe_genv Asm_g.
    
End ProgramArgs.*)

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
  
  (* We want to prove something like this. Maybe with extra assumptions, 
     or (probably) the convers. In the end we want to unify the two predicates. *)
  (* Lemma entry_point_problem:
    forall src_m src_cpm1 src_cpm2,
      Clight.entry_point
        (Clight.globalenv C_program) src_m src_cpm1 (main_ptr C_program) nil ->
      CSL_init_setup C_program src_m src_cpm2 -> src_cpm1 = src_cpm2.
  Proof.
    intros * H1  H2.
    inversion H1; inversion H2; subst.
    unfold Clight_init_state; simpl.
    (* The two ways of getting an initial state:
         LHS -  Clight_init_state, how the CSL proof defines initial states
         RHS -  Clight.entry_point our new way of defining initial states 
                (entry points)
     *)
    rename f into f_main2.
    - admit.
  Admitted. *)
      

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

(*Module Test_Main:= (MainTheorem CC_correct ProgramArgs).
Import Test_Main.
*)
Check top2bottom_correct.
Print Assumptions top2bottom_correct.
