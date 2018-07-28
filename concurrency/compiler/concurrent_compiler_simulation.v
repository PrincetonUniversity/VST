(* Concurrent Compiler Correcntess *)

(** Prove a simulation between the Clight concurrent semantics and 
    the x86 concurrent semantics.
*)

Require Import VST.concurrency.compiler.HybridMachine_simulation.

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.


Section ConcurrentCopmpilerSpecification.
  (*Import the Clight Hybrid Machine*)
  Import ClightMachine.
  Import DMS.  
  (*Import the Asm X86 Hybrid Machine*)
  Import X86Context.

  (*Import the Asm Hybrid Machine*)
  Context (Clight_g : Clight.genv).
  Context (Asm_g : Clight.genv).
  Context (Asm_program: Asm.program).
  Context (Asm_genv_safe: Asm_core.safe_genv (@the_ge Asm_program)).

  Variable opt_init_mem_source: option Memory.Mem.mem.
  Variable opt_init_mem_target: option Memory.Mem.mem.
  Definition ConcurrentCompilerCorrectness_specification: Type:=
    HybridMachine_simulation (ClightConcurSem(ge:=Clight_g) opt_init_mem_source) (@AsmConcurSem Asm_program Asm_genv_safe opt_init_mem_target).


End ConcurrentCopmpilerSpecification.
