(***********
 This file sets the defintions for the main theorem with explanations
 *************)

Require Import compcert.cfrontend.Ctypes.
Require Import compcert.x86.Asm.
Require Import compcert.cfrontend.Clight.

Require Import VST.concurrency.juicy.semax_to_juicy_machine.
Require Import VST.concurrency.juicy.Clight_safety.
Require Import VST.concurrency.sc_drf.mem_obs_eq.
Require Import VST.concurrency.sc_drf.x86_inj.
Require Import VST.concurrency.sc_drf.executions.
Require Import VST.concurrency.sc_drf.spinlocks.



Export Integers.Ptrofs Values Globalenvs.
Export threadPool semantics.
Export CoreInjections dry_context AsmContext.
Export HybridMachineSig.HybridMachineSig HybridFineMachine erased_machine.
Export BareMachine.
Export semax_to_juicy_machine.
Import x86_context.X86Context Asm_core.

Definition permissionless_concursem (SemTarget : Semantics) m:=
    (HybridMachineSig.HybridMachineSig.ConcurMachineSemantics
       (Sem:=SemTarget)
       (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=SemTarget))
       (HybridMachine:=@bareMach SemTarget)
       (machineSig:= BareMachine.BareMachineSig) m).
Definition permissionless_init_machine (asm_prog: Asm.program) limited_builtins:=
  machine_semantics.initial_machine (permissionless_concursem
                                       (@X86Sem asm_prog limited_builtins)
                                       (Genv.init_mem asm_prog)) (Some tt).

(* Predicate stating the a Clight program is:
   1. Correct: with Consurrent Separation Logic proof
   2. Has spawn wrappers for spawning threads.
 *)
Inductive CSL_correct: Ctypes.program Clight.function -> Prop:=
| Build_safe_prog:
    forall (CPROOF: CSL_proof),
      spawn_wrapper CPROOF ->
      CSL_correct (CSL_prog CPROOF).

(* Get a pointr to Main function from the main in block*)
Definition main_ptr (prog:Ctypes.program function):=
  Vptr (Ctypes.prog_main prog) zero.

(*Constructs the initial state *)
(** * This comes from initial_Clight_state in juicy/Clight_safety.v
    I think that is wheree it comes from. 
    In any case, this is what appears, when one uses the CSL safety proof.
 *)

Definition Clight_init_state (prog:Ctypes.program function) main_symb f_main init_mem :=
  State main_handler
        (Scall None (Etempvar BinNums.xH (type_of_fundef f_main))
               (List.map (fun x : AST.ident * Ctypes.type => Etempvar (fst x) (snd x))
                         (Clight_new.params_of_types (BinNums.xO BinNums.xH)
                                                     (Clight_new.params_of_fundef f_main))))
        (Kseq (Sloop Sskip Sskip) Kstop) empty_env
        (temp_bindings BinNums.xH (main_symb:: nil)) init_mem.

(* Erasing permissions from memory. *)
Definition bare_mem:= @diluteMem dry_context.AsmContext.BareDilMem.

(*This is a statically checked property:
    - The initial memory is well formed:
    Potentially we can prove this is preserved.
    - The initial global env. is well formed:
    Potentially we can prove this is preserved.
 *)
Definition asm_prog_well_formed (Asm_prog: Asm.program) asm_genv_safe:=
  (forall init_mem_target,
      Genv.init_mem  Asm_prog = Some init_mem_target ->
      MemoryWD.valid_mem init_mem_target /\
      @ge_wd _ (X86Inj.X86Inj Asm_prog asm_genv_safe)
             (Renamings.id_ren init_mem_target)
             (Genv.globalenv Asm_prog)).

Inductive CSL_init_setup c_prog: Memory.mem -> state -> Prop :=
| Build_CSL_initial_setup:
    forall init_mem_source init_st b_main f_main,
      Clight_init_state c_prog (Vptr b_main zero) f_main init_mem_source = init_st ->
      Genv.init_mem (Ctypes.program_of_program c_prog) = Some init_mem_source ->
      Genv.find_symbol (globalenv c_prog) (prog_main c_prog) = Some b_main ->
      Genv.find_funct_ptr (Genv.globalenv (program_of_program c_prog)) b_main = Some f_main ->
      CSL_init_setup c_prog init_mem_source init_st.


Notation sc_execution := (@Executions.fine_execution _ BareDilMem BareMachine.resources
                                                     BareMachine.BareMachineSig).
Definition spinlock_well_synchronized {sem} U (st: @ThreadPool.t BareMachine.resources sem _) m: Prop:=
  forall final_st final_m tr,
    sc_execution (U, nil, st) m (nil,tr,final_st) final_m ->
    SpinLocks.spinlock_synchronized tr.

Notation bare_safe := (@fsafe _ _ _ BareMachine.BareMachineSig BareDilMem).
Record spinlock_safe {sem} U tgt_cpm tgt_m:=
  { spin_sync: spinlock_well_synchronized U tgt_cpm (bare_mem tgt_m);
    safe_execution: forall n, @fsafe _ sem _ BareMachineSig BareDilMem tgt_cpm (bare_mem tgt_m) U n
  }.

Ltac destruct_sig:=
  match goal with
    |- context[ssrfun.sval ?X] => destruct X
  end.
Definition init_tp {Sem TP}(thread:semC):=  @ThreadPool.mkPool resources Sem TP (Krun thread) tt.
