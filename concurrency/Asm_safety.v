
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.

Require Import compcert.common.Values.
Require Import compcert.ia32.Asm.
Require Import concurrency.permissions.

Require Import concurrency.x86_context.
Require Import concurrency.concursim_safety.


Import X86Machines.


Variable gs: X86SEM.G.
Variable sch: DryConc.Sch.
(*Variable ptgt: option CoreMachine.DryMachine.ThreadPool.RES.res.*)

Lemma Initial_Asm_safety:
  forall (prog : program  )
    (U : DryConc.Sch) (n : nat) (b: block) init_m,
    let ge:= Genv.globalenv prog in
    Genv.init_mem prog = Some init_m ->
    exists init_st,
      (machine_semantics.initial_machine
         (DryConc.new_MachineSemantics U (Some (getCurPerm init_m, empty_map))))
        ge
        init_m (Vptr b Int.zero) nil =
      Some (init_st, None) /\
      forall U',
        DryConc.new_valid (DryConc.mk_nstate (U', nil, init_st) init_m) U' ->
        DryConc.safe_new_step ge (U', nil, init_st)
                                                init_m.
Proof.
Admitted.
  


