
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.

Require Import compcert.common.Values.

Require Import VST.concurrency.machine_simulation.
Require Import VST.concurrency.permissions.

Require Import VST.concurrency.DryMachineSource.
Require Import VST.concurrency.DryMachineSourceCore.

Require Import VST.concurrency.concursim_safety.
Require Import VST.concurrency.semax_to_juicy_machine.
Require Import VST.concurrency.Clight_safety.


  Module NewMachine:= THE_DRY_MACHINE_SOURCE.DMS.
  Module CoreMachine:= DMS.
  Module NewDryConc:= NewMachine.DryConc.
  Module CoreDryConc:= CoreMachine.DryConc.

  Theorem new2core_simulation:
   forall  (sch: DMS.SC.Sch)
              (psrc: option NewMachine.DryMachine.ThreadPool.RES.res)
              (ptgt: option CoreMachine.DryMachine.ThreadPool.RES.res)
              prog b,
       Genv.find_symbol (Clight.genv_genv (Clight.globalenv prog))
       (AST.prog_main (Ctypes.program_of_program prog)) =
     Some b ->
    Machine_sim
      (NewDryConc.new_MachineSemantics sch psrc)
      (CoreDryConc.new_MachineSemantics sch ptgt)
      (Clight.globalenv prog) (Clight.globalenv prog)
      (Values.Vptr b Int.zero).
  Proof.
    (*You may ignore core_initial.*)
    (*Waiting for the new Compcert interface.*)
  Admitted.

  Module Clight_new2core_simulation_safety:=
    concure_simulation_safety NewMachine CoreMachine.

  Theorem new2core_safe:
    forall (sch: DMS.SC.Sch)
              (psrc: option NewMachine.DryMachine.ThreadPool.RES.res)
              (ptgt: option CoreMachine.DryMachine.ThreadPool.RES.res)
         prog b
        (FS: Genv.find_symbol (Clight.genv_genv (Clight.globalenv prog))
               (AST.prog_main (Ctypes.program_of_program prog)) =  Some b)
         (Sds : THE_DRY_MACHINE_SOURCE.DMS.FineConc.machine_state) 
         (Sm : Memory.Mem.mem) (Tds : DMS.FineConc.machine_state) 
         (Tm : Memory.Mem.mem) 
        (cd : MSdata _ (new2core_simulation sch psrc ptgt prog b FS))
         (j : Values.Val.meminj),
       MSmatch_states _ (new2core_simulation sch psrc ptgt prog b FS) cd j Sds Sm Tds Tm ->
       (forall sch : DMS.SC.Sch,
        NewMachine.DryConc.valid (sch, nil, Sds) ->
        NewMachine.DryConc.safe_new_step (Clight.globalenv prog) (sch, nil, Sds) Sm) ->
       forall sch : DMS.SC.Sch,
       CoreMachine.DryConc.valid (sch, nil, Tds) ->
       CoreMachine.DryConc.safe_new_step (Clight.globalenv prog) (sch, nil, Tds) Tm.
  Proof.
  intros sch psrc ptgt prog b FS.
    exact (Clight_new2core_simulation_safety.safety_preservation _ _
     sch psrc ptgt (Vptr b Int.zero) (new2core_simulation sch psrc ptgt prog b FS)).
  Qed.

Require Import veric.Clight_sim.

(*
    Lemma Initial_dry_safety_concur_core:
      forall (CPROOF : CSL_proof),
    forall (sch: DMS.SC.Sch),
      exists init_st, exists init_m,
        (machine_semantics.initial_machine
           (CoreDryConc.new_MachineSemantics sch (Some (getCurPerm init_m, empty_map)))) (Clight.globalenv (CSL_prog CPROOF))
                                                                                       init_m (Vptr (projT1 (spr CPROOF)) Int.zero) nil =
        Some (init_st, None) /\
        forall U',
          CoreDryConc.new_valid (CoreDryConc.mk_nstate (U', nil, init_st) init_m) U' ->
       CoreMachine.DryConc.safe_new_step (Clight.globalenv (CSL_prog CPROOF)) (U', nil, init_st)
         init_m.
    Proof. 
     intros.
     assert (n:nat). apply O.
     pose (m := juicy_mem.m_dry (initial_jm CPROOF n)).
     destruct (Genv.init_mem (Ctypes.program_of_program (CSL_prog CPROOF))) eqn:?H;
        [ | contradiction (CSL_init_mem_not_none CPROOF)].
     assert (H0: Genv.find_symbol (Clight.genv_genv (Clight.globalenv (prog CPROOF)))
    (AST.prog_main (Ctypes.program_of_program (prog CPROOF))) =
                Some (projT1 (spr CPROOF))). {
        destruct spr as (b & q & ?H & ?). auto.
    }
     destruct (Initial_dry_safety_concur CPROOF (projT1 (spr CPROOF)) H0 sch n) as [init_st [? ?]].
     assert (H8 := new2core_simulation sch
                   (Some (getCurPerm m, empty_map))
                   (Some (getCurPerm m, empty_map))
                    (CSL_prog CPROOF) (projT1 (spr CPROOF)) H0).
     destruct (core_initial _ _ _ _ _ H8 inject_id init_st nil m None nil m None H1).
     ad mit.
     constructor.
     hnf; auto.
     destruct H3 as [q' [? ?]].
     exists q', m. split; auto.
     clear - H3 H4 H8 H0 H2.
     assert (H5 := Clight_new2core_simulation_safety.safety_preservation _ _ _ _ _ _ H8).
     eapply Clight_new2core_simulation_safety.safety_preservation; eauto.
     intros.
    assert (m = proj1_sig (init_mem CPROOF)). {
      subst m. clear.
      destruct CPROOF; simpl. unfold init_mem; simpl. unfold initial_jm; simpl.
        destruct spr as (b & q & ?H & ?); simpl.
        destruct (s n). simpl. destruct a. rewrite H0. simpl. unfold init_mem; simpl. auto.
    }
     rewrite H1.
     apply safe_new_step_bound_safe_new_step.
      split. apply H. simpl.
      apply bounded_initial_mem.
     apply H2.
      apply H.
Ad_itted.

*)
