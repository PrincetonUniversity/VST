Require Import concurrency.machine_simulation.

Require Import concurrency.DryMachineSource.
Require Import concurrency.DryMachineSourceCore.

Require Import concurrency.concursim_safety.


  Module NewMachine:= THE_DRY_MACHINE_SOURCE.DMS.
  Module CoreMachine:= DMS.
  Module NewDryConc:= NewMachine.DryConc.
  Module CoreDryConc:= CoreMachine.DryConc.

  Variable gs: CoreMachine.DryMachine.ThreadPool.SEM.G.
  Variable gt: NewMachine.DryMachine.ThreadPool.SEM.G.
  Variable sch: DMS.SC.Sch.
  Variable psrc: option NewMachine.DryMachine.ThreadPool.RES.res.
  Variable ptgt: option CoreMachine.DryMachine.ThreadPool.RES.res.

  Theorem new2core_simulation:
    Machine_sim
      (NewDryConc.new_MachineSemantics sch psrc)
      (CoreDryConc.new_MachineSemantics sch ptgt)
      gs gt Values.Vundef.
  Proof.
    (*You may ignore core_initial, I'm not 100% satisfied with it.*)
  Admitted.

  Module Clight_new2core_simulation_safety:=
    concure_simulation_safety NewMachine CoreMachine.

  Definition new2core_safe:
    forall (Sds : THE_DRY_MACHINE_SOURCE.DMS.FineConc.machine_state) 
         (Sm : Memory.Mem.mem) (Tds : DMS.FineConc.machine_state) 
         (Tm : Memory.Mem.mem) (cd : MSdata Values.Vundef new2core_simulation)
         (j : Values.Val.meminj),
       MSmatch_states Values.Vundef new2core_simulation cd j Sds Sm Tds Tm ->
       (forall sch : DMS.SC.Sch,
        NewMachine.DryConc.valid (sch, nil, Sds) ->
        NewMachine.DryConc.safe_new_step gs (sch, nil, Sds) Sm) ->
       forall sch : DMS.SC.Sch,
       CoreMachine.DryConc.valid (sch, nil, Tds) ->
       CoreMachine.DryConc.safe_new_step gt (sch, nil, Tds) Tm:=
    Clight_new2core_simulation_safety.safety_preservation
  gs gt sch psrc ptgt new2core_simulation.

  (*TODO: Get the Clight_new safety from Clight_safety.v and put it 
    together with the new2core_safe*)
  


