From mathcomp.ssreflect Require Import ssreflect fintype.

Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.

(* The concurrent machinery*)
Require Import concurrency.concurrent_machine.
Require Import concurrency.semantics.
Require Import concurrency.dry_machine. Import Concur.
Require Import concurrency.scheduler.

(* We assume, on each thread, a structured simulation *)
Require Import sepcomp.simulations. Import SM_simulation.

(* We lift to a whole-program simulation on the dry concurrency machine *)
Require Import sepcomp.wholeprog_simulations. Import Wholeprog_sim.

Require Import sepcomp.event_semantics.

(** The X86 DryConc Machine*)
Require Import concurrency.dry_context.

(** The Clight DryConc Machine*)
Require Import concurrency.DryMachineSource.

(** The new machine simulation*)
Require Import concurrency.machine_semantics. Import machine_semantics.
Require Import concurrency.machine_simulation. Import Machine_sim.

Module lifting (SEMT: Semantics) (Machine: MachinesSig with Module SEM := SEMT).
  Section lifting.
    Import THE_DRY_MACHINE_SOURCE.
    Import THE_DRY_MACHINE_SOURCE.DMS.
    Notation GS := (SEM.G).
    Notation GT := (SEMT.G).
    Variable gT : GT.
    Variable gS : GS.
    
    Notation semS := (SEM.Sem).
    Notation semT := (SEMT.Sem).

    Notation CT := (SEMT.C).
    Notation CS := (SEM.C).

    Definition ge_inv (geS : GS) (geT : GT) :=
      genvs_domain_eq (Clight.genv_genv geS) (SEMT.getEnv geT).

    Definition init_inv j (geS : GS) valsS mS (geT : GT) valsT mT :=
      Mem.mem_inj j mS mT /\
      List.Forall2 (val_inject j) valsS valsT /\
      Events.meminj_preserves_globals (Clight.genv_genv geS) j.

    Definition halt_inv j (geS : GS) rv1 mS (geT : GT) rv2 mT :=
      Mem.mem_inj j mS mT /\
      val_inject j rv1 rv2.

    Lemma concur_whole_sim main psrc ptgt (sch : mySchedule.schedule) :
      Wholeprog_sim
        (DMachineSem sch psrc)
        (Machine.DryConc.MachineSemantics sch ptgt)
        gS gT main
        ge_inv init_inv halt_inv.
    Proof.
    Admitted.

    Lemma concur_sim main psrc ptgt (sch : mySchedule.schedule) :
      Machine_sim
        (new_DMachineSem sch psrc)
        (Machine.DryConc.new_MachineSemantics sch ptgt)
        gS gT main
        ge_inv init_inv halt_inv.
    Proof.
    Admitted.

  End lifting.
End lifting.
      
                  


