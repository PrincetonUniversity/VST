From mathcomp.ssreflect Require Import ssreflect fintype.

Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.

(* The concurrent machinery*)
Require Import concurrency.concurrent_machine.
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

Module lifting.  
  Section lifting.
    Import THE_DRY_MACHINE_SOURCE.
    Notation GS := (SEM.G).
    Notation GT := (dry_context.SEM.G).    
    Variable gT : GT.
    Variable gS : GS.
    
    Notation semS := (SEM.Sem).
    Notation semT := (dry_context.SEM.Sem).

    Notation CT := (dry_context.SEM.C).
    Notation CS := (SEM.C).

    Definition ge_inv (geS : GS) (geT : GT) :=
      genvs_domain_eq (Clight.genv_genv geS) geT.

    Definition init_inv j (geS : GS) valsS mS (geT : GT) valsT mT :=
      Mem.mem_inj j mS mT /\
      List.Forall2 (val_inject j) valsS valsT /\
      Events.meminj_preserves_globals (Clight.genv_genv geS) j.

    Definition halt_inv j (geS : GS) rv1 mS (geT : GT) rv2 mT :=
      Mem.mem_inj j mS mT /\
      val_inject j rv1 rv2.
    
    Lemma concur_sim main p (sch : mySchedule.schedule) :
      Wholeprog_sim
        (DMachineSem sch p)
        (dry_context.DryConc.MachineSemantics sch p)
        gS gT main
        ge_inv init_inv halt_inv.
    Proof.
    Admitted.

  End lifting.
End lifting.
      
                  


