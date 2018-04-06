From mathcomp.ssreflect Require Import ssreflect fintype.

Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.

(* The concurrent machinery*)
Require Import VST.concurrency.concurrent_machine.
Require Import VST.concurrency.semantics.
Require Import VST.concurrency.dry_machine. Import Concur.
Require Import VST.concurrency.scheduler.

(* We assume, on each thread, a structured simulation *)
Require Import VST.sepcomp.simulations. Import SM_simulation.

(* We lift to a whole-program simulation on the dry VST.concurrency machine *)
Require Import VST.sepcomp.wholeprog_simulations. Import Wholeprog_sim.

Require Import VST.sepcomp.event_semantics.

(** The X86 DryConc Machine*)
Require Import VST.concurrency.dry_context.

(** The Clight DryConc Machine*)
Require Import VST.concurrency.DryMachineSource.

(** The new machine simulation*)
Require Import VST.concurrency.machine_semantics. Import machine_semantics.
Require Import VST.concurrency.machine_simulation. Import Machine_sim.

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

    (* Lemma concur_whole_sim main psrc ptgt (sch : mySchedule.schedule) :
      Wholeprog_sim
        (DMachineSem sch psrc)
        (Machine.DryConc.MachineSemantics sch ptgt)
        gS gT main
        ge_inv init_inv halt_inv.
    Proof.
      
    Admitted. *)

    Lemma concur_sim main psrc ptgt (sch : mySchedule.schedule) :
      Machine_sim
        (new_DMachineSem sch psrc)
        (Machine.DryConc.new_MachineSemantics sch ptgt)
        gS gT main
        ge_inv init_inv halt_inv.
    Proof.
      
      (*Transitivity lemma*)
      Lemma compose_machine_simulations:
        forall G1 G2 G3 C1 C2 C3 TID SCH TR M, 
        forall (Sem1: @ConcurSemantics G1 TID SCH TR C1 M)
          (Sem2: @ConcurSemantics G2 TID SCH TR C2 M)
          (Sem3: @ConcurSemantics G3 TID SCH TR C3 M)
          g1 g2 g3 main ge_inv1 ge_inv2 init_inv1 init_inv2 halt_inv1 halt_inv2,
        Machine_sim Sem1 Sem2 g1 g2 main ge_inv1 init_inv1 halt_inv1 ->
        Machine_sim Sem2 Sem3 g2 g3 main ge_inv2 init_inv2 halt_inv2->
        exists ge_inv3 init_inv3 halt_inv3,
          (Machine_sim Sem1 Sem3 g1 g3 main ge_inv3 init_inv3 halt_inv3) .
        
      Admitted.

      eapply compose_machine_simulations.
      
          
      eapply Build_Machine_sim.
      - admit. (*Order is well founded*) 
      - admit. (*ge_in*)
      - { admit. 
         (* simpl;
          unfold DryConc.init_machine', Machine.DryConc.init_machine';
          intros.
          destruct (DryMachine.init_mach psrc gS main vals1) eqn:HH;
            inversion H.
          subst t.
          eexists; eexists.
          unfold DryMachine.init_mach in HH.
        rewrite /ge_inv /genvs_domain_eq; intros.
        { repeat split; simpl; intros.
          + destruct H as [id H].
            exists id. *) }
      - intros. 
    Admitted.

  End lifting.
End lifting.




