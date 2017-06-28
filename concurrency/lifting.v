From mathcomp.ssreflect Require Import ssreflect fintype.

Require Import Omega.
Require Import msl.Coqlib2.

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
Require Import concurrency.x86_context.

(** The Clight DryConc Machine*)
Require Import concurrency.DryMachineSourceCore.

(** The new machine simulation*)
Require Import concurrency.machine_semantics. Import machine_semantics.
Require Import concurrency.machine_simulation. 

(** The hybrid simulation proof*)
Require Import concurrency.CoreSemantics_sum.
Require Import concurrency.HybridMachine_simulation_proof.


Set Bullet Behavior "Strict Subproofs".

Module lifting.
  Section lifting.
    Import DMS.
    Import X86Machines.
    Notation GS := (DMS.SEM.G).
    Notation GT := (SEM.G).
    Definition gT : GT:= snd genv'.
    Definition gS : GS:= fst genv'.

    Notation semS := (DMS.SEM.Sem).
    Notation semT := (SEM.Sem).

    Notation CT := (SEM.C).
    Notation CS := (DMS.SEM.C).

   (* I don't think we need these
      Definition ge_inv (geS : GS) (geT : GT) :=
      genvs_domain_eq (Clight.genv_genv geS) (SEM.getEnv geT). *)

   (* Definition init_inv j (geS : GS) valsS mS (geT : GT) valsT mT :=
      Mem.mem_inj j mS mT /\
      List.Forall2 (val_inject j) valsS valsT /\
      Events.meminj_preserves_globals (Clight.genv_genv geS) j. *)

    (* Definition halt_inv j (geS : GS) rv1 mS (geT : GT) rv2 mT :=
      Mem.mem_inj j mS mT /\
      val_inject j rv1 rv2. *)

    (* Lemma concur_whole_sim main psrc ptgt (sch : mySchedule.schedule) :
      Wholeprog_sim
        (DMachineSem sch psrc)
        (Machine.DryConc.MachineSemantics sch ptgt)
        gS gT main
        ge_inv init_inv halt_inv.
    Proof.
      
    Admitted. *)

    
    
    Context (p : Clight.program) (tp : Asm.program).
    Hypothesis compiled : Compiler.simpl_transf_clight_program p = Errors.OK tp.

    (** *First: lets realte the concurrent machines and Hybrid machines*)
    Definition source_state_make_hybrid (st: DMS.FineConc.machine_state):
          t HybridMachine.Resources (HybridMachine.Sem (Some 0) Sems Semt).
          destruct st.
          econstructor; eauto.
          intros t; apply pool in t.
          destruct t.
          eapply Krun. simpl.
          eapply SState.
          simpl in c. exact c.
          eapply Kblocked. simpl.
          eapply SState.
          simpl in c. exact c.
          eapply Kresume; eauto. simpl.
          eapply SState.
          simpl in c. exact c.
          eapply (Kinit v v0).
    Defined.

    Lemma source_step_to_hybrid:
          forall sch psrc gS gT U st1 m1 st1' m1',
          thread_step (new_DMachineSem sch psrc) gS U st1 m1 st1' m1' ->
          thread_step (HybridMachine_simulation.HCSem (Sems) Semt (Some 0) sch)
                      (gS, gT) U
                      (source_state_make_hybrid st1) m1
                      (source_state_make_hybrid st1') m1'.
        Proof.
          intros. inversion H; subst.
          assert (Hcmpt_: HybridMachine.mem_compatible (Some 0) (Sems) Semt
                                                       (source_state_make_hybrid st1) m1).
          { inversion Hcmpt; destruct st1; constructor; eauto. }
          assert (Htid_: containsThread_ (HybridMachine.ThreadPool (Some 0) (Sems) Semt)
                                  (source_state_make_hybrid st1) tid) by
              (destruct st1; apply Htid).
          econstructor; eauto.
          instantiate (1:= nil).
          instantiate (1:= Hcmpt_).
          instantiate (1:= Htid_).
          inversion Htstep; subst.
          econstructor; eauto.
          - (*invariant*)
            inversion Hinv; destruct st1; simpl in *; econstructor;eauto.
            simpl. unfold containsThread; simpl.
            unfold DMS.DryMachine.ThreadPool.containsThread in Htid; simpl.
            + intros. destruct ( pool (Ordinal (n:=pos.n num_threads) (m:=i) cnti));
                        inversion H0; subst. exists c0; auto.
            + intros. clear - H1; simpl.
              simpl in H1; eapply NPeano.Nat.ltb_lt in H1. omega.
          - clear - Hcode.
            simpl. instantiate (1 := SState _ _ c).
            destruct st1; simpl in *.
            clear - Hcode. simpl in Htid_.
            replace Htid_ with Htid. Focus 2. apply proof_irr. 
            rewrite Hcode; auto.
          - simpl.
            econstructor; eauto.
            simpl. admit. (*What is this???*)

          - simpl. unfold updThread; simpl; destruct st1; simpl.
            f_equal. extensionality id.
            replace Htid_ with Htid. Focus 2. apply proof_irr. 
            if_tac; eauto.
            replace Htid_ with Htid. Focus 2. apply proof_irr.
            auto.
        Admitted.

        Lemma source_machine_step_to_hybrid:
          forall sch psrc gS gT U U' tr tr' st1 m1 st1' m1',
          machine_step (new_DMachineSem sch psrc) gS U tr st1 m1 U' tr' st1' m1' ->
          machine_step (HybridMachine_simulation.HCSem (Sems) Semt (Some 0) sch)
                      (gS, gT) U nil
                      (source_state_make_hybrid st1) m1 U' nil
                      (source_state_make_hybrid st1') m1'.
         Proof.
           intros. inversion H; subst.
           - (*INIT thread*)
             econstructor 1; eauto.
             inversion Hcmpt; destruct st1; econstructor; eauto.
             inversion Htstep; subst.
             admit.
           - econstructor 2; eauto.
             inversion Hcmpt; destruct st1; econstructor; eauto.
             inversion Htstep; subst.
             admit.
           - econstructor 3; eauto.
             inversion Hcmpt; destruct st1; econstructor; eauto.
             inversion Htstep; subst.
             admit.
           - econstructor 4; eauto.
             admit.
           - econstructor 5; eauto.
             inversion Hcmpt; destruct st1'; econstructor; eauto.
             inversion Hinv; destruct st1'; econstructor; eauto.
             admit.
             admit.
             unfold HybridMachine.threadHalted.
             inversion Hhalted; subst.
             admit.
           - econstructor 6; eauto.
             intros HH; apply Htid.
             destruct st1'; eauto.
             admit.
         Admitted.

        Definition target_state_make_hybrid (st: FineConc.machine_state):
          t HybridMachine.Resources (HybridMachine.Sem None (Sems) Semt).
          destruct st.
          econstructor; eauto.
          intros t; apply pool in t.
          destruct t.
          eapply Krun. simpl.
          eapply TState.
          simpl in c. exact c.
          eapply Kblocked. simpl.
          eapply TState.
          simpl in c. exact c.
          eapply Kresume; eauto. simpl.
          eapply TState.
          simpl in c. exact c.
          eapply (Kinit v v0).
        Defined.

        
        Lemma target_hybrid_to_step:
          forall sch ptgt gS gT U st2 m2 st2_ m2',
          thread_step
            (HybridMachine_simulation.HCSem (Sems) Semt None sch) 
            (gS, gT) U (target_state_make_hybrid st2) m2 st2_ m2' ->
          exists st2', st2_ = (target_state_make_hybrid st2') /\
                  thread_step (DryConc.new_MachineSemantics sch ptgt) gT U st2 m2 st2' m2'.
        Proof.
        Admitted.
        Lemma target_hybrid_to_plus:
          forall sch ptgt gS gT U st2 m2 st2_ m2',
          machine_semantics_lemmas.thread_step_plus
            (HybridMachine_simulation.HCSem (Sems) Semt None sch) 
            (gS, gT) U (target_state_make_hybrid st2) m2 st2_ m2' ->
          exists st2', st2_ = (target_state_make_hybrid st2') /\
                  machine_semantics_lemmas.thread_step_plus
                    (DryConc.new_MachineSemantics sch ptgt) gT U st2 m2 st2' m2'.
        Proof.
        Admitted.
        Lemma target_hybrid_to_star:
          forall sch ptgt gS gT U st2 m2 st2_ m2',
          machine_semantics_lemmas.thread_step_star
            (HybridMachine_simulation.HCSem (Sems) Semt None sch) 
            (gS, gT) U (target_state_make_hybrid st2) m2 st2_ m2' ->
          exists st2', st2_ = (target_state_make_hybrid st2') /\
                  machine_semantics_lemmas.thread_step_star
                    (DryConc.new_MachineSemantics sch ptgt) gT U st2 m2 st2' m2'.
        Proof.
        Admitted.

        Lemma target_hybrid_to_machine_step:
          forall sch ptgt gS gT U U' tr tr' st2 m2 st2_ m2',
            machine_step (HybridMachine_simulation.HCSem (Sems) Semt None sch) 
                         (gS, gT) U tr' (target_state_make_hybrid st2) m2 U' tr st2_ m2' ->
            exists st2', st2_ = (target_state_make_hybrid st2') /\
                    machine_step (DryConc.new_MachineSemantics sch ptgt) gT U nil st2 m2 U' nil st2' m2'.
          
        Admitted.
        

    (** *Proof the simulation between the Clight_core and Asm machines*)
    Lemma concur_sim psrc ptgt (sch : mySchedule.schedule) :
      Machine_sim
        (new_DMachineSem sch psrc)
        (DryConc.new_MachineSemantics sch ptgt)
        (fst genv') (snd genv') Values.Vundef.
    Proof.
      pose proof (All_compiled_thread_simulation p tp compiled sch).
      simpl in H.
      inversion H.
      eapply Build_Machine_sim with
          (MSdata:= list (compiler_index p tp compiled))
          (MSorder:= (list_order p tp compiled))
          (MSmatch_states:= fun cd mu c1 m1 c2 m2 =>
           All_concur_match' p tp compiled sch
                     cd mu (source_state_make_hybrid c1) m1 (target_state_make_hybrid c2) m2)
      ; eauto.
      - admit. (*initial*)
      - clear - thread_diagram; intros.
        destruct genv'.
        eapply source_step_to_hybrid in H.
        eapply thread_diagram in H0; eauto.
        destruct genv'; eauto. 
        destruct H0 as
            (st2_ & m2' &  cd' & mu' & MATCH & STEPS).
        destruct STEPS as [STEPS | [STEPS ORDER]].
        + eapply target_hybrid_to_plus in STEPS.
          destruct STEPS as (st2' & eqST2 & STEPS).
          exists st2', m2', cd', mu'.
          split; eauto. rewrite <- eqST2; eauto.
        + eapply target_hybrid_to_star in STEPS.
          destruct STEPS as (st2' & eqST2 & STEPS).
          exists st2', m2', cd', mu'.
          split; auto. rewrite <- eqST2; eauto.
      - clear - machine_diagram; intros.
        destruct genv'.
        assert (HH: tr = nil /\ tr' = nil).
        { inversion H; subst; auto. }
        destruct HH as [HH1 HH2]. subst.

        eapply source_machine_step_to_hybrid in H.
        eapply machine_diagram in H0; eauto.
        destruct H0 as
            (st2_ & m2' &  cd' & MATCH & STEPS).
        eapply target_hybrid_to_machine_step in STEPS.
        destruct STEPS as (st2' & eqST2' & STEPS).
        exists st2', m2', cd', mu; split; auto.
        rewrite <- eqST2'; auto.
      - (*Running*) admit.
    Admitted.
      
  End lifting.
End lifting.




