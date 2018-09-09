(** * Safety of the FineConc Machine (abstract semantics)*)

Require Import compcert.lib.Axioms.

Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.common.pos.


From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.dry_machine_step_lemmas.
Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.sc_drf.mem_obs_eq.
Require Import VST.concurrency.sc_drf.compcert_threads_lemmas.
Require Import VST.concurrency.common.dry_context.
Require Import VST.concurrency.common.tactics.
Require Import compcert.lib.Coqlib.
Require Import VST.msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module FineConcInitial.

  Import Renamings MemObsEq ValObsEq ValueWD MemoryWD
         AsmContext CoreInjections event_semantics.

  Section FineConcInitial.

    Context {Sem : Semantics}
            {CI: CoreInj}.

    Class FineInit :=
      { init_mem : Memory.Mem.mem; (** some initial memory *)
        init_mem_wd: (** The initial memory is well-defined*)
          valid_mem init_mem;
        the_ge_wd:   (** The initial global env is well-defined*)
          ge_wd (id_ren init_mem) the_ge
      }.
    (* init_core_wd:   (** The initial core is well-defined*) *)
    (*   forall c v args m m' (ARGS:valid_val_list (id_ren m) args), *)
    (*     init_mem = Some m -> *)
    (*     initial_core semSem 0 m c m' v args -> *)
    (*     core_wd (id_ren m) c /\ valid_mem m'; *)

  End FineConcInitial.
  
End FineConcInitial.

(** ** Safety for FineConc (interleaving) semantics *)
Module FineConcSafe.

  Import ThreadPool AsmContext ThreadPoolWF HybridMachine DryHybridMachine HybridMachineSig.
  Import Renamings MemObsEq ValObsEq ValueWD CoreInjections FineConcInitial.
  Import StepType InternalSteps StepLemmas.

  Import MemoryWD ThreadPoolInjections event_semantics.

  Section FineConcSafe.

    Context {Sem : Semantics}
            {semAx: CoreLanguage.SemAxioms}
            {semDet: CoreLanguage.SemDet}
            {CI : CoreInj}
            {FI : FineInit}.

    (** Excluded middle is required, but can be easily lifted*)
    Variable em : ClassicalFacts.excluded_middle.

    (* Is this the right instance? *)
    Existing Instance DryHybridMachine.dryResources.
    Existing Instance DryHybridMachine.DryHybridMachineSig.
    Existing Instance OrdinalPool.OrdinalThreadPool.
    Existing Instance dryFineMach.
    Existing Instance FineDilMem.
    Existing Instance dryCoarseMach.
    Existing Instance HybridFineMachine.scheduler.
    Existing Instance HybridCoarseMachine.scheduler.
    Existing Instance HybridCoarseMachine.DilMem.

    Lemma init_tp_wd:
      forall pmap v args m' tp (ARGS:valid_val_list (id_ren init_mem) args),
        @init_mach DryHybridMachine.dryResources _ _ _ pmap init_mem tp m' v args ->
        tp_wd (id_ren m') tp /\ valid_mem m'.
    Proof.
      intros.
      simpl in H.
      unfold DryHybridMachine.init_mach in H.
      destruct H as [c [Hinit_core Hinit_perm]].
      subst.
      eapply initial_core_wd with (f := id_ren init_mem) (fg := id_ren init_mem) in Hinit_core; eauto.
      destruct Hinit_core as [Hvalid' Hf'].
      destruct Hf' as [[f' [? ?]] Hcore_wd].
      split; auto.
      simpl.
      intros i cnti.
      unfold ctl_wd.
      assert (Hget: getThreadC cnti = Krun c)
        by (unfold getThreadC, OrdinalPool.getThreadC;
            reflexivity).
      rewrite Hget.
      eapply Hcore_wd; eauto using id_ren_domain.
      eapply init_mem_wd; eauto.
      now apply id_ren_domain.
      now apply the_ge_wd.
      now apply ren_domain_incr_refl.
    Qed.

    (** Assuming safety of cooperative VST.concurrency*)
    Section Safety.

      Variables (f : val) (arg : list val).

      Variable init_coarse_safe:
        forall sched tpc mem' n,
          tpc_init sched init_mem (sched, [::], tpc) mem' f arg ->
          HybridCoarseMachine.csafe (sched,[::],tpc) mem' n.

      (** [init_mach] and [init_mem] are related by [mem_compatible]*)
      (* Lemma init_compatible: *)
      (*   forall pmap tp m m', *)
      (*     @init_mach DryHybridMachine.dryResources _ _ _ pmap m tp m' f arg -> *)
      (*     mem_compatible tp m'. *)
      (* Proof. *)
      (*   intros. *)
      (*   destruct init_perm as [pmap|] eqn:Hinit_perm; *)
      (*     [| eapply init_mach_none in H0; now exfalso]. *)
      (*   unfold init_perm in Hinit_perm. *)
      (*   rewrite H in Hinit_perm. *)
      (*   inversion Hinit_perm; subst. *)
      (*   constructor. *)
      (*   - intros j cntj. *)
      (*     pose proof (init_thread H0 cntj); subst. *)
      (*     erewrite getThreadR_init by eauto. *)
      (*     simpl. *)
      (*     split; [intros ? ?; now apply getCur_Max |now apply empty_LT]. *)
      (*   - intros. *)
      (*     erewrite init_lockRes_empty in H1 by eauto. *)
      (*     discriminate. *)
      (*   - intros. *)
      (*     erewrite init_lockRes_empty in H1 by eauto. *)
      (*     discriminate. *)
      (* Qed. *)

      (** Simulation relation with id renaming for initial memory*)
      Lemma init_mem_obs_eq :
        forall pmap m' tp i (cnti : containsThread tp i)
          (Hcomp: mem_compatible tp m')
          (HcompF: mem_compatible tp (@diluteMem FineDilMem m'))
          (ARGS:valid_val_list (id_ren init_mem) arg),
          @init_mach DryHybridMachine.dryResources _ _ _ pmap init_mem tp m' f arg ->
          mem_obs_eq (id_ren m') (restrPermMap (compat_th _ _ Hcomp cnti).1)
                     (restrPermMap (HcompF _ cnti).1) /\
          mem_obs_eq (id_ren m') (restrPermMap (Hcomp _ cnti).2)
                     (restrPermMap (HcompF _ cnti).2).
      Proof.
        intros.
        unfold init_mach in H. simpl in H.
        unfold DryHybridMachine.init_mach in H.
        destruct H as [c [Hinit Htp]].
        subst tp.
        pose proof init_mem_wd as Hinit_mem_wd.
        pose proof the_ge_wd as Hge_wd.
        eapply @initial_core_wd with (f := id_ren init_mem) (fg := id_ren init_mem) in Hinit;
          eauto using id_ren_domain, ren_domain_incr_refl.
        destruct Hinit as [Hvalid_mem' [Hf' Hcore_wd']].
        pose proof (mem_obs_eq_id Hvalid_mem') as Hobs_eq_id.
        destruct Hobs_eq_id.
        split.
        - constructor.
          + constructor;
              destruct weak_obs_eq0; eauto.
            intros.
            do 2 rewrite restrPermMap_Cur.
            simpl.
            apply id_ren_correct in Hrenaming. subst.
            apply po_refl.
          + constructor.
            intros.
            apply id_ren_correct in Hrenaming.
            subst.
            do 2 rewrite restrPermMap_Cur.
            reflexivity.
            intros.
            apply id_ren_correct in Hrenaming. subst b2.
            eapply memval_obs_eq_id.
            apply Mem.perm_valid_block in Hperm.
            simpl.
            unfold valid_mem in Hvalid_mem'.
            unfold valid_memval.
            destruct (ZMap.get ofs (Mem.mem_contents m') !! b1) eqn:Hget; auto.
            pose proof (Hvalid_mem' _ Hperm ofs _ Hget).
            rewrite <- wd_val_valid with (m := m'); eauto.
            apply id_ren_domain.
            apply id_ren_correct.
        - constructor.
          + constructor;
              destruct weak_obs_eq0; eauto.
            intros.
            do 2 rewrite restrPermMap_Cur.
            simpl.
            rewrite! empty_map_spec.
            now apply po_refl.
          + constructor.
            intros.
            do 2 rewrite restrPermMap_Cur.
            simpl.
            rewrite! empty_map_spec.
            reflexivity.
            intros.
            unfold Mem.perm in Hperm.
            pose proof (restrPermMap_Cur (Hcomp i cnti).2 b1 ofs).
            unfold permission_at in H.
            rewrite H in Hperm.
            simpl in Hperm.
            rewrite empty_map_spec in Hperm.
            simpl in Hperm.
            now exfalso.
      Qed.

      (** The [strong_tsim] relation is reflexive under the identity renaming*)
      Lemma strong_tsim_refl:
        forall pmap tp m' i (cnti: containsThread tp i)
          (Hcomp: mem_compatible tp m')
          (HcompF: mem_compatible tp (@diluteMem FineDilMem m'))
          (ARGS:valid_val_list (id_ren init_mem) arg),
          @init_mach DryHybridMachine.dryResources _ _ _ pmap init_mem tp m' f arg ->
          SimDefs.strong_tsim (id_ren m') cnti cnti Hcomp HcompF.
      Proof.
        intros.
        destruct (init_mem_obs_eq cnti Hcomp HcompF ARGS H).
        constructor; eauto.
        eapply ctl_inj_id; eauto.
        destruct (init_tp_wd ARGS H).
        specialize (H2 _ cnti).
        assumption.
        now apply id_ren_correct.
      Qed.

      Lemma setMaxPerm_inv:
        forall m, SimDefs.max_inv (@diluteMem FineDilMem m).
      Proof.
        intros.
        unfold diluteMem, SimDefs.max_inv, Mem.valid_block, permission_at.
        simpl.
        intros b ofs H.
        simpl in H.
        apply setMaxPerm_MaxV with (ofs := ofs) in H.
        unfold permission_at in H.
        now auto.
      Qed.

      (** Establishing the simulation relation for the initial state*)
      Lemma init_sim:
        forall sched tpc tpf m' n (ARG:valid_val_list (id_ren init_mem) arg),
          tpc_init sched init_mem (sched, [::], tpc) m' f arg ->
          tpf_init sched init_mem (sched, [::], tpf) m' f arg ->
          SimDefs.sim tpc [::] m' tpf [::] (@diluteMem FineDilMem m') nil (id_ren m')
                      (id_ren init_mem) (fun i cnti => id_ren m') n.
      Proof.
        intros.    
        unfold tpc_init, tpf_init in *. simpl in *.
        destruct H as [? HinitC].
        destruct H0 as [? HinitF].
        assert (HmemComp: mem_compatible tpc m')
          by (eapply @safeC_compatible with (n:=1%nat); eauto).
        assert (tpf = tpc).
        { unfold DryHybridMachine.init_mach in *.
          destruct HinitC as [cc [Hinit_cc Htpc]]. 
          destruct HinitF as [cf [Hinit_cf Htpf]].
          subst.
          apply f_equal2; auto.
          apply f_equal.
          eapply CoreLanguage.initial_core_det; eauto.
        }
        subst.
        pose proof HinitC as HinitC'.
        unfold DryHybridMachine.init_mach in HinitC.
        destruct HinitC as [cc [HinitC Hinit_permC]].
        assert (HmemCompF: mem_compatible tpc (@diluteMem FineDilMem m'))
          by (eapply mem_compatible_setMaxPerm; eauto).
        subst tpc.
        pose proof HinitC as HinitC2.
        eapply initial_core_wd with (fg := id_ren init_mem) in HinitC;
          eauto using id_ren_domain, init_mem_wd, the_ge_wd, ren_domain_incr_refl.
        destruct HinitC as [Hvalid_mem' [Hf' Hcore_wd']].
        eapply SimDefs.Build_sim with (mem_compc := HmemComp) (mem_compf := HmemCompF).
        - intros; split; auto.
        - intros.
          eapply @HybridCoarseMachine.csafe_trace with (tr := [::]).
          simpl. rewrite addn0.
          eapply init_coarse_safe with (n := n);
            now eauto.
        - intros i cnti cnti'.
          pose proof (strong_tsim_refl cnti HmemComp HmemCompF ARG HinitC').
          Tactics.pf_cleanup.
          destruct H1. destruct obs_eq_data, obs_eq_locks.
          constructor;
            now eauto.
        - intros; by congruence.
        - intros.
          exists (@mkPool dryResources _ _  (Krun cc) ((getCurPerm m', empty_map)#1, empty_map)), m'.
          split; eauto with renamings.
          split; eauto.
          split; first by constructor.
          split.
          intros; Tactics.pf_cleanup.
          eapply strong_tsim_refl; eauto.
          pose proof (init_thread HinitC' pff); subst tid.
          repeat (split; intros); try congruence.
          + erewrite getThreadR_init by eauto.
            simpl.
            pose proof (@strong_tsim_refl None _ _ _ pfc HmemComp HmemCompF ARG) as Hstrong_sim.
            simpl in Hstrong_sim.
            specialize (Hstrong_sim HinitC').
            Tactics.pf_cleanup.
            destruct Hstrong_sim. destruct obs_eq_data.
            destruct weak_obs_eq0.
            destruct (valid_block_dec m' b2).
            * pose proof (domain_valid0 _ v) as Hmapped.
              destruct Hmapped as [b' Hid].
              pose proof (id_ren_correct _ _ Hid); subst.
              exfalso. apply H1.
              eexists; eauto.
            * apply Mem.nextblock_noaccess with (k := Cur) (ofs := ofs) in n0.
              rewrite getCurPerm_correct.
              unfold permission_at.
              assumption.
          + erewrite getThreadR_init by eauto.
            simpl.
            now apply empty_map_spec.
        - unfold DryHybridMachine.init_mach in *.
          destruct HinitC' as [c' [HinitC' Heq]].
          split.
          + intros.
            exfalso.
            unfold initial_machine, lockRes in *. simpl in *.
            unfold OrdinalPool.mkPool, OrdinalPool.lockRes in *.
            simpl in Hl1, Hl2.
            erewrite OrdinalPool.find_empty in Hl1, Hl2.
            discriminate.
          + split.
            * intros.
              unfold lockRes, initial_machine in H.
              unfold OrdinalPool.mkPool, OrdinalPool.lockRes in *.
              simpl in H.
              now exfalso.
            * intros.
              apply id_ren_correct in H1; subst.
              split;
                now auto.
        - intros.
          unfold DryHybridMachine.init_mach in HinitC'.
          destruct HinitC' as [c' [HinitC' Heq]].
          unfold initial_machine, lockRes in *. simpl in *.
          unfold OrdinalPool.mkPool, OrdinalPool.lockRes in *.
          simpl in H.
          erewrite OrdinalPool.find_empty in H1.
          discriminate.
        - eapply ThreadPoolWF.initial_invariant;
            now eauto.
        - apply setMaxPerm_inv; auto.
        - assumption.
        - eapply init_tp_wd; eauto.
        - eapply the_ge_wd; eauto.
        - split; eauto with renamings.
          destruct Hf' as [f' [Hincrf' Hdomainf']].
          intros b1 b2 Hid.
          unfold id_ren in *.
          destruct (valid_block_dec init_mem b1); simpl in Hid; try discriminate.
          inversion Hid; subst.
          destruct (valid_block_dec m' b2); simpl; auto.
          exfalso.
          apply n0.
          unfold Mem.valid_block, Plt in *.
          apply CoreLanguage.initial_core_nextblock in HinitC2.
          zify; omega.
          now apply id_ren_correct.
        - simpl. tauto.
        - constructor.
          Unshelve. apply None.
      Qed.

      (** Proof of safety of the FineConc machine*)

      Notation fsafe := (@HybridFineMachine.fsafe _ _ _ _ FineDilMem).

      (** If a thread has reached an external then it cannot be in the
          list that denotes the delta of execution between the two machines *)
      Lemma at_external_not_in_xs:
        forall tpc trc mc tpf trf mf xs f fg fp i n
          (Hsim: SimDefs.sim tpc trc mc tpf trf mf xs f fg fp n)
          (pffi: containsThread tpf i),
          let mrestr := restrPermMap (compat_th _ _ (SimDefs.mem_compf Hsim) pffi).1 in
          forall (Hexternal: getStepType pffi mrestr Concurrent),
            ~ List.In i xs.
      Proof.
        intros; intro Hin.
        destruct Hsim.
        assert (pfci: containsThread tpc i)
          by (eapply numThreads; eauto).
        pose proof (simStrong _ pfci pffi) as HsimStrongi.
        destruct HsimStrongi as (tpc' & mc' & Hincr & _ & Hexec & Htsim & _).
        assert (pfci' : containsThread tpc' i)
          by (eapply InternalSteps.containsThread_internal_execution; eauto).
        assert (HmemCompC': mem_compatible tpc' mc')
          by (eapply InternalSteps.internal_execution_compatible with (tp := tpc) (m := mc);
              eauto; eapply Hexec).
        specialize (Htsim pfci' HmemCompC').
        destruct Htsim.
        clear - Hexec code_eq Hexternal Hin HmemCompC' obs_eq_data Hincr semAx.
        unfold getStepType in Hexternal.
        pose proof Hexec as Hexec'.
        eapply internal_execution_result_type with (cnti' := pfci') (Hcomp' := HmemCompC') in Hexec;
          eauto.
        unfold getStepType in Hexec.
        destruct fg_spec.
        erewrite SimProofs.ctlType_inj with (f:= fp i pfci) in Hexec; eauto.
        eapply ren_incr_trans; eauto.
        - erewrite <- restrPermMap_mem_valid.
          eapply SimProofs.internal_execution_wd; eauto.
          destruct (simWeak _ pfci pffi).
          erewrite restrPermMap_domain with (Hlt := (compat_th _ _ mem_compc pfci).1).
          eapply weak_obs_eq_domain_ren; now eauto.
          eapply ren_incr_domain_incr; now eauto.
      Qed.

      Lemma getStepType_cases:
        forall tp m i (cnti: containsThread tp i),
          getStepType cnti m Concurrent \/
          getStepType cnti m Internal \/
          getStepType cnti m Suspend.
      Proof.
        intros.
        unfold getStepType, ctlType.
        destruct (getThreadC cnti); try auto.
        destruct (at_external semSem s m) eqn:?; try auto.
       Qed.
      
      (** Simulation between the two machines implies safety*)
      Lemma fine_safe_sched:
        forall tpf trf tpc trc mf mc (g fg : memren) fp xs sched
          (Hsim: SimDefs.sim tpc trc mc tpf trf mf xs g fg fp (S (size sched))),
          @fsafe tpf mf sched (S (size sched)).
      Proof.
        intros.
        generalize dependent xs.
        generalize dependent mf.
        generalize dependent tpf.
        generalize dependent fp.
        generalize dependent tpc.
        generalize dependent trc.
        generalize dependent trf.
        generalize dependent mc.
        generalize dependent g.
        induction sched as [|i sched]; intros; simpl; auto.
        econstructor; simpl; eauto.
        destruct (OrdinalPool.containsThread_dec i tpf) as [cnti | invalid].
        - (** By case analysis on the step type *)
          pose proof (getStepType_cases (restrPermMap (compat_th _ _ (SimDefs.mem_compf Hsim) cnti).1)
                                        cnti) as Htype.
          destruct Htype as [Htype | [Htype | Htype]].
          + assert (~ List.In i xs)
              by (eapply at_external_not_in_xs; eauto).
            pose proof (@SimProofs.sim_external _ _ _ _ sched em _ _ _ _ _ _ _ _ _ _ _ _ cnti H Hsim Htype) as Hsim'.
            destruct Hsim' as (tpc' & trc' & mc' & tpf' & mf' & f' & fp' & tr' & Hstep & Hsim'').
            specialize (IHsched _ _ _ _ _ _ _ _ _ Hsim'').
            specialize (Hstep sched).
            unfold corestep in Hstep.
            simpl in Hstep.
            eapply @HybridFineMachine.StepSafe with (dilMem := FineDilMem);
              eauto.
          + pose proof (@SimProofs.sim_internal _ _ _ _ sched  _ _ _ _ _ _ _ _ _ _ _ _ cnti Hsim Htype) as
                (tpf' & m' & fp' & tr' & Hstep & Hsim').
            specialize (Hstep sched).
            specialize (IHsched _ _ _ _ _ _ _ _ _ Hsim').
            unfold corestep in Hstep.
            simpl in Hstep.
            econstructor 3; simpl; eauto.
          + pose proof (@SimProofs.sim_suspend _ _ _ _ sched em _ _ _ _ _ _ _  _ _ _ _ _ cnti Hsim Htype) as
                (tpc' & trc' & mc' & tpf' & mf' & f' & fp' & tr' & Hstep & Hsim').
            specialize (IHsched _ _ _ _ _ _ _ _ _ Hsim').
            specialize (Hstep sched).
            unfold corestep in Hstep.
            simpl in Hstep.
            econstructor 3; simpl;
              now eauto.
        -  pose proof (@SimProofs.sim_fail _ _  sched _ _ _ _  _  _ _  _ _ _ _ _ invalid Hsim) as
              (tr' & Hstep & Hsim').
           specialize (IHsched _ _ _ _ _ _ _ _ _ Hsim').
           specialize (Hstep sched).
           unfold corestep in Hstep.
           simpl in Hstep.
           econstructor 3; eauto.
           Unshelve. eapply [::].
      Qed.

      Lemma fsafe_reduce:
        forall sched tp mem n m,
          fsafe tp mem sched n ->
          (m <= n)%nat ->
          fsafe tp mem sched m.
      Proof.
        intros until 1; revert m.
        induction H; intros.
        - assert (m0 = 0%nat) by ssromega; subst; constructor.
        - eapply @HybridFineMachine.HaltedSafe with (tr := tr); eauto.
        - destruct m0; [constructor|].
          eapply HybridFineMachine.StepSafe;
            now eauto.
      Qed.

      Lemma fine_safe:
        forall n tpf mf sched,
          @fsafe tpf mf sched (S (size sched)) -> 
          @fsafe tpf mf sched n.
      Proof.
        intros.
        destruct ((n <= (S (size sched)))%nat) eqn:?.
        eapply fsafe_reduce; eauto.
        clear - H Heqb.
        generalize dependent tpf.
        generalize dependent mf.
        generalize dependent n.
        induction sched; intros.
        -  eapply @HybridFineMachine.HaltedSafe with (tr := [::]) (dilMem := FineDilMem);
             simpl;
             now eauto.
        - simpl in *.
          destruct n.
          exfalso. ssromega.
          inv H. simpl in H0. now exfalso.
          eapply @HybridFineMachine.StepSafe with (tr := tr) (dilMem := FineDilMem);
            eauto.
      Qed.
      
      (** *** Safety preservation for the FineConc machine starting from the initial state*)
      Theorem init_fine_safe:
        forall sched n tpf m'
          (Hinit: tpf_init sched init_mem (sched, [::], tpf) m' f arg)
          (ARG: valid_val_list (id_ren init_mem) arg),
          fsafe tpf (@diluteMem FineDilMem m') sched n.
      Proof.
        intros.
        assert (Hsim := init_sim (S (size sched)) ARG Hinit Hinit).
        eapply fine_safe.
        eapply fine_safe_sched;
          now eauto.
      Qed.

    End Safety.
  End FineConcSafe.
End FineConcSafe.





