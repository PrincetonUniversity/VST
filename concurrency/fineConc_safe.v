(** * Safety of the FineConc Machine (generic)*)

Require Import compcert.lib.Axioms.

Require Import VST.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.pos.


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

Require Import VST.concurrency.dry_machine_lemmas.
Require Import VST.concurrency.dry_machine_step_lemmas.
Require Import VST.concurrency.threads_lemmas.
Require Import VST.concurrency.permissions.
Require Import VST.concurrency.concurrent_machine.
Require Import VST.concurrency.mem_obs_eq.
Require Import VST.concurrency.compcert_threads_lemmas.
Require Import VST.concurrency.dry_context.
Require Import Coqlib.
Require Import VST.msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module Type FineConcInitial (SEM : Semantics)
       (Machine : MachinesSig with Module SEM := SEM)
       (AsmContext : AsmContext SEM Machine)
       (CI : CoreInjections SEM).

  Import Renamings MemObsEq ValObsEq ValueWD MemoryWD
         AsmContext CI event_semantics.

  (** The initial memory is well-defined*)
  Parameter init_mem_wd:
    forall m, init_mem = Some m -> valid_mem m.

  (** The initial core is well-defined*)
  Parameter init_core_wd:
    forall v args m (ARGS:valid_val_list (id_ren m) args),
      init_mem = Some m ->
      match initial_core SEM.Sem 0 the_ge v args with
      | Some c => core_wd (id_ren m) c
      | None => True
      end.

  (** The initial global env is well-defined*)
  Parameter the_ge_wd:
    forall m,
      init_mem = Some m ->
      ge_wd (id_ren m) the_ge.

End FineConcInitial.

(** ** Safety for FineConc (interleaving) semantics *)
Module FineConcSafe (SEM : Semantics) (SemAxioms : SemanticsAxioms SEM)
       (Machine : MachinesSig with Module SEM := SEM)
       (AsmContext : AsmContext SEM Machine)
       (CI : CoreInjections SEM)
       (FineConcInitial: FineConcInitial SEM Machine AsmContext CI).

  Module SimProofs := SimProofs SEM SemAxioms Machine AsmContext CI.
  Module ThreadPoolWF := ThreadPoolWF SEM Machine.
  Import AsmContext SimProofs SimDefs Machine DryMachine ThreadPoolWF.
  Import Renamings MemObsEq ValObsEq ValueWD CI FineConcInitial ThreadPool.
  Import SimDefs.StepType dry_machine.Concur.mySchedule.
  Import StepType.InternalSteps StepLemmas.

  Import MemoryWD ThreadPoolInjections event_semantics.

  (** Excluded middle is required, but can be easily lifted*)
  Axiom em : ClassicalFacts.excluded_middle.

  Lemma init_tp_wd:
    forall v args m tp (ARGS:valid_val_list (id_ren m) args),
      init_mem = Some m ->
      init_mach init_perm the_ge v args = Some tp ->
      tp_wd (id_ren m) tp.
  Proof.
    intros.
    intros i cnti.
    unfold init_mach in H0.
    destruct (initial_core SEM.Sem 0 the_ge v args) eqn:?, init_perm; try discriminate.
    inversion H0; subst.
    simpl.
    specialize (init_core_wd v ARGS H). rewrite Heqo; trivial.
  Qed.

  (** Assuming safety of cooperative VST.concurrency*)
  Section Safety.
    Variable (f : val) (arg : list val).
    Variable init_coarse_safe:
      forall  U tpc mem sched n,
        init_mem = Some mem ->
        tpc_init f arg = Some (U, [::], tpc) ->
        csafe the_ge (sched,[::],tpc) mem n.

  (** If the initial state is defined then the initial memory was also defined*)
  Lemma tpc_init_mem_defined:
    forall U tpc,
      tpc_init f arg = Some (U, tpc) ->
      exists m, init_mem = Some m.
  Proof.
    unfold tpc_init. simpl.
    unfold DryConc.init_machine.
    unfold init_mach. intros.
    destruct init_perm eqn:?.
    unfold init_perm in *.
    destruct init_mem; try discriminate.
    eexists; reflexivity.
    destruct (initial_core SEM.Sem 0 the_ge f arg); try discriminate.
  Qed.

  (** [init_mach] and [init_mem] are related by [mem_compatible]*)
  Lemma init_compatible:
    forall tp m,
      init_mem = Some m ->
      init_mach init_perm the_ge f arg = Some tp ->
      mem_compatible tp m.
  Proof.
    intros.
    destruct init_perm as [pmap|] eqn:Hinit_perm;
      [| rewrite init_mach_none in H0; discriminate].
    unfold init_perm in Hinit_perm.
    rewrite H in Hinit_perm.
    inversion Hinit_perm; subst.
    constructor.
    - intros j cntj.
      pose proof (init_thread _ _ _ _ H0 cntj); subst.
      erewrite getThreadR_init by eauto.
      simpl.
      split; [intros ? ?; now apply getCur_Max |now apply empty_LT].
    - intros.
      erewrite init_lockRes_empty in H1 by eauto.
      discriminate.
    - intros.
      erewrite init_lockRes_empty in H1 by eauto.
      discriminate.
  Qed.

  (** Simulation relation with id renaming for initial memory*)
  Lemma init_mem_obs_eq :
    forall m tp i (cnti : containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (HcompF: mem_compatible tp (diluteMem m)),
      init_mem = Some m ->
      init_mach init_perm the_ge f arg = Some tp ->
      mem_obs_eq (id_ren m) (restrPermMap (Hcomp _ cnti).1)
                 (restrPermMap (HcompF _ cnti).1) /\
      mem_obs_eq (id_ren m) (restrPermMap (Hcomp _ cnti).2)
                 (restrPermMap (HcompF _ cnti).2).
  Proof.
    intros.
    pose proof (mem_obs_eq_id (init_mem_wd H)) as Hobs_eq_id.
    unfold init_mach in H0.
    destruct (initial_core SEM.Sem 0 the_ge f arg), init_perm eqn:Hinit_perm;
      try discriminate.
    inversion H0; subst.
    unfold init_perm in Hinit_perm.
    rewrite H in Hinit_perm.
    inversion Hinit_perm. subst.
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
        apply id_ren_correct in Hrenaming. subst.
        eapply memval_obs_eq_id.
        apply Mem.perm_valid_block in Hperm.
        simpl.
        pose proof (init_mem_wd H Hperm ofs ltac:(reflexivity)).
        destruct (ZMap.get ofs (Mem.mem_contents m) # b2); simpl; auto.
        rewrite <- wd_val_valid; eauto.
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
        unfold permission_at in H1.
        rewrite H1 in Hperm.
        simpl in Hperm.
        rewrite empty_map_spec in Hperm.
        simpl in Hperm.
        now exfalso.
  Qed.

  (** The [strong_tsim] relation is reflexive under the identity renaming*)
  Lemma strong_tsim_refl:
    forall tp m i (cnti: containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (HcompF: mem_compatible tp (diluteMem m))
      (ARGS:valid_val_list (id_ren m) arg),
      init_mem = Some m ->
      init_mach init_perm the_ge f arg = Some tp ->
      strong_tsim (id_ren m) cnti cnti Hcomp HcompF.
  Proof.
    intros.
    destruct (init_mem_obs_eq cnti Hcomp HcompF H H0).
    constructor; eauto.
    eapply ctl_inj_id; eauto.
    apply (init_tp_wd _ ARGS H H0).
    apply id_ren_correct.
  Qed.

  Lemma setMaxPerm_inv:
    forall m, max_inv (diluteMem m).
  Proof.
    intros.
    unfold diluteMem, max_inv, Mem.valid_block, permission_at.
    intros b ofs H.
    simpl in H.
    apply setMaxPerm_MaxV with (ofs := ofs) in H.
    unfold permission_at in H.
    auto.
  Qed.

  (** Establishing the simulation relation for the initial state*)
  Lemma init_sim:
    forall U U' tpc tpf m n (ARG:valid_val_list (id_ren m) arg),
      tpc_init f arg = Some (U, [::], tpc) ->
      tpf_init f arg = Some (U', [::], tpf) ->
      init_mem = Some m ->
      sim tpc m tpf (diluteMem m) nil (id_ren m) (id_ren m) (fun i cnti => id_ren m) n.
  Proof.
    intros.
    unfold tpc_init, tpf_init in *. simpl in *.
    unfold DryConc.init_machine, FineConc.init_machine in *.
    destruct (init_mach init_perm the_ge f arg) eqn:Hinit; try discriminate.
    inversion H; subst. inversion H0; subst.
    clear H H0.
    assert (HmemComp := init_compatible H1 Hinit).
    assert (HmemCompF: mem_compatible tpf (diluteMem m))
      by (eapply mem_compatible_setMaxPerm; eauto).
    eapply Build_sim with (mem_compc := HmemComp) (mem_compf := HmemCompF).
    - intros; split; auto.
    - simpl. rewrite addn0.
      intros.
      eapply init_coarse_safe with (n := n); eauto.
    - intros i cnti cnti'.
      pose proof (strong_tsim_refl cnti HmemComp HmemCompF ARG H1 Hinit).
      pf_cleanup.
      destruct H. destruct obs_eq_data0, obs_eq_locks0.
      constructor; eauto.
    - intros; by congruence.
    - intros.
      exists tpf, m.
      split; eauto with renamings.
      split; eauto.
      split; first by constructor.
      split.
      intros; pf_cleanup.
      eapply strong_tsim_refl; eauto.
      pose proof (init_thread _ _ _ _  Hinit pff); subst.
      repeat (split; intros); try congruence.
      + erewrite getThreadR_init
          by (unfold init_perm in Hinit;
              rewrite H1 in Hinit;
              eauto).
        simpl.
        pose proof (strong_tsim_refl pfc HmemComp HmemCompF ARG H1 Hinit).
        pf_cleanup.
        destruct H0. destruct obs_eq_data0.
        destruct weak_obs_eq0.
        destruct (valid_block_dec m b2).
        * pose proof (domain_valid0 _ v) as Hmapped.
          destruct Hmapped as [b' Hid].
          pose proof (id_ren_correct _ _ Hid); subst.
          exfalso. apply H.
          eexists; eauto.
        * apply Mem.nextblock_noaccess with (k := Cur) (ofs := ofs) in n0.
          rewrite getCurPerm_correct.
          unfold permission_at.
          assumption.
      + erewrite getThreadR_init
          by ( unfold init_perm in Hinit;
               rewrite H1 in Hinit;
               eauto).
        simpl.
        now apply empty_map_spec.
    - unfold init_mach in *.
      unfold init_perm in Hinit.
      rewrite H1 in Hinit.
      destruct (initial_core SEM.Sem 0 the_ge f arg); try discriminate.
      inversion Hinit; subst.
      split.
      + intros.
        exfalso.
        unfold initial_machine, lockRes in *. simpl in *.
        erewrite threadPool.find_empty in Hl1, Hl2.
        discriminate.
      + split.
        * intros.
          unfold lockRes, initial_machine in H.
          rewrite threadPool.find_empty in H.
          now exfalso.
        * intros.
          apply id_ren_correct in H; subst.
          split; auto.
    - intros.
      unfold init_mach, init_perm in Hinit.
      rewrite H1 in Hinit.
      destruct (initial_core SEM.Sem 0 the_ge f arg); try discriminate.
      inversion Hinit; subst.
      unfold lockRes, initial_machine in *. simpl.
      rewrite threadPool.find_empty in H.
      discriminate.
    - eapply ThreadPoolWF.initial_invariant;
        now eauto.
    - apply setMaxPerm_inv; auto.
    - apply init_mem_wd; auto.
    - eapply init_tp_wd; eauto.
    - eapply the_ge_wd; eauto.
    - split; eauto with renamings.
      apply id_ren_correct.
    - simpl. tauto.
  Qed.

  (** Proof of safety of the FineConc machine*)

  Notation fsafe := (FineConc.fsafe the_ge).

  (** If a thread has reached an external then it cannot be in the
  list that denotes the delta of execution between the two machines *)
  Lemma at_external_not_in_xs:
    forall tpc mc tpf mf xs f fg fp i n
      (Hsim: sim tpc mc tpf mf xs f fg fp n)
      (pffi: containsThread tpf i)
      (Hexternal: pffi @ E),
      ~ List.In i xs.
  Proof.
    intros; intro Hin.
    destruct Hsim.
    assert (pfci: containsThread tpc i)
      by (eapply numThreads0; eauto).
    specialize (simStrong0 _ pfci pffi).
    destruct simStrong0 as (tpc' & mc' & Hincr & _ & Hexec & Htsim & _).
    assert (pfci' : containsThread tpc' i)
      by (eapply InternalSteps.containsThread_internal_execution; eauto).

    assert (HmemCompC': mem_compatible tpc' mc')
      by (eapply InternalSteps.internal_execution_compatible with (tp := tpc); eauto).
    specialize (Htsim pfci' HmemCompC').
    destruct Htsim.
    clear - Hexec code_eq0 Hexternal Hin.
    unfold getStepType in Hexternal.
    eapply internal_execution_result_type with (cnti' := pfci') in Hexec; eauto.
    unfold getStepType in Hexec.
    apply ctlType_inj in code_eq0.
    rewrite Hexternal in code_eq0.
    auto.
  Qed.

  (** Simulation between the two machines implies safety*)
  Lemma fine_safe:
    forall tpf tpc mf mc (g fg : memren) fp (xs : Sch) sched
      (Hsim: sim tpc mc tpf mf xs g fg fp (S (size sched))),
      fsafe tpf mf sched (S (size sched)).
  Proof.
    intros.
    generalize dependent xs.
    generalize dependent mf.
    generalize dependent tpf.
    generalize dependent fp.
    generalize dependent tpc.
    generalize dependent mc.
    generalize dependent g.
    induction sched as [|i sched]; intros; simpl; auto.
    econstructor; simpl; eauto.
    destruct (containsThread_dec i tpf) as [cnti | invalid].
    - (** By case analysis on the step type *)
      destruct (getStepType cnti) eqn:Htype.
      + pose proof (sim_internal [::] cnti Htype Hsim) as
            (tpf' & m' & fp' & tr' & Hstep & Hsim').
        specialize (Hstep sched).
        specialize (IHsched _ _ _ _ _ _ _ Hsim').
        econstructor 3; simpl; eauto.
      + assert (~ List.In i xs)
          by (eapply at_external_not_in_xs; eauto).
        pose proof (sim_external [::] cnti Htype H Hsim) as Hsim'.
        destruct Hsim' as (? & ? & ? & ? & ? & ? & tr' & Hstep & Hsim'').
        specialize (IHsched _ _ _ _ _ _ _ Hsim'').
        specialize (Hstep sched).
        econstructor 3; simpl; eauto.
      + pose proof (sim_halted [::] cnti Htype Hsim) as Hsim'.
        destruct Hsim' as (tr' & Hstep & Hsim'').
        specialize (IHsched _ _ _ _ _ _ _ Hsim'').
        specialize (Hstep sched).
        econstructor 3;
          eauto.
      + pose proof (sim_suspend [::] cnti Htype Hsim) as
            (? & ? & tpf' & m' & ? & ? & tr' & Hstep & Hsim').
        specialize (IHsched _ _ _ _ _ _ _ Hsim').
        specialize (Hstep sched).
        econstructor 3; simpl; eauto.
    -  pose proof (sim_fail [::] invalid Hsim) as
          (tr' & Hstep & Hsim').
       specialize (IHsched _ _ _ _ _ _ _ Hsim').
       specialize (Hstep sched).
       econstructor 3; eauto.
       Unshelve. eapply [::].
  Qed.

  (** *** Safety preservation for the FineConc machine starting from the initial state*)
  Theorem init_fine_safe:
    forall U tpf m
      (Hmem: init_mem = Some m)
      (Hinit: tpf_init f arg = Some (U, [::], tpf))
      (ARG: valid_val_list (id_ren m) arg),
    forall (sched : Sch),
      fsafe tpf (diluteMem m) sched (size sched).+1.
  Proof.
    intros.
    assert (Hsim := init_sim (size sched).+1 ARG Hinit Hinit Hmem).
    clear - Hsim.
    eapply fine_safe; now eauto.
  Qed.

  End Safety.
End FineConcSafe.






