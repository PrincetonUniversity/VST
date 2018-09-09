(** * Definitions and properties of machine executions *)
Require Import compcert.lib.Axioms.

Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.event_semantics.

Require Import VST.concurrency.common.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.permjoin_def.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.memory_lemmas.
(* Require Import VST.concurrency.common.ClightSemanticsForMachines. *)
Require Import VST.concurrency.common.dry_context.
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.dry_machine_step_lemmas.
Require Import VST.concurrency.common.erased_machine.
Require Import VST.concurrency.common.tactics.
Require Import compcert.lib.Coqlib.
Require Import VST.msl.Coqlib2.
Import Tactics.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module Executions.

  Import  HybridMachine.DryHybridMachine HybridMachineSig StepLemmas StepType ThreadPool AsmContext.
  Import event_semantics threads_lemmas.
  Import Events.

  Section Executions.

    Context
      {Sem : Semantics}
      {initU : seq.seq nat}
      {SemAx : CoreLanguage.SemAxioms}
      {SemD : CoreLanguage.SemDet}
      {DilMem : DiluteMem}
      {Res: Resources}.
    
    (* Existing Instance FineDilMem. *)
    Existing Instance HybridFineMachine.scheduler.
    Existing Instance OrdinalPool.OrdinalThreadPool.
    Context {Hbs : MachineSig}.

    (** Reflexive-transitive closure of machine step relation*)
    Inductive multi_step :
      MachState -> mem -> MachState -> mem -> Prop :=
    | Step_refl : forall ms (m : mem),
        multi_step ms m ms m
    | Step_trans : forall i U U'
                     (tp tp' tp'' : t)
                     tr tr' tr''
                     (m m' m'' : mem),
        MachStep (i :: U, tr, tp) m (U, tr ++ tr', tp') m' ->
        multi_step (U, tr ++ tr', tp') m' (U', tr ++ tr' ++ tr'', tp'') m'' ->
        multi_step (i :: U,tr,tp) m (U',tr ++ tr' ++ tr'',tp'') m''.

    (** Complete executions (until the schedule is empty) of the FineConc machine*)
    Inductive fine_execution :
      MachState -> mem -> MachState -> mem -> Prop :=
    | fine_completed : forall ms (m : mem),
        halted_machine ms ->
        fine_execution ms m ms m
    | fine_exec : forall i U U'
                    tp tp' tp''
                    tr tr' tr''
                    (m m' m'' : mem),
        MachStep (i :: U, tr, tp) m (U, tr ++ tr', tp') m' ->
        fine_execution (U, tr ++ tr', tp') m' (U', tr ++ tr' ++ tr'', tp'') m'' ->
        fine_execution (i :: U,tr,tp) m (U',tr ++ tr' ++ tr'',tp'') m''.

    (** ** Generic Properties of executions and steps *)

    (** Connection between [multi_step] and [fine_execution]*)
    Lemma fine_execution_multi_step:
      forall U  tr tr' tp m tp' m',
        fine_execution (U, tr, tp) m ([::], tr', tp') m' ->
        multi_step (U, tr, tp) m ([::], tr', tp') m'.
    Proof.
      intros.
      induction H;
        econstructor;
        now eauto.
    Qed.

    (** [fine_execution] has empty schedules*)
    Lemma fine_execution_schedule:
      forall U U' tr tr' tp m tp' m',
        fine_execution (U, tr, tp) m (U', tr', tp') m' ->
        U' = [::].
    Proof.
      intro U.
      induction U; intros.
      - inversion H;
          reflexivity.
      - inversion H; subst.
        + simpl in H6.
            by exfalso.
        + eapply IHU.
          eapply H10.
    Qed.

    (** A property of steps is that any sequence of events added by
    one external step is a singleton *)
    Lemma step_ext_trace:
      forall a U
        (i : nat) tr tr' tp tp'
        (m m' : mem) (ev : machine_event),
        is_external ev ->
        nth_error tr' i = Some ev ->
        MachStep ((a :: U)%SEQ, tr, tp) m
                 (U, tr ++ tr', tp') m' ->
        tr' = [:: ev].
    Proof.
      intros.
      inversion H1; subst;
        simpl in *;
        try match goal with
            | [H: ?X = app ?X ?Y |- _] =>
              rewrite <- app_nil_r in H at 1;
                apply app_inv_head in H
            end; subst;
          try match goal with
              | [H: nth_error [::] _ = _ |- _] =>
                rewrite nth_error_nil in H;
                  discriminate
              end.
      apply app_inv_head in H8.
      subst.
      rewrite list_map_nth in H0.
      destruct (nth_error ev0 i); simpl in H0; try discriminate.
      inv H0.
      simpl in H. by exfalso.
      apply app_inv_head in H8. subst.
      apply nth_error_In in H0. inversion H0; subst; auto.
      simpl in H2. by exfalso.
    Qed.

    Lemma step_event_tid:
      forall U tr tp m U' tr' tp' m'
        (Hstep: MachStep (U, tr, tp) m
                         (U', tr ++ tr', tp') m'),
      forall ev ev', List.In ev tr' ->
                List.In ev' tr' ->
                thread_id ev = thread_id ev'.
    Proof.
      intros.
      inv Hstep; simpl in *;
        try (apply app_eq_refl_nil in H6; subst);
        simpl in H, H0;
        try (by exfalso);
        apply app_inv_head in H7; subst.
      eapply in_map_iff in H.
      destruct H as (? & ? & ?).
      eapply in_map_iff in H0.
      destruct H0 as (? & ? & ?); subst.
      reflexivity.
      simpl in H, H0; destruct H, H0; try (by exfalso);
        subst; reflexivity.
    Qed.

    Lemma step_trace_monotone:
      forall U tp m tr U' tp' m' tr'
        (Hstep: MachStep (U, tr, tp) m
                         (U', tr', tp') m'),
      exists tr'',
        tr' = tr ++ tr''.
    Proof.
      intros.
      inv Hstep; simpl in *; subst;
        try (exists [::]; rewrite app_nil_r; reflexivity);
        eexists; reflexivity.
    Qed.

    Lemma multi_step_trace_monotone:
      forall U tr tp m U' tr' tp' m'
        (Hexec: multi_step (U, tr, tp) m (U', tr', tp') m'),
      exists tr'',
        tr' = tr ++ tr''.
    Proof.
      induction U; intros.
      - inv Hexec. exists [::]. rewrite app_nil_r. reflexivity.
      - inv Hexec. exists [::]. rewrite app_nil_r. reflexivity.
        eapply step_trace_monotone in H8.
        destruct H8 as [tr''0 H8].
        apply app_inv_head in H8; subst.
        eapply IHU in H9.
        now eauto.
    Qed.

    (** Decomposing steps based on an external event*)
    Lemma multi_step_inv_ext:
      forall U U' i tr tr' tp m tp' m' ev
        (Hext: is_external ev)
        (Hi: nth_error tr' i = Some ev)
        (Hexec: multi_step (U, tr, tp) m (U', tr ++ tr', tp') m'),
      exists U'' U''' tp'' m'' tr'' tp''' m''',
        multi_step (U, tr, tp) m (U'', tr ++ tr'', tp'') m'' /\
        MachStep (U'', tr ++ tr'', tp'') m''
                 (U''', tr ++ tr'' ++ [:: ev], tp''') m''' /\
        multi_step (U''', tr ++ tr'' ++ [:: ev], tp''') m'''
                   (U', tr ++ tr', tp') m' /\
        length tr'' = i.
    Proof.
      intros U.
      induction U; intros.
      - inversion Hexec. simpl in *.
        apply app_eq_refl_nil in H3. subst.
        destruct i; simpl in Hi; discriminate.
      - inversion Hexec.
        + rewrite <- app_nil_r in H3 at 1.
          apply app_inv_head in H3; subst.
          rewrite nth_error_nil in Hi. discriminate.
        + subst.
          apply app_inv_head in H6. subst.
          (* need a case analysis on whether it belongs on the first list or not*)
          destruct (i < length tr'0)%nat eqn:Hlt.
          * erewrite nth_error_app1 in Hi by ssromega.
            exists (a :: U), U, tp, m, [::], tp'0, m'0.
            assert (tr'0 = [:: ev]) by (eapply step_ext_trace; eauto).
            subst.
            split. rewrite app_nil_r.
            econstructor.
            split. rewrite app_nil_r.
            simpl. eauto.
            split; simpl; eauto.
            destruct i; simpl in *; auto;
              ssromega.
          * erewrite nth_error_app2 in Hi by ssromega.
            specialize (IHU U' _ (tr ++ tr'0) tr'' tp'0 m'0 tp' m' _ Hext Hi).
            rewrite <- app_assoc in IHU.
            specialize (IHU H9).
            destruct IHU as (U'' & U''' & tp'' & m'' & tr''0 & tp''' & m'''
                             & Hexec0' & Hstep & Hexec''' & Hnth).
            exists U'', U''', tp'', m'', (tr'0 ++ tr''0), tp''', m'''.
            split.
            rewrite <- app_assoc in Hexec0'.
            econstructor; eauto.
            split.
            rewrite <- app_assoc.
            repeat rewrite <- app_assoc in Hstep.
            eauto.
            rewrite <- app_assoc.
            rewrite <- app_assoc in Hexec'''.
            split. eauto.
            rewrite app_length.
            rewrite Hnth.
            ssromega.
    Qed.

    (** Decomposing steps on any kind of event. This
    theorem is stronger than the previous one *)
    Lemma multi_step_inv:
      forall U U' i tr tr' tp m tp' m' ev
        (Hi: nth_error tr' i = Some ev)
        (Hexec: multi_step (U, tr, tp) m (U', tr ++ tr', tp') m'),
      exists U'' U''' tp'' m'' tr'' pre_ev post_ev  tp''' m''',
        multi_step (U, tr, tp) m (U'', tr ++ tr'', tp'') m'' /\
        MachStep (U'', tr ++ tr'', tp'') m''
                 (U''', tr ++ tr'' ++ pre_ev ++ [:: ev] ++ post_ev, tp''') m''' /\
        multi_step (U''', tr ++ tr'' ++ pre_ev ++ [:: ev] ++ post_ev , tp''') m'''
                   (U', tr ++ tr', tp') m' /\
        length (tr'' ++ pre_ev) = i.
    Proof.
      intros U.
      induction U; intros.
      - inversion Hexec. simpl in *.
        apply app_eq_refl_nil in H3. subst.
        destruct i; simpl in Hi; discriminate.
      - inversion Hexec.
        + rewrite <- app_nil_r in H3 at 1.
          apply app_inv_head in H3; subst.
          rewrite nth_error_nil in Hi. discriminate.
        + subst.
          apply app_inv_head in H6. subst.
          (* need a case analysis on whether it belongs on the first list or not*)
          destruct (i < length tr'0)%nat eqn:Hlt.
          * erewrite nth_error_app1 in Hi by ssromega.
            eapply nth_error_split in Hi.
            destruct Hi as (l1 & l2 & Htr'0 & Hl1).
            exists (a :: U), U, tp, m, [::], l1, l2, tp'0, m'0.
            subst.
            split. rewrite app_nil_r.
            econstructor.
            split. rewrite app_nil_r.
            simpl. eauto.
            split; simpl; eauto.
          * erewrite nth_error_app2 in Hi by ssromega.
            specialize (IHU U' _ (tr ++ tr'0) tr'' tp'0 m'0 tp' m' _ Hi).
            rewrite <- app_assoc in IHU.
            specialize (IHU H9).
            destruct IHU as (U'' & U''' & tp'' & m'' & tr''0 & pre_ev & post_ev
                             & tp''' & m''' & Hexec0' & Hstep & Hexec''' & Hnth).
            exists U'', U''', tp'', m'', (tr'0 ++ tr''0), pre_ev, post_ev, tp''', m'''.
            split.
            rewrite <- app_assoc in Hexec0'.
            econstructor; eauto.
            split.
            rewrite <- app_assoc.
            repeat rewrite <- app_assoc in Hstep.
            eauto.
            rewrite <- app_assoc.
            rewrite <- app_assoc in Hexec'''.
            split. eauto.
            do 2 rewrite app_length.
            rewrite <- plus_assoc.
            rewrite app_length in Hnth.
            rewrite Hnth.
            ssromega.
    Qed.

    Lemma step_sched_inv:
      forall i U tp m tr U' tp' m' tr'
        (Hstep: MachStep (i :: U, tr, tp) m
                         (U', tr', tp') m'),
        U' = U.
    Proof.
      intros.
      inversion Hstep; subst; auto.
    Qed.

    Lemma multi_step_snoc:
      forall U U' U'' tr tr' tr'' tp m tp' m' tp'' m''
        (Hexec: multi_step (U, tr, tp) m (U', tr ++ tr', tp') m')
        (Hstep: MachStep (U', tr ++ tr', tp') m' (U'', tr ++ tr' ++ tr'', tp'') m''),
        multi_step (U, tr, tp) m (U'', tr ++ tr' ++ tr'', tp'') m''.
    Proof.
      induction U; intros.
      - inversion Hexec.
        rewrite <- app_nil_r in H3 at 1.
        apply app_inv_head in H3. subst.
        simpl in *. erewrite app_nil_r in *.
        inversion Hstep; simpl in *;
          try discriminate.
      - inversion Hexec.
        + rewrite <- app_nil_r in H3 at 1.
          apply app_inv_head in H3. subst.
          erewrite app_nil_r in *.
          simpl in *.
          assert (U = U'')
            by (erewrite step_sched_inv by eauto; reflexivity); subst.
          replace (tr ++ tr'') with (tr ++ tr'' ++ [::])
            by (rewrite app_nil_r; auto).
          econstructor; eauto.
          rewrite app_nil_r.
          now econstructor.
        + subst.
          apply app_inv_head in H6. subst.
          clear Hexec.
          rewrite <- app_assoc.
          econstructor.
          eauto.
          specialize (IHU U' U'' (tr ++ tr'0) tr''0 tr'' tp'0 m'0 tp' m' tp'' m'').
          rewrite app_assoc.
          eapply IHU.
          rewrite <- app_assoc.
          now eassumption.
          rewrite! app_assoc in Hstep.
          rewrite! app_assoc.
          assumption.
    Qed.

    (** The trace is irrelevant to further execution of the
  machine. It's just a history of the memory operations *)
    Lemma step_trace_irr:
      forall U i tp m tp' m' tr tr'
        (Hstep: MachStep (i :: U, tr, tp) m (U, tr', tp') m'),
      forall tr'', exists ev,
          MachStep (i :: U, tr'', tp) m (U, tr'' ++ ev, tp') m'.
    Proof.
      intros.
      inversion Hstep; subst; simpl in *; subst; inv HschedN; pf_cleanup.
      - exists [::]; erewrite cats0; econstructor; simpl; eauto.
      - exists [::]; erewrite cats0; econstructor 2; simpl; eauto.
      - exists (map [eta Events.internal tid] ev); econstructor 3; simpl; eauto.
      - exists [::]; erewrite cats0; econstructor 4; simpl; eauto.
      - exists [:: Events.external tid ev]; econstructor 5; simpl; eauto.
      - exists [::]; erewrite cats0; econstructor 6; simpl; eauto.
    Qed.

    Lemma  multi_step_contra:
      forall U U' tr tp m tr' tp' m'
        (HU': U' <> [::])
        (Hexec: multi_step (U, tr, tp) m (U' ++ U, tr', tp') m'),
        False.
    Proof.
      induction U; intros.
      - rewrite app_nil_r in Hexec.
        inversion Hexec.
        subst. now eauto.
      - inversion Hexec.
        + destruct U'; eauto.
          inversion H2.
          assert (length U = length ((U' ++ (n :: U))%list))
            by (erewrite <- H7; reflexivity).
          rewrite app_length in H5. clear - H5.
          simpl in H5. ssromega.
        + subst.
          eapply IHU with (U' := (U' ++ [:: a])).
          destruct U'; simpl; intros Hcontra; inversion Hcontra.
          replace ((U' ++ [:: a]) ++ U) with (U' ++ (a :: U)).
          eauto.
          rewrite <- app_assoc. simpl. reflexivity.
    Qed.

    Lemma  multi_step_refl:
      forall U tr tp m tr' tp' m'
        (Hexec: multi_step (U, tr, tp) m (U, tr', tp') m'),
        tp = tp' /\ m = m' /\ tr = tr'.
    Proof.
      induction U; intros.
      - inversion Hexec; subst; auto.
      - inversion Hexec; subst; auto.
        replace (a :: U) with ([:: a] ++ U) in H9
          by (reflexivity).
        exfalso.
        eapply multi_step_contra in H9; eauto.
        intros Hcontra; inv Hcontra.
    Qed.
  End Executions.

  Section FineGrainedExecutions.

    Context
      {Sem : Semantics}
      {initU : seq.seq nat}
      {SemAx : CoreLanguage.SemAxioms}.

    Existing Instance dryResources.
    Existing Instance HybridFineMachine.scheduler.
    Existing Instance OrdinalPool.OrdinalThreadPool.
    Existing Instance DryHybridMachineSig.
    Existing Instance FineDilMem.
    Existing Instance dryFineMach.

     Lemma step_event_sched:
      forall U tr tp m U' ev tr_pre tr_post tp' m'
        (Hstep: MachStep (U, tr, tp) m
                         (U', tr ++ tr_pre ++ [:: ev] ++ tr_post, tp') m'),
        U = (thread_id ev) :: U'.
    Proof.
      intros.
      inv Hstep; simpl in *;
        try (apply app_eq_refl_nil in H4; exfalso;
             eapply app_cons_not_nil; by eauto);
        apply app_inv_head in H5.
      inv Htstep.
      pose proof (in_map_iff ([eta internal tid]) ev0 ev) as HIn.
      rewrite H5 in HIn.
      erewrite in_app in HIn.
      destruct (HIn.1 ltac:(right; simpl; eauto)) as [? [? ?]].
      subst.
      simpl.
      destruct U; simpl in HschedN; inv HschedN.
      reflexivity.
      destruct tr_pre; [| destruct tr_pre];
        simpl in H5; inv H5.
      destruct U; simpl in HschedN; inv HschedN.
      reflexivity.
    Qed.

    Lemma step_ev_contains:
      forall U tr tp m U' ev
        tr_pre tr_post tp' m'
        (Hstep: MachStep (U, tr, tp) m
                         (U', tr ++ tr_pre ++ [:: ev] ++ tr_post, tp') m'),
        containsThread tp (thread_id ev) /\ containsThread tp' (thread_id ev).
    Proof.
      intros.
      pose proof (step_event_sched _ _ _ Hstep) as Heq.
      inv Hstep; simpl in *;
        try (apply app_eq_refl_nil in H4; exfalso;
             eapply app_cons_not_nil; by eauto);
        try subst.
      inv HschedN.
      inv Htstep;
        split; eauto.
      inv HschedN.
      inv Htstep; split; eauto.
      apply OrdinalPool.cntAdd.
      apply OrdinalPool.cntUpdate.
      assumption.
    Qed.

        Lemma multi_step_mem_compatible :
      forall U tr tp m U' tr' tp' m'
        (Hexec: multi_step (U, tr, tp) m (U', tr', tp') m'),
        mem_compatible tp m \/ tp = tp' /\ m = m' /\ U = U' /\ tr = tr'.
    Proof.
      intros.
      inversion Hexec; subst.
      right; auto.
      eapply step_mem_compatible in H7.
      left; auto.
    Qed.

    Lemma multi_step_invariant :
      forall U tr tp m U' tr' tp' m'
        (Hexec: multi_step (U, tr, tp) m (U', tr', tp') m'),
        invariant tp \/ tp = tp' /\ m = m' /\ U = U' /\ tr = tr'.
    Proof.
      intros.
      inversion Hexec; subst.
      right; auto.
      eapply step_invariant in H7.
      left; auto.
    Qed.

    Lemma multi_step_containsThread :
      forall U tp tr m U' tp' tr' m' i
        (Hexec: multi_step (U, tr, tp) m (U', tr', tp') m'),
        containsThread tp i -> containsThread tp' i.
    Proof.
      intros U.
      induction U. intros.
      inversion Hexec; subst; simpl in *; auto; try discriminate.
      intros.
      inversion Hexec; subst; eauto.
      eapply step_containsThread with (j := i) in H9;
        now eauto.
    Qed.

    Lemma multi_step_valid_block:
      forall U tr tp m U' tr' tp' m' b
        (Hexec: multi_step (U, tr, tp) m (U', tr', tp') m')
        (Hvalid: Mem.valid_block m b),
        Mem.valid_block m' b.
    Proof.
      intros.
      induction Hexec.
      assumption.
      eapply IHHexec.
      eapply (fstep_valid_block (initU := initU)); eauto.
    Qed.


    (** A location that the machine has no access to (i.e. the permission is
  empty in all its resources) *)
    Inductive deadLocation tp m b ofs : Prop :=
    | Dead: forall
        (Hvalid: Mem.valid_block m b)
        (Hthreads: forall i (cnti: containsThread tp i),
            (getThreadR cnti).1 !! b ofs = None /\ (getThreadR cnti).2 !! b ofs = None)
        (Hresources: forall l pmap,
            lockRes tp l = Some pmap ->
            pmap.1 !! b ofs = None /\ pmap.2 !! b ofs = None),
        deadLocation tp m b ofs.

    Lemma updThreadC_deadLocation:
      forall tp m b ofs i (cnti: containsThread tp i) c,
        deadLocation tp m b ofs ->
        deadLocation (updThreadC cnti c) m b ofs.
    Proof.
      intros.
      inversion H.
      constructor; eauto.
    Qed.

    Lemma step_deadLocation:
      forall U U' tr tp m tr' tp' m' b ofs
        (Hdead: deadLocation tp m b ofs)
        (Hstep: MachStep (U, tr, tp) m (U',tr ++ tr', tp') m'),
        deadLocation tp' m' b ofs.
    Proof.
      intros;
        inv Hstep; simpl in *;
          try apply app_eq_refl_nil in H4;
          try inv Htstep;
          destruct U; inversion HschedN; subst; pf_cleanup;
            try (eapply updThreadC_deadLocation; eauto);
            auto 1.
      - (*initial core case *)
        inversion Hdead.
        inv Hperm.
        econstructor.
        + eapply CoreLanguage.initial_core_validblock in Hinitial; eauto.
        + intros.
          destruct (i == tid) eqn:Heq; move/eqP:Heq=>Heq.
          * subst.
            pf_cleanup.
            rewrite gssThreadRes.
            simpl.
            destruct (Hthreads _ ctn).
            eapply CoreLanguage.initial_core_decay in Hinitial.
            destruct (Hinitial b ofs) as [_ Hsame].
            rewrite getCurPerm_correct. unfold permission_at.
            specialize (Hsame Hvalid).
            erewrite <- Hsame.
            split; auto.
            pose proof (restrPermMap_Cur (compat_th _ _ Hcmpt ctn).1 b ofs) as Hperm.
            unfold permission_at in Hperm.
            rewrite Hperm.
            assumption.
          * rewrite! gsoThreadRes;
              now auto.
        + intros.
          rewrite gsoThreadLPool in H.
          now eauto.
      - apply app_inv_head in H5; subst.
        inversion Hdead.
        econstructor.
        + eapply CoreLanguage.ev_step_validblock in Hcorestep; eauto.
        + intros.
          destruct (i == tid) eqn:Heq; move/eqP:Heq=>Heq.
          * subst.
            pf_cleanup.
            rewrite gssThreadRes.
            simpl.
            destruct (Hthreads _ Htid).
            eapply CoreLanguage.ev_step_decay in Hcorestep.
            destruct (Hcorestep b ofs) as [_ Hsame].
            rewrite getCurPerm_correct. unfold permission_at.
            destruct (Hsame Hvalid) as [Heq | Heq];
              specialize (Heq Cur);
              [rewrite Heq.2 | rewrite <- Heq]; split;
                auto.
            pose proof (restrPermMap_Cur (compat_th _ _ Hcmpt Htid).1 b ofs) as Hperm.
            unfold permission_at in Hperm.
            rewrite Hperm.
            assumption.
          * rewrite! gsoThreadRes;
              now auto.
        + intros.
          rewrite gsoThreadLPool in H.
          now eauto.
      - inversion Hdead.
        econstructor; eauto using Mem.store_valid_block_1.
        + intros.
          destruct (tid == i) eqn:Heq; move/eqP:Heq=>Heq.
          * subst.
            specialize (Hangel1 b ofs).
            specialize (Hangel2 b ofs).
            specialize (Hthreads _ Htid).
            specialize (Hresources _ _ HisLock).
            erewrite Hthreads.1, Hresources.1 in Hangel1.
            erewrite Hthreads.2, Hresources.2 in Hangel2.
            rewrite gLockSetRes gssThreadRes.
            simpl.
            inversion Hangel1; inversion Hangel2;
              split; now auto.
          * rewrite! gLockSetRes gsoThreadRes;
              now auto.
        + intros.
          destruct (EqDec_address (b0, Ptrofs.intval ofs0) l); subst.
          * rewrite gssLockRes in H. inv H.
            simpl; split; rewrite empty_map_spec;
              now auto.
          * rewrite gsoLockRes in H; eauto.
            rewrite gsoThreadLPool in H; eauto.
      - inversion Hdead.
        econstructor; eauto using Mem.store_valid_block_1.
        + intros.
          destruct (tid == i) eqn:Heq; move/eqP:Heq=>Heq.
          * subst.
            specialize (Hangel1 b ofs).
            specialize (Hangel2 b ofs).
            specialize (Hthreads _ Htid).
            specialize (Hresources _ _ HisLock).
            erewrite Hthreads.1 in Hangel1.
            erewrite Hthreads.2 in Hangel2.
            rewrite gLockSetRes gssThreadRes.
            simpl.
            apply permjoin_order in Hangel1.
            apply permjoin_order in Hangel2.
            simpl in Hangel1, Hangel2.
            repeat match goal with
                   | [H: context[match ?X with _ => _ end] |- _] =>
                     destruct X
                   | [H: _ /\ _ |- _] => destruct H
                   end;
              try (by exfalso); auto.
          * rewrite! gLockSetRes gsoThreadRes;
              now auto.
        + intros.
          destruct (EqDec_address (b0, Ptrofs.intval ofs0) l); subst.
          * rewrite gssLockRes in H.
            inv H.
            specialize (Hangel1 b ofs).
            specialize (Hangel2 b ofs).
            specialize (Hthreads _ Htid).
            specialize (Hresources _ _ HisLock).
            erewrite Hthreads.1 in Hangel1.
            erewrite Hthreads.2 in Hangel2.
            simpl.
            apply permjoin_order in Hangel1.
            apply permjoin_order in Hangel2.
            simpl in Hangel1, Hangel2.
            destruct Hangel1 as [_ Hangel1];
              destruct Hangel2 as [_ Hangel2].

            repeat match goal with
                   | [H: context[match ?X with _ => _ end] |- _] =>
                     destruct X eqn:?
                   end;
              try (by exfalso); auto.
          * rewrite gsoLockRes in H; eauto.
            rewrite gsoThreadLPool in H; eauto.
      - inversion Hdead.
        econstructor; eauto.
        intros i cnti'.
        destruct (cntAdd' _ _ _ cnti') as [[cnti ?] | Heq].
        + rewrite gsoAddRes.
          destruct (tid == i) eqn:Heq; move/eqP:Heq=>Heq.
          * subst.
            rewrite gssThreadRes.
            specialize (Hangel1 b ofs).
            specialize (Hangel2 b ofs).
            specialize (Hthreads _ Htid).
            erewrite Hthreads.1 in Hangel1.
            erewrite Hthreads.2 in Hangel2.
            simpl.
            apply permjoin_order in Hangel1.
            apply permjoin_order in Hangel2.
            simpl in Hangel1, Hangel2.
            repeat match goal with
                   | [H: context[match ?X with _ => _ end] |- _] =>
                     destruct X
                   | [H: _ /\ _ |- _] => destruct H
                   end;
              try (by exfalso); auto.
          * rewrite! gsoThreadRes;
              now auto.
        + subst.
          rewrite gssAddRes.
          specialize (Hangel1 b ofs).
          specialize (Hangel2 b ofs).
          specialize (Hthreads _ Htid).
          erewrite Hthreads.1 in Hangel1.
          erewrite Hthreads.2 in Hangel2.
          simpl.
          apply permjoin_order in Hangel1.
          apply permjoin_order in Hangel2.
          simpl in Hangel1, Hangel2.
          repeat match goal with
                 | [H: context[match ?X with _ => _ end] |- _] =>
                   destruct X
                 | [H: _ /\ _ |- _] => destruct H
                 end;
            try (by exfalso); auto.
          unfold latestThread;
            reflexivity.
      - inversion Hdead.
        econstructor; eauto using Mem.store_valid_block_1.
        + intros.
          destruct (tid == i) eqn:Heq; move/eqP:Heq=>Heq.
          * subst.
            rewrite gLockSetRes gssThreadRes.
            rewrite <- Hdata_perm, <- Hlock_perm.
            destruct (Pos.eq_dec b b0); subst.
            destruct (Intv.In_dec ofs (Ptrofs.intval ofs0, (Ptrofs.intval ofs0) + lksize.LKSIZE)%Z).
            exfalso.
            specialize (Hfreeable _ i0).
            unfold Mem.perm in Hfreeable.
            specialize (Hthreads _ Htid).
            rewrite <- restrPermMap_Cur with (Hlt := (compat_th _ _ Hcmpt Htid).1) in Hthreads.
            unfold permission_at in Hthreads.
            rewrite Hthreads.1 in Hfreeable.
            simpl in Hfreeable; now auto.
            eapply Intv.range_notin in n; try (simpl; lksize.lkomega).
            erewrite! setPermBlock_other_1 by eauto.
            now eauto.
            erewrite! setPermBlock_other_2 by eauto.
            now eauto.
          * rewrite! gLockSetRes gsoThreadRes;
              now auto.
        + intros.
          destruct (EqDec_address (b0, Ptrofs.intval ofs0) l); subst.
          * rewrite gssLockRes in H.
            inv H; rewrite empty_map_spec;
              split; reflexivity.
          * rewrite gsoLockRes in H; auto;
              rewrite gsoThreadLPool in H;
              now eauto.
      - inversion Hdead.
        econstructor; eauto using Mem.store_valid_block_1.
        + intros.
          destruct (tid == i) eqn:Heq; move/eqP:Heq=>Heq.
          * subst.
            rewrite gRemLockSetRes gssThreadRes.
            rewrite <- Hdata_perm, <- Hlock_perm.
            destruct (Pos.eq_dec b b0); subst.
            destruct (Intv.In_dec ofs (Ptrofs.intval ofs0, (Ptrofs.intval ofs0) + lksize.LKSIZE)%Z).
            exfalso.
            specialize (Hfreeable _ i0).
            unfold Mem.perm in Hfreeable.
            specialize (Hthreads _ Htid).
            rewrite <- restrPermMap_Cur with (Hlt := (Hcmpt i Htid).2) in Hthreads.
            unfold permission_at in Hthreads.
            rewrite Hthreads.2 in Hfreeable.
            simpl in Hfreeable; now auto.
            eapply Intv.range_notin in n; try (simpl; lksize.lkomega).
            erewrite! setPermBlock_other_1, setPermBlock_var_other_1 by eauto.
            now eauto.
            erewrite! setPermBlock_other_2, setPermBlock_var_other_2 by eauto.
            now eauto.
          * rewrite! gRemLockSetRes gsoThreadRes;
              now auto.
        + intros.
          destruct (EqDec_address (b0, Ptrofs.intval ofs0) l); subst.
          * rewrite gsslockResRemLock in H.
            discriminate.
          * rewrite gsolockResRemLock in H; auto;
              rewrite gsoThreadLPool in H;
              now eauto.
    Qed.

    Lemma multi_step_deadLocation:
      forall U U' tr tp m tr' tp' m' b ofs
        (Hdead: deadLocation tp m b ofs)
        (Hexec: multi_step (U, tr, tp) m (U',tr ++ tr', tp') m'),
        deadLocation tp' m' b ofs.
    Proof.
      induction U; intros.
      - inversion Hexec. subst tp' m'.
        assumption.
      - inversion Hexec.
        eapply app_eq_refl_nil in H3; subst.
        assumption.
        apply app_inv_head in H6; subst.
        eapply step_deadLocation in H8; eauto.
        eapply IHU with (tr := tr ++ tr'0); eauto.
        erewrite <- app_assoc. now eauto.
    Qed.

    (** ** Properties of specific stepss and executions *)

    (** After a step that generates a [mklock] event at [address] addr, addr
  will be in the [lockRes] and thread i will have lock permission on addr*)
    Lemma Mklock_lockRes:
      forall i U tr tp m tp' m' addr
        (Hstep: MachStep (i :: U, tr, tp) m
                         (U, tr ++ [:: external i (Events.mklock addr)], tp') m'),
        lockRes tp' addr /\
        forall (cnti': containsThread tp' i) ofs,
          Intv.In ofs (addr.2, addr.2 + lksize.LKSIZE)%Z ->
          ((getThreadR cnti').2 !! (addr.1)) ofs = Some Writable.
    Proof.
      intros.
      inv Hstep; simpl in *;
        try (apply app_eq_refl_nil in H4; discriminate).
      apply app_inv_head in H5.
      destruct ev; simpl in *; discriminate.
      apply app_inv_head in H5;
        inv H5.
      (** case it's an external step that generates a mklock event*)
      inv Htstep.
      rewrite OrdinalPool.gsslockResUpdLock; split; auto.
      intros cnti'.
      rewrite OrdinalPool.gLockSetRes OrdinalPool.gssThreadRes.
      rewrite <- Hlock_perm.
      intros.
      erewrite setPermBlock_same by eauto.
      reflexivity.
    Qed.

    (** [True] whenever some resource in [tp] has above [Readable] lock-permission on [laddr]*)
    (* I could not prove the stronger version, where quantification happens inside each case*)
    Definition isLock tp laddr :=
      forall ofs, Intv.In ofs (laddr.2, laddr.2 + lksize.LKSIZE)%Z ->
             (exists i (cnti: containsThread tp i),
                 Mem.perm_order'' ((getThreadR cnti).2 !! (laddr.1) ofs) (Some Readable)) \/
             (exists laddr' rmap, lockRes tp laddr' = Some rmap /\
                             Mem.perm_order'' (rmap.2 !! (laddr.1) ofs) (Some Readable)).

    (** If no freelock event is generated by a step, locks are
    preserved*)
    Lemma remLockRes_Freelock:
      forall i U tr tr' tp m tp' m' addr
        (Hlock: lockRes tp addr)
        (HisLock: isLock tp addr)
        (Hstep: MachStep (i :: U, tr, tp) m
                         (U, tr ++ tr', tp') m')
        (Hev: forall u ev, nth_error tr' u = Some ev ->
                      action ev <> Freelock \/
                      location ev <> Some (addr, lksize.LKSIZE_nat)),
        lockRes tp' addr /\
        isLock tp' addr.
    Proof.
      intros.
      inv Hstep; simpl in *;
        try (inversion Htstep;
             subst tp');
        try (rewrite OrdinalPool.gsoThreadCLPool; auto);
        try (rewrite OrdinalPool.gsoThreadLPool; auto);
        try subst tp'0; try subst tp''.
      - (** initial core case *)
        split; auto.
        unfold isLock in *.
        inv HschedN.
        inv Hperm.
        intros ofs0 Hintv.
        destruct (HisLock ofs0 Hintv) as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
        + left.
          pose proof (cntUpdate (Krun c_new) (getCurPerm m'0, (getThreadR Htid).2) Htid cntj) as cntj'.
          exists j, cntj'.
          destruct (tid == j) eqn:Hij;
            move/eqP:Hij=>Hij;
                           subst;
                           [rewrite gssThreadRes | erewrite @gsoThreadRes with (cntj := cntj) by eauto];
                           simpl; pf_cleanup; auto.
        + right.
          exists laddr', rmap'.
          rewrite gsoThreadLPool.
          split; eauto.
      - (** [threadStep] case*)
        split; auto.
        unfold isLock in *.
        inv HschedN.
        intros ofs0 Hintv.
        destruct (HisLock ofs0 Hintv) as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
        + left.
          pose proof (cntUpdate (Krun c') (getCurPerm m'0, (getThreadR Htid).2) Htid cntj) as cntj'.
          exists j, cntj'.
          destruct (tid == j) eqn:Hij;
            move/eqP:Hij=>Hij;
                           subst;
                           [rewrite gssThreadRes | erewrite @gsoThreadRes with (cntj := cntj) by eauto];
                           simpl; pf_cleanup; auto.
        + right.
          exists laddr', rmap'.
          rewrite gsoThreadLPool.
          split; eauto.
      - unfold isLock in *.
        inv HschedN.
        split.
        destruct (EqDec_address (b, Ptrofs.intval ofs) addr); subst.
        rewrite OrdinalPool.gssLockRes; auto.
        rewrite OrdinalPool.gsoLockRes; eauto.
        intros ofs0 Hintv.
        specialize (Hangel2 (addr.1) ofs0).
        apply permjoin_order in Hangel2.
        destruct Hangel2 as [Hlt1 Hlt2].
        destruct (HisLock ofs0 Hintv) as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
        + pose proof (cntUpdate (Kresume c Vundef) newThreadPerm Htid
                                (cntUpdateL (b, Ptrofs.intval ofs) (empty_map, empty_map) cntj)) as cntj'.
          destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij.
          * subst.
            left.
            exists j, cntj'.
            rewrite gLockSetRes gssThreadRes.
            pf_cleanup.
            eauto using po_trans.
          * left.
            exists j, cntj'.
            rewrite gLockSetRes.
            erewrite @gsoThreadRes with (cntj := cntj) by eauto.
            now eauto using po_trans.
        + destruct (EqDec_address (b, Ptrofs.intval ofs) laddr').
          * subst.
            left.
            pose proof (cntUpdate (Kresume c Vundef) newThreadPerm Htid
                                  (cntUpdateL (b, Ptrofs.intval ofs) (empty_map, empty_map) Htid)) as cnti'.
            exists tid, cnti'.
            rewrite gLockSetRes gssThreadRes.
            rewrite HisLock0 in Hres; inv Hres.
            eauto using po_trans.
          * right.
            exists laddr', rmap'.
            erewrite gsoLockRes by eauto.
            rewrite gsoThreadLPool.
            split; now eauto.
      - unfold isLock in *.
        inv HschedN.        split.
        destruct (EqDec_address (b, Ptrofs.intval ofs) addr); subst.
        rewrite OrdinalPool.gssLockRes; auto.
        rewrite OrdinalPool.gsoLockRes; eauto.
        intros ofs0 Hintv.
        specialize (Hangel2 (addr.1) ofs0).
        destruct (HisLock ofs0 Hintv) as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
        + destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij.
          * subst.
            pf_cleanup.
            apply permjoin_readable_iff in Hangel2.
            destruct (Hangel2.1 Hperm) as [Hperm' | Hperm'].
            left.
            exists j, cntj.
            rewrite gLockSetRes gssThreadRes.
            now eauto.
            right.
            exists (b, Ptrofs.intval ofs), virtueLP.
            rewrite gssLockRes.
            split;
              now eauto.
          * left.
            exists j, cntj.
            rewrite gLockSetRes.
            erewrite @gsoThreadRes with (cntj := cntj) by eauto.
            now eauto.
        + destruct (EqDec_address (b, Ptrofs.intval ofs) laddr').
          * subst.
            rewrite HisLock0 in Hres; inv Hres.
            destruct (Hrmap addr.1 ofs0) as [_ Hrmap2].
            rewrite Hrmap2 in Hperm.
            exfalso. simpl in Hperm.
            now assumption.
          * right.
            exists laddr', rmap'.
            erewrite gsoLockRes by eauto.
            rewrite gsoThreadLPool.
            split; now eauto.
      - unfold isLock in *.
        inv HschedN.
        split;
          first by (rewrite OrdinalPool.gsoAddLPool OrdinalPool.gsoThreadLPool;
                    assumption).
        intros ofs0 Hintv.
        specialize (Hangel2 (addr.1) ofs0).
        apply permjoin_readable_iff in Hangel2.
        destruct (HisLock ofs0 Hintv) as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
        + destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij.
          * subst.
            pf_cleanup.
            destruct (Hangel2.1 Hperm) as [Hperm' | Hperm'].
            left.
            exists (OrdinalPool.latestThread tp), (OrdinalPool.contains_add_latest (updThread cntj (Kresume c Vundef) threadPerm') (Vptr b ofs) arg newThreadPerm).
            erewrite gssAddRes by reflexivity.
            assumption.
            left.
            exists j, (cntAdd(resources:=dryResources) (Vptr b ofs) arg newThreadPerm cntj).
            rewrite @gsoAddRes gssThreadRes.
            assumption.
          * left.
            exists j, (cntAdd(resources:=dryResources) (Vptr b ofs) arg newThreadPerm cntj).
            rewrite @gsoAddRes.
            erewrite @gsoThreadRes with (cntj := cntj) by eauto.
            now eauto.
        + right.
          exists laddr', rmap'.
          rewrite gsoAddLPool gsoThreadLPool.
          split;
            now auto.
      - (** Makelock case*)
        inv HschedN.
        split.
        destruct (EqDec_address (b, Ptrofs.intval ofs) addr); subst.
        rewrite OrdinalPool.gssLockRes; auto.
        rewrite OrdinalPool.gsoLockRes; eauto.
        intros ofs0 Hintv.
        destruct (HisLock ofs0 Hintv) as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
        + left. exists j, cntj.
          rewrite gLockSetRes.
          destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij.
          * subst.
            pf_cleanup.
            rewrite gssThreadRes.
            rewrite <- Hlock_perm.
            destruct (setPermBlock_or (Some Writable) b (Ptrofs.intval ofs) (lksize.LKSIZE_nat) (getThreadR cntj).2 addr.1 ofs0)
              as [Heq | Heq];
              rewrite Heq; simpl; auto using perm_order.
          * rewrite gsoThreadRes;
              now auto.
        + assert ((b, Ptrofs.intval ofs) <> laddr')
            by (intros Hcontra; subst; congruence).
          right.
          exists laddr', rmap'.
          erewrite gsoLockRes by eauto.
          rewrite gsoThreadLPool.
          split; auto.
      - (** Interesting case: freelock *)
        unfold isLock in *.
        apply app_inv_head in H5; subst.
        specialize (Hev O (external tid (freelock (b, Ptrofs.intval ofs)))
                        ltac:(reflexivity)).
        simpl in Hev.
        destruct Hev; first by exfalso.
        rewrite OrdinalPool.gsolockResRemLock; [|intros Hcontra; subst; auto].
        rewrite OrdinalPool.gsoThreadLPool.
        split; auto.
        intros ofs0 Hintv.
        destruct (HisLock ofs0 Hintv) as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
        + left.
          exists j, cntj.
          rewrite gRemLockSetRes.
          destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij.
          * subst.
            pf_cleanup.
            rewrite gssThreadRes.
            rewrite <- Hlock_perm.
            assert (Hneq: b <> addr.1 \/ (b = addr.1) /\ ((ofs0 < (Ptrofs.intval ofs))%Z \/ (ofs0 >= (Ptrofs.intval ofs) + lksize.LKSIZE)%Z)).
            { destruct (Pos.eq_dec b (addr.1)); subst; auto.
              destruct addr as [b' ofs']; simpl;
                right; split; auto.
              simpl in His_lock, Hintv.
              assert (Hofs': (ofs' + lksize.LKSIZE <= Ptrofs.intval ofs \/ ofs' >= Ptrofs.intval ofs + lksize.LKSIZE)%Z).
              { destruct (zle (ofs' + lksize.LKSIZE)%Z (Ptrofs.intval ofs)).
                - left; auto.
                - destruct (zlt ofs' (Ptrofs.intval ofs + lksize.LKSIZE)%Z); eauto.
                  destruct (zlt ofs' (Ptrofs.intval ofs)).
                  + exfalso.
                    pose proof (lockRes_valid _ Hinv b' ofs') as Hvalid.
                    destruct (lockRes(ThreadPool := OrdinalPool.OrdinalThreadPool) tp (b', ofs')) eqn:Hlock'; auto.
                    specialize (Hvalid (Ptrofs.intval ofs)).
                    setoid_rewrite Hvalid in His_lock.
                    congruence.
                    omega.
                    setoid_rewrite Hlock' in Hlock; auto.
                  + exfalso.
                    pose proof (lockRes_valid _ Hinv b' (Ptrofs.intval ofs)) as Hvalid.
                    simpl in *.
                    rewrite His_lock in Hvalid.
                    specialize (Hvalid ofs').
                    erewrite Hvalid in Hlock.
                    now eauto.
                    assert (Hneq: Ptrofs.intval ofs <> ofs')
                      by (intros Hcontra; subst; apply H; auto).
                    clear - g l g0 Hneq.
                    omega.
              }
              unfold Intv.In in Hintv.
              simpl in Hintv.
              destruct Hofs'; omega.
            }
            destruct Hneq as [? | [? ?]]; subst;
              [rewrite setPermBlock_other_2 | rewrite setPermBlock_other_1];
              auto.
          * rewrite gsoThreadRes;
              now auto.
        + destruct (EqDec_address (b, Ptrofs.intval ofs) laddr').
          * subst.
            rewrite Hres in His_lock; inv His_lock.
            exfalso.
            destruct (Hrmap addr.1 ofs0) as [_ Hrmap2].
            rewrite Hrmap2 in Hperm.
            simpl in Hperm.
            now assumption.
          * right.
            exists laddr', rmap'.
            erewrite gsolockResRemLock;
              now auto.
      - split; assumption.
      - subst tp'; auto.
    Qed.

    (** If some address is a lock and there is no event of type Freelock at this
  address in some trace tr then the address is still a lock at the resulting
  state *)
    Lemma remLockRes_Freelock_execution:
      forall U U' tr tr' tp m tp' m' addr
        (Hlock: lockRes tp addr)
        (HisLock: isLock tp addr)
        (Hstep: multi_step (U, tr, tp) m
                           (U', tr ++ tr', tp') m')
        (Hfreelock: forall (u : nat) (evu : machine_event),
            nth_error tr' u = Some evu ->
            action evu <> Freelock \/
            location evu <> Some (addr, lksize.LKSIZE_nat)),
        lockRes tp' addr /\
        isLock tp' addr.
    Proof.
      induction U; intros.
      - inversion Hstep.
        rewrite <- app_nil_r in H3 at 1.
        apply app_inv_head in H3; subst.
        split; assumption.
      - inversion Hstep.
        + rewrite <- app_nil_r in H3 at 1.
          apply app_inv_head in H3; subst;
            split; assumption.
        + subst.
          apply app_inv_head in H6. subst.
          eapply remLockRes_Freelock in H8; eauto.
          destruct H8 as [Hres0 HisLock0].
          specialize (IHU U' (tr ++ tr'0) tr'' tp'0 m'0 tp' m' addr Hres0 HisLock0).
          rewrite <- app_assoc in IHU.
          specialize (IHU H9).
          eapply IHU.
          intros u evu Hnth''.
          erewrite nth_error_app with (ys := tr'0) in Hnth''.
          eauto.
          intros.
          erewrite <- nth_error_app1 with (l' := tr'') in H.
          eauto.
          eapply nth_error_Some.
          intros Hcontra; congruence.
    Qed.

    (** *** Properties of internal steps*)
    (** Permissions of addresses that are valid and not freeable do
    not change by internal steps*)
    Lemma ev_elim_stable:
      forall m m' b ofs es
        (Hvalid: Mem.valid_block m b)
        (Hperm: Mem.perm_order'' (Some Writable)
                                 (permission_at m b ofs Cur))
        (Helim: ev_elim m es m'),
        permission_at m b ofs Cur = permission_at m' b ofs Cur.
    Proof.
      intros.
      generalize dependent m.
      induction es as [|ev es]; intros.
      - inversion Helim; subst; auto.
      - simpl in Helim.
        destruct ev;
          try (destruct Helim as [m'' [Haction Helim']]).
        + pose proof (MemoryLemmas.mem_storebytes_cur _ _ _ _ _ Haction b ofs) as Heq.
          do 2 rewrite getCurPerm_correct in Heq.
          rewrite Heq.
          rewrite Heq in Hperm.
          eapply IHes; eauto.
          eapply Mem.storebytes_valid_block_1; eauto.
        + destruct Helim; eauto.
        + pose proof (MemoryLemmas.permission_at_alloc_1
                        _ _ _ _ _ _ ofs Haction Hvalid Cur) as Heq.
          rewrite Heq. rewrite Heq in Hperm.
          eapply IHes; eauto.
          eapply Mem.valid_block_alloc; eauto.
        + assert (Hlt: ~ Mem.perm m b ofs Cur Freeable).
          { intros Hcontra.
            unfold Mem.perm in Hcontra.
            simpl in Hperm. unfold permission_at in *.
            destruct ((Mem.mem_access m) !! b ofs Cur); inv Hperm;
              simpl in Hcontra; inversion Hcontra.
          }
          pose proof (MemoryLemmas.permission_at_free_list_1 _ _ _ _ _
                                                             Haction Hlt Cur) as Heq.
          rewrite Heq. rewrite Heq in Hperm.
          eapply IHes; eauto.
          pose proof (freelist_forward _ _ _ Haction) as Hfwd.
          destruct (Hfwd _ Hvalid); auto.
    Qed.

    (*TODO: Move to ev_semantics*)
    Definition in_free_list (b : block) ofs xs :=
      exists x, List.In x xs /\
           let '(b', lo, hi) := x in
           b = b' /\
           (lo <= ofs < hi)%Z.

    Fixpoint in_free_list_trace (b : block) ofs es :=
      match es with
      | event_semantics.Free l :: es =>
        in_free_list b ofs l \/ in_free_list_trace b ofs es
      | _ :: es =>
        in_free_list_trace b ofs es
      | [:: ] =>
        False
      end.

    (** If (b, ofs) is in the list of freed addresses then the
          permission was Freeable and became None or it was not allocated*)
    Lemma ev_elim_free_1:
      forall m ev m' b ofs,
        ev_elim m ev m' ->
        in_free_list_trace b ofs ev ->
        (permission_at m b ofs Cur = Some Freeable \/
         ~ Mem.valid_block m b) /\
        permission_at m' b ofs Cur = None /\
        Mem.valid_block m' b /\
        exists e, List.In e ev /\
             match e with
             | event_semantics.Free _ => True
             | _ => False
             end.
    Proof.
      unfold permission_at.
      intros.
      eapply event_semantics.ev_elim_free_1 in H; eauto.
      destruct H as (? & ? & ? & ?).
      repeat split; auto.
      unfold Mem.perm in H.
      destruct H; auto.
      destruct ((Mem.mem_access m) # b ofs Cur); simpl in H;
        inv H;
        now auto.
    Qed.

    (** If (b, ofs) is not in the list of freed locations and b
          is a valid block then the permissions remains the same
          (cannot be freed or allocated)*)
    Lemma ev_elim_free_2:
      forall m ev m' b ofs,
        ev_elim m ev m' ->
        ~ in_free_list_trace b ofs ev ->
        Mem.perm_order'' (permission_at m' b ofs Cur) (permission_at m b ofs Cur).
    Proof.
      intros.
      unfold permission_at.
      eapply event_semantics.ev_elim_free_2;
        now eauto.
    Qed.

    Lemma free_list_cases:
      forall l m m' b ofs
        (Hfree: Mem.free_list m l = Some m'),
        (permission_at m b ofs Cur = Some Freeable /\
         permission_at m' b ofs Cur = None) \/
        (permission_at m b ofs Cur = permission_at m' b ofs Cur).
    Proof.
      intros.
      unfold permission_at.
      eapply event_semantics.free_list_cases;
        now eauto.
    Qed.

    Lemma elim_perm_valid_block:
      forall m T m' b ofs ofs' bytes
        (Hintv: Intv.In ofs' (ofs, (ofs + Z.of_nat (length bytes))%Z))
        (Helim: ev_elim m T m')
        (Hvalid: Mem.valid_block m b),
        (** Either the location was freed*)
        (permission_at m b ofs' Cur = Some Freeable /\ permission_at m' b ofs' Cur = None) \/
        (** or it wasn't and the operation denoted by the event implies the permission*)
        ((List.In (event_semantics.Write b ofs bytes) T ->
          Mem.perm_order'' (permission_at m b ofs' Cur) (Some Writable) /\
          Mem.perm_order'' (permission_at m' b ofs' Cur) (Some Writable)) /\
         (forall n,
             List.In (event_semantics.Read b ofs n bytes) T ->
             Mem.perm_order'' (permission_at m b ofs' Cur) (Some Readable) /\
             Mem.perm_order'' (permission_at m' b ofs' Cur) (Some Readable))).
    Proof.
      intros.
      generalize dependent m'.
      generalize dependent m.
      induction T as [| ev]; intros.
      - inversion Helim; subst.
        right; split; intros; simpl in H; by exfalso.
      - simpl in Helim.
        destruct ev.
        + destruct Helim as [m'' [Hstore Helim']].
          eapply Mem.storebytes_valid_block_1 in Hvalid; eauto.
          destruct (IHT _ Hvalid _ Helim') as [? | [Hwrite Hread]].
          * pose proof (MemoryLemmas.mem_storebytes_cur _ _ _ _ _ Hstore b ofs') as Heq.
            rewrite! getCurPerm_correct in Heq.
            rewrite Heq.
            left; assumption.
          * destruct (event_semantics.in_free_list_trace_dec b ofs' T) as [Hfree | HnotFree].
            { (** If (b, ofs') was freed in the trace T*)
              eapply ev_elim_free_1 in Hfree; eauto.
              destruct Hfree as [[? | ?] [? [? ?]]]; try (by exfalso).
              left.
              pose proof (MemoryLemmas.mem_storebytes_cur _ _ _ _ _ Hstore b ofs') as Heq.
              rewrite! getCurPerm_correct in Heq.
              rewrite Heq. now eauto.
            }
            { (** If [(b,ofs')] was not freed in [T]*)
              right.
              eapply ev_elim_free_2 in HnotFree; eauto.
              pose proof (MemoryLemmas.mem_storebytes_cur _ _ _ _ _ Hstore b ofs') as Heq.
              rewrite! getCurPerm_correct in Heq.
              rewrite <- Heq in HnotFree.
              clear Heq.
              split.
              - intros Hin.
                simpl in Hin.
                destruct Hin as [Heq | Hin].
                + inv Heq.
                  apply Mem.storebytes_range_perm in Hstore.
                  specialize (Hstore _ Hintv).
                  unfold Mem.perm, permission_at in *.
                  rewrite <- po_oo.
                  split;
                    now eauto using po_trans.
                + specialize (Hwrite Hin).
                  pose proof (MemoryLemmas.mem_storebytes_cur _ _ _ _ _ Hstore b ofs') as Heq.
                  rewrite! getCurPerm_correct in Heq.
                  rewrite Heq.
                  destruct Hwrite;
                    split;
                    now assumption.
              - intros n Hin.
                simpl in Hin.
                destruct Hin as [Heq | Hin].
                discriminate.
                specialize (Hread _ Hin).
                pose proof (MemoryLemmas.mem_storebytes_cur _ _ _ _ _ Hstore b ofs') as Heq.
                rewrite! getCurPerm_correct in Heq.
                rewrite Heq.
                destruct Hread; split;
                  now assumption.
            }
        + (** Case the new operation is a read*)
          destruct Helim as [Hload Helim'].
          destruct (IHT _ Hvalid _ Helim') as [? | [Hwrite Hread]].
          * left; assumption.
          * destruct (event_semantics.in_free_list_trace_dec b ofs' T) as [Hfree | HnotFree].
            { (** If (b, ofs') was freed in the trace T*)
              eapply ev_elim_free_1 in Hfree; eauto.
              destruct Hfree as [[? | ?] [? [? ?]]]; try (by exfalso).
              left.
              now eauto.
            }
            { (** If [(b,ofs')] waas not freed in [T]*)
              right.
              eapply ev_elim_free_2 in HnotFree; eauto.
              split.
              - intros Hin.
                simpl in Hin.
                destruct Hin as [Heq | Hin];
                  first by discriminate.
                destruct (Hwrite Hin).
                split;
                  now assumption.
              - intros n0 Hin.
                simpl in Hin.
                destruct Hin as [Heq | Hin].
                + inv Heq.
                  pose proof (Mem.loadbytes_length _ _ _ _ _ Hload) as Hlength.
                  destruct (zle n0 0).
                  * exfalso.
                    eapply Mem.loadbytes_empty with (m := m) (b := b) (ofs := ofs) in l.
                    rewrite Hload in l. inv l.
                    unfold Intv.In in Hintv. simpl in Hintv.
                    rewrite Z.add_0_r in Hintv.
                    ssromega.
                  * rewrite Hlength in Hintv.
                    erewrite nat_of_Z_eq in Hintv by omega.
                    apply Mem.loadbytes_range_perm in Hload.
                    specialize (Hload _ Hintv).
                    unfold Mem.perm, permission_at in *.
                    split;
                      now eauto using po_trans.
                + split; eapply Hread;
                    now eauto.
            }
        + (** Case thew new operation allocated memory*)
          destruct Helim as [m'' [Halloc Helim']].
          pose proof (Mem.valid_block_alloc _ _ _ _ _ Halloc _ Hvalid) as Hvalid'.
          destruct (IHT _ Hvalid' _ Helim') as [Heq | [Hwrite Hread]].
          * erewrite <- MemoryLemmas.permission_at_alloc_1 in Heq by eauto.
            left; eauto.
          * destruct (event_semantics.in_free_list_trace_dec b ofs' T) as [Hfree | HnotFree].
            { (** If (b, ofs') was freed in the trace T*)
              eapply ev_elim_free_1 in Hfree; eauto.
              destruct Hfree as [[? | ?] [? [? ?]]]; try (by exfalso).
              left.
              erewrite MemoryLemmas.permission_at_alloc_1 by eauto.
              now eauto using po_trans.
            }
            { (** If [(b,ofs')] waas not freed in [T]*)
              right.
              eapply ev_elim_free_2 in HnotFree; eauto.
              split; intros; simpl in H;
                destruct H; try (discriminate);
                  erewrite MemoryLemmas.permission_at_alloc_1 by eauto;
                  [split; eapply Hwrite | split; eapply Hread];
                  now eauto.
            }
        + (** Case the new operation freed memory*)
          destruct Helim as [m'' [Hfree Helim']].
          assert (Hvalid': Mem.valid_block m'' b)
            by (unfold Mem.valid_block in *; erewrite nextblock_freelist by eauto; eauto).
          destruct (IHT _ Hvalid' _ Helim') as [Heq | [Hwrite Hread]].
          * assert (Hperm: Mem.perm m'' b ofs' Cur Freeable)
              by (unfold Mem.perm; unfold permission_at in Heq;
                  rewrite Heq.1; simpl; auto using perm_order).
            pose proof (perm_freelist _ _ _ _ _ Cur Freeable Hfree Hperm) as Hperm'.
            unfold Mem.perm in Hperm'.
            destruct Heq.
            left; split; auto.
            unfold permission_at.
            destruct ((Mem.mem_access m) !! b ofs' Cur) as [p|]; simpl in Hperm';
              inv Hperm'; reflexivity.
          * eapply free_list_cases with (b := b) (ofs := ofs') in Hfree.
            destruct Hfree as [[Heq1 Heq2] | Heq].
            left. split; auto.
            erewrite <- ev_elim_stable; eauto.
            rewrite Heq2.
            now apply po_None.
            rewrite Heq.
            right; split; intros; simpl in H;
              destruct H; try (discriminate);
                eauto.
    Qed.

    Lemma free_list_valid_block:
      forall m m' l b,
        Mem.free_list m l = Some m' ->
        Mem.valid_block m b <-> Mem.valid_block m' b.
    Proof.
      intros.
      eapply nextblock_freelist in H.
      unfold Mem.valid_block. rewrite H.
      now auto.
    Qed.

    Lemma elim_perm_invalid_block:
      forall m T m' b ofs ofs' bytes
        (Hintv: Intv.In ofs' (ofs, (ofs + Z.of_nat (length bytes))%Z))
        (Helim: ev_elim m T m')
        (Hinvalid: ~ Mem.valid_block m b),
        (** or it wasn't and the operation denoted by the event implies the permission*)
        (List.In (event_semantics.Write b ofs bytes) T ->
         (permission_at m' b ofs' Cur = Some Freeable \/ permission_at m' b ofs' Cur = None)
         /\ Mem.valid_block m' b) /\
        (forall n,
            List.In (event_semantics.Read b ofs n bytes) T ->
            (permission_at m' b ofs' Cur = Some Freeable \/ permission_at m' b ofs' Cur =  None) /\ Mem.valid_block m' b).
    Proof.
      intros.
      generalize dependent m'.
      generalize dependent m.
      induction T as [| ev]; intros.
      - inversion Helim; subst.
        split; intros; simpl in H; by exfalso.
      - simpl in Helim.
        destruct ev.
        + destruct Helim as [m'' [Hstore Helim']].
          assert (Hinvalid'': ~ Mem.valid_block m'' b)
            by (intro Hcontra;
                eapply Mem.storebytes_valid_block_2 in Hcontra; eauto).
          destruct (IHT _ Hinvalid'' _ Helim') as [Hwrite Hread].
          split; [intros Hin | intros n Hin].
          * simpl in Hin.
            destruct Hin as [Heq | Hin]; eauto.
            inv Heq.
            exfalso.
            apply Mem.storebytes_range_perm in Hstore.
            unfold Mem.range_perm in Hstore.
            specialize (Hstore _ Hintv).
            apply Mem.nextblock_noaccess with (k := Cur) (ofs := ofs') in Hinvalid.
            unfold Mem.perm in Hstore.
            rewrite Hinvalid in Hstore.
            simpl in Hstore.
            now assumption.
          * simpl in Hin; destruct Hin; [discriminate | now eauto].
        + destruct Helim as [Hload Helim'].
          destruct (IHT _ Hinvalid _ Helim') as [Hwrite Hread].
          split.
          * intros Hin; simpl in Hin.
            destruct Hin as [Heq | Hin];
              [discriminate | now eauto].
          * intros ? Hin; simpl in Hin.
            destruct Hin as [Heq | Hin].
            exfalso.
            inv Heq.
            assert (Hlength: nat_of_Z n0 = length bytes)
              by (apply Mem.loadbytes_length in Hload; auto).
            apply Mem.loadbytes_range_perm in Hload.
            rewrite <- Hlength in Hintv.
            specialize (Hload ofs').
            assert (Hintv': (ofs <= ofs' < ofs + n0)%Z).
            { rewrite nat_of_Z_max in Hintv.
              destruct (Z.max_dec n0 0);
                erewrite e in *;
                eauto.
              destruct Hintv.
              simpl in *. ssromega.
            }
            specialize (Hload Hintv').
            apply Mem.nextblock_noaccess with (k := Cur) (ofs := ofs') in Hinvalid.
            unfold Mem.perm in Hload.
            rewrite Hinvalid in Hload. simpl in Hload; now auto.
            now eauto.
        + destruct Helim as [m'' [Halloc Helim']].
          destruct (Pos.eq_dec b b0); subst.
          { destruct (zle lo ofs').
            - destruct (zlt ofs' hi).
              + assert (Hfreeable:permission_at m'' b0 ofs' Cur = Some Freeable)
                  by (eapply MemoryLemmas.permission_at_alloc_2; eauto).
                destruct (event_semantics.in_free_list_trace_dec b0 ofs' T) as [Hfree | HnotFree].
                * eapply ev_elim_free_1 in Hfree; eauto.
                  destruct Hfree as [[? | ?] [Hfreed [? ?]]]; try (by exfalso);
                    split; intros; eauto.
                * eapply ev_elim_free_2 in HnotFree; eauto.
                  rewrite Hfreeable in HnotFree.
                  destruct (permission_at m' b0 ofs' Cur) eqn:Hfreeable'; simpl in HnotFree;
                    try by exfalso.
                  assert (p = Freeable)
                    by (inv HnotFree; auto); subst.
                  split; intros; split;
                    now eauto using ev_elim_valid_block, Mem.valid_new_block.
              + assert (Hfreeable:permission_at m'' b0 ofs' Cur = None)
                  by (eapply MemoryLemmas.permission_at_alloc_3; eauto).
                pose proof (Mem.valid_new_block _ _ _ _ _ Halloc) as Hvalid.
                pose proof (ev_elim_stable _ ofs' _ Hvalid ltac:(rewrite Hfreeable; simpl; now constructor) Helim') as Heq.
                rewrite <- Heq.
                rewrite Hfreeable.
                split; intros; now eauto using ev_elim_valid_block.
            - assert (Hfreeable:permission_at m'' b0 ofs' Cur = None).
                by (eapply MemoryLemmas.permission_at_alloc_3; eauto; left; omega).
                pose proof (Mem.valid_new_block _ _ _ _ _ Halloc) as Hvalid.
                pose proof (ev_elim_stable _ ofs' _ Hvalid ltac:(rewrite Hfreeable; simpl; now constructor) Helim') as Heq.
                rewrite <- Heq.
                rewrite Hfreeable.
                split; intros; now eauto using ev_elim_valid_block.
          }
          { assert (Hinvalid': ~ Mem.valid_block m'' b)
              by (intros Hcontra; eapply Mem.valid_block_alloc_inv in Hcontra; eauto;
                  destruct Hcontra; subst; now auto).
            destruct (IHT _ Hinvalid' _ Helim') as [Hwrite Hread].
            split; intros; simpl in H; destruct H; try (discriminate);
              now eauto.
          }
        + destruct Helim as [m'' [Hfree_list Helim']].
          assert (Hinvalid': ~ Mem.valid_block m'' b)
            by (intros Hcontra;
                erewrite <- free_list_valid_block in Hcontra by eauto;
                now auto).
          destruct (IHT _ Hinvalid' _ Helim') as [Hwrite Hread].
          split; intros; destruct H; try (discriminate);
            now eauto.
    Qed.

    (** *** Properties about permission decay and events *)

    (** Permission decrease: A thread can decrease its data permissions by:
- Freeing memory.
- Spawning a thread
- A makelock operation, turning data into lock
- Releasing a lock *)
    Lemma data_permission_decrease_step:
      forall U tr tp m U' tp' m' tr' tidn b ofs
        (cnt: containsThread tp tidn)
        (cnt': containsThread tp' tidn)
        (Hstep: MachStep (U, tr, tp) m (U', tr ++ tr', tp') m')
        (Hperm: Mem.perm_order'' ((getThreadR cnt).1 !! b ofs) (Some Readable))
        (Hperm': ~ Mem.perm_order'' ((getThreadR cnt').1 !! b ofs) (Some Readable)),
      exists ev,
        (List.In ev tr' /\ action ev = Free /\ deadLocation tp' m' b ofs) \/
        (tr' = [:: ev] /\ action ev = Spawn) \/
        (tr' = [:: ev] /\ action ev = Mklock /\
         thread_id ev = tidn /\
         match location ev with
         | Some (addr, sz) =>
           b = addr.1 /\
           Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
         | None =>
           False
         end) \/
        (tr' = [:: ev] /\ action ev = Release /\ thread_id ev = tidn /\
         exists rmap, match location ev with
                 | Some (laddr, sz) =>
                   sz = lksize.LKSIZE_nat /\
                   lockRes tp' laddr = Some rmap /\
                   Mem.perm_order'' (rmap.1 !! b ofs) (Some Readable)
                 | None => False
                 end).
    Proof.
      Opaque containsThread getThreadR.
      intros;
      inv Hstep;  simpl in *;
        try apply app_eq_refl_nil in H4;
        try inv Htstep;
        destruct U; inversion HschedN; subst; pf_cleanup;
          try (inv Hhalted);
          try (rewrite gThreadCR in Hperm');
          try  (exfalso; by eauto);
          try (apply app_inv_head in H5; subst).
      - (** initial core case *)
        exfalso.
        inv Hperm0.
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          apply CoreLanguage.initial_core_decay in Hinitial.
          destruct (Hinitial b ofs) as [_ Hsame].
          rewrite gssThreadRes in Hperm'.
          simpl in Hperm'.
          erewrite getCurPerm_correct in Hperm'.
          unfold permission_at in Hperm', Hperm.
          pose proof (restrPermMap_Cur (Hcmpt tidn cnt).1 b ofs) as Heq.
          erewrite <- Hsame in Hperm'.
          eapply Hperm'.
          rewrite <- Heq in Hperm.
          unfold permission_at in Hperm.
          now auto.
          destruct (valid_block_dec (restrPermMap (Hcmpt tidn cnt).1) b); auto.
          exfalso.
          apply Mem.nextblock_noaccess with (ofs := ofs) (k := Cur) in n.
          unfold permission_at in Heq.
          rewrite <- Heq in Hperm.
          rewrite n in Hperm.
          simpl in Hperm.
          assumption.
        + erewrite gsoThreadRes with (cntj := cnt) in Hperm' by eauto.
          now eauto.
      - (** internal step case *)
        (*destruct (ev_step_elim  _ _ _ _ _ _ Hcorestep) as [Helim _].*)
        assert (Helim:= ev_step_elim  _ _ _ _ _ _ Hcorestep).
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          (* NOTE: this is decidable*)
          destruct (event_semantics.in_free_list_trace_dec b ofs ev) as [Hdead | Hlive].
          { (** case this address was freed*)
            eapply ev_elim_free_1 with (m := (restrPermMap (Hcmpt _ cnt).1))
                                       (m' := m'0) in Hdead; eauto.
            destruct Hdead as [Hinit [Hempty [Hvalid' [evf [Hin HFree]]]]].
            destruct Hinit as [Hfreeable | Hinvalid].
            { (** case the block was allocated*)
              destruct evf; try by exfalso.
              exists (internal tidn (event_semantics.Free l)).
              simpl. left.
              rewrite restrPermMap_Cur in Hfreeable.
              split; [|split; auto].
              - apply in_map with (f := fun ev => internal tidn ev) in Hin.
                assumption.
              - constructor.
                + (** [b] is a valid block*)
                  erewrite <- diluteMem_valid in Hvalid'.
                  simpl in *.
                  assumption.
                + (** no thread has permission on [(b, ofs)]*)
                  intros.
                  destruct (i == tidn) eqn:Hij; move/eqP:Hij=>Hij; subst.
                  * rewrite gssThreadRes.
                    rewrite getCurPerm_correct.
                    simpl.
                    split; first by assumption.
                    (** To prove that there is no lock permission on that location we use the [invariant]*)
                    pose proof ((thread_data_lock_coh _ Hinv _ cnt).1 _ cnt b ofs) as Hcoh.
                    rewrite Hfreeable in Hcoh.
                    simpl in Hcoh.
                    destruct ((getThreadR cnt).2 !! b ofs);
                      [by exfalso | reflexivity].
                  * (** case i is a different thread than the one that stepped*)
                    (** by the invariant*)
                    assert (cnti' := cntUpdate' _ _ _ cnti).
                    rewrite gsoThreadRes; auto.
                    split.
                    pose proof ((no_race_thr _ Hinv _ _ cnti' cnt Hij).1 b ofs) as Hno_race.
                    rewrite Hfreeable in Hno_race.
                    rewrite perm_union_comm in Hno_race.
                    apply no_race_racy in Hno_race.
                    inv Hno_race. auto.
                    now constructor.
                    pose proof ((thread_data_lock_coh _ Hinv _ cnti').1 _ cnt b ofs) as Hcoh.
                    rewrite Hfreeable in Hcoh.
                    simpl in Hcoh.
                    destruct ((getThreadR cnti').2 !! b ofs) eqn: ?;
                                                                                [by exfalso | auto].
                + (** no lock resource has permission on the location*)
                  intros laddr rmap Hres.
                  rewrite gsoThreadLPool in Hres.
                  split.
                  * pose proof ((no_race _ Hinv _ _ cnt _ Hres).1 b ofs) as Hno_race.
                    rewrite Hfreeable in Hno_race.
                    apply no_race_racy in Hno_race.
                    inversion Hno_race.
                    reflexivity.
                    now constructor.
                  * pose proof (((locks_data_lock_coh _ Hinv) _ _ Hres).1 _ cnt b ofs) as Hcoh.
                    rewrite Hfreeable in Hcoh.
                    simpl in Hcoh.
                    destruct (rmap.2 !! b ofs);
                      [by exfalso | reflexivity].
            }
            { (** case the block was not allocated*)
              destruct evf; try by exfalso.
              exists (internal tidn (event_semantics.Free l)).
              simpl. left.
              split; [|split; auto].
              - apply in_map with (f := fun ev => internal tidn ev) in Hin.
                assumption.
              - constructor.
                + erewrite <- diluteMem_valid in Hvalid'.
                  simpl in *.
                  assumption.
                + intros.
                  destruct (i == tidn) eqn:Hij; move/eqP:Hij=>Hij; subst.
                  * pf_cleanup.
                    rewrite gssThreadRes.
                    rewrite getCurPerm_correct.
                    simpl.
                    split; first by assumption.
                    erewrite restrPermMap_valid in Hinvalid.
                    eapply ThreadPoolWF.mem_compatible_invalid_block with (ofs0 := ofs) in Hinvalid; eauto.
                    rewrite (Hinvalid.1 _ cnt).2.
                    reflexivity.
                  * (** case i is a different thread than the one that stepped*)
                    erewrite restrPermMap_valid in Hinvalid.
                    eapply ThreadPoolWF.mem_compatible_invalid_block with (ofs0 := ofs) in Hinvalid; eauto.
                    rewrite! gsoThreadRes; auto.
                    erewrite (Hinvalid.1 _ cnti).2, (Hinvalid.1 _ cnti).1.
                    split;
                      reflexivity.
                + intros.
                  rewrite gsoThreadLPool in H.
                  erewrite restrPermMap_valid in Hinvalid.
                  eapply ThreadPoolWF.mem_compatible_invalid_block with (ofs0 := ofs) in Hinvalid; eauto.
                  erewrite (Hinvalid.2 _ _ H).2, (Hinvalid.2 _ _ H).1.
                  split;
                    reflexivity.
            }
          }
          { (** case the address was not freed *)
            exfalso.
            clear - Hlive Helim Hperm Hperm'.
            eapply ev_elim_free_2 in Hlive; eauto.
            rewrite restrPermMap_Cur in Hlive.
            rewrite gssThreadRes in Hperm', Hperm. simpl in *.
            rewrite getCurPerm_correct in Hperm', Hperm.
            apply Hperm'.
            eapply po_trans;
              now eauto.
          }
        + (** case it was another thread that stepped *)
          exfalso.
          setoid_rewrite gsoThreadRes with (cntj := cnt) in Hperm'; [|assumption].
          now eauto.
      - (** lock acquire*)
        (** In this case the permissions of a thread can only increase,
            hence we reach a contradiction by the premise*)
        exfalso.
        clear - Hangel1 Hangel2 HisLock Hperm Hperm'.
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + rewrite gLockSetRes gssThreadRes in Hperm, Hperm'.
          specialize (Hangel1 b ofs).
          apply permjoin_order in Hangel1.
          destruct Hangel1 as [_ Hperm''].
          pf_cleanup.
          apply Hperm'.
          eapply po_trans;
            now eauto.
        + rewrite gLockSetRes gsoThreadRes in Hperm';
            now auto.
      - (** lock release *)
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          eexists.
          do 3 right. repeat (split; eauto).
          exists virtueLP; split.
          reflexivity.
          rewrite OrdinalPool.gssLockRes.
          split. reflexivity.
          rewrite gLockSetRes gssThreadRes in Hperm'.
          specialize (Hangel1 b ofs).
          apply permjoin_readable_iff in Hangel1.
          rewrite! po_oo in Hangel1.
          destruct (Hangel1.1 Hperm);
            first by (simpl in *; by exfalso).
          assumption.
        + exfalso.
          rewrite gLockSetRes gsoThreadRes in Hperm';
            now eauto.
      - (** thread spawn*)
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          eexists.
          right.
          left;
            simpl; split;
              now eauto.
        + exfalso.
          rewrite gsoAddRes gsoThreadRes in Hperm';
            now eauto.
      - (** MkLock *)
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          eexists.
          do 2 right.
          left.
          do 3 (split; simpl; eauto).
          rewrite gLockSetRes gssThreadRes in Hperm'.
          destruct (Pos.eq_dec b b0).
          * subst.
            split; auto.
            destruct (Intv.In_dec ofs (Ptrofs.intval ofs0, Ptrofs.intval ofs0 + lksize.LKSIZE)%Z); auto.
            exfalso.
            rewrite <- Hdata_perm in Hperm'.
            rewrite setPermBlock_other_1 in Hperm'.
            now auto.
            apply Intv.range_notin in n.
            destruct n; eauto.
            simpl. now lksize.lkomega.
          * exfalso.
            rewrite <- Hdata_perm in Hperm'.
            erewrite setPermBlock_other_2 in Hperm' by eauto.
            now auto.
        + exfalso.
          rewrite gLockSetRes gsoThreadRes in Hperm';
            now eauto.
      - exfalso.
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          clear - Hdata_perm Hperm Hperm' Hfreeable Hinv Hneq_perms.
          rewrite gRemLockSetRes gssThreadRes in Hperm', Hperm.
          destruct (Pos.eq_dec b b0).
          * subst.
            rewrite <- Hdata_perm in Hperm'.
            destruct (Intv.In_dec ofs (Ptrofs.intval ofs0, Ptrofs.intval ofs0 + lksize.LKSIZE)%Z); auto.
            erewrite setPermBlock_var_same in Hperm' by eauto.
            apply Hperm'.
            specialize (Hneq_perms (nat_of_Z (ofs - Ptrofs.intval ofs0))).
            assert (Hrange: (0 <= Z.of_nat (nat_of_Z (ofs - Ptrofs.intval ofs0))
                             < lksize.LKSIZE)%Z).
            { unfold Intv.In, lksize.LKSIZE in *.
              rewrite nat_of_Z_eq.
              simpl in i.
              destruct i; split; ssromega.
              unfold Intv.In, lksize.LKSIZE in i.
              simpl in i.
              ssromega.
            }
            specialize (Hneq_perms Hrange).
            replace ((nat_of_Z (ofs - Ptrofs.intval ofs0)).+1) with
                (nat_of_Z (ofs - Ptrofs.intval ofs0 +1)) in Hneq_perms.
            eapply po_trans;
              eauto; simpl; now constructor.
            destruct i.
            zify.
            erewrite! nat_of_Z_eq
              by (unfold lksize.LKSIZE in *; simpl in *; ssromega).
            omega.
            rewrite setPermBlock_var_other_1 in Hperm'.
            now auto.
            apply Intv.range_notin in n.
            destruct n; eauto.
            simpl. now lksize.lkomega.
          * exfalso.
            rewrite <- Hdata_perm in Hperm'.
            erewrite setPermBlock_var_other_2 in Hperm' by eauto.
            now auto.
        + exfalso.
          rewrite gRemLockSetRes gsoThreadRes in Hperm';
            now eauto.
    Qed.

    (** Lifting [data_permission_decrease_step] to multiple steps using [multi_step] *)
    Lemma data_permission_decrease_execution:
      forall U tr tpi mi U' tr' tpj mj
        b ofs tidn
        (cnti: containsThread tpi tidn)
        (cntj: containsThread tpj tidn)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hperm: Mem.perm_order'' ((getThreadR cnti).1 !! b ofs) (Some Readable))
        (Hperm: ~ Mem.perm_order'' ((getThreadR cntj).1 !! b ofs) (Some Readable)),
      exists tr_pre tru U'' U''' tp_pre m_pre tp_dec m_dec,
        multi_step (U, tr, tpi) mi (U'', tr ++ tr_pre, tp_pre) m_pre /\
        MachStep (U'', tr ++ tr_pre, tp_pre) m_pre
                 (U''', tr ++ tr_pre ++ tru, tp_dec) m_dec /\
        multi_step (U''', tr ++ tr_pre ++ tru, tp_dec) m_dec
                   (U', tr ++ tr',tpj) mj /\
        (exists evu,
            (List.In evu tru /\ action evu = Free /\ deadLocation tpj mj b ofs) \/
            (tru = [:: evu] /\ action evu = Spawn) \/
            (tru = [:: evu] /\ action evu = Mklock /\ thread_id evu = tidn /\
             match location evu with
             | Some (addr, sz) =>
               b = addr.1 /\
               Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
             | None => False
             end) \/
            (tru = [:: evu] /\ action evu = Release /\ thread_id evu = tidn /\
             (exists rmap, match location evu with
                      | Some (laddr, sz) =>
                        sz = lksize.LKSIZE_nat /\
                        lockRes tp_dec laddr = Some rmap /\
                        Mem.perm_order'' (rmap.1 !! b ofs) (Some Readable)
                      | None => False
                      end))).
    Proof.
      induction U as [|tid' U]; intros.
      - inversion Hexec. apply app_eq_refl_nil in H3; subst.
        pf_cleanup. by congruence.
      - inversion Hexec.
        + apply app_eq_refl_nil in H3; subst.
          pf_cleanup;
            by congruence.
        + apply app_inv_head in H6; subst.
          assert (cnt': containsThread tp' tidn)
            by (eapply step_containsThread with (tp := tpi); eauto).
          (** Case the permissions were changed by the inductive step. There
                are two subcases, either they increased and hence we can apply
                the IH again by transitivity or they decreased and
                [data_permission_decrease_step] applies directly*)
          destruct (perm_order''_dec ((getThreadR cnt').1 !! b ofs)
                                     (Some Readable)) as [Hincr | Hdecr].

          { (** Case permissions increased*)
            rewrite app_assoc in H9.
            (** And we can apply the IH*)
            destruct (IHU _ _ _ _ _ _ _ _ _ _ _ _ H9 Hincr Hperm0)
              as (tr_pre & tru & U'' & U''' & tp_pre & m_pre & tp_dec
                  & m_dec & Hexec_pre & Hstep & Hexec_post & evu & Hspec).
            destruct Hspec as [[Hin [Haction Hdead]] |
                               [[Heq Haction] | [[Heq [Haction [Hthreadid Hloc]]]
                                                | [? [Haction [Hthreadid Hstable]]]]]].
            + (** case the drop was by a [Free] event*)
              exists (tr'0 ++ tr_pre), tru, U'', U''', tp_pre, m_pre, tp_dec, m_dec.
              split.
              econstructor 2; eauto.
              rewrite app_assoc.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              exists evu.
              left.
              split;
                now auto.
            + (** case the drop was by a [Spawn] event *)
              exists (tr'0 ++ tr_pre), tru, U'', U''', tp_pre, m_pre, tp_dec, m_dec.
              split.
              econstructor 2; eauto.
              rewrite app_assoc.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              exists evu.
              right. left.
              split;
                now auto.
            + (** case the drop was by a [Mklock] event *)
              exists (tr'0 ++ tr_pre), tru, U'', U''', tp_pre, m_pre, tp_dec, m_dec.
              split.
              econstructor 2; eauto.
              rewrite app_assoc.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              exists evu.
              do 2 right. left.
              split;
                now auto.
            + (** case the drop was by a [Release] event*)
              exists (tr'0 ++ tr_pre), tru, U'', U''', tp_pre, m_pre, tp_dec, m_dec.
              split.
              econstructor 2; eauto.
              rewrite app_assoc.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              exists evu.
              do 3 right.
              split. now auto.
              split. now auto.
              split. now auto.
              destruct Hstable as [rmap Hloc].
              destruct (location evu) as [[[bl ofsl] szl]|]; try (by exfalso).
              destruct Hloc as [HlockRes HpermRes].
              exists rmap;
                now eauto.
          }
          { (** Case permissions decreased by this step. In that case we don't need the IH*)
            clear IHU.
            exists [::], tr'0, (tid' :: U), U, tpi, mi, tp', m'.
            repeat split.
            + rewrite app_nil_r.
              now constructor.
            + rewrite! app_nil_r. assumption.
            + simpl.
              now assumption.
            + destruct (data_permission_decrease_step _ _ _ _ _ H8 Hperm Hdecr)
                as [ev [[Hin [Haction Hdead]] | [[? Haction]
                                                | [[? [Haction [Hthread_id Hloc]]]
                                                  | [? [Haction [Hthread_id Hrmap]]]]]]].
              * exists ev.
                left.
                split. now auto.
                split. now auto.
                rewrite app_assoc in H9.
                eapply multi_step_deadLocation; eauto.
              * subst.
                exists ev.
                right. left.
                split; now auto.
              * subst.
                exists ev.
                do 2 right.
                left.
                repeat split; now auto.
              * subst.
                exists ev.
                do 3 right.
                repeat split;
                  now auto.
          }
    Qed.

    (** Permission decrease: A thread can decrease its lock permissions by:
- Spawning a thread
- A freelock operation, turning a lock into data
- Releasing a lock *)
    Lemma lock_permission_decrease_step:
      forall U tr tp m U' tp' m' tr' tidn b ofs
        (cnt: containsThread tp tidn)
        (cnt': containsThread tp' tidn)
        (Hstep: MachStep (U, tr, tp) m (U', tr ++ tr', tp') m')
        (Hperm: Mem.perm_order'' ((getThreadR cnt).2 !! b ofs) (Some Readable))
        (Hperm': ~ Mem.perm_order'' ((getThreadR cnt').2 !! b ofs) (Some Readable)),
      exists ev,
        (List.In ev tr' /\ action ev = Free /\ deadLocation tp' m' b ofs) \/
        (tr' = [:: ev] /\ action ev = Spawn) \/
        (tr' = [:: ev] /\ action ev = Freelock /\
         thread_id ev = tidn /\
         match location ev with
         | Some (addr, sz) =>
           b = addr.1 /\
           Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
         | None =>
           False
         end) \/
        (tr' = [:: ev] /\ action ev = Release /\ thread_id ev = tidn /\
         exists rmap, match location ev with
                 | Some (laddr, sz) =>
                   sz = lksize.LKSIZE_nat /\
                   lockRes tp' laddr = Some rmap /\
                   Mem.perm_order'' (rmap.2 !! b ofs) (Some Readable)
                 | None => False
                 end).
    Proof.
      intros.
      inv Hstep; simpl in *;
        try apply app_eq_refl_nil in H4;
        try inv Htstep;
        destruct U; inversion HschedN; subst; pf_cleanup;
          try (inv Hhalted);
          try (rewrite gThreadCR in Hperm');
          try  (exfalso; by eauto);
          try (apply app_inv_head in H5; subst).
      - (** initial_core step case *)
        exfalso.
        destruct (tidn == tid) eqn:Heq; move/eqP:Heq=>Heq.
        + subst.
          pf_cleanup.
          rewrite gssThreadRes in Hperm'.
          simpl in Hperm'.
          auto.
        + rewrite gsoThreadRes in Hperm';
            now auto.
      - (** internal step case *)
        exfalso.
        destruct (tidn == tid) eqn:Heq; move/eqP:Heq=>Heq.
        + subst.
          pf_cleanup.
          rewrite gssThreadRes in Hperm'.
          simpl in Hperm'.
          auto.
        + rewrite gsoThreadRes in Hperm';
            now auto.
      - (** lock acquire*)
        (** In this case the permissions of a thread can only increase,
            hence we reach a contradiction by the premise*)
        exfalso.
        clear - Hangel1 Hangel2 HisLock Hperm Hperm'.
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + rewrite gLockSetRes gssThreadRes in Hperm, Hperm'.
          specialize (Hangel2 b ofs).
          apply permjoin_order in Hangel2.
          destruct Hangel2 as [_ Hperm''].
          pf_cleanup.
          apply Hperm'.
          eapply po_trans;
            now eauto.
        + rewrite gLockSetRes gsoThreadRes in Hperm';
            now auto.
      - (** lock release *)
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          eexists.
          do 3 right. repeat (split; eauto).
          exists virtueLP; split.
          reflexivity.
          rewrite OrdinalPool.gssLockRes.
          split. reflexivity.
          rewrite gLockSetRes gssThreadRes in Hperm'.
          specialize (Hangel2 b ofs).
          apply permjoin_readable_iff in Hangel2.
          rewrite! po_oo in Hangel2.
          destruct (Hangel2.1 Hperm);
            first by (simpl in *; by exfalso).
          assumption.
        + exfalso.
          rewrite gLockSetRes gsoThreadRes in Hperm';
            now eauto.
      - (** thread spawn*)
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          eexists.
          right.
          left;
            simpl; split;
              now eauto.
        + exfalso.
          rewrite gsoAddRes gsoThreadRes in Hperm';
            now eauto.
      - (** MkLock *)
        exfalso.
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          rewrite gLockSetRes gssThreadRes in Hperm'.
          rewrite <- Hlock_perm in Hperm'.
          destruct (Pos.eq_dec b b0).
          * subst.
            destruct (Intv.In_dec ofs (Ptrofs.intval ofs0, Ptrofs.intval ofs0 + lksize.LKSIZE)%Z); auto.
            erewrite setPermBlock_same in Hperm' by eauto.
            simpl in Hperm'.
            now eauto using perm_order.
            rewrite setPermBlock_other_1 in Hperm'.
            now auto.
            apply Intv.range_notin in n.
            destruct n; eauto.
            simpl. now lksize.lkomega.
          * exfalso.
            erewrite setPermBlock_other_2 in Hperm' by eauto.
            now auto.
        + exfalso.
          rewrite gLockSetRes gsoThreadRes in Hperm';
            now eauto.
      - destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          eexists.
          do 2 right.
          left.
          do 3 (split; simpl; eauto).
          rewrite gRemLockSetRes gssThreadRes in Hperm', Hperm.
          destruct (Pos.eq_dec b b0).
          * subst.
            rewrite <- Hlock_perm in Hperm'.
            destruct (Intv.In_dec ofs (Ptrofs.intval ofs0, Ptrofs.intval ofs0 + lksize.LKSIZE)%Z); auto.
            exfalso.
            rewrite setPermBlock_other_1 in Hperm'.
            now auto.
            apply Intv.range_notin in n.
            destruct n; eauto.
            simpl. now lksize.lkomega.
          * exfalso.
            rewrite <- Hlock_perm in Hperm'.
            erewrite setPermBlock_other_2 in Hperm' by eauto.
            now auto.
        + exfalso.
          rewrite gRemLockSetRes gsoThreadRes in Hperm';
            now eauto.
    Qed.

    (** Lifting [lock_permission_decrease_step] to multiple steps using [multi_step] *)
    Lemma lock_permission_decrease_execution:
      forall U tr tpi mi U' tr' tpj mj
        b ofs tidn
        (cnti: containsThread tpi tidn)
        (cntj: containsThread tpj tidn)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hperm: Mem.perm_order'' ((getThreadR cnti).2 !! b ofs) (Some Readable))
        (Hperm: ~ Mem.perm_order'' ((getThreadR cntj).2 !! b ofs) (Some Readable)),
      exists tr_pre tru U'' U''' tp_pre m_pre tp_dec m_dec,
        multi_step (U, tr, tpi) mi (U'', tr ++ tr_pre, tp_pre) m_pre /\
        MachStep (U'', tr ++ tr_pre, tp_pre) m_pre
                 (U''', tr ++ tr_pre ++ tru, tp_dec) m_dec /\
        multi_step (U''', tr ++ tr_pre ++ tru, tp_dec) m_dec
                   (U', tr ++ tr',tpj) mj /\
        (exists evu,
            (List.In evu tru /\ action evu = Free /\ deadLocation tpj mj b ofs) \/
            (tru = [:: evu] /\ action evu = Spawn) \/
            (tru = [:: evu] /\ action evu = Freelock /\ thread_id evu = tidn /\
             match location evu with
             | Some (addr, sz) =>
               b = addr.1 /\
               Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
             | None => False
             end) \/
            (tru = [:: evu] /\ action evu = Release /\ thread_id evu = tidn /\
             (exists rmap, match location evu with
                      | Some (laddr, sz) =>
                        sz = lksize.LKSIZE_nat /\
                        lockRes tp_dec laddr = Some rmap /\
                        Mem.perm_order'' (rmap.2 !! b ofs) (Some Readable)
                      | None => False
                      end))).
    Proof.
      induction U as [|tid' U]; intros.
      - inversion Hexec. apply app_eq_refl_nil in H3; subst.
        pf_cleanup. by congruence.
      - inversion Hexec.
        + apply app_eq_refl_nil in H3; subst.
          pf_cleanup;
            by congruence.
        + apply app_inv_head in H6; subst.
          assert (cnt': containsThread tp' tidn)
            by (eapply step_containsThread with (tp := tpi); eauto).
          (** Case the permissions were changed by the inductive step. There
                are two subcases, either they increased and hence we can apply
                the IH again by transitivity or they decreased and
                [data_permission_decrease_step] applies directly*)
          destruct (perm_order''_dec ((getThreadR cnt').2 !! b ofs)
                                     (Some Readable)) as [Hincr | Hdecr].

          { (** Case permissions increased*)
            rewrite app_assoc in H9.
            (** And we can apply the IH*)
            destruct (IHU _ _ _ _ _ _ _ _ _ _ _ _ H9 Hincr Hperm0)
              as (tr_pre & tru & U'' & U''' & tp_pre & m_pre & tp_dec
                  & m_dec & Hexec_pre & Hstep & Hexec_post & evu & Hspec).
            destruct Hspec as [[Hin [Haction Hdead]] |
                               [[Heq Haction] | [[Heq [Haction [Hthreadid Hloc]]]
                                                | [? [Haction [Hthreadid Hstable]]]]]].
            + (** case the drop was by a [Free] event*)
              exists (tr'0 ++ tr_pre), tru, U'', U''', tp_pre, m_pre, tp_dec, m_dec.
              split.
              econstructor 2; eauto.
              rewrite app_assoc.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              exists evu.
              left.
              split;
                now auto.
            + (** case the drop was by a [Spawn] event *)
              exists (tr'0 ++ tr_pre), tru, U'', U''', tp_pre, m_pre, tp_dec, m_dec.
              split.
              econstructor 2; eauto.
              rewrite app_assoc.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              exists evu.
              right. left.
              split;
                now auto.
            + (** case the drop was by a [Mklock] event *)
              exists (tr'0 ++ tr_pre), tru, U'', U''', tp_pre, m_pre, tp_dec, m_dec.
              split.
              econstructor 2; eauto.
              rewrite app_assoc.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              exists evu.
              do 2 right. left.
              split;
                now auto.
            + (** case the drop was by a [Release] event*)
              exists (tr'0 ++ tr_pre), tru, U'', U''', tp_pre, m_pre, tp_dec, m_dec.
              split.
              econstructor 2; eauto.
              rewrite app_assoc.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              exists evu.
              do 3 right.
              split. now auto.
              split. now auto.
              split. now auto.
              destruct Hstable as [rmap Hloc].
              destruct (location evu) as [[[bl ofsl] szl]|]; try (by exfalso).
              destruct Hloc as [HlockRes HpermRes].
              exists rmap;
                now eauto.
          }
          { (** Case permissions decreased by this step. In that case we don't need the IH*)
            clear IHU.
            exists [::], tr'0, (tid' :: U), U, tpi, mi, tp', m'.
            repeat split.
            + rewrite app_nil_r.
              now constructor.
            + rewrite! app_nil_r. assumption.
            + simpl.
              now assumption.
            + destruct (lock_permission_decrease_step _ _ _ _ _ H8 Hperm Hdecr)
                as [ev [[Hin [Haction Hdead]] | [[? Haction]
                                                | [[? [Haction [Hthread_id Hloc]]]
                                                  | [? [Haction [Hthread_id Hrmap]]]]]]].
              * exists ev.
                left.
                split. now auto.
                split. now auto.
                rewrite app_assoc in H9.
                eapply multi_step_deadLocation; eauto.
              * subst.
                exists ev.
                right. left.
                split; now auto.
              * subst.
                exists ev.
                do 2 right.
                left.
                repeat split; now auto.
              * subst.
                exists ev.
                do 3 right.
                repeat split;
                  now auto.
          }
    Qed.

    Lemma permission_decrease_execution:
      forall U tr tpi mi U' tr' tpj mj
        b ofs tidn
        (cnti: containsThread tpi tidn)
        (cntj: containsThread tpj tidn)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hperm: (Mem.perm_order'' ((getThreadR cnti).1 !! b ofs) (Some Readable) /\
                 ~ Mem.perm_order'' ((getThreadR cntj).1 !! b ofs) (Some Readable)) \/
                (Mem.perm_order'' ((getThreadR cnti).2 !! b ofs) (Some Readable) /\
                 ~ Mem.perm_order'' ((getThreadR cntj).2 !! b ofs) (Some Readable))),
      exists tr_pre tru U'' U''' tp_pre m_pre tp_dec m_dec,
        multi_step (U, tr, tpi) mi (U'', tr ++ tr_pre, tp_pre) m_pre /\
        MachStep (U'', tr ++ tr_pre, tp_pre) m_pre
                 (U''', tr ++ tr_pre ++ tru, tp_dec) m_dec /\
        multi_step (U''', tr ++ tr_pre ++ tru, tp_dec) m_dec
                   (U', tr ++ tr',tpj) mj /\
        (exists evu,
            (List.In evu tru /\ action evu = Free /\ deadLocation tpj mj b ofs) \/
            (tru = [:: evu] /\ action evu = Spawn) \/
            (tru = [:: evu] /\ action evu = Freelock /\ thread_id evu = tidn /\
             match location evu with
             | Some (addr, sz) =>
               b = addr.1 /\
               Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
             | None => False
             end) \/
            (tru = [:: evu] /\ action evu = Mklock /\ thread_id evu = tidn /\
             match location evu with
             | Some (addr, sz) =>
               b = addr.1 /\
               Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
             | None => False
             end) \/
            (tru = [:: evu] /\ action evu = Release /\ thread_id evu = tidn /\
             (exists rmap, match location evu with
                      | Some (laddr, sz) =>
                        sz = lksize.LKSIZE_nat /\
                        lockRes tp_dec laddr = Some rmap /\
                        (Mem.perm_order'' (rmap.1 !! b ofs) (Some Readable) \/
                         Mem.perm_order'' (rmap.2 !! b ofs) (Some Readable))
                      | None => False
                      end))).
    Proof.
      intros.
      destruct Hperm as [[Hperm Hperm'] | [Hperm Hperm']];
        [destruct (data_permission_decrease_execution _ _ _ cnti cntj Hexec Hperm Hperm')
          as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hspec)
        | destruct (lock_permission_decrease_execution _ _ _ cnti cntj Hexec Hperm Hperm')
          as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hspec)];
        do 8 eexists;
        repeat match goal with
               | [H: _ \/ _ |- _] =>
                 destruct H
               | [H: _ /\ _ |- _] =>
                 destruct H
                          (* | [H: exists _, _ |- _] => *)
                          (*   destruct H *)
                          (* | [H: match ?X with _ => _ end |- _] => *)
                          (*   destruct X eqn:Hloc *)
               end; subst;
          repeat split; eauto 10;
            eexists; do 4 right;
              repeat split; eauto;
                repeat match goal with
                       | [H: exists _, _ |- _] =>
                         destruct H
                       | [H: _ /\ _ |- _ ] => destruct H
                       | [H: match ?Expr with _ => _ end |- _] =>
                         destruct Expr; try by exfalso
                       end; subst;
                  eexists; repeat split; eauto.
    Qed.

    (** Permission increase: A thread can increase its data permissions on a valid block by:
- If it is spawned
- A freelock operation, turning a lock into data.
- Acquiring a lock *)
    Lemma data_permission_increase_step:
      forall U tr tp m U' tp' m' tr' tidn b ofs
        (cnt: containsThread tp tidn)
        (cnt': containsThread tp' tidn)
        (Hstep: MachStep (U, tr, tp) m (U', tr ++ tr', tp') m')
        (Hperm': Mem.perm_order'' ((getThreadR cnt').1 !! b ofs) (Some Readable))
        (Hperm: ~ Mem.perm_order'' ((getThreadR cnt).1 !! b ofs) (Some Readable))
        (Hvalid: Mem.valid_block m b),
      exists ev,
        (tr' = [:: ev] /\ action ev = Spawn) \/
        (tr' = [:: ev] /\ action ev = Freelock /\ thread_id ev = tidn /\
         match location ev with
         | Some (addr, sz) =>
           b = addr.1 /\
           Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
         | None =>
           False
         end) \/
        (tr' = [:: ev] /\ action ev = Acquire /\ thread_id ev = tidn /\
         exists rmap, match location ev with
                 | Some (laddr, sz) =>
                   sz = lksize.LKSIZE_nat /\
                   lockRes tp laddr = Some rmap /\
                   Mem.perm_order'' (rmap.1 !! b ofs) (Some Readable)
                 | None => False
                 end).
    Proof.
      intros.
      inv Hstep; simpl in *;
        try apply app_eq_refl_nil in H4;
        try inv Htstep;
        destruct U; inversion HschedN; subst; pf_cleanup;
          try (inv Hhalted);
          try (rewrite gThreadCR in Hperm');
          try  (exfalso; by eauto);
          try (apply app_inv_head in H5; subst).
       - (** initial core case *)
        exfalso.
        inv Hperm0.
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          apply CoreLanguage.initial_core_decay in Hinitial.
          destruct (Hinitial b ofs) as [_ Hsame].
          rewrite gssThreadRes in Hperm'.
          simpl in Hperm'.
          erewrite getCurPerm_correct in Hperm'.
          unfold permission_at in Hperm', Hperm.
          pose proof (restrPermMap_Cur (Hcmpt tidn cnt).1 b ofs) as Heq.
          unfold permission_at in Heq.
          erewrite <- Hsame in Hperm'.
          eapply Hperm.
          rewrite <- Heq.
          now auto.
          now auto.
        + erewrite gsoThreadRes with (cntj := cnt) in Hperm' by eauto.
          now eauto.
      - (** internal step case *)
        (*destruct (ev_step_elim _ _ _ _ _ _ Hcorestep) as [Helim _].*)
        assert (Helim:=ev_step_elim _ _ _ _ _ _ Hcorestep).
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          exfalso.
          eapply ev_elim_stable with (b := b) (ofs := ofs) in Helim; eauto.
          rewrite restrPermMap_Cur in Helim.
          rewrite Helim in Hperm.
          rewrite gssThreadRes in Hperm'.
          rewrite getCurPerm_correct in Hperm'.
          now auto.
          rewrite restrPermMap_Cur.
          destruct ((getThreadR cnt).1 !! b ofs) as [p|] eqn: Heq;
            try (destruct p); simpl in Hperm; simpl;
              eauto using perm_order.
              exfalso; now eauto using perm_order.
        + (** case it was another thread that stepped *)
          exfalso.
          setoid_rewrite gsoThreadRes with (cntj := cnt) in Hperm'; [|assumption].
          now eauto.
      - (** lock acquire*)
        (** In this case the permissions of a thread can only increase*)
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          eexists.
          do 2 right. repeat (split; eauto).
          exists pmap; split.
          reflexivity.
          split.
          assumption.
          specialize (Hangel1 b ofs).
          eapply permjoin_readable_iff in Hangel1.
          rewrite gLockSetRes gssThreadRes in Hperm'.
          rewrite! po_oo in Hangel1.
          destruct (Hangel1.1 Hperm');
            [assumption | exfalso; now auto].
        + exfalso.
          rewrite gLockSetRes gsoThreadRes in Hperm';
            now eauto.
      - (** lock release *)
        exfalso.
        clear - Hangel1 Hangel2 HisLock Hperm Hperm'.
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + rewrite gLockSetRes gssThreadRes in Hperm, Hperm'.
          specialize (Hangel1 b ofs). pf_cleanup.
          simpl in Hangel1.
          apply permjoin_readable_iff in Hangel1.
          apply Hperm.
          eapply Hangel1.
          now eauto.
        + rewrite gLockSetRes gsoThreadRes in Hperm';
            now auto.
      - (** thread spawn*)
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          eexists.
          left.
          simpl; split;
            now eauto.
        + exfalso.
          rewrite gsoAddRes gsoThreadRes in Hperm';
            now eauto.
      - (** MkLock *)
        exfalso.
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          rewrite gLockSetRes gssThreadRes in Hperm'.
          destruct (Pos.eq_dec b b0).
          * subst.
            rewrite <- Hdata_perm in Hperm'.
            destruct (Intv.In_dec ofs (Ptrofs.intval ofs0, Ptrofs.intval ofs0 + lksize.LKSIZE)%Z); auto.
            erewrite setPermBlock_same in Hperm' by eauto.
            simpl in Hperm'.
            now inv Hperm'.
            rewrite setPermBlock_other_1 in Hperm'.
            now auto.
            simpl.
            apply Intv.range_notin in n.
            destruct n; eauto.
            simpl. now lksize.lkomega.
          * rewrite <- Hdata_perm in Hperm'.
            erewrite setPermBlock_other_2 in Hperm' by eauto.
            now auto.
        + exfalso.
          rewrite gLockSetRes gsoThreadRes in Hperm';
            now eauto.
      - (** Freelock*)
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          eexists.
          right; left.
          do 3 split; simpl; eauto.
          rewrite gRemLockSetRes gssThreadRes in Hperm'.
          destruct (Pos.eq_dec b b0).
          * subst.
            rewrite <- Hdata_perm in Hperm'.
            destruct (Intv.In_dec ofs (Ptrofs.intval ofs0, Ptrofs.intval ofs0 + lksize.LKSIZE)%Z); auto.
            exfalso.
            erewrite setPermBlock_var_other_1 in Hperm'.
            now eauto.
            eapply Intv.range_notin in n; eauto.
            simpl; now lksize.lkomega.
          * exfalso.
            rewrite <- Hdata_perm in Hperm'.
            erewrite setPermBlock_var_other_2 in Hperm' by eauto.
            now auto.
        + exfalso.
          rewrite gRemLockSetRes gsoThreadRes in Hperm';
            now eauto.
    Qed.

    Lemma data_permission_increase_execution:
      forall U tr tpi mi U' tr' tpj mj
        b ofs tidn
        (cnti: containsThread tpi tidn)
        (cntj: containsThread tpj tidn)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hperm': Mem.perm_order'' ((getThreadR cntj).1 !! b ofs) (Some Readable))
        (Hperm: ~ Mem.perm_order'' ((getThreadR cnti).1 !! b ofs) (Some Readable))
        (Hvalid: Mem.valid_block mi b),
      exists tr_pre evu U'' U''' tp_pre m_pre tp_inc m_inc,
        multi_step (U, tr, tpi) mi (U'', tr ++ tr_pre, tp_pre) m_pre /\
        MachStep (U'', tr ++ tr_pre, tp_pre) m_pre
                 (U''', tr ++ tr_pre ++ [:: evu], tp_inc) m_inc /\
        multi_step (U''', tr ++ tr_pre ++ [:: evu], tp_inc) m_inc
                   (U', tr ++ tr',tpj) mj /\
        ((action evu = Spawn) \/
         (action evu = Freelock /\ thread_id evu = tidn /\
          match location evu with
          | Some (addr, sz) =>
            b = addr.1 /\
            Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
          | None =>
            False
          end) \/
         (action evu = Acquire /\ thread_id evu = tidn /\
          exists rmap, match location evu with
                  | Some (laddr, sz) =>
                    sz = lksize.LKSIZE_nat /\
                    lockRes tp_pre laddr = Some rmap /\
                    Mem.perm_order'' (rmap.1 !! b ofs) (Some Readable)
                  | None => False
                  end)).
    Proof.
      induction U as [|tid' U]; intros.
      - inversion Hexec. apply app_eq_refl_nil in H3; subst.
        pf_cleanup. by congruence.
      - inversion Hexec.
        + apply app_eq_refl_nil in H3; subst.
          pf_cleanup;
            by congruence.
        + apply app_inv_head in H6; subst.
          assert (cnt': containsThread tp' tidn)
            by (eapply step_containsThread with (tp := tpi); eauto).
          (** Case the permissions were changed by the inductive step. There are
                two subcases, either they went above readable and we don't need
                the IH or they did not and we apply the IH*)
          destruct (perm_order''_dec ((getThreadR cnt').1 !! b ofs)
                                     (Some Readable)) as [Hincr | Hstable].
          { (** Case permissions increased *)
            destruct (data_permission_increase_step _ _ _ _ H8 Hincr Hperm Hvalid)
              as [ev Hspec].
            assert (tr'0 = [:: ev])
              by (destruct Hspec as [[? _] | [[? _] | [? _]]]; subst; auto);
              subst.
            exists [::], ev, (tid' :: U), U, tpi, mi, tp', m'.
            repeat split.
            + rewrite app_nil_r.
              now constructor.
            + rewrite! app_nil_r.
              simpl.
              assumption.
            + simpl.
              now assumption.
            + destruct Hspec
                as [[Hin Haction] | [[? [Haction [Hthread_id Hloc]]]
                                    | [? [Haction [Hthread_id Hrmap]]]]];
                now eauto.
          }
          { (** Case permissions did not increase*)
            rewrite app_assoc in H9.
            (** And we can apply the IH*)
            destruct (IHU _ _ _ _ _ _ _ _ _ _ _ _ H9 Hperm' Hstable)
              as (tr_pre & evu & U'' & U''' & tp_pre & m_pre & tp_inc
                  & m_inc & Hexec_pre & Hstep & Hexec_post & Hspec); eauto.
            eapply (StepType.fstep_valid_block (initU := initU)); eauto.
            destruct Hspec as [Haction | [[Haction [Hthread_id Hloc]]
                                         | [Haction [Hthread_id Hrmap]]]].
            + (** case the increase was by a [Spawn] event *)
              exists (tr'0 ++ tr_pre), evu, U'', U''', tp_pre, m_pre, tp_inc, m_inc.
              split.
              econstructor 2; eauto.
              rewrite app_assoc.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              left; now assumption.
            + (** case the drop was by a [Freelock] event *)
              exists (tr'0 ++ tr_pre), evu, U'', U''', tp_pre, m_pre, tp_inc, m_inc.
              split.
              econstructor 2; eauto.
              rewrite app_assoc.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              right. left.
              split;
                now auto.
            + (** case the drop was by a [Acquire] event*)
              exists (tr'0 ++ tr_pre), evu, U'', U''', tp_pre, m_pre, tp_inc, m_inc.
              split.
              econstructor 2; eauto.
              rewrite app_assoc.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              do 2 right.
              now eauto.
          }
    Qed.

    (** Permission increase: A thread can increase its lock permissions on a valid block by:
- If it is spawned
- A freelock operation, turning a lock into data.
- Acquiring a lock *)
    Lemma lock_permission_increase_step:
      forall U tr tp m U' tp' m' tr' tidn b ofs
        (cnt: containsThread tp tidn)
        (cnt': containsThread tp' tidn)
        (Hstep: MachStep (U, tr, tp) m (U', tr ++ tr', tp') m')
        (Hperm': Mem.perm_order'' ((getThreadR cnt').2 !! b ofs) (Some Readable))
        (Hperm: ~ Mem.perm_order'' ((getThreadR cnt).2 !! b ofs) (Some Readable))
        (Hvalid: Mem.valid_block m b),
      exists ev,
        (tr' = [:: ev] /\ action ev = Spawn) \/
        (tr' = [:: ev] /\ action ev = Mklock /\ thread_id ev = tidn /\
         match location ev with
         | Some (addr, sz) =>
           b = addr.1 /\
           Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
         | None =>
           False
         end) \/
        (tr' = [:: ev] /\ action ev = Acquire /\ thread_id ev = tidn /\
         exists rmap, match location ev with
                 | Some (laddr, sz) =>
                   sz = lksize.LKSIZE_nat /\
                   lockRes tp laddr = Some rmap /\
                   Mem.perm_order'' (rmap.2 !! b ofs) (Some Readable)
                 | None => False
                 end).
    Proof.
      intros.
      inv Hstep; simpl in *;
        try apply app_eq_refl_nil in H4;
        try inv Htstep;
        destruct U; inversion HschedN; subst; pf_cleanup;
          try (inv Hhalted);
          try (rewrite gThreadCR in Hperm');
          try  (exfalso; by eauto);
          try (apply app_inv_head in H5; subst).
      - (** initial core case *)
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          exfalso.
          rewrite gssThreadRes in Hperm'.
          simpl in Hperm'.
          now auto.
        + (** case it was another thread that stepped *)
          exfalso.
          setoid_rewrite gsoThreadRes with (cntj := cnt) in Hperm'; [|assumption].
          now eauto.
      - (** internal step case *)
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          exfalso.
          rewrite gssThreadRes in Hperm'.
          simpl in Hperm'.
          now auto.
        + (** case it was another thread that stepped *)
          exfalso.
          setoid_rewrite gsoThreadRes with (cntj := cnt) in Hperm'; [|assumption].
          now eauto.
      - (** lock acquire*)
        (** In this case the permissions of a thread can only increase*)
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          eexists.
          do 2 right. repeat (split; eauto).
          exists pmap; split.
          reflexivity.
          split.
          assumption.
          specialize (Hangel2 b ofs).
          eapply permjoin_readable_iff in Hangel2.
          rewrite gLockSetRes gssThreadRes in Hperm'.
          rewrite! po_oo in Hangel2.
          destruct (Hangel2.1 Hperm');
            [assumption | exfalso; now auto].
        + exfalso.
          rewrite gLockSetRes gsoThreadRes in Hperm';
            now eauto.
      - (** lock release *)
        exfalso.
        clear - Hangel1 Hangel2 HisLock Hperm Hperm'.
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + rewrite gLockSetRes gssThreadRes in Hperm, Hperm'.
          specialize (Hangel2 b ofs). pf_cleanup.
          simpl in Hangel2.
          apply permjoin_readable_iff in Hangel2.
          apply Hperm.
          eapply Hangel2.
          now eauto.
        + rewrite gLockSetRes gsoThreadRes in Hperm';
            now auto.
      - (** thread spawn*)
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          eexists.
          left.
          simpl; split;
            now eauto.
        + exfalso.
          rewrite gsoAddRes gsoThreadRes in Hperm';
            now eauto.
      - (** MkLock *)
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          eexists.
          right.
          left.
          do 3 (split; simpl; eauto).
          rewrite gLockSetRes gssThreadRes in Hperm'.
          destruct (Pos.eq_dec b b0).
          * subst.
            split; auto.
            destruct (Intv.In_dec ofs (Ptrofs.intval ofs0, Ptrofs.intval ofs0 + lksize.LKSIZE)%Z); auto.
            exfalso.
            rewrite <- Hlock_perm in Hperm'.
            rewrite setPermBlock_other_1 in Hperm'.
            now auto.
            apply Intv.range_notin in n.
            destruct n; eauto.
            simpl. now lksize.lkomega.
          * exfalso.
            rewrite <- Hlock_perm in Hperm'.
            erewrite setPermBlock_other_2 in Hperm' by eauto.
            now auto.
        + exfalso.
          rewrite gLockSetRes gsoThreadRes in Hperm';
            now eauto.
      - (** Freelock*)
        exfalso.
        destruct (tid == tidn) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + pf_cleanup.
          clear - Hlock_perm Hperm Hperm' Hfreeable Hinv.
          rewrite gRemLockSetRes gssThreadRes in Hperm', Hperm.
          destruct (Pos.eq_dec b b0).
          * subst.
            rewrite <- Hlock_perm in Hperm'.
            destruct (Intv.In_dec ofs (Ptrofs.intval ofs0, Ptrofs.intval ofs0 + lksize.LKSIZE)%Z); auto.
            erewrite setPermBlock_same in Hperm' by eauto.
            simpl in Hperm';
              now auto.
            rewrite setPermBlock_other_1 in Hperm'.
            now auto.
            apply Intv.range_notin in n.
            destruct n; eauto.
            simpl. now lksize.lkomega.
          * exfalso.
            rewrite <- Hlock_perm in Hperm'.
            erewrite setPermBlock_other_2 in Hperm' by eauto.
            now auto.
        + exfalso.
          rewrite gRemLockSetRes gsoThreadRes in Hperm';
            now eauto.
    Qed.

    Lemma lock_permission_increase_execution:
      forall U tr tpi mi U' tr' tpj mj
        b ofs tidn
        (cnti: containsThread tpi tidn)
        (cntj: containsThread tpj tidn)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hperm': Mem.perm_order'' ((getThreadR cntj).2 !! b ofs) (Some Readable))
        (Hperm: ~ Mem.perm_order'' ((getThreadR cnti).2 !! b ofs) (Some Readable))
        (Hvalid: Mem.valid_block mi b),
      exists tr_pre evu U'' U''' tp_pre m_pre tp_inc m_inc,
        multi_step (U, tr, tpi) mi (U'', tr ++ tr_pre, tp_pre) m_pre /\
        MachStep (U'', tr ++ tr_pre, tp_pre) m_pre
                 (U''', tr ++ tr_pre ++ [:: evu], tp_inc) m_inc /\
        multi_step (U''', tr ++ tr_pre ++ [:: evu], tp_inc) m_inc
                   (U', tr ++ tr',tpj) mj /\
        ((action evu = Spawn) \/
         (action evu = Mklock /\ thread_id evu = tidn /\
          match location evu with
          | Some (addr, sz) =>
            b = addr.1 /\
            Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
          | None =>
            False
          end) \/
         (action evu = Acquire /\ thread_id evu = tidn /\
          exists rmap, match location evu with
                  | Some (laddr, sz) =>
                    sz = lksize.LKSIZE_nat /\
                    lockRes tp_pre laddr = Some rmap /\
                    Mem.perm_order'' (rmap.2 !! b ofs) (Some Readable)
                  | None => False
                  end)).
    Proof.
      induction U as [|tid' U]; intros.
      - inversion Hexec. apply app_eq_refl_nil in H3; subst.
        pf_cleanup. by congruence.
      - inversion Hexec.
        + apply app_eq_refl_nil in H3; subst.
          pf_cleanup;
            by congruence.
        + apply app_inv_head in H6; subst.
          assert (cnt': containsThread tp' tidn)
            by (eapply step_containsThread with (tp := tpi); eauto).
          (** Case the permissions were changed by the inductive step. There are
                two subcases, either they went above readable and we don't need
                the IH or they did not and we apply the IH*)
          destruct (perm_order''_dec ((getThreadR cnt').2 !! b ofs)
                                     (Some Readable)) as [Hincr | Hstable].
          { (** Case permissions increased *)
            destruct (lock_permission_increase_step _ _ _ _ H8 Hincr Hperm Hvalid)
              as [ev Hspec].
            assert (tr'0 = [:: ev])
              by (destruct Hspec as [[? _] | [[? _] | [? _]]]; subst; auto);
              subst.
            exists [::], ev, (tid' :: U), U, tpi, mi, tp', m'.
            repeat split.
            + rewrite app_nil_r.
              now constructor.
            + rewrite! app_nil_r.
              simpl.
              assumption.
            + simpl.
              now assumption.
            + destruct Hspec
                as [[Hin Haction] | [[? [Haction [Hthread_id Hloc]]]
                                    | [? [Haction [Hthread_id Hrmap]]]]];
                now eauto.
          }
          { (** Case permissions did not increase*)
            rewrite app_assoc in H9.
            (** And we can apply the IH*)
            destruct (IHU _ _ _ _ _ _ _ _ _ _ _ _ H9 Hperm' Hstable)
              as (tr_pre & evu & U'' & U''' & tp_pre & m_pre & tp_inc
                  & m_inc & Hexec_pre & Hstep & Hexec_post & Hspec); eauto.
            eapply (StepType.fstep_valid_block(initU := initU)); eauto.
            destruct Hspec as [Haction | [[Haction [Hthread_id Hloc]]
                                         | [Haction [Hthread_id Hrmap]]]].
            + (** case the increase was by a [Spawn] event *)
              exists (tr'0 ++ tr_pre), evu, U'', U''', tp_pre, m_pre, tp_inc, m_inc.
              split.
              econstructor 2; eauto.
              rewrite app_assoc.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              left; now assumption.
            + (** case the drop was by a [Freelock] event *)
              exists (tr'0 ++ tr_pre), evu, U'', U''', tp_pre, m_pre, tp_inc, m_inc.
              split.
              econstructor 2; eauto.
              rewrite app_assoc.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              right. left.
              split;
                now auto.
            + (** case the drop was by a [Acquire] event*)
              exists (tr'0 ++ tr_pre), evu, U'', U''', tp_pre, m_pre, tp_inc, m_inc.
              split.
              econstructor 2; eauto.
              rewrite app_assoc.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              split.
              erewrite! app_assoc in *.
              now eauto.
              do 2 right.
              now eauto.
          }
    Qed.

    Lemma permission_increase_execution:
      forall U tr tpi mi U' tr' tpj mj
        b ofs tidn
        (cnti: containsThread tpi tidn)
        (cntj: containsThread tpj tidn)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hperm: (Mem.perm_order'' ((getThreadR cntj).1 !! b ofs) (Some Readable) /\
                 ~ Mem.perm_order'' ((getThreadR cnti).1 !! b ofs) (Some Readable)) \/
                (Mem.perm_order'' ((getThreadR cntj).2 !! b ofs) (Some Readable) /\
                 ~ Mem.perm_order'' ((getThreadR cnti).2 !! b ofs) (Some Readable)))
        (Hvalid: Mem.valid_block mi b),
      exists tr_pre evu U'' U''' tp_pre m_pre tp_inc m_inc,
        multi_step (U, tr, tpi) mi (U'', tr ++ tr_pre, tp_pre) m_pre /\
        MachStep (U'', tr ++ tr_pre, tp_pre) m_pre
                 (U''', tr ++ tr_pre ++ [:: evu], tp_inc) m_inc /\
        multi_step (U''', tr ++ tr_pre ++ [:: evu], tp_inc) m_inc
                   (U', tr ++ tr',tpj) mj /\
        ((action evu = Spawn) \/
         (action evu = Freelock /\ thread_id evu = tidn /\
          match location evu with
          | Some (addr, sz) =>
            b = addr.1 /\
            Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
          | None =>
            False
          end) \/
         (action evu = Mklock /\ thread_id evu = tidn /\
          match location evu with
          | Some (addr, sz) =>
            b = addr.1 /\
            Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
          | None =>
            False
          end) \/
         (action evu = Acquire /\ thread_id evu = tidn /\
          exists rmap, match location evu with
                  | Some (laddr, sz) =>
                    sz = lksize.LKSIZE_nat /\
                    lockRes tp_pre laddr = Some rmap /\
                    (Mem.perm_order'' (rmap.1 !! b ofs) (Some Readable) \/
                     Mem.perm_order'' (rmap.2 !! b ofs) (Some Readable))
                  | None => False
                  end)).
    Proof.
      intros.
      destruct Hperm as [[Hperm Hperm'] | [Hperm Hperm']];
        [destruct (data_permission_increase_execution _ _ cnti cntj Hexec Hperm Hperm' Hvalid)
          as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hspec)
        | destruct (lock_permission_increase_execution _ _ cnti cntj Hexec Hperm Hperm' Hvalid)
          as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hspec)];
        destruct Hspec as [? | [[? [? ?]] | [? [? [? ?]]]]];
        do 8 eexists; repeat split; eauto 10;
          destruct (location x0) as [[[? ?] ?] |]; try (by exfalso);
            destruct H4 as [? [? ?]];
            do 3 right;
            repeat split; eauto.
    Qed.

    Lemma lockRes_mklock_step:
      forall U tr tp m U' tp' m' tr' laddr rmap
        (Hres: lockRes tp laddr = None)
        (Hres': lockRes tp' laddr = Some rmap)
        (Hstep: MachStep (U, tr, tp) m (U', tr ++ tr', tp') m'),
      exists ev,
        tr' = [:: ev] /\ action ev = Mklock /\
        location ev = Some (laddr, lksize.LKSIZE_nat) /\
        lockRes tp' laddr = Some (empty_map, empty_map).
    Proof.
      intros.
      Opaque lockRes.
      inv Hstep; simpl in *;
        try apply app_eq_refl_nil in H4;
        try inv Htstep;
        destruct U; inversion HschedN; subst; pf_cleanup;
          try (inv Hhalted);
          try (rewrite gsoThreadCLPool in Hres');
          try (rewrite gsoThreadLPool in Hres');
          try (rewrite gsoAddLPool gsoThreadLPool in Hres');
          try (congruence);
          try (apply app_inv_head in H5; subst);
            try (destruct (EqDec_address (b, Ptrofs.intval ofs) laddr); subst;
                 [setoid_rewrite Hres in HisLock | rewrite gsoLockRes in Hres'; auto; rewrite gsoThreadLPool in Hres'; auto];
                 congruence).
      destruct (EqDec_address (b, Ptrofs.intval ofs) laddr); subst.
      eexists; repeat split; eauto.
      rewrite gssLockRes; reflexivity.
      rewrite gsoLockRes in Hres'; auto; rewrite gsoThreadLPool in Hres'; auto.
      rewrite Hres in Hres'; discriminate.
      destruct (EqDec_address (b, Ptrofs.intval ofs) laddr); subst.
      setoid_rewrite Hres in His_lock; congruence.
      rewrite gsolockResRemLock in Hres'; auto; rewrite gsoThreadLPool in Hres'; auto.
        by congruence.
    Qed.

    Lemma lockRes_mklock_execution:
      forall U tr tpi mi U' tpj mj tr' laddr rmapj
        (Hres: lockRes tpi laddr = None)
        (Hres': lockRes tpj laddr = Some rmapj)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj),
      exists tr_pre evu U'' U''' tp_pre m_pre tp_mk m_mk,
        multi_step (U, tr, tpi) mi (U'', tr ++ tr_pre, tp_pre) m_pre /\
        MachStep (U'', tr ++ tr_pre, tp_pre) m_pre
                 (U''', tr ++ tr_pre ++ [:: evu], tp_mk) m_mk /\
        multi_step (U''', tr ++ tr_pre ++ [:: evu], tp_mk) m_mk
                   (U', tr ++ tr',tpj) mj /\
        action evu = Mklock /\
        location evu = Some (laddr, lksize.LKSIZE_nat) /\
        lockRes tp_mk laddr = Some (empty_map, empty_map).
    Proof.
      induction U as [|tid' U]; intros.
      - inversion Hexec. apply app_eq_refl_nil in H3; subst.
        rewrite Hres in Hres'; inv Hres';
          by congruence.
      - inversion Hexec.
        + apply app_eq_refl_nil in H3; subst.
          rewrite Hres in Hres'; inv Hres';
            by congruence.
        + apply app_inv_head in H6; subst.
          destruct (lockRes tp' laddr) as [rmap'|] eqn:Hres''.
          { (** Case the lock is created*)
            destruct (lockRes_mklock_step _ _ Hres Hres'' H8)
              as (ev & ? & Hact & Hloc & Hres_empty);
              subst.
            exists [::], ev, (tid' :: U), U, tpi, mi, tp', m'.
            simpl. rewrite! app_nil_r.
            repeat (split); eauto.
            econstructor; now eauto.
          }
          { (** Case the lock is still not there *)
            rewrite app_assoc in H9.
            destruct (IHU _ _ _ _ _ _ _ _ _ Hres'' Hres' H9)
              as (tr_pre & evu & U'' & U''' & tp_pre & m_pre
                  & tp_mk & m_mk & Hexec_pre & Hstep_mk & Hexec_post
                  & Hactionu & Hlocu & Hres_mk).
            erewrite! app_assoc in *.
            do 8 eexists; repeat split; eauto.
            econstructor; eauto.
            erewrite app_assoc. eauto.
            erewrite! app_assoc; eauto.
            erewrite! app_assoc; eauto.
          }
    Qed.

    Lemma lockRes_freelock_step:
      forall U tr tp m U' tp' m' tr' laddr rmap
        (Hres: lockRes tp laddr = Some rmap)
        (Hres': lockRes tp' laddr = None)
        (Hstep: MachStep (U, tr, tp) m (U', tr ++ tr', tp') m'),
      exists ev,
        tr' = [:: ev] /\ action ev = Freelock /\
        location ev = Some (laddr, lksize.LKSIZE_nat) /\
        forall b ofs, rmap.1 !! b ofs = None /\ rmap.2 !! b ofs = None.
    Proof.
      intros.
      inv Hstep; simpl in *;
        try apply app_eq_refl_nil in H4;
        try inv Htstep;
        destruct U; inversion HschedN; subst; pf_cleanup;
          try (inv Hhalted);
          try (rewrite gsoThreadCLPool in Hres');
          try (rewrite gsoThreadLPool in Hres');
          try (rewrite gsoAddLPool gsoThreadLPool in Hres');
          try (congruence);
          apply app_inv_head in H5; subst;
            try (destruct (EqDec_address (b, Ptrofs.intval ofs) laddr); subst;
                 [rewrite gssLockRes in Hres' | rewrite gsoLockRes in Hres'; auto; rewrite gsoThreadLPool in Hres'; auto];
                 congruence).
      destruct (EqDec_address (b, Ptrofs.intval ofs) laddr); subst.
      setoid_rewrite Hres in His_lock; inv His_lock.
      eexists; repeat split; eauto;
        now eapply Hrmap.
      rewrite gsolockResRemLock in Hres'; auto; rewrite gsoThreadLPool in Hres'; auto.
        by congruence.
    Qed.

    Lemma lockRes_freelock_execution:
      forall U tr tpi mi U' tpj mj tr' laddr rmapi
        (Hres: lockRes tpi laddr = Some rmapi)
        (Hres': lockRes tpj laddr = None)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj),
      exists tr_pre evu U'' U''' tp_pre m_pre tp_mk m_mk,
        multi_step (U, tr, tpi) mi (U'', tr ++ tr_pre, tp_pre) m_pre /\
        MachStep (U'', tr ++ tr_pre, tp_pre) m_pre
                 (U''', tr ++ tr_pre ++ [:: evu], tp_mk) m_mk /\
        multi_step (U''', tr ++ tr_pre ++ [:: evu], tp_mk) m_mk
                   (U', tr ++ tr',tpj) mj /\
        action evu = Freelock /\
        location evu = Some (laddr, lksize.LKSIZE_nat) /\
        exists rmap,
          lockRes tp_pre laddr = Some rmap /\
          forall b ofs, rmap.1 !! b ofs = None /\
                   rmap.2 !! b ofs = None.
    Proof.
      induction U as [|tid' U]; intros.
      - inversion Hexec. apply app_eq_refl_nil in H3; subst.
        rewrite Hres in Hres'; inv Hres';
          by congruence.
      - inversion Hexec.
        + apply app_eq_refl_nil in H3; subst.
          rewrite Hres in Hres'; inv Hres';
            by congruence.
        + apply app_inv_head in H6; subst.
          destruct (lockRes tp' laddr) as [rmap'|] eqn:Hres''.
          { (** Case the lock is not freed yet*)
            rewrite app_assoc in H9.
            destruct (IHU _ _ _ _ _ _ _ _ _ Hres'' Hres' H9)
              as (tr_pre & evu & U'' & U''' & tp_pre & m_pre
                  & tp_mk & m_mk & Hexec_pre & Hstep_mk & Hexec_post
                  & Hactionu & Hlocu & Hres_mk).
            erewrite! app_assoc in *.
            do 8 eexists; repeat split; eauto.
            econstructor; eauto.
            erewrite app_assoc. eauto.
            erewrite! app_assoc; eauto.
            erewrite! app_assoc; eauto.
          }
          { destruct (lockRes_freelock_step _ _ Hres Hres'' H8)
              as (ev & ? & Hact & Hloc & Hres_empty);
              subst.
            exists [::], ev, (tid' :: U), U, tpi, mi, tp', m'.
            simpl. rewrite! app_nil_r.
            repeat split; eauto;
              econstructor; eauto.
          }
    Qed.

    Lemma lockRes_data_permission_decrease_step:
      forall U tr tp m U' tp' m' tr' laddr rmap rmap' b ofs
        (Hres: lockRes tp laddr = Some rmap)
        (Hres': lockRes tp' laddr = Some rmap')
        (Hstep: MachStep (U, tr, tp) m (U', tr ++ tr', tp') m')
        (Hperm: Mem.perm_order'' (rmap.1 !! b ofs) (Some Readable))
        (Hperm': ~ Mem.perm_order'' (rmap'.1 !! b ofs) (Some Readable)),
      exists ev,
        tr' = [:: ev] /\ action ev = Acquire /\
        location ev = Some (laddr, lksize.LKSIZE_nat).
    Proof.
      intros.
      inv Hstep; simpl in *;
        try apply app_eq_refl_nil in H4;
        try inv Htstep;
        destruct U; inversion HschedN; subst; pf_cleanup;
          try (inv Hhalted);
          try (rewrite gsoThreadCLPool in Hres');
          try (rewrite Hres in Hres'; inv Hres');
          try  (exfalso; by eauto);
          try (apply app_inv_head in H5; subst).
      - (** initial core step case *)
        exfalso.
        rewrite gsoThreadLPool in Hres'.
        rewrite Hres in Hres'; inv Hres';
          now auto.
      - (** internal step case *)
        exfalso.
        rewrite gsoThreadLPool in Hres'.
        rewrite Hres in Hres'; inv Hres';
          now auto.
      - (** lock acquire*)
        (** In this case the permissions of a lock can decrease*)
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          eexists; split; eauto.
        + exfalso.
          rewrite gsoLockRes in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
      - (** lock release *)
        (** In this case the permissions of a lock can only increase; contradiction.*)
        exfalso.
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          setoid_rewrite Hres in HisLock; inv HisLock.
          rewrite (Hrmap b ofs).1 in Hperm.
          simpl in Hperm.
          assumption.
        + rewrite gsoLockRes in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
      - (** thread spawn*)
        rewrite gsoAddLPool gsoThreadLPool in Hres'.
        rewrite Hres' in Hres; inv Hres;
          now eauto.
      - (** MkLock *)
        exfalso.
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          setoid_rewrite Hres in HlockRes.
          discriminate.
        + rewrite gsoLockRes in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
      - exfalso.
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          rewrite gsslockResRemLock in Hres'.
          discriminate.
        + rewrite gsolockResRemLock in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
    Qed.


    Lemma lockRes_data_permission_decrease_execution:
      forall U tr tpi mi U' tpj mj tr' laddr rmapi rmapj b ofs
        (Hres: lockRes tpi laddr = Some rmapi)
        (Hres': lockRes tpj laddr = Some rmapj)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hperm: Mem.perm_order'' (rmapi.1 !! b ofs) (Some Readable))
        (Hperm': ~ Mem.perm_order'' (rmapj.1 !! b ofs) (Some Readable)),
      exists v ev,
        nth_error tr' v = Some ev /\ action ev = Acquire /\
        location ev = Some (laddr, lksize.LKSIZE_nat).
    Proof.
      induction U as [|tid' U]; intros.
      - inversion Hexec. apply app_eq_refl_nil in H3; subst.
        rewrite Hres in Hres'; inv Hres';
          by congruence.
      - inversion Hexec.
        + apply app_eq_refl_nil in H3; subst.
          rewrite Hres in Hres'; inv Hres';
            by congruence.
        + apply app_inv_head in H6; subst.
          destruct (lockRes tp' laddr) as [rmap'|] eqn:Hres''.
          { (** Case the lock is still there*)
            destruct (perm_order''_dec (rmap'.1 !! b ofs)
                                       (Some Readable)) as [Hstable | Hdecr].
            { (** Case permissions did not decrease*)
              rewrite app_assoc in H9.
              (** And we can apply the IH*)
              destruct (IHU _ _ _ _ _ _ _ _ _ _ _ _ Hres'' Hres' H9 Hstable Hperm')
                as (v & ev & Hnth & Hact & Hloc).
              exists ((length tr'0) + v)%nat, ev.
              split.
              rewrite <- nth_error_app; auto.
              now auto.
            }
            { (** Case permissions decreased *)
              destruct (lockRes_data_permission_decrease_step _ _ _ _ Hres Hres'' H8 Hperm Hdecr)
                as (ev & ? & Hact & Hloc); subst.
              exists O, ev.
              simpl;
                now auto.
            }
          }
          { (** Case the lock is removed *)
            exfalso.
            eapply lockRes_freelock_step in H8; eauto.
            destruct H8 as (? & ? & ? & ? & Hempty).
            specialize (Hempty b ofs).
            rewrite Hempty.1 in Hperm.
            simpl in Hperm.
            assumption.
          }
    Qed.

    Lemma lockRes_lock_permission_decrease_step:
      forall U tr tp m U' tp' m' tr' laddr rmap rmap' b ofs
        (Hres: lockRes tp laddr = Some rmap)
        (Hres': lockRes tp' laddr = Some rmap')
        (Hstep: MachStep (U, tr, tp) m (U', tr ++ tr', tp') m')
        (Hperm: Mem.perm_order'' (rmap.2 !! b ofs) (Some Readable))
        (Hperm': ~ Mem.perm_order'' (rmap'.2 !! b ofs) (Some Readable)),
      exists ev,
        tr' = [:: ev] /\ action ev = Acquire /\
        location ev = Some (laddr, lksize.LKSIZE_nat).
    Proof.
      intros.
      inv Hstep; simpl in *;
        try apply app_eq_refl_nil in H4;
        try inv Htstep;
        destruct U; inversion HschedN; subst; pf_cleanup;
          try (inv Hhalted);
          try (rewrite gsoThreadCLPool in Hres');
          try (rewrite Hres in Hres'; inv Hres');
          try  (exfalso; by eauto);
          try apply app_inv_head in H5; subst.
      - (** initial core step case *)
        exfalso.
        rewrite gsoThreadLPool in Hres'.
        rewrite Hres in Hres'; inv Hres';
          now auto.
      - (** internal step case *)
        exfalso.
        rewrite gsoThreadLPool in Hres'.
        rewrite Hres in Hres'; inv Hres';
          now auto.
      - (** lock acquire*)
        (** In this case the permissions of a lock can decrease*)
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          eexists; split; eauto.
        + exfalso.
          rewrite gsoLockRes in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
      - (** lock release *)
        (** In this case the permissions of a lock can only increase; contradiction.*)
        exfalso.
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          setoid_rewrite Hres in HisLock; inv HisLock.
          rewrite (Hrmap b ofs).2 in Hperm.
          simpl in Hperm.
          assumption.
        + rewrite gsoLockRes in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
      - (** thread spawn*)
        rewrite gsoAddLPool gsoThreadLPool in Hres'.
        rewrite Hres' in Hres; inv Hres;
          now eauto.
      - (** MkLock *)
        exfalso.
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          setoid_rewrite Hres in HlockRes.
          discriminate.
        + rewrite gsoLockRes in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
      - exfalso.
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          rewrite gsslockResRemLock in Hres'.
          discriminate.
        + rewrite gsolockResRemLock in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
    Qed.

    Lemma lockRes_lock_permission_decrease_execution:
      forall U tr tpi mi U' tpj mj tr' laddr rmapi rmapj b ofs
        (Hres: lockRes tpi laddr = Some rmapi)
        (Hres': lockRes tpj laddr = Some rmapj)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hperm: Mem.perm_order'' (rmapi.2 !! b ofs) (Some Readable))
        (Hperm': ~ Mem.perm_order'' (rmapj.2 !! b ofs) (Some Readable)),
      exists v ev,
        nth_error tr' v = Some ev /\ action ev = Acquire /\
        location ev = Some (laddr, lksize.LKSIZE_nat).
    Proof.
      induction U as [|tid' U]; intros.
      - inversion Hexec. apply app_eq_refl_nil in H3; subst.
        rewrite Hres in Hres'; inv Hres';
          by congruence.
      - inversion Hexec.
        + apply app_eq_refl_nil in H3; subst.
          rewrite Hres in Hres'; inv Hres';
            by congruence.
        + apply app_inv_head in H6; subst.
          destruct (lockRes tp' laddr) as [rmap'|] eqn:Hres''.
          { (** Case the lock is still there*)
            destruct (perm_order''_dec (rmap'.2 !! b ofs)
                                       (Some Readable)) as [Hstable | Hdecr].
            { (** Case permissions did not decrease*)
              rewrite app_assoc in H9.
              (** And we can apply the IH*)
              destruct (IHU _ _ _ _ _ _ _ _ _ _ _ _ Hres'' Hres' H9 Hstable Hperm')
                as (v & ev & Hnth & Hact & Hloc).
              exists ((length tr'0) + v)%nat, ev.
              split.
              rewrite <- nth_error_app; auto.
              now auto.
            }
            { (** Case permissions decreased *)
              destruct (lockRes_lock_permission_decrease_step _ _ _ _ Hres Hres'' H8 Hperm Hdecr)
                as (ev & ? & Hact & Hloc); subst.
              exists O, ev.
              simpl;
                now auto.
            }
          }
          { (** Case the lock is removed *)
            exfalso.
            eapply lockRes_freelock_step in H8; eauto.
            destruct H8 as (? & ? & ? & ? & Hempty).
            specialize (Hempty b ofs).
            rewrite Hempty.2 in Hperm.
            simpl in Hperm.
            assumption.
          }
    Qed.

    Lemma lockRes_permission_decrease_execution:
      forall U tr tpi mi U' tpj mj tr' laddr rmapi rmapj b ofs
        (Hres: lockRes tpi laddr = Some rmapi)
        (Hres': lockRes tpj laddr = Some rmapj)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hperm: (Mem.perm_order'' (rmapi.1 !! b ofs) (Some Readable) /\
                 ~ Mem.perm_order'' (rmapj.1 !! b ofs) (Some Readable)) \/
                (Mem.perm_order'' (rmapi.2 !! b ofs) (Some Readable) /\
                 ~ Mem.perm_order'' (rmapj.2 !! b ofs) (Some Readable))),
      exists v ev,
        nth_error tr' v = Some ev /\ action ev = Acquire /\
        location ev = Some (laddr, lksize.LKSIZE_nat).
    Proof.
      intros.
      destruct Hperm as [[Hperm Hperm'] | [Hperm Hperm']];
        eauto using lockRes_data_permission_decrease_execution,
        lockRes_lock_permission_decrease_execution.
    Qed.

    Lemma lockRes_data_permission_increase_step:
      forall U tr tp m U' tp' m' tr' laddr rmap rmap' b ofs
        (Hres: lockRes tp laddr = Some rmap)
        (Hres': lockRes tp' laddr = Some rmap')
        (Hstep: MachStep (U, tr, tp) m (U', tr ++ tr', tp') m')
        (Hperm: ~ Mem.perm_order'' (rmap.1 !! b ofs) (Some Readable))
        (Hperm': Mem.perm_order'' (rmap'.1 !! b ofs) (Some Readable)),
      exists ev,
        tr' = [:: ev] /\ action ev = Release /\
        location ev = Some (laddr, lksize.LKSIZE_nat).
    Proof.
      intros.
      inv Hstep; simpl in *;
        try apply app_eq_refl_nil in H4;
        try inv Htstep;
        destruct U; inversion HschedN; subst; pf_cleanup;
          try (inv Hhalted);
          try (rewrite gsoThreadCLPool in Hres');
          try (rewrite Hres in Hres'; inv Hres');
          try  (exfalso; by eauto);
          try apply app_inv_head in H5; subst.
      - (** initial core step case *)
        exfalso.
        rewrite gsoThreadLPool in Hres'.
        rewrite Hres in Hres'; inv Hres';
          now auto.
      - (** internal step case *)
        exfalso.
        rewrite gsoThreadLPool in Hres'.
        rewrite Hres in Hres'; inv Hres';
          now auto.
      - (** lock acquire*)
        (** In this case the permissions of a lock can only decrease; contradiction*)
        exfalso.
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          setoid_rewrite Hres in HisLock; inv HisLock.
          specialize (Hangel1 b ofs).
          rewrite gssLockRes in Hres'.
          inv Hres'.
          rewrite empty_map_spec in Hperm'.
          simpl in Hperm'.
          assumption.
        + exfalso.
          rewrite gsoLockRes in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
      - (** lock release *)
        (** In this case the permissions of a lock can increase.*)
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          setoid_rewrite Hres in HisLock; inv HisLock.
          eexists; split;
            now eauto.
        + exfalso.
          rewrite gsoLockRes in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
      - (** thread spawn*)
        rewrite gsoAddLPool gsoThreadLPool in Hres'.
        rewrite Hres' in Hres; inv Hres;
          now eauto.
      - (** MkLock *)
        exfalso.
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          setoid_rewrite Hres in HlockRes.
          discriminate.
        + rewrite gsoLockRes in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
      - exfalso.
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          rewrite gsslockResRemLock in Hres'.
          discriminate.
        + rewrite gsolockResRemLock in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
    Qed.

    Lemma lockRes_lock_permission_increase_step:
      forall U tr tp m U' tp' m' tr' laddr rmap rmap' b ofs
        (Hres: lockRes tp laddr = Some rmap)
        (Hres': lockRes tp' laddr = Some rmap')
        (Hstep: MachStep (U, tr, tp) m (U', tr ++ tr', tp') m')
        (Hperm: ~ Mem.perm_order'' (rmap.2 !! b ofs) (Some Readable))
        (Hperm': Mem.perm_order'' (rmap'.2 !! b ofs) (Some Readable)),
      exists ev,
        tr' = [:: ev] /\ action ev = Release /\
        location ev = Some (laddr, lksize.LKSIZE_nat).
    Proof.
      intros.
      inv Hstep; simpl in *;
        try apply app_eq_refl_nil in H4;
        try inv Htstep;
        destruct U; inversion HschedN; subst; pf_cleanup;
          try (inv Hhalted);
          try (rewrite gsoThreadCLPool in Hres');
          try (rewrite Hres in Hres'; inv Hres');
          try  (exfalso; by eauto);
          try apply app_inv_head in H5; subst.
      - (** initial core step case *)
        exfalso.
        rewrite gsoThreadLPool in Hres'.
        rewrite Hres in Hres'; inv Hres';
          now auto.
      - (** internal step case *)
        exfalso.
        rewrite gsoThreadLPool in Hres'.
        rewrite Hres in Hres'; inv Hres';
          now auto.
      - (** lock acquire*)
        (** In this case the permissions of a lock can only decrease; contradiction*)
        exfalso.
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          setoid_rewrite Hres in HisLock; inv HisLock.
          specialize (Hangel2 b ofs).
          rewrite gssLockRes in Hres'.
          inv Hres'.
          rewrite empty_map_spec in Hperm'.
          simpl in Hperm'.
          assumption.
        + exfalso.
          rewrite gsoLockRes in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
      - (** lock release *)
        (** In this case the permissions of a lock can increase.*)
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          setoid_rewrite Hres in HisLock; inv HisLock.
          eexists; split;
            now eauto.
        + exfalso.
          rewrite gsoLockRes in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
      - (** thread spawn*)
        rewrite gsoAddLPool gsoThreadLPool in Hres'.
        rewrite Hres' in Hres; inv Hres;
          now eauto.
      - (** MkLock *)
        exfalso.
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          setoid_rewrite Hres in HlockRes.
          discriminate.
        + rewrite gsoLockRes in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
      - exfalso.
        destruct (EqDec_address laddr (b0, Ptrofs.intval ofs0)).
        + inv e.
          rewrite gsslockResRemLock in Hres'.
          discriminate.
        + rewrite gsolockResRemLock in Hres'; auto.
          rewrite gsoThreadLPool in Hres'.
          rewrite Hres' in Hres; inv Hres;
            now eauto.
    Qed.

    Fixpoint lockRes_data_permission_add_execution U
             U' tr tpi mi tpj mj tr' laddr rmapj b ofs
             (Hres: lockRes tpi laddr = None)
             (Hres': lockRes tpj laddr = Some rmapj)
             (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
             (Hperm': Mem.perm_order'' (rmapj.1 !! b ofs) (Some Readable)) {struct U}:
      exists v ev,
        nth_error tr' v = Some ev /\ action ev = Release /\
        location ev = Some (laddr, lksize.LKSIZE_nat)
    with
    lockRes_data_permission_increase_execution U {struct U}:
      forall U' tr tpi mi tpj mj tr' laddr rmapi rmapj b ofs
        (Hres: lockRes tpi laddr = Some rmapi)
        (Hres': lockRes tpj laddr = Some rmapj)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hperm: ~ Mem.perm_order'' (rmapi.1 !! b ofs) (Some Readable))
        (Hperm': Mem.perm_order'' (rmapj.1 !! b ofs) (Some Readable)),
      exists v ev,
        nth_error tr' v = Some ev /\ action ev = Release /\
        location ev = Some (laddr, lksize.LKSIZE_nat).
    Proof.
      { intros.
        destruct U.
        - inversion Hexec. subst tpi.
            by congruence.
        - inversion Hexec. subst tpi.
            by congruence.
            subst.
            apply app_inv_head in H6; subst. clear Hexec.
            destruct (lockRes tp' laddr) as [rmap'|] eqn:Hres''.
            { (** Case the lock is there*)
              eapply lockRes_mklock_step in H8; eauto.
              destruct H8 as (ev & ? & ? & ? & ?); subst.
              assert (Hperm'': ~ Mem.perm_order'' (((empty_map, empty_map).1) !! b ofs)
                                 (Some Readable))
                by (rewrite empty_map_spec; simpl; intro Hcontra; auto).
              rewrite app_assoc in H9.
              destruct (lockRes_data_permission_increase_execution _ _ _ _ _ _ _ _ _ _ _ _ _ H2 Hres' H9 Hperm'' Hperm')
                as (u & eu & Hnth & ? & ?).
              exists (S u), eu.
              repeat split; eauto.
            }
            { (** Case the lock is not there*)
              rewrite app_assoc in H9.
              destruct (lockRes_data_permission_add_execution _ _ _ _ _ _ _ _ _ _ _ _
                                                              Hres'' Hres' H9 Hperm')
                as (v & ev & Hnth & Hact & Hloc).
              exists ((length tr'0) + v)%nat, ev.
              split.
              rewrite <- nth_error_app; auto.
              now auto.
            }
      }
      { intros.
        destruct U.
        - inversion Hexec. subst tpi.
            by congruence.
        - inversion Hexec.
          subst tpi. by congruence.
          subst.
          apply app_inv_head in H6; subst.
          clear Hexec.
          destruct (lockRes tp' laddr) as [rmap'|] eqn:Hres''.
          { (** Case the lock is there*)
            destruct (perm_order''_dec (rmap'.1 !! b ofs)
                                       (Some Readable)) as [Hincr | Hstable].
            { (** Case permissions did increase*)
              eapply lockRes_data_permission_increase_step in H8; eauto.
              destruct H8 as (ev & ? & ? & ?).
              subst.
              exists O, ev. repeat split; auto.
            }
            { (** Case permissions did not increase*)
              rewrite app_assoc in H9.
              (** And we can apply the IH*)
              destruct (lockRes_data_permission_increase_execution
                          _ _ _ _ _ _ _ _ _ _ _ _ _ Hres'' Hres' H9 Hstable Hperm')
                as (v & ev & Hnth & Hact & Hloc).
              exists ((length tr'0) + v)%nat, ev.
              split.
              rewrite <- nth_error_app; auto.
              now auto.
            }
          }
          { (** Case the lock is not there*)
            rewrite app_assoc in H9.
            destruct (lockRes_data_permission_add_execution _ _ _ _ _ _ _ _ _ _ _ _
                                                            Hres'' Hres' H9 Hperm')
              as (v & ev & Hnth & Hact & Hloc).
            exists ((length tr'0) + v)%nat, ev.
            split.
            rewrite <- nth_error_app; auto.
            now auto.
          }
      }
    Qed.

    Fixpoint lockRes_lock_permission_add_execution U
             U' tr tpi mi tpj mj tr' laddr rmapj b ofs
             (Hres: lockRes tpi laddr = None)
             (Hres': lockRes tpj laddr = Some rmapj)
             (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
             (Hperm': Mem.perm_order'' (rmapj.2 !! b ofs) (Some Readable)) {struct U}:
      exists v ev,
        nth_error tr' v = Some ev /\ action ev = Release /\
        location ev = Some (laddr, lksize.LKSIZE_nat)
    with
    lockRes_lock_permission_increase_execution U {struct U}:
      forall U' tr tpi mi tpj mj tr' laddr rmapi rmapj b ofs
        (Hres: lockRes tpi laddr = Some rmapi)
        (Hres': lockRes tpj laddr = Some rmapj)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hperm: ~ Mem.perm_order'' (rmapi.2 !! b ofs) (Some Readable))
        (Hperm': Mem.perm_order'' (rmapj.2 !! b ofs) (Some Readable)),
      exists v ev,
        nth_error tr' v = Some ev /\ action ev = Release /\
        location ev = Some (laddr, lksize.LKSIZE_nat).
    Proof.
      { intros.
        destruct U.
        - inversion Hexec. subst tpi.
            by congruence.
        - inversion Hexec. subst tpi.
            by congruence.
            subst.
            apply app_inv_head in H6; subst. clear Hexec.
            destruct (lockRes tp' laddr) as [rmap'|] eqn:Hres''.
            { (** Case the lock is there*)
              eapply lockRes_mklock_step in H8; eauto.
              destruct H8 as (ev & ? & ? & ? & ?); subst.
              assert (Hperm'': ~ Mem.perm_order'' (((empty_map, empty_map).1)
                                                     !! b ofs) (Some Readable))
                by (rewrite empty_map_spec; simpl; intro Hcontra; auto).
              rewrite app_assoc in H9.
              destruct (lockRes_lock_permission_increase_execution
                          _ _ _ _ _ _ _ _ _ _ _ _ _ H2 Hres' H9 Hperm'' Hperm')
                as (u & eu & Hnth & ? & ?).
              exists (S u), eu.
              repeat split; eauto.
            }
            { (** Case the lock is not there*)
              rewrite app_assoc in H9.
              destruct (lockRes_lock_permission_add_execution _ _ _ _ _ _ _ _ _ _ _ _
                                                              Hres'' Hres' H9 Hperm')
                as (v & ev & Hnth & Hact & Hloc).
              exists ((length tr'0) + v)%nat, ev.
              split.
              rewrite <- nth_error_app; auto.
              now auto.
            }
      }
      { intros.
        destruct U.
        - inversion Hexec. subst tpi.
            by congruence.
        - inversion Hexec.
          subst tpi. by congruence.
          subst.
          apply app_inv_head in H6; subst.
          clear Hexec.
          destruct (lockRes tp' laddr) as [rmap'|] eqn:Hres''.
          { (** Case the lock is there*)
            destruct (perm_order''_dec (rmap'.2 !! b ofs)
                                       (Some Readable)) as [Hincr | Hstable].
            { (** Case permissions did increase*)
              eapply lockRes_lock_permission_increase_step in H8; eauto.
              destruct H8 as (ev & ? & ? & ?).
              subst.
              exists O, ev. repeat split; auto.
            }
            { (** Case permissions did not increase*)
              rewrite app_assoc in H9.
              (** And we can apply the IH*)
              destruct (lockRes_lock_permission_increase_execution
                          _ _ _ _ _ _ _ _ _ _ _ _ _ Hres'' Hres' H9 Hstable Hperm')
                as (v & ev & Hnth & Hact & Hloc).
              exists ((length tr'0) + v)%nat, ev.
              split.
              rewrite <- nth_error_app; auto.
              now auto.
            }
          }
          { (** Case the lock is not there*)
            rewrite app_assoc in H9.
            destruct (lockRes_lock_permission_add_execution _ _ _ _ _ _ _ _ _ _ _ _
                                                            Hres'' Hres' H9 Hperm')
              as (v & ev & Hnth & Hact & Hloc).
            exists ((length tr'0) + v)%nat, ev.
            split.
            rewrite <- nth_error_app; auto.
            now auto.
          }
      }
    Qed.

    Lemma lockRes_permission_increase_execution:
      forall U tr tpi mi U' tpj mj tr' laddr rmapi rmapj b ofs
        (Hres: lockRes tpi laddr = Some rmapi)
        (Hres': lockRes tpj laddr = Some rmapj)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hperm: (~ Mem.perm_order'' (rmapi.1 !! b ofs) (Some Readable) /\
                 Mem.perm_order'' (rmapj.1 !! b ofs) (Some Readable)) \/
                (~ Mem.perm_order'' (rmapi.2 !! b ofs) (Some Readable) /\
                 Mem.perm_order'' (rmapj.2 !! b ofs) (Some Readable))),
      exists v ev,
        nth_error tr' v = Some ev /\ action ev = Release /\
        location ev = Some (laddr, lksize.LKSIZE_nat).
    Proof.
      intros.
      destruct Hperm as [[Hperm Hperm'] | [Hperm Hperm']];
        eauto using lockRes_data_permission_increase_execution,
        lockRes_lock_permission_increase_execution.
    Qed.

    Lemma thread_spawn_step:
      forall U tr tp m U' tp' m' tr' tidn
        (cnt: ~ containsThread tp tidn)
        (cnt': containsThread tp' tidn)
        (Hstep: MachStep (U, tr, tp) m (U', tr ++ tr', tp') m'),
      exists ev,
        tr' = [:: ev] /\ action ev = Spawn.
    Proof.
      intros;
        inv Hstep; simpl in *;
          try apply app_eq_refl_nil in H4;
          try inv Htstep;
          destruct U; inversion HschedN; subst; pf_cleanup;
            try (inv Hhalted);
            try  (exfalso; by eauto);
            apply app_inv_head in H5; subst.
      eexists; simpl; split;
        now eauto.
    Qed.

    Lemma thread_spawn_execution:
      forall U tr tpi mi U' tr' tpj mj
        tidn
        (cnti: ~ containsThread tpi tidn)
        (cntj: containsThread tpj tidn)
        (Hexec: multi_step (U, tr, tpi) mi (U', tr ++ tr', tpj) mj),
      exists tr_pre evu U'' U''' tp_pre m_pre tp_inc m_inc,
        multi_step (U, tr, tpi) mi (U'', tr ++ tr_pre, tp_pre) m_pre /\
        MachStep (U'', tr ++ tr_pre, tp_pre) m_pre
                 (U''', tr ++ tr_pre ++ [:: evu], tp_inc) m_inc /\
        multi_step (U''', tr ++ tr_pre ++ [:: evu], tp_inc) m_inc
                   (U', tr ++ tr',tpj) mj /\
        action evu = Spawn.
    Proof.
      induction U as [|tid' U]; intros.
      - inversion Hexec. apply app_eq_refl_nil in H3; subst.
        pf_cleanup. by congruence.
      - inversion Hexec.
        + apply app_eq_refl_nil in H3; subst.
          pf_cleanup;
            by congruence.
        + apply app_inv_head in H6; subst.
          destruct (OrdinalPool.containsThread_dec tidn tp') as [cnt' | not_cnt'].
          * destruct (thread_spawn_step _ cnti cnt' H8) as [ev [? ?]].
            subst.
            exists [:: ], ev, (tid' :: U)%SEQ, U, tpi, mi, tp', m'.
            split.
            rewrite app_nil_r. constructor.
            split.
            simpl.
            rewrite app_nil_r.
            assumption.
            split. simpl; assumption.
            assumption.
          * erewrite! app_assoc in *.
            destruct (IHU _ _ _ _ _ _ _ _ not_cnt' cntj H9)
              as (tr_pre & evu & U'' & U''' & tp_pre & m_pre & tp_inc & m_inc
                  & Hexec_pre & Hstep & Hexec_post & Hevu).
            exists (tr'0 ++ tr_pre), evu, U'', U''', tp_pre, m_pre, tp_inc, m_inc.
            erewrite! app_assoc in *.
            repeat (split); eauto.
            rewrite <- app_assoc.
            econstructor; eauto.
            rewrite! app_assoc;
              now eauto.
    Qed.
  End FineGrainedExecutions.

  Section SCExecutions.

    Context
      {Sem : Semantics}
      {initU : seq.seq nat}
      {SemAx : CoreLanguage.SemAxioms}
      {SemD : CoreLanguage.SemDet}.

    Existing Instance BareMachine.resources.
    Existing Instance HybridFineMachine.scheduler.
    Existing Instance OrdinalPool.OrdinalThreadPool.
    Existing Instance BareMachine.BareMachineSig.
    Existing Instance BareDilMem.
    Existing Instance bareMach.

    Opaque containsThread mem_compatible.
    Lemma start_thread_det:
      forall tp m tid (cnt: containsThread tp tid) tp' m' tp'' m''
        (Hstart: start_thread m cnt tp' m')
        (Hstart': start_thread m cnt tp'' m''),
        tp' = tp'' /\ m' = m''.
    Proof.
      intros.
      inv Hstart; inv Hstart'.
      inv Hperm; inv Hperm0.
      Tactics.pf_cleanup.
      rewrite Hcode in Hcode0.
      inv Hcode0.
      eapply CoreLanguage.initial_core_det in Hinitial; eauto.
      destruct Hinitial; subst.
      now auto.
    Qed.
    

    Lemma sync_step_det:
      forall tp m tid (cnt: containsThread tp tid) tp' m' tp'' m'' ev ev'
        (Hcmpt: mem_compatible tp m)
        (Hstep: @BareMachine.syncStep _ false _ tp m cnt Hcmpt tp' m' ev)
        (Hstep': @BareMachine.syncStep _ false _ tp m cnt Hcmpt tp'' m'' ev'),
        tp' = tp'' /\ m' = m'' /\ ev = ev'.
    Proof.
      intros.
      inv Hstep; inv Hstep';
        repeat match goal with
               | [H: ?Expr = _, H1: ?Expr = _ |- _] =>
                 rewrite H in H1; inv H1
               end;
        now auto.
    Qed.
    
    Lemma suspend_thread_det:
      forall tp m tid (cnt: containsThread tp tid) tp' tp''
        (Hsuspend: suspend_thread m cnt tp')
        (Hsuspend': suspend_thread m cnt tp''),
        tp' = tp''.
    Proof.
      intros.
      inv Hsuspend; inv Hsuspend';
        inv Hperm; inv Hperm0;
          Tactics.pf_cleanup.
      repeat match goal with
             | [H: ?Expr = _, H1: ?Expr = _ |- _] =>
               rewrite H in H1; inv H1
             end;
        reflexivity.
    Qed.

    Lemma step_thread_det:
      forall tp m tid (cnt: containsThread tp tid) tp' m' tp'' m'' ev ev'
        (Hcmpt: mem_compatible tp m)
        (Hstep: threadStep cnt Hcmpt tp' m' ev)
        (Hstep': threadStep cnt Hcmpt tp'' m'' ev'),
        tp' = tp'' /\ m' = m'' /\ ev = ev'.
    Proof.
      intros.
      inv Hstep; inv Hstep'.
      rewrite Hcode in Hcode0; inv Hcode0.
      destruct (CoreLanguage.ev_step_det _ _ _ _ _ _ _ _ Hcorestep Hcorestep0) as [? [? ?]];
        subst.
      now auto.
    Qed.
    
    Lemma resume_thread_det:
      forall tp m tid (cnt: containsThread tp tid) tp' tp''
        (Hresume: resume_thread m cnt tp')
        (Hresume': resume_thread m cnt tp''),
        tp' = tp''.
    Proof.
      intros.
      inv Hresume; inv Hresume';
        inv Hperm; inv Hperm0;
          Tactics.pf_cleanup.
      repeat match goal with
             | [H: ?Expr = _, H1: ?Expr = _ |- _] =>
               rewrite H in H1; inv H1
             end;
        reflexivity.
    Qed.
    
    Lemma bareStep_det:
      forall U tr tp m U' tr' tp' m' U'' tr'' tp'' m''
        (Hstep: MachStep (U, tr, tp) m
                         (U', tr', tp') m')
        (Hstep': MachStep (U, tr, tp) m
                          (U'', tr'', tp'') m''),
        U' = U'' /\ tr' = tr'' /\ tp' = tp'' /\ m' = m''.
    Proof.
      intros.
      inv Hstep; simpl in *; subst;
      inv Hstep'; simpl in *; subst;
      match goal with
      | [H: schedPeek _ = _, H1: schedPeek _ = _ |- _] =>
        rewrite H in H1; inv H1
      end; Tactics.pf_cleanup;
        try (inv Htstep; inv Htstep0;
             Tactics.pf_cleanup;
             congruence);
      try (inv Htstep; inv Hhalted;
           Tactics.pf_cleanup;
           congruence);
      try (now exfalso);
      try (inv Htstep; inv Htstep0;
      Tactics.pf_cleanup;
      rewrite Hcode in Hcode0; inv Hcode0;
      eapply ev_step_ax1 in Hcorestep;
      eapply corestep_not_at_external in Hcorestep;
      inv Hperm;
      congruence);
      try (exfalso;
      inv Hhalted;
      inv Htstep;
      Tactics.pf_cleanup;
      rewrite Hcode in Hcode0; inv Hcode0;
      solve [eapply ev_step_ax1 in Hcorestep;
             eapply corestep_not_halted in Hcorestep;
             now eauto |
             destruct (CoreLanguage.at_external_halted_excl c0 m') as [Hcontra | Hcontra]
               in Hat_external;
             [congruence | eapply Hcontra; eauto]]).
      destruct (start_thread_det Htstep Htstep0); subst;
        now auto.
      destruct (resume_thread_det Htstep Htstep0); subst;
        now auto.
      destruct (step_thread_det Htstep Htstep0) as [? [? ?]]; subst;
        now auto.
      destruct (suspend_thread_det Htstep Htstep0); subst;
        now auto.      
      destruct (sync_step_det Htstep Htstep0) as [? [? ?]]; subst;
        now auto.
      now auto.      
    Qed.


    Lemma bare_execution_det:
      forall st m st' m' st'' m''
        (Hstep: fine_execution st m st' m')
        (Hstep': fine_execution st m st'' m''),
        st' = st'' /\ m' = m''.
    Proof.
      intros st.
      destruct st as [[U tr] tp].
      generalize dependent tr.
      generalize dependent tp.
      induction U; intros.
      - inv Hstep; inv Hstep'.
        now  auto.
      - inv Hstep;
        [simpl in H;
         now exfalso|].
        inv Hstep';
          [simpl in H;
           now exfalso|].
        destruct (bareStep_det H6 H8) as [? [? [? ?]]];
          subst.
        apply app_inv_head in H0; subst.
        now eauto.
    Qed.

    End SCExecutions.
    
End Executions.
