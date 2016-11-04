
(** * Definitions and properties of machine executions *)
Require Import compcert.lib.Axioms.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Memory.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import concurrency.semantics.
Require Import concurrency.dry_context.
Require Import concurrency.dry_machine_lemmas.
Require Import Coqlib.
Require Import msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module Executions (SEM: Semantics) (SemAxioms: SemanticsAxioms SEM)
       (Machines: MachinesSig with Module SEM := SEM)
       (AsmContext: AsmContext SEM Machines).
  Module StepLemmas := StepLemmas SEM Machines.
  Module StepType := StepType SEM SemAxioms Machines AsmContext.
  Import Machines DryMachine StepLemmas StepType ThreadPool AsmContext.
  Import event_semantics.
  Import Events.

  (** Reflexive-transitive closure of FineConc's step relation*)
  Inductive multi_fstep :
    FineConc.MachState -> mem -> FineConc.MachState -> mem -> Prop :=
  | fine_refl : forall ms (m : mem),
      multi_fstep ms m ms m
  | fine_trans : forall i U U'
                        (tp tp' tp'': FineConc.machine_state)
                        (tr tr' tr'': FineConc.event_trace)
                        (m m' m'' : mem),
      FineConc.MachStep the_ge (i :: U, tr, tp) m (U, tr ++ tr', tp') m' ->
      multi_fstep (U, tr ++ tr', tp') m' (U', tr ++ tr' ++ tr'', tp'') m'' ->
      multi_fstep (i :: U,tr,tp) m (U',tr ++ tr' ++ tr'',tp'') m''.

  (** Complete executions (until the schedule is empty) of the FineConc machine*)
  Inductive fine_execution :
    FineConc.MachState -> mem -> FineConc.MachState -> mem -> Prop :=
  | fine_completed : forall ms (m : mem),
      FineConc.halted ms ->
      fine_execution ms m ms m
  | fine_exec : forall i U U'
                        (tp tp' tp'': FineConc.machine_state)
                        (tr tr' tr'': FineConc.event_trace)
                        (m m' m'' : mem),
      FineConc.MachStep the_ge (i :: U, tr, tp) m (U, tr ++ tr', tp') m' ->
      fine_execution (U, tr ++ tr', tp') m' (U', tr ++ tr' ++ tr'', tp'') m'' ->
      fine_execution (i :: U,tr,tp) m (U',tr ++ tr' ++ tr'',tp'') m''.
  
  (** Complete executions of the SC machine *)
  Inductive sc_execution :
    SC.MachState -> mem -> SC.MachState -> mem -> Prop :=
  | sc_completed : forall ms (m : mem),
      SC.halted ms ->
      sc_execution ms m ms m
  | sc_exec : forall i U U'
                      (tp tp' tp'': SC.machine_state)
                      (tr tr' tr'': SC.event_trace)
                      (m m' m'' : mem),
      SC.MachStep the_ge (i :: U, tr, tp) m (U, tr', tp') m' ->
      sc_execution (U, tr', tp') m' (U', tr'', tp'') m'' ->
      sc_execution (i :: U,tr,tp) m (U',tr'',tp'') m''.


  (*TODO: move to threads_lemmas*)
  Lemma app_eq_nil:
    forall {A:Type} (xs ys : list A),
      xs = xs ++ ys ->
      ys = nil.
  Proof.
    intros.
    erewrite <- app_nil_r in H at 1.
    apply app_inv_head in H; auto.
  Qed.

  (** ** Properties of executions and steps *)
  
  (** A property of steps is that any sequence of events added by
    one external step is a singleton *)
  Lemma fstep_ext_trace:
    forall (a : tid) U
      (i : nat) (tr tr' : SC.event_trace) (tp tp' : thread_pool) 
      (m m' : mem) (ev : machine_event),
      is_external ev ->
      nth_error tr' i = Some ev ->
      FineConc.MachStep the_ge ((a :: U)%SEQ, tr, tp) m 
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

  Lemma fstep_event_sched:
    forall U tr tp m U' ev tr_pre tr_post tp' m'
      (Hstep: FineConc.MachStep the_ge (U, tr, tp) m
                                (U', tr ++ tr_pre ++ [:: ev] ++ tr_post, tp') m'),
      U = (thread_id ev) :: U'.
  Proof.
    intros.
    inv Hstep; simpl in *;
    try (apply app_eq_nil in H4; exfalso;
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

  Lemma fstep_ev_contains:
    forall U tr tp m U' ev tr_pre tr_post tp' m'
      (Hstep: FineConc.MachStep the_ge (U, tr, tp) m
                                (U', tr ++ tr_pre ++ [:: ev] ++ tr_post, tp') m'),
      containsThread tp (thread_id ev) /\ containsThread tp' (thread_id ev).
  Proof.
    intros.
    pose proof (fstep_event_sched _ _ _ Hstep) as Heq.
    inv Hstep; simpl in *;
      try (apply app_eq_nil in H4; exfalso;
           eapply app_cons_not_nil; by eauto);
      try subst.
    inv HschedN.
    inv Htstep;
      split; eauto.
    inv HschedN.
    inv Htstep; split; eauto.
    apply cntAdd.
    apply cntUpdate.
    assumption.
  Qed.

  Lemma fstep_event_tid:
    forall U tr tp m U' tr' tp' m'
      (Hstep: FineConc.MachStep the_ge (U, tr, tp) m
                                (U', tr ++ tr', tp') m'),
    forall ev ev', List.In ev tr' ->
              List.In ev' tr' ->
              thread_id ev = thread_id ev'.
  Proof.
    intros.
    inv Hstep; simpl in *;
      try (apply app_eq_nil in H6; subst);
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

  Lemma multi_fstep_mem_compatible :
    forall U tr tp m U' tr' tp' m'
      (Hexec: multi_fstep (U, tr, tp) m (U', tr', tp') m'),
      mem_compatible tp m \/ tp = tp' /\ m = m' /\ U = U' /\ tr = tr'.
  Proof.
    intros.
    inversion Hexec; subst.
    right; auto.
    eapply fstep_mem_compatible in H7.
    left; auto.
  Qed.

  Lemma multi_fstep_invariant :
    forall U tr tp m U' tr' tp' m'
      (Hexec: multi_fstep (U, tr, tp) m (U', tr', tp') m'),
      invariant tp \/ tp = tp' /\ m = m' /\ U = U' /\ tr = tr'.
  Proof.
    intros.
    inversion Hexec; subst.
    right; auto.
    eapply fstep_invariant in H7.
    left; auto.
  Qed.

  Lemma multi_fstep_containsThread :
    forall U tp tr m U' tp' tr' m' i
      (Hexec: multi_fstep (U, tr, tp) m (U', tr', tp') m'),
      containsThread tp i -> containsThread tp' i.
  Proof.
    intros U.
    induction U. intros.
    inversion Hexec; subst; simpl in *; auto; try discriminate.
    intros.
    inversion Hexec; subst; eauto.
    eapply fstep_containsThread with (j := i) in H9;
      now eauto.
  Qed.


  Lemma multi_fstep_valid_block:
    forall U tr tp m U' tr' tp' m' b
      (Hexec: multi_fstep (U, tr, tp) m (U', tr', tp') m')
      (Hvalid: Mem.valid_block m b),
      Mem.valid_block m' b.
  Proof.
    intros.
    induction Hexec.
    assumption.
    eapply IHHexec.
    eapply fstep_valid_block; eauto.
  Qed.
  
  Lemma fstep_trace_monotone:
    forall U tp m tr U' tp' m' tr'
      (Hstep: FineConc.MachStep the_ge (U, tr, tp) m
                                (U', tr', tp') m'),
    exists tr'',
      tr' = tr ++ tr''.
  Proof.
    intros.
    inv Hstep; simpl in *; subst;
      try (exists [::]; rewrite app_nil_r; reflexivity);
      eexists; reflexivity.
  Qed.

  Lemma multi_fstep_trace_monotone:
    forall U tr tp m U' tr' tp' m'
      (Hexec: multi_fstep (U, tr, tp) m (U', tr', tp') m'),
    exists tr'',
      tr' = tr ++ tr''.
  Proof.
    induction U; intros.
    - inv Hexec. exists [::]. rewrite app_nil_r. reflexivity.
    - inv Hexec. exists [::]. rewrite app_nil_r. reflexivity.
      eapply fstep_trace_monotone in H8.
      destruct H8 as [tr''0 H8].
      apply app_inv_head in H8; subst.
      eapply IHU in H9.
      now eauto.
  Qed.
  
  (** Decomposing steps based on an external event*)
  Lemma multi_fstep_inv_ext:
    forall U U' i tr tr' tp m tp' m' ev
      (Hext: is_external ev)
      (Hi: nth_error tr' i = Some ev)
      (Hexec: multi_fstep (U, tr, tp) m (U', tr ++ tr', tp') m'),
    exists U'' U''' tp'' m'' tr'' tp''' m''',
      multi_fstep (U, tr, tp) m (U'', tr ++ tr'', tp'') m'' /\
      FineConc.MachStep the_ge (U'', tr ++ tr'', tp'') m''
                        (U''', tr ++ tr'' ++ [:: ev], tp''') m''' /\
      multi_fstep (U''', tr ++ tr'' ++ [:: ev], tp''') m'''
                     (U', tr ++ tr', tp') m' /\
      length tr'' = i.
  Proof.
    intros U.
    induction U; intros.
    - inversion Hexec. simpl in *.
      apply app_eq_nil in H3. subst.
      destruct i; simpl in Hi; discriminate.
    - inversion Hexec.
      + rewrite <- app_nil_r in H3 at 1.
        apply app_inv_head in H3; subst.
        rewrite nth_error_nil in Hi. discriminate.
      + subst.
        apply app_inv_head in H6. subst.
        (* need a case analysis on whether it belongs on the first list or not*)
        destruct (i < length tr'0) eqn:Hlt.
        * erewrite nth_error_app1 in Hi by ssromega.
          exists (a :: U), U, tp, m, [::], tp'0, m'0.
          assert (tr'0 = [:: ev]) by (eapply fstep_ext_trace; eauto).
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
  Lemma multi_fstep_inv:
    forall U U' i tr tr' tp m tp' m' ev
      (Hi: nth_error tr' i = Some ev)
      (Hexec: multi_fstep (U, tr, tp) m (U', tr ++ tr', tp') m'),
    exists U'' U''' tp'' m'' tr'' pre_ev post_ev  tp''' m''',
      multi_fstep (U, tr, tp) m (U'', tr ++ tr'', tp'') m'' /\
      FineConc.MachStep the_ge (U'', tr ++ tr'', tp'') m''
                        (U''', tr ++ tr'' ++ pre_ev ++ [:: ev] ++ post_ev, tp''') m''' /\
      multi_fstep (U''', tr ++ tr'' ++ pre_ev ++ [:: ev] ++ post_ev , tp''') m'''
                     (U', tr ++ tr', tp') m' /\
      length (tr'' ++ pre_ev) = i.
  Proof.
    intros U.
    induction U; intros.
    - inversion Hexec. simpl in *.
      apply app_eq_nil in H3. subst.
      destruct i; simpl in Hi; discriminate.
    - inversion Hexec.
      + rewrite <- app_nil_r in H3 at 1.
        apply app_inv_head in H3; subst.
        rewrite nth_error_nil in Hi. discriminate.
      + subst.
        apply app_inv_head in H6. subst.
        (* need a case analysis on whether it belongs on the first list or not*)
        destruct (i < length tr'0) eqn:Hlt.
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

  Lemma fstep_sched_inv:
    forall i U tp m tr U' tp' m' tr'
      (Hstep: FineConc.MachStep the_ge (i :: U, tr, tp) m
                                (U', tr', tp') m'),
      U' = U.
  Proof.
    intros.
    inversion Hstep; subst; auto.
  Qed.

  Lemma multi_fstep_snoc:
    forall U U' U'' tr tr' tr'' tp m tp' m' tp'' m''
      (Hexec: multi_fstep (U, tr, tp) m (U', tr ++ tr', tp') m')
      (Hstep: FineConc.MachStep the_ge (U', tr ++ tr', tp') m' (U'', tr ++ tr' ++ tr'', tp'') m''),
      multi_fstep (U, tr, tp) m (U'', tr ++ tr' ++ tr'', tp'') m''.
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
          by (erewrite fstep_sched_inv by eauto; reflexivity); subst.
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
  Lemma fstep_trace_irr:
    forall U i tp m tp' m' tr tr'
      (Hstep: FineConc.MachStep the_ge (i :: U, tr, tp) m (U, tr', tp') m'),
    forall tr'', exists ev,
        FineConc.MachStep the_ge (i :: U, tr'', tp) m (U, tr'' ++ ev, tp') m'.
  Proof.
    intros.
    inversion Hstep; subst; simpl in *; subst; inv HschedN; pf_cleanup.
    - exists [::]; erewrite cats0; econstructor; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 2; simpl; eauto.
    - exists (map [eta Events.internal tid] ev); econstructor 3; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 4; simpl; eauto.
    - exists [:: Events.external tid ev]; econstructor 5; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 6; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 7; simpl; eauto.
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
  
  Lemma multi_fstep_deadLocation:
    forall U U' tr tp m tr' tp' m' b ofs
      (Hdead: deadLocation tp m b ofs)
      (Hexec: multi_fstep (U, tr, tp) m (U',tr ++ tr', tp') m'),
      deadLocation tp' m' b ofs.
  Proof.
  Admitted.
  
End Executions.