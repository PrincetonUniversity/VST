(** * Lemmas about the Hybrid Machine steps*)
Require Import compcert.lib.Axioms.

Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.common.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat seq ssrfun eqtype fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.dry_context.
Require Import VST.concurrency.common.semantics. 
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.tactics.
Import threadPool.

Require Import Coq.Logic.FunctionalExtensionality.

Global Notation "a # b" := (Maps.PMap.get b a) (at level 1).

(** This file holds various results about the dry machine*)
(* Find other lemmas in dry_machine_lemmas.v          *)

(** These lemmas require the machines. But the machines are
parameterized by the semantics so they can be used by either
high-level or low-level languages*)
Module StepLemmas.
  Import HybridMachine ThreadPool.
  Import DryHybridMachine HybridMachineSig.

  Section StepLemmas.
    Context {asmSem : Semantics}
            {Sch: Scheduler}
            {DilMem: DiluteMem}.

    Existing Instance OrdinalPool.OrdinalThreadPool.
    Existing Instance DryHybridMachine.dryResources.

    Existing Instance DryHybridMachine.DryHybridMachineSig.
    
  (** [mem_compatible] is preserved by [updThreadC] *)
  Lemma updThreadC_compatible:
    forall (tp : t) m i c
      (ctn : containsThread tp i)
      (Hcomp: mem_compatible tp m),
      mem_compatible (updThreadC ctn c) m.
  Proof.
    intros.
    constructor.
    intros j cntj'.
    assert (cntj: containsThread tp j)
      by (eapply cntUpdateC'; eauto).
    specialize ((compat_th _ _ Hcomp) cntj).
    erewrite @gThreadCR with (cntj := cntj);
      by auto.
    intros.
    erewrite gsoThreadCLPool in H.
    destruct Hcomp;
      by eauto.
    intros.
    erewrite gsoThreadCLPool in H;
      eapply (lockRes_blocks _ _ Hcomp);
      by eauto.
  Qed.

  (** ***Lemmas about suspend steps*)

  (** [suspend_thread] is deterministic*)
  Lemma suspend_step_det:
    forall m tp tp' tp'' i (cnt: containsThread tp i)
      (Hstep: suspend_thread m cnt tp')
      (Hstep': suspend_thread m cnt tp''),
      tp' = tp''.
  Proof.
    intros.
    inversion Hstep; inversion Hstep'; subst.
    Tactics.pf_cleanup. rewrite Hcode in Hcode0.
    inversion Hcode0; by subst.
  Qed.

  (** [suspend_thread] does not change the number of threads*)
  Lemma suspend_containsThread:
    forall m tp tp' i j (cnti: containsThread tp i)
      (Hsuspend: suspend_thread m cnti tp'),
      containsThread tp j <-> containsThread tp' j.
  Proof.
    intros; inversion Hsuspend; subst.
    split;
      [eapply cntUpdateC | eapply cntUpdateC'].
  Qed.

  (** [mem_compatible] is preserved by [suspend_thread]*)
  Corollary suspend_compatible:
    forall tp tp' m i (cnt: containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (Hsuspend: suspend_thread m cnt tp'),
      mem_compatible tp' m.
  Proof.
    intros. inversion Hsuspend; subst.
      by eapply updThreadC_compatible.
  Qed.

  Lemma gsoThreadC_blocked:
    forall (tp : t) i j (cntj : containsThread tp j)
      c (Hneq: i <> j) (cnti : containsThread tp i)
      (cntj' : containsThread (updThreadC cnti (Kblocked c)) j),
      getThreadC cntj = getThreadC cntj'.
  Proof.
    intros; erewrite gsoThreadCC; eauto.
  Qed.

  Corollary gsoThreadC_suspend:
    forall m tp tp' i j (cnt: containsThread tp i) (cntj: containsThread tp j)
      (cntj': containsThread tp' j) (Hneq: i <> j)
      (Hsuspend: suspend_thread m cnt tp'),
      getThreadC cntj = getThreadC cntj'.
  Proof.
    intros; inversion Hsuspend; subst;
      by apply gsoThreadC_blocked.
  Qed.
  
  Lemma gsoThreadR_suspend:
    forall m tp tp' i j (cnt: containsThread tp i) (cntj: containsThread tp j)
      (cntj': containsThread tp' j)
      (Hsuspend: suspend_thread m cnt tp'),
      getThreadR cntj = getThreadR cntj'.
  Proof.
    intros. inversion Hsuspend. subst.
      by erewrite @gThreadCR with (cntj := cntj).
  Qed.

  (** [invariant] is preserved by [suspend_thread]*)
  Lemma suspend_invariant:
    forall m tp tp' i
      (pff: containsThread tp i)
      (Hinv: invariant tp)
      (Hsuspend: suspend_thread m pff tp'),
      invariant tp'.
  Proof.
    intros.
    inversion Hsuspend; subst.
      by apply ThreadPoolWF.updThreadC_invariant.
  Qed.

  (** [lockRes] is not changed by [suspend_thread]*)
  Lemma suspend_lockRes:
    forall m tp tp' i
      (pff: containsThread tp i)
      (Hsuspend: suspend_thread m pff tp'),
      lockRes tp = lockRes tp'.
  Proof.
    intros.
    inversion Hsuspend; subst.
    extensionality addr.
      by erewrite gsoThreadCLPool.
  Qed.

  Lemma suspend_lockPool :
    forall m (tp tp' : t) i (pfc : containsThread tp i)
      (Hsuspend: suspend_thread m pfc tp') addr,
      lockRes tp addr = lockRes tp' addr.
  Proof.
    intros. inversion Hsuspend; subst.
      by erewrite gsoThreadCLPool.
  Qed.

  (** [mem_compatible] is preserved by [setMaxPerm] *)
  Lemma mem_compatible_setMaxPerm :
    forall tp m
      (Hcomp: mem_compatible tp m),
      mem_compatible tp (setMaxPerm m).
  Proof.
    intros tp m Hcomp.
    constructor;
      [intros i cnti; split; intros b ofs | intros l pmap Hres; split; intros b ofs |
       intros l rmap Hres];
      try (rewrite getMaxPerm_correct;
      destruct (valid_block_dec m b) as [Hvalid | Hinvalid];
      try (
          erewrite setMaxPerm_MaxV by assumption; simpl;
          match goal with
          | [ |- match ?Expr with _ => _ end] =>
            destruct Expr
          end; constructor);
      try (
          erewrite setMaxPerm_MaxI by assumption;
          apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid;
          destruct Hcomp as [Hcompat_thr Hcompat_lp]);
      try (destruct (Hcompat_thr _ cnti) as [Hcompat_thr1 Hcompat_thr2]);
      try (destruct (Hcompat_lp _ _ Hres) as [Hcompat_lp1 Hcompat_lp2]);
      repeat match goal with
             | [H: permMapLt _ _ |- _] =>
               specialize (H b ofs)
             | [H: context[(getMaxPerm _) !! _ _] |- _] =>
               rewrite getMaxPerm_correct in H
             end;
      unfold permission_at in *;
    repeat match goal with
           | [H: Mem.perm_order'' ?Expr _, H2: ?Expr = _ |- _] =>
             rewrite H2 in H
           end; simpl in *;
      by auto).
    eapply (lockRes_blocks _ _ Hcomp); eauto.
  Qed.

  (** Any state that steps, requires its threadpool and memory to be
  [mem_compatible]*)
  Lemma step_mem_compatible:
    forall U tr tp m U' tr' tp' m'
      (Hstep: MachStep (U, tr, tp) m (U', tr', tp') m'),
      mem_compatible tp m.
  Proof.
    intros.
    inversion Hstep; simpl in *; subst;
      try (now eauto);
      try (inversion Htstep; now eauto).
  Qed.

  (** Any state that steps satisfies the [invariant] *)
  Lemma step_invariant:
    forall U tr tp m U' tr' tp' m'
      (Hstep: MachStep (U, tr, tp) m (U', tr', tp') m'),
      invariant tp.
  Proof.
    intros.
    inversion Hstep; simpl in *; subst;
      try (inversion Htstep; eauto).
    now eauto.
  Qed.

  Lemma step_containsThread :
    forall tp tp' m m' i j U tr tr'
      (cntj: containsThread tp j)
      (Hstep: MachStep (i :: U, tr, tp) m (U, tr', tp') m'),
      containsThread tp' j.
  Proof.
    intros.
    inversion Hstep; subst; try inversion Htstep;
      simpl in *; try inversion HschedN;
        subst; auto;
          repeat match goal with
                 | [ |- containsThread (updThreadC _ _) _] =>
                   apply cntUpdateC; auto
                 | [ |- containsThread (updThread _ _ _) _] =>
                   apply cntUpdate; auto
                 | [ |- containsThread (updThreadR _ _) _] =>
                   apply cntUpdateR; auto
                                       (*NOTE: automation broke here*)
                 (* | [ |- OrdinalPool.containsThread _ _ (OrdinalPool.addThread _ _ _ _) _] => *)
                 (*   eapply OrdinalPool.cntAdd; auto *)
                 end.
    eapply OrdinalPool.cntAdd; eauto.
  Qed.

  Lemma gsoThreadR_step:
    forall tp tp' m m' i j U tr tr'
      (Hneq: i <> j)
      (pfj: containsThread tp j)
      (pfj': containsThread tp' j)
      (Hstep: MachStep (i :: U,tr, tp) m (U,tr', tp') m'),
      getThreadR pfj = getThreadR pfj'.
  Proof.
    intros.    
    inversion Hstep; simpl in *; subst;
      try (inversion Htstep); subst; inversion HschedN; subst; Tactics.pf_cleanup;
        try (by rewrite <- OrdinalPool.gThreadCR with (cntj' := pfj'));
        try (rewrite OrdinalPool.gLockSetRes);
        try (rewrite @OrdinalPool.gsoThreadRes); eauto.
    rewrite OrdinalPool.gsoAddRes OrdinalPool.gsoThreadRes; now auto.
    rewrite OrdinalPool.gRemLockSetRes OrdinalPool.gsoThreadRes; now auto.
  Qed.

  Lemma permission_at_step:
    forall tp tp' m m' i j U tr tr'
      (Hneq: i <> j)
      (pfj: containsThread tp j)
      (pfj': containsThread tp' j)
      (Hcomp: mem_compatible tp m)
      (Hcomp': mem_compatible tp' m')
      (Hstep: MachStep (i :: U, tr, tp) m (U,tr',tp') m') b ofs,
      permission_at (restrPermMap ((compat_th _ _ Hcomp) pfj).1) b ofs Cur =
      permission_at (restrPermMap ((compat_th _ _ Hcomp') pfj').1) b ofs Cur.
  Proof.
    intros.
    do 2 rewrite restrPermMap_Cur;
      erewrite gsoThreadR_step;
        by eauto.
  Qed.

  Lemma safeC_invariant:
    forall tpc trc mc n
      (Hn: n > 0)
      (Hsafe: forall U,
          HybridCoarseMachine.csafe (U,trc,tpc) mc n),
      invariant tpc.
  Proof.
    intros.
    specialize (Hsafe [:: 1]).
    simpl in Hsafe.
    inversion Hsafe; subst; try (by exfalso);
      inversion Hstep; try inversion Htstep; auto;
        try (inversion Hhalted; simpl in *; subst; auto);
        simpl in *; subst; auto.
  Qed.

  Lemma safeC_compatible:
    forall tpc trc mc n
      (Hn: n > 0)
      (Hsafe: forall U,
          HybridCoarseMachine.csafe (U,trc,tpc) mc n),
      mem_compatible tpc mc.
  Proof.
    intros.
    specialize (Hsafe [:: 0]).
    simpl in Hsafe.
    destruct Hsafe as [|Hhalted | |];
      [by exfalso |simpl in Hhalted;
                     by exfalso | |];
      inversion Hstep; try inversion Htstep; auto;
        simpl in *; subst; auto; try discriminate.
  Qed.
  Opaque containsThread.

  Lemma step_schedule:
    forall tpc tpc' mc mc' i U1 U2 U1' tr tr'
      (Hstep: MachStep (i :: U1, tr, tpc) mc (U2, tr ++ tr', tpc') mc'),
      exists U2',
      MachStep (i :: U1', tr, tpc) mc (U2', tr ++ tr', tpc') mc'.
  Proof.
    intros.
    inversion Hstep; subst; simpl in *;
    repeat match goal with
          | [H: ?X :: ?U = ?U |- _] =>
            exfalso; eapply list_cons_irrefl; eauto
          | [H: Some ?X = Some ?Y |- _] =>
            inversion H; subst; clear H
          | [H: ?X = cat ?X ?Y |- _] =>
            erewrite List.app_nil_end with (l := X) in H at 1;
              apply List.app_inv_head in H; subst;
                rewrite cats0
        end.

    eexists; econstructor 1; simpl; eauto.
    eexists; econstructor 2; simpl; eauto.
    eexists; econstructor 3; simpl; eauto.
    exists U1'; econstructor 4; simpl; eauto.
    exists U1'; econstructor 5; simpl; eauto.
    exists U1'; econstructor 6; simpl; eauto.
  Qed.

  End StepLemmas.
  End StepLemmas.

(** ** Definition of internal steps *)
  Module InternalSteps.

    Import StepLemmas ThreadPool.
    Import CoreLanguage HybridMachine.DryHybridMachine HybridMachineSig.

    Section InternalSteps.

      Context {Sem : Semantics}
              {SemAx : SemAxioms}
              {SemD : SemDet}.

      Notation schedule := (seq nat).

      Existing Instance OrdinalPool.OrdinalThreadPool.
      Existing Instance dryResources.
      Existing Instance DryHybridMachineSig.

      
      (** Internal steps are just thread coresteps or resume steps or start steps,
          they mimic fine-grained internal steps *)
      Definition internal_step {tid} {tp} m (cnt: containsThread tp tid)
                 (Hcomp: mem_compatible tp m) tp' m' :=
      (exists ev, threadStep cnt Hcomp tp' m' ev) \/
      (resume_thread m cnt tp' /\ m = m') \/
      (start_thread m cnt tp' m').

    (* For now we don't emit events from internal_execution*)
    (*NOTE: we will probably never need to do so*)
    Inductive internal_execution : schedule -> t -> mem ->
                                   t -> mem -> Prop :=
    | refl_exec : forall tp m,
        internal_execution [::] tp m tp m
    | step_trans : forall tid U U' tp m tp' m' tp'' m''
                     (cnt: containsThread tp tid)
                     (HschedN: schedPeek U = Some tid)
                     (HschedS: schedSkip U = U')
                     (Hcomp: mem_compatible tp m)
                     (Hstep: internal_step cnt Hcomp tp' m')
                     (Htrans: internal_execution U' tp' m' tp'' m''),
        internal_execution U tp m tp'' m''.

    (** ** Lemmas about internal steps and internal executions *)

    (** Reverse composition of [internal_execution] and [internal_step]*)
    Lemma internal_execution_trans :
      forall i U tp tp' tp'' m m' m'' (pf': containsThread tp' i)
        (Hcomp: mem_compatible tp' m')
        (Hstep: internal_step pf' Hcomp tp'' m'')
        (Hexec: internal_execution U tp m tp' m'),
        internal_execution (U ++ (i :: nil))%list tp m tp'' m''.
    Proof.
      intros i U. induction U; intros.
      simpl in *.
      inversion Hexec; subst.
      econstructor; simpl; eauto. constructor.
      simpl in HschedN. discriminate.
      inversion Hexec. subst. simpl in *.
      econstructor; simpl; eauto.
    Qed.

    (** [internal_step] is deterministic *)
    Lemma internal_step_det :
      forall tp tp' tp'' m m' m'' i
             (Hcnt: containsThread tp i)
             (Hcomp: mem_compatible tp m)
             (Hstep: internal_step Hcnt Hcomp tp' m')
             (Hstep': internal_step Hcnt Hcomp tp'' m''),
        tp' = tp'' /\ m' = m''.
    Proof.
      intros.
      destruct Hstep as [[? Htstep] | [[Htstep ?] | Htstep]],
                        Hstep' as [[? Htstep'] | [[Htstep' ?] | Htstep']]; subst;
        inversion Htstep; inversion Htstep'; subst; Tactics.pf_cleanup;
          try (rewrite Hcode in Hcode0; inversion Hcode0; subst).
      - apply event_semantics.ev_step_ax1 in Hcorestep0;
          apply event_semantics.ev_step_ax1 in Hcorestep.
        assert (Heq: c' = c'0 /\ m' = m'')
          by (eapply corestep_det; eauto).
        now solve [destruct Heq; subst; auto].
      - inversion Hperm; inversion Hperm0; subst.
        rewrite Hafter_external in Hafter_external0;
          now inversion Hafter_external0.
      - inversion Hperm; inversion Hperm0; subst.
        pose proof (initial_core_det _ _ _ _ _ _ _ _ Hinitial Hinitial0) as [? ?];
          subst.
        split;
          now auto.
    Qed.

    Ltac exec_induction base_case :=
      intros;
      match goal with
      | [xs : list _, i : nat, Hexec: internal_execution _ ?Tp ?M _ _ |- _] =>
        generalize dependent Tp; generalize dependent M;
        induction xs as [| x xs' IHxs]; intros;
        [ match goal with
          | [Hexec: internal_execution _ _ _ _ _ |- _] =>
            try (inversion Hexec; subst;
                   by Tactics.pf_cleanup)
          end
        | match goal with
          | [Hexec: internal_execution _ _ _ _ _ |- _] =>
            simpl in Hexec;
              destruct (x == i) eqn:Heq;
              move/eqP:Heq=>Heq;
              try eauto;
              subst;
              try (inversion Hexec as [|? ? ? ? ? ? ? ? ? ?
                                          HschedN HschedS Hcomp ? Htrans]; subst;
                   simpl in Htrans;
                   simpl in HschedN; inversion HschedN; subst;
                   Tactics.pf_cleanup;
                   specialize (IHxs _ _  Htrans);
                   rewrite <- IHxs;
                   erewrite base_case; eauto)
          end
        ]
      end.

    (** [containsThread] is preserved by [internal_step]*)
    Lemma containsThread_internal_step :
      forall tp m tp' m' tid0 tid
        (Hcnt0: containsThread tp tid0)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step Hcnt0 Hcomp tp' m')
        (Hcnt: containsThread tp tid),
        containsThread tp' tid.
    Proof.
      intros.
      inversion Hstep. destruct H.
      inversion H; subst.
      eapply CoreLanguageDry.corestep_containsThread; by eauto.
      destruct H as [[Htstep _] | Htstep];
        inversion Htstep; subst;
        [by eapply cntUpdateC | by eapply cntUpdate].
    Qed.

    (** [containsThread] is preserved by [internal_execution]*)
    Lemma containsThread_internal_execution :
      forall U tp m tp' m' i
        (Hexec: internal_execution U tp m tp' m'),
        containsThread tp i -> containsThread tp' i.
    Proof.
      intros U. induction U. intros.
      inversion Hexec; subst; simpl in *; auto; try discriminate.
      intros.
      inversion Hexec as [|tid0 U0 U0' ? ? tp0' m0' ? ?];
        subst. eapply containsThread_internal_step in Hstep; eauto.
    Qed.

    (** The other direction: if a thread is in the threadpool after an
    [internal_step] then it must have been there before the step *)
    Lemma containsThread_internal_step' :
      forall tp m tp' m' i j
        (Hcnt0: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step Hcnt0 Hcomp tp' m')
        (Hcnt: containsThread tp' i),
        containsThread tp i.
    Proof.
      intros. inversion Hstep as [[? Htstep] | [[Htstep _] | Htstep]];
        inversion Htstep; subst;
        [eapply CoreLanguageDry.corestep_containsThread'; eauto
        |  by eapply cntUpdateC'; eauto
        |  by eapply cntUpdate'; eauto].
    Qed.

    Lemma containsThread_internal_execution' :
      forall U tp m tp' m' i
        (Hexec: internal_execution U tp m tp' m')
        (Hcnt: containsThread tp' i),
        containsThread tp i.
    Proof.
      intros U. induction U. intros.
      inversion Hexec; subst; simpl in *; auto; try discriminate.
      intros.
      inversion Hexec as [|tid0 U0 U0' ? ? tp0' m0' ? ?];
        subst. eapply containsThread_internal_step' in Hstep; eauto.
    Qed.

    (** [mem_compatible] is preserved by [dry_step]*)
    Lemma dry_step_compatible :
      forall (tp tp' : t) m m' (i : nat) ev (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hdry: dry_step pf Hcompatible tp' m' ev),
        mem_compatible tp' m'.
    Proof.
      intros.
      inversion Hdry; subst; eapply CoreLanguageDry.corestep_compatible; eauto.
    Qed.

    (** [mem_compatible] is preserved by [resume_thread]*)
    Corollary resume_compatible :
      forall (tp tp' : t) m (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hresume: resume_thread m pf tp'),
        mem_compatible tp' m.
    Proof.
      intros.
      inversion Hresume; subst;
      eapply updThreadC_compatible;
        by eauto.
    Qed.

    (** [mem_compatible] is preserved by [start_thread]*)
    Corollary start_compatible :
      forall (tp tp' : t) m m' (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hstart: start_thread m pf tp' m'),
        mem_compatible tp' m'.
    Proof.
      intros.
      inversion Hstart; subst.
      simpl (add_block).
      unfold HybridMachine.DryHybridMachine.add_block.
      inversion Hperm; subst.
      eapply CoreLanguageDry.initial_core_compatible;
        now eauto.
    Qed.

    (** [mem_compatible] is preserved by [internal_step]*)
    Corollary internal_step_compatible :
      forall (tp tp' : t) m m' (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hstep: internal_step pf Hcompatible tp' m'),
        mem_compatible tp' m'.
    Proof.
      intros.
      destruct Hstep as [[? Hdry] | [[Hresume ?] | Hstart]];
        subst;
        [eapply dry_step_compatible
        | eapply resume_compatible
        | eapply start_compatible];
          by eauto.
    Qed.

    (** [invariant] is preserved by [internal_step]*)
    Lemma internal_step_invariant:
      forall (tp tp' : t) m m' (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hstep: internal_step pf Hcompatible tp' m'),
        invariant tp'.
    Proof.
      intros.
      destruct Hstep as [[? Hdry] | Hsr].
      - inversion Hdry as [tp'0 c m1 m1' c']. subst m' tp'0 tp' ev.
        apply event_semantics.ev_step_ax1 in Hcorestep.
        eapply CoreLanguageDry.corestep_invariant; eauto.
      - destruct Hsr as [H1 | H1].
        + destruct H1 as [H2 ?];  subst.
          inversion H2; subst.        
            by apply ThreadPoolWF.updThreadC_invariant.
        + inversion H1; subst.
          inversion Hperm; subst.
          simpl (add_block).
          unfold HybridMachine.DryHybridMachine.add_block.
          eapply CoreLanguageDry.initial_core_invariant;
            now eauto.
    Qed.

    Lemma internal_execution_compatible :
      forall (tp tp' : t) m m' xs
        (Hcompatible: mem_compatible tp m)
        (Hstep: internal_execution xs tp m tp' m'),
        mem_compatible tp' m'.
    Proof.
      intros. induction Hstep. auto. subst.
      eapply IHHstep; eauto.
      eapply internal_step_compatible; eauto.
    Qed.

    Lemma internal_execution_invariant :
      forall (tp tp' : t) m m' xs
        (Hcompatible: mem_compatible tp m)
        (Hinv: invariant tp)
        (Hstep: internal_execution xs tp m tp' m'),
        invariant tp'.
    Proof.
      intros. induction Hstep. auto. subst.
      eapply IHHstep; eauto.
      eapply internal_step_compatible; eauto.
      eapply internal_step_invariant; eauto.
    Qed.

    Lemma gsoThreadC_step:
      forall tp tp' m m' i j (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step pfi Hcomp tp' m')
        (Hneq: i <> j),
        getThreadC pfj = getThreadC pfj'.
    Proof.
      intros. destruct Hstep as [[? Hstep] | [[Hstep Heq] | Hstep]];
        inversion Hstep; subst;
        [erewrite <- gsoThreadCode with (cntj' := pfj')
          by eauto
        |
        erewrite gsoThreadCC with (cntj' := pfj')
          by eauto
        |
        erewrite gsoThreadCode with (cntj' := pfj')
          by eauto];
        reflexivity.
    Qed.

    Lemma gsoThreadC_exec:
      forall tp m tp' m' i j xs
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m')
        (Hneq: i <> j),
        getThreadC pfj = getThreadC pfj'.
    Proof.
      intros. generalize dependent tp. generalize dependent m.
      induction xs; intros.
      - simpl in Hstep. inversion Hstep; subst.
        now Tactics.pf_cleanup.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst a. inversion Hstep; subst.
          simpl in Htrans.
          assert (pfj'0: containsThread tp'0 j)
            by (eapply containsThread_internal_step; eauto).
          specialize (IHxs _ _  pfj'0 Htrans).
          rewrite <- IHxs.
          erewrite gsoThreadC_step; eauto.
          simpl in HschedN. inversion HschedN; subst.
          assumption.
        + eauto.
    Qed.

    (** Other thread permissions do not change by [internal_step]*)
    Lemma gsoThreadR_step:
      forall tp tp' m m' i j (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step pfi Hcomp tp' m')
        (Hneq: i <> j),
        getThreadR pfj = getThreadR pfj'.
    Proof.
      intros. destruct Hstep as [[? Hstep] | [[Hstep Heq] | Hstep]];
        inversion Hstep; subst;
        [erewrite <- @gsoThreadRes with (cntj' := pfj') |
         erewrite <- @gThreadCR with (cntj' := pfj')
         | erewrite <- @gsoThreadRes with (cntj' := pfj')];
          by eauto.
    Qed.

    Corollary permission_at_step:
      forall tp tp' m m' i j
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step pfi Hcomp tp' m') b ofs,
        permission_at (restrPermMap ((compat_th _ _ Hcomp) pfj).1) b ofs Cur =
        permission_at (restrPermMap ((compat_th _ _ Hcomp') pfj').1) b ofs Cur /\
        permission_at (restrPermMap ((compat_th _ _ Hcomp) pfj).2) b ofs Cur =
        permission_at (restrPermMap ((compat_th _ _ Hcomp') pfj').2) b ofs Cur.
    Proof.
      intros;
        rewrite! restrPermMap_Cur;
      erewrite @gsoThreadR_step;
        by eauto.
    Qed.

    Lemma gsoThreadR_execution:
      forall tp m tp' m' i j xs
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hneq: i <> j)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m'),
        getThreadR pfj = getThreadR pfj'.
    Proof.
      intros. generalize dependent tp. generalize dependent m.
      induction xs; intros.
      - simpl in Hstep. inversion Hstep; subst.
        now Tactics.pf_cleanup.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst a. inversion Hstep; subst.
          simpl in Htrans.
          simpl in HschedN; inversion HschedN; subst tid.
          Tactics.pf_cleanup.
          assert (pfj'0: containsThread tp'0 j)
            by (eapply containsThread_internal_step; eauto).
          specialize (IHxs _ _  pfj'0 Htrans).
          rewrite <- IHxs.
          erewrite gsoThreadR_step; eauto.
        + eauto.
    Qed.

    (** The [lockRes] is preserved by [internal_step]*)
    Lemma gsoLockPool_step:
      forall tp tp' m m' i (pfi: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step pfi Hcomp tp' m') addr,
        lockRes tp addr = lockRes tp' addr.
    Proof.
      intros;
      destruct Hstep as [[? Htstep] | [[Htstep ?] | [Htstep ?]]];
      inversion Htstep;
      subst;
      [erewrite gsoThreadLPool |
       erewrite gsoThreadCLPool |
       erewrite gsoThreadLPool];
        by reflexivity.
    Qed.

    (** The [lockRes] is preserved by [internal_execution]*)
    Lemma gsoLockPool_execution :
      forall (tp : t) (m : mem) (tp' : t)
        (m' : mem) (i : nat) (xs : seq nat_eqType)
        (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m')
        addr,
        lockRes tp addr = lockRes tp' addr.
    Proof.
      intros. generalize dependent tp. generalize dependent m.
      induction xs; intros.
      - simpl in Hexec.
        inversion Hexec; subst;
          Tactics.pf_cleanup;
          [reflexivity| simpl in *; discriminate].
      - simpl in Hexec.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq; try eauto.
        subst a. inversion Hexec; subst.
        simpl in Htrans.
        simpl in HschedN; inversion HschedN; subst tid.
        Tactics.pf_cleanup.
        specialize (IHxs _ _  Htrans).
        rewrite <- IHxs.
        erewrite gsoLockPool_step; eauto.
    Qed.

    (** Lock resources of the threads are preserved by [internal_step] *)
    Lemma internal_step_locks_eq:
      forall tp m tp' m' i (cnti: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step cnti Hcomp tp' m'),
      forall j (cntj: containsThread tp j) (cntj': containsThread tp' j),
        (getThreadR cntj).2 = (getThreadR cntj').2.
    Proof.
      intros.
      destruct Hstep as [[? Htstep] | [[Htstep ?] | Htstep]];
        inversion Htstep;
        subst;
      destruct (i == j) eqn:Hij;
        move/eqP:Hij=>Hij;
                       subst;
                       solve
                         [rewrite gssThreadRes; Tactics.pf_cleanup; reflexivity
                         | erewrite @gsoThreadRes with (cntj := cntj) by eauto;
                           Tactics.pf_cleanup; reflexivity
                         | rewrite gThreadCR; Tactics.pf_cleanup; reflexivity].
    Qed.

    (** Lock resources of the threads are preserved by [internal_execution] *)
    Lemma internal_execution_locks_eq:
      forall tp m tp' m' xs
        (Hexec: internal_execution xs tp m tp' m'),
      forall j (cntj: containsThread tp j) (cntj': containsThread tp' j),
        (getThreadR cntj).2 = (getThreadR cntj').2.
    Proof.
      intros. generalize dependent tp. generalize dependent m.
      induction xs; intros.
      - simpl in Hexec. inversion Hexec; subst.
        now Tactics.pf_cleanup.
        simpl in HschedN. by discriminate.
      - simpl in Hexec.
        inversion Hexec; subst; simpl in *.
        inversion HschedN; subst.
        pose proof Hstep as Hstep2.
        eapply internal_step_locks_eq with
        (cntj := cntj)
          (cntj' := containsThread_internal_step Hstep cntj)
          in Hstep2; eauto.
        specialize (IHxs _ _  Htrans).
        rewrite Hstep2.
        now eapply IHxs.
    Qed.

    Lemma permission_at_execution:
      forall tp m tp' m' i j xs
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hneq: i <> j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m'),
      forall b ofs,
        permission_at (restrPermMap ((compat_th _ _ Hcomp) pfj).1) b ofs Cur =
        permission_at (restrPermMap ((compat_th _ _ Hcomp') pfj').1) b ofs Cur /\
        permission_at (restrPermMap ((compat_th _ _ Hcomp) pfj).2) b ofs Cur =
        permission_at (restrPermMap ((compat_th _ _ Hcomp') pfj').2) b ofs Cur.
    Proof.
      intros.
      rewrite! restrPermMap_Cur.
      erewrite gsoThreadR_execution; eauto.
    Qed.

    (** Lifting [corestep_disjoint_val] to [internal_step]*)
    Lemma internal_step_disjoint_val :
      forall tp tp' m m' i j
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step pfi Hcomp tp' m') b ofs
        (Hreadable:
           Mem.perm (restrPermMap ((compat_th _ _ Hcomp) pfj).1)b ofs Cur Readable \/
           Mem.perm (restrPermMap ((compat_th _ _ Hcomp) pfj).2) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      inversion Hstep as [[? Htstep] | [[Htstep Heq] | Htstep]]; subst; auto.
      inversion Htstep; subst; eapply event_semantics.ev_step_ax1 in Hcorestep;
        eapply CoreLanguageDry.corestep_disjoint_val;
          by eauto.
      inversion Htstep; subst.
      inversion Hperm; subst.
      Tactics.pf_cleanup.
      eapply CoreLanguageDry.initial_core_disjoint_val;
        now eauto.
    Qed.
      
    Lemma internal_exec_disjoint_val :
      forall tp tp' m m' i j xs
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m') b ofs
        (Hreadable:
           Mem.perm (restrPermMap ((compat_th _ _ Hcomp) pfj).1) b ofs Cur Readable \/
           Mem.perm (restrPermMap ((compat_th _ _ Hcomp) pfj).2) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      generalize dependent tp.  generalize dependent m.
      induction xs as [|x xs]; intros.
      - simpl in Hstep; inversion Hstep; subst.
        reflexivity.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (x == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst x.
          inversion Hstep; subst.
          simpl in Htrans.
          simpl in HschedN.
          inversion HschedN; subst tid.
          Tactics.pf_cleanup.
          assert (pfj0': containsThread tp'0 j) by
              (eapply containsThread_internal_step; eauto).
          assert (pfi0': containsThread tp'0 i) by
              (eapply containsThread_internal_step; eauto).
          assert(Hcomp0': mem_compatible tp'0 m'0) by
              (eapply internal_step_compatible; eauto).
          assert (Hreadable0':
                    Mem.perm (restrPermMap ((compat_th _ _ Hcomp0') pfj0').1) b ofs Cur Readable \/
                    Mem.perm (restrPermMap ((compat_th _ _ Hcomp0') pfj0').2) b ofs Cur Readable).
          { clear IHxs Htrans HschedN Hstep.
            destruct (permission_at_step Hneq  pfj pfj0' Hcomp0' Hstep0 b ofs)
              as [Hperm_eq1 Hperm_eq2].
            rewrite! restrPermMap_Cur in Hperm_eq1 Hperm_eq2.
            unfold Mem.perm in *.
            assert (H1:= restrPermMap_Cur ((compat_th _ _ Hcomp0') pfj0').1 b ofs).
            assert (H2:= restrPermMap_Cur ((compat_th _ _ Hcomp0') pfj0').2 b ofs).
            unfold permission_at in H1, H2.
            rewrite H1 H2. rewrite <- Hperm_eq1, <- Hperm_eq2.
            assert (H1':= restrPermMap_Cur ((compat_th _ _ Hcomp) pfj).1 b ofs).
            assert (H2':= restrPermMap_Cur ((compat_th _ _ Hcomp) pfj).2 b ofs).
            unfold permission_at in H1', H2'.
            rewrite H1' H2' in Hreadable. assumption.
          }
          specialize (IHxs _ _  pfi0' pfj0' Hcomp0' Htrans Hreadable0').
          rewrite <- IHxs.
          eapply internal_step_disjoint_val; eauto.
        + by eauto.
    Qed.

    (** Locks resources are always disjoint from data resources (even for the
    same thread)*)
    Lemma internal_step_disjoint_locks :
      forall tp tp' m m' i j
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step pfi Hcomp tp' m') b ofs
        (Hreadable:
           Mem.perm (restrPermMap ((compat_th _ _ Hcomp) pfj).2) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      inversion Hstep as [[? Htstep] | [[Htstep Heq] | Htstep]]; subst; auto.
      inversion Htstep; subst; eapply event_semantics.ev_step_ax1 in Hcorestep;
        eapply CoreLanguageDry.corestep_disjoint_locks;
          by eauto.
      (* initial core *)
      inversion Htstep; subst.
      inversion Hperm.
      subst.
      Tactics.pf_cleanup.
      eapply CoreLanguageDry.initial_core_disjoint_locks;
        now eauto.
    Qed.
    
    Lemma internal_exec_disjoint_locks:
      forall tp tp' m m' i j xs
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m') b ofs
        (Hreadable: Mem.perm (restrPermMap ((compat_th _ _ Hcomp) pfj).2) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      generalize dependent tp.  generalize dependent m.
      induction xs as [|x xs]; intros.
      - simpl in Hstep; inversion Hstep; subst.
        reflexivity.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (x == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst x.
          inversion Hstep; subst.
          simpl in Htrans.
          simpl in HschedN.
          inversion HschedN; subst tid.
          Tactics.pf_cleanup.
          assert (pfj0': containsThread tp'0 j) by
              (eapply containsThread_internal_step; eauto).
          assert (pfi0': containsThread tp'0 i) by
              (eapply containsThread_internal_step; eauto).
          assert(Hcomp0': mem_compatible tp'0 m'0) by
              (eapply internal_step_compatible; eauto).
          assert (Hreadable0':
                    Mem.perm (restrPermMap ((compat_th _ _ Hcomp0') pfj0').2) b ofs Cur Readable).
          { clear IHxs Htrans HschedN Hstep.
            pose proof (internal_step_locks_eq Hstep0 pfj pfj0') as Heq_perm.
            unfold Mem.perm in *.
            assert (H2:= restrPermMap_Cur ((compat_th _ _ Hcomp0') pfj0').2 b ofs).
            assert (H2':= restrPermMap_Cur ((compat_th _ _ Hcomp) pfj).2 b ofs).
            unfold permission_at in H2, H2'.
            rewrite H2.
            rewrite H2' in Hreadable.
            rewrite <- Heq_perm.
            assumption.
          }
          specialize (IHxs _ _  pfi0' pfj0' Hcomp0' Htrans Hreadable0').
          rewrite <- IHxs.
          eapply internal_step_disjoint_locks; eauto.
        + by eauto.
    Qed.

    Lemma internal_step_stable :
      forall tp tp' m m' i
        (pfi: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step pfi Hcomp tp' m')
        b ofs
        (Hvalid: Mem.valid_block m b)
        (Hstable: ~ Mem.perm (restrPermMap ((compat_th _ _ Hcomp) pfi).1) b ofs Cur Writable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      inversion Hstep as [[? Htstep] | [[Htstep Heq] | Htstep]]; subst; auto.
      inversion Htstep; subst; eapply ev_unchanged_on in Hcorestep;
        by eauto.
      inversion Htstep; subst.
      inversion Hperm; subst.
      Tactics.pf_cleanup.
      eapply initial_core_unchanged_on in Hinitial;
        now eauto.
    Qed.

    (** Data resources of a thread that took an internal step are related by [decay]*)
    Lemma internal_step_decay:
      forall tp m tp' m' i (cnt: containsThread tp i)
        (cnt': containsThread tp' i)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step cnt Hcomp tp' m'),
        decay (restrPermMap ((compat_th _ _ Hcomp) cnt).1)
              (restrPermMap ((compat_th _ _ Hcomp') cnt').1).
    Proof.
      intros. unfold decay. intros b ofs.
      assert (HpermCur: permission_at
                       (restrPermMap ((compat_th _ _ Hcomp') cnt').1) b ofs Cur =
                     (getThreadR cnt').1 # b ofs)
        by (eapply restrPermMap_Cur; eauto).
      assert (HpermMax: permission_at
                          (restrPermMap ((compat_th _ _ Hcomp') cnt').1) b ofs Max =
                        (Mem.mem_access m') # b ofs Max)
        by (erewrite restrPermMap_Max;
             erewrite getMaxPerm_correct;
               by unfold permission_at).
      unfold permission_at in *.
      destruct Hstep as [[? Hcstep] | [[Hresume ?] | Hstart]]; subst.
      - inversion Hcstep. subst.
        apply event_semantics.ev_step_ax1 in Hcorestep.
        eapply corestep_decay in Hcorestep.
        destruct (Hcorestep b ofs).
        split.
        + intros.
          erewrite restrPermMap_valid in H2.
          assert (Hpmap: (getThreadR cnt').1 = getCurPerm m')
            by (by rewrite gssThreadRes).
          specialize (H H1 H2).
          destruct H as [H | H];
            [left | right]; intros k;
            specialize (H k);
            destruct k;
            try (rewrite HpermMax);
            try (rewrite HpermCur); auto;
          try (rewrite Hpmap;
               rewrite getCurPerm_correct;
               unfold permission_at;
                 by assumption).
        + intros Hvalid.
          specialize (H0 Hvalid).
          destruct H0 as [H0 | H0];
            [left | right];
            intros k;
            specialize (H0 k);
            [destruct H0 | idtac];
            destruct k;
            try rewrite HpermMax;
            try rewrite HpermCur;
            try split;
            auto;
          try rewrite gssThreadRes;
          try rewrite getCurPerm_correct;
          unfold permission_at;
            by assumption.
      - inversion Hresume; subst.
        assert (Hpmap: getThreadR cnt' = getThreadR cnt)
          by (apply gThreadCR).
        assert (H: forall k,
                   (Mem.mem_access (restrPermMap ((compat_th _ _ Hcomp') cnt').1)) # b ofs k =
                   (Mem.mem_access (restrPermMap ((compat_th _ _ Hcomp) cnt).1)) # b ofs k).
        { intros k.
          destruct k.
          rewrite HpermMax.
          assert (H := restrPermMap_Max (((compat_th _ _ Hcomp) cnt).1) b ofs).
          rewrite getMaxPerm_correct in H.
          unfold permission_at in H.
            by rewrite H.
          rewrite HpermCur.
          rewrite Hpmap.
          assert (H := restrPermMap_Cur (((compat_th _ _ Hcomp) cnt).1) b ofs).
          unfold permission_at in H;
            by rewrite H. }
        split.
        intros.
        right.
        intros k.
        apply Mem.nextblock_noaccess with (ofs := ofs) (k := k) in H0.
        specialize (H k).
        rewrite H;
          by assumption.
        intros; auto.
      - inversion Hstart; subst.
        inversion Hperm; subst.
        eapply initial_core_decay in Hinitial.
        eapply strong_decay_implies_decay in Hinitial.
        destruct (Hinitial b ofs) as [Hfresh Hold].
        split.
        + intros.
          erewrite restrPermMap_valid in Hold.
          assert (Hpmap: (getThreadR cnt').1 = getCurPerm m')
            by (by rewrite gssThreadRes).
          specialize (Hfresh H H0).
          destruct Hfresh as [Hfresh | Hfresh];
            [left | right]; intros k;
            specialize (Hfresh k);
            destruct k;
            try (rewrite HpermMax);
            try (rewrite HpermCur); auto;
          try (rewrite Hpmap;
               rewrite getCurPerm_correct;
               unfold permission_at;
                 by assumption).
        + intros Hvalid.
          specialize (Hold Hvalid).
          Tactics.pf_cleanup.
          destruct Hold as [Hold | Hold];
            [left | right];
            intros k;
            specialize (Hold k);
            [destruct Hold | idtac];
            destruct k;
            try rewrite HpermMax;
            try rewrite HpermCur;
            try split;
            auto;
          try rewrite gssThreadRes;
          try rewrite getCurPerm_correct;
          unfold permission_at;
            by assumption.
    Qed.
    
    (** [Mem.valid_block] is preserved by [internal_step]*)
    Lemma internal_step_valid:
      forall tp m tp' m' i (cnt: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step cnt Hcomp tp' m') b
        (Hvalid: Mem.valid_block m b),
        Mem.valid_block m' b.
    Proof.
      intros.
      destruct Hstep as [[? Htstep] | [[_ ?] | ?]];
        [inversion Htstep; subst;
         eapply ev_step_validblock;
           by eauto | by subst | subst].
      inversion H. subst.
      inversion Hperm; subst.
      eapply initial_core_validblock in Hinitial;
        now eauto.
    Qed.

    Lemma internal_execution_valid :
      forall tp m tp' m' xs
        (Hexec: internal_execution xs tp m tp' m') b
        (Hvalid: Mem.valid_block m b),
        Mem.valid_block m' b.
    Proof.
      intros.
      generalize dependent tp. generalize dependent m.
      induction xs as [|x xs]; intros.
      inversion Hexec; subst; first by assumption.
      simpl in HschedN;
        by discriminate.
      inversion Hexec; subst.
      simpl in HschedN. inversion HschedN; subst.
      simpl in Htrans.
      assert (Hvalid0: Mem.valid_block m'0 b)
        by (eapply internal_step_valid; eauto).
        by eauto.
    Qed.

    Lemma internal_exec_stable:
      forall tp tp' m m' i xs
        (pfi: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m')
        b ofs
        (Hvalid: Mem.valid_block m b)
        (Hstable:  ~ Mem.perm (restrPermMap ((compat_th _ _ Hcomp) pfi).1) b ofs Cur Writable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      generalize dependent tp.  generalize dependent m.
      induction xs as [|x xs]; intros.
      - simpl in Hstep; inversion Hstep; subst.
        reflexivity.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (x == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst x.
          inversion Hstep; subst.
          simpl in Htrans.
          simpl in HschedN.
          inversion HschedN; subst tid.
          Tactics.pf_cleanup.
          assert (pfi0': containsThread tp'0 i) by
              (eapply containsThread_internal_step; eauto).
          assert(Hcomp0': mem_compatible tp'0 m'0) by
              (eapply internal_step_compatible; eauto).
          assert (Hstable0':
                    ~ Mem.perm (restrPermMap ((compat_th _ _ Hcomp0') pfi0').1) b ofs Cur Writable).
          { clear IHxs Htrans HschedN Hstep.
            pose proof (internal_step_decay pfi0' Hcomp0' Hstep0) as Hdecay.
            unfold decay in Hdecay.
            destruct (Hdecay b ofs) as [_ Hdecay'].
            destruct (Hdecay' Hvalid) as [Hcontra | Heq].
            - destruct (Hcontra Cur) as [Hcontra' _].
              unfold Mem.perm in Hstable.
              rewrite Hcontra' in Hstable.
              simpl in Hstable. exfalso.
              now eauto using perm_order.
            - specialize (Heq Cur).
              unfold Mem.perm in *.
              rewrite Heq in Hstable.
              assumption.
          }
          pose proof Hvalid as Hvalid0'.
          eapply internal_step_valid in Hvalid0'; eauto.
          specialize (IHxs _ Hvalid0' _ pfi0' Hcomp0' Htrans Hstable0').
          rewrite <- IHxs.
          eapply internal_step_stable; eauto.
        + by eauto.
    Qed.

    Lemma internal_execution_decay:
      forall tp m tp' m' xs i (cnt: containsThread tp i)
        (cnt': containsThread tp' i)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m'),
        decay (restrPermMap ((compat_th _ _ Hcomp) cnt).1)
              (restrPermMap ((compat_th _ _ Hcomp') cnt').1).
    Proof.
      intros tp m tp' m' xs.
      generalize dependent tp. generalize dependent m.
      induction xs.
      - intros. simpl in Hexec. inversion Hexec; subst.
        Tactics.pf_cleanup.
          by apply decay_refl.
        simpl in HschedN. discriminate.
      - intros.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + simpl in Hexec.
          erewrite if_true in Hexec by (apply eq_refl).
          inversion Hexec; subst; simpl in *.
          inversion HschedN; subst tid.
          assert (Hcomp'0: mem_compatible tp'0 m'0)
            by (eapply internal_step_compatible; eauto).
          assert (cnt0': containsThread tp'0 i)
            by (eapply containsThread_internal_step; eauto).
          Tactics.pf_cleanup.
          eapply IHxs with
          (Hcomp := Hcomp'0) (Hcomp' := Hcomp')
                             (cnt := cnt0') (cnt' := cnt') in Htrans.
          assert (Hdecay:
                    decay (restrPermMap ((compat_th _ _ Hcomp0) cnt).1)
                          (restrPermMap ((compat_th _ _ Hcomp'0) cnt0').1))
            by (eapply internal_step_decay; eauto).
          eapply decay_trans with (m' := (restrPermMap ((compat_th _ _ Hcomp'0) cnt0').1));
            eauto.
          intros.
          erewrite restrPermMap_valid.
          eapply internal_step_valid;
            by eauto.
        + simpl in Hexec.
          erewrite if_false in Hexec
            by (apply/eqP; assumption).
          auto.
    Qed.

    Lemma internal_step_disjoint_val_lockPool :
      forall tp tp' m m' i bl ofsl pmap
        (pfi: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step pfi Hcomp tp' m') b ofs
        (Hl: lockRes tp (bl,ofsl) = Some pmap)
        (Hreadable: Mem.perm (restrPermMap ((compat_lp _ _ Hcomp) _ _ Hl).1)
                             b ofs Cur Readable \/
                    Mem.perm (restrPermMap ((compat_lp _ _ Hcomp) _ _ Hl).2)
                             b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      inversion Hstep as [[? Hcstep] | [[Hrstep Heq] | Hsstep]]; subst; auto.
      inversion Hcstep; subst; eapply event_semantics.ev_step_ax1 in Hcorestep;
      eapply CoreLanguageDry.corestep_disjoint_val_lockpool;
        by eauto.
      inversion Hsstep; subst.
      inversion Hperm; subst.
      Tactics.pf_cleanup.
      eapply CoreLanguageDry.initial_core_disjoint_val_lockpool;
        eauto.
    Qed.

    Lemma internal_exec_disjoint_val_lockPool:
      forall (tp tp' : t) (m m' : mem) (i : nat) xs bl ofsl pmap
        (Hcomp : mem_compatible tp m)
        (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m')
        (Hl: lockRes tp (bl,ofsl) = Some pmap)
        b ofs
        (Hreadable: Mem.perm (restrPermMap ((compat_lp _ _ Hcomp) _ _ Hl).1)
                             b ofs Cur Readable \/
                    Mem.perm (restrPermMap ((compat_lp _ _ Hcomp) _ _ Hl).2)
                             b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      generalize dependent tp.  generalize dependent m.
      induction xs as [|x xs]; intros.
      - simpl in Hexec; inversion Hexec; subst.
        reflexivity.
        simpl in HschedN. by discriminate.
      - simpl in Hexec.
        destruct (x == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst x.
          inversion Hexec; subst.
          simpl in Htrans.
          simpl in HschedN.
          inversion HschedN; subst tid.
          Tactics.pf_cleanup.
          assert (pfi0': containsThread tp'0 i) by
              (eapply containsThread_internal_step; eauto).
          assert(Hcomp0': mem_compatible tp'0 m'0) by
              (eapply internal_step_compatible; eauto).
          assert (Hl0': lockRes tp'0 (bl, ofsl) = Some pmap)
            by (erewrite <- gsoLockPool_step; eauto).
          assert (Hreadable0':
                    Mem.perm (restrPermMap ((compat_lp _ _ Hcomp0') _ _ Hl0').1)
                             b ofs Cur Readable \/
                    Mem.perm (restrPermMap ((compat_lp _ _ Hcomp0') _ _ Hl0').2)
                             b ofs Cur Readable).
          { clear IHxs Htrans HschedN.
            unfold Mem.perm in *.
            assert (H1:= restrPermMap_Cur ((compat_lp _ _ Hcomp0') _ _ Hl0').1 b ofs).
            assert (H2:= restrPermMap_Cur ((compat_lp _ _ Hcomp0') _ _ Hl0').2 b ofs).
            unfold permission_at in H1, H2.
            rewrite H1 H2.
            assert (H1':= restrPermMap_Cur ((compat_lp _ _ Hcomp) _ _ Hl).1 b ofs).
            assert (H2':= restrPermMap_Cur ((compat_lp _ _ Hcomp) _ _ Hl).2 b ofs).
            unfold permission_at in H1', H2'.
              by rewrite H1' H2' in Hreadable.
          }
          specialize (IHxs _ _  Hcomp0' Htrans Hl0' Hreadable0').
          rewrite <- IHxs.
          eapply internal_step_disjoint_val_lockPool; eauto.
        + by eauto.
    Qed.

    Opaque OrdinalPool.getThreadR.
    Lemma updThread_internal_step:
      forall tp tp' m m' i j c pmap
        (Hneq: i <> j)
        (cnti: containsThread tp i)
        (cnti': containsThread tp' i)
        (cntj: containsThread tp j)
        (cntj': containsThread (updThread cnti c pmap) j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible (updThread cnti c pmap) m)
        (Hinv': invariant (updThread cnti c pmap))
        (Hstep: internal_step cntj Hcomp tp' m'),
        internal_step cntj' Hcomp' (updThread cnti' c pmap) m'.
    Proof.
      intros.
      inversion Hstep as [[? ?] | [[? ?] | ?]].
      - inversion H; subst.
        left.
        exists x.
        eapply @step_dry with (c := c0) (c' := c'); eauto.
        erewrite gsoThreadCode; eauto.
        erewrite <- restrPermMap_irr' with
        (Hlt' := ((compat_th _ _ Hcomp') cntj').1) (Hlt := ((compat_th _ _ Hcomp) cntj).1);
          eauto.
        erewrite @gsoThreadRes with (cntj := cntj); eauto.
        erewrite @gsoThreadRes with (cntj := cntj) by eauto.
        rewrite updThread_comm; auto.
      - subst.
        inversion H; subst.
        right. left.
        split; auto.
        Tactics.pf_cleanup.
        econstructor; eauto.
        simpl in *. unfold HybridMachine.DryHybridMachine.install_perm in *.
        erewrite restrPermMap_irr with (m2 := m') (P2 := (Hcomp j ctn).1); eauto.
        simpl.
        erewrite @OrdinalPool.gsoThreadRes;
          now eauto.
        erewrite @gsoThreadCode with (cntj := ctn); eauto.
        Tactics.pf_cleanup. auto.
        simpl.
        rewrite OrdinalPool.updThread_updThreadC_comm; auto.
      - subst.
        inversion H; subst.
        do 2 right.
        eapply @StartThread with (Hcmpt := Hcomp'); eauto.
        + erewrite @gsoThreadCode with (cntj := cntj) by eauto.
          Tactics.pf_cleanup. now auto.
        + simpl in *.
          unfold HybridMachine.DryHybridMachine.install_perm in *.
          subst.
          eapply restrPermMap_irr'.
          simpl.
          erewrite @OrdinalPool.gsoThreadRes with (cntj' := cntj');
            now eauto.
        + Tactics.pf_cleanup.
          simpl in *.
          unfold HybridMachine.DryHybridMachine.add_block in *.
          simpl in *.
          rewrite OrdinalPool.updThread_comm; eauto.
          erewrite @OrdinalPool.gsoThreadRes with (cntj' := cntj') by eauto.
          reflexivity.
          (* inversion Hperm; subst. *)
        (*   clear - SemAx Hcomp' Hcmpt' Hinitial. *)
        (*   destruct Hcmpt'. *)
        (*   destruct Hcomp'. *)
        (*   econstructor; eauto. *)
        (*   intros tid cnt. *)
        (*   destruct (i == tid) eqn:Hitid; move/eqP:Hitid=>Hitid; subst. *)
        (*   *  Tactics.pf_cleanup. *)
        (*      pose proof (cntUpdate c pmap cnti cnti) as cnti''. *)
        (*      specialize (compat_th1 _ cnti''). *)
        (*      erewrite gssThreadRes. *)
        (*      erewrite gssThreadRes in compat_th1. *)
        (*      eapply initial_core_decay in Hinitial. *)
        (*      destruct compat_th1. *)
        (*      split; *)
        (*      eapply CoreLanguageDry.permMapLt_decay; eauto; *)
        (*      intros b ofs; *)
        (*      rewrite getMax_restr; *)
        (*      auto. *)
        (*   * pose proof (cntUpdate' _ _ cnti' cnt) as cnt'. *)
        (*     specialize (compat_th0 _ cnt'). *)
        (*     erewrite gsoThreadRes with (cntj := cnt') by eauto. *)
        (*     eapply compat_th0. *)
        (* + econstructor; eauto. *)
        (*   { intros k l cntk cntl Hneqkl. *)
        (*     pose proof (cntUpdate c pmap cnti cnti) as cnti1. *)
        (*     destruct (k == i) eqn:Hki, (l == i) eqn:Hli; *)
        (*       move/eqP:Hki=>Hki;move/eqP:Hli=>Hli; subst. *)
        (*     - exfalso; auto. *)
        (*     - erewrite gssThreadRes. *)
        (*       pose proof (cntUpdate' _ _ cnti' cntl) as cntl0. *)
        (*       erewrite @gsoThreadRes with (cntj := cntl0) by eauto. *)
        (*       destruct (l == j) eqn:Hlj; *)
        (*         move/eqP:Hlj=>Hlj; subst. *)
        (*       + erewrite gssThreadRes. *)
        (*         simpl (add_block) in *. *)
        (*         unfold HybridMachine.DryHybridMachine.add_block in *. *)
        (*         split. *)
        (*         * simpl. *)
        (*           eapply initial_core_decay in Hinitial. *)
        (*           eapply strong_decay_implies_decay in Hinitial. *)
        (*           inversion Hperm; subst. *)
        (*           apply permMapsDisjoint_comm. *)
        (*           eapply CoreLanguageDry.decay_disjoint; eauto. *)
        (*           intros b ofs. *)
        (*           rewrite getMax_restr. *)
        (*           pose proof (compat_th _ _ Hcomp' cnti1) as [Hlt _]. *)
        (*           rewrite gssThreadRes in Hlt. *)
        (*           now eauto. *)
        (*           pose proof (no_race_thr _ Hinv' _ _ cnti1 cntj' Hneqkl) as [Hdisjoint _]. *)
        (*           rewrite gssThreadRes in Hdisjoint. *)
        (*           intros b ofs. *)
        (*           erewrite getCurPerm_correct. *)
        (*           rewrite restrPermMap_Cur. *)
        (*           erewrite @gsoThreadRes with (cntj:= ctn) in Hdisjoint by eauto. *)
        (*           apply permMapsDisjoint_comm. *)
        (*           now eauto. *)
        (*         * pose proof (no_race_thr _ Hinv' _ _ cnti1 cntj' Hneqkl) as [_ Hdisjoint]. *)
        (*           rewrite gssThreadRes in Hdisjoint. *)
        (*           erewrite @gsoThreadRes with (cntj:= ctn) in Hdisjoint by eauto. *)
        (*           now eauto. *)
        (*       + pose proof (cntUpdate' _ _ ctn cntl0) as cntl00. *)
        (*         erewrite @gsoThreadRes with (cntj := cntl00) by eauto. *)
        (*         pose proof (cntUpdate c pmap cnti cntl00) as cntli. *)
        (*         erewrite <- @gsoThreadRes with (cntj' := cntli) by eauto. *)
        (*         pose proof (no_race_thr _ Hinv' _ _ cnti1 cntli Hneqkl) as Hdis. *)
        (*         rewrite gssThreadRes in Hdis. *)
        (*         assumption. *)
        (*     - erewrite gssThreadRes. *)
        (*       pose proof (cntUpdate' _ _ cnti' cntk) as cntk0. *)
        (*       erewrite @gsoThreadRes with (cntj := cntk0) by eauto. *)
        (*       destruct (k == j) eqn:Hkj; *)
        (*         move/eqP:Hkj=>Hkj; subst. *)
        (*       + erewrite gssThreadRes. *)
        (*         simpl (add_block) in *. *)
        (*         unfold HybridMachine.DryHybridMachine.add_block in *. *)
        (*         split. *)
        (*         * simpl. *)
        (*           eapply initial_core_decay in Hinitial. *)
        (*           eapply strong_decay_implies_decay in Hinitial. *)
        (*           inversion Hperm; subst. *)
        (*           eapply CoreLanguageDry.decay_disjoint; eauto. *)
        (*           intros b ofs. *)
        (*           rewrite getMax_restr. *)
        (*           pose proof (compat_th _ _ Hcomp' cnti1) as [Hlt _]. *)
        (*           rewrite gssThreadRes in Hlt. *)
        (*           now eauto. *)
        (*           pose proof (no_race_thr _ Hinv' _ _ cnti1 cntj' Hneq) as [Hdisjoint _]. *)
        (*           rewrite gssThreadRes in Hdisjoint. *)
        (*           intros b ofs. *)
        (*           erewrite getCurPerm_correct. *)
        (*           rewrite restrPermMap_Cur. *)
        (*           erewrite @gsoThreadRes with (cntj:= ctn) in Hdisjoint by eauto. *)
        (*           apply permMapsDisjoint_comm. *)
        (*           now eauto. *)
        (*         * pose proof (no_race_thr _ Hinv' _ _ cnti1 cntj' Hneq) as [_ Hdisjoint]. *)
        (*           rewrite gssThreadRes in Hdisjoint. *)
        (*           erewrite @gsoThreadRes with (cntj:= ctn) in Hdisjoint by eauto. *)
        (*           now eauto using permMapsDisjoint_comm. *)
        (*       + pose proof (cntUpdate' _ _ ctn cntk0) as cntk00. *)
        (*         erewrite @gsoThreadRes with (cntj := cntk00) by eauto. *)
        (*         pose proof (cntUpdate c pmap cnti cntk00) as cntki. *)
        (*         erewrite <- @gsoThreadRes with (cntj' := cntki) by eauto. *)
        (*         pose proof (no_race_thr _ Hinv' _ _ cntki cnti1 ltac:(eauto)) as Hdis. *)
        (*         rewrite gssThreadRes in Hdis. *)
        (*         assumption. *)
        (*     - pose proof (cntUpdate' _ _ cnti' cntk) as cntk0. *)
        (*       pose proof (cntUpdate' _ _ ctn cntk0) as cntk00. *)
        (*       pose proof (cntUpdate' _ _ cnti' cntl) as cntl0. *)
        (*       pose proof (cntUpdate' _ _ ctn cntl0) as cntl00. *)
        (*       erewrite @gsoThreadRes with (cntj := cntk0) by eauto. *)
        (*       erewrite @gsoThreadRes with (cntj := cntl0) by eauto. *)
        (*       eapply Hinv'0; *)
        (*         now eauto. *)
        (*   } *)
        (*   { intros. *)
        (*     erewrite! gsoThreadLPool in Hres1, Hres2. *)
        (*     eapply Hinv; *)
        (*        now eauto. *)
        (*   } *)
        (*   { intros. *)
        (*     erewrite! gsoThreadLPool in Hres. *)
        (*     destruct (i0 == i) eqn:Hii0; move/eqP:Hii0=>Hii0; subst. *)
        (*     - rewrite gssThreadRes. *)
        (*       pose proof (no_race _ Hinv' _ _ cnti0 _ Hres) as Hdis. *)
        (*       rewrite gssThreadRes in Hdis. *)
        (*       assumption. *)
        (*     - pose proof (cntUpdate' _ _ cnti' cnti0) as cnti00. *)
        (*       pose proof (no_race _ Hinv'0 _ _ cnti00 _ Hres). *)
        (*       erewrite @gsoThreadRes with (cntj := cnti00) by eauto. *)
        (*       assumption. *)
        (*   } *)
        (*   { intros. *)
        (*     pose proof (cntUpdate c pmap cnti cnti) as cnti1. *)
        (*     destruct (i0 == i) eqn:Hii0; move/eqP:Hii0=>Hii0; subst. *)
        (*     - rewrite gssThreadRes. *)
        (*       split. *)
        (*       + intros j0 cntj0. *)
        (*         destruct (j0 == i) eqn:Hij0; move/eqP:Hij0=>Hij0; subst. *)
        (*         * rewrite gssThreadRes. *)
        (*           pose proof ((thread_data_lock_coh _ Hinv' _ cnti0).1 _ cnti0) as Hcoh. *)
        (*           rewrite gssThreadRes in Hcoh. *)
        (*           assumption. *)
        (*         * pose proof (cntUpdate' _ _ cnti' cntj0) as cntj00. *)
        (*           pose proof (cntUpdate' _ _ ctn cntj00) as cntj000. *)
        (*           pose proof (cntUpdate c pmap cnti cntj000) as cntj0'. *)
        (*           erewrite @gsoThreadRes with (cntj := cntj00) by eauto. *)
        (*           destruct (j == j0) eqn:Hjj0; move/eqP:Hjj0=>Hjj0; subst. *)
        (*           ** rewrite gssThreadRes. *)
        (*              inversion Hperm; subst. *)
        (*              eapply initial_core_decay in Hinitial. *)
        (*              eapply strong_decay_implies_decay in Hinitial. *)
        (*              eapply CoreLanguageDry.decay_coherence in Hinitial; eauto. *)
        (*              intros b ofs. *)
        (*              rewrite getMax_restr. *)
        (*              pose proof (compat_th _ _ Hcomp' cnti1) as [_ Hlt]. *)
        (*              rewrite gssThreadRes in Hlt. *)
        (*              now eauto. *)
        (*              pose proof ((thread_data_lock_coh _ Hinv' _ cnti1).1 _ cntj') as Hcoh. *)
        (*              rewrite gssThreadRes in Hcoh. *)
        (*              intros b ofs. *)
        (*              erewrite getCurPerm_correct. *)
        (*              rewrite restrPermMap_Cur. *)
        (*              erewrite @gsoThreadRes with (cntj:= ctn) in Hcoh by eauto. *)
        (*              specialize (Hcoh b ofs). *)
        (*              now auto. *)
        (*           ** pose proof ((thread_data_lock_coh _ Hinv' _ cnti1).1 _ cntj0') as Hcoh. *)
        (*              erewrite @gsoThreadRes with (cntj := cntj000) in * by eauto. *)
        (*              erewrite <- @gsoThreadRes with (cntj' := cntj0') in * by eauto. *)
        (*              rewrite gssThreadRes in Hcoh. *)
        (*              assumption. *)
        (*       + intros laddr rmap Hres. *)
        (*         erewrite! gsoThreadLPool in Hres. *)
        (*         erewrite <- @gsoThreadLPool with (c := c) (p := pmap) (cnti := cnti) in Hres. *)
        (*         pose proof ((thread_data_lock_coh _ Hinv' _ cnti1).2 _ _ Hres) as Hcoh. *)
        (*         rewrite gssThreadRes in Hcoh. *)
        (*         assumption. *)
        (*     - split. *)
        (*       + intros j0 cntj0. *)
        (*         destruct (j0 == i) eqn:Hij0; move/eqP:Hij0=>Hij0; subst. *)
        (*         * rewrite gssThreadRes. *)
        (*           pose proof (cntUpdate' _ _ cnti' cnti0) as cnti00. *)
        (*           pose proof (cntUpdate' _ _ ctn cnti00) as cnti000. *)
        (*           pose proof (cntUpdate c pmap cnti cnti000) as cnti0'. *)
        (*           erewrite @gsoThreadRes with (cntj := cnti00) by eauto. *)
        (*           destruct (j == i0) eqn:Hji0; move/eqP:Hji0=>Hji0; subst. *)
        (*           ** rewrite gssThreadRes. *)
        (*              inversion Hperm; subst. *)
        (*              simpl (add_block) in *. *)
        (*              unfold HybridMachine.DryHybridMachine.add_block in *. *)
        (*              pose proof ((thread_data_lock_coh _ Hinv' _ cntj').1 _ cnti1) as Hcoh. *)
        (*              rewrite gssThreadRes in Hcoh. *)
        (*              erewrite @gsoThreadRes with (cntj := ctn) in Hcoh by eauto. *)
        (*              now eauto. *)
        (*           ** erewrite @gsoThreadRes with (cntj := cnti000) by eauto. *)
        (*              erewrite <- @gsoThreadRes with (cntj' := cnti0') by eauto. *)
        (*              pose proof ((thread_data_lock_coh _ Hinv' _ cnti0').1 _ cnti1) as Hcoh. *)
        (*              rewrite gssThreadRes in Hcoh. *)
        (*              now auto. *)
        (*         * pose proof (cntUpdate' _ _ cnti' cnti0) as cnti00. *)
        (*           pose proof (cntUpdate' _ _ cnti' cntj0) as cntj00. *)
        (*           erewrite @gsoThreadRes with (cntj := cntj00) by eauto. *)
        (*           erewrite @gsoThreadRes with (cntj := cnti00) by eauto. *)
        (*           now apply ((thread_data_lock_coh _ Hinv'0 _ cnti00).1 _ cntj00). *)
        (*       + intros laddr rmap Hres. *)
        (*         pose proof (cntUpdate' _ _ cnti' cnti0) as cnti00. *)
        (*         erewrite @gsoThreadRes with (cntj := cnti00) by eauto. *)
        (*         rewrite gsoThreadLPool in Hres. *)
        (*         now apply ((thread_data_lock_coh _ Hinv'0 _ cnti00).2 _ _ Hres). *)
        (*   } *)
        (*   { intros. *)
        (*     rewrite gsoThreadLPool in Hres. *)
        (*     pose proof (cntUpdate c pmap cnti cnti) as cnti1. *)
        (*     split. *)
        (*     - intros j0 cntj0. *)
        (*       destruct (j0 == i) eqn:Hij0; move/eqP:Hij0=>Hij0; subst. *)
        (*       * rewrite gssThreadRes. *)
        (*         rewrite gsoThreadLPool in Hres. *)
        (*         erewrite <- @gsoThreadLPool with (c := c) (p := pmap) (cnti := cnti) in Hres. *)
        (*         pose proof ((locks_data_lock_coh _ Hinv' _ _ Hres).1 _ cnti1) as Hcoh. *)
        (*         rewrite gssThreadRes in Hcoh. *)
        (*         assumption. *)
        (*       * pose proof (cntUpdate' _ _ cnti' cntj0) as cntj00. *)
        (*         pose proof ((locks_data_lock_coh _ Hinv'0 _ _ Hres).1 _ cntj00) as Hcoh. *)
        (*         erewrite @gsoThreadRes with (cntj := cntj00) by eauto. *)
        (*         assumption. *)
        (*     - intros laddr' rmap' Hres'. *)
        (*       rewrite gsoThreadLPool in Hres'. *)
        (*       now eapply ((locks_data_lock_coh _ Hinv'0 _ _ Hres).2 _ _ Hres'). *)
        (*   } *)
        (*   { simpl. *)
        (*     unfold OrdinalPool.lr_valid. *)
        (*     intros. *)
        (*     rewrite! OrdinalPool.gsoThreadLPool. *)
        (*     destruct Hinv. *)
        (*     specialize (lockRes_valid0 b ofs). *)
        (*     simpl in lockRes_valid0. *)
        (*     destruct (OrdinalPool.lockRes tp (b,ofs)); *)
        (*       now auto. *)
        (*   } *)
          Unshelve. auto.
    Qed.


    Lemma updThread_internal_execution:
      forall tp tp' m m' i j xs c pmap
        (cnti: containsThread tp i)
        (cnti': containsThread tp' i)
        (Hinv: invariant (updThread cnti c pmap))
        (Hcomp' : mem_compatible (updThread cnti c pmap) m)
        (Hneq: i <> j)
        (Hexec: internal_execution [seq x <- xs | x == j] tp m tp' m'),
        internal_execution [seq x <- xs | x == j] (updThread cnti c pmap) m
                           (updThread cnti' c pmap) m'.
    Proof.
      intros.
      generalize dependent m.
      generalize dependent tp.
      induction xs; intros.
      - inversion Hexec; subst;
        first by constructor.
        simpl in HschedN;
          by discriminate.
      - destruct (a == j) eqn:Heq; move/eqP:Heq=>Heq.
        + subst a.
          simpl in Hexec.
          erewrite if_true in Hexec by eauto.
          inversion Hexec; subst.
          simpl in HschedN. inversion HschedN; subst tid.
          assert (cntj' := cntUpdate c pmap cnti cnt).
          assert (cnti0' := containsThread_internal_step Hstep cnti).
          eapply updThread_internal_step
        with (cntj' := cntj') (cnti' := cnti0') (Hcomp' := Hcomp') in Hstep; eauto.
        specialize (IHxs tp'0 _
                         ltac:(eapply internal_step_invariant; eauto)
                                m'0
                                ltac:(eapply (internal_step_compatible);
                                      eauto) Htrans).
        simpl in Htrans.
        simpl in *. erewrite if_true by eauto.
        econstructor;
          by eauto.
        + simpl ([seq x <- a :: xs | x == j]) in *.
          erewrite if_false in * by (now apply/eqP).
          eapply IHxs; eauto.
    Qed.

    Lemma addThread_internal_step:
      forall tp tp' m m' i vf arg pmap
        (cnti: containsThread tp i)
        (cnti': containsThread (addThread tp vf arg pmap) i)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible (addThread tp vf arg pmap) m)
        (Hinv': invariant (addThread tp vf arg pmap))
        (Hstep: internal_step cnti Hcomp tp' m'),
        internal_step cnti' Hcomp' (addThread tp' vf arg pmap) m'.
    Proof.
      intros.
      destruct Hstep as [[? Htstep] | [Hresume | Hinit]].
      - inversion Htstep; subst tp'0 m'0.
        left.
        exists x.
        eapply @step_dry with (c := c) (c' := c'); eauto.
        erewrite gsoAddCode with (cntj := cnti); eauto.
        subst.
        erewrite restrPermMap_irr' with (Hlt' := ((compat_th _ _ Hcomp) cnti).1); eauto.
        erewrite gsoAddRes with (cntj := cnti); eauto.
        subst.
        erewrite @gsoAddRes with (cntj := cnti) by eauto.
          by rewrite add_update_comm.
      - destruct Hresume as [Hresume ?]; subst.
        inversion Hresume; subst.
        right; left.
        split; auto.
        econstructor; eauto.
        simpl in *. unfold HybridMachine.DryHybridMachine.install_perm in *.
        erewrite restrPermMap_irr with (m2 := m') (P2 := (Hcmpt _ ctn).1); eauto.
        simpl.
        erewrite OrdinalPool.gsoAddRes;
          now eauto.
        erewrite gsoAddCode with (cntj := ctn); eauto.
          by rewrite add_updateC_comm.
      - destruct Hinit; subst.
        right; right.
        eapply @StartThread with (Hcmpt := Hcomp'); eauto.
        erewrite gsoAddCode; eauto.
        simpl in *.
        unfold HybridMachine.DryHybridMachine.install_perm in *. subst.
        eapply restrPermMap_irr'.
        simpl.
        erewrite @OrdinalPool.gsoAddRes; now eauto.
        rewrite add_update_comm.
        simpl (add_block).
        unfold HybridMachine.DryHybridMachine.add_block.
        erewrite <- @gsoAddRes with (cntj' := cnti') (cntj := ctn).
        reflexivity.


        (* Lemma mem_compatible_addThread: *)
        (*   forall tp pmap vf arg m *)
        (*     (Hcomp_pmap: permMapLt pmap.1 (getMaxPerm m) /\ permMapLt pmap.2 (getMaxPerm m)) *)
        (*     (Hcomp: mem_compatible tp m), *)
        (*     mem_compatible (addThread tp vf arg pmap) m. *)
        (* Proof. *)
        (*   intros. *)
        (*   destruct Hcomp. *)
        (*   econstructor; intros; eauto. *)
        (*   - destruct (cntAdd' _ _ _ cnt) as[[cnt0 ?] | cntLatest]. *)
        (*     + erewrite @gsoAddRes with (cntj := cnt0) by eauto. *)
        (*       now eauto. *)
        (*     + subst. *)
        (*       erewrite gssAddRes by eauto. *)
        (*       now eauto. *)
        (*   - rewrite gsoAddLPool in H. *)
        (*     now eauto. *)
        (* Qed. *)
        (* (** new state is [mem_compatible] *) *)
        (* eapply mem_compatible_addThread; *)
        (*   eauto. *)
        (* eapply initial_core_decay in Hinitial. *)
        (* eapply mem_compatible *)
        (*        admit. *)
        (* admit. *)
        Unshelve.
        assumption.
    Qed.


    Lemma addThread_internal_execution:
      forall tp tp' m m' i j xs vf arg pmap
        (Hneq: i <> j)
        (Hinv': invariant (addThread tp vf arg pmap))
        (Hcomp': mem_compatible (addThread tp vf arg pmap) m)
        (Hexec: internal_execution [seq x <- xs | x == j] tp m tp' m'),
        internal_execution [seq x <- xs | x == j]
                           (addThread tp vf arg pmap) m
                           (addThread tp' vf arg pmap) m'.
    Proof.
      intros.
      generalize dependent m.
      generalize dependent tp.
      induction xs; intros.
      - simpl in *.
        inversion Hexec; subst;
        first by constructor.
        simpl in HschedN;
          by discriminate.
      - simpl in *.
        destruct (a == j) eqn:Heq; move/eqP:Heq=>Heq.
        subst a.
        inversion Hexec; subst.
        simpl in HschedN. inversion HschedN; subst tid.
        assert (cnt':= cntAdd vf arg pmap cnt).
        eapply addThread_internal_step
        with (cnti' := cnt') (Hcomp' := Hcomp') in Hstep; eauto.
        specialize (IHxs tp'0
                         ltac:(eapply internal_step_invariant; eauto)
                                m'0
                                ltac:(eapply (internal_step_compatible);
                                       eauto) Htrans).
        econstructor;
          by eauto.
        eauto.
    Qed.

    Lemma remLock_internal_step:
      forall tp tp' m m' j (cntj: containsThread tp j) b ofs
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible (remLockSet tp (b,ofs)) m)
        (cntj': containsThread (remLockSet tp (b,ofs)) j)
        (Hstep: internal_step cntj Hcomp tp' m'),
        internal_step cntj' Hcomp' (remLockSet tp' (b,ofs)) m'.
    Proof.
      intros.
      inversion Hstep as [[? ?] | [[? ?] | ?]].
      - inversion H; subst.
        left.
        exists x.
        eapply @step_dry with (c := c) (c' := c'); eauto.
        eapply ThreadPoolWF.remLock_inv; eauto.
        rewrite gRemLockSetCode.
        auto.
        erewrite <- restrPermMap_irr' with
        (Hlt' := ((compat_th _ _ Hcomp') cntj').1) (Hlt := ((compat_th _ _ Hcomp) cntj).1);
          eauto.
        rewrite gRemLockSetRes; auto.
        rewrite gRemLockSetRes; auto.
      - subst.
        inversion H; subst.
        right. left.
        split; auto.
        econstructor; eauto.
        simpl in *. unfold HybridMachine.DryHybridMachine.install_perm in *.
        erewrite restrPermMap_irr with (m2 := m') (P2 := (Hcmpt _ ctn).1); eauto.
        simpl.
        erewrite OrdinalPool.gRemLockSetRes;
          now eauto.
        rewrite gRemLockSetCode; auto.
        eapply ThreadPoolWF.remLock_inv; eauto.
      - subst.
        inversion H; subst.
        do 2 right.
        eapply @StartThread with (Hcmpt := Hcomp'); eauto.
        rewrite gRemLockSetCode; auto.
        simpl in *.
        unfold HybridMachine.DryHybridMachine.install_perm in *. subst.
        eapply restrPermMap_irr'.
        simpl.
        erewrite @OrdinalPool.gRemLockSetRes; now eauto.
        eapply ThreadPoolWF.remLock_inv; eauto.
        erewrite @remLock_updThread_comm with (cnti' := cntj').
        simpl (add_block). unfold HybridMachine.DryHybridMachine.add_block.
        erewrite <- @gRemLockSetRes with (cnti' := cntj') (cnti := ctn).
        reflexivity.
        Unshelve.
        assumption.
    Qed.

    Lemma remLock_internal_execution:
      forall tp tp' m m' j xs b ofs
        (Hcomp': mem_compatible (remLockSet tp (b,ofs)) m)
        (Hexec: internal_execution [seq x <- xs | x == j] tp m tp' m'),
        internal_execution [seq x <- xs | x == j] (remLockSet tp (b, ofs)) m
                           (remLockSet tp' (b,ofs)) m'.
    Proof.
      intros.
      generalize dependent m.
      generalize dependent tp.
      induction xs; intros.
      - simpl in *.
        inversion Hexec; subst;
        first by constructor.
        simpl in HschedN;
          by discriminate.
      - simpl in *.
        destruct (a == j) eqn:Heq; move/eqP:Heq=>Heq.
        subst a.
        inversion Hexec; subst.
        simpl in HschedN. inversion HschedN; subst tid.
        assert (cntj' := cntRemoveL (b, ofs) cnt).
        eapply remLock_internal_step
        with (cntj' := cntj') (Hcomp' := Hcomp') in Hstep; eauto.
        specialize (IHxs tp'0 _
                         ltac:(eapply (internal_step_compatible);
                                eauto) Htrans).
        econstructor;
          by eauto.
        eauto.
    Qed.

    Lemma internal_step_nextblock:
      forall tp m tp' m' i (cnti: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step cnti Hcomp tp' m'),
        (Mem.nextblock m <= Mem.nextblock m')%positive.
    Proof.
      intros.
      destruct Hstep as [[? H] | [[? ?] | ?]]; subst.
      inversion H; subst.
      eapply ev_step_nextblock in Hcorestep;
        by rewrite restrPermMap_nextblock in Hcorestep.
      apply Pos.le_refl.
      inversion H. subst.
      inversion Hperm; subst.
      eapply initial_core_nextblock in Hinitial;
        eauto.
    Qed.

    Lemma internal_execution_nextblock:
      forall tp m tp' m' xs
        (Hexec: internal_execution xs tp m tp' m'),
        (Mem.nextblock m <= Mem.nextblock m')%positive.
    Proof.
      intros.
      generalize dependent m.
      generalize dependent tp.
      induction xs; intros; inversion Hexec; subst;
      first by apply Pos.le_refl.
      simpl in HschedN. discriminate.
      simpl in *.
      inversion HschedN; subst.
      specialize (IHxs _ _ Htrans).
      eapply Pos.le_trans.
      eapply internal_step_nextblock; eauto.
      eauto.
    Qed.

    End InternalSteps.

    Arguments internal_step {Sem} {tid} {tp} {m}.
    Arguments internal_execution {Sem} ge.
    
End InternalSteps.

  (** ** Type of steps the concurrent machine supports *)
  (*Note: Internal and External steps were introduced in the
  HybridMachine after this development. However, this is not exactly
  the same, as it treats resume and start steps as internal as
  well. Basically anything that may not pop the schedule *)
Module StepType.

  Import ThreadPoolWF CoreLanguageDry ThreadPool
         event_semantics HybridMachine DryHybridMachine HybridMachineSig InternalSteps.
  (** Distinguishing the various step types of the concurrent machine *)
  
  Section StepType.
    Context {Sem : Semantics}
            {Sch: Scheduler}.

    Existing Instance dryResources.
    Existing Instance OrdinalPool.OrdinalThreadPool.
    Existing Instance DryHybridMachineSig.
  
  Inductive StepType : Type :=
    Internal | Concurrent | Suspend.

  Definition ctlType (code : @threadPool.ctl semC) (m : Mem.mem) (st : StepType) : Prop :=
    match code with
    | Kinit _ _ => st = Internal
    | Krun c =>
      match at_external semSem c m with
      | None => (* ((exists i, halted semSem c i) /\ st = Halted) \/ *)
                st = Internal
      | Some _ => st = Suspend
      end
    | Kblocked c => st = Concurrent
    | Kresume c _ => st = Internal
    end.

  Definition getStepType {i tp} (cnt : containsThread tp i) m st :=
    ctlType (getThreadC cnt) m st.

  Notation "cnt '$' m '@'  'I'" := (getStepType cnt m Internal) (at level 80).
  Notation "cnt '$' m '@'  'E'" := (getStepType cnt m Concurrent) (at level 80).
  Notation "cnt '$' m '@'  'S'" := (getStepType cnt m Suspend) (at level 80).
  (* Notation "cnt '$' m '@'  'H'" := (getStepType cnt m Halted) (at level 80). *)

  Lemma internal_step_type :
    forall  i tp tp' m m' (cnt : containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (Hstep_internal: internal_step cnt Hcomp tp' m'),
      let mrestr := restrPermMap (((compat_th _ _ Hcomp) cnt).1) in
      cnt$mrestr @ I.
  Proof.
    intros.
    unfold getStepType, ctlType.
    destruct Hstep_internal as [[? Hcstep] | [[Hresume Heq] | [Hstart Heq]]].
    inversion Hcstep. subst. rewrite Hcode.
    apply ev_step_ax1 in Hcorestep.
    assert (H1:= corestep_not_at_external semSem _ _ _ _ Hcorestep).
    rewrite H1.
    reflexivity.
    inversion Hresume; subst.
    Tactics.pf_cleanup;
      by rewrite Hcode.
    inversion Hstart; subst.
    Tactics.pf_cleanup;
      by rewrite Hcode.
  Qed.

  Lemma internal_step_result_type:
    forall tp m tp' m' i (cnti: containsThread tp i)
      (cnti': containsThread tp' i)
      (Hcomp: mem_compatible tp m)
      (Hcomp': mem_compatible tp' m')
      (Hinternal: internal_step cnti Hcomp tp' m'),
      let mrestr := restrPermMap (((compat_th _ _ Hcomp') cnti').1) in
      ~ (cnti'$mrestr @ E).
  Proof.
    intros. intro Hcontra.
    destruct Hinternal as [[? Htstep] | [[Htstep ?] | Htstep]]; subst;
    inversion Htstep; subst;
    unfold getStepType in Hcontra;
    try rewrite gssThreadCode in Hcontra;
    try rewrite gssThreadCC in Hcontra; unfold ctlType in Hcontra;
    repeat destruct (at_external _ _ _); try discriminate;
    destruct Hcontra as [? ?]; discriminate.
  Qed.

  Lemma internal_execution_result_type:
    forall tp m tp' m' i xs
      (cnti': containsThread tp' i)
      (Hin: List.In i xs)
      (Hcomp': mem_compatible tp' m')
      (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m'),
      let mrestr := restrPermMap (((compat_th _ _ Hcomp') cnti').1) in
      ~ (cnti'$mrestr @ E).
  Proof.
    intros.
    generalize dependent m.
    generalize dependent tp.
    induction xs; intros.
    - simpl in *.
      inversion Hexec; subst.
      by exfalso.
      simpl in HschedN;
        by discriminate.
    - destruct (a == i) eqn:Hia; move/eqP:Hia=>Hia.
      subst a.
      simpl in *.
      erewrite if_true in Hexec by apply eq_refl.
      inversion Hexec; subst.
      simpl in HschedN. inversion HschedN; subst tid.
      simpl in Htrans.
      destruct (List.In_dec (eq_dec.nat_eq_dec) i xs).
      eauto.
      rewrite not_in_filter in Htrans; auto.
      inversion Htrans; subst.
      eapply internal_step_result_type; eauto.
      simpl in HschedN0; discriminate.
      destruct Hin; first by (exfalso; auto).
      simpl in Hexec.
      erewrite if_false in Hexec.
      eauto.
      move/eqP:Hia; auto.
  Qed.

  (** ** Proofs about [AsmContext.dryFineMach]*)

  Section FineMachineInternal.
    Context {initU : seq nat}
            {semAx: CoreLanguage.SemAxioms}
            {dilMem: DiluteMem}.
    
  Notation fmachine_step := ((corestep (AsmContext.fine_semantics initU))).

  (*TODO: maybe move to tactics *)
  (** Solves absurd cases from fine-grained internal steps *)
  Ltac absurd_internal Hstep :=
    inversion Hstep; try inversion Htstep; subst; Tactics.pf_cleanup; simpl in *;
    try match goal with
        | [H: Some _ = Some _ |- _] => inversion H; subst
        end; Tactics.pf_cleanup;
    repeat match goal with
           | [H: getThreadC ?Pf = _, Hint: ?Pf$_ @ I |- _] =>
             unfold getStepType in Hint; simpl in *;
               rewrite H in Hint; simpl in Hint
           | [H1: match ?Expr with _ => _ end = _,
                  H2: ?Expr = _ |- _] => rewrite H2 in H1
           end; try discriminate; try (exfalso; by auto).

  Opaque getThreadC updThreadC containsThread updThread updLockSet addThread remLockSet getThreadR lockSet.
  
  Lemma fstep_containsThread' :
    forall tp tp' m m' i j U tr tr'
      (cnti: containsThread tp i)
      (cntj: containsThread tp' j)
      (Hcomp: mem_compatible tp m),
      let mrestr := restrPermMap (((compat_th _ _ Hcomp) cnti).1) in
      forall
        (Hinternal: cnti$mrestr @ I)
        (Hstep: fmachine_step (i :: U, tr, tp) m (U, tr', tp') m'),
        containsThread tp j.
  Proof.
    intros; absurd_internal Hstep;
      by eauto.
  Qed.

  Lemma fmachine_step_invariant:
    forall (tp tp' : t) m m' (i : nat) (pf : containsThread tp i) U tr tr'
      (Hcomp: mem_compatible tp m),
      let mrestr := restrPermMap (((compat_th _ _ Hcomp) pf).1) in
      forall (Hinternal: pf$mrestr @ I)
        (Hstep: fmachine_step (i :: U, tr, tp) m (U, tr', tp') m'),
        invariant tp'.
  Proof.
    intros.
    absurd_internal Hstep.
    - inversion Hperm; subst.
      unfold DryHybridMachine.add_block.
      eapply initial_core_invariant; simpl; eauto.
      eapply Hinitial.
    - apply updThreadC_invariant; auto.
    - eapply ev_step_ax1 in Hcorestep.
      eapply corestep_invariant; simpl; eauto.
    - now apply updThreadC_invariant.
  Qed.

  Lemma fmachine_step_compatible:
    forall (tp tp' : t) m m' (i : nat) (pf : containsThread tp i) U tr tr'
      (Hcomp: mem_compatible tp m),
      let mrestr := restrPermMap (((compat_th _ _ Hcomp) pf).1) in
      forall (Hinternal: pf$mrestr @ I)
        (Hstep: fmachine_step (i :: U,tr, tp) m (U, tr',tp') m'),
        mem_compatible tp' m'.
  Proof.
    intros.
    absurd_internal Hstep; auto;
      try (eapply StepLemmas.updThreadC_compatible;
             by eauto).
    inversion Hperm; subst.
    eapply start_compatible in Htstep; eauto.
    eapply StepLemmas.mem_compatible_setMaxPerm; eauto.
    destruct (at_external semSem c mrestr) eqn:?; try discriminate.
    eapply StepLemmas.mem_compatible_setMaxPerm; eauto.
    eapply corestep_compatible;simpl;
      now eauto.
  Qed.
  
  Lemma gsoThreadC_fstepI:
    forall tp tp' m m' i j U tr tr'
      (pfj: containsThread tp j)
      (pfj': containsThread tp' j)
      (pfi: containsThread tp i)
      (Hcomp: mem_compatible tp m),
      let mrestr := restrPermMap (((compat_th _ _ Hcomp) pfi).1) in
      forall (Hinternal: pfi$mrestr @ I)
        (Hstep: fmachine_step (i :: U, tr, tp) m (U, tr', tp') m')
        (Hneq: i <> j),
      getThreadC pfj = getThreadC pfj'.
  Proof.
    intros.
    absurd_internal Hstep;
      try (erewrite gsoThreadCC with (cntj' := pfj');
            by eauto);
     try (erewrite gsoThreadCode with (cntj := pfj);
            by eauto);
     try reflexivity.
  Qed.

  Lemma gsoLockSet_fstepI:
    forall tp tp' m m' i U tr tr'
      (pfi: containsThread tp i)
      (Hcomp: mem_compatible tp m),
      let mrestr := restrPermMap (((compat_th _ _ Hcomp) pfi).1) in
      forall (Hinternal: pfi$mrestr @ I)
        (Hstep: fmachine_step (i :: U, tr, tp) m (U, tr', tp') m'),
        lockSet tp = lockSet tp'.
  Proof.
    intros.
    absurd_internal Hstep;
      try (apply initial_core_nomem in Hinitial; subst om; simpl machine_semantics.option_proj);
      try (erewrite gsoThreadCLock;
             by eauto);
    try (erewrite gsoThreadLock;
           by eauto).
  Qed.

  Opaque lockRes.
  Lemma gsoLockRes_fstepI :
    forall tp tp' (m m' : mem) i tr tr'
      U (pfi : containsThread tp i)
      (Hcomp: mem_compatible tp m),
      let mrestr := restrPermMap (((compat_th _ _ Hcomp) pfi).1) in
      forall (Hinternal: pfi$mrestr @ I)
      (Hstep: fmachine_step (i :: U,tr, tp) m (U, tr', tp') m'),
      lockRes tp' = lockRes tp.
  Proof.
    intros.
    absurd_internal Hstep;
      try (apply initial_core_nomem in Hinitial; subst om; simpl machine_semantics.option_proj);
     extensionality addr;
      try (by rewrite gsoThreadCLPool);
      try (by rewrite gsoThreadLPool).
  Qed.

  Lemma fmachine_step_disjoint_val :
    forall tp tp' m m' i j U tr tr'
      (Hneq: i <> j)
      (pfi: containsThread tp i)
      (pfj: containsThread tp j)
      (pfj': containsThread tp' j)
      (Hcomp: mem_compatible tp m)
      (Hcomp': mem_compatible tp' m'),
      let mrestr := restrPermMap (((compat_th _ _ Hcomp) pfi).1) in
      forall (Hinternal: pfi$mrestr @ I)
        (Hstep: fmachine_step (i :: U, tr, tp) m (U,tr', tp') m') b ofs
        (Hreadable:
           Mem.perm (restrPermMap (Hcomp _ pfj).1) b ofs Cur Readable \/
           Mem.perm (restrPermMap (Hcomp _ pfj).2) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    absurd_internal Hstep;
      try reflexivity.
    inversion Hperm; subst.
    eapply initial_core_disjoint_val; eauto.
    eapply Hreadable.
    apply ev_step_ax1 in Hcorestep;
      eapply corestep_disjoint_val;
        by (simpl; eauto).
  Qed.
  
  Lemma fstep_valid_block:
    forall tpf tpf' mf mf' i U b tr tr'
      (Hvalid: Mem.valid_block mf b)
      (Hstep: fmachine_step (i :: U, tr, tpf) mf (U, tr',tpf') mf'),
      Mem.valid_block mf' b.
  Proof.
    intros.
    inversion Hstep; clear Hstep; subst; auto.
    inversion Htstep; clear Htstep; subst.
    eauto.
    erewrite diluteMem_valid.
    eapply CoreLanguage.initial_core_validblock; eauto.
    inversion Hperm; subst.
    erewrite restrPermMap_valid;
      now eauto.
    erewrite diluteMem_valid.
    inversion Htstep; subst; eauto.
    eapply CoreLanguage.ev_step_validblock; eauto.
    simpl in *. inversion HschedN; clear HschedN; subst. clear HschedS.
    inversion Htstep; subst;
      eauto;
    eapply Mem.store_valid_block_1; eauto.
  Qed.
  End FineMachineInternal.

  Hint Resolve fmachine_step_compatible fmachine_step_invariant
       StepLemmas.step_containsThread fstep_containsThread' gsoLockSet_fstepI : fstep.

  (* Hint Rewrite gsoThreadR_step permission_at_step : fstep. *)
  
  End StepType.



End StepType.
