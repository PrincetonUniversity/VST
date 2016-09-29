(** * DryConc to FineConc simulation*)

Require Import compcert.lib.Axioms.

Add LoadPath "../concurrency" as concurrency.

Require Import concurrency.sepcomp.
Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

Require Import Coq.Program.Program.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import concurrency.addressFiniteMap.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Notation CREATE_SIG := (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint)).
Notation CREATE := (EF_external 2%positive CREATE_SIG).

Notation MKLOCK := 
  (EF_external 5%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).
Notation FREE_LOCK := 
  (EF_external 6%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).

Notation LOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).
Notation LOCK := (EF_external 7%positive LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).
Notation UNLOCK := (EF_external 8%positive UNLOCK_SIG).

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.scheduler.
Require Import concurrency.concurrent_machine.
Require Import concurrency.dry_machine_lemmas concurrency.dry_context.
Require Import concurrency.memory_lemmas.
Require Import concurrency.mem_obs_eq.

Module SimDefs (SEM: Semantics)
       (SemAxioms: SemanticsAxioms SEM)
       (Machine: MachinesSig with Module SEM := SEM)
       (AsmContext: AsmContext SEM Machine)
       (CI: CoreInjections SEM).

  (* Step Imports*)
  Module StepType := StepType SEM SemAxioms Machine AsmContext.
  Import StepType StepType.InternalSteps.

  (* Memory Imports*)
  Import MemObsEq ValObsEq MemoryLemmas.
  Import CI ValueWD MemoryWD Renamings.

  (* Machine and Context Imports*)
  Import Machine DryMachine ThreadPool AsmContext dry_machine.Concur.mySchedule.
  Module ThreadPoolInjections := ThreadPoolInjections SEM Machine CI.
  Import ThreadPoolInjections.
  
  Notation threadStep := (threadStep the_ge).
  Notation Sch := schedule.
  Notation cmachine_step := ((corestep coarse_semantics) the_ge).
  Notation fmachine_step := ((corestep fine_semantics) the_ge).
  Notation CoarseSem := coarse_semantics.
  Hint Unfold DryConc.MachStep FineConc.MachStep.

  (** *** Simulations between individual threads. *)
  
  (* Consider hiding thread_pool completely *)
  (** The weak simulation is required to prove the correctness of
  concurrent calls. In particular, suppose that a thread executes an
  external call, this thread will be "synchronized" meaning that its
  permissions will be equal between the two machines. When the angel
  provides a new permission map for this thread we still need to show
  that it is compatible with the other threads, hence we need to know
  something about those threads as well. The fact that the permissions
  of the coarse grained machine are above the ones on the fine is
  enough to establish non-interference for the fine grained machine *)
  Record weak_tsim {tpc tpf : thread_pool} (mc mf : Mem.mem)
             {i} (f: memren) (pfc : containsThread tpc i)
             (pff : containsThread tpf i) (compc: mem_compatible tpc mc)
             (compf: mem_compatible tpf mf) : Prop :=
    { weak_tsim_data:
        weak_mem_obs_eq f (restrPermMap (fst (compc i pfc)))
                        (restrPermMap (proj1 (compf i pff)));
      weak_tsim_locks:
        weak_mem_obs_eq f (restrPermMap (snd (compc i pfc)))
                        (restrPermMap (snd (compf i pff)))}.
  
  Record strong_tsim {tpc tpf : thread_pool} (mc mf : Mem.mem) {i}
         (f: memren) (pfc : containsThread tpc i)
         (pff : containsThread tpf i) (compc: mem_compatible tpc mc)
         (compf: mem_compatible tpf mf) : Prop :=
    { code_eq: ctl_inj f (getThreadC pfc) (getThreadC pff);
      obs_eq_data: mem_obs_eq f (restrPermMap ((fst (compc i pfc))))
                         (restrPermMap (fst (compf i pff)));
      obs_eq_locks: mem_obs_eq f (restrPermMap ((snd (compc i pfc))))
                         (restrPermMap (snd (compf i pff)));                              
    }.

  (** *** Simulation between the two machines *)
  

  (* simStrong now maintains the extra invariant that any new blocks
      from the internal execution are owned by thread tid. This is
     needed for the suspend_sim proof. Note that it's not possible
     to prove it just by the fact that only thread tid executes because
     1. some location may be allocated and then freed in this multistep
      execution and 2. our relation only strongly relates the final state
      of the execution not in-between states. *)

  Definition fpool tpc : Type :=
    forall i (cnti: containsThread tpc i), memren.

  Definition max_inv mf := forall b ofs, Mem.valid_block mf b ->
                                    permission_at mf b ofs Max = Some Freeable.
  (** Simulation relation between DryConc and FineConc:
- The two machines have exactly the same threads.
- The state of the DryConc machine is compatible with it's memory.
- The same for FineConc.
- The DryConc machine is safe for all schedules
- There is a weak simulation ([weak_tsim]) between threads with the same id in the two machines
- Blocks that are not yet committed (in the sense that the global renaming [f : memren] does not map these blocks) are mapped in different blocks by distinct thread renamings.
- Every thread in the DryConc machine can be stepped as mandated by the delta [xs] until the DryConc machine reaches a state for which this thread is in [strong_tsim] between the two machines.
- Lock resources are related by the global renaming and the two machines have equivalent [lockRes] for mapped blocks
- The [invariant] holds for the FineConc machine
- The [Max] permissions on the memory of the FineConc machine are always set to [Freeable]
- The state, memory, and genv of DryConc are well-formed (no dangling pointers)
- the delta list [xs] contains only valid thread ids. *)
  
  Record sim tpc mc tpf mf (xs : Sch) (f fg: memren) (fp: fpool tpc) fuelF : Prop :=
    { numThreads : forall i, containsThread tpc i <-> containsThread tpf i;
      mem_compc: mem_compatible tpc mc;
      mem_compf: mem_compatible tpf mf;
      safeCoarse: forall sched,
          DryConc.csafe the_ge (sched,[::],tpc) mc (fuelF + size xs);
      simWeak:
        forall tid
          (pfc: containsThread tpc tid)
          (pff: containsThread tpf tid),
          weak_tsim f pfc pff mem_compc mem_compf;
      fpSeperate: forall i j
                    (cnti: containsThread tpc i)
                    (cntj: containsThread tpc j)
                    (Hij: i <> j) b b' b2 b2'
                    (Hfb: f b = None)
                    (Hfb': f b' = None)
                    (Hfib: (fp _ cnti) b = Some b2)
                    (Hfjb': (fp _ cntj) b' = Some b2'),
          b2 <> b2';
      simStrong:
        forall tid (pfc: containsThread tpc tid) (pff: containsThread tpf tid),
        exists tpc' mc', ren_incr f (fp _ pfc) /\
                    ([seq x <- xs | x == tid] = nil -> f = (fp _ pfc)) /\
                    internal_execution the_ge ([seq x <- xs | x == tid])
                                       tpc mc tpc' mc' /\
                    (forall (pfc': containsThread tpc' tid)
                       (mem_compc': mem_compatible tpc' mc'),
                        strong_tsim (fp _ pfc) pfc' pff mem_compc' mem_compf) /\
                    (forall tid2 (pff2: containsThread tpf tid2)
                       (Hneq: tid <> tid2) b1 b2 ofs,
                        (fp _ pfc) b1 = Some b2 ->
                        f b1 = None ->
                        (getThreadR pff2).1 # b2 ofs = None /\ (getThreadR pff2).2 # b2 ofs = None) /\
                    (forall bl ofsl rmap b1 b2 ofs,
                        (fp _ pfc) b1 = Some b2 ->
                        f b1 = None ->
                        lockRes tpf (bl,ofsl) = Some rmap -> 
                        rmap.1 # b2 ofs = None /\ rmap.2 # b2 ofs = None);
      simLockRes: (forall bl1 bl2 ofs rmap1 rmap2
                    (Hf: f bl1 = Some bl2)
                    (Hl1: lockRes tpc (bl1,ofs) = Some rmap1)
                    (Hl2: lockRes tpf (bl2,ofs) = Some rmap2),
                      strong_mem_obs_eq f (restrPermMap (fst ((compat_lp mem_compc) _ _ Hl1)))
                                        (restrPermMap (fst ((compat_lp mem_compf) _ _ Hl2))) /\
                      strong_mem_obs_eq f (restrPermMap (snd ((compat_lp mem_compc) _ _ Hl1)))
                                        (restrPermMap (snd ((compat_lp mem_compf) _ _ Hl2)))) /\
                  (forall bl2 ofs,
                    lockRes tpf (bl2, ofs) ->
                    exists bl1, f bl1 = Some bl2) /\
                  (forall bl1 bl2 ofs,
                      f bl1 = Some bl2 ->
                      lockRes tpc (bl1, ofs) <-> lockRes tpf (bl2, ofs));
      invF: invariant tpf;
      maxF: max_inv mf;
      memc_wd: valid_mem mc;
      tpc_wd: tp_wd f tpc;
      thege_wd: ge_wd fg the_ge;
      fg_spec: ren_incr fg f /\ forall b b', fg b = Some b' -> b = b';
      xs_wd: forall i, List.In i xs -> containsThread tpc i
    }.

  Arguments sim : clear implicits.

  (** *** Simulations Diagrams *)
  
  Definition sim_internal_def :=
    forall (tpc tpf : thread_pool) (mc mf : Mem.mem) tr fuelF
      (xs : Sch) (f fg : memren) (fp : fpool tpc) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hinternal: pff @ I)
      (Hsim: sim tpc mc tpf mf xs f fg fp (S (S fuelF))),
    exists tpf' mf' fp' tr',
      (forall U, fmachine_step (i :: U, tr, tpf) mf (U, tr', tpf') mf') /\
      sim tpc mc tpf' mf' (i :: xs) f fg fp' (S fuelF).

  Definition sim_external_def :=
    forall (tpc tpf : thread_pool) (mc mf : Mem.mem) tr fuelF
      (xs : Sch) (f fg : memren) (fp : fpool tpc) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hexternal: pff @ E)
      (Hsynced: ~ List.In i xs)
      (Hsim: sim tpc mc tpf mf xs f fg fp (S (S fuelF))),
    exists tpc' mc' tpf' mf' f' fp' tr',
      (forall U, fmachine_step (i :: U, tr, tpf) mf (U, tr', tpf') mf') /\
      sim tpc' mc' tpf' mf' xs f' fg fp' (S fuelF).

  (** When we reach a suspend step, we can ``synchronize'' the two
  machines by executing on the coarse machine the internal steps of
  the thread that reached the suspend step. The injection of this
  thread will now serve as the new injection. *)

  Definition sim_suspend_def :=
    forall (tpc tpf : thread_pool) (mc mf : Mem.mem) tr fuelF
      (xs : Sch) (f fg : memren) (fp : fpool tpc) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hexternal: pff @ S)
      (Hsim: sim tpc mc tpf mf xs f fg fp (S (S fuelF))),
    exists tpc' mc' tpf' mf' f' fp' tr',
      (forall U, fmachine_step (i :: U, tr, tpf) mf (U, tr', tpf') mf') /\
      sim tpc' mc' tpf' mf' [seq x <- xs | x != i] f' fg fp'
          (S fuelF).

  Definition sim_halted_def :=
    forall (tpc tpf : thread_pool) (mc mf : Mem.mem) tr fuelF
      (xs : Sch) (f fg : memren) (fp : fpool tpc) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hinternal: pff @ H)
      (Hsim: sim tpc mc tpf mf xs f fg fp (S (S fuelF))),
      exists tr',
        (forall U, fmachine_step (i :: U, tr, tpf) mf (U, tr', tpf) mf) /\
        sim tpc mc tpf mf xs f fg fp (S fuelF).

  Definition sim_fail_def :=
    forall (tpc tpf : thread_pool) (mc mf : Mem.mem) tr fuelF
      (xs : Sch) (f fg : memren) (fp : fpool tpc) (i : NatTID.tid)
      (pff: ~ containsThread tpf i)
      (Hsim: sim tpc mc tpf mf xs f fg fp (S (S fuelF))),
    exists tr',
      (forall U, fmachine_step (i :: U, tr, tpf) mf (U, tr', tpf) mf) /\
      sim tpc mc tpf mf xs f fg fp (S fuelF).
  
End SimDefs.

(** ** Proofs *)
Module SimProofs (SEM: Semantics)
       (SemAxioms: SemanticsAxioms SEM)
       (Machine: MachinesSig with Module SEM := SEM)
       (AsmContext: AsmContext SEM Machine)
       (CI: CoreInjections SEM).

  Module SimDefs := SimDefs SEM SemAxioms Machine AsmContext CI.
  Import SimDefs.
  Import StepType StepType.InternalSteps StepType.StepLemmas.
  Import CoreLanguage CoreLanguageDry SemAxioms.

  (* Memory Imports*)
  Import MemObsEq ValObsEq MemoryLemmas.
  Import CI ValueWD MemoryWD Renamings.

  (* Machine and Context Imports*)
  Import Machine DryMachine ThreadPool AsmContext dry_machine.Concur.mySchedule.
  Import ThreadPoolInjections.
  Import event_semantics Events.

  Module ThreadPoolWF := ThreadPoolWF SEM Machine.
  
  Notation csafe := (DryConc.csafe).
  Notation internal_step := (internal_step the_ge).
  Notation internal_execution := (internal_execution the_ge).
  
  Lemma ctlType_inj :
    forall c c' (f: memren)
      (Hinj: ctl_inj f c c'),
      ctlType c = ctlType c'.
  Proof.
    intros. unfold ctl_inj in Hinj.
    destruct c; destruct c'; try (by exfalso);
    unfold ctlType in *;
    try assert (Hat_ext := core_inj_ext Hinj);
    try assert (Hhalted := core_inj_halted Hinj); auto.
    destruct (at_external SEM.Sem c) as [[[? ?] ?]|]; simpl in *;
    destruct (at_external SEM.Sem c0) as [[[? ?] ?]|]; simpl in *; auto;
    try (by exfalso).
    destruct (halted SEM.Sem c), (halted SEM.Sem c0); by tauto.
  Qed.

  Lemma stepType_inj:
    forall tpc tpf i (pffi:containsThread tpf i) (pfci: containsThread tpc i) f,
      ctl_inj f (getThreadC pfci) (getThreadC pffi) ->
      getStepType pfci = getStepType pffi.
  Proof.
    intros.
    eapply ctlType_inj;
      by eauto.
  Qed.

  Lemma sim_reduce:
    forall tpc mc tpf mf xs f fg fp n m,
      sim tpc mc tpf mf xs f fg fp n ->
      m <= n ->
      sim tpc mc tpf mf xs f fg fp m.
  Proof.
    intros.
    inversion H.
    econstructor; eauto.
    intros.
    eapply DryConc.csafe_reduce; eauto.
    ssromega.
  Qed.
  
  (** Proof of simulation of trivial halted step*)
      
  Lemma sim_halted: sim_halted_def.
  Proof.
    unfold sim_halted_def.
    intros.
    pose proof (mem_compf Hsim).
    pose proof (invF Hsim).
    unfold getStepType in Hinternal.
    destruct (getThreadC pff) eqn:Hget; simpl in *;
    try discriminate.
    destruct (at_external SEM.Sem c), (halted SEM.Sem c) eqn:?; try discriminate.
    exists tr.
    split.
    intros.
    econstructor 6; simpl; eauto.
    econstructor; eauto. 
    rewrite Heqo; eauto.
    eapply sim_reduce; eauto.
  Qed.

  Lemma sim_fail: sim_fail_def.
  Proof.
    unfold sim_fail_def.
    intros.
    exists tr.
    split.
    intros. econstructor 7; simpl; eauto.
    eapply sim_reduce; eauto.
  Qed.

  (** Proofs about [internal_execution] and [internal_step] *)

  Lemma internal_step_cmachine_step :
    forall (i : NatTID.tid) (tp tp' : thread_pool) (m m' : mem)
      (U : list NatTID.tid)
      (Hcnt: containsThread tp i)
      (Hcomp: mem_compatible tp m) 
      (Hstep_internal: internal_step Hcnt Hcomp tp' m'),
      cmachine_step ((buildSched (i :: U)), [::], tp) m
                    ((buildSched (i :: U)), [::], tp') m' /\
      (forall tp'' m'' U',
          cmachine_step ((buildSched (i :: U)), [::],tp) m
                        ((buildSched U'), [::], tp'') m'' ->
          tp' = tp'' /\ m' = m'' /\ i :: U = U').
  Proof.
    intros. split.
    destruct Hstep_internal as [[? Hcore] | [[Hresume ?] | [Hstart ?]]]; subst;
    autounfold.
    econstructor; simpl; eauto.
    econstructor 2; simpl; eauto.
    econstructor 1; simpl; eauto.
    intros tp'' m'' U' Hstep.
    assert (Hstep_internal': internal_step Hcnt Hcomp tp'' m'' /\ i :: U = U').
    { inversion Hstep; subst; clear Hstep;
      simpl in *; inversion HschedN; subst; pf_cleanup;
      unfold internal_step; try (by eexists; eauto);
      apply internal_step_type in Hstep_internal; exfalso;
      unfold getStepType, ctlType in Hstep_internal;
      try inversion Htstep; 
      try (inversion Hhalted); subst;
      unfold getThreadC in *; pf_cleanup;
      repeat match goal with
             | [H1: context[match ?Expr with | _ => _ end],
                    H2: ?Expr = _ |- _] =>
               rewrite H2 in H1
             end; try discriminate.
      destruct (at_external_halted_excl SEM.Sem c) as [Hnot_ext | Hcontra].
      rewrite Hnot_ext in Hstep_internal; try discriminate.
      destruct (halted SEM.Sem c) eqn:Hhalted'; try discriminate.
      rewrite Hcontra in Hcant;
        by auto.
    }
    destruct Hstep_internal' as [Hstep_internal' Heq]; subst.
    destruct (internal_step_det Hstep_internal Hstep_internal'); subst.
    auto.
  Qed.

  Lemma list_cons_irrefl:
    forall {A: Type} (x : A) xs,
      ~ x :: xs = xs.
  Proof.
    intros.
    induction xs; intro Hcontra; simpl; try discriminate.
    inversion Hcontra; subst a; auto.
  Qed.
  
 Lemma safety_det_corestepN_internal:
    forall xs i U tpc mc tpc' mc' fuelF
      (Hsafe : csafe the_ge (buildSched (i :: U),[::],tpc) mc
                     (fuelF.+1 + size xs))
      (Hexec : internal_execution [seq x <- xs | x == i] tpc mc tpc' mc'),
      corestepN CoarseSem the_ge (size [seq x <- xs | x == i])
                (buildSched (i :: U), [::], tpc) mc (buildSched (i :: U), [::], tpc') mc'
      /\ csafe the_ge (buildSched (i :: U),[::],tpc') mc'
              (fuelF.+1 + size [seq x <- xs | x != i]).
  Proof.
    intros xs.
    induction xs as [ | x xs]; intros.
    { simpl in *. inversion Hexec; subst.
      eexists; eauto.
      simpl in HschedN. discriminate.
    }
    { simpl in *.
      destruct (x == i) eqn:Hx; move/eqP:Hx=>Hx; subst.
      - unfold buildSched in *. inversion Hsafe.
        + simpl in H; by exfalso.
        + simpl in *.
          subst.
          inversion Hexec; subst; simpl in *; clear Hexec;
          inversion HschedN; subst i.
          assert (Hmach_step_det :=
                    internal_step_cmachine_step U Hstep0).
          destruct Hmach_step_det as [Hmach_step' Hmach_det].
          specialize (Hmach_det _ _ _ Hstep).
          destruct Hmach_det as [? [? ?]]; subst.
          rewrite <- addSnnS in Hsafe0.
          destruct (IHxs tid U tp' m' tpc' mc' _ Hsafe0 Htrans)
            as [HcorestepN Hsafe'].
          split; eauto.
        + exfalso.
          inversion Hexec; subst; simpl in *; clear Hexec;
          inversion HschedN; subst i.
          assert (Hmach_step_det := internal_step_cmachine_step U Hstep0).
          destruct Hmach_step_det as [Hmach_step' Hmach_det].
          specialize (Hmach_det _ _ _ Hstep).
          destruct Hmach_det as [? [? ?]].
          exfalso;
            eapply list_cons_irrefl; eauto.
      - simpl.
        rewrite <- addSnnS in Hsafe.
        destruct (IHxs i U tpc mc tpc' mc' (fuelF.+1) Hsafe Hexec).
        split; auto.
        rewrite <- addSnnS.
        eapply IHxs; eauto.
    }
  Qed.
  
  Lemma at_internal_cmachine_step :
    forall i U U' tp tp' m m' (cnt: containsThread tp i)
      (isInternal: cnt @ I)
      (Hstep: cmachine_step (buildSched (i :: U), [::],tp) m (U', [::], tp') m'),
    exists (Hcomp : mem_compatible tp m),
      internal_step cnt Hcomp tp' m' /\ U' = buildSched (i :: U).
  Proof.
    intros.
    absurd_internal Hstep.
    exists Hcmpt. split; auto.
    do 2 right;
      by auto.
    exists Hcmpt. split; auto.
    right; left;
      by auto.
    exists Hcmpt. split; auto.
    left; eauto.
  Qed.
  
  (** Starting from a well-defined state, an internal execution
  retains the well-definedeness for any injection that corresponds to
  the domain of the new memory. *)
  
  Lemma internal_step_wd:
    forall tp m tp' m' i (cnti: containsThread tp i) f fg
      (Hcomp: mem_compatible tp m)
      (Hmem_wd: valid_mem m)
      (Hdomain: domain_memren f m)
      (Htp_wd: tp_wd f tp)
      (Hge_wd: ge_wd fg the_ge)
      (Hfg_incr: ren_domain_incr fg f)
      (Hstep: internal_step cnti Hcomp tp' m'),
      valid_mem m' /\
      (exists f' : memren, ren_domain_incr f f' /\ domain_memren f' m') /\
      (forall f' : memren, domain_memren f' m' -> tp_wd f' tp').
  Proof.
    intros.
    inversion Hstep as [[? Htstep] | [[Htstep ?] | [Htstep ?]]].
    - inversion Htstep; subst.
      erewrite restrPermMap_mem_valid with (Hlt := fst (Hcomp i cnti)) in Hmem_wd.
      eapply ev_step_ax1 in Hcorestep.
      apply corestep_wd with (f := f) (fg := fg) in Hcorestep; eauto.
      destruct Hcorestep as [Hmem_wd' [Hf' Hcore_wd']].
      destruct Hf' as [f' [Hincr Hdomain']].
      assert (Hcore_wd_f':= Hcore_wd' _ Hdomain').
      split; auto.
      split; first by (eexists; eauto).
      intros f'' Hdomain''.
      intros j cntj.
      specialize (Hcore_wd' f'' Hdomain'').
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
      rewrite gssThreadCode.
      simpl;
        by auto.
      assert (cntj' := containsThread_internal_step' Hstep cntj).
      erewrite @gsoThreadCode with (cntj := cntj') by eauto.
      specialize (Htp_wd _ cntj').
      assert (Hincr': ren_domain_incr f f'').
        by (eapply domain_memren_incr with (f' := f'); eauto).
      eapply ctl_wd_incr;
        by eauto.
      specialize (Htp_wd _ cnti).
      rewrite Hcode in Htp_wd;
        by simpl in Htp_wd.
    - subst. split; auto.
      inversion Htstep; subst.
      split.
      exists f.
      split; unfold ren_domain_incr;
        by auto.
      intros f'' Hdomain''.
      intros j cntj'.
      assert (cntj: containsThread tp j)
        by (eapply cntUpdateC'; eauto).
      assert (Hincr: ren_domain_incr f f'')
        by (eapply domain_memren_incr with (f' := f) (f'' := f''); eauto;
            apply ren_domain_incr_refl).
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
      + rewrite gssThreadCC.
        pf_cleanup.
        specialize (Htp_wd _ cntj).
        rewrite Hcode in Htp_wd.
      destruct X as [[? ?] ?].
      simpl in *.
      destruct Htp_wd as [Hcore_wd _].
      assert (Hargs:= at_external_wd Hcore_wd Hat_external).
      eapply after_external_wd; eauto.
      eapply core_wd_incr; eauto.
      eapply valid_val_list_incr;
        by eauto.
      simpl; auto.
      + erewrite <- @gsoThreadCC with (cntj := cntj); eauto.
        specialize (Htp_wd _ cntj).
        eapply ctl_wd_incr;
          by eauto.
    - subst; split; auto.
      inversion Htstep; subst.
      split.
      exists f.
      split; unfold ren_domain_incr;
        by auto.
      intros f'' Hdomain''.
      intros j cntj'.
      assert (cntj: containsThread tp j)
        by (eapply cntUpdateC'; eauto).
      assert (Hincr: ren_domain_incr f f'')
        by (eapply domain_memren_incr with (f' := f) (f'' := f''); eauto;
            apply ren_domain_incr_refl).
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
      rewrite gssThreadCC.
      pf_cleanup.
      simpl.
      eapply initial_core_wd; eauto.
      specialize (Htp_wd _ cntj).
      rewrite Hcode in Htp_wd.
      simpl in Htp_wd.
      destruct Htp_wd.
      eapply valid_val_incr;
        by eauto.
      eapply ge_wd_incr; eauto.
      eapply ren_domain_incr_trans;
        by eauto.
      erewrite <- @gsoThreadCC with (cntj := cntj); eauto.
      specialize (Htp_wd _ cntj).
      eapply ctl_wd_incr;
        by eauto.
  Qed.

  Lemma internal_execution_wd:
    forall tp m tp' m' i xs f fg
      (Hdomain: domain_memren f m)
      (Hmem_wd: valid_mem m)
      (Htp_wd: tp_wd f tp)
      (Hge_wd: ge_wd fg the_ge)
      (Hge_incr: ren_domain_incr fg f)
      (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m'),
      valid_mem m' /\
      (exists f' : memren, ren_domain_incr f f' /\ domain_memren f' m') /\
      (forall f' : memren, domain_memren f' m' -> tp_wd f' tp').
  Proof.
    intros.
    generalize dependent m.
    generalize dependent f.
    generalize dependent tp.
    induction xs; intros.
    simpl in Hexec; inversion Hexec; subst;
    [idtac| simpl in HschedN; by discriminate];
    split; auto;
    split; [exists f; split; unfold ren_domain_incr; auto | eauto].
    intros.
    eapply tp_wd_domain;
      by eauto.
    simpl in Hexec.
    destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq; try eauto.
    subst a. inversion Hexec; subst.
    simpl in Htrans.
    simpl in HschedN; inversion HschedN; subst tid.
    assert (H := internal_step_wd Hmem_wd Hdomain Htp_wd Hge_wd Hge_incr Hstep).
    destruct H as [Hmem_wd0' [[f' [Hincr Hdomain0']] Htp_wd0']].
    specialize (Htp_wd0' f' Hdomain0').
    assert (Hge_incr0': ren_domain_incr fg f')
      by ( eapply ren_domain_incr_trans; eauto).
    assert (Hge_wd0': ge_wd f' the_ge)
      by (eapply ge_wd_incr; eauto).
    destruct (IHxs _ f' Htp_wd0' Hge_incr0'  m'0 Hdomain0' Hmem_wd0' Htrans)
      as (Hwd_mem' & Hf'' & Htp_wd').
    destruct Hf'' as [f'' [Hincr'' Hdomain'']].
    specialize (Htp_wd' _ Hdomain'').
    assert (ren_domain_incr f f'')
      by (eapply ren_domain_incr_trans; eauto).
    repeat match goal with
           | [|- _ /\ _] => split; eauto
           | [|- exists _, _] => eexists; eauto
           | [|- forall _, _] => intros
           end.
    eapply tp_wd_domain;
      by eauto.
  Qed.

  Lemma suspend_tp_wd:
    forall tpc tpc' (f : memren) i (pfc : containsThread tpc i)
      (Hsuspend: DryConc.suspend_thread pfc tpc')
      (Htp_wd: tp_wd f tpc),
      tp_wd f tpc'.
  Proof.
    intros.
    inversion Hsuspend; subst.
    intros j cntj.
    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
    rewrite gssThreadCC.
    simpl. specialize (Htp_wd _ ctn).
    rewrite Hcode in Htp_wd.
    simpl in Htp_wd;
      by assumption.
    assert (ctnj0: containsThread tpc j)
      by (eapply cntUpdateC'; eauto).
    specialize (Htp_wd _ ctnj0).
    erewrite <- @gsoThreadCC with (cntj := ctnj0);
      by auto.
  Qed.


  (** Profs about [mem_obs_eq] and [weak_mem_obs_eq] *)
  
  Lemma weak_obs_eq_restr :
    forall (m m' : Mem.mem) (f : memren)
      (weakObsEq: weak_mem_obs_eq f m m')
      (pf: permMapLt (getCurPerm m) (getMaxPerm m))
      (pf': permMapLt (getCurPerm m') (getMaxPerm (setMaxPerm m'))),
      weak_mem_obs_eq f (restrPermMap pf) (restrPermMap pf').
  Proof.
    intros. inversion weakObsEq.
    constructor; auto.
    intros.
    assert (Hrestr := restrPermMap_correct pf b1 ofs).
    destruct Hrestr as [_ Hcur].
    assert (Hrestr' :=
              restrPermMap_correct pf' b2 ofs).
    destruct Hrestr' as [_ Hcur'].
    rewrite Hcur; rewrite Hcur';
    do 2 rewrite getCurPerm_correct; eauto.
  Qed.

  Lemma mem_obs_eq_restr :
    forall (m m' : Mem.mem) (f : memren)
      (memObsEq: mem_obs_eq f m m')
      (pf: permMapLt (getCurPerm m) (getMaxPerm m))
      (pf': permMapLt (getCurPerm m') (getMaxPerm (setMaxPerm m'))),
      mem_obs_eq f (restrPermMap pf) (restrPermMap pf').
  Proof.
    intros.
    destruct memObsEq as [HweakObs HstrongObs].
    destruct HstrongObs as [Hperm_eq Hval].
    assert (Hrestr := restrPermMap_correct pf).
    assert (Hrestr' :=
              restrPermMap_correct pf').
    constructor;
      first by (eapply weak_obs_eq_restr; eauto).
    constructor;
      first by
        (intros;
          destruct (Hrestr b1 ofs) as [_ Hcur];
          destruct (Hrestr' b2 ofs) as [_ Hcur'];
          rewrite Hcur Hcur';
          do 2 rewrite getCurPerm_correct; auto).
    intros b1 b2 ofs Hf Hperm. unfold restrPermMap; simpl.
    eapply Hval; eauto.
    unfold Mem.perm in *.
    destruct (Hrestr b1 ofs) as [_ Hcur].
    unfold permission_at in *.
    rewrite Hcur in Hperm.
    rewrite getCurPerm_correct in Hperm;
      by assumption.
  Qed.

  Lemma weak_obs_eq_setMax:
    forall (f : memren) (m m' : mem),
      weak_mem_obs_eq f m m' <-> weak_mem_obs_eq f m (setMaxPerm m').
  Proof.
    intros. split; intros Hweak_obs;
            inversion Hweak_obs;
            constructor; auto;
            intros.
    rewrite setMaxPerm_Cur;
      by auto.
    specialize (perm_obs_weak0 _ _ ofs Hrenaming).
    rewrite setMaxPerm_Cur in perm_obs_weak0.
      by auto.
  Qed.

  Lemma weak_mem_obs_eq_restrEq:
    forall f f' mc mf mc' mf' pmap pmapF
      (Hlt: permMapLt pmap (getMaxPerm mc))
      (HltF: permMapLt pmapF (getMaxPerm mf))
      (Hlt': permMapLt pmap (getMaxPerm mc'))
      (HltF': permMapLt pmapF (getMaxPerm mf'))
      (Hobs_eq: weak_mem_obs_eq f (restrPermMap Hlt) (restrPermMap HltF))
      (Hobs_eq': weak_mem_obs_eq f' mc' mf')
      (Hincr: ren_incr f f')
      (Hsep: ren_separated f f' mc mf),
      weak_mem_obs_eq f' (restrPermMap Hlt') (restrPermMap HltF').
  Proof.
    intros.
    destruct Hobs_eq'.
    econstructor; intros; eauto.
    erewrite restrPermMap_valid; eauto.
    destruct (valid_block_dec mc b1) as [Hvalid | Hinvalid].
    - apply (domain_valid Hobs_eq) in Hvalid.
      destruct Hvalid as [b2' Hf].
      assert (b2 = b2')
        by (apply Hincr in Hf; rewrite Hf in Hrenaming; inversion Hrenaming; subst; auto).
      subst b2'.
      pose proof (perm_obs_weak Hobs_eq b1 ofs Hf).
      rewrite! restrPermMap_Cur.
      rewrite! restrPermMap_Cur in H.
      assumption.
    - apply (domain_invalid Hobs_eq) in Hinvalid.
      destruct (Hsep b1 b2 Hinvalid Hrenaming) as [_ Hnone].
      pose proof (invalid_block_empty HltF Hnone ofs) as HnoneCur.
      rewrite! restrPermMap_Cur. rewrite HnoneCur.
      now apply po_None.
  Qed.

  (** Changes to the memories in place where permissions are below [Readable] preserve [strong_mem_obs_eq] *)
  Lemma strong_mem_obs_eq_disjoint_step:
    forall f f' mc mf mc' mf' pmap pmapF
      (Hlt: permMapLt pmap (getMaxPerm mc))
      (HltF: permMapLt pmapF (getMaxPerm mf))
      (Hlt': permMapLt pmap (getMaxPerm mc'))
      (HltF': permMapLt pmapF (getMaxPerm mf'))
      (Hobs_eq: mem_obs_eq f (restrPermMap Hlt) (restrPermMap HltF))
      (Hstable: forall b ofs, Mem.perm (restrPermMap Hlt) b ofs Cur Readable ->
                         ZMap.get ofs (Mem.mem_contents mc) # b = ZMap.get ofs (Mem.mem_contents mc') # b)
      (HstableF: forall b ofs, Mem.perm (restrPermMap HltF) b ofs Cur Readable ->
                          ZMap.get ofs (Mem.mem_contents mf) # b = ZMap.get ofs (Mem.mem_contents mf') # b)
      (Hincr: ren_incr f f')
      (Hsep: ren_separated f f' mc mf),
      strong_mem_obs_eq f' (restrPermMap Hlt') (restrPermMap HltF').
  Proof.
    intros. 
    econstructor; intros.
    - destruct (valid_block_dec mc b1) as [Hvalid | Hinvalid].
      + (** if [b1] is a valid block in [mc] *)
        pose proof (weak_obs_eq Hobs_eq) as Hweak_obs_eq.
        apply (domain_valid Hweak_obs_eq) in Hvalid.
        destruct Hvalid as [b2' Hf].
        assert (b2 = b2')
          by (apply Hincr in Hf; rewrite Hrenaming in Hf; inversion Hf; subst; auto);
          subst b2'.
        rewrite! restrPermMap_Cur.
        pose proof (perm_obs_strong (strong_obs_eq Hobs_eq) _ ofs Hf) as Heq.
        rewrite! restrPermMap_Cur in Heq.
        now assumption.
      + (** if [b1] is not a valid block in [mc]*)
        apply (domain_invalid (weak_obs_eq Hobs_eq)) in Hinvalid.
        destruct (Hsep b1 b2 Hinvalid Hrenaming) as [Hnone HnoneF].
        pose proof (invalid_block_empty Hlt Hnone ofs) as HnoneCur.
        pose proof (invalid_block_empty HltF HnoneF ofs) as HnoneCurF.
        rewrite! restrPermMap_Cur. rewrite HnoneCur HnoneCurF; reflexivity.
    - simpl.
      pose proof (val_obs_eq (strong_obs_eq Hobs_eq)) as Hval_eq.
      unfold Mem.perm in *.
      destruct (valid_block_dec mc b1) as [Hvalid | Hinvalid].
      + (** if [b1] is a valid block in [mc]*)
        apply (domain_valid (weak_obs_eq Hobs_eq)) in Hvalid.
        destruct Hvalid as [b2' Hf].
        assert (b2 = b2')
          by (apply Hincr in Hf; rewrite Hrenaming in Hf; inversion Hf; subst; auto);
          subst b2'.
        pose proof (restrPermMap_Cur Hlt b1 ofs) as H1.
        pose proof (restrPermMap_Cur Hlt' b1 ofs) as H1'.
        unfold permission_at in *.
        specialize (Hval_eq b1 b2 ofs Hf).
        rewrite H1' in Hperm; rewrite H1 in Hval_eq.
        specialize (Hval_eq Hperm).
        simpl in Hval_eq.
        erewrite <- Hstable by (rewrite H1; assumption).
        erewrite <- HstableF by (pose proof (perm_obs_strong (strong_obs_eq Hobs_eq)) as Heq;
                                unfold permission_at in Heq;
                                erewrite Heq; eauto;
                                rewrite H1; assumption).
        eauto using memval_obs_eq_incr.
      + (** if [b1] is an invalid block in [mc]*)
        exfalso.
        apply (domain_invalid (weak_obs_eq Hobs_eq)) in Hinvalid.
        destruct (Hsep b1 b2 Hinvalid Hrenaming) as [Hnone HnoneF].
        pose proof (invalid_block_empty Hlt Hnone ofs) as HnoneCur.
        pose proof (restrPermMap_Cur Hlt' b1 ofs) as H1'.
        unfold permission_at in *.
        rewrite H1' in Hperm.
        rewrite HnoneCur in Hperm.
        simpl in Hperm.
        now assumption.
  Qed.
  
  (** ** Proofs of internal step safety and simulation*)

  Lemma tsim_fstep_safe:
    forall tpc tpc' tpf mc mc' mf i fi fg tr
      (pfc: containsThread tpc i) (pff: containsThread tpf i)
      (Hcompc: mem_compatible tpc mc)
      (Hcompf: mem_compatible tpf mf)
      (HmaxF: max_inv mf)
      (HinvF: invariant tpf)
      (Hge_wd: ge_wd fg the_ge)
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hren_incr: ren_incr fg fi)
      (Hstrong_sim: strong_tsim fi pfc pff Hcompc Hcompf)
      (Hstep_internal: internal_step pfc Hcompc tpc' mc'),
    exists tpf' mf' fi' tr',
      (forall U, fmachine_step (i :: U, tr, tpf) mf (U, tr', tpf') mf') /\
      max_inv mf' /\
      ren_incr fi fi' /\
      ren_separated fi fi' mc mf /\
      (forall (pfc': containsThread tpc' i) (pff': containsThread tpf' i)
         (Hcompc': mem_compatible tpc' mc') (Hcompf': mem_compatible tpf' mf'),
          strong_tsim fi' pfc' pff' Hcompc' Hcompf') /\
      (forall j (pffj : containsThread tpf j),
          i <> j ->
          forall (b1 b2 : block),
            fi' b1 = Some b2 ->
            fi b1 = None ->
            forall ofs, (getThreadR pffj).1 # b2 ofs = None /\ (getThreadR pffj).2 # b2 ofs = None) /\
      (forall (bl : block) (ofsl : Z)
         (rmap : dry_machine.LocksAndResources.lock_info)
         (b1 b2 : block) (ofs : Z),
          fi' b1 = Some b2 ->
          fi b1 = None ->
          lockRes tpf (bl, ofsl) = Some rmap -> rmap.1 # b2 ofs = None /\ rmap.2 # b2 ofs = None).
  Proof.
    intros.
    assert (HinvC': invariant tpc')
      by (eapply internal_step_invariant; eauto).
    destruct Hstep_internal as [[? Hcstep] | [Hresume | Hstart]].
    { inversion Hcstep; subst; clear Hcstep.
      destruct Hstrong_sim as [Hcode_eq memObsEq_data memObsEq_locks].
      rewrite Hcode in Hcode_eq.
      (* getThreadC pff returns a Krun*)
      simpl in Hcode_eq. destruct (getThreadC pff) as [cf| ? | ? | ?] eqn:Hcodef;
        try (by exfalso).
      assert (H' := Hcorestep).
      apply ev_step_ax1 in Hcorestep.
      eapply corestep_obs_eq in Hcorestep; eauto.
      destruct Hcorestep as
          (cf' & mf' & fi' & HcorestepF & Hcode_eq'
           & Hobs_eq' & Hincr & Hseparated
           & Hblocks & _ & _).
      remember (restrPermMap (fst (Hcompf _ pff))) as mf1 eqn:Hrestrict.
      symmetry in Hrestrict.
      remember (updThread pff (Krun cf') (getCurPerm mf', (getThreadR pff).2))
        as tpf' eqn:Hupd.
      assert (Hevent_stepF:=ev_step_ax2 _ _ _ _ _ _ HcorestepF).
      destruct Hevent_stepF as [evF Hev_stepF].
      exists tpf', (setMaxPerm mf'), fi', (tr ++ (List.map (fun mev => internal i mev) evF)).
      split.
      { (* FineConc machine steps *)
        intros U. eapply FineConc.thread_step; simpl; eauto.
        econstructor; eauto.
      }
      {
        split.
        unfold max_inv.
        intros b ofs Hvalid.
        rewrite setMaxPerm_MaxV;
          by auto.
        split; first by assumption.
        split.
        (* Proof of seperation*)
        clear - Hupd Hseparated Hrestrict HmaxF.
        subst mf1.
        unfold ren_separated in *.
        intros b1 b2 Hfi Hfi'.
        specialize (Hseparated _ _ Hfi Hfi').
        do 2 erewrite restrPermMap_valid in Hseparated;
          by assumption.
        split.
        (* Proof of strong simulation*)
        intros. econstructor;
          first by (subst tpf'; by do 2 erewrite gssThreadCode).
        - (* mem_obs_eq for data permissions *)
          assert (Hlt_mc' : permMapLt (getCurPerm mc')
                                      (getMaxPerm mc'))
            by (unfold permMapLt; intros;
                rewrite getCurPerm_correct; rewrite getMaxPerm_correct;
                apply Mem.access_max).
          erewrite restrPermMap_irr' with (Hlt' := Hlt_mc')
            by (by rewrite gssThreadRes).
          assert (Hlt_mf': permMapLt (getCurPerm mf')
                                     (getMaxPerm (setMaxPerm mf'))).
          { unfold permMapLt. intros.
            rewrite getCurPerm_correct. rewrite getMaxPerm_correct.
            destruct (valid_block_dec mf' b) as [Hvalid | Hinvalid].
            erewrite setMaxPerm_MaxV by assumption. simpl.
            destruct (permission_at mf' b ofs Cur); constructor.
            erewrite setMaxPerm_MaxI by assumption. simpl.
            apply Mem.nextblock_noaccess with (ofs := ofs) (k := Cur) in Hinvalid.
            unfold permission_at. rewrite Hinvalid. constructor.
          }
          erewrite restrPermMap_irr' with (Hlt' := Hlt_mf')
            by (subst tpf'; rewrite gssThreadRes; eauto);
            by eapply mem_obs_eq_restr.
        - (** mem_obs_eq for lock permissions *)
          (** lock permissions do not change by internal steps. Hence
           [weak_mem_obs_eq] should be trivial to obtain using
           [weak_mem_obs_eq_restrEq]. For [strong_mem_obs_eq] we need to use the
           fact that permissions are disjoint/coherent and hence the step could
           not have changed the contents at locations where there is readable
           permission for the lock. *)
          subst.
          assert (Hlt: permMapLt (getThreadR pfc').2 (getMaxPerm mc))
            by (rewrite gssThreadRes; simpl; destruct Hcompc; destruct (compat_th0 _ pfc); eauto).
          assert (HltF: permMapLt (getThreadR pff').2 (getMaxPerm mf))
            by (rewrite gssThreadRes; simpl; destruct Hcompf as [compat_thf ?]; destruct (compat_thf _ pff); eauto).
          constructor.
          (* dependent types mumbo-jumbo*)
          pose proof (weak_obs_eq memObsEq_locks) as Hobs_weak_locks.
          erewrite restrPermMap_irr' with (Hlt' := Hlt) in Hobs_weak_locks by (rewrite gssThreadRes; simpl; auto).
          erewrite restrPermMap_irr' with (Hlt' := HltF) in Hobs_weak_locks by (rewrite gssThreadRes; simpl; auto).
          (* apply the lemma *)
          eapply weak_mem_obs_eq_restrEq with (Hlt := Hlt) (HltF := HltF); eauto.
          erewrite <- weak_obs_eq_setMax; now eapply (weak_obs_eq Hobs_eq').
          (* proof of strong_mem_obs_eq*)
          erewrite restrPermMap_irr' with (Hlt' := Hlt) in memObsEq_locks by (rewrite gssThreadRes; simpl; auto).
          erewrite restrPermMap_irr' with (Hlt' := HltF) in memObsEq_locks by (rewrite gssThreadRes; simpl; auto).
          eapply strong_mem_obs_eq_disjoint_step; eauto.
          (* stability of contents of DryConc *)
          intros.
          pose proof (fst (thread_data_lock_coh Hinv pfc) _ pfc).
          apply ev_step_ax1 in H'.
          eapply corestep_stable_val with (Hlt2 := Hlt); eauto.
          rewrite gssThreadRes; simpl;
            by eauto.
          (* stability of contents of FineConc *)
          intros.
          pose proof (fst (thread_data_lock_coh HinvF pff) _ pff).
          simpl.
          eapply corestep_stable_val with (Hlt2 := HltF); eauto.
          rewrite gssThreadRes; simpl;
            by eauto.
        (* block ownership*)
        (*sketch: the invariant is maintanted by coresteps hence it
           will hold for tpf'. Moreover we know that the new blocks in
           mc'|i will be mapped to new blocks in mf' by inject separated,
           where the permissions are empty for other threads. *)
          split.
          + intros j pffj Hij b1 b2 Hfi' Hfi ofs.
            specialize (Hseparated _ _ Hfi Hfi').
            destruct Hseparated as [Hinvalidmc1 Hinvalidmf1].
            subst mf1.
            erewrite restrPermMap_valid in Hinvalidmf1.
            pose proof (invalid_block_empty (fst (Hcompf _ pffj)) Hinvalidmf1 ofs).
            pose proof (invalid_block_empty (snd (Hcompf _ pffj)) Hinvalidmf1 ofs);
              split; by assumption.
          + intros bl ofsl rmap b1 b2 ofs Hfi' Hfi Hres.
            specialize (Hseparated _ _ Hfi Hfi').
            destruct Hseparated as [Hinvalidmc1 Hinvalidmf1].
            subst mf1.
            erewrite restrPermMap_valid in Hinvalidmf1.
            pose proof (invalid_block_empty (fst (compat_lp Hcompf _ Hres)) Hinvalidmf1 ofs).
            pose proof (invalid_block_empty (snd (compat_lp Hcompf _ Hres)) Hinvalidmf1 ofs);
              split; by assumption.
      }
    }
    { destruct Hresume as [Hresume Heq]; subst.
      inversion Hresume; subst; clear Hresume; pf_cleanup.
      destruct Hstrong_sim as [Hcode_eq memObsEq].
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pff) as [?|?|cf |? ] eqn:HcodeF;
        try (by exfalso).
      destruct Hcode_eq as [Hcode_eq Hval_eq].
      inversion Hval_eq; subst.
      (* After external for cf*)
      assert (Hvalid_val: match (Some (Vint Int.zero)) with
                          | Some v1 => valid_val fi v1
                          | None => True
                          end)
        by (by simpl).
      assert (Hafter_externalF :=
                core_inj_after_ext (Some (Vint Int.zero)) Hcode_eq
                                   Hvalid_val Hafter_external).
      destruct Hafter_externalF as [ov2 [cf' [Hafter_externalF [Hcode_eq' Hval_obs]]]].
      destruct ov2 as [v2 |]; try by exfalso.
      inversion Hval_obs; subst.
      (* cf is at external*)
      assert (Hat_externalF_spec := core_inj_ext Hcode_eq).
      rewrite Hat_external in Hat_externalF_spec.
      simpl in Hat_externalF_spec.
      destruct X as [[ef sig] val].
      destruct (at_external SEM.Sem cf) as [[[ef' sig'] val']|] eqn:Hat_externalF;
        try by exfalso.
      destruct Hat_externalF_spec as [? [? Harg_obs]]; subst.                         
      remember (updThreadC pff (Krun cf')) as tpf' eqn:Hupd.
      exists tpf', mf, fi, tr.
      split.
      { (* The fine-grained machine steps *)
        intros. eapply FineConc.resume_step with (Htid := pff); simpl; eauto.
        eapply FineConc.ResumeThread with (c := cf);
          by eauto.
      }
      { split; first by auto.
        split; first by auto.
        split; first by congruence.
        split.
        intros.
        constructor;
          first by (subst tpf';
                     do 2 rewrite gssThreadCC; by simpl).
        erewrite restrPermMap_irr' with
        (Hlt' := fst (Hcompf _ pff)) by (subst; by erewrite @gThreadCR with (cntj := pff)).
        erewrite restrPermMap_irr; eauto;
          by rewrite gThreadCR.
        erewrite restrPermMap_irr' with
        (Hlt' := snd (Hcompf _ pff)) by (subst; by erewrite @gThreadCR with (cntj := pff)).
        erewrite restrPermMap_irr; eauto;
          by rewrite gThreadCR.
        split; [ | split]; intros; by congruence.
      }
    }
    { destruct Hstart as [Hstart Heq]; subst.
      inversion Hstart; subst; clear Hstart; pf_cleanup.
      destruct Hstrong_sim as [Hcode_eq memObsEq].
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pff) as [?|?|? |vf' arg'] eqn:HcodeF;
        try (by exfalso).
      destruct Hcode_eq as [Hvf Harg_obs].
      assert (Harg_obs_list: val_obs_list fi [:: arg] [:: arg'])
        by (constructor; auto; constructor).
      assert (HinitF := core_inj_init Harg_obs_list Hvf Hfg Hge_wd Hren_incr Hinitial).
      destruct HinitF as [c_newF [HinitialF Hcode_eq]].
      remember (updThreadC pff (Krun c_newF)) as tpf' eqn:Hupd.
      exists tpf', mf, fi, tr.
      split.
      { (* The fine-grained machine steps *)
        intros. eapply FineConc.start_step with (Htid := pff); simpl; eauto.
        eapply FineConc.StartThread with (c_new := c_newF);
          by eauto.
      }
      { split; first by auto.
        split; first by auto.
        split; first by congruence.
        split.
        intros.
        constructor;
          first by (subst tpf';
                     do 2 rewrite gssThreadCC; by simpl).
        erewrite restrPermMap_irr' with
        (Hlt' := fst (Hcompf _ pff)) by (subst; by erewrite @gThreadCR with (cntj := pff)).
        erewrite restrPermMap_irr; eauto;
          by rewrite gThreadCR.
        erewrite restrPermMap_irr' with
        (Hlt' := snd (Hcompf _ pff)) by (subst; by erewrite @gThreadCR with (cntj := pff)).
        erewrite restrPermMap_irr; eauto;
          by rewrite gThreadCR.
        split; [|split]; intros; by congruence.
      }
    }
  Qed.
  
  Lemma weak_tsim_fstep:
    forall tpc tpf tpf' mc mf mf' i j f U tr tr'
      (pffi: containsThread tpf i)
      (pfcj: containsThread tpc j) (pffj: containsThread tpf j)
      (pffj': containsThread tpf' j)
      (Hcompc: mem_compatible tpc mc)
      (Hcompf: mem_compatible tpf mf)
      (Hcompf': mem_compatible tpf' mf')
      (HinvF: invariant tpf)
      (Hinternal: pffi @ I)
      (Hstep: fmachine_step (i :: U, tr, tpf) mf (U, tr',tpf') mf')
      (HweakSim: weak_tsim f pfcj pffj Hcompc Hcompf),
      weak_tsim f pfcj pffj' Hcompc Hcompf'.
  Proof.
    intros.
    Opaque containsThread.
    destruct HweakSim as [Hweak_data Hweak_locks].
    destruct Hweak_data
      as [Hdomain_invalid Hdomain_valid Hcodomain_valid Hinjective Hperm_obs_weak_data].
    pose proof (perm_obs_weak Hweak_locks) as Hperm_obs_weak_lock.
    absurd_internal Hstep;
      do 2 constructor; auto.
    (* Case of start step*)
    intros b1 b2 ofs Hf.
    specialize (Hperm_obs_weak_data b1 b2 ofs Hf).
    do 2 rewrite restrPermMap_Cur.
    do 2 rewrite restrPermMap_Cur in Hperm_obs_weak_data.
    erewrite gThreadCR with (cntj := pffj);
      by assumption.
    intros b1 b2 ofs Hf.
    specialize (Hperm_obs_weak_lock b1 b2 ofs Hf).
    do 2 rewrite restrPermMap_Cur.
    do 2 rewrite restrPermMap_Cur in Hperm_obs_weak_lock.
    erewrite gThreadCR with (cntj := pffj);
      by assumption.
    (* Case of resume step*)
     intros b1 b2 ofs Hf.
    specialize (Hperm_obs_weak_data b1 b2 ofs Hf).
    do 2 rewrite restrPermMap_Cur.
    do 2 rewrite restrPermMap_Cur in Hperm_obs_weak_data.
    erewrite gThreadCR with (cntj := pffj);
      by assumption.
    intros b1 b2 ofs Hf.
    specialize (Hperm_obs_weak_lock b1 b2 ofs Hf).
    do 2 rewrite restrPermMap_Cur.
    do 2 rewrite restrPermMap_Cur in Hperm_obs_weak_lock.
    erewrite gThreadCR with (cntj := pffj);
      by assumption.
    (*Case of corestep*)
    - intros b1 b2 Hf.
      erewrite restrPermMap_valid.
      erewrite <- diluteMem_valid.
      specialize (Hcodomain_valid b1 b2 Hf).
      erewrite restrPermMap_valid in Hcodomain_valid.
      eapply ev_step_validblock;
        by eauto.
    - intros b1 b2 ofs Hf.
      specialize (Hperm_obs_weak_data _ _ ofs Hf).
      clear - Hcorestep Hf Hcodomain_valid Hperm_obs_weak_data.
      eapply ev_step_ax1 in Hcorestep.
      destruct (j == tid) eqn:Hjtid; move/eqP:Hjtid=>Hjtid.
      + subst.
        eapply corestep_decay in Hcorestep.
        specialize (Hcorestep b2 ofs).
        destruct Hcorestep as [_ Hold].
        apply Hcodomain_valid in Hf.
        specialize (Hold Hf).
        unfold permission_at in Hperm_obs_weak_data.
        do 2 erewrite restrPermMap_Cur.
        rewrite gssThreadRes.
        rewrite getCurPerm_correct.
        unfold permission_at.
        destruct Hold as [Hfree | Heq].
        * destruct (Hfree Cur) as [Hfreeable Hempty].
          rewrite Hempty.
          destruct ((getThreadR pfcj).1 # b1 ofs); simpl;
            by constructor.
        * rewrite <- Heq.
          rewrite <- restrPermMap_Cur with (Hlt := fst (Hcompc tid pfcj)).
          unfold permission_at.
          pf_cleanup.
            by assumption.
      + do 2 rewrite restrPermMap_Cur.
        erewrite gsoThreadRes with (cntj := pffj); eauto.
        do 2 rewrite restrPermMap_Cur in Hperm_obs_weak_data;
          by assumption.
    - intros b1 b2 Hf.
      erewrite restrPermMap_valid.
      erewrite <- diluteMem_valid.
      specialize (Hcodomain_valid b1 b2 Hf).
      erewrite restrPermMap_valid in Hcodomain_valid.
      eapply ev_step_validblock;
        by eauto.
    - intros b1 b2 ofs Hf.
      specialize (Hperm_obs_weak_lock _ _ ofs Hf).
      clear - Hcorestep Hf Hcodomain_valid Hperm_obs_weak_lock.
      rewrite! restrPermMap_Cur in Hperm_obs_weak_lock.
      do 2 rewrite restrPermMap_Cur.
      destruct (j == tid) eqn:Hjtid; move/eqP:Hjtid=>Hjtid.
      + subst. erewrite gssThreadRes. simpl. pf_cleanup.
        assumption.
      + erewrite gsoThreadRes with (cntj := pffj) by eauto.
        assumption.
  Qed.
  
  Lemma cmachine_step_invariant:
    forall tpc mc tpc' mc' tpc'' mc'' U U' U'' n
      (HstepN: corestepN CoarseSem the_ge n
                         (U, [::], tpc) mc (U', [::],tpc') mc')
      (Hstep: cmachine_step (U', [::], tpc') mc' (U'',[::], tpc'') mc''),
      invariant tpc.
  Proof.
    intros. destruct n; simpl in HstepN. inversion HstepN; subst.
    inversion Hstep; subst; try inversion Htstep; auto.
    inversion Hhalted; simpl in *; subst; auto.
    simpl in *; subst; auto.
    destruct HstepN as [tpc''' [mc''' [Hstep0 _]]].
    clear Hstep.
    inversion Hstep0; subst; try inversion Htstep; auto.
    inversion Hhalted; simpl in *; subst; auto.
    simpl in *; subst; auto.
  Qed.

  (** *** Lemmas about renaming pools [fpool]*)
  Definition updateFP {tpc i} (cnti: containsThread tpc i)
             (fp: fpool tpc) (f' : memren) :=
    fun j cntj => if i == j then f' else fp j cntj.

  Lemma gssFP :
    forall tpc i f' (fp : fpool tpc) (cnti: containsThread tpc i),
      (updateFP cnti fp f') i cnti = f'.
  Proof.
    intros. unfold updateFP.
    rewrite if_true; auto.
  Qed.

  Lemma gsoFP :
    forall tpc i j f' (fp : fpool tpc) (cnti: containsThread tpc i)
      (cntj: containsThread tpc j) (Hneq: i <> j),
      (updateFP cnti fp f') j cntj = fp j cntj.
  Proof.
    intros. unfold updateFP.
    erewrite if_false; auto.
    apply/eqP; auto.
  Qed.

  Definition addFP {tp} (fp: fpool tp) (f': memren) vf arg pmap :
    fpool (addThread tp vf arg pmap).
  Proof.
    refine( fun j cntj =>
              let n := Ordinal cntj in
              match unlift (ordinal_pos_incr (num_threads tp)) n with
              | Some (Ordinal _ cntj') => _
                | None => f'
              end).
    simpl in *.
    eapply (fp n0 cntj').
  Defined.

  Transparent  containsThread.
  Lemma gsoAddFP :
    forall tp fp f vf arg pmap i
      (cnti: containsThread tp i)
      (cnti': containsThread (addThread tp vf arg pmap) i),
      addFP fp f cnti' = fp _ cnti.
  Proof.
    intros.
    unfold addFP in *.
    match goal with
    | [|- match ?Expr with _ => _ end = _] =>
      destruct Expr eqn:Hunlift
    end.
    destruct o. simpl in *.
    apply unlift_m_inv in Hunlift.
    subst. simpl.
    unfold containsThread in cnti.
    simpl in cnti;
      by pf_cleanup.
    exfalso.
    unfold containsThread in *.
    simpl in *.
    assert (Hcontra: (ordinal_pos_incr (num_threads tp))
                       != (Ordinal (n:=(num_threads tp).+1) (m:=i) cnti')).
    { apply/eqP. intros Hcontra.
      unfold ordinal_pos_incr in Hcontra.
      inversion Hcontra; auto. subst.
        by ssromega.
    }
    apply unlift_some in Hcontra. rewrite Hunlift in Hcontra.
    destruct Hcontra;
      by discriminate.
  Qed.

  Lemma gssAddFP:
    forall tp fp f vf arg pmap j
      (Heq: j = latestThread tp)
      (cnt': containsThread (addThread tp vf arg pmap) j),
      addFP fp f cnt' = f.
  Proof.
    intros. subst.
    unfold addFP.
    unfold containsThread in cnt'. simpl in cnt'.
    destruct (unlift (ordinal_pos_incr (num_threads tp))
                     (Ordinal (n:=(num_threads tp).+1)
                              (m:=num_threads tp) cnt')) eqn:H.
    apply unlift_m_inv in H.
    destruct o. simpl in *.
    subst. exfalso;
      ssromega.
    rewrite H.
      by reflexivity.
  Qed.
  Opaque containsThread.

  (** *** Safety and simulation lemmas *)

  (** If some state is [csafe] then it can take a [cmachine_step]*)
  Lemma csafe_internal_step:
    forall tp m i (cnti: containsThread tp i) U n
      (Hn: n > 0)
      (Hinternal: cnti @ I)
      (Hsafe: csafe the_ge (buildSched (i :: U),[::],tp) m n),
    exists tp' m', cmachine_step (buildSched (i :: U), [::], tp) m
                            (buildSched (i :: U), [::], tp') m'.
  Proof.
    intros.
    unfold buildSched in *.
    inversion Hsafe; simpl in *.
    - subst; by exfalso.
    - subst; by exfalso.
    - do 2 eexists; eauto.
    - inversion Hstep; progress subst;
      simpl in *;
      try match goal with
          | [H: ?X :: ?Y = ?Y |- _] =>
            exfalso; eapply list_cons_irrefl; eauto
          end;
      subst; (try by exfalso);
      unfold getStepType in Hinternal; inversion HschedN; subst.
      inversion Htstep; subst.
      pf_cleanup.
      rewrite Hcode in Hinternal.
      simpl in Hinternal.
      rewrite Hat_external in Hinternal;
        by discriminate.
      inversion Htstep; 
      pf_cleanup;
      rewrite Hcode in Hinternal;
      simpl in Hinternal;
        by discriminate.
      inversion Hhalted; subst.
      pf_cleanup.
      rewrite Hcode in Hinternal. simpl in Hinternal.
      destruct (halted SEM.Sem c) eqn:Hhalt; try (by exfalso). 
      destruct (at_external SEM.Sem c);
        by discriminate.
        by exfalso.
  Qed.

  (** Proof of simulation for internal steps*)
  Lemma sim_internal : sim_internal_def.
  Proof.
    unfold sim_internal_def.
    intros.
    inversion Hsim as
        [HnumThreads HmemCompC HmemCompF HsafeC
                     HsimWeak Hfpsep HsimStrong HsimRes
                     HinvF HmaxF Hmemc_wd Htpc_wd Hge_wd Hge_spec Hxs].
    assert (pfc: containsThread tpc i)
      by (eapply HnumThreads; eauto).
    (** Strong simulation for thread i*)
    destruct (HsimStrong i pfc pff)
      as (tpc' &  mc' & Hincr & Hsynced & Hexec & Htsim &
          Hownedi & Hownedi_lp);
      clear HsimStrong.
    assert (pfc': containsThread tpc' i)
      by (clear - Hexec pfc;
           eapply containsThread_internal_execution in pfc; eauto).
    specialize (Htsim pfc').
    (** The coarse machine is also at internal*)
    assert (memCompC' := internal_execution_compatible HmemCompC Hexec).
    specialize (Htsim memCompC').
    assert (Hinternal_pfc': pfc' @ I)
      by (by erewrite (stepType_inj _ _ _ (code_eq Htsim))).
    (** It's safe to step the coarse grained machine for one more step on i*)
    specialize (HsafeC (buildSched [:: i])).
    assert (HcoreN := safety_det_corestepN_internal xs HsafeC Hexec).
    destruct HcoreN as [HcorestepN Hsafety].
    destruct (@csafe_internal_step _ _ _ pfc' _ (fuelF.+2 + size [seq x <- xs | x != i])
                                   ltac:(ssromega) Hinternal_pfc' Hsafety) as
        (tpc'' & mc'' & Hstep').
    assert (HinvC: invariant tpc)
      by (eapply cmachine_step_invariant; eauto).
    apply at_internal_cmachine_step with (cnt := pfc') in Hstep'; eauto.
    destruct Hstep' as [Hcomp [Hstep' _]].  pf_cleanup.
    assert (Hge_incr': ren_incr fg (fp i pfc))
      by (destruct Hge_spec; eapply ren_incr_trans; eauto).
    (** And from this we derive safety for 1 step for FineConc*)
    destruct (tsim_fstep_safe tr HmaxF HinvF Hge_wd (snd Hge_spec)
                              Hge_incr' Htsim Hstep')
      as (tpf' & mf' & fi' & tr' & HstepF & HmaxF' & Hincr' & Hsepi & Htsim'
          & Howned' & Hownedlp').
    assert (HstepF_empty := HstepF empty).
    assert (pfc'': containsThread tpc'' i)
      by (eapply containsThread_internal_step; eauto).
    assert (pff': containsThread tpf' i)
      by (eapply (fstep_containsThread pff); eauto).
    assert (memCompC'': mem_compatible tpc'' mc'').
    eapply internal_step_compatible with (Hcompatible := memCompC'); eauto.
    assert (memCompF': mem_compatible tpf' mf')
      by (eapply fmachine_step_compatible with (pf := pff); eauto).
    exists tpf', mf', (updateFP pfc fp fi'), tr'.
    split.
    (** Proof that the FineConc execution steps *)
    assumption.
    (** Proof that the simulation is preserved*)
    clear HsafeC HcorestepN.
    eapply Build_sim with (mem_compc := HmemCompC) (mem_compf := memCompF').
    - intros k;
      split;
      intro pfk;
      [apply HnumThreads in pfk | apply HnumThreads];
        by eauto with fstep.
    - intros.
      simpl.
      rewrite <- addSnnS.
      apply (safeCoarse Hsim).
    - (** Proof of weak simulation between threads *)
      intros j pfcj pffj'.
      assert (pffj: containsThread tpf j)
        by (eauto with fstep).
      eapply weak_tsim_fstep with (pffi := pff); eauto.
    - (** Proof of seperation of injection pool*)
      (*TODO: comment this proof*)
      intros k j cntk cntj Hkj.
      (** By case anaylis on i == k and i == j*)
      destruct (i == k) eqn:Hik;
        move/eqP:Hik=>Hik;
        try subst k;
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
      + by exfalso.
      + pf_cleanup.
        rewrite gssFP. rewrite gsoFP; auto.
        intros b b' b2 b2' Hf Hf' Hfi' Hfj.
        destruct (fp i pfc b) as [b2''|] eqn:Hfi.
        assert (Heq:b2 = b2'')
          by (apply Hincr' in Hfi; rewrite Hfi in Hfi';
                by inversion Hfi'); subst b2''.
        eapply Hfpsep with (i := i) (j := j) (b := b); eauto.
        unfold ren_separated in Hsepi.
        specialize (Hsepi _ _ Hfi Hfi').
        destruct Hsepi as [HinvalidC' HinvalidF'].
        assert (pfj: containsThread tpf j)
          by (eapply HnumThreads; eauto).
        assert (Hsimj := (simStrong Hsim) j cntj pfj).
        destruct Hsimj as [tpcj' [mc'j [_ [_ [Hexecj [Htsimj _]]]]]].
        assert (pfj': containsThread tpcj' j)
          by (eapply containsThread_internal_execution; eauto).
        assert (HmemCompCj': mem_compatible tpcj' mc'j)
          by (eapply internal_execution_compatible with (tp := tpc); eauto).
        specialize (Htsimj pfj' HmemCompCj').
        assert (Hcodomain := codomain_valid (weak_obs_eq (obs_eq_data Htsimj))).
        specialize (Hcodomain _ _ Hfj).
        erewrite restrPermMap_valid in Hcodomain.
        intros Hcontra. subst.
          by auto.
      + pf_cleanup.
        rewrite gssFP.
        rewrite gsoFP; auto.
        intros b b' b2 b2' Hf Hf' Hfk' Hfj'.
        destruct (fp j cntj b') as [b2''|] eqn:Hfj.
        assert (Heq:b2' = b2'')
          by (apply Hincr' in Hfj; rewrite Hfj in Hfj';
                by inversion Hfj'); subst b2''.
        intros Hcontra.
        eapply Hfpsep with (i := j) (j := k) (b := b') (b' := b) (b2 := b2');
          by eauto.
        unfold ren_separated in Hsepi.
        specialize (Hsepi _ _ Hfj Hfj').
        destruct Hsepi as [HinvalidC' HinvalidF'].
        assert (pffk: containsThread tpf k)
          by (by eapply HnumThreads).
        assert (Hsimk := (simStrong Hsim) k cntk pffk).
        destruct Hsimk as [tpck' [mck' [_ [_ [Hexeck [Htsimk _]]]]]].
        assert (pfck': containsThread tpck' k)
          by (eapply containsThread_internal_execution; eauto).
        assert (HmemCompCk': mem_compatible tpck' mck')
          by (eapply internal_execution_compatible with (tp := tpc); eauto).
        specialize (Htsimk pfck' HmemCompCk').
        assert (Hcodomain := codomain_valid (weak_obs_eq (obs_eq_data Htsimk))).
        specialize (Hcodomain _ _ Hfk').
        erewrite restrPermMap_valid in Hcodomain.
        intros Hcontra. subst. by auto.
      + rewrite gsoFP; auto.
        rewrite gsoFP; eauto.
    - (** Proof of strong simulation between threads*)
      intros j pfcj pffj'.
      destruct (i == j) eqn:Heq; move/eqP:Heq=>Heq.
      { subst j. exists tpc'', mc''.
        pf_cleanup. rewrite gssFP.
        split;
          first by (eapply ren_incr_trans; eauto).
        split.
        intros Hnostep.
        simpl in Hnostep.
        erewrite if_true in Hnostep by (apply eq_refl);
          by discriminate.
        split.
        simpl. erewrite if_true by (apply eq_refl).
        assert (Heq: i :: [seq x <- xs | x == i] =
                     [seq x <- xs | x == i] ++ [:: i]).
        { clear. induction xs. reflexivity.
          simpl. destruct (a==i) eqn:Heq; move/eqP:Heq=>Heq.
          subst. simpl. rewrite IHxs. reflexivity.
          auto.
        }
        rewrite Heq.
        eapply internal_execution_trans;
          by eauto.
        split;
          first by (intros; eapply Htsim').
        split.
        (** Proof of block ownership for threads*)
        intros k pffk' Hik b1 b2 ofs Hfi' Hf.
        assert (pffk: containsThread tpf k)
          by (eauto with fstep).
        erewrite <- gsoThreadR_fstep with (pfj := pffk); eauto.
        destruct (valid_block_dec mc' b1) as [Hvalidmc'b1 | Hinvalidmc'b1].
        (** Case [b1] is a valid block in [mc']*)
        assert (Hfb1 := (domain_valid (weak_obs_eq (obs_eq_data Htsim))) b1).
        erewrite restrPermMap_valid in Hfb1.
        destruct (Hfb1 Hvalidmc'b1) as [b2' Hfi].
        assert (b2' = b2)
          by (apply Hincr' in Hfi; rewrite Hfi in Hfi';
              inversion Hfi'; by subst); subst;
          by eauto.
        (** Case [b1] is an invalid block in [mc']*)
        assert (Hfb1 := (domain_invalid
                           (weak_obs_eq (obs_eq_data Htsim))) b1).
        erewrite restrPermMap_valid in Hfb1.
        specialize (Hfb1 Hinvalidmc'b1);
          by eauto.
        (** Proof of block ownership for lock resources *)
        intros bl ofsl rmap b1 b2 ofs Hfi' Hf Hres.
        erewrite gsoLockRes_fstepI with (tp := tpf) in Hres; eauto.
        destruct (valid_block_dec mc' b1) as [Hvalidmc'b1 | Hinvalidmc'b1].
        assert (Hfb1 := (domain_valid (weak_obs_eq (obs_eq_data Htsim))) b1).
        erewrite restrPermMap_valid in Hfb1.
        destruct (Hfb1 Hvalidmc'b1) as [b2' Hfi].
        assert (b2' = b2)
          by (apply Hincr' in Hfi; rewrite Hfi in Hfi';
              inversion Hfi'; by subst); subst;
          by eauto.
        assert (Hfb1 := (domain_invalid
                           (weak_obs_eq (obs_eq_data Htsim))) b1).
        erewrite restrPermMap_valid in Hfb1.
        specialize (Hfb1 Hinvalidmc'b1).
          by eauto.
      }
      { (** Proof of strong simulation for threads different than i*)
        simpl.
        rewrite gsoFP; auto.
        erewrite if_false by (apply/eqP; intros Hcontra; auto).
        clear HsimWeak Htsim Hincr Hincr'.
        assert (HsimStrong := simStrong Hsim).
        assert (pffj: containsThread tpf j)
          by eauto with fstep.
        destruct (HsimStrong j pfcj pffj)
          as (tpcj' & mcj' & Hincrj & Hsyncedj & Hexecj & Htsimj & Hownedj
              & Hownedj_lp).
        exists tpcj', mcj'. split; auto. split; [ by auto | split; auto].
        split.
        (* difficult part: simulation between tpf' and tpcj' *)
        intros pfcj' memCompCj'.
        specialize (Htsimj pfcj' memCompCj').
        inversion Htsimj as [code_eqjj memObsEqj memObsEqj_locks].
        constructor;
          first by (erewrite <- gsoThreadC_fstepI
                    with (pfj' := pffj') (pfj := pffj); by eauto).
        { (** data mem_obs_eq proof *)
          constructor. (*mem_obs_eq proof*)
          { constructor.
            - apply (domain_invalid (weak_obs_eq memObsEqj)).
            - apply (domain_valid (weak_obs_eq memObsEqj)).
            - assert (Hcodomain := (codomain_valid (weak_obs_eq memObsEqj))).
              intros b1 b2 Hfj.
              specialize (Hcodomain b1 b2 Hfj).
              erewrite restrPermMap_valid.
              erewrite restrPermMap_valid in Hcodomain.
              eapply fstep_valid_block;
                by eauto. 
            - by apply (injective (weak_obs_eq (obs_eq_data Htsimj))).
            - intros b1 b2 ofs.
              rewrite <- permission_at_fstep with
              (ge := the_ge) (Hcomp := (mem_compf Hsim)) (U := empty)
                             (i := i) (pfi := pff)
                             (pfj := pffj) (tr := tr) (tr' := tr')
                                        (Hcomp' := memCompF'); auto.
                by apply (perm_obs_weak (weak_obs_eq memObsEqj)).
          }
          constructor. (*strong_obs_eq proof *)
          { intros b1 b2 ofs.
            rewrite <- permission_at_fstep with
            (Hcomp := (mem_compf Hsim)) (i := i) (U := empty) (ge := the_ge)
                                        (pfi := pff) (tr := tr) (tr' := tr')
                                        (pfj := pffj) (Hcomp' := memCompF'); auto.
              by apply (perm_obs_strong (strong_obs_eq memObsEqj)).
          }
          { intros b1 b2 ofs Hfj Hperm. unfold restrPermMap. simpl.
            assert (Hval := val_obs_eq (strong_obs_eq memObsEqj)).
            specialize (Hval b1 b2 ofs Hfj Hperm).
            unfold restrPermMap in Hval. simpl in Hval.
            assert (Hpermf: Mem.perm (restrPermMap (fst (HmemCompF _ pffj)))
                                     b2 ofs Cur Readable).
            { specialize (HstepF empty).
              assert (Hperm_eqf :=
                        permission_at_fstep Heq pff pffj pffj' HmemCompF memCompF'
                                            Hinternal HstepF b2 ofs).
              unfold permission_at in Hperm_eqf.
              assert (Hperm_weak := (perm_obs_weak (weak_obs_eq memObsEqj) b1
                                                   ofs Hfj)).
              assert (Hperm_strong := (perm_obs_strong (strong_obs_eq memObsEqj))
                                        b1 b2 ofs Hfj).
              clear - Hperm Hperm_eqf Hperm_strong Hperm_weak.
              unfold permission_at in *.
              unfold Mem.perm. rewrite Hperm_strong.
                by auto.
            }
            specialize (HstepF empty).
            erewrite <- fmachine_step_disjoint_val with
            (tp := tpf) (i := i) (j := j) (m' := mf')
                        (m := mf) (tp' := tpf') (U := empty);
              by eauto.
          }
        }
        { (** lock mem_obs_eq proof*)
          constructor. (*mem_obs_eq proof*)
          { constructor.
            - apply (domain_invalid (weak_obs_eq memObsEqj)).
            - apply (domain_valid (weak_obs_eq memObsEqj)).
            - assert (Hcodomain := (codomain_valid (weak_obs_eq memObsEqj))).
              intros b1 b2 Hfj.
              specialize (Hcodomain b1 b2 Hfj).
              erewrite restrPermMap_valid.
              erewrite restrPermMap_valid in Hcodomain.
              eapply fstep_valid_block;
                by eauto. 
            - by apply (injective (weak_obs_eq (obs_eq_locks Htsimj))).
            - intros b1 b2 ofs.
              rewrite !restrPermMap_Cur.
              erewrite <- gsoThreadR_fstep with (pfj := pffj) (pfj' := pffj'); eauto.
              rewrite <- restrPermMap_Cur with (Hlt := snd (memCompCj' j pfcj')).
              rewrite <- restrPermMap_Cur with (Hlt := snd ((mem_compf Hsim) j pffj)).
                by apply (perm_obs_weak (weak_obs_eq memObsEqj_locks)).
          }
          constructor. (*strong_obs_eq proof *)
          { intros b1 b2 ofs.
            rewrite !restrPermMap_Cur.
            erewrite <- gsoThreadR_fstep with (pfj := pffj) (pfj' := pffj'); eauto.
            rewrite <- restrPermMap_Cur with (Hlt := snd (memCompCj' j pfcj')).
            rewrite <- restrPermMap_Cur with (Hlt := snd ((mem_compf Hsim) j pffj)).
              by apply (perm_obs_strong (strong_obs_eq memObsEqj_locks)).
          }
          { intros b1 b2 ofs Hfj Hperm. unfold restrPermMap. simpl.
            assert (Hval := val_obs_eq (strong_obs_eq memObsEqj_locks)).
            specialize (Hval b1 b2 ofs Hfj Hperm).
            unfold restrPermMap in Hval. simpl in Hval.
            assert (Hpermf: Mem.perm (restrPermMap (snd (HmemCompF _ pffj)))
                                     b2 ofs Cur Readable).
            { specialize (HstepF empty).
              assert (Hperm_eqf :=
                        permission_at_fstep Heq pff pffj pffj' HmemCompF memCompF'
                                            Hinternal HstepF b2 ofs).
              unfold permission_at in Hperm_eqf.
              assert (Hperm_weak := (perm_obs_weak (weak_obs_eq memObsEqj_locks) b1
                                                   ofs Hfj)).
              assert (Hperm_strong := (perm_obs_strong (strong_obs_eq memObsEqj_locks))
                                        b1 b2 ofs Hfj).
              clear - Hperm Hperm_eqf Hperm_strong Hperm_weak.
              unfold permission_at in *.
              unfold Mem.perm. rewrite Hperm_strong.
                by auto.
            }
            specialize (HstepF empty).
            erewrite <- fmachine_step_disjoint_val with
            (tp := tpf) (i := i) (j := j) (m' := mf')
                        (m := mf) (tp' := tpf') (U := empty);
              by eauto.
          }
        }
        (** block ownership *)
        split.
        intros k pffk' Hjk b1 b2 ofs Hfj Hf.
        assert (pffk: containsThread tpf k)
          by (eapply fstep_containsThread'; eauto).
        specialize (Hownedj _ pffk Hjk b1 b2 ofs Hfj Hf).
        destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
        (** case k is thread i*)
        subst k.
        assert (pfcj': containsThread tpcj' j)
          by (eapply containsThread_internal_execution; eauto).
        assert (Hcompcj': mem_compatible tpcj' mcj')
          by (eapply internal_execution_compatible with (tp := tpc) (m := mc);
               eauto).
        specialize (Htsimj pfcj' Hcompcj').
        assert (Hcodomain := (codomain_valid (weak_obs_eq
                                                (obs_eq_data Htsimj)))).
        specialize (Hcodomain _ _ Hfj).
        erewrite restrPermMap_valid in Hcodomain.
        clear - Hownedj Hcodomain Hjk HstepF_empty Hinternal HmemCompF.
        absurd_internal HstepF_empty;
          try by erewrite gThreadCR with (cntj := Htid).
        apply ev_step_ax1 in Hcorestep.
        apply corestep_decay in Hcorestep.
        destruct (Hcorestep b2 ofs) as [_ Hdecay_valid].
        assert (Hp := restrPermMap_Cur (fst (HmemCompF _ Htid)) b2 ofs).
        unfold permission_at in Hp.
        destruct (Hdecay_valid Hcodomain) as [Hnew | Hstable].
        destruct (Hnew Cur) as [Hcontra _].
        rewrite Hp in Hcontra.
        destruct Hownedj;
          by congruence.
        specialize (Hstable Cur).
        rewrite Hp in Hstable.
        destruct Hownedj as [Hownedj1 Hownedj2].
        rewrite Hownedj1 in Hstable.
        erewrite gssThreadRes.
        rewrite getCurPerm_correct;
          by auto.
        (** case k is another thread*)
        erewrite <- gsoThreadR_fstep with (pfi := pff) (pfj := pffk);
          by eauto.
        (** block ownership for lockres*)
        intros bl ofsl rmap b1 b2 ofs Hfj Hf Hres.
        erewrite gsoLockRes_fstepI with (tp := tpf) in Hres;
          by eauto.
      }
      { (** lock resources sim*)
        destruct HsimRes as [HsimRes [Hlock_mapped Hlock_if]].
        split.
        - intros.
          assert (Hl_eq := gsoLockRes_fstepI pff Hinternal HstepF_empty).
          assert (Hl2': lockRes tpf (bl2, ofs) = Some rmap2)
            by (rewrite <- Hl_eq; assumption).
          destruct (HsimRes _ _ _ _ _ Hf Hl1 Hl2') as [HsimRes1 HsimRes2].
          split.
          + destruct HsimRes1 as [HpermRes1 HvalRes1].
            constructor.
            intros b1 b2 ofs0 Hf1.
            do 2 rewrite restrPermMap_Cur.
            specialize (HpermRes1 _ _ ofs0 Hf1);
              by do 2 rewrite restrPermMap_Cur in HpermRes1.
            intros b1 b2 ofs0 Hf1 Hperm.
            simpl in *.
            specialize (HvalRes1 _ _ ofs0 Hf1 Hperm).
            assert (HpermF: Mem.perm (restrPermMap (fst (compat_lp HmemCompF (bl2,ofs) Hl2')))
                                     b2 ofs0 Cur Readable).
            { unfold Mem.perm in *.
              specialize (HpermRes1 _ _ ofs0 Hf1).
              unfold permission_at in HpermRes1.
                by rewrite HpermRes1.
            }
            absurd_internal HstepF_empty; auto.
            apply ev_step_ax1 in Hcorestep.
            erewrite <- corestep_disjoint_val_lockpool with (m := mf) (m' := m');
              by (simpl; eauto).
          + destruct HsimRes2 as [HpermRes2 HvalRes2].
            constructor.
            intros b1 b2 ofs0 Hf1.
            do 2 rewrite restrPermMap_Cur.
            specialize (HpermRes2 _ _ ofs0 Hf1);
              by do 2 rewrite restrPermMap_Cur in HpermRes2.
            intros b1 b2 ofs0 Hf1 Hperm.
            simpl in *.
            specialize (HvalRes2 _ _ ofs0 Hf1 Hperm).
            assert (HpermF: Mem.perm (restrPermMap (snd (compat_lp HmemCompF (bl2,ofs) Hl2')))
                                     b2 ofs0 Cur Readable).
            { unfold Mem.perm in *.
              specialize (HpermRes2 _ _ ofs0 Hf1).
              unfold permission_at in HpermRes2.
                by rewrite HpermRes2.
            }
            absurd_internal HstepF_empty; auto.
            apply ev_step_ax1 in Hcorestep.
            erewrite <- corestep_disjoint_val_lockpool with (m := mf) (m' := m');
              by (simpl; eauto).
            split.
            intros bl2 ofs Hres.
            erewrite gsoLockRes_fstepI with (tp := tpf) (tp' := tpf') in Hres; eauto.
            intros bl1 bl2 ofs Hf.
            erewrite gsoLockRes_fstepI with (tp' := tpf'); eauto.
      }
      { (*invariant tpf' *)
        eapply fmachine_step_invariant with (tp := tpf); eauto.
      }
      { assumption. }
      { assumption. }
      { assumption. }
      { assumption. }
      { assumption. }
      { intros j Hin.
        inversion Hin; subst;
          by auto.
      }
      Unshelve. auto.
  Qed.
  
  (** ** Proof of simulation for stop steps *)

  (*TODO : move this*)
  Lemma filter_neq_eq :
    forall {A :eqType} (xs : seq A) i j (Hneq: i <> j),
      [seq x <- [seq x <- xs | x != i] | x == j] = [seq x <- xs | x == j].
  Proof.
    intros. induction xs.
    - reflexivity.
    - simpl. destruct (a != i) eqn:Hai; move/eqP:Hai=>Hai.
      simpl.
      destruct (a ==j) eqn:Haj; move/eqP:Haj=>Haj;
        [by apply f_equal | assumption].
      subst. erewrite if_false by (apply/eqP; auto).
      assumption.
  Qed.
  
  Lemma suspend_step_inverse:
    forall i U U' tpc tpc' mc mc'
      (cnt: containsThread tpc i)
      (Hsuspend: cnt @ S)
      (Hstep: cmachine_step (i :: U, [::], tpc) mc (U', [::], tpc') mc'),
      U = U' /\ mc = mc' /\ mem_compatible tpc mc /\
      DryConc.suspend_thread cnt tpc'.
  Proof.
    intros.
    inversion Hstep; simpl in *; subst; inversion HschedN; subst;
    try (inversion Htstep || inversion Hhalted); subst; pf_cleanup;
    unfold getStepType in Hsuspend;
    try rewrite Hcode in Hsuspend; simpl in Hsuspend;
    try match goal with
        | [H: match ?Expr with _ => _ end = _, H2: ?Expr = _ |- _] =>
          rewrite H2 in H
        end; try discriminate;
    try match goal with
        | [H: ~ containsThread _ _, H2: containsThread _ _ |- _] =>
          exfalso; by auto
        | [H: is_true (isSome (@halted _ _ _ _ _))  |- _] => 
          destruct (at_external_halted_excl SEM.Sem c) as [Hnot_ext | Hcontra];
            [rewrite Hnot_ext in Hsuspend;
              destruct (halted SEM.Sem c); discriminate |
             rewrite Hcontra in Hcant; by auto]
        end.
    destruct (at_external SEM.Sem c) eqn:Hat_external.
    apply ev_step_ax1 in Hcorestep.
    apply corestep_not_at_external in Hcorestep.
    rewrite Hcorestep in Hat_external;
      by discriminate.
    destruct (halted SEM.Sem c); by discriminate.
      split; by auto.
  Qed.

  Lemma strong_tsim_step:
    forall tp1 tp2 tp1' m1 m2 m1' j f fg
      (pf1j: containsThread tp1 j)
      (pf1j': containsThread tp1' j)
      (Hcomp1: mem_compatible tp1 m1)
      (Hcomp1': mem_compatible tp1' m1')
      (Hinv: invariant tp1')
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg the_ge)
      (Hge_incr: ren_incr fg f)
      (Hsim: strong_tsim f pf1j pf1j' Hcomp1 Hcomp1')
      (Hstep: internal_step pf1j Hcomp1 tp2 m2),
    exists tp2' m2' f',
      internal_step pf1j' Hcomp1' tp2' m2' /\
      ren_incr f f' /\
      ren_separated f f' m1 m1' /\
      ((exists p, ((Mem.nextblock m2 = Mem.nextblock m1 + p)%positive /\
              (Mem.nextblock m2' = Mem.nextblock m1' + p)%positive))
       \/ ((Mem.nextblock m2 = Mem.nextblock m1) /\
          (Mem.nextblock m2' = Mem.nextblock m1'))) /\
      (forall b,
          Mem.valid_block m2' b ->
          ~ Mem.valid_block m1' b ->
          let bz := ((Zpos b) - ((Zpos (Mem.nextblock m1')) -
                                 (Zpos (Mem.nextblock m1))))%Z in
          f' (Z.to_pos bz) = Some b /\
          f (Z.to_pos bz) = None) /\
      (exists (pf2j: containsThread tp2 j)
         (pf2j': containsThread tp2' j)
         (Hcomp2: mem_compatible tp2 m2)
         (Hcomp2': mem_compatible tp2' m2'),
          strong_tsim f' pf2j pf2j' Hcomp2 Hcomp2') /\
      (Mem.nextblock m1 = Mem.nextblock m1' ->
       (forall b1 b2 : block, f b1 = Some b2 -> b1 = b2) ->
       forall b1 b2 : block, f' b1 = Some b2 -> b1 = b2).
  Proof.
    intros.
    inversion Hstep as [[? Hcstep] | [[Hresume ?] | [Hstart ?]]].
    - inversion Hcstep; subst.
      inversion Hsim as [Hcode_eq Hmem_obs_eq Hmem_obs_locks].
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pf1j') as [c1' | | |] eqn:Hcodej'; try by exfalso.
      apply ev_step_ax1 in Hcorestep.
      assert (H := corestep_obs_eq _ _ Hmem_obs_eq Hcode_eq Hfg Hge_wd
                                   Hge_incr Hcorestep).
      destruct H
        as (c2' & m2' & f' & Hcorestep' & Hcode_eq'
            & Hobs_eq & Hincr & Hseparated
            & Hnextblock & Hinverse & Hid).
      exists (updThread pf1j' (Krun c2') (getCurPerm m2', (getThreadR pf1j').2)), m2', f'.
      eapply ev_step_ax2 in Hcorestep'.
      destruct Hcorestep' as [evF Hcorestep'].
      assert (Hinternal':
                internal_step pf1j' Hcomp1'
                              (updThread pf1j' (Krun c2') (getCurPerm m2', (getThreadR pf1j').2)) m2')
        by (left; eexists; econstructor; eauto).
      split; first by assumption.
      split; first by assumption.
      split; first by assumption.
      split; first by assumption.
      split; first by assumption.
      split.
      { assert (pf2j := containsThread_internal_step Hstep pf1j).
        assert (pf2j' := containsThread_internal_step Hinternal' pf1j').
        assert (Hcomp2 := internal_step_compatible Hstep).
        assert (Hcomp2' := internal_step_compatible Hinternal').
        exists pf2j, pf2j', Hcomp2, Hcomp2'.
        constructor; first by do 2 rewrite gssThreadCode.
        - destruct Hobs_eq as [[Hinvalid' Hvalid' ? ? Hweak_perm] [Hstrong_perm Hval]].
          constructor.
          + (*weak_mem_obs_eq proof*)
            constructor.
            * intros b Hinvalid;
                erewrite restrPermMap_valid in Hinvalid;
                  by eauto. 
            * intros b Hvalid;
                erewrite restrPermMap_valid in Hvalid;
                  by eauto.
            * eauto.
            * eauto. 
            * intros b1 b2 ofs Hf';
                do 2 rewrite restrPermMap_Cur;
                do 2 rewrite gssThreadRes;
                do 2 rewrite getCurPerm_correct;
                  by eauto.
          +(* strong_perm proof *)
            constructor.
            * intros b1 b2 ofs Hf'.
              do 2 rewrite restrPermMap_Cur;
                do 2 rewrite gssThreadRes;
                do 2 rewrite getCurPerm_correct;
                  by eauto.
            * (* val proof *)
              intros b1 b2 ofs Hf' Hreadable.
              simpl.
              eapply Hval; eauto.
              unfold Mem.perm in *.
              assert (H:= restrPermMap_Cur (fst (Hcomp2 j pf2j)) b1 ofs).
              unfold permission_at in H.
              rewrite H in Hreadable.
              rewrite gssThreadRes in Hreadable;
                rewrite getCurPerm_correct in Hreadable.
                by assumption.
        - subst.
          assert (Hlt: permMapLt (getThreadR pf2j).2 (getMaxPerm m1))
            by (rewrite gssThreadRes; simpl; destruct Hcomp1; destruct (compat_th0 _ pf1j); eauto).
          assert (Hlt': permMapLt (getThreadR pf2j').2 (getMaxPerm m1'))
            by (rewrite gssThreadRes; simpl; destruct Hcomp1'; destruct (compat_th0 _ pf1j'); eauto).
          constructor.
          (* dependent types mumbo-jumbo*)
          pose proof (weak_obs_eq Hmem_obs_locks) as Hobs_weak_locks.
          erewrite restrPermMap_irr' with (Hlt' := Hlt) in Hobs_weak_locks by (rewrite gssThreadRes; simpl; auto).
          erewrite restrPermMap_irr' with (Hlt' := Hlt') in Hobs_weak_locks by (rewrite gssThreadRes; simpl; auto).
          (* apply the lemma *)
          eapply weak_mem_obs_eq_restrEq with (Hlt := Hlt) (HltF := Hlt'); eauto.
          now eapply (weak_obs_eq Hobs_eq).
          (** proof of strong_mem_obs_eq*)
          erewrite restrPermMap_irr' with (Hlt' := Hlt) in Hmem_obs_locks by (rewrite gssThreadRes; simpl; auto).
          erewrite restrPermMap_irr' with (Hlt' := Hlt') in Hmem_obs_locks by (rewrite gssThreadRes; simpl; auto).
          eapply strong_mem_obs_eq_disjoint_step; eauto.
          (* stability of contents of DryConc *)
          intros.
          eapply corestep_stable_val with (Hlt2 := Hlt); eauto.
          rewrite gssThreadRes; simpl; right;
            by (eapply (fst ((thread_data_lock_coh Hinv0) _ pf1j) _ pf1j)).
          (* stability of contents of FineConc *)
          intros.
          simpl.
          apply ev_step_ax1 in Hcorestep'.
          eapply corestep_stable_val with (Hlt2 := Hlt'); eauto.
          rewrite gssThreadRes; simpl; right;
            by (eapply (fst ((thread_data_lock_coh Hinv) _ pf1j') _ pf1j')).
      }
      do 2 erewrite restrPermMap_nextblock in Hid;
        by eauto.
    - (* Case internal step is a resume or start step*)
      subst m2.
      inversion Hsim as [Hcode_eq Hmem_obs_eq].
      inversion Hresume; subst.
      pf_cleanup.
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pf1j') as [ | |c1'|] eqn:Hcode'; try by exfalso.
      destruct Hcode_eq as [Hcode_eq Hval_eq].
      inversion Hval_eq; subst.
      assert (Hat_external_spec := core_inj_ext Hcode_eq).
      rewrite Hat_external in Hat_external_spec.
      destruct X as [[? ?] vs].
      destruct (at_external SEM.Sem c1') as [[[? ?] ?] | ] eqn:Hat_external';
        try by exfalso.
      destruct Hat_external_spec as [? [? ?]]; subst.
      assert (Hvalid_val: match (Some (Vint Int.zero)) with
                          | Some v1 => valid_val f v1
                          | None => True
                          end)
        by (by simpl).
      assert (Hafter_external' :=
                core_inj_after_ext (Some (Vint Int.zero)) 
                                   Hcode_eq Hvalid_val Hafter_external).
      destruct Hafter_external' as [ov2 [c2' [Hafter_external'
                                                [Hcore_inj' Hval_obs]]]].
      destruct ov2 as [? |]; try by exfalso.
      inversion Hval_obs; subst.
      exists (updThreadC pf1j' (Krun c2')), m1', f.
      assert (Hinternal':
                internal_step pf1j' Hcomp1' (updThreadC pf1j' (Krun c2')) m1')
        by ( clear - Hat_external' Hafter_external' Hcode' Hinv;
             right; left; split; econstructor; eauto).
      split;
        first by assumption.
      split; first by auto.
      split; first by congruence.
      split; first by auto.
      split; first by
          (intros; by exfalso).
      split; try by eauto.
      assert (pf2j := containsThread_internal_step Hstep pf1j).
      assert (pf2j' := containsThread_internal_step Hinternal' pf1j').
      assert (Hcomp2 := internal_step_compatible Hstep).
      assert (Hcomp2' := internal_step_compatible Hinternal').
      exists pf2j, pf2j', Hcomp2, Hcomp2'.
      constructor; first by do 2 rewrite gssThreadCC.
      (** since permission maps and memories do not change by these steps, [mem_obs_eq] is reestabhlised easily*)
      erewrite restrPermMap_irr' with (Hlt' := fst (Hcomp1 j pf1j)) by (rewrite gThreadCR; eauto).
      erewrite restrPermMap_irr' with (Hlt' := fst (Hcomp1' j pf1j')) by (rewrite gThreadCR; eauto);
        by eauto.
      erewrite restrPermMap_irr' with (Hlt' := snd (Hcomp1 j pf1j)) by (rewrite gThreadCR; eauto).
      erewrite restrPermMap_irr' with (Hlt' := snd (Hcomp1' j pf1j')) by (rewrite gThreadCR; eauto);
        by eauto.
    - (*case it's a start step*)      
      subst m2.
      inversion Hsim as [Hcode_eq Hmem_obs_eq].
      inversion Hstart; subst.
      pf_cleanup.
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pf1j') as [| | |vf' arg'] eqn:Hcode'; try by exfalso.
      destruct Hcode_eq as [Hvf Harg_obs].
      assert (Harg_obs_list: val_obs_list f [:: arg] [:: arg'])
        by (constructor; auto; constructor).
      assert (HinitF := core_inj_init Harg_obs_list Hvf Hfg Hge_wd
                                      Hge_incr Hinitial).
      destruct HinitF as [c_newF [HinitialF Hcode_eq]].
      exists (updThreadC pf1j' (Krun c_newF)), m1', f.
      assert (Hinternal':
                internal_step pf1j' Hcomp1' (updThreadC pf1j' (Krun c_newF)) m1')
        by ( clear - Hcode' Hinv HinitialF;
             right; right; split; econstructor; eauto).
      split;
        first by assumption.
      split; first by auto.
      split; first by congruence.
      split; first by auto.
      split; first by
          (intros; by exfalso).
      split; try by eauto.
      assert (pf2j := containsThread_internal_step Hstep pf1j).
      assert (pf2j' := containsThread_internal_step Hinternal' pf1j').
      assert (Hcomp2 := internal_step_compatible Hstep).
      assert (Hcomp2' := internal_step_compatible Hinternal').
      exists pf2j, pf2j', Hcomp2, Hcomp2'.
      constructor; first by do 2 rewrite gssThreadCC.
      (** since permission maps and memories do not change by these steps, [mem_obs_eq] is reestabhlised easily*)
      erewrite restrPermMap_irr' with (Hlt' := fst (Hcomp1 j pf1j)) by (rewrite gThreadCR; eauto).
      erewrite restrPermMap_irr' with (Hlt' := fst (Hcomp1' j pf1j')) by (rewrite gThreadCR; eauto);
        by eauto.
      erewrite restrPermMap_irr' with (Hlt' := snd (Hcomp1 j pf1j)) by (rewrite gThreadCR; eauto).
      erewrite restrPermMap_irr' with (Hlt' := snd (Hcomp1' j pf1j')) by (rewrite gThreadCR; eauto);
        by eauto.
  Qed.

  Lemma strong_tsim_execution:
    forall tp1 tp2 tp1' m1 m2 m1' j xs f fg
      (pf1j: containsThread tp1 j)
      (pf1j': containsThread tp1' j)
      (Hcomp1: mem_compatible tp1 m1)
      (Hcomp1': mem_compatible tp1' m1')
      (Hinv: invariant tp1')
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg the_ge)
      (Hge_incr: ren_incr fg f)
      (Hsim: strong_tsim f pf1j pf1j' Hcomp1 Hcomp1')
      (Hexec: internal_execution [seq x <- xs | x == j] tp1 m1 tp2 m2),
    exists tp2' m2' f',
      internal_execution [seq x <- xs | x == j] tp1' m1' tp2' m2' /\
      ren_incr f f' /\
      ren_separated f f' m1 m1' /\
      ((exists p, ((Mem.nextblock m2 = Mem.nextblock m1 + p)%positive /\
              (Mem.nextblock m2' = Mem.nextblock m1' + p)%positive))
       \/ ((Mem.nextblock m2 = Mem.nextblock m1) /\
          (Mem.nextblock m2' = Mem.nextblock m1'))) /\
      (forall b,
          Mem.valid_block m2' b ->
          ~ Mem.valid_block m1' b ->
          let bz := ((Zpos b) - ((Zpos (Mem.nextblock m1')) -
                                 (Zpos (Mem.nextblock m1))))%Z in
          f' (Z.to_pos bz) = Some b /\
          f (Z.to_pos bz) = None) /\
      (exists (pf2j: containsThread tp2 j)
         (pf2j': containsThread tp2' j)
         (Hcomp2: mem_compatible tp2 m2)
         (Hcomp2': mem_compatible tp2' m2'),
          strong_tsim f' pf2j pf2j' Hcomp2 Hcomp2') /\
      (Mem.nextblock m1 = Mem.nextblock m1' ->
       (forall b1 b2 : block, f b1 = Some b2 -> b1 = b2) ->
       forall b1 b2 : block, f' b1 = Some b2 -> b1 = b2).
  Proof.
    intros.
    generalize dependent tp1.
    generalize dependent m1.
    generalize dependent f.
    generalize dependent tp1'. generalize dependent m1'.
    induction xs as [|x xs]; simpl; intros.
    - inversion Hexec; subst.
      exists tp1', m1', f.
      split; first by constructor.
      split; first by auto.
      split; first by congruence.
      split; first by auto.
      split; first by (intros; by exfalso).
      split; by eauto.
      simpl in HschedN;
        by inversion HschedN.
    - destruct (x == j) eqn:Hxj; move/eqP:Hxj=>Hxj.
      + subst x. inversion Hexec as [|tid U U' tp1a m1a tp0 m0].
        subst U U' tp1a m1a tp'' m''.
        simpl in Htrans. simpl in HschedN;
          inversion HschedN; subst tid; clear HschedN Hexec.
        pf_cleanup.
        assert (Htsim := strong_tsim_step Hinv Hfg Hge_wd Hge_incr Hsim Hstep).
        destruct Htsim as
            (tp0' & m0' & f0 & Hstep0' & Hincr0' & Hsep0'
             & Hnextblock0' & Hinverse0' & Htsim0' & Hid0').
        destruct Htsim0' as [pfj' [pfj0' [Hcomp' [Hcomp0' Htsim0]]]].
        pf_cleanup.
        assert (Hinv0': invariant tp0')
          by (eapply internal_step_invariant; eauto).
        assert (Hge_incr0': ren_incr fg f0)
          by (eapply ren_incr_trans; eauto).
        destruct (IHxs _ _ _ _ Hinv0' _ Hge_incr0' _ _ _ _ Htsim0 Htrans)
          as (tp2' & m2' & f2' & Hexec & Hincr2 & Hsep2
             & Hnextblock2 & Hinverse2 & Hsim2 & Hid2);
          exists tp2', m2', f2'.
        destruct Hsim2 as [pf2j [pf2j' [Hcomp2 [Hcomp2' Htsim2]]]].
        split; first by (econstructor; simpl; eauto).
        split; first by (eapply ren_incr_trans; eauto).
        split.
        { (*injection separated *)
          intros b1 b2 Hf Hf2'.
          unfold ren_separated in *.
          destruct (valid_block_dec m0 b1) as [Hvalidm0 | Hinvalidm0].
          * apply (domain_valid (weak_obs_eq (obs_eq_data Htsim0))) in Hvalidm0.
            destruct Hvalidm0 as [x Hf0].
            assert (b2 = x).
            {  assert (Hf2'' : f2' b1 = Some x)
                by (eapply Hincr2; eauto).
               rewrite Hf2' in Hf2''. inversion Hf2''; by subst. }
            subst x.
            eapply Hsep0';
              by eauto.
          * apply (domain_invalid (weak_obs_eq (obs_eq_data Htsim0))) in Hinvalidm0.
            destruct (Hsep2 _ _ Hinvalidm0 Hf2') as [Hinvalid Hinvalidm0'].
            split;
              intros Hcontra;
              eapply internal_step_valid in Hcontra; eauto.
        }
        split.
        { (*Nextblock*)
          destruct Hnextblock0' as [[p0 [Hnextblock0 Hnextblock0']]
                                   | [Hnextblock0 Hnextblock0']];
          destruct Hnextblock2 as [[p2 [Hnextblock2 Hnextblock2']]
                                  | [Hnextblock2 Hnextblock2']];
          clear - Hnextblock0 Hnextblock0' Hnextblock2 Hnextblock2';
          rewrite Hnextblock2 Hnextblock2';
          rewrite Hnextblock0 Hnextblock0'.
          - left. exists (p0+p2)%positive.
            split; by rewrite Pos.add_assoc.
          - left;
            exists p0; by split.
          - left; exists p2;
              by split.
          - right; by split.
        } split.
        { (*inverse, TODO: sketch proof *)
          clear - Hinverse2 Hinverse0' Hincr2 Hincr0' Hnextblock0' Hnextblock2.
          intros b Hvalidm2' Hinvalidm1'.
          destruct (valid_block_dec m0' b) as [Hvalidm0' | Hinvalidm0'].
          - specialize (Hinverse0' _ Hvalidm0' Hinvalidm1').
            simpl in Hinverse0'.
            destruct Hinverse0' as [Hf0 Hf].
            apply Hincr2 in Hf0. by split.
          - specialize (Hinverse2 _ Hvalidm2' Hinvalidm0').
            simpl in Hinverse2.
            destruct Hinverse2 as [Hf2' Hf0].
            (* NOTE: axiom on nextblock is used for the difference here*)
            assert (Heq: ((Z.pos (Mem.nextblock m1') - Z.pos (Mem.nextblock m1)) =
                          Z.pos (Mem.nextblock m0') - Z.pos(Mem.nextblock m0))%Z).
            { clear - Hnextblock0'.
              destruct Hnextblock0' as [[p0 [Hnextblock0 Hnextblock0']]
                                       | [Hnextblock0 Hnextblock0']];
                rewrite Hnextblock0 Hnextblock0';
                [do 2 rewrite Pos2Z.inj_add;
                  rewrite Zminus_plus_simpl_r;
                    by reflexivity | by reflexivity].
            }
            simpl in *.
            rewrite <- Heq in Hf2', Hf0.
            split; first by assumption.
            match goal with
            | [|- ?Expr = None] =>
              destruct Expr as [?|] eqn:Hf
            end;
              [apply Hincr0' in Hf; by congruence | trivial].
        }
        split; first by eauto.
        intros Hnb1 Hf.
        specialize (Hid0' Hnb1 Hf).
        assert (Hnb0: Mem.nextblock m0 = Mem.nextblock m0')
          by (destruct Hnextblock0' as [[p [Hnb0 Hnb0']] | [Hnb0 Hnb0']];
                by rewrite Hnb0 Hnb0' Hnb1).
        specialize (Hid2 Hnb0 Hid0').
          by assumption.
    - destruct (IHxs _ _ _ _ Hinv f Hge_incr _ _ _ _ Hsim Hexec)
        as
          [tp2' [m2' [f2' [Hexec2
                             [Hincr2
                                [Hsep2 [Hnextblock2 [Hinverse2 [Hsim2 Hid2]]]]]]]]];
      exists tp2', m2', f2'.
      repeat (split; auto).
  Qed.
  
  Lemma strong_tsim_stop:
    forall tpc tpc' tpf mc mc' mf i fi
      (pfc: containsThread tpc i) (pff: containsThread tpf i)
      (Hcompc: mem_compatible tpc mc) (Hcompf: mem_compatible tpf mf)
      (HinvF: invariant tpf)
      (Hstrong_sim: strong_tsim fi pfc pff Hcompc Hcompf)
      (Hstep: cmachine_step (buildSched [:: i], [::], tpc) mc (empty, [::], tpc') mc')
      (Hsuspend: pfc @ S),
    exists tpf',
      FineConc.suspend_thread pff tpf' /\
      forall (Hcompc': mem_compatible tpc' mc') (Hcompf' : mem_compatible tpf' mf)
        (pfc': containsThread tpc' i) (pff': containsThread tpf' i),
        strong_tsim fi pfc' pff' Hcompc' Hcompf'.
  Proof.
    intros.
    inversion Hstep; simpl in *; subst; inversion HschedN; subst;
    try (inversion Htstep || inversion Hhalted); subst; pf_cleanup;
    unfold getStepType in Hsuspend;
    try rewrite Hcode in Hsuspend; simpl in Hsuspend;
    try match goal with
        | [H: match ?Expr with _ => _ end = _, H2: ?Expr = _ |- _] =>
          rewrite H2 in H
        end; try discriminate;
    try match goal with
        | [H: ~ containsThread _ _, H2: containsThread _ _ |- _] =>
          exfalso; by auto
        | [H: is_true (isSome (@halted _ _ _ _ _))  |- _] => 
          destruct (at_external_halted_excl SEM.Sem c) as [Hnot_ext | Hcontra];
            [rewrite Hnot_ext in Hsuspend;
              destruct (halted SEM.Sem c); discriminate |
             rewrite Hcontra in Hcant; by auto]
        end.
    destruct Hstrong_sim as [Hcode_eq memObsEq].
    rewrite Hcode in Hcode_eq.
    simpl in Hcode_eq.
    destruct (getThreadC pff) as [c'| | |] eqn:Hcode';
      try by exfalso.
    assert (Hat_external_spec := core_inj_ext Hcode_eq).
    rewrite Hat_external in Hat_external_spec.
    destruct X as [[? ?] ?].
    destruct (at_external SEM.Sem c') as [[[? ?] ?]|] eqn:Hat_external';
      try by exfalso.
    destruct Hat_external_spec as [? [? ?]]; subst.
    exists (updThreadC pff (Kblocked c')).
    split; first by (econstructor; eauto).
    intros.
    constructor;
      first by do 2 rewrite gssThreadCC.
    erewrite restrPermMap_irr' with
    (Hlt := fst (Hcompc' tid pfc')) (Hlt' := fst (Hcmpt tid Htid))
      by (erewrite gThreadCR with (cntj := Htid); reflexivity).
    erewrite restrPermMap_irr' with
    (Hlt := fst (Hcompf' tid pff')) (Hlt' := fst (Hcompf tid pff))
      by (erewrite gThreadCR with (cntj := pff); reflexivity);
      by assumption.
    erewrite restrPermMap_irr' with
    (Hlt := snd (Hcompc' tid pfc')) (Hlt' := snd (Hcmpt tid Htid))
      by (erewrite gThreadCR with (cntj := Htid); reflexivity).
    erewrite restrPermMap_irr' with
    (Hlt := snd (Hcompf' tid pff')) (Hlt' := snd (Hcompf tid pff))
      by (erewrite gThreadCR with (cntj := pff); reflexivity);
      by assumption.
  Qed.
 
  (** Stepping on thread i with internal steps and then a suspend step
  retains a strong simulation with the id injection on all other
  threads*)
  Lemma strong_tsim_id :
    forall tp tp' tp'' m m' i j xs f fg
      (Hij: i <> j)
      (pfj: containsThread tp j)
      (pfj': containsThread tp' j)
      (pfj'': containsThread tp'' j)
      (pfi': containsThread tp' i)
      (Hmem_wd: valid_mem m)
      (Hdomain: domain_memren f m)
      (Htp_wd: tp_wd f tp)
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg the_ge)
      (Hcomp: mem_compatible tp m)
      (Hcomp'': mem_compatible tp'' m')
      (Hsuspend: DryConc.suspend_thread pfi' tp'')
      (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m'),
      strong_tsim (id_ren m) pfj pfj'' Hcomp Hcomp''.
  Proof.
    intros.
    assert (Hdomain_id: domain_memren (id_ren m) m)
      by (apply id_ren_domain).
    assert (Htp_wd_id: tp_wd (id_ren m) tp)
      by (eapply tp_wd_domain; eauto).
    assert (Hid := id_ren_correct m).
    assert (Heq: (getThreadR pfj) = (getThreadR pfj''))
      by (erewrite gsoThreadR_execution with (pfj' := pfj') by eauto;
          erewrite gsoThreadR_suspendC with (cntj' := pfj'') by eauto;
          reflexivity).
    constructor.
    - (* cores are related*)
      assert (Hcore := gsoThreadC_suspendC pfj' pfj'' Hij Hsuspend).
      rewrite <- Hcore.
      erewrite <- gsoThreadC_exec with (pfj := pfj) (pfj' := pfj'); eauto.
      specialize (Htp_wd_id _ pfj).
      eapply ctl_inj_id;
        by eauto.
    - (** [mem_obs_eq] for data *)
      assert (Hlt : permMapLt ((getThreadR pfj'').1) (getMaxPerm m))
        by (rewrite <- Heq; by  (eapply (fst (Hcomp _ pfj)))).
      assert (mem_obs_eq (id_ren m) (restrPermMap (fst (Hcomp j pfj))) (restrPermMap (fst (Hcomp j pfj))))
        by (erewrite id_ren_restr with (Hlt := (Hcomp j pfj).1); apply mem_obs_eq_id; eauto).
      erewrite restrPermMap_irr' with (Hlt' := Hlt) in H at 2 by (rewrite Heq; auto).
      eapply mem_obs_eq_extend; eauto using internal_execution_valid.
      intros.
      eapply internal_exec_disjoint_val with (Hcomp := Hcomp) (pfj := pfj) (tp' := tp'); eauto using containsThread_internal_execution'.
      left.
      unfold Mem.perm in *.
      erewrite restrPermMap_irr' with (Hlt' := Hlt) by (rewrite Heq; eauto).
      assumption.
      (** [mem_obs_eq] for locks *)
      assert (Hlt : permMapLt ((getThreadR pfj'').2) (getMaxPerm m))
        by (rewrite <- Heq; by  (eapply (Hcomp _ pfj).2)).
      assert (mem_obs_eq (id_ren m) (restrPermMap (Hcomp j pfj).2) (restrPermMap (Hcomp j pfj).2))
        by (erewrite id_ren_restr with (Hlt := (Hcomp j pfj).2); eapply mem_obs_eq_id; eauto).
      erewrite restrPermMap_irr' with (Hlt' := Hlt) in H at 2 by (rewrite Heq; auto).
      eapply mem_obs_eq_extend; eauto using internal_execution_valid.
      intros.
      eapply internal_exec_disjoint_val with (Hcomp := Hcomp) (pfj := pfj) (tp' := tp'); eauto using containsThread_internal_execution'.
      right.
      unfold Mem.perm in *.
      erewrite restrPermMap_irr' with (Hlt' := Hlt) by (rewrite Heq; eauto).
      assumption.
  Qed.

  Lemma csafe_pop_step :
    forall (tp : thread_pool) (m : mem) (i : tid) (cnti : containsThread tp i)
      (U : seq tid) n
      (Hpop: cnti @ E \/ cnti @ S)
      (Hsafe: csafe the_ge (buildSched (i :: U),[::],tp) m (S n)),
    exists (tp' : thread_pool) (m' : mem),
      cmachine_step (buildSched (i :: U), [::],tp) m (U, [::],tp') m' /\
      forall U'', csafe the_ge (U'',[::],tp') m' n.
  Proof.
    intros.
    unfold buildSched in *.
    inversion Hsafe; simpl in *.
    - subst; by exfalso.
    - unfold getStepType in Hpop.
      inversion Hstep; subst; simpl in *;
      inversion HschedN; subst tid;
      try match goal with
          | [H: ?X = ?Y :: ?X |- _] =>
            exfalso;
              clear - HschedS; induction U; simpl in *; try discriminate;
              inversion HschedS;
                by auto
          end.
      inversion Htstep; subst.
      pf_cleanup.
      rewrite Hcode in Hpop. simpl in Hpop.
      destruct Hpop;
        by discriminate.
      inversion Htstep; subst.
      pf_cleanup.
      rewrite Hcode in Hpop; simpl in Hpop.
      destruct Hpop;
        by discriminate.
      inversion Htstep; subst; pf_cleanup.
      rewrite Hcode in Hpop. simpl in Hpop.
      apply ev_step_ax1 in Hcorestep.
      apply corestep_not_at_external in Hcorestep.
      rewrite Hcorestep in Hpop.
      destruct (halted SEM.Sem c);
        destruct Hpop;
          by discriminate.
    - subst. do 2 eexists; split; eauto.
  Qed.
  
  Lemma sim_suspend : sim_suspend_def.
  Proof.
    unfold sim_suspend_def.
    intros.
    inversion Hsim as
        [HnumThreads HmemCompC HmemCompF HsafeC HsimWeak Hfpsep
                     HsimStrong HsimRes HinvF HmaxF
                     Hwd_mem Htp_wd Hge_wd [Hge_incr Hfg] Hxs].
    assert (pfc: containsThread tpc i)
      by (eapply HnumThreads; eauto).
    destruct (HsimStrong i pfc pff)
      as (tpc' & mc' & Hincr & Hsynced & Hexec & Htsim & Hownedi & Hownedi_lp);
      clear HsimStrong.
    (** The coarse machine is also at suspend*)
    assert (pfc': containsThread tpc' i)
      by (clear - Hexec pfc; eapply containsThread_internal_execution in pfc;
          eauto).
    assert (memCompC' := internal_execution_compatible HmemCompC Hexec).
    specialize (Htsim pfc' memCompC').
    assert (Hstop_pfc': pfc' @ S)
      by (by erewrite (stepType_inj _ _ _ (code_eq Htsim))).
    (** It's safe to step the coarse grained machine for one more step on i*)
    specialize (HsafeC (buildSched [:: i])).
    assert (HcoreN := safety_det_corestepN_internal xs HsafeC Hexec).
    destruct HcoreN as [HcorestepN Hsafety].
    destruct (csafe_pop_step pfc' ltac:(eauto) Hsafety) as
        (tpc'' & mc'' & Hstep' & Hsafe').
    assert (HinvC: invariant tpc)
      by (eapply cmachine_step_invariant; eauto).
    (** A suspend step pops the schedule and does not touch the memory *)
    assert (Heq : mc' = mc'' /\ mem_compatible tpc' mc' /\
                  DryConc.suspend_thread pfc' tpc'')
      by (eapply suspend_step_inverse; eauto).
    destruct Heq as [? [Hcomp' HsuspendC]]; subst mc'.
    assert (memCompC'': mem_compatible tpc'' mc'')
      by (eapply suspendC_compatible; eauto).
    assert (HstepF := strong_tsim_stop HinvF Htsim Hstep' Hstop_pfc').
    destruct HstepF as [tpf' [HstepF Htsim']].
    assert (memCompF': mem_compatible tpf' mf)
      by (eapply suspendF_compatible; eauto).
    exists tpc'', mc'', tpf', mf.
    (** since thread i commits, the new global renaming will be fi *)
    exists (fp i pfc).
    assert (pfci': containsThread tpc' i)
      by (eapply containsThread_internal_execution; eauto).
    assert (pfci'': containsThread tpc'' i)
      by (eapply suspendC_containsThread with (tp := tpc'); eauto).
    (** and we need to shift all other mappings..*)
    exists (fun j (cntj'': containsThread tpc'' j) =>
         let cntj := (containsThread_internal_execution'
                        Hexec ((snd (suspendC_containsThread j HsuspendC)) cntj'')) in
         if i == j then
           fp i pfc else
           fun b1 =>
             if valid_block_dec mc b1 then f b1
             else
               if valid_block_dec mc'' b1 then
                 (fp i pfc) b1
               else
                 let bz :=
                     (Z.pos b1 - (Z.pos (Mem.nextblock mc'') -
                                  Z.pos (Mem.nextblock mc)))%Z in
                 (fp j cntj) (Z.to_pos bz)), tr.
    split.
    { (** the fine-grained machine takes a suspend step *)
      intros U; eapply FineConc.suspend_step; simpl; eauto.
    }
    { (** The simulation between tpc'' and tpf' is retained. *)
      (** We prove first that well-definedeness of the components of
      the state is also preserved. We only prove it here to avoid
      duplicated work when we re-establish these invariants *)
      (** Notice also that the nextblock of mc will be
                smaller or equal to that of mc''*)
      assert (Hle: (Mem.nextblock mc <= Mem.nextblock mc'')%positive)
        by (eapply internal_execution_nextblock; eauto).
      assert (Hdomainf: domain_memren f mc)
        by (destruct (HsimWeak _ pfc pff) as [HsimWeak' _];
             eapply weak_obs_eq_domain_ren in HsimWeak'; eauto).
      assert (Hwd := internal_execution_wd _ _ Hdomainf Hwd_mem Htp_wd
                                           Hge_wd (ren_incr_domain_incr
                                                     Hge_incr) Hexec).
      destruct Hwd as [Hwd_mem' [[f' [Hincrf' Hdomainf']] Htp_wd']].
      assert (pffi': containsThread tpf' i)
        by (eapply suspendF_containsThread with (cnti := pff); eauto).
      specialize (Htsim' memCompC'' memCompF' pfci'' pffi').
      assert (Hdomain_fi: domain_memren (fp i pfc) mc'')
        by (eapply (mem_obs_eq_domain_ren (obs_eq_data Htsim')); eauto).
      specialize (Htp_wd' _ Hdomain_fi).
      eapply Build_sim with (mem_compc := memCompC'') (mem_compf := memCompF').
      { (** number of threads *)
        clear - HnumThreads Hexec HsuspendC HstepF.
        intros j. assert (Hpffj := suspendF_containsThread j HstepF).
        assert (Hpfcj' := suspendC_containsThread j HsuspendC).
        split; intros;
        [apply Hpffj; apply HnumThreads;
         destruct Hpfcj'; eapply containsThread_internal_execution'; eauto
        |  apply Hpfcj';
          destruct Hpffj;
          eapply containsThread_internal_execution; eauto;
          destruct (HnumThreads j); by auto].            
      }
      { (** safety of coarse state *)
        assumption.
      }
      { (** Proof of weak simulation between the threadpools and memories *)
        clear HsafeC. pf_cleanup.
        intros j pfcj'' pffj'.
        pose proof (weak_obs_eq (obs_eq_data Htsim)) as Hweak_obs_eq_data.
        (** We will proof the two complicated weak_mem_obs_eq (for locks and data) goals at the same time*)
        assert (Hperm_weak: forall (b1 b2 : block) (ofs : Z),
                   fp i pfc b1 = Some b2 ->
                   Mem.perm_order'' (permission_at (restrPermMap (fst (memCompC'' j pfcj''))) b1 ofs Cur)
                                    (permission_at (restrPermMap (fst (memCompF' j pffj'))) b2 ofs Cur) /\
                   Mem.perm_order'' (permission_at (restrPermMap (snd (memCompC'' j pfcj''))) b1 ofs Cur)
                                    (permission_at (restrPermMap (snd (memCompF' j pffj'))) b2 ofs Cur)).
        { (* Permissions of the coarse-state are higher than the fine-state *)
          (* Proof idea: for thread i, we have a strong simulation
            on internal steps and then a suspend step so it should be
            straightforward. For thread j: For blocks before
            (nextblock mc) from weak-sim and for blocks after
            (nextblock mc) this should be freeable on i and thus empty
            on j. Correction: This doesn't hold, because the new
            blocks may have been freed by some internal step. Hence we
            need some other way to capture that they belong to thread
            i and the other threads should have empty permission (a
            new invariant). In fact, this invariant should talk about
            the permissions at the fine-grained level as we no longer
            can use the non-interference invariant because the
            permissions of thread i are not necessary freeable. *)
          intros b1 b2 ofs Hfi.
          (** The permissions will be same as before taking the suspend step*)
          assert (pffj: containsThread tpf j)
            by (eapply suspendF_containsThread; eauto).
          assert (Hperm_eqF: permission_at (restrPermMap (memCompF' _ pffj').1)
                                           b2 ofs Cur =
                             permission_at (restrPermMap (HmemCompF _ pffj).1)
                                           b2 ofs Cur)
            by (do 2 rewrite restrPermMap_Cur;
                erewrite <- gsoThreadR_suspendF with (cntj := pffj); eauto).
          assert (Hperm_eqF_locks: permission_at (restrPermMap (memCompF' _ pffj').2)
                                           b2 ofs Cur =
                             permission_at (restrPermMap (HmemCompF _ pffj).2)
                                           b2 ofs Cur)
            by (do 2 rewrite restrPermMap_Cur;
                erewrite <- gsoThreadR_suspendF with (cntj := pffj); eauto).
          rewrite Hperm_eqF Hperm_eqF_locks.
          (** Likewise for the DryConc machine*)
          assert (pfcj': containsThread tpc' j)
            by (eapply suspendC_containsThread; eauto).
          assert (Hperm_eqC: permission_at (restrPermMap (memCompC'' _ pfcj'').1)
                                           b1 ofs Cur =
                             permission_at (restrPermMap (memCompC' _ pfcj').1)
                                           b1 ofs Cur)
            by (do 2 rewrite restrPermMap_Cur;
                erewrite <- gsoThreadR_suspendC with (cntj := pfcj'); eauto).
          assert (Hperm_eqC_locks: permission_at (restrPermMap (memCompC'' _ pfcj'').2)
                                           b1 ofs Cur =
                             permission_at (restrPermMap (memCompC' _ pfcj').2)
                                           b1 ofs Cur)
            by (do 2 rewrite restrPermMap_Cur;
                erewrite <- gsoThreadR_suspendC with (cntj := pfcj'); eauto).
          rewrite Hperm_eqC Hperm_eqC_locks.
          clear Hperm_eqF Hperm_eqC HcorestepN HstepF Hstep'.
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          { (** Case j = i *)
            subst.
            clear - Htsim Hfi.
            destruct Htsim as [_ Hmem_obs_eq_data Hmem_obs_eq_locks];
              destruct Hmem_obs_eq_data as [Hweak_data _];
              destruct Hweak_data as [_ _ _ _ Hperm_weak_data];
              destruct Hmem_obs_eq_locks as [Hweak_locks _];
              destruct Hweak_locks as [_ _ _ _ Hperm_weak_locks].
            specialize (Hperm_weak_data b1 b2 ofs Hfi).
            specialize (Hperm_weak_locks b1 b2 ofs Hfi);
              by pf_cleanup.
          }
          { (** Case j <> i *)
            assert (pfcj: containsThread tpc j)
              by (eapply containsThread_internal_execution'; eauto).
            destruct (HsimWeak _ pfcj pffj) as [Hweak_data Hweak_locks].
            destruct Hweak_data as [Hinvdomain Hdomain Hcodomain Hinjective Hobs_weak_data].
            destruct Hweak_locks as [_ _ _ _ Hobs_weak_locks].
            destruct (valid_block_dec mc b1) as [Hvalid_mc | Hinvalid_mc].
            - (** b1 is a block that's valid in mc, i.e. not allocated by i *)
              assert (Hvalid: Mem.valid_block (restrPermMap (HmemCompC _ pfcj).1) b1)
                by (unfold Mem.valid_block in *;
                      by rewrite restrPermMap_nextblock).
              apply Hdomain in Hvalid.
              destruct Hvalid as [b2' Hf].
              assert (b2 = b2')
                by (apply Hincr in Hf; rewrite Hf in Hfi;
                    inversion Hfi; by subst); subst b2'.
              destruct (permission_at_execution xs pfc pfcj pfcj' Hij HmemCompC memCompC' Hexec b1 ofs) as [H1 H2].
              erewrite <- H1, <- H2;
                by eauto.
            - (** b1 is a block that's not valid in mc, i.e. allocated by i *)
              (* NOTE: here is the place where we use the invariant
                about blocks owned by i. The proof became much smaller
                (but the burden was moved elsewhere)*)
              apply Hinvdomain in Hinvalid_mc.
              destruct (Hownedi j pffj Hij _ _ ofs Hfi Hinvalid_mc) as [Hownedi_data Hownedi_locks].
              rewrite! restrPermMap_Cur.
              rewrite Hownedi_data Hownedi_locks.
              destruct ((getThreadR pfcj').1 # b1 ofs), ((getThreadR pfcj').2 # b1 ofs); simpl;
                by auto.
          }
        }
        constructor;
          constructor; try (by (destruct Hweak_obs_eq_data; eauto));
            intros; by (destruct (Hperm_weak _ _ ofs Hrenaming)).
      }
      { (* Proof of seperation*)
        intros k j cntk cntj Hkj b b' b2 b2' Hfi Hfi' Hfk Hfj.
        simpl in Hfk, Hfj.
        destruct (i == k) eqn:Hik; destruct (i == j) eqn: Hij;
        move/eqP:Hik=> Hik; move/eqP:Hij => Hij.
        - subst k j. by exfalso.
        - subst k.
            by congruence.
        - subst j.
            by congruence.
        - destruct (valid_block_dec mc b) as [Hvalidb | Hinvalidb];
          first by (apply Hincr in Hfk; by congruence).
          destruct (valid_block_dec mc'' b) as [Hvalidib | Hinvalidib];
            first by (simpl in *; congruence).
          destruct (valid_block_dec mc b') as [Hvalidb' | Hinvalidb'];
            first by (apply Hincr in Hfj; by congruence).
          destruct (valid_block_dec mc'' b') as [Hvalidib' | Hinvalidib'];
            first by (simpl in *; congruence).
          specialize (HsimWeak _ pfc pff).
          apply Pos.lt_eq_cases in Hle.
          simpl in Hfj, Hfk.
          destruct Hle as [Hlt | Heq].
          + apply Pos.le_nlt in Hinvalidb.
            apply Pos.le_nlt in Hinvalidib.
            assert (Hinvalid:
                      (Mem.nextblock mc <=
                       Z.to_pos (Z.pos_sub b (Mem.nextblock mc'' -
                                              Mem.nextblock mc)))%positive)
              by (eapply le_sub; eauto).
            eapply Hfpsep with (i := k) (j := j); eauto.
            apply Pos.le_nlt in Hinvalid.
            apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalid.
            rewrite Z.pos_sub_gt; auto.
            apply Pos.le_nlt in Hinvalidb'.
            apply Pos.le_nlt in Hinvalidib'.
            assert (Hinvalid':
                      (Mem.nextblock mc <=
                       Z.to_pos (Z.pos_sub b' (Mem.nextblock mc'' -
                                               Mem.nextblock mc)))%positive)
              by (eapply le_sub; eauto).
            apply Pos.le_nlt in Hinvalid'.
            apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalid'.
            rewrite Z.pos_sub_gt; auto.
          + eapply Hfpsep with (i := k) (j := j); eauto; 
            rewrite Heq;
            rewrite Z.pos_sub_diag; simpl;
            [ by apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalidb
            | by apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalidb'].
      }  
      { (** Proof of strong simulation
- If thread i = thread j then it's straightforward. 
- If thread i <> thread j then we need to shuffle things.
- In particular we know that for some memory mcj s.t mc -->j mcj we have a strong simulation with mf and we want to establish it for mcj' s.t. mc -->i mci --> mcj'. 
- Take as fj' = | b < nb mc => id | nb mc =< b < nb mci => fi  | nb mci =< b < nb mcj' => fj (g b)) where g is the inverse of the f that storngly injects mcj to mcj'.
Note that: mc strongly injects in mci|j with id, hence mcj strongly injects
into mcj' with an extension of the id injection (fij). *)
        intros j pfcj'' pffj'.
        case (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        { subst j. exists tpc'', mc''. simpl.
          split;
            first by (apply ren_incr_refl).
          split; auto. split.
          assert (Hempty: [seq x <- [seq x <- xs | x != i] | x == i] = nil).
          { clear. induction xs as [|x xs]; first by reflexivity.
            simpl; destruct (x == i) eqn:Heq;
            simpl; first by assumption.
            erewrite if_false
              by (apply/eqP; intro Hcontra; subst;
                    by move/eqP:Heq=>Heq).
              by assumption.
          }
          rewrite Hempty;
            by constructor.
          split; first by (intros; pf_cleanup; auto).
          split; first by congruence.
          split; by congruence.
        }
        { (** case j <> i *)
          assert (pfc'j: containsThread tpc' j)
            by (eapply suspendC_containsThread with (cnti := pfc'); eauto).
          assert (pfcj: containsThread tpc j)
            by (eapply containsThread_internal_execution'; eauto).
          specialize (HsimWeak _ pfc pff).
          (*domain of f*)
          assert (Hdomain_f: domain_memren f mc)
            by (apply (weak_obs_eq_domain_ren (weak_tsim_data HsimWeak))).
          (* domain of id renaming*)
          assert (Hdomain_id: domain_memren (id_ren mc) mc)
            by (apply id_ren_domain).
          (* the thread-pool is well-defined for id renaming*)
          assert (Htp_wd_id: tp_wd (id_ren mc) tpc)
            by (eapply tp_wd_domain; eauto).
          simpl.
          assert (H : containsThread_internal_execution'
                        Hexec (snd (suspendC_containsThread
                                        j HsuspendC) pfcj'') = pfcj) by 
              (erewrite proof_irr
               with (a1 := (containsThread_internal_execution'
                              Hexec (snd (suspendC_containsThread j HsuspendC)
                                           pfcj'')))
                      (a2 := pfcj); auto).
          rewrite H; clear H.
          (** The original <tpc, mc> strongly injects into <tpc'',mc''> where
               <tpc, mc> -->i <tpc', mc'> -->iS <tpc'',mc'>  with the id map*)
          assert (Hsim_c_ci: strong_tsim (id_ren mc)
                                         pfcj pfcj'' HmemCompC memCompC'')
            by (eapply strong_tsim_id with (f := id_ren mc) (pfi' := pfc'); eauto).
          assert (pffj: containsThread tpf j)
            by (eapply suspendF_containsThread; eauto).
          assert (Htsimj := (simStrong Hsim) j pfcj pffj).
          (** executing the internal steps for thread j gives us a strong 
              simulation between the coarse and fine-grained states. *)
          destruct Htsimj as
              (tpcj & mcj & Hincrj & Hsyncedj & Hexecj & Htsimj
               & Hownedj & Hownedj_lp).
          (** by the strong simulation on mc and mc'' (via id) we can
              obtain a strong simulation between mcj and mcj', where
              mcj' mc -->i --> mci -->j mcj' *)
          assert (Hinv'': invariant tpc'')
            by (eapply suspendC_invariant with (tp := tpc');
                 [eapply internal_execution_invariant with (tp := tpc);
                   eauto | eauto]).
          assert (Hge_incr_id: ren_incr fg (id_ren mc))
            by (clear - Hge_incr Hfg Hdomain_f;
                 eapply incr_domain_id; eauto).
          assert (Hsimjj':= strong_tsim_execution xs Hinv'' Hfg Hge_wd
                                                  Hge_incr_id Hsim_c_ci Hexecj).
          destruct Hsimjj'
            as (tpcj' & mcj' & fij & Hexecij
                & Hincr' & Hsep  & Hnextblockj' & Hinverse & Hsimjj').
          destruct Hsimjj' as [[pfcjj [pfij [Hcompjj [Hcompij Hsimij]]]] Hid_case].
          pf_cleanup.
          (* notice that mcj and mcj' will be equal up to nextblock mc
           * (mcj injects to mcj' with id up to nextblock mc). Hence
           * for blocks smaller than nb mc we follow the fj injection to mf
           * for blocks between nb mc and nb mc'' we follow the fi injection
           * and for blocks after that we follow the fj one after taking
           * the inverse. (TODO: point to a diagram) *)
          (*TODO: comment deprecated*)
          specialize (Htsimj pfcjj Hcompjj).
          exists tpcj', mcj'.
          (* Moreover we prove that for all blocks b1 if the
                inverse of b1 is mapped by fpj and b1 is not valid in
                mc and mc'' then it is is valid in mcj'*)
          (* TODO: make this a separate lemma*)
          assert (Hvalidmcj':
                    forall b1 b2 (pf: containsThread tpc j),
                      ~ Mem.valid_block mc b1 ->
                      ~ Mem.valid_block mc'' b1 ->
                      fp j pf
                         (Z.to_pos ((Z.pos b1 -
                                     (Z.pos (Mem.nextblock mc'') -
                                      Z.pos (Mem.nextblock mc)))%Z)) = Some b2 ->
                      Mem.valid_block mcj' b1).
          { (*NOTE: this is a somewhat tedious proof,
                      probably because the definitions are weak in
                      some sense. It's still doable, so I'll go ahead
                      but maybe at some point we should reconsider the
                      relations*)
            (*Proof sketch: We prove that if b1 >= nb mcj'
                        then (b1 - (nb mcj' - nb mcj)) >= nb mcj
                        hence, it's invalid in mcj and we derive a
                        contradiction by the fact that it's mapped by
                        fpj. *)
            intros b1 b2 pf Hinvalidmc Hinvalidmc'' Hf'.
            destruct (valid_block_dec mcj' b1) as [? | Hinvalidmcj'];
              first by assumption.
            exfalso.
            clear - Hnextblockj' Hinvalidmc Hinvalidmc''
                                 Hf' Hinvalidmcj' Htsimj Hle.
            pf_cleanup.
            apply Pos.le_lteq in Hle.
            destruct Hle as [Hlt | Hnbeq].
            - (*TODO: factor this out as a lemma*)
              assert (Hnblocks:
                        (Z.pos (Mem.nextblock mc'') + Z.neg (Mem.nextblock mc) =
                         Z.pos (Mem.nextblock mcj') + Z.neg (Mem.nextblock mcj))%Z).
              { clear -Hnextblockj'.
                destruct Hnextblockj' as [[p [Hmcj Hmcj']]|[Hmcj Hmcj']];
                  rewrite Hmcj Hmcj'; try reflexivity.
                replace (Z.neg (Mem.nextblock mc + p)) with
                (Z.opp (Z.pos (Mem.nextblock mc + p))%Z)
                  by (by rewrite Pos2Z.opp_pos).
                rewrite Z.add_opp_r.
                do 2 rewrite Pos2Z.inj_add.
                rewrite Zminus_plus_simpl_r.
                  by reflexivity.
              }
              simpl in Hf'.
              rewrite <- Pos2Z.add_pos_neg in Hf'.
              rewrite Hnblocks in Hf'. simpl in Hf'.
              assert (Hnb': (Mem.nextblock mcj < Mem.nextblock mcj')%positive).
              { simpl in Hnblocks.
                rewrite Z.pos_sub_gt in Hnblocks; auto.
                destruct (Coqlib.plt (Mem.nextblock mcj) (Mem.nextblock mcj'))
                  as [? | Hcontra];
                  first by assumption.
                unfold Coqlib.Plt in Hcontra.
                apply Pos.le_nlt in Hcontra.
                apply Pos.le_lteq in Hcontra.
                exfalso.
                destruct Hcontra as [Hcontra | Hcontra].
                rewrite Z.pos_sub_lt in Hnblocks; auto.
                  by congruence.
                  rewrite Hcontra in Hnblocks.
                  rewrite Z.pos_sub_diag in Hnblocks.
                  assert (H:= Pos2Z.is_pos (Mem.nextblock mc'' - Mem.nextblock mc)).
                  rewrite Hnblocks in H.
                    by apply Z.lt_irrefl with (x :=0%Z).
              }
              rewrite Z.pos_sub_gt in Hf'; auto.
              simpl in Hf'.        
              apply Pos.le_nlt in Hinvalidmcj'.
              assert (Hinvalid: (Mem.nextblock mcj
                                 <=
                                 Z.to_pos (Z.pos_sub b1 (Mem.nextblock mcj'
                                                         - Mem.nextblock mcj)))%positive)
                by (eapply le_sub; eauto).
              apply Pos.le_nlt in Hinvalid.
              apply (domain_invalid (weak_obs_eq (obs_eq_data Htsimj))) in Hinvalid.
                by congruence.
            - rewrite Hnbeq in Hf'.
              simpl in Hf'.
              rewrite Z.pos_sub_diag in Hf'.
              simpl in Hf'.
              destruct Hnextblockj' as [[p [Hmcj Hmcj']] | [Hmcj Hmcj']].
              + rewrite Hnbeq in Hmcj.
                rewrite <- Hmcj' in Hmcj.
                assert (Hcontra: ~ Mem.valid_block mcj b1)
                  by (unfold Mem.valid_block in *; rewrite Hmcj; auto).
                apply (domain_invalid (weak_obs_eq (obs_eq_data Htsimj))) in Hcontra.
                  by congruence.
              + assert (Hcontra: ~ Mem.valid_block mcj b1)
                  by (unfold Mem.valid_block in *; rewrite Hmcj; auto).
                apply (domain_invalid (weak_obs_eq (obs_eq_data Htsimj))) in Hcontra.
                  by congruence.
          }
          split.
          { (* fi is included in f' *)
            intros b1 b2 Hfi.
            destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
            - assert (Hf_val := (domain_valid (weak_tsim_data HsimWeak)) b1).
              specialize (Hf_val
                            ((snd (restrPermMap_valid
                                       (HmemCompC i pfc).1 b1)) Hvalidmc)).
              destruct Hf_val as [b2' Hf_val].
              assert (Heq: b2 = b2')
                by (apply Hincr in Hf_val;
                     rewrite Hf_val in Hfi; inversion Hfi; by subst);
                subst b2';
                  by assumption.
            - destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''];
              first by assumption.
              destruct (valid_block_dec mcj' b1) as [Hvalidmcj'_b1 | Hinvalidmcj'];
                assert (Hcontra := domain_invalid (weak_obs_eq (obs_eq_data Htsim')));
                assert (Hinvalid: ~ Mem.valid_block
                                    (restrPermMap (memCompC'' i pfci'').1) b1)
                  by (intros Hcontra2;
                        by apply restrPermMap_valid in Hcontra2);
                specialize (Hcontra _ Hinvalid);
                  by congruence.
          } split.
          { (* synced *)
            intros Hsynced'.
            assert (Hlst :[seq x <- [seq x <- xs | x != i] | x == j] =
                          [seq x <- xs | x == j]) by (by eapply filter_neq_eq).
            rewrite Hlst in Hsynced'.
            rewrite Hsynced' in Hexecij.
            inversion Hexecij; subst;
            [|simpl in HschedN; inversion HschedN; subst; discriminate].
            rewrite Hsynced' in Hexecj.
            specialize (Hsyncedj Hsynced'). simpl. subst f.
            extensionality b.
            destruct (valid_block_dec mc b) as [Hvalidmc | Hinvalidmc].
            - assert (Hfb := (domain_valid (weak_tsim_data HsimWeak)) b Hvalidmc).
              destruct Hfb as [b' Hfb].
              rewrite Hfb. by apply Hincr in Hfb.
            - destruct (valid_block_dec mcj' b) as [? | Hinvalidmcj'];
              first by reflexivity.
              assert (Hinvdomain := domain_invalid (weak_obs_eq (obs_eq_data Htsim))).
              assert (Hinvalidmcji':
                        ~ Mem.valid_block (restrPermMap (memCompC' i pfc').1) b)
                by (intros Hcontra; by apply restrPermMap_valid in Hcontra).
              specialize (Hinvdomain _ Hinvalidmcji'). rewrite Hinvdomain.
              assert (Heq: mc = mcj)
                by (inversion Hexecj; [subst mcj; auto |
                                       simpl in HschedN; discriminate]).
              subst mcj.
              apply Pos.lt_eq_cases in Hle.
              simpl.
              destruct Hle as [Hlt | Heq].
              + apply Pos.le_nlt in Hinvalidmc.
                apply Pos.le_nlt in Hinvalidmcj'.
                assert (Hinvalid:
                          (Mem.nextblock mc <=
                           Z.to_pos (Z.pos_sub b (Mem.nextblock mcj' -
                                                  Mem.nextblock mc)))%positive)
                  by (eapply le_sub; eauto).
                rewrite Z.pos_sub_gt; auto.
                simpl.
                apply Pos.le_nlt in Hinvalid.
                apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalid.
                  by auto.
              + rewrite Heq. rewrite Z.pos_sub_diag. simpl.
                apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalidmc;
                  by auto.
          } split.
          { (** tpc'' can step in a fine grained way for thread j *)
              by rewrite filter_neq_eq.
          } split.
          { (** strong simulation between mcj' and mf' *)
            intros pfcj' Hcompcj'. pf_cleanup.
            (** We prove [mem_obs_eq] between the two threads by asserting its
            components here (in order to reduce proof repetition).*)

            (** **** Proof of the components of [weak_mem_obs_eq] *)
            (** the renaming is not defined on invalid blocks*)
            assert (Hinvalid_domain:
                      forall b,
                        ~ Mem.valid_block mcj' b ->
                        (if valid_block_dec mc b
                         then f b
                         else
                           if valid_block_dec mc'' b
                           then fp i pfc b
                           else
                             fp j pfcj
                                (Z.to_pos
                                   match (- Z.pos_sub (Mem.nextblock mc'') (Mem.nextblock mc))%Z with
                                   | 0%Z => Z.pos b
                                   | Z.pos y' => Z.pos (b + y')
                                   | Z.neg y' => Z.pos_sub b y'
                                   end)) = None).
            { intros b Hinvalid.
              assert (Hinvalidmc'': ~ Mem.valid_block mc'' b)
                by (intros Hcontra;
                    eapply internal_execution_valid with (m' := mcj')
                      in Hcontra;
                    eauto).
              assert (Hinvalidmc: ~ Mem.valid_block mc b)
                by (intros Hcontra;
                    eapply internal_execution_valid with (m' := mc'')
                      in Hcontra;
                    eauto).
              simpl.
              unfold is_left.
              erewrite Coqlib2.if_false by eassumption.
              erewrite Coqlib2.if_false by eassumption.
              match goal with
              | [|- fp _ _ ?Expr = _] =>
                destruct (valid_block_dec mcj Expr) as [Hvalidmcj | Hinvalidmcj]
              end.
              + apply Pos.lt_eq_cases in Hle.
                destruct Hle as [Hlt | Heq].
                * apply Pos.le_nlt in Hinvalidmc''.
                  apply Pos.le_nlt in Hinvalidmc.
                  assert (Hinvalid':
                            (Mem.nextblock mc <=
                             Z.to_pos (Z.pos_sub b (Mem.nextblock mc'' -
                                                    Mem.nextblock mc)))%positive)
                    by (eapply le_sub; eauto).
                  apply Pos.le_nlt in Hinvalid'.
                  apply (domain_valid (weak_obs_eq (obs_eq_data Hsimij))) in Hvalidmcj.
                  apply (domain_invalid (weak_obs_eq (obs_eq_data Hsim_c_ci))) in Hinvalid'.
                  destruct Hvalidmcj as [b2 Hfij].
                  rewrite Z.pos_sub_gt in Hfij; auto.
                  assert (Hinvalid2 := Hsep _ _ Hinvalid' Hfij).
                  assert (Hvalidb2 :=
                            (codomain_valid (weak_obs_eq (obs_eq_data Hsimij))) _ _ Hfij).
                  erewrite restrPermMap_valid in Hvalidb2.
                  destruct Hinvalid2 as [_ Hinvalidb2''].
                  specialize (Hinverse _ Hvalidb2 Hinvalidb2'').
                  simpl in Hinverse.
                  destruct Hinverse as [Hcontra _].
                  assert (Heq_contra :=
                            (injective (weak_obs_eq (obs_eq_data Hsimij)))
                              _ _ _ Hfij Hcontra).
                  assert (Heq : b = b2).
                  { apply Pos.le_nlt in Hinvalidb2''.
                    assert (((Mem.nextblock mc'' - Mem.nextblock mc) < b)%positive)
                      by (eapply lt_lt_sub; eauto).
                    assert (((Mem.nextblock mc'' - Mem.nextblock mc) < b2)%positive)
                      by (eapply lt_lt_sub; eauto).
                    rewrite Z.pos_sub_gt in Heq_contra; auto.
                    simpl in Heq_contra.
                    apply Z2Pos.inj_iff in Heq_contra;
                      try (rewrite Z.pos_sub_gt; auto;
                           apply Pos2Z.is_pos).
                    rewrite Z.pos_sub_gt in Heq_contra; auto.
                    rewrite Z.pos_sub_gt in Heq_contra; auto.
                    inversion Heq_contra as [Heq_contra2].
                    apply Pos.compare_eq_iff in Heq_contra2.
                    rewrite Pos.sub_compare_mono_r in Heq_contra2;
                      try (eapply lt_lt_sub; eauto).
                      by apply Pos.compare_eq_iff.
                  } subst b. by exfalso.
                * rewrite Heq in Hvalidmcj.
                  rewrite Z.pos_sub_diag in Hvalidmcj.
                  simpl in Hvalidmcj.
                  rewrite Heq. rewrite Z.pos_sub_diag.
                  simpl.
                  apply (domain_valid (weak_obs_eq (obs_eq_data Hsimij))) in Hvalidmcj.
                  apply (domain_invalid (weak_obs_eq (obs_eq_data Hsim_c_ci ))) in Hinvalidmc.
                  destruct Hvalidmcj as [b2 Hfij].
                  assert (Hinvalid2 := Hsep _ _ Hinvalidmc Hfij).
                  assert (Hvalidb2 :=
                            (codomain_valid (weak_obs_eq (obs_eq_data Hsimij))) _ _ Hfij).
                  erewrite restrPermMap_valid in Hvalidb2.
                  destruct Hinvalid2 as [_ Hinvalidb2''].
                  specialize (Hinverse _ Hvalidb2 Hinvalidb2'').
                  simpl in Hinverse.
                  destruct Hinverse as [Hcontra _].
                  rewrite Heq in Hcontra.
                  rewrite Z.pos_sub_diag in Hcontra.
                  simpl in Hcontra.
                  assert (Heq_contra :=
                            (injective (weak_obs_eq (obs_eq_data Hsimij)))
                              _ _ _ Hfij Hcontra).
                  subst;
                    by exfalso.
              + apply (domain_invalid (weak_obs_eq (obs_eq_data Htsimj))) in Hinvalidmcj.
                  by assumption.
            }
            assert (Hvalid_domain:
                      forall b,
                        Mem.valid_block mcj' b ->
                        exists b' : block,
                          (if valid_block_dec mc b
                           then f b
                           else
                             if valid_block_dec mc'' b
                             then fp i pfc b
                             else
                               fp j pfcj
                                  (Z.to_pos
                                     match (- Z.pos_sub (Mem.nextblock mc'') (Mem.nextblock mc))%Z with
                                     | 0%Z => Z.pos b
                                     | Z.pos y' => Z.pos (b + y')
                                     | Z.neg y' => Z.pos_sub b y'
                                     end)) = Some b').
            { intros b1 Hvalid.
              simpl.
              destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
              - assert (Hf := (domain_valid (weak_tsim_data HsimWeak)) b1).
                erewrite restrPermMap_valid in Hf.
                destruct (Hf Hvalidmc) as [b2 Hf_val].
                eexists; eassumption.
              - destruct (valid_block_dec mc'' b1)
                  as [Hvalidmc'' | Hinvalidmc''].
                + assert (Hfi := (domain_valid
                                    (weak_obs_eq (obs_eq_data Htsim'))) b1).
                  erewrite restrPermMap_valid in Hfi.
                  eauto.
                + specialize (Hinverse b1 Hvalid Hinvalidmc'').
                  simpl in Hinverse.
                  destruct Hinverse as [Hfij Hf'].
                  destruct (
                      valid_block_dec mcj
                                      (Z.to_pos
                                         match
                                           (- Z.pos_sub (Mem.nextblock mc'') (Mem.nextblock mc))%Z
                                         with
                                         | 0%Z => Z.pos b1
                                         | Z.pos y' => Z.pos (b1 + y')
                                         | Z.neg y' => Z.pos_sub b1 y'
                                         end)) as [Hvalidmcj | Hinvalidmcj];
                    [ apply (domain_valid (weak_obs_eq (obs_eq_data Htsimj))) in Hvalidmcj;
                        by assumption |
                      apply (domain_invalid (weak_obs_eq (obs_eq_data Hsimij))) in Hinvalidmcj;
                        by congruence].
            }
            (** the codomain of the new renaming*)
            assert (Hcodomain: forall b1 b2 : block,
                       (if valid_block_dec mc b1
                        then f b1
                        else
                          if valid_block_dec mc'' b1
                          then fp i pfc b1
                          else
                            fp j pfcj
                               (Z.to_pos
                                  match (- Z.pos_sub (Mem.nextblock mc'') (Mem.nextblock mc))%Z with
                                  | 0%Z => Z.pos b1
                                  | Z.pos y' => Z.pos (b1 + y')
                                  | Z.neg y' => Z.pos_sub b1 y'
                                  end)) = Some b2 -> Mem.valid_block mf b2).
              {  intros b1 b2 Hf'.
                  assert (Hfj_codomain := codomain_valid (weak_obs_eq (obs_eq_data Htsimj))).
                  assert (Hfi_codomain := codomain_valid (weak_obs_eq (obs_eq_data Htsim))).
                  simpl in Hf'.
                  unfold is_left in Hf'.
                  repeat match goal with
                         | [H: context[match valid_block_dec ?M ?B with
                                       | _ => _ end] |- _] =>
                           destruct (valid_block_dec M B)
                         end; try discriminate.
                  specialize (Hfj_codomain b1 b2);
                    erewrite restrPermMap_valid in *.
                  eauto.
                  specialize (Hfi_codomain b1 b2);
                    erewrite restrPermMap_valid in *.
                  eauto.
                  specialize (Hfj_codomain _ _ Hf');
                    by erewrite restrPermMap_valid in *.
              }
              (** proof of injectivity of the new renaming*)
              assert (Hinjective: forall b1 b1' b2 : block,
                         (if valid_block_dec mc b1
                          then f b1
                          else
                            if valid_block_dec mc'' b1
                            then fp i pfc b1
                            else
                              fp j pfcj
                                 (Z.to_pos
                                    match (- Z.pos_sub (Mem.nextblock mc'') (Mem.nextblock mc))%Z with
                                    | 0%Z => Z.pos b1
                                    | Z.pos y' => Z.pos (b1 + y')
                                    | Z.neg y' => Z.pos_sub b1 y'
                                    end)) = Some b2 ->
                         (if valid_block_dec mc b1'
                          then f b1'
                          else
                            if valid_block_dec mc'' b1'
                            then fp i pfc b1'
                            else
                              fp j pfcj
                                 (Z.to_pos
                                    match (- Z.pos_sub (Mem.nextblock mc'') (Mem.nextblock mc))%Z with
                                    | 0%Z => Z.pos b1'
                                    | Z.pos y' => Z.pos (b1' + y')
                                    | Z.neg y' => Z.pos_sub b1' y'
                                    end)) = Some b2 -> b1 = b1').
              {  intros b1 b1' b2 Hfb1 Hfb1'. 
                  destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
                  { (** case b1 is valid in mc*)
                    destruct (valid_block_dec mc b1') as [Hvalidmc' | Hinvalidmc'].
                    - (** case b1' is also valid in mc*)
                      eapply (injective (weak_tsim_data HsimWeak)); eauto.
                    - (** case b1' is not valid in mc *)
                      destruct (valid_block_dec mc'' b1') as [Hvalidmc''' | Hinvalidmc'''].
                      + apply Hincr in Hfb1.
                        eapply (injective (weak_obs_eq (obs_eq_data Htsim))); eauto.
                      + (** case b1' is in mcj' or invalid *)
                        (** we can derive a contradiction by the fact
                          that the inverse of b1' will be a block that
                          is invalid in mc, and that fpj maps it to
                          the same block as b1 which is valid in mc,
                          using injectivity of fpj*)
                        clear - Hfb1' Hfb1 Hincrj Htsimj Hvalidmc Hexec
                                      Hinvalidmc''' Hinvalidmc' Hle.
                        apply Hincrj in Hfb1.
                        apply Pos.le_lteq in Hle.
                        destruct Hle as [Hlt | Hnbeq].
                        * rewrite Z.pos_sub_gt in Hfb1'; auto. simpl in Hfb1'.
                          apply Pos.le_nlt in Hinvalidmc'''.
                          assert (Hinvalid: (Mem.nextblock mc
                                             <=
                                             Z.to_pos (Z.pos_sub b1' (Mem.nextblock mc''
                                                                      - Mem.nextblock mc)))%positive)
                            by (eapply le_sub; eauto).
                          apply Pos.le_nlt in Hinvalid.
                          assert (Hcontra:= (injective
                                               (weak_obs_eq (obs_eq_data Htsimj)))
                                              _ _ _ Hfb1 Hfb1').
                          subst b1.
                            by exfalso.
                        * rewrite Hnbeq in Hfb1'.
                          rewrite Z.pos_sub_diag in Hfb1'.
                          simpl in Hfb1'.
                          assert (Hcontra := (injective (weak_obs_eq (obs_eq_data Htsimj)))
                                               _ _ _ Hfb1 Hfb1').
                          subst b1;
                            by exfalso.
                  }
                  { (** case b1 is a block that is invalid in mc *)
                    destruct (valid_block_dec mc b1') as [Hvalidmc' | Hinvalidmc'].
                    - (** case b1' is a block is that valid in mc*)
                      (**this is orthogonal to the above case, maybe factor it out?*)
                      destruct (valid_block_dec mc'' b1) as [Hvalidmc''' | Hinvalidmc'''].
                      + apply Hincr in Hfb1'.
                        eapply (injective (weak_obs_eq (obs_eq_data Htsim)));
                          by eauto.
                      + (** case b1' is in mcj' or invalid *)
                        (** we can derive a contradiction by the fact
                          that the inverse of b1' will be a block that
                          is invalid in mc, and that fpj maps it to
                          the same block as b1 which is valid in mc,
                          using injectivity of fpj*)
                        clear - Hfb1' Hfb1 Hincrj Htsimj Hvalidmc' Hexec
                                      Hinvalidmc''' Hinvalidmc Hle.
                        apply Hincrj in Hfb1'.
                        apply Pos.le_lteq in Hle.
                        destruct Hle as [Hlt | Hnbeq].
                        * rewrite Z.pos_sub_gt in Hfb1; auto. simpl in Hfb1.
                          apply Pos.le_nlt in Hinvalidmc'''.
                          assert (Hinvalid: (Mem.nextblock mc
                                             <=
                                             Z.to_pos (Z.pos_sub b1 (Mem.nextblock mc''
                                                                      - Mem.nextblock mc)))%positive)
                            by (eapply le_sub; eauto).
                          apply Pos.le_nlt in Hinvalid.
                          assert (Hcontra:= (injective
                                               (weak_obs_eq (obs_eq_data Htsimj)))
                                              _ _ _ Hfb1 Hfb1').
                          subst b1';
                            by exfalso.
                        * rewrite Hnbeq in Hfb1.
                          rewrite Z.pos_sub_diag in Hfb1.
                          simpl in Hfb1.
                          assert (Hcontra := (injective (weak_obs_eq (obs_eq_data Htsimj)))
                                               _ _ _ Hfb1 Hfb1').
                          subst b1';
                            by exfalso.
                    - (** case b1' is invalid in mc*)
                      destruct (valid_block_dec mc'' b1) as [Hvalidmci | Hinvalidmci].
                      + destruct (valid_block_dec mc'' b1') as [Hvalidmci' | Hinvalidmci'];
                        first by (eapply (injective (weak_obs_eq (obs_eq_data Htsim))); eauto).
                        (** the inverse of b1' will be in invalid in
                          mc (fresh in mcj). Hence by seperation
                          between fpj and fpi it must be that b2 <>
                          b2, contradiction. *)
                        clear - Hfb1' Hfb1 Htsimj Hfpsep Hinvalidmc Hexec
                                      Hinvalidmc' Hinvalidmci' HsimWeak Hij Hle.
                        exfalso.
                        simpl in Hfb1', Hfb1.
                        apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalidmc.
                        apply Pos.le_lteq in Hle.
                        destruct Hle as [Hlt | Hnbeq].
                        * rewrite Z.pos_sub_gt in Hfb1'; auto. simpl in Hfb1'.
                          apply Pos.le_nlt in Hinvalidmci'.
                          assert (Hinvalid: (Mem.nextblock mc
                                             <=
                                             Z.to_pos (Z.pos_sub b1' (Mem.nextblock mc''
                                                                      - Mem.nextblock mc)))%positive)
                            by (eapply le_sub; eauto).
                          apply Pos.le_nlt in Hinvalid.
                          apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalid.
                          eapply Hfpsep with (b := b1) (i := i) (j := j); eauto.
                        * rewrite Hnbeq in Hfb1'.
                          rewrite Z.pos_sub_diag in Hfb1'.
                          simpl in Hfb1', Hfb1.
                          apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalidmc'.
                          eapply Hfpsep with (b := b1) (i:=i) (j:=j); eauto.
                      + (**case b1 is invalid in mc''*)
                        destruct (valid_block_dec mc'' b1') as [Hvalidmci' | Hinvalidmci'].
                        { (**again orthogonal to the above case*)
                          clear - Hfb1' Hfb1 Htsimj Hfpsep Hexec Hinvalidmc
                                        Hinvalidmc' Hinvalidmci Hvalidmci' HsimWeak Hij
                                        Hle.
                          exfalso.
                          simpl in Hfb1', Hfb1.
                          apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalidmc'.
                          apply Pos.le_lteq in Hle.
                          destruct Hle as [Hlt | Hnbeq].
                          * rewrite Z.pos_sub_gt in Hfb1; auto. simpl in Hfb1.
                            apply Pos.le_nlt in Hinvalidmci.
                            assert (Hinvalid: (Mem.nextblock mc
                                               <=
                                               Z.to_pos (Z.pos_sub b1 (Mem.nextblock mc''
                                                                       - Mem.nextblock mc)))%positive)
                              by (eapply le_sub; eauto).
                            apply Pos.le_nlt in Hinvalid.
                            apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalid.
                            eapply Hfpsep with (b := b1') (i := i) (j := j); eauto.
                          * rewrite Hnbeq in Hfb1.
                            rewrite Z.pos_sub_diag in Hfb1.
                            simpl in Hfb1.
                            apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalidmc.
                            eapply Hfpsep with (b := b1') (b' := b1) (i:=i) (j:=j);
                              by eauto.
                        }
                        { (** case where they are both valid in mcj',
                              by injectivity of fpj for the inverses of b1 and b1'*)
                          simpl in Hfb1, Hfb1'.
                          apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalidmc.
                          apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalidmc'.
                          assert (Heq := (injective (weak_obs_eq (obs_eq_data Htsimj)))
                                           _ _ _ Hfb1 Hfb1').
                          apply Pos.le_lteq in Hle.
                          destruct Hle as [Hlt | Hnbeq].
                          * eapply Pos.le_nlt in Hinvalidmci.
                            eapply Pos.le_nlt in Hinvalidmci'.
                            assert (((Mem.nextblock mc'' - Mem.nextblock mc) < b1)%positive)
                              by (eapply lt_lt_sub; eauto).
                            assert (((Mem.nextblock mc'' - Mem.nextblock mc) < b1')%positive)
                              by (eapply lt_lt_sub; eauto).
                            rewrite Z.pos_sub_gt in Heq; auto.
                            simpl in Heq.
                            apply Z2Pos.inj in Heq;
                              try (rewrite Z.pos_sub_gt; auto;
                                   apply Pos2Z.is_pos). 
                            rewrite Z.pos_sub_gt in Heq; auto.
                            rewrite Z.pos_sub_gt in Heq; auto.
                            inversion Heq as [Heq2].
                            apply Pos.compare_eq_iff in Heq2.
                            rewrite Pos.sub_compare_mono_r in Heq2;
                              try (eapply lt_lt_sub; eauto).
                              by apply Pos.compare_eq_iff.
                          * rewrite Hnbeq in Heq.
                            rewrite Z.pos_sub_diag in Heq.
                            simpl in Heq;
                              by assumption.
                        }
                  }
              }

              (** Before going into the actual proof, some assertions about
                  how the permissions in the various proofs relate.
                  Again we should point at a figure somewhere. *)

              (** For a block that's valid in mc, j-permissions of mcj'
                         and mcj are equal *)
              assert (HpermC_mc_block: forall b1 ofs,
                         Mem.valid_block mc b1 ->
                         permission_at (restrPermMap (Hcompij j pfij).1)
                                       b1 ofs Cur =
                         permission_at (restrPermMap (Hcompjj j pfcjj).1)
                                       b1 ofs Cur /\
                         permission_at (restrPermMap (Hcompij j pfij).2)
                                       b1 ofs Cur =
                         permission_at (restrPermMap (Hcompjj j pfcjj).2)
                                       b1 ofs Cur).
              { intros b1 ofs Hvalidmc.
                specialize (Hincr' b1 b1 ltac:(eapply id_ren_validblock; eauto)).
                pose proof ((perm_obs_strong (strong_obs_eq (obs_eq_locks Hsimij)))
                            b1 b1 ofs Hincr');                  
                  pose proof ((perm_obs_strong (strong_obs_eq (obs_eq_data Hsimij)))
                                b1 b1 ofs Hincr');
                  by eauto.
              }
              (** j-permissions of mcj are higher than mf*)
              assert (HpermF_mcj_data :=
                        perm_obs_weak (weak_obs_eq (obs_eq_data Htsimj))).
              assert (HpermF_mcj_locks :=
                        perm_obs_weak (weak_obs_eq (obs_eq_locks Htsimj))).
              
              (** also j-permissions of mcj are equal to mf*)
              assert (Hpermmcj_F_data := perm_obs_strong (strong_obs_eq
                                                       (obs_eq_data Htsimj))).
              assert (Hpermmcj_F_locks := perm_obs_strong (strong_obs_eq
                                                       (obs_eq_locks Htsimj))).
              
              (** The permission of j at an i-block in mci is
                   empty. We can deduce that by the fact that mc steps
                   to mc'' with i-steps hence the permissions of
                   thread-j will remain empty and then mc'' steps to
                   mcj' and the permissions will remain empty by
                   decay*)
              assert (Hpermj_mc'':
                        forall b1 ofs,
                          ~ Mem.valid_block mc b1 ->
                          Mem.valid_block mc'' b1 ->
                          permission_at (restrPermMap (memCompC'' _ pfcj'').1)
                                        b1 ofs Cur = None /\
                          permission_at (restrPermMap (memCompC'' _ pfcj'').2)
                                        b1 ofs Cur = None).
              { intros b1 ofs Hinvalidmc Hvalidmc''.
                (** Proof that the permission at b1 in mc|j is empty *)
                assert (Hinitp:
                          permission_at (restrPermMap (HmemCompC _ pfcj).1) b1 ofs Cur = None /\
                          permission_at (restrPermMap (HmemCompC _ pfcj).2) b1 ofs Cur = None).
                { apply Mem.nextblock_noaccess with (k := Max) (ofs := ofs)
                    in Hinvalidmc.
                  assert (Hlt := (HmemCompC _ pfcj).1 b1 ofs).
                  assert (Hlt_lock := (HmemCompC _ pfcj).2 b1 ofs).
                  rewrite getMaxPerm_correct in Hlt, Hlt_lock.
                  unfold permission_at in Hlt, Hlt_lock. rewrite Hinvalidmc in Hlt, Hlt_lock.
                  simpl in Hlt, Hlt_lock.
                  rewrite! restrPermMap_Cur.
                  destruct ((getThreadR pfcj).1 # b1 ofs); destruct ((getThreadR pfcj).2 # b1 ofs);
                    by tauto.
                }
                (** Proof that internal execution on thread i
                  preserves these empty permissions*)
                assert (pfcj': containsThread tpc' j)
                  by (eapply containsThread_internal_execution; eauto).
                assert (Hp': permission_at (restrPermMap (memCompC' _ pfcj').1) b1 ofs Cur = None /\
                             permission_at (restrPermMap (memCompC' _ pfcj').2) b1 ofs Cur = None).
                { rewrite! restrPermMap_Cur.
                  erewrite <- gsoThreadR_execution with (pfj := pfcj); eauto.
                  rewrite! restrPermMap_Cur in Hinitp. by assumption.
                }
                rewrite! restrPermMap_Cur.
                erewrite <- gsoThreadR_suspendC with (cntj:= pfcj'); eauto.
                rewrite! restrPermMap_Cur in Hp'.
                  by assumption.
              }

              (** The permission of j at an i-block in mcij/mcj' is empty*)
              assert (Hpermj_mcj': forall b1 ofs,
                         ~ Mem.valid_block mc b1 ->
                         Mem.valid_block mc'' b1 ->
                         permission_at (restrPermMap (Hcompij j pfij).1) b1 ofs Cur = None /\
                         permission_at (restrPermMap (Hcompij j pfij).2) b1 ofs Cur = None).
              { (** Proof: By the fact that this block is allocated by i, we
                           know that the permission of thread j on memory mc''
                           will be empty. Moreover by the decay predicate, mcj'
                           will have the same permission as mc'' on this block
                           (since valid blocks cannot increase their
                           permissions). Moreover lock permissions do not change
                           by internal steps (lemma
                           [internal_execution_locks_eq]) *)
                intros b1 ofs Hinvalidmc Hvalidmc''.
                specialize (Hpermj_mc'' b1 ofs Hinvalidmc Hvalidmc'').
                unfold permission_at in Hpermj_mc''.
                erewrite! restrPermMap_Cur.
                assert (Hdecay := internal_execution_decay).
                specialize (Hdecay _ _ _ _ _ _ _ pfcj'' pfij memCompC''
                                   Hcompij Hexecij).
                specialize (Hdecay b1 ofs).
                destruct Hdecay as [_ Hold].
                erewrite restrPermMap_valid in Hold.
                specialize (Hold Hvalidmc'').
                destruct Hpermj_mc'' as [Hpermj_mc''_data Hpermj_mc''_locks].
                destruct Hold as [Hold | Heq];
                  first by (destruct (Hold Cur); simpl in *; congruence).
                specialize (Heq Cur).
                rewrite Hpermj_mc''_data in Heq.
                assert (Hperm_at := restrPermMap_Cur (Hcompij j pfij).1 b1 ofs).
                unfold permission_at in Hperm_at. rewrite Hperm_at in Heq.
                rewrite <- Heq.
                (** proof of equality for lock permissions*)
                pose proof (internal_execution_locks_eq Hexecij pfcj'' pfij) as Heq_locks.
                rewrite <- Heq_locks.
                assert (Hperm_at_locks := restrPermMap_Cur (memCompC'' j pfcj'').2 b1 ofs).
                unfold permission_at in Hperm_at_locks.
                rewrite <- Hperm_at_locks.
                rewrite Hpermj_mc''_locks.
                split; reflexivity.
              }

              (** The permission of j at an i-block in mf is empty *)
              assert (Hpermj_eqF: forall b1 b2 ofs,
                         ~ Mem.valid_block mc b1 ->
                         Mem.valid_block mc'' b1 ->
                         fp i pfc b1 = Some b2 ->
                         permission_at (restrPermMap (memCompF' j pffj').1) b2 ofs Cur = None /\
                         permission_at (restrPermMap (memCompF' j pffj').2) b2 ofs Cur = None).
              { (** Proof is straightforward by the blocks owned by i invariant*)
                intros b1 b2 ofs Hinvalidmc Hvalidmc'' Hfi.
                rewrite! restrPermMap_Cur.
                erewrite <- gsoThreadR_suspendF with (cntj := pffj) by eauto.
                assert (Hf := (domain_invalid (weak_tsim_data HsimWeak))).
                specialize (Hf b1).
                erewrite restrPermMap_valid in Hf. 
                eapply Hownedi;
                  by eauto.
              }
              
              (** The j-permission of a j-block at mcj is equal to the 
                   permission at mcj'*)
              assert (Hpermmcj_mcj': forall b1' b1 ofs,
                         fij b1' = Some b1 ->
                         permission_at (restrPermMap (Hcompjj j pfcjj).1)
                                       b1' ofs Cur =
                         permission_at (restrPermMap (Hcompij j pfij).1)
                                       b1 ofs Cur /\
                         permission_at (restrPermMap (Hcompjj j pfcjj).2)
                                       b1' ofs Cur =
                         permission_at (restrPermMap (Hcompij j pfij).2)
                                       b1 ofs Cur).
              { intros b1' b1 ofs Hfij;
                pose proof (perm_obs_strong (strong_obs_eq (obs_eq_data Hsimij))
                                            b1' ofs Hfij);
                pose proof (perm_obs_strong (strong_obs_eq (obs_eq_locks Hsimij))
                                            b1' ofs Hfij);
                  by eauto.
              }


              (** Permissions of DryConc are higher than the permissions of FineConc *)
              assert (Hperm_weak:
                        forall (b1 b2 : block) (ofs : Z),
                          (if valid_block_dec mc b1
                           then f b1
                           else
                             if valid_block_dec mc'' b1
                             then fp i pfc b1
                             else
                               fp j pfcj
                                  (Z.to_pos
                                     match (- Z.pos_sub (Mem.nextblock mc'') (Mem.nextblock mc))%Z with
                                     | 0%Z => Z.pos b1
                                     | Z.pos y' => Z.pos (b1 + y')
                                     | Z.neg y' => Z.pos_sub b1 y'
                                     end)) = Some b2 ->
                          Mem.perm_order'' (permission_at (restrPermMap (fst (Hcompij j pfij))) b1 ofs Cur)
                                           (permission_at (restrPermMap (fst (memCompF' j pffj'))) b2 ofs Cur) /\
                          Mem.perm_order'' (permission_at (restrPermMap (snd (Hcompij j pfij))) b1 ofs Cur)
                                           (permission_at (restrPermMap (snd (memCompF' j pffj'))) b2 ofs Cur)). 
              { intros b1 b2 ofs Hf'.
                simpl in Hf'.
                destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
                { (**case it's a block that's valid in mc*)
                  specialize (HpermC_mc_block b1 ofs Hvalidmc).
                  apply Hincrj in Hf'.
                  specialize (HpermF_mcj_data b1 b2 ofs Hf').
                  specialize (HpermF_mcj_locks b1 b2 ofs Hf').
                  rewrite <- HpermC_mc_block.1 in HpermF_mcj_data;
                    rewrite <- HpermC_mc_block.2 in HpermF_mcj_locks.
                  erewrite! restrPermMap_Cur in *.
                  erewrite <- gsoThreadR_suspendF
                  with (cntj := pffj) (cntj' := pffj'); eauto.
                }
                { (**case it's a block that's invalid in mc*)
                  destruct (valid_block_dec mc'' b1)
                    as [Hvalidmc'' | Hinvalidmc''].
                  (**case it's a block that's valid in mc'' (an i-block)*)
                  specialize (Hpermj_eqF _ _ ofs Hinvalidmc Hvalidmc'' Hf').
                  rewrite Hpermj_eqF.1 Hpermj_eqF.2.
                  specialize (Hpermj_mcj' b1 ofs Hinvalidmc Hvalidmc'').
                  rewrite Hpermj_mcj'.1 Hpermj_mcj'.2.
                  simpl;
                    by constructor.
                  (**case it's a block that's invalid in mc'' *)
                  specialize (Hvalidmcj' _ _ pfcj Hinvalidmc Hinvalidmc'' Hf').
                  specialize (Hinverse b1 Hvalidmcj' Hinvalidmc'').
                  simpl in Hinverse.
                  destruct Hinverse as [Hfij _].
                  specialize (HpermF_mcj_data _ _ ofs Hf').
                  specialize (HpermF_mcj_locks _ _ ofs Hf').
                  specialize (Hpermmcj_F_data _ _ ofs Hf').
                  specialize (Hpermmcj_F_locks _ _ ofs Hf').
                  replace (permission_at (restrPermMap (fst (memCompF' j pffj'))) b2 ofs Cur)
                  with ((getThreadR pffj').1 # b2 ofs)
                    by (rewrite restrPermMap_Cur; reflexivity).
                  replace (permission_at (restrPermMap (snd (memCompF' j pffj'))) b2 ofs Cur)
                  with ((getThreadR pffj').2 # b2 ofs)
                    by (rewrite restrPermMap_Cur; reflexivity).
                  erewrite <- gsoThreadR_suspendF with (cntj := pffj) (cntj' := pffj'); eauto.
                  replace ((getThreadR pffj).1 # b2 ofs) with
                  (permission_at (restrPermMap (fst (mem_compf Hsim _ pffj))) b2 ofs Cur)
                    by (rewrite restrPermMap_Cur; reflexivity).
                  replace ((getThreadR pffj).2 # b2 ofs) with
                  (permission_at (restrPermMap (snd (mem_compf Hsim _ pffj))) b2 ofs Cur)
                    by (rewrite restrPermMap_Cur; reflexivity).
                  specialize (Hpermmcj_mcj' _ _ ofs Hfij).
                  rewrite <- Hpermmcj_mcj'.1; rewrite <- Hpermmcj_mcj'.2;
                    by auto.
                }
              }

              (** **** Proofs of the components of [strong_mem_obs_eq]*)

              (** proof of [perm_obs_strong] *)
              assert (Hstrong_perm_eq: forall b1 b2 ofs
                                         (Hrenaming: (if is_left (valid_block_dec mc b1)
                                                      then f b1
                                                      else
                                                        if is_left (valid_block_dec mc'' b1)
                                                        then fp i pfc b1
                                                        else
                                                          fp j pfcj
                                                             (Z.to_pos
                                                                match (- Z.pos_sub (Mem.nextblock mc'') (Mem.nextblock mc))%Z with
                                                                | 0%Z => Z.pos b1
                                                                | Z.pos y' => Z.pos (b1 + y')
                                                                | Z.neg y' => Z.pos_sub b1 y'
                                                                end)) = Some b2),
                         permission_at (restrPermMap (memCompF' j pffj').1) b2 ofs Cur =
                         permission_at (restrPermMap (Hcompij j pfij).1) b1 ofs Cur /\
                         permission_at (restrPermMap (memCompF' j pffj').2) b2 ofs Cur =
                         permission_at (restrPermMap (Hcompij j pfij).2) b1 ofs Cur).
              { intros b1 b2 ofs Hf'.
                (** the permissions of mf' and mf are the same,
                     suspend step does not touch the memory*)
                rewrite! restrPermMap_Cur.
                erewrite <- gsoThreadR_suspendF
                with (cntj := pffj) (cntj' := pffj'); eauto.
                rewrite <- restrPermMap_Cur with (Hlt := (mem_compf Hsim _ pffj).1).
                rewrite <- restrPermMap_Cur with (Hlt := (mem_compf Hsim _ pffj).2).
                destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
                - (** b is a valid block in mc*)
                  specialize (HpermC_mc_block _ ofs Hvalidmc).
                  apply Hincrj in Hf'.
                  specialize (Hpermmcj_F_data _ _ ofs Hf').
                  specialize (Hpermmcj_F_locks _ _ ofs Hf').
                  rewrite <- HpermC_mc_block.1 in Hpermmcj_F_data.
                  rewrite <- HpermC_mc_block.2 in Hpermmcj_F_locks.
                  rewrite Hpermmcj_F_data Hpermmcj_F_locks.
                  rewrite! restrPermMap_Cur; auto.
                - destruct (valid_block_dec mc'' b1)
                    as [Hvalidmc'' | Hinvalidmc''].
                  + (* b1 is an i-block (allocated by thread i) *)
                    specialize (Hpermj_mcj' _ ofs Hinvalidmc Hvalidmc'').
                    rewrite! restrPermMap_Cur in Hpermj_mcj'.
                    rewrite Hpermj_mcj'.1 Hpermj_mcj'.2.
                    simpl in Hf'.
                    apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalidmc.
                    rewrite! restrPermMap_Cur;
                      by eauto.
                  + specialize (Hvalidmcj' _ _ _ Hinvalidmc Hinvalidmc'' Hf').
                    specialize (Hinverse b1 Hvalidmcj' Hinvalidmc'').
                    simpl in Hinverse.
                    destruct Hinverse as [Hfij _].
                    specialize (Hpermmcj_mcj' _ _ ofs Hfij).
                    simpl in Hf'.
                    rewrite <- restrPermMap_Cur with (Hlt := (Hcompij j pfij).1).
                    rewrite <- restrPermMap_Cur with (Hlt := (Hcompij j pfij).2).
                    rewrite <- Hpermmcj_mcj'.1, <- Hpermmcj_mcj'.2;
                      by eauto.
              }

              (** Proof of [val_obs_eq] *)
              assert (Hval_obs_eq:   forall (b1 b2 : block) (ofs : Z),
                         (if is_left (valid_block_dec mc b1)
                          then f b1
                          else
                            if is_left (valid_block_dec mc'' b1)
                            then fp i pfc b1
                            else
                              fp j pfcj
                                 (Z.to_pos
                                    match (- Z.pos_sub (Mem.nextblock mc'') (Mem.nextblock mc))%Z with
                                    | 0%Z => Z.pos b1
                                    | Z.pos y' => Z.pos (b1 + y')
                                    | Z.neg y' => Z.pos_sub b1 y'
                                    end)) = Some b2 ->
                         (Mem.perm (restrPermMap (fst (Hcompij j pfij))) b1 ofs Cur Readable \/
                          Mem.perm (restrPermMap (snd (Hcompij j pfij))) b1 ofs Cur Readable) ->
                         memval_obs_eq
                           (fun b0 : block =>
                              if is_left (valid_block_dec mc b0)
                              then f b0
                              else
                                if is_left (valid_block_dec mc'' b0)
                                then fp i pfc b0
                                else
                                  fp j pfcj
                                     (Z.to_pos
                                        match (- Z.pos_sub (Mem.nextblock mc'') (Mem.nextblock mc))%Z with
                                        | 0%Z => Z.pos b0
                                        | Z.pos y' => Z.pos (b0 + y')
                                        | Z.neg y' => Z.pos_sub b0 y'
                                        end)) (ZMap.get ofs (Mem.mem_contents mcj') # b1)
                                                        (ZMap.get ofs (Mem.mem_contents mf) # b2)).
                { intros b1 b2 ofs Hf' Hreadable.
                  simpl.
                  assert (Hvalmcj_mcj'_data := val_obs_eq (strong_obs_eq (obs_eq_data Hsimij)));
                    simpl in Hvalmcj_mcj'_data.
                  assert (Hvalmcj_mcj'_locks := val_obs_eq (strong_obs_eq (obs_eq_locks Hsimij)));
                    simpl in Hvalmcj_mcj'_locks.
                  assert (Hvalmcj_mf_data := (val_obs_eq (strong_obs_eq (obs_eq_data Htsimj))));
                    simpl in Hvalmcj_mf_data.
                  assert (Hvalmcj_mf_locks := (val_obs_eq (strong_obs_eq (obs_eq_locks Htsimj))));
                    simpl in Hvalmcj_mf_locks.
                  destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc] eqn:Hvalidmcdec.
                - (** Value of a block that is valid in mc *)
                  (** Idea: this block is mapped between mcj and mcj' by id
                       and from mcj to mf by fj. Hence we can reuse fj *)
                  assert (Hincr'_b1 := Hincr' b1 b1 ltac:(eapply id_ren_validblock; eauto)).
                  apply Hincrj in Hf'.

                  assert (Hvalmcj_mcj'_b1_data := Hvalmcj_mcj'_data _ _ ofs Hincr'_b1).
                  assert (Hvalmcj_mcj'_b1_locks := Hvalmcj_mcj'_locks _ _ ofs Hincr'_b1).
                  assert (Hvalmcj_mf_b1_data := Hvalmcj_mf_data _ _ ofs Hf').
                  assert (Hvalmcj_mf_b1_locks := Hvalmcj_mf_locks _ _ ofs Hf').
                  unfold Mem.perm in Hreadable, Hvalmcj_mcj'_b1_data, Hvalmcj_mcj'_b1_locks,
                                     Hvalmcj_mf_b1_data, Hvalmcj_mf_b1_locks.
                  destruct (Hpermmcj_mcj' _ _ ofs Hincr'_b1) as [Hreadable'_data Hreadable'_locks].
                  unfold permission_at in *.
                  rewrite <- Hreadable'_data, <- Hreadable'_locks in Hreadable.
                  assert (Hvalmcj_mf_b1:  memval_obs_eq (fp j pfcj)
                                                        (ZMap.get ofs (Mem.mem_contents mcj) # b1)
                                                        (ZMap.get ofs (Mem.mem_contents mf) # b2))
                    by (destruct Hreadable as [Hreadable | Hreadable]; eauto).
                  assert (Hvalmcj_mcj'_b1: memval_obs_eq fij
                                                         (ZMap.get ofs (Mem.mem_contents mcj) # b1)
                                                         (ZMap.get ofs (Mem.mem_contents mcj') # b1))
                    by (destruct Hreadable as [Hreadable | Hreadable]; eauto).

                  (*TODO: can we make a lemma for this "transitive" reasoning*)
                  inversion Hvalmcj_mcj'_b1 as
                      [n Hn_mcj Hn_mcj' | vj vj' q1 n Hval_obsjj' Hvj Hvj'
                       | Hundef_mcj Hmv_mcj'].
                  + rewrite <- Hn_mcj in Hvalmcj_mf_b1.
                    inversion Hvalmcj_mf_b1 as [n0 Heq Hn_mf| |];
                      first by constructor.
                  + (* Fragments case *)
                    rewrite <- Hvj in Hvalmcj_mf_b1.
                    inversion Hvalmcj_mf_b1 as [| vj0 vf q n0 Hval_obsjf Hvj0 Hvf |];
                      subst vj0 q1 n0.
                    constructor.
                    inversion Hval_obsjj' as [| | | | bpj1 bpj'2 ofsp Hfijp|]; subst;
                    inversion Hval_obsjf as [| | | | bpj0 bpf2 ofspf Hf'p|];
                    try subst bpj0; subst; try by constructor.
                    clear Hval_obsjf Hval_obsjj' Hvf Hvj.
                    constructor.
                    destruct (valid_block_dec mc bpj1) as [Hvalidmcbpj1 | Hinvalidmcbpj1]
                                                            eqn:Hdecbpj1.
                    { assert (Hincr'_bpj1 := Hincr' bpj1 bpj1 ltac:(eapply id_ren_validblock; eauto)).
                      rewrite Hincr'_bpj1 in Hfijp; inversion Hfijp; subst bpj'2.
                      rewrite Hdecbpj1.
                      clear Hfijp Hdecbpj1.
                      simpl.
                      apply (domain_valid (weak_tsim_data HsimWeak)) in Hvalidmcbpj1.
                      destruct Hvalidmcbpj1 as [b2' Hf].
                      assert (b2' = bpf2)
                        by (apply Hincrj in Hf; rewrite Hf in Hf'p; by inversion Hf'p);
                        by subst.
                    }
                    { (* here it is usefulto have inject seperation for fij*)
                      unfold inject_separated in Hsep.
                      specialize (Hsep bpj1 bpj'2
                                       ltac:(eapply id_ren_invalidblock; eauto) Hfijp).
                      destruct Hsep as [_ Hinvalidmc''bpj'2].
                      assert (Hinvalidbmcpj'2: ~ Mem.valid_block mc bpj'2).
                      { intros Hcontra.
                        eapply internal_execution_valid with
                        (b := bpj'2) (m' := mc'') in Hcontra;
                          by eauto.
                      }
                      destruct (valid_block_dec mc bpj'2) as
                          [Hvalidmcbpj'2 | Hinvalidmcbpj'2];
                        first (by exfalso; auto).
                      simpl.
                      destruct (valid_block_dec mc'' bpj'2) as [? | ?];
                        first by (exfalso; auto).
                      simpl.
                      destruct (valid_block_dec mcj' bpj'2) as [Hvalidmcj'bpj'2 | Hcontra].
                      specialize (Hinverse _ Hvalidmcj'bpj'2 Hinvalidmc''bpj'2).
                      simpl in Hinverse.
                      destruct Hinverse as [Hfij0 Hfid0].
                      clear HpermC_mc_block HpermF_mcj_data HpermF_mcj_locks
                            Hpermmcj_F_data Hpermmcj_F_locks Hpermj_mc'' Hreadable'_data
                            Hreadable'_locks Hreadable Hpermmcj_mcj' Hpermj_eqF Hvj'.
                      clear Hdecbpj1.
                      apply (domain_invalid (weak_obs_eq (obs_eq_data Hsim_c_ci)))
                        in Hinvalidmcbpj1.
                      assert (Hinj := injective (weak_obs_eq (obs_eq_data Hsimij))).
                      specialize (Hinj _ _ _ Hfij0 Hfijp).
                      subst bpj1;
                        by assumption.
                      apply (codomain_valid (weak_obs_eq (obs_eq_data Hsimij))) in Hfijp.
                      erewrite restrPermMap_valid in Hfijp;
                        by exfalso.
                    }
                    rewrite <- Hundef_mcj in Hvalmcj_mf_b1.
                    inversion Hvalmcj_mf_b1;
                      by constructor.
                - (* Notice that this case is exactly the same as
                       above.  What changes is in which memory region
                       the pointer is in, but the proof about the
                       pointer itself is the same.  TODO: can we merge
                       the two cases? I think no, but need to check
                       again *)

                  destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''].
                  destruct (Hpermj_mcj' _ ofs Hinvalidmc Hvalidmc'')
                           as [Hreadable_data Hreadable_locks].
                  unfold Mem.perm in Hreadable.
                  unfold permission_at in Hreadable_data, Hreadable_locks.
                  rewrite Hreadable_data Hreadable_locks in Hreadable.
                  simpl in Hreadable; destruct Hreadable;
                    by exfalso.
                  specialize (Hvalidmcj' _ _ _ Hinvalidmc Hinvalidmc'' Hf').
                  assert (Hinverse_b1 := Hinverse _ Hvalidmcj' Hinvalidmc'').
                  simpl in Hinverse_b1.
                  destruct Hinverse_b1 as [Hfij _].
                  assert (Hpermeq := Hpermmcj_mcj' _ _ ofs Hfij).
                  simpl in Hf'.
                  assert (Hmem_val_obs_eq:
                            memval_obs_eq fij (ZMap.get ofs (Mem.mem_contents mcj) #
                                                        (Z.to_pos
                                                           match (- Z.pos_sub (Mem.nextblock mc'') (Mem.nextblock mc))%Z with
                                                           | 0%Z => Z.pos b1
                                                           | Z.pos y' => Z.pos (b1 + y')
                                                           | Z.neg y' => Z.pos_sub b1 y'
                                                           end)) (ZMap.get ofs (Mem.mem_contents mcj') # b1) /\
                            memval_obs_eq (fp j pfcj) (ZMap.get ofs (Mem.mem_contents mcj) #
                                                                (Z.to_pos
                                                                   match (- Z.pos_sub (Mem.nextblock mc'') (Mem.nextblock mc))%Z with
                                                                   | 0%Z => Z.pos b1
                                                                   | Z.pos y' => Z.pos (b1 + y')
                                                                   | Z.neg y' => Z.pos_sub b1 y'
                                                                   end)) (ZMap.get ofs (Mem.mem_contents mf) # b2)).
                  { assert (Hreadable': Mem.perm (restrPermMap (Hcompjj j pfcjj).1)
                                                 ((Z.to_pos
                                                     match
                                                       (- Z.pos_sub (Mem.nextblock mc'')
                                                                    (Mem.nextblock mc))%Z
                                                     with
                                                     | 0%Z => Z.pos b1
                                                     | Z.pos y' => Z.pos (b1 + y')
                                                     | Z.neg y' => Z.pos_sub b1 y'
                                                     end)) ofs Cur Readable \/
                                        Mem.perm (restrPermMap (Hcompjj j pfcjj).2)
                                                 ((Z.to_pos
                                                     match
                                                       (- Z.pos_sub (Mem.nextblock mc'')
                                                                    (Mem.nextblock mc))%Z
                                                     with
                                                     | 0%Z => Z.pos b1
                                                     | Z.pos y' => Z.pos (b1 + y')
                                                     | Z.neg y' => Z.pos_sub b1 y'
                                                     end)) ofs Cur Readable)
                      by (unfold Mem.perm in *; unfold permission_at in Hpermeq;
                          rewrite Hpermeq.1 Hpermeq.2; eauto).
                    destruct Hreadable' as [Hreadable' | Hreadable'];
                    [specialize (Hvalmcj_mcj'_data _ _ ofs Hfij Hreadable');
                     specialize (Hvalmcj_mf_data _ _ ofs Hf' Hreadable') |
                     specialize (Hvalmcj_mcj'_locks _ _ ofs Hfij Hreadable');
                     specialize (Hvalmcj_mf_locks _ _ ofs Hf' Hreadable')]; eauto.
                  }
                  clear Hreadable Hpermeq Hpermmcj_mcj' Hpermj_eqF Hpermj_mcj'
                  Hpermj_mc'' Hpermmcj_F_data Hpermmcj_F_locks HpermF_mcj_data HpermF_mcj_locks HpermC_mc_block.
                  destruct Hmem_val_obs_eq as [Hvalmcj_mcj' Hvalmcj_mf].
                  inversion Hvalmcj_mcj' as
                      [n Hn_mcj Hn_mcj' | vj vj' q1 n Hval_obsjj' Hvj Hvj'| Hundef_mcj Hmv_mcj'].
                  + rewrite <- Hn_mcj in Hvalmcj_mf.
                    inversion Hvalmcj_mf as [n0 Heq Hn_mf| |];
                      first by constructor.
                  + (* Fragments case *)
                    rewrite <- Hvj in Hvalmcj_mf.
                    inversion Hvalmcj_mf as [| vj0 vf q n0 Hval_obsjf Hvj0 Hvf |];
                      subst vj0 q1 n0.
                    constructor.
                    inversion Hval_obsjj' as [| | | | bpj1 bpj'2 ofsp Hfijp|]; subst;
                    inversion Hval_obsjf as [| | | | bpj0 bpf2 ofspf Hf'p|];
                    try subst bpj0; subst; try by constructor.
                    clear Hval_obsjf Hval_obsjj' Hvf Hvj.
                    constructor.
                    destruct (valid_block_dec mc bpj1) as [Hvalidmcbpj1 | Hinvalidmcbpj1]
                                                            eqn:Hdecbpj1.
                    { assert (Hincr'_bpj1 := Hincr' bpj1 bpj1
                                                    ltac:(eapply id_ren_validblock; eauto)).
                      rewrite Hincr'_bpj1 in Hfijp; inversion Hfijp; subst bpj'2.
                      rewrite Hdecbpj1.
                      clear Hfijp Hdecbpj1.
                      simpl.
                      apply (domain_valid (weak_tsim_data HsimWeak)) in Hvalidmcbpj1.
                      destruct Hvalidmcbpj1 as [b2' Hf].
                      assert (b2' = bpf2)
                        by (apply Hincrj in Hf; rewrite Hf in Hf'p; by inversion Hf'p);
                        by subst.
                    }
                    { (* here it is usefulto have inject seperation for fij*)
                      unfold inject_separated in Hsep.
                      specialize (Hsep bpj1 bpj'2
                                       ltac:(eapply id_ren_invalidblock; eauto) Hfijp).
                      destruct Hsep as [_ Hinvalidmc''bpj'2].
                      assert (Hinvalidbmcpj'2: ~ Mem.valid_block mc bpj'2).
                      { intros Hcontra.
                        eapply internal_execution_valid with
                        (b := bpj'2) (m' := mc'') in Hcontra;
                          by eauto.
                      }
                      destruct (valid_block_dec mc bpj'2) as
                          [Hvalidmcbpj'2 | Hinvalidmcbpj'2];
                        first (by exfalso; auto).
                      destruct (valid_block_dec mc'' bpj'2) as [? | ?];
                        first by (exfalso; auto).
                      destruct (valid_block_dec mcj' bpj'2) as [Hvalidmcj'bpj'2 | Hcontra].
                      simpl.
                      specialize (Hinverse _ Hvalidmcj'bpj'2 Hinvalidmc''bpj'2).
                      simpl in Hinverse.
                      destruct Hinverse as [Hfij0' Hfid0'].
                      (* NOTE: i need injectivity for the newly
                           (Separated) blocks. So fij bpj1 and fij
                           imply b0 = bpj1. I can have that *)
                      clear Hdecbpj1.
                      apply (domain_invalid (weak_obs_eq (obs_eq_data Hsim_c_ci)))
                        in Hinvalidmcbpj1.
                      assert (Hinj := injective (weak_obs_eq (obs_eq_data Hsimij))).
                      specialize (Hinj _ _ _  Hfij0' Hfijp).
                      subst bpj1;
                        by assumption.
                      apply (codomain_valid (weak_obs_eq (obs_eq_data Hsimij))) in Hfijp.
                      erewrite restrPermMap_valid in Hfijp;
                        by exfalso.
                    }
                    rewrite <- Hundef_mcj in Hvalmcj_mf.
                    inversion Hvalmcj_mf.
                      by constructor.
                }
                constructor.
            - (** code injection between thread j on tpj' and tpf'*)
              assert (Hctlij := code_eq Hsimij).
              assert (Hctljj := code_eq Htsimj).
              erewrite <- gsoThreadC_suspendF with (cntj := pffj) (cntj' := pffj');
                eauto.
              eapply ctl_inj_trans with (c:= getThreadC pfcjj); eauto.
              (** transitivity of f''*)              
              intros b b' b'' Hfpj Hfij.
              destruct (valid_block_dec mc b'); simpl.
              assert (Hfid := (domain_valid (weak_obs_eq (obs_eq_data Hsim_c_ci))) _ v).
              destruct Hfid as [b2' Hfid].
              assert (b' = b2')
                by (apply id_ren_correct in Hfid; auto); subst b2'.
              apply Hincr' in Hfid.
              assert (b = b')
                by (eapply (injective (weak_obs_eq (obs_eq_data Hsimij))); eauto);
                subst.
              apply (domain_valid (weak_tsim_data HsimWeak)) in v.
              destruct v as [b2' Hf].
              assert (b2' = b'')
                by ( apply Hincrj in Hf;
                     rewrite Hf in Hfpj; by inversion Hfpj);
                by subst b2'.
              destruct (valid_block_dec mc'' b').
              destruct (valid_block_dec mc b) eqn:dec_mc_b.
              assert (v0' := v0).
              apply (domain_valid (weak_obs_eq (obs_eq_data Hsim_c_ci))) in v0'.
              destruct v0' as [b2' Hid].
              assert (b = b2')
                by (apply id_ren_correct in Hid; auto); subst b2'.
              apply Hincr' in Hid. rewrite Hfij in Hid.
              inversion Hid; subst;
                by exfalso.
              clear dec_mc_b.
              apply (domain_invalid (weak_obs_eq (obs_eq_data Hsim_c_ci))) in n0.
              specialize (Hsep _ _ n0 Hfij).
              destruct Hsep as [? ?];
                by exfalso.
              destruct (valid_block_dec mc b) as [Hcontra | ?].
              assert (Hfid :=
                        (domain_valid (weak_obs_eq (obs_eq_data Hsim_c_ci))) _ Hcontra).
              destruct Hfid as [b2' Hfid].
              assert (b = b2')
                by (apply id_ren_correct in Hfid; auto); subst b2'.
              apply Hincr' in Hfid. rewrite Hfij in Hfid.
              inversion Hfid; subst;
                by exfalso.
              assert (Hvalidb': Mem.valid_block mcj' b')
                by ( apply (codomain_valid (weak_obs_eq (obs_eq_data Hsimij))) in Hfij;
                       by erewrite restrPermMap_valid in Hfij).
              specialize (Hinverse _ Hvalidb' n0).
              simpl in Hinverse.
              destruct Hinverse as [Hfij' Hg].
              assert (Hinj := injective (weak_obs_eq (obs_eq_data Hsimij))).
              assert (b = Z.to_pos
                            match
                              (- Z.pos_sub (Mem.nextblock mc'')
                                           (Mem.nextblock mc))%Z
                            with
                            | 0%Z => Z.pos b'
                            | Z.pos y' => Z.pos (b' + y')
                            | Z.neg y' => Z.pos_sub b' y'
                            end)
                by (eapply Hinj; eauto;
                    assert (Hfid_domain:= iffLRn (id_ren_domain mc b) n1);
                    subst b; eauto);
                by subst.
            - (** mem_obs_eq between thread-j on mij=mcj' and on mff' on data permissions*)
              do 2 constructor; intros; eauto.
              erewrite restrPermMap_valid; eauto.
              now eapply ((Hperm_weak _ _ ofs Hrenaming).1).
              now eapply (Hstrong_perm_eq _ _ ofs Hrenaming).1.
              do 2 constructor; intros; eauto.
              erewrite restrPermMap_valid; eauto.
              now eapply ((Hperm_weak _ _ ofs Hrenaming).2).
              now eapply (Hstrong_perm_eq _ _ ofs Hrenaming).2.
          }
          split.
          { (** Proof that block ownership is preserved*)
            intros k pffk' Hjk b1 b2 ofs Hf' Hfi.
            destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
            - (** If b1 is valid in mc then it should be in f and
                since fi is an extension of f it should be in fi as
                well *)
              simpl in Hf'.
              apply (domain_valid (weak_tsim_data HsimWeak)) in Hvalidmc.
              destruct Hvalidmc as [? Hf].
              apply Hincr in Hf. by congruence.
            - destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''];
              first by (simpl in Hf'; congruence).
              specialize (Hvalidmcj' _ _ _ Hinvalidmc Hinvalidmc'' Hf').
              destruct (Hinverse _ Hvalidmcj' Hinvalidmc'') as [Hfij ?].
              unfold inject_separated in Hsep.
              specialize (Hsep _ _ H Hfij).
              destruct Hsep as [Hinvalidb0 _].
              apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalidb0.
              assert (pffk: containsThread tpf k)
                by (eapply suspendF_containsThread with (cnti := pff); eauto).
              specialize (Hownedj _ pffk Hjk _ _ ofs Hf' Hinvalidb0).
              erewrite <- gsoThreadR_suspendF with (cntj := pffk);
                by eauto.
          }
          { (** Block ownership with lock resources *)
            intros bl ofsl rmap b1 b2 ofs Hf' Hfi Hres.
            destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
            - (** If b1 is valid in mc then it should be in f and
                since fi is an extension of f it should be in fi as
                well *)
              simpl in Hf'.
              apply (domain_valid (weak_tsim_data HsimWeak)) in Hvalidmc.
              destruct Hvalidmc as [? Hf].
              apply Hincr in Hf. by congruence.
            - destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''];
              first by (simpl in Hf'; congruence).
              specialize (Hvalidmcj' _ _ _ Hinvalidmc Hinvalidmc'' Hf').
              destruct (Hinverse _ Hvalidmcj' Hinvalidmc'') as [Hfij Hfinv].
              unfold inject_separated in Hsep.
              specialize (Hsep _ _ Hfinv Hfij).
              destruct Hsep as [Hinvalidb0 _].
              apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalidb0.
              simpl in Hf'.
              erewrite <- suspendF_lockPool with (tp := tpf) in Hres;
                by eauto.
          }
        }
      }
      { (** Proof of strong simulation of resources *)
        clear - HstepF Hexec HsuspendC HsimRes Hincr Htsim
                       HsimWeak Hownedi_lp.
        destruct HsimRes as [HsimRes [Hlock_mapped Hlock_if]].
        split.
        - intros bl1 bl2 ofs rmap1 rmap2 Hfl Hl1'' Hl2'.
          (** The [lockRes] of the DryConc machine remained unchanged*)
          assert (Hl1: lockRes tpc (bl1,ofs) = Some rmap1)
            by (erewrite <- suspendC_lockPool with (pfc := pfc') in Hl1''; eauto;
                erewrite <- gsoLockPool_execution in Hl1''; eauto).

          (** The [lockRes] of the FineConc machine remained unchanged*)
          assert (Hl2: lockRes tpf (bl2,ofs) = Some rmap2)
            by (erewrite <- suspendF_lockPool with (pff := pff) in Hl2'; eauto).

          assert (pff': containsThread tpf' i)
            by (eapply suspendF_containsThread with (cnti := pff); eauto).          
          
          assert (Hperm_eq: forall b ofs,
                     permission_at (restrPermMap (compat_lp memCompC'' _ Hl1'').1) b ofs Cur =
                     permission_at (restrPermMap (compat_lp HmemCompC _ Hl1).1) b ofs Cur /\
                     permission_at (restrPermMap (compat_lp memCompC'' _ Hl1'').2) b ofs Cur =
                     permission_at (restrPermMap (compat_lp HmemCompC _ Hl1).2) b ofs Cur)
            by (intros; split; by rewrite! restrPermMap_Cur).

                   
          assert (Hvalid: Mem.valid_block mc (bl1, ofs).1)
            by (eapply (lockRes_blocks HmemCompC); eauto).
          specialize (HsimWeak _ pfc pff).
          apply (domain_valid (weak_tsim_data HsimWeak)) in Hvalid.
          destruct Hvalid as [bl2' Hfl0].
          assert (bl2 = bl2')
            by (apply Hincr in Hfl0; rewrite Hfl in Hfl0; by inversion Hfl0); subst.

          specialize (HsimRes _ _ _ _ _ Hfl0 Hl1 Hl2).
          destruct HsimRes as [HsimRes_data HsimRes_locks].
          destruct HsimRes_data as [HpermRes_data HvalRes_data].
          destruct HsimRes_locks as [HpermRes_locks HvalRes_locks].
          assert (Hperm_strong:
                    forall (b1 b2 : block) (ofs0 : Z),
                      fp i pfc b1 = Some b2 ->
                      permission_at (restrPermMap (compat_lp memCompF' (bl2', ofs) Hl2')#1) b2 ofs0 Cur =
                      permission_at (restrPermMap (compat_lp memCompC'' (bl1, ofs) Hl1'')#1) b1 ofs0 Cur /\
                      permission_at (restrPermMap (compat_lp memCompF' (bl2', ofs) Hl2')#2) b2 ofs0 Cur =
                      permission_at (restrPermMap (compat_lp memCompC'' (bl1, ofs) Hl1'')#2) b1 ofs0 Cur).
          { intros b1 b2 ofs0 Hf1.
            specialize (Hperm_eq b1 ofs0).
            rewrite Hperm_eq.1 Hperm_eq.2.

            rewrite! restrPermMap_Cur.
            destruct (valid_block_dec mc b1) as [Hvalid | Hinvalid].
            - apply (domain_valid (weak_tsim_data HsimWeak)) in Hvalid.
              destruct Hvalid as [b2' Hf].
              assert (b2' = b2)
                by (apply Hincr in Hf; rewrite Hf in Hf1; by inversion Hf1);
                subst b2'.
              specialize (HpermRes_data _ _ ofs0 Hf);
                specialize (HpermRes_locks _ _ ofs0 Hf);
                  by rewrite! restrPermMap_Cur in HpermRes_locks HpermRes_data.
            - assert (Hempty:= Mem.nextblock_noaccess _ _ ofs0 Max Hinvalid).
              assert (Hlt1:= ((compat_lp HmemCompC _ Hl1).1 b1 ofs0)).
              assert (Hlt2:= ((compat_lp HmemCompC _ Hl1).2 b1 ofs0)).
              rewrite getMaxPerm_correct in Hlt1 Hlt2. unfold permission_at in Hlt1, Hlt2.
              rewrite Hempty in Hlt1 Hlt2. simpl in Hlt1, Hlt2.
              destruct (rmap1.1 # b1 ofs0);
                first by exfalso.
              destruct (rmap1.2 # b1 ofs0);
                first by exfalso.
              apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalid.
              eapply Hownedi_lp;
                by eauto.
          }

          (** [val_obs_eq] for lockpool*)
          assert (Hval_obs_eq:
                    forall (b1 b2 : block) (ofs0 : Z),
                      fp i pfc b1 = Some b2 ->
                      (Mem.perm (restrPermMap (proj1 (compat_lp memCompC'' (bl1, ofs) Hl1''))) b1 ofs0 Cur Readable \/
                      Mem.perm (restrPermMap (proj2 (compat_lp memCompC'' (bl1, ofs) Hl1''))) b1 ofs0 Cur Readable) -> 
                      memval_obs_eq (fp i pfc) (ZMap.get ofs0 (Mem.mem_contents mc'') # b1) (ZMap.get ofs0 (Mem.mem_contents mf) # b2)).
          { intros b1 b2 ofs0 Hfi Hperm.
            simpl.
            unfold Mem.perm in *.
            unfold permission_at in Hperm_eq.
            rewrite (Hperm_eq b1 ofs0).1 in Hperm.
            rewrite (Hperm_eq b1 ofs0).2 in Hperm.
            destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
            - apply (domain_valid (weak_tsim_data HsimWeak)) in Hvalidmc.
              destruct Hvalidmc as [b2' Hf].
              assert (b2 = b2')
                by (apply Hincr in Hf; rewrite Hfi in Hf; by inversion Hf);
                subst b2'.
              erewrite <- internal_exec_disjoint_val_lockPool with (m := mc) (tp := tpc);
                unfold Mem.perm; eauto.
              assert (HvalRes: memval_obs_eq f (ZMap.get ofs0 (Mem.mem_contents mc) # b1) (ZMap.get ofs0 (Mem.mem_contents mf) # b2)).
              { destruct Hperm as [Hperm | Hperm].
                specialize (HvalRes_data _ _ ofs0 Hf Hperm); eauto.
                specialize (HvalRes_locks _ _ _ Hf Hperm); eauto.
              }
              eapply memval_obs_eq_incr;
                by eauto.
            - assert (Hempty:= Mem.nextblock_noaccess _ _ ofs0 Max Hinvalidmc).
              assert (Hlt1:= (compat_lp HmemCompC _ Hl1).1 b1 ofs0).
              assert (Hlt2:= (compat_lp HmemCompC _ Hl1).2 b1 ofs0).
              rewrite getMaxPerm_correct in Hlt1 Hlt2. unfold permission_at in Hlt1, Hlt2.
              rewrite Hempty in Hlt1 Hlt2. simpl in Hlt1, Hlt2.
              apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalidmc.
              assert (Hcontra1:= restrPermMap_Cur (compat_lp HmemCompC _ Hl1).1 b1 ofs0).
              assert (Hcontra2:= restrPermMap_Cur (compat_lp HmemCompC _ Hl1).2 b1 ofs0).
              unfold permission_at in Hcontra1, Hcontra2. rewrite Hcontra1 Hcontra2 in Hperm.
              destruct (rmap1.1 # b1 ofs0);
                try by (simpl in Hperm; exfalso).
              destruct (rmap1.2 # b1 ofs0);
                try by (simpl in Hperm; exfalso).
              destruct Hperm as [Hperm | Hperm];
                by inversion Hperm.
          }
          split; constructor;
            intros; destruct (Hperm_strong _ _ ofs0 Hrenaming);
              by eauto.
          split.
        - (** lockRes on the FineConc machine are always mapped*)
          intros bl2 ofs Hres.
          erewrite <- suspendF_lockRes with (tp := tpf) in Hres by eauto.
          specialize (Hlock_mapped _ _ Hres).
          destruct Hlock_mapped as [bl1 Hf].
          eapply Hincr in Hf.
          eexists; eauto.
        - (** the two machines have the same [lockRes]*)
          intros bl1 bl2 ofs Hf.
          erewrite <- suspendF_lockRes with (tp' := tpf') (tp := tpf) by eauto.
          erewrite <- suspendC_lockPool with (tp := tpc') (tp' := tpc'') by eauto.
          erewrite <- gsoLockPool_execution; eauto.
          specialize (HsimWeak _ pfc pff).
          split; intros Hres.
          eapply Hlock_if; eauto.
          destruct (lockRes tpc (bl1, ofs)) eqn:Hres'; try by exfalso.
          apply (lockRes_blocks HmemCompC) in Hres'.
          apply (domain_valid (weak_tsim_data HsimWeak)) in Hres'.
          destruct Hres' as [bl2' Hf'].
          assert (bl2 = bl2')
            by (apply Hincr in Hf'; rewrite Hf in Hf';
                inversion Hf'; subst; auto);
            subst bl2'.
          auto.
          specialize (Hlock_mapped _ _ Hres).
          destruct Hlock_mapped as [bl1' Hf'].
          assert (bl1 = bl1')
            by (apply Hincr in Hf'; eapply (injective ((weak_obs_eq (obs_eq_data Htsim)))); eauto).
          subst.
          eapply Hlock_if; eauto.
      }
        { (* Proof that the fine grained invariant is preserved *)
            by eapply suspendF_invariant with (pff := pff); eauto.
        }
        { (* Proof the max_inv is preserved *)
          by auto.
        }
        { by auto. }
        { eapply suspend_tp_wd;
            by eauto.
        }
        { apply ren_incr_domain_incr in Hincr.
          eapply ge_wd_incr;
            by eauto.
        }
        { split; auto.
          eapply ren_incr_trans;
            by eauto.
        }
        { intros k Hin.
          clear - pfc Hxs Hin Hexec HsuspendC.
          assert (List.In k xs).
          { clear - Hin.
            induction xs; first by simpl in *.
            destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq.
            subst. simpl in *.
            rewrite if_false in Hin; auto.
            do 2 apply/eqP.
            rewrite Bool.negb_true_iff;
              by apply/eqP.
            simpl in *.
            rewrite if_true in Hin; auto.
            simpl in *. destruct Hin; auto.
              by apply/eqP.
          }
          specialize (Hxs k H).
          eapply suspendC_containsThread with (tp := tpc'); eauto.
          eapply containsThread_internal_execution;
            by eauto.
        }
    }
  Qed.

  (** ** Proofs about external steps*)
  
  Lemma external_step_inverse :
    forall U U' tp m tp' m' i (cnti: containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (Hexternal: cnti @ E)
      (Hstep: DryConc.MachStep the_ge (i :: U, [::], tp) m (U', [::], tp') m'),
      U = U' /\ exists ev, syncStep the_ge cnti Hcomp tp' m' ev.
  Proof.
    intros.
    inversion Hstep;
      try inversion Htstep; subst; simpl in *;
      try match goal with
          | [H: Some _ = Some _ |- _] => inversion H; subst
          end; pf_cleanup;

      repeat match goal with
             | [H: getThreadC ?Pf = _, Hext: ?Pf @ E |- _] =>
               unfold getStepType in Hext;
                 rewrite H in Hext; simpl in Hext
             | [H1: match ?Expr with _ => _ end = _ |- _] =>
               destruct Expr
             | [H: threadHalted _ |- _] =>
               inversion H; clear H; subst; pf_cleanup
             | [H1: is_true (isSome (halted ?Sem ?C)),
                    H2: match at_external _ _ with _ => _ end = _ |- _] =>
               destruct (at_external_halted_excl Sem C) as [Hext | Hcontra];
                 [rewrite Hext in H2;
                   destruct (halted Sem C); discriminate |
                  rewrite Hcontra in H1; exfalso; by auto]
             end; try discriminate; eexists;
      eauto.
      by exfalso.
  Qed.

  (** Function that projects the angel through a memory injection to
    compute a new angel *)

  Definition projectAngel (f : memren) (deltaMap : delta_map) : delta_map :=
    Maps.PTree.fold (fun acc b bperm =>
                       match f b with
                       | Some b' =>
                         Maps.PTree.set b' bperm acc
                       | None =>
                         acc end)
                    deltaMap (Maps.PTree.empty _).

  
  Definition isProjection (f : memren) (deltaMap deltaMap' : delta_map) : Prop :=
    forall b b',
      f b = Some b' ->
      Maps.PTree.get b deltaMap = Maps.PTree.get b' deltaMap'.

  (** Its proof of correctness under the assumption that f is injective *)
  Lemma projectAngel_correct:
    forall (f:memren) deltaMap
      (Hf_injective: forall b1 b1' b2,
          f b1 = Some b2 ->
          f b1' = Some b2 ->
          b1 = b1'),
      isProjection f deltaMap (projectAngel f deltaMap).
  Proof.
    intros.
    eapply Maps.PTree_Properties.fold_rec with (P := isProjection f).
    { intros dmap dmap' a Heq Hprojection. intros b b' Hf.
      specialize (Heq b). rewrite <- Heq.
      unfold isProjection in Hprojection. eauto.
    }
    { unfold isProjection.
      intros;
        by do 2 rewrite Maps.PTree.gempty.
    }
    { intros dmap a bnew fnew Hget_dmap Hget_delta Hprojection.
      intros b b' Hf.
      destruct (Pos.eq_dec b bnew) as [Heq | Hneq].
      - subst bnew. rewrite Maps.PTree.gss.
        rewrite Hf.
          by rewrite Maps.PTree.gss.
      - rewrite Maps.PTree.gso; auto.
        unfold isProjection in Hprojection.
        destruct (f bnew) as [b'0|] eqn:Hfnew;
          try eauto.
        rewrite Maps.PTree.gso.
        eapply Hprojection; eauto.
        intros Hcontra.
        subst b'0;
          by eauto.
    }
  Qed.

  Lemma projectAngel_correct_2:
    forall (f:memren) deltaMap b'
      (Hf: ~ exists b, f b = Some b'),
      Maps.PTree.get b' (projectAngel f deltaMap) = None.
  Proof.
    intros.
    unfold projectAngel.
    eapply Maps.PTree_Properties.fold_rec. auto.
    rewrite Maps.PTree.gempty. reflexivity.
    intros.
    destruct (f k) as [b'0 |] eqn:Hf'.
    destruct (Pos.eq_dec b' b'0); subst.
    exfalso.
      by eauto.
      rewrite Maps.PTree.gso;
        by auto.
        by assumption.
  Qed.

  Lemma computeMap_projection_1:
    forall (mc mf : mem) f
      pmap pmapF
      (Hlt: permMapLt pmap (getMaxPerm mc))
      (HltF: permMapLt pmapF (getMaxPerm mf))
      (virtue : delta_map)
      (Hobs_eq: mem_obs_eq f (restrPermMap Hlt)
                           (restrPermMap HltF))
      b1 b2
      (Hf: f b1 = Some b2),
      (computeMap pmapF (projectAngel f virtue)) # b2 =
      (computeMap pmap virtue) # b1.
  Proof.
    intros.
    extensionality ofs.
    destruct Hobs_eq as [Hweak_obs Hstrong_obs].
    destruct Hweak_obs.
    assert (Hangel := projectAngel_correct _ virtue injective0).
    specialize (Hangel _ _ Hf).
    symmetry in Hangel.
    destruct (Maps.PTree.get b1 virtue) as [df |] eqn:Hget.
    destruct (df ofs) as [p|] eqn:Hdf.
    erewrite (computeMap_1 _ _ _ _ Hget Hdf).
    erewrite (computeMap_1 _ _ _ _ Hangel Hdf);
      by reflexivity.
    erewrite (computeMap_2 _ _ _ _ Hget Hdf).
    erewrite (computeMap_2 _ _ _ _ Hangel Hdf).
    destruct Hstrong_obs.
    specialize (perm_obs_strong0 b1 b2 ofs Hf);
      by do 2 rewrite restrPermMap_Cur in perm_obs_strong0.
    erewrite (computeMap_3 _ _ _ _ Hget).
    erewrite (computeMap_3 _ _ _ _ Hangel).
    destruct Hstrong_obs.
    specialize (perm_obs_strong0 b1 b2 ofs Hf);
      by do 2 rewrite restrPermMap_Cur in perm_obs_strong0.
  Qed.

  Lemma computeMap_projection_2:
    forall f pmap
      (virtue : delta_map) b2
      (Hb1: ~ (exists b1 : block, f b1 = Some b2)),
      (computeMap pmap (projectAngel f virtue)) # b2 =
      pmap # b2.
  Proof.
    intros.
    assert (H := projectAngel_correct_2 _ virtue Hb1).
    extensionality ofs';
      by erewrite computeMap_3.
  Qed.

  Lemma computeMap_projection_3 :
    forall  (f : memren) (virtue : delta_map) b1 b2 
       (Hf: f b1 = Some b2)
       (Hinjective : forall b1 b1' b2 : block,
           f b1 = Some b2 -> f b1' = Some b2 -> b1 = b1'),
      (computeMap empty_map (projectAngel f virtue)) # b2 =
      (computeMap empty_map virtue) # b1.
  Proof.
    intros.
    extensionality ofs.
    assert (Hangel := projectAngel_correct _ virtue Hinjective).
    specialize (Hangel _ _ Hf).
    symmetry in Hangel.
    destruct (Maps.PTree.get b1 virtue) as [df |] eqn:Hget.
    destruct (df ofs) as [p|] eqn:Hdf.
    erewrite (computeMap_1 _ _ _ _ Hget Hdf).
    erewrite (computeMap_1 _ _ _ _ Hangel Hdf);
      by reflexivity.
    erewrite (computeMap_2 _ _ _ _ Hget Hdf).
    erewrite (computeMap_2 _ _ _ _ Hangel Hdf);
      by do 2 rewrite empty_map_spec.
    erewrite (computeMap_3 _ _ _ _ Hget).
    erewrite (computeMap_3 _ _ _ _ Hangel);
      by do 2 rewrite empty_map_spec.
  Qed.

  
  (* Blocks that are not mapped by f are set to empty permission. This
  makes the invariant preservation easier. *)
  Definition projectMap (f : memren) (pmap : access_map) : access_map :=
    (pmap#1, Maps.PTree.fold (fun acc b bperm =>
                                      match f b with
                                      | Some b' =>
                                        Maps.PTree.set b' bperm acc
                                      | None =>
                                        acc end)
                                   pmap.2 (Maps.PTree.empty _)).


  (** Its proof of correctness under the assumption that f is injective *)
  Lemma projectMap_tree:
    forall (f:memren) pmap
      (Hf_injective: forall b1 b1' b2,
          f b1 = Some b2 ->
          f b1' = Some b2 ->
          b1 = b1') b b'
      (Hf: f b = Some b'),
      Maps.PTree.get b pmap.2 = Maps.PTree.get b' (projectMap f pmap).2.
  Proof.
    intros.
    unfold projectMap.
    eapply Maps.PTree_Properties.fold_rec; eauto.
    { intros dmap dmap' a Heq Hprojection. simpl in *. 
      specialize (Heq b). rewrite <- Heq. auto.
    }
    { by do 2 rewrite Maps.PTree.gempty.
    }
    { intros dmap a bnew fnew Hget_dmap Hget_delta Hprojection.
      destruct (Pos.eq_dec b bnew) as [Heq | Hneq].
      - subst bnew. rewrite Maps.PTree.gss.
        rewrite Hf.
          by rewrite Maps.PTree.gss.
      - rewrite Maps.PTree.gso; auto.
        unfold isProjection in Hprojection.
        destruct (f bnew) as [b'0|] eqn:Hfnew;
          try eauto.
        rewrite Maps.PTree.gso.
        eapply Hprojection; eauto.
        intros Hcontra.
        subst b'0;
          by eauto.
    }
  Qed.

  Lemma projectMap_correct:
    forall (f:memren) pmap
      (Hf_injective: forall b1 b1' b2,
          f b1 = Some b2 ->
          f b1' = Some b2 ->
          b1 = b1') b b'
      (Hf: f b = Some b'),
      Maps.PMap.get b pmap = Maps.PMap.get b' (projectMap f pmap).
  Proof.
    intros.
    unfold Maps.PMap.get.
    erewrite projectMap_tree;
      by eauto.
  Qed.

  Lemma projectMap_tree_2:
    forall (f:memren) pmap b'
      (Hf: ~ exists b, f b = Some b'),
      Maps.PTree.get b' (projectMap f pmap).2 = None.
  Proof.
    intros.
    unfold projectMap.
    eapply Maps.PTree_Properties.fold_rec. auto.
    rewrite Maps.PTree.gempty. reflexivity.
    intros.
    destruct (f k) as [b'0 |] eqn:Hf'.
    destruct (Pos.eq_dec b' b'0); subst.
    exfalso.
      by eauto.
      rewrite Maps.PTree.gso;
        by auto.
        by assumption.
  Qed.


  Lemma projectMap_tree_unchanged :
    forall f (pmap : access_map) (b2 : positive)
      (Hb1: ~ (exists b1 : block, f b1 = Some b2)),
      Maps.PTree.get b2 (projectMap f pmap).2 = None.
  Proof.
    intros.
    unfold projectMap.
    eapply Maps.PTree_Properties.fold_rec; auto.
    rewrite Maps.PTree.gempty. reflexivity.
    intros.
    destruct (f k) as [b'0 |] eqn:Hf'.
    destruct (Pos.eq_dec b2 b'0); subst.
    exfalso;
      by eauto.
    rewrite Maps.PTree.gso;
        by auto.
      by assumption.
  Qed.
    
  Lemma projectMap_correct_2:
    forall f pmap b2
      (Hb1: ~ (exists b1 : block, f b1 = Some b2)),
      (projectMap f pmap) # b2 = pmap.1.
  Proof.
    intros.
    assert (H := projectMap_tree_2 _ pmap Hb1).
    extensionality ofs'.
    unfold Maps.PMap.get. rewrite H.
      by reflexivity.
  Qed.
  
  Lemma sync_locks_mem_obs_eq:
    forall (tpc tpc' tpf tpf' : thread_pool) (mc mc' mf mf' : mem) f
      pmap pmapF
      (Hlt: permMapLt pmap (getMaxPerm mc))
      (HltF: permMapLt pmapF (getMaxPerm mf))
      (HmemCompC : mem_compatible tpc mc)
      (HmemCompF : mem_compatible tpf mf)
      (b b2 : block) ofs v rmap rmap'
      (HmemCompC' : mem_compatible tpc' mc')
      (HmemCompF': mem_compatible tpf' mf')
      (Htpc': lockSet (updLockSet tpc (b, Int.intval ofs) rmap) = lockSet tpc')
      (Htpf': lockSet (updLockSet tpf (b2, Int.intval ofs) rmap') = lockSet tpf')
      (Hinj: forall b1 b1' b2 : block,
          f b1 = Some b2 ->
          f b1' = Some b2 -> b1 = b1')
      (Hf: f b = Some b2)
      (Hmem_obs: strong_mem_obs_eq f
                                   (restrPermMap (compat_ls HmemCompC))
                                   (restrPermMap (compat_ls HmemCompF)))
      (Hstore: Mem.store Mint32 (restrPermMap Hlt) b
                         (Int.intval ofs) (Vint v) = Some mc')
      (HstoreF: Mem.store Mint32 (restrPermMap HltF) b2
                          (Int.intval ofs) (Vint v) = Some mf'),
      strong_mem_obs_eq f (restrPermMap (compat_ls HmemCompC'))
                        (restrPermMap (compat_ls HmemCompF')).
  Proof.
    intros.
    destruct Hmem_obs as [Hperm_obs Hval_obs].
    constructor.
    { intros b0 b3 ofs0 Hf0.
      specialize (Hperm_obs _ _ ofs0 Hf0).
      do 2 rewrite restrPermMap_Cur.
      do 2 rewrite restrPermMap_Cur in Hperm_obs.
      rewrite <- Htpc'.
      rewrite <- Htpf'.
      destruct (Pos.eq_dec b b0) as [Heq | Hneq].
      - subst.
        assert (b2 = b3)
          by (rewrite Hf0 in Hf; inversion Hf; by subst);
          subst b3.
        destruct (Z_le_dec (Int.intval ofs) ofs0);
          destruct (Z_lt_dec ofs0 ((Int.intval ofs) + Z.of_nat (lksize.LKSIZE_nat))).
        + erewrite gssLockSet; eauto.
          erewrite gssLockSet; eauto.
        + rewrite gsoLockSet_1; auto.
          rewrite gsoLockSet_1; auto.
        + erewrite gsoLockSet_1 by omega.
          erewrite gsoLockSet_1 by omega; auto.
        + erewrite gsoLockSet_1 by omega.
          erewrite gsoLockSet_1 by omega;
            auto.
      - assert (Hneq': b2 <> b3).
        { intros Hcontra.
          inversion Hcontra; subst.
          assert (b0 = b)
            by (eapply Hinj; eauto).
          subst b0;
            by auto.
        }
        erewrite gsoLockSet_2; auto.
        erewrite gsoLockSet_2; auto.
    }
    { intros b0 b3 ofs0 Hf0 Hperm.
      simpl in *.
      erewrite Mem.store_mem_contents; eauto. simpl.
      erewrite Mem.store_mem_contents with (m2 := mf'); eauto. simpl.
      destruct (Pos.eq_dec b b0) as [? | Hneq].
      subst b0.
      assert (b2 = b3)
        by (rewrite Hf in Hf0; by inversion Hf0); subst b3.
      do 2 rewrite Maps.PMap.gss.
      destruct (Z_lt_le_dec ofs0 (Int.intval ofs)) as [Hltofs | Hge].
      assert (Hperm0: Mem.perm (restrPermMap (compat_ls HmemCompC)) b ofs0 Cur Readable).
      { unfold Mem.perm in *.
        assert (H1 := restrPermMap_Cur (compat_ls HmemCompC') b ofs0).
        assert (H2 := restrPermMap_Cur (compat_ls HmemCompC) b ofs0).
        unfold permission_at in *.
        rewrite H1 in Hperm.
        rewrite H2.
        rewrite <- Htpc' in Hperm.
        erewrite gsoLockSet_1 in Hperm;
          eauto.
      }
      do 2 erewrite Mem.setN_outside
        by (left; auto);
        by eauto.
      destruct (Z_lt_ge_dec
                  ofs0
                  ((Int.intval ofs) +
                   Z.of_nat (length (inj_bytes (encode_int 4 (Int.unsigned v))))))
        as [Hltofs | Hge'].
      (*case it's the lock address*)
      unfold inj_bytes in *.
      rewrite Coqlib.list_length_map in Hltofs.
      rewrite encode_int_length in Hltofs.
      assert (H1 := Mem.getN_setN_same (inj_bytes (encode_int 4 (Int.unsigned v)))
                                       (Int.intval ofs) (Mem.mem_contents mc) # b).
      assert (H2 := Mem.getN_setN_same (inj_bytes (encode_int 4 (Int.unsigned v)))
                                       (Int.intval ofs) (Mem.mem_contents mf) # b2).
      unfold inj_bytes in H1, H2.
      rewrite Coqlib.list_length_map in H1, H2.
      rewrite encode_int_length in H1, H2. simpl in H1, H2.
      assert (Hofs: (ofs0 = Int.intval ofs \/ ofs0 = (Int.intval ofs) + 1
                     \/ ofs0 = (Int.intval ofs) + 1 + 1 \/
                     ofs0 = (Int.intval ofs) + 1 + 1 + 1)%Z)
        by (clear - Hltofs Hge; simpl in Hltofs; omega).
      destruct (encode_int 4 (Int.unsigned v)); first by discriminate.
      destruct l; first by discriminate.
      destruct l; first by discriminate. destruct l; first by discriminate.
      destruct l. 2: by discriminate.
      simpl in H1, H2.
      inversion H1; inversion H2. simpl in *.
      destruct Hofs as [? | [? | [? | ?]]]; subst;
      repeat (try rewrite Maps.ZMap.gss;
               try erewrite Maps.ZMap.gso
                by (intros Hcontra; clear - Hcontra;
                    destruct ofs; simpl in Hcontra;  clear intrange;
                    symmetry in Hcontra;
                    rewrite <- Z.add_0_r in Hcontra;
                    repeat rewrite <- Z.add_assoc in Hcontra;
                    simpl in Hcontra;
                    apply Z.add_reg_l in Hcontra; by omega));
        by constructor.
      erewrite Mem.setN_outside
        by (right; auto).
      assert (Hperm0: Mem.perm (restrPermMap (compat_ls HmemCompC)) b ofs0 Cur Readable).
      { unfold Mem.perm in *.
        assert (H1 := restrPermMap_Cur (compat_ls HmemCompC') b ofs0).
        assert (H2 := restrPermMap_Cur (compat_ls HmemCompC) b ofs0).
        unfold permission_at in *.
        rewrite H1 in Hperm.
        rewrite H2.
        rewrite <- Htpc' in Hperm.
        erewrite gsoLockSet_1 in Hperm; eauto.
      }
      erewrite Mem.setN_outside
        by (right; auto);
        by eauto.
      assert (b2 <> b3) (*by injectivity*)
        by (intros Hcontra; subst; eauto).
      erewrite Maps.PMap.gso by auto.
      erewrite Maps.PMap.gso by auto.
      assert (Hperm0: Mem.perm (restrPermMap (compat_ls HmemCompC)) b0 ofs0 Cur Readable).
      { unfold Mem.perm in *.
        assert (H1 := restrPermMap_Cur (compat_ls HmemCompC') b0 ofs0).
        assert (H2 := restrPermMap_Cur (compat_ls HmemCompC) b0 ofs0).
        unfold permission_at in *.
        rewrite H1 in Hperm.
        rewrite H2.
        rewrite <- Htpc' in Hperm.
        erewrite gsoLockSet_2 in Hperm; eauto.
      }
        by eauto.
    }
  Qed.
  
  (* NOTE: this is only needed to find out if a block is in the
    codomain of f, which is decidable *)
  Require Import Coq.Logic.ClassicalFacts.
  Hypothesis em : excluded_middle.

  (** Maintaing the invariant through projection of the angel*)

  (** This lemma is for the case we are trying to establish
    disjointness between some thread's resource map and the newly
    installed map from the angel*)
  Lemma disjoint_angel_project:
    forall (tpc tpf : thread_pool) (mc mf : mem) f
      (i j: tid) (pff : containsThread tpf i) (pfc : containsThread tpc i)
      (HmemCompC : mem_compatible tpc mc)
      (HmemCompF : mem_compatible tpf mf) (virtue : delta_map) 
      (c cf : ctl)
      (pffj' : containsThread
                 (updThread pff cf
                            (computeMap (getThreadR pff)
                                        (projectAngel f virtue))) j)
      (pffi' : containsThread
                 (updThread pff cf
                            (computeMap (getThreadR pff)
                                        (projectAngel f virtue))) i)
      (HnumThreads: forall k, containsThread tpc k <-> containsThread tpf k)
      (Hij: i <> j)
      (Hno_raceC: race_free (updThread pfc c (computeMap (getThreadR pfc) virtue)))
      (HsimWeak: forall (tid : tid) (pfc0 : containsThread tpc tid)
                   (pff0 : containsThread tpf tid),
          weak_tsim f pfc0 pff0 HmemCompC HmemCompF)
      (HinvF: invariant tpf)
      (Hobs_eq: mem_obs_eq f (restrPermMap (HmemCompC i pfc))
                           (restrPermMap (HmemCompF i pff))),
      permMapsDisjoint (getThreadR pffi') (getThreadR pffj').
  Proof.
    intros.
    rewrite gssThreadRes.
    assert (pffj:= cntUpdate' _ _ pff pffj').
    erewrite gsoThreadRes with (cntj := pffj) by eauto.
    assert (pfcj := (snd (HnumThreads _)) pffj).
    assert (pfcj' := cntUpdate c (computeMap (getThreadR pfc) virtue)
                               pfc pfcj).
    assert (pfc' := cntUpdate c (computeMap (getThreadR pfc) virtue) pfc pfc).
    specialize (Hno_raceC _ _ pfc' pfcj' Hij).
    erewrite gssThreadRes in Hno_raceC.
    unfold permMapsDisjoint.
    intros b2 ofs.
    specialize (HsimWeak _ pfcj pffj).
    destruct HsimWeak.
    assert (Hmapped: forall b1 b2,
               f b1 = Some b2 ->
               (computeMap (getThreadR pff)
                           (projectAngel f virtue)) # b2 =
               (computeMap (getThreadR pfc) virtue) # b1)
      by (eapply computeMap_projection_1; eauto).
    assert (Hunmapped: forall b2,
               (~ exists b1, f b1 = Some b2) ->
               (computeMap (getThreadR pff) (projectAngel f virtue)) # b2 =
               (getThreadR pff) # b2)
      by (eapply computeMap_projection_2; eauto).
    (*NOTE: this is actually decidable*)
    assert (Hb2: (exists b1, f b1 = Some b2) \/
                 ~ (exists b1, f b1 = Some b2))
      by eapply em.
    destruct Hb2 as [Hb2m | Hb2u].
    (*case b2 is mapped by f*)
    destruct Hb2m as [b1 Hf].
    specialize (Hmapped _ _ Hf).
    rewrite Hmapped.
    specialize (Hno_raceC b1 ofs).
    erewrite gsoThreadRes with (cntj := pfcj) in Hno_raceC by eauto.
    specialize (perm_obs_weak0 _ _ ofs Hf).
    do 2 rewrite restrPermMap_Cur in perm_obs_weak0.
    eapply perm_union_lower;
      by eauto.
    (* case b2 is not mapped by f*)
    specialize (Hunmapped _ Hb2u).
    rewrite Hunmapped.
      by apply ((no_race HinvF) _ _ pff pffj Hij b2 ofs).
  Qed.

  (** Storing on disjoint permisison maps should not affect the result*)
  Lemma gsoMem_obs_eq:
    forall (tpc tpf : thread_pool) (mc mf mc' mf' : mem) 
      (f : memren) (bl1 bl2 : block) (ofs : Z) (v : int) pmapC pmapC' pmapF
      i (pfc: containsThread tpc i) (pff: containsThread tpf i)
      (HltC: permMapLt pmapC (getMaxPerm mc))
      (HltF: permMapLt pmapF (getMaxPerm mf))
      (b1 : block) (ofs0 : Z) (b2 : block)
      (Hinj: forall b1 b1' b2 : block,
          f b1 = Some b2 ->
          f b1' = Some b2 -> b1 = b1')
      (Hval_obs_eq: memval_obs_eq f (Maps.ZMap.get ofs0 (Mem.mem_contents mc) # b1)
                                  (Maps.ZMap.get ofs0 (Mem.mem_contents mf) # b2))
      (Hf: f b1 = Some b2)
      (Hfl: f bl1 = Some bl2)
      (Hstore: Mem.store Mint32 (restrPermMap HltC)
                         bl1 ofs (Vint v) = Some mc')
      (HstoreF: Mem.store Mint32 (restrPermMap HltF)
                          bl2 ofs (Vint v) = Some mf')
      (Hreadable : Mem.perm_order' (pmapC' # b1 ofs0) Readable)
      (Hdisjoint: permMapsDisjoint pmapC pmapC'),
      memval_obs_eq f (Maps.ZMap.get ofs0 (Mem.mem_contents mc') # b1)
                    (Maps.ZMap.get ofs0 (Mem.mem_contents mf') # b2).
  Proof.
    intros.
    erewrite Mem.store_mem_contents; eauto.
    erewrite Mem.store_mem_contents with (m2 := mf'); eauto.
    simpl.
    destruct (Pos.eq_dec b1 bl1) as [? | Hneq_b1].
    - subst bl1.
      assert (b2 = bl2)
        by (rewrite Hf in Hfl; inversion Hfl; by subst).
      subst bl2.
      do 2 rewrite Maps.PMap.gss.
      destruct (Z_lt_le_dec ofs0 ofs) as [Hlt | Hge].
      do 2 erewrite Mem.setN_outside
        by (left; auto);
        by eauto.
      destruct (Z_lt_ge_dec
                  ofs0 (ofs + Z.of_nat
                                (length (inj_bytes (encode_int 4 (Int.unsigned v))))))
        as [Hlt | Hge'].
      (* case the two addresses coincide - contradiction by invariant*)
      + unfold inj_bytes in *.
        rewrite Coqlib.list_length_map in Hlt.
        rewrite encode_int_length in Hlt. simpl in Hlt.
        clear - Hreadable Hstore Hge Hlt Hdisjoint.
        apply Mem.store_valid_access_3 in Hstore.
        unfold Mem.valid_access in Hstore. simpl in Hstore.
        destruct Hstore as [Hcontra _].
        simpl in *.
        unfold Mem.range_perm in Hcontra.
        specialize (Hcontra ofs0 (conj Hge Hlt)).
        unfold Mem.perm in Hcontra.
        assert (H := restrPermMap_Cur HltC b1 ofs0).
        unfold permission_at in H.
        rewrite H in Hcontra; clear H.
        specialize (Hdisjoint b1 ofs0).
        destruct (pmapC # b1 ofs0) as [pl|],
                                              (pmapC' # b1 ofs0) as [pi|];
          try (destruct pl); try (destruct pi); simpl in *;
          destruct Hdisjoint as [? Hdisjoint]; inversion Hdisjoint; subst;
          try (by inversion Hreadable); try (by inversion Hcontra).
      + erewrite Mem.setN_outside
          by (right; auto).
        erewrite Mem.setN_outside
          by (right; auto);
          by eauto.
    - assert (b2 <> bl2) (*by injectivity*)
        by (intros Hcontra; subst; eauto).
      erewrite Maps.PMap.gso by auto.
      erewrite Maps.PMap.gso by auto.
        by eauto.
  Qed.
  
  Lemma invariant_project:
    forall (tpc tpf : thread_pool) (mc mf : mem) f rmap1 b1 b2 ofs
      (i : tid) (pff : containsThread tpf i) (pfc : containsThread tpc i)
      (HmemCompC : mem_compatible tpc mc)
      (HmemCompF : mem_compatible tpf mf)
      (Hcanonical: isCanonical rmap1)
      (virtue : delta_map) c cf
      (HinvF: invariant tpf)
      (Hf: f b1 = Some b2)
      (HinvC': invariant (updLockSet
                            (updThread pfc c (computeMap (getThreadR pfc) virtue))
                            (b1, ofs) rmap1))
      (HsimWeak: forall (tid : tid) (pfc0 : containsThread tpc tid)
                   (pff0 : containsThread tpf tid),
          weak_tsim f pfc0 pff0 HmemCompC HmemCompF)
      (Htsim: mem_obs_eq f (restrPermMap (HmemCompC i pfc))
                         (restrPermMap (HmemCompF i pff)))
      (HsimLP: strong_mem_obs_eq f
                                 (restrPermMap (compat_ls HmemCompC))
                                 (restrPermMap (compat_ls HmemCompF)))
      (Hlocks: forall (bl2 : block) (ofs : Z),
          lockRes tpf (bl2, ofs) ->
          exists bl1 : block, f bl1 = Some bl2)
      (HsimRes:
         forall (bl1 bl2 : block) (ofs : Z)
           (rmap1 rmap2 : dry_machine.LocksAndResources.lock_info),
           f bl1 = Some bl2 ->
           forall (Hl1 : lockRes tpc (bl1, ofs) = Some rmap1)
             (Hl2 : lockRes tpf (bl2, ofs) = Some rmap2),
             strong_mem_obs_eq f
                               (restrPermMap (compat_lp HmemCompC (bl1, ofs) Hl1))
                               (restrPermMap (compat_lp HmemCompF (bl2, ofs) Hl2)))
       (Hlock_if: forall (bl1 bl2 : block) (ofs : Z),
           f bl1 = Some bl2 ->
           lockRes tpc (bl1, ofs) <-> lockRes tpf (bl2, ofs))
      (HnumThreads: forall i, containsThread tpc i <-> containsThread tpf i),
      invariant
        (updLockSet (updThread pff cf
                               (computeMap (getThreadR pff)
                                           (projectAngel f virtue))) (b2, ofs)
                    (projectMap f rmap1)).
  Proof.
    intros.
    constructor.
    { (* no race for coarse-grained state*)
      assert (Hno_raceC:= no_race HinvC').
      intros k j pffk' pffj' Hkj.
      destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik;
        first by (subst k; eapply disjoint_angel_project;
                  eauto).
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij;
        first by (apply permMapsDisjoint_comm; subst;
                  eapply disjoint_angel_project; eauto).
      assert (pffj0:= cntUpdateL' _ _ pffj').
      assert (pffj:= cntUpdate' _ _ pff pffj0).
      erewrite gLockSetRes with (cnti := pffj0) by eauto.
      erewrite gsoThreadRes with (cntj := pffj) by eauto.
      assert (pffk0:= cntUpdateL' _ _ pffk').
      assert (pffk:= cntUpdate' _ _ pff pffk0).
      erewrite gLockSetRes with (cnti := pffk0) by eauto.
      erewrite gsoThreadRes with (cntj := pffk) by eauto;
        by apply ((no_race HinvF) _ _ pffk pffj Hkj).
    }
    { (* no race between lockset and threads*)
      intros j pffj'.
      destruct HinvC' as [_ HinvC' _ _].
      assert (pfcj': containsThread
                       (updLockSet
                          (updThread pfc c
                                     (computeMap (getThreadR pfc) virtue)) 
                          (b1, ofs) rmap1) j).
      { assert (pffj0:= cntUpdateL' _ _ pffj').
        assert (pffj:= cntUpdate' _ _ pff pffj0).
        apply HnumThreads in pffj.
        apply cntUpdateL.
          by apply cntUpdate.
      }
      specialize (HinvC' _ pfcj').
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
      { subst j.
        rewrite gLockSetRes.
        rewrite gssThreadRes.
        rewrite gLockSetRes in HinvC'.
        rewrite gssThreadRes in HinvC'.
        intros b0 ofs0.
        assert (Hmapped: forall b1 b2,
                   f b1 = Some b2 ->
                   (computeMap (getThreadR pff)
                               (projectAngel f virtue)) # b2 =
                   (computeMap (getThreadR pfc) virtue) # b1)
          by (eapply computeMap_projection_1; eauto).
        assert (Hunmapped: forall b2,
                   (~ exists b1, f b1 = Some b2) ->
                   (computeMap (getThreadR pff) (projectAngel f virtue)) # b2 =
                   (getThreadR pff) # b2)
          by (eapply computeMap_projection_2; eauto).
        (*NOTE: this is actually decidable*)
        assert (Hb0: (exists b1, f b1 = Some b0) \/
                     ~ (exists b1, f b1 = Some b0))
          by eapply em.
        destruct Hb0 as [Hb0m | Hb0u].
        { (*case b0 is mapped by f*)
          destruct Hb0m as [b Hfb].
          specialize (Hmapped _ _ Hfb).
          rewrite Hmapped.
          specialize (HinvC' b ofs0).
          destruct (Pos.eq_dec b b1) as [Heq | Hneq].
          - subst.
            assert (b2 = b0)
              by (rewrite Hf in Hfb; by inversion Hfb).
            subst b0.
            destruct (Z_le_dec ofs ofs0).
            destruct (Z_lt_dec ofs0 (ofs +
                                       Z.of_nat (lksize.LKSIZE_nat))).
            rewrite gssLockSet; auto.
            rewrite gssLockSet in HinvC';
              by auto.
            rewrite gsoLockSet_1; auto.
            rewrite gsoLockSet_1 in HinvC'; auto.
            rewrite gsoThreadLock.
            rewrite gsoThreadLock in HinvC'.
            destruct HsimLP as [HpermLP _].
            specialize (HpermLP _ _ ofs0 Hfb).
            do 2 rewrite restrPermMap_Cur in HpermLP.
            rewrite HpermLP; auto.
            erewrite gsoLockSet_1 by omega; auto.
            erewrite gsoLockSet_1 in HinvC' by omega; auto.
            rewrite gsoThreadLock.
            rewrite gsoThreadLock in HinvC'.
            destruct HsimLP as [HpermLP _].
            specialize (HpermLP _ _ ofs0 Hfb).
            do 2 rewrite restrPermMap_Cur in HpermLP.
            rewrite HpermLP; auto.
          - assert (b2 <> b0)
              by (intros Hcontra; subst;
                  pose proof ((injective (weak_obs_eq Htsim)) _ _ _ Hfb Hf);
                  auto).
            erewrite gsoLockSet_2 by eauto.
            erewrite gsoLockSet_2 in HinvC' by eauto.
            rewrite gsoThreadLock in HinvC'.
            rewrite gsoThreadLock.
            destruct HsimLP as [HpermLP _].
            specialize (HpermLP _ _ ofs0 Hfb).
            do 2 rewrite restrPermMap_Cur in HpermLP.
            rewrite HpermLP; auto.
        }
        { (* case b0 is not mapped by f*)
          specialize (Hunmapped _ Hb0u).
          rewrite Hunmapped.
          assert (Hneq: b2 <> b0)
            by (intros Hcontra; inversion Hcontra; subst; eauto).
          erewrite gsoLockSet_2 by auto.
          rewrite gsoThreadLock.
            by apply ((lock_set_threads HinvF) _ pff b0 ofs0).
        }
      }
      { (*case i <> j *)
        assert (pffj0:= cntUpdateL' _ _ pffj').
        assert (pffj:= cntUpdate' _ _ pff pffj0).
          erewrite gLockSetRes with (cnti := pffj0) by eauto.
          erewrite gsoThreadRes with (cntj := pffj) by eauto.
        assert (pfcj0:= cntUpdateL' _ _ pfcj').
        assert (pfcj:= cntUpdate' _ _ pfc pfcj0).
        erewrite gLockSetRes with (cnti := pfcj0) in HinvC' by eauto.
        erewrite gsoThreadRes with (cntj := pfcj) in HinvC' by eauto.
        intros b2' ofs'.
        (*NOTE: this is actually decidable*)
        assert (Hb2: (exists b1, f b1 = Some b2') \/
                     ~ (exists b1, f b1 = Some b2'))
          by eapply em.
        destruct Hb2 as [Hb2m | Hb2u].
        (*case b2' is mapped by f*)
        destruct Hb2m as [b Hfb].
        specialize (HinvC' b ofs').
        specialize (HsimWeak _ pfcj pffj).
        assert (H:= perm_obs_weak HsimWeak).
        specialize (H b b2' ofs' Hfb).
        do 2 rewrite restrPermMap_Cur in H.
        destruct (Pos.eq_dec b b1).
        - subst.
          assert (b2 = b2')
            by (rewrite Hf in Hfb; by inversion Hfb).
          subst b2'.
          destruct (Z_le_dec ofs ofs').
          destruct (Z_lt_dec ofs' (ofs +
                                   Z.of_nat (lksize.LKSIZE_nat))).
          rewrite gssLockSet; auto.
          rewrite gssLockSet in HinvC'; auto.
          eapply perm_union_lower;
            by eauto.
          rewrite gsoLockSet_1; auto.
          rewrite gsoLockSet_1 in HinvC'; auto.
          rewrite gsoThreadLock.
          rewrite gsoThreadLock in HinvC'.
          destruct HsimLP as [HpermLP _].
          specialize (HpermLP _ _ ofs' Hfb).
          do 2 rewrite restrPermMap_Cur in HpermLP.
          rewrite HpermLP; auto.
          eapply perm_union_lower;
            by eauto.
          erewrite gsoLockSet_1 by omega; auto.
          erewrite gsoLockSet_1 in HinvC' by omega; auto.
          rewrite gsoThreadLock.
          rewrite gsoThreadLock in HinvC'.
          destruct HsimLP as [HpermLP _].
          specialize (HpermLP _ _ ofs' Hfb).
          do 2 rewrite restrPermMap_Cur in HpermLP.
          rewrite HpermLP.
          eapply perm_union_lower;
            by eauto.
        - assert (b2 <> b2')
            by (intros Hcontra; subst;
                pose proof ((injective (weak_obs_eq Htsim)) _ _ _ Hfb Hf);
                auto).
          erewrite gsoLockSet_2 by eauto.
          erewrite gsoLockSet_2 in HinvC' by eauto.
          rewrite gsoThreadLock in HinvC'.
          rewrite gsoThreadLock.
          destruct HsimLP as [HpermLP _].
          specialize (HpermLP _ _ ofs' Hfb).
          do 2 rewrite restrPermMap_Cur in HpermLP.
          rewrite HpermLP; auto.
          eapply perm_union_lower;
            by eauto.
          (*case b2 is not mapped *)
          assert (Hneq: b2 <> b2')
            by (intros Hcontra; inversion Hcontra; subst; eauto).
          rewrite gsoLockSet_2; auto.
          rewrite  gsoThreadLock.
            by apply ((lock_set_threads HinvF) _ pffj b2' ofs').
      }
      }
    { (* no race between lock resources and threads *)
      intros (bl & ofsl) rmap j pffj' Hres.
      destruct HinvC' as [_ _ HinvC' _].
      assert (pfcj': containsThread
                       (updLockSet
                          (updThread pfc c
                                     (computeMap (getThreadR pfc) virtue)) 
                          (b1, ofs) rmap1) j).
      { assert (pffj0:= cntUpdateL' _ _ pffj').
        assert (pffj:= cntUpdate' _ _ pff pffj0).
        apply HnumThreads in pffj.
        apply cntUpdateL.
          by apply cntUpdate.
      }
      assert (pfcj0:= cntUpdateL' _ _ pfcj').
      assert (pffj0:= cntUpdateL' _ _ pffj').
      assert (pfcj:= cntUpdate' _ _ pfc pfcj0).
      assert (pffj:= cntUpdate' _ _ pff pffj0).
      (* Two cases, either l is the updated lock or not*)
      destruct (EqDec_address (bl, ofsl) (b2, ofs)) as [Heq | Hneq].
      { (* case l is the updated lock*)
        inversion Heq; subst.
        assert (H: projectMap f rmap1 = rmap)
          by (erewrite gssLockRes in Hres; by inversion Hres).
        subst rmap.
        specialize (HinvC' (b1, ofs) rmap1 _ pfcj' ltac:(eapply gssLockRes; eauto)).
        inversion Hres; subst.
        intros b2' ofs2'.
        assert (Hb2': (exists b1, f b1 = Some b2') \/
                      ~ (exists b1, f b1 = Some b2'))
          by eapply em.
        destruct Hb2' as [Hb2m' | Hb2u'].
        (*case b2' is mapped by f*)
        destruct Hb2m' as [b1' Hf'].
        specialize (HsimWeak _ pfcj pffj).
        erewrite <- projectMap_correct; eauto.
        specialize (HinvC' b1' ofs2').
        eapply perm_union_lower; eauto.
        assert (H := (perm_obs_weak HsimWeak) _ _ ofs2' Hf').
        do 2 rewrite restrPermMap_Cur in H.
        do 2 rewrite gLockSetRes.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        { (*case i = j*)
          subst j.
          do 2 rewrite gssThreadRes.
          erewrite computeMap_projection_1; eauto.
            by eapply po_refl.
        }
        { erewrite gsoThreadRes with (cntj := pfcj); eauto.
          erewrite gsoThreadRes with (cntj := pffj); eauto.
        }
          by eapply (injective HsimWeak).
        (* case b2' is not mapped by f*)
        rewrite gLockSetRes.
        rewrite projectMap_correct_2; auto.
        rewrite Hcanonical.
        simpl;
          by eauto.
      }
      { (*case l is another lock*)
        rewrite gsoLockRes in Hres; auto.
        rewrite gsoThreadLPool in Hres.
        specialize (Hlocks bl ofsl ltac:(rewrite Hres; auto)).
        destruct Hlocks as [bl1 Hfbl].
        destruct HsimLP as [HpermLP _].
        specialize (HpermLP _ _ ofsl Hfbl).
        do 2 rewrite restrPermMap_Cur in HpermLP.
        assert (Hperm_bl := lockSet_spec_1 tpf bl ofsl ltac:(rewrite Hres; auto)).
        rewrite Hperm_bl in HpermLP.
        symmetry in HpermLP.
        destruct (Hlock_if _ _ ofsl Hfbl) as [_ Hlock_if2].
        unfold isSome in Hlock_if2. 
        rewrite Hres in Hlock_if2.
        specialize (Hlock_if2 ltac:(auto)).
        destruct (lockRes tpc (bl1, ofsl)) as [rmap'|] eqn:Hres1; try by exfalso.
        assert ((b1, ofs) <> (bl1, ofsl))
          by (intros Hcontra; inversion Hcontra; subst;
              rewrite Hfbl in Hf; inversion Hf; subst; auto).
        specialize (HinvC' (bl1, ofsl) rmap' j pfcj').
        rewrite gsoLockRes in HinvC'; auto.
        rewrite gsoThreadLPool in HinvC'.
        specialize (HinvC' Hres1).
        specialize (HsimRes _ _ _ _ _ Hfbl Hres1 Hres).
        destruct HsimRes as [HPermRes _].
        intros b2' ofs2'.
        assert (Hb2: (exists b1, f b1 = Some b2') \/
                     ~ (exists b1, f b1 = Some b2'))
          by eapply em.
        destruct Hb2 as [Hb2m | Hb2u].
        (*case it is mapped by f*)
        destruct Hb2m as [b1' Hfb1'].
        specialize (HPermRes _ _ ofs2' Hfb1').
        do 2 rewrite restrPermMap_Cur in HPermRes.
        rewrite HPermRes.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        { (* case i = j*)
          subst j.
          rewrite gLockSetRes.
          rewrite gssThreadRes.
          erewrite computeMap_projection_1; eauto.
          rewrite gLockSetRes in HinvC'.
          rewrite gssThreadRes in HinvC'.
            by eauto.
        }
        { (* case i <> j *)
          rewrite gLockSetRes.
          rewrite gsoThreadRes; eauto.
          rewrite gLockSetRes in HinvC'.
          rewrite gsoThreadRes in HinvC'; eauto.
          eapply perm_union_lower; eauto.
          specialize (HsimWeak _ pfcj pffj).
          assert (Hperm_eq := (perm_obs_weak HsimWeak) b1' b2' ofs2' Hfb1').
          do 2 rewrite restrPermMap_Cur in Hperm_eq.
          auto.
        }
        (* case it is not mapped by f*) 
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        subst j.
        rewrite gLockSetRes.
        rewrite gssThreadRes.
        rewrite computeMap_projection_2; auto.
        eapply HinvF;
          by eauto.
        rewrite gLockSetRes.
        rewrite gsoThreadRes; auto.
        eapply HinvF;
          by eauto.
      }
    }
    { (*disjointness between lockset and resources *)
      intros (bl & ofsl) rmap2 Hres2.
      specialize (HsimWeak _ pfc pff).
      assert (Hinj := injective HsimWeak).
      destruct HinvC' as [_ _ _ HinvC'].
      assert (H1 := gssLockRes (updThread pfc c (computeMap (getThreadR pfc) virtue))
                               (b1, ofs) rmap1).
      intros b2' ofs'.
      destruct HsimLP as [HpermLP _].
      destruct (EqDec_address (b2, ofs) (bl, ofsl)) as [Heq | Hneq].
      { inversion Heq; subst.
        specialize (HinvC' (b1, ofsl) _ H1).
        rewrite gssLockRes in Hres2. inversion Hres2. subst.
        destruct (Pos.eq_dec b2' bl) as [Heqb2' | Hneqb2'].
        - subst bl.
          specialize (HpermLP _ _ ofs' Hf).
          do 2 rewrite restrPermMap_Cur in HpermLP.
          destruct (Z_le_dec ofsl ofs').
          destruct (Z_lt_dec ofs' (ofsl + Z.of_nat (lksize.LKSIZE_nat))).
          erewrite gssLockSet by eauto.
          erewrite <- projectMap_correct; eauto.
          specialize (HinvC' b1 ofs').
          erewrite gssLockSet in HinvC';
            by eauto.
          erewrite gsoLockSet_1 by eauto.
          erewrite <- projectMap_correct; eauto.
          specialize (HinvC' b1 ofs').
          erewrite gsoLockSet_1 in HinvC' by eauto.
          rewrite gsoThreadLock.
          rewrite gsoThreadLock in HinvC'.
          rewrite HpermLP;
            by auto.
          erewrite gsoLockSet_1 by omega.
          erewrite <- projectMap_correct; eauto.
          specialize (HinvC' b1 ofs').
          erewrite gsoLockSet_1 in HinvC' by omega.
          rewrite gsoThreadLock.
          rewrite gsoThreadLock in HinvC'.
          rewrite HpermLP;
            by auto.
        - erewrite gsoLockSet_2 by eauto.
          assert (Hb2': (exists b1, f b1 = Some b2') \/
                        ~ (exists b1, f b1 = Some b2'))
            by eapply em.
          destruct Hb2' as [Hb2m' | Hb2u'].
          (*case b2' is mapped by f*)
          destruct Hb2m' as [b1' Hfb1'].
          erewrite <- projectMap_correct; eauto.
          specialize (HinvC' b1' ofs').
          rewrite gsoThreadLock.
          assert (b1 <> b1')
            by (intro Hcontra; subst; rewrite Hfb1' in Hf; inversion Hf; subst; auto).
          erewrite gsoLockSet_2 in HinvC' by eauto.
          rewrite gsoThreadLock in HinvC'.
          specialize (HpermLP _ _ ofs' Hfb1').
          do 2 rewrite restrPermMap_Cur in HpermLP.
          rewrite HpermLP;
            by auto.
          (*case b2' is not mapped*)
          erewrite projectMap_correct_2 by eauto.
          rewrite Hcanonical.
          eapply not_racy_union;
            by constructor.
      }
      { (* case it's another lock *)
        rewrite gsoLockRes in Hres2; auto.
        rewrite gsoThreadLPool in Hres2.
        specialize (Hlocks bl ofsl ltac:(rewrite Hres2; auto)).
        destruct Hlocks as [bl1 Hfbl1].
        assert (H := lockSet_spec_1 tpf bl ofsl ltac:(rewrite Hres2; auto)).
        specialize (snd (Hlock_if _ _ ofsl Hfbl1) ltac:(unfold isSome; rewrite Hres2; auto)).
        intro Hres1_true.
        destruct (lockRes tpc (bl1, ofsl)) as [res1|] eqn:Hres1; try by exfalso.
        specialize (HsimRes _ _ _ _ _ Hfbl1 Hres1 Hres2).
        destruct HsimRes as [HpermRes _].
        specialize (HinvC' (bl1, ofsl) res1).
        erewrite gsoLockRes in HinvC'
          by (intros Hcontra; inversion Hcontra; subst;
              rewrite Hfbl1 in Hf; inversion Hf; subst; auto).
        specialize (HinvC' Hres1).
        destruct (Pos.eq_dec b2 b2') as [Heqb2 | Hneqb2].
        - subst.
          erewrite <- lockSet_updLockSet; eauto.
          specialize (HpermRes _ _ ofs' Hf).
          do 2 rewrite restrPermMap_Cur in HpermRes. rewrite HpermRes.
          specialize (HinvC' b1 ofs').
          destruct (Z_le_dec ofs ofs').
          destruct (Z_lt_dec ofs' (ofs + Z.of_nat (lksize.LKSIZE_nat))).
          erewrite gssLockSet by eauto.
          erewrite gssLockSet in HinvC';
            by eauto.
          erewrite gsoLockSet_1 by eauto.
          erewrite gsoLockSet_1 in HinvC' by eauto.
          specialize (HpermLP _ _ ofs' Hf).
          do 2 rewrite restrPermMap_Cur in HpermLP.
          rewrite HpermLP;
            by auto.
          erewrite gsoLockSet_1 by omega.
          erewrite gsoLockSet_1 in HinvC' by omega.
          specialize (HpermLP _ _ ofs' Hf).
          do 2 rewrite restrPermMap_Cur in HpermLP.
          rewrite HpermLP;
            by auto.
        - erewrite <- lockSet_updLockSet; eauto.
          erewrite gsoLockSet_2 by eauto.
          assert (Hb2': (exists b1, f b1 = Some b2') \/
                        ~ (exists b1, f b1 = Some b2'))
            by eapply em.
          destruct Hb2' as [Hb2m' | Hb2u'].
          (*case b2' is mapped by f*)
          destruct Hb2m' as [b1' Hfb1'].
          specialize (HinvC' b1' ofs').
          assert (b1 <> b1')
            by (intro Hcontra; subst; rewrite Hfb1' in Hf; inversion Hf; subst; auto).
          erewrite gsoLockSet_2 in HinvC' by eauto.
          rewrite gsoThreadLock in HinvC'.
          specialize (HpermLP _ _ ofs' Hfb1').
          do 2 rewrite restrPermMap_Cur in HpermLP.
          rewrite HpermLP.
          specialize (HpermRes _ _ ofs' Hfb1').
          do 2 rewrite restrPermMap_Cur in HpermRes.
          rewrite HpermRes;
            by auto.
          (*case b2' is not mapped*)
          destruct HinvF.
          eapply lock_res_set0; eauto.
      }
    }
    { (* lr_valid *)
      intros b0 ofs0.
      destruct (lockRes
       (updLockSet
          (updThread pff cf
             (computeMap (getThreadR pff) (projectAngel f virtue)))
          (b2, ofs) (projectMap f rmap1)) (b0, ofs0)) eqn:Hres0; auto.
      intros ofs1 Hofs1.
      pose proof (lockRes_valid HinvC') as HlrC'.
      destruct (Pos.eq_dec b0 b2).
      { subst.
        destruct (Z.eq_dec ofs ofs1).
        - subst.
          specialize (HlrC' b1 ofs0).
          erewrite gsolockResUpdLock in HlrC'
            by (intros Hcontra; inversion Hcontra; subst; omega).
          erewrite gsolockResUpdLock in Hres0
            by (intros Hcontra; inversion Hcontra; subst; omega).
          rewrite gsoThreadLPool in Hres0.
          rewrite gsoThreadLPool in HlrC'.
          specialize (snd (Hlock_if _ _ ofs0 Hf) ltac:(rewrite Hres0;auto)).
          intro HresC.
          destruct (lockRes tpc (b1, ofs0)); try by exfalso.
          specialize (HlrC' ofs1 Hofs1).
          rewrite gsslockResUpdLock in HlrC'.
          discriminate.
        - erewrite gsolockResUpdLock
            by (intros Hcontra; inversion Hcontra; subst; auto).
          rewrite gsoThreadLPool.
          destruct (Z.eq_dec ofs ofs0).
          + subst.
            specialize (HlrC' b1 ofs0).
            rewrite gsslockResUpdLock in HlrC'.
            specialize (HlrC' ofs1 Hofs1).
            unfold lksize.LKSIZE in Hofs1. simpl in Hofs1.
            erewrite gsolockResUpdLock in HlrC'
              by (intro Hcontra; inversion Hcontra; subst; omega).
            rewrite gsoThreadLPool in HlrC'.
            destruct (lockRes tpf (b2, ofs1)) eqn:HlockF; auto.
            specialize (snd (Hlock_if _ _ ofs1 Hf) ltac:(rewrite HlockF; auto)).
            intro Hcontra. rewrite HlrC' in Hcontra; by exfalso.
          + erewrite gsolockResUpdLock in Hres0
              by (intro Hcontra; inversion Hcontra; subst; omega).
            rewrite gsoThreadLPool in Hres0.
            pose proof (lockRes_valid HinvF).
            specialize (H b2 ofs0).
            rewrite Hres0 in H; eauto.
      }
      { erewrite gsolockResUpdLock
          by (intro Hcontra; inversion Hcontra; subst; auto).
        rewrite gsoThreadLPool.
        erewrite gsolockResUpdLock in Hres0
          by (intro Hcontra; inversion Hcontra; subst; auto).
        rewrite gsoThreadLPool in Hres0.
        pose proof (lockRes_valid HinvF).
        specialize (H b0 ofs0).
        rewrite Hres0 in H; eauto. 
      }
    }
    Unshelve. auto. auto.
  Qed.
  
  (** The projected angel satisfies the [angelSpec] *)
    (* TODO: generalize this for non-empty map *)
  Lemma acqAngelSpec_project:
    forall (tpc tpf : thread_pool) (mc mf : mem) (f : memren)
      (i : tid)
      (pfc : containsThread tpc i)
      (pff : containsThread tpf i)
      (HmemCompC : mem_compatible tpc mc)
      (HmemCompF : mem_compatible tpf mf)
      (bl1 bl2 : block) ofs
      (pmap pmapF: dry_machine.LocksAndResources.lock_info)
      (virtueThread : delta_map)
      (Hres: lockRes tpc (bl1, ofs) = Some pmap)
      (HresF: lockRes tpf (bl2,ofs) = Some pmapF)
      (Hangel: acqAngelSpec pmap (getThreadR pfc) empty_map
                         (computeMap (getThreadR pfc) virtueThread))
      (Hf: f bl1 = Some bl2)
      (HsimRes: strong_mem_obs_eq f
                                  (restrPermMap (compat_lp HmemCompC (bl1, ofs) Hres))
                                  (restrPermMap (compat_lp HmemCompF (bl2, ofs) HresF)))
      (Htsim: strong_tsim f pfc pff HmemCompC HmemCompF),
      acqAngelSpec pmapF (getThreadR pff) empty_map
                (computeMap (getThreadR pff) (projectAngel f virtueThread)).
  Proof.
    intros.
    destruct Hangel as [HangelIncr HangelDecr].
    constructor.
    { (*Angel Incr *)
      intros b2 ofs0 Hperm.
    (*NOTE: this is actually decidable*)
    assert (Hb2: (exists b1, f b1 = Some b2) \/
                 ~ (exists b1, f b1 = Some b2))
      by eapply em.
    destruct Hb2 as [[b1 Hf1] | Hunmapped].
    destruct Htsim as [? Hmem_obs_eq].
    erewrite computeMap_projection_1 in Hperm; eauto.
    specialize (HangelIncr _ _ Hperm).
    destruct HangelIncr as [Hreadable | Hreadable];
      [destruct Hmem_obs_eq as [_ [Hperm_eq _]] | destruct HsimRes as [Hperm_eq _]];
      specialize (Hperm_eq _ _ ofs0 Hf1);
      do 2 rewrite restrPermMap_Cur in Hperm_eq;
      rewrite Hperm_eq;
        by auto.
    erewrite computeMap_projection_2 in Hperm; eauto.
    }
    { (*Angel Decr*)
      intros b2 ofs0.
      replace (empty_map # b2 ofs0) with (@None permission)
        by (unfold Maps.PMap.get; rewrite Maps.PTree.gempty; by simpl).
      destruct (pmapF # b2 ofs0);
        by simpl.
    }
  Qed.

  Lemma relAngelSpec_project:
    forall (tpc tpf : thread_pool) (mc mf : mem) (f : memren)
      (i : tid)
      (pfc : containsThread tpc i)
      (pff : containsThread tpf i)
      (HmemCompC : mem_compatible tpc mc)
      (HmemCompF : mem_compatible tpf mf)
      (bl1 bl2 : block) ofs
      (pmap pmapF virtueLP: dry_machine.LocksAndResources.lock_info)
      (Hcanonical: isCanonical virtueLP)
      (virtueThread : delta_map)
      (Hres: lockRes tpc (bl1, ofs) = Some pmap)
      (HresF: lockRes tpf (bl2,ofs) = Some pmapF)
      (Hangel: relAngelSpec (getThreadR pfc) pmap
                         (computeMap (getThreadR pfc) virtueThread) virtueLP)
      (Hf: f bl1 = Some bl2)
      (HsimRes: strong_mem_obs_eq f
                                  (restrPermMap (compat_lp HmemCompC (bl1, ofs) Hres))
                                  (restrPermMap (compat_lp HmemCompF (bl2, ofs) HresF)))
      (Htsim: strong_tsim f pfc pff HmemCompC HmemCompF),
      relAngelSpec (getThreadR pff) pmapF
                (computeMap (getThreadR pff)
                            (projectAngel f virtueThread))
                (projectMap f virtueLP).
  Proof.
    intros.
    destruct Hangel as [HangelIncr HangelDecr].
    constructor.
    { (* Angel Incr *)
      intros b2 ofs0.
      split.
      - intros Hperm.
        assert (Hb2: (exists b1, f b1 = Some b2) \/
                        ~ (exists b1, f b1 = Some b2))
            by eapply em.
        destruct Hb2 as [[b1 Hf1] | Hunmapped].
        + destruct Htsim as [? Hmem_obs_eq].
          erewrite computeMap_projection_1; eauto.
          destruct Hmem_obs_eq as [Hweak_obs_eq [Hperm_eq _]].
          specialize (Hperm_eq _ _ ofs0 Hf1).
          do 2 rewrite restrPermMap_Cur in Hperm_eq.
          rewrite Hperm_eq in Hperm.
          pose proof (fst (HangelIncr b1 ofs0) ltac:(eauto)).
          destruct H.
          erewrite <- projectMap_correct; eauto.
          apply (injective Hweak_obs_eq).
          auto.
        + erewrite computeMap_projection_2; eauto.
      - intros [HpermT | HpermS].
        + assert (Hb2: (exists b1, f b1 = Some b2) \/
                        ~ (exists b1, f b1 = Some b2))
            by eapply em.
          destruct Hb2 as [[b1 Hf1] | Hunmapped].
          * destruct Htsim as [? Hmem_obs_eq].
            destruct Hmem_obs_eq as [Hweak_obs_eq [Hperm_eq _]].
            specialize (Hperm_eq _ _ ofs0 Hf1).
            erewrite <- projectMap_correct in HpermT; eauto.
            pose proof (snd (HangelIncr b1 ofs0) ltac:(eauto)).
            do 2 rewrite restrPermMap_Cur in Hperm_eq.
            rewrite Hperm_eq; auto.
            apply (injective Hweak_obs_eq).
          * erewrite projectMap_correct_2 in HpermT by eauto.
            rewrite Hcanonical in HpermT.
            simpl in HpermT;
              by exfalso.
      -  assert (Hb2: (exists b1, f b1 = Some b2) \/
                      ~ (exists b1, f b1 = Some b2))
          by eapply em.
         destruct Hb2 as [[b1 Hf1] | Hunmapped].
         * destruct Htsim as [? Hmem_obs_eq].
           erewrite computeMap_projection_1 in HpermS; eauto.
           destruct Hmem_obs_eq as [_ [Hperm_eq _]].
           specialize (Hperm_eq _ _ ofs0 Hf1).
           do 2 rewrite restrPermMap_Cur in Hperm_eq.
           rewrite Hperm_eq.
           pose proof (snd (HangelIncr b1 ofs0) ltac:(eauto));
             by auto.
         * erewrite computeMap_projection_2 in HpermS;
             by eauto.
    }
    { (* Angel decrease*)
      intros b2 ofs0.
      assert (Hb2: (exists b1, f b1 = Some b2) \/
                   ~ (exists b1, f b1 = Some b2))
        by eapply em.
      destruct Hb2 as [[b1 Hf1] | Hunmapped].
      destruct Htsim as [_ Hmem_obs_eq].
      erewrite computeMap_projection_1; eauto.
      destruct Hmem_obs_eq. destruct strong_obs_eq0.
      specialize (perm_obs_strong0 _ _ ofs0 Hf1).
      do 2 rewrite restrPermMap_Cur in perm_obs_strong0.
      rewrite perm_obs_strong0;
        by eauto.
      rewrite computeMap_projection_2; eauto.
        by apply po_refl.
    }
  Qed.
  
  Lemma gss_mem_obs_eq_lock:
    forall tpc tpf mc mf mc' mf' pmap pmapF
      c cf i (f: memren)
      bl1 bl2 ofs v virtue
      (pfc: containsThread tpc i)
      (pff: containsThread tpf i)
      (pfc': containsThread (updLockSet
                               (updThread pfc (Kresume c Vundef)
                                          (computeMap (getThreadR pfc) virtue))
                               (bl1, ofs) empty_map) i)
      (pff': containsThread (updLockSet
                               (updThread pff (Kresume cf Vundef)
                                          (computeMap (getThreadR pff)
                                                      (projectAngel f virtue)))
                               (bl1, ofs) empty_map) i)
      (HmemCompC: mem_compatible tpc mc)
      (HmemCompF: mem_compatible tpf mf)
      (HmemCompC': mem_compatible
                     (updLockSet
                        (updThread pfc (Kresume c Vundef)
                                   (computeMap (getThreadR pfc) virtue))
                        (bl1, ofs) empty_map) mc')
      (HmemCompF'' : mem_compatible
                       (updLockSet
                          (updThread pff (Kresume cf Vundef)
                                     (computeMap (getThreadR pff)
                                                 (projectAngel f virtue)))
                          (bl2, ofs) empty_map) mf')
      (Hf: f bl1 = Some bl2)
      (HinvC: invariant tpc)
      (HinvF: invariant tpf)
      (HisLock : lockRes tpc (bl1, ofs) = Some pmap)
      (HisLockF : lockRes tpf (bl2, ofs) = Some pmapF)
      (Hobs_eq: mem_obs_eq f (restrPermMap (HmemCompC i pfc))
                           (restrPermMap (HmemCompF i pff)))
      (HstoreC: Mem.store Mint32 (restrPermMap (compat_ls HmemCompC)) bl1
                          ofs (Vint v) = Some mc')
      (HstoreF: Mem.store Mint32 (restrPermMap (compat_ls HmemCompF)) bl2
                          ofs (Vint v) = Some mf')
      (Hangel : acqAngelSpec pmap (getThreadR pfc) empty_map
                          (computeMap (getThreadR pfc) virtue))
      (HsimRes:
         strong_mem_obs_eq f
                           (restrPermMap (compat_lp HmemCompC (bl1, ofs) HisLock))
                           (restrPermMap (compat_lp HmemCompF (bl2, ofs) HisLockF))),
      mem_obs_eq f (restrPermMap (HmemCompC' i pfc'))
                 (restrPermMap (HmemCompF'' i pff')).
  Proof.
    intros.
    inversion Hobs_eq.
    assert (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b)
      by (
          intros;
          erewrite <- restrPermMap_valid with (Hlt := compat_ls HmemCompC);
          split;
          [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
          eauto).
    assert (Hvb': forall b, ~ Mem.valid_block mc b <-> ~ Mem.valid_block mc' b)
      by (intros; split; intros Hinvalid Hcontra;
            by apply Hvb in Hcontra).
    assert (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b)
      by (
          intros;
          erewrite <- restrPermMap_valid with (Hlt := compat_ls HmemCompF);
          split;
          [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
          eauto).
    constructor.
    (*weak_obs_eq*)
    destruct weak_obs_eq0.
    constructor;
      try (intros b1; erewrite restrPermMap_valid);
      try (erewrite <- Hvb');
      try (erewrite <- Hvb);
      try by eauto.
    intros b1 b2 Hf1. erewrite restrPermMap_valid.
    erewrite <- HvbF.
    specialize (codomain_valid0 _ _ Hf1);
      by erewrite restrPermMap_valid in codomain_valid0.
    intros b1 b2 ofs0 Hf1.
    do 2 rewrite restrPermMap_Cur.
    do 2 rewrite gLockSetRes.
    do 2 rewrite gssThreadRes.
    erewrite computeMap_projection_1; eauto;
      by apply po_refl.
    constructor.
    intros b1 b2 ofs0 Hf1.
    do 2 rewrite restrPermMap_Cur.
    do 2 rewrite gLockSetRes.
    do 2 rewrite gssThreadRes.
    erewrite computeMap_projection_1; eauto;
      by apply po_refl.
    intros b1 b2 ofs0 Hf1 Hperm.
    destruct Hangel as [HangelIncr HangelDecr].
    unfold Mem.perm in *.
    assert (Hperm_eq := restrPermMap_Cur (HmemCompC' i pfc') b1 ofs0).
    unfold permission_at in Hperm_eq.
    rewrite Hperm_eq in Hperm.
    rewrite gLockSetRes in Hperm.
    rewrite gssThreadRes in Hperm.
    specialize (HangelIncr _ _ Hperm).
    destruct HangelIncr as [Hreadablei | Hreadablelp].
    (* case the address was already readable on thread i*)
    simpl.
    destruct strong_obs_eq0 as [_ Hval_obs_eq].
    unfold Mem.perm in Hval_obs_eq.
    assert (Hperm_eq_old := restrPermMap_Cur (HmemCompC i pfc) b1 ofs0).
    unfold permission_at in Hperm_eq_old.
    specialize (Hval_obs_eq _ _ ofs0 Hf1).
    rewrite Hperm_eq_old in Hval_obs_eq.
    specialize (Hval_obs_eq Hreadablei).
    simpl in Hval_obs_eq.
    destruct weak_obs_eq0.
    destruct HinvC.
    eapply gsoMem_obs_eq with (bl1 := bl1) (HltC := compat_ls HmemCompC)
                                           (HltF := compat_ls HmemCompF)
                                           (pmapC':= getThreadR pfc);
      by eauto.
    (*case the address was readable on the lockpool*)
    simpl.
    destruct HsimRes as [_ Hval_obs_eq].
    unfold Mem.perm in Hval_obs_eq.
    assert (Hperm_eq_old := restrPermMap_Cur
                              (compat_lp HmemCompC (bl1, ofs) HisLock) b1 ofs0).
    unfold permission_at in Hperm_eq_old.
    specialize (Hval_obs_eq _ _ ofs0 Hf1).
    rewrite Hperm_eq_old in Hval_obs_eq.
    specialize (Hval_obs_eq Hreadablelp).
    simpl in Hval_obs_eq.
    destruct weak_obs_eq0.
    destruct HinvC.
    specialize (lock_res_set0 _ _ HisLock).
    apply permMapsDisjoint_comm in lock_res_set0.
    eapply gsoMem_obs_eq with (bl1 := bl1) (HltC := compat_ls HmemCompC)
                                           (HltF := compat_ls HmemCompF)
                                           (pmapC':= pmap);
      by eauto.
  Qed.

  Lemma invariant_mklock:
    forall (tpc tpf : thread_pool) (i : tid) (cnti : containsThread tpf i)
      (ccnti: containsThread tpc i)
      ofs (bc b : block) (c cc: ctl) pmapc f
      (Hdrop:
         forall ofs0, (ofs <= ofs0 < ofs + Z.of_nat (lksize.LKSIZE_nat))%Z ->
                 Mem.perm_order' ((getThreadR cnti) # b ofs0) Writable)
      (Hlock_if: forall (bl1 bl2 : block) (ofs : Z),
          f bl1 = Some bl2 ->
          lockRes tpc (bl1, ofs) <-> lockRes tpf (bl2, ofs))
      (Hf: f bc = Some b)
      (HinvC: invariant
               (updLockSet
                  (updThread ccnti cc pmapc) 
                  (bc, ofs) empty_map))
      (Hinv: invariant tpf),
      invariant
        (updLockSet
           (updThread cnti c
                      (setPermBlock (Some Nonempty) b ofs 
                                    (getThreadR cnti) lksize.LKSIZE_nat)) 
           (b, ofs) empty_map).
  Proof.
    intros.
    constructor.
    - intros j k cntj cntk Hkj.
      destruct Hinv as [Hinv _ _ _].
      assert (cntk0 : containsThread tpf k).
        by (apply cntUpdateL' in cntk;
             apply cntUpdate' in cntk; auto).
      assert (cntj0 : containsThread tpf j)
        by (apply cntUpdateL' in cntj;
             apply cntUpdate' in cntj; auto).
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
      + subst.
        do 2 rewrite gLockSetRes.
        rewrite gssThreadRes.
        rewrite gsoThreadRes; auto.
        intros b' ofs'.
        pf_cleanup.
        specialize (Hinv _ _ cntj0 cntk0 Hkj b' ofs').
        destruct (Pos.eq_dec b b') as [? | Hbneq].
        * subst.
          destruct (Z_le_dec ofs ofs').
          destruct (Z_lt_dec ofs' (ofs + Z.of_nat (lksize.LKSIZE_nat))).
          erewrite setPermBlock_same; eauto.
          specialize (Hdrop _ ltac:(eauto)).
          rewrite perm_union_comm.
          rewrite perm_union_comm in Hinv.
          eapply perm_union_lower; eauto.
          rewrite po_oo in Hdrop.
          eapply po_trans; eauto.
          constructor.
          erewrite setPermBlock_other_1; eauto.
          erewrite setPermBlock_other_1 by omega; eauto.
        * rewrite setPermBlock_other_2; auto.
      + do 2 rewrite gLockSetRes.
        rewrite gsoThreadRes; auto.
        specialize (Hinv _ _ cntj0 cntk0 Hkj).
        destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
        * subst.
          rewrite gssThreadRes; auto.
          intros b' ofs'.
          pf_cleanup.
          specialize (Hinv b' ofs').
          destruct (Pos.eq_dec b b') as [? | Hbneq].
          subst.
          destruct (Z_le_dec ofs ofs').
          destruct (Z_lt_dec ofs' (ofs + Z.of_nat (lksize.LKSIZE_nat))).
          erewrite setPermBlock_same; eauto.
          specialize (Hdrop _ ltac:(eauto)).
          eapply perm_union_lower; eauto.
          rewrite po_oo in Hdrop.
          eapply po_trans; eauto.
          constructor.
          erewrite setPermBlock_other_1; eauto.
          erewrite setPermBlock_other_1 by omega; eauto.
          rewrite setPermBlock_other_2; auto.
        * rewrite gsoThreadRes; auto.
    - intros j cntj''.
      destruct Hinv as [Hno_race Hinv _ _].
      intros b' ofs'.
      rewrite <- lockSet_updLockSet.
      destruct (Pos.eq_dec b b').
      + subst.
        destruct (Z_le_dec ofs ofs').
        destruct (Z_lt_dec ofs' (ofs + Z.of_nat (lksize.LKSIZE_nat))).
        * rewrite gssLockSet; auto.
          rewrite gLockSetRes.
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          subst.
          rewrite gssThreadRes.
          erewrite setPermBlock_same; eauto.
          simpl; eexists;
            by eauto.
          rewrite gsoThreadRes; auto.
          specialize (Hno_race _ _ cnti cntj'' Hij b' ofs').
          specialize (Hdrop ofs' ltac:(eauto)).
          rewrite perm_union_comm.
          rewrite perm_union_comm in Hno_race.
          eapply perm_union_lower; eauto.
        * rewrite gLockSetRes.
          erewrite gsoLockSet_1 by auto.
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          subst.
          rewrite gssThreadRes.
          erewrite setPermBlock_other_1; eauto.
          specialize (Hinv _ cnti b' ofs');
            by eauto.
          rewrite gsoThreadRes; auto.
          specialize (Hinv _ cntj'' b' ofs'); eauto.
        * erewrite gsoLockSet_1 by omega.
          rewrite gLockSetRes.
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          subst.
          rewrite gssThreadRes.
          erewrite setPermBlock_other_1 by omega; eauto.
          specialize (Hinv _ cnti b' ofs'); eauto.
          rewrite gsoThreadRes; auto.
          specialize (Hinv _ cntj'' b' ofs'); eauto.
        * erewrite gsoLockSet_2 by (intro Hcontra; inversion Hcontra; auto).
          rewrite gLockSetRes.
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          subst.
          rewrite gssThreadRes.
          erewrite setPermBlock_other_2
            by (intro Hcontra; inversion Hcontra; auto).
          specialize (Hinv _ cnti b' ofs');
            by eauto.
          rewrite gsoThreadRes; auto.
          specialize (Hinv _ cntj'' b' ofs');
            by eauto.
    - intros (b', ofs') rmap j cntj Hres.
      rewrite gLockSetRes.
      destruct (EqDec_address (b, ofs) (b', ofs')).
      + inversion e; subst.
        rewrite gsslockResUpdLock in Hres.
        inversion Hres; subst.
        apply empty_disjoint'.
      + rewrite gsolockResUpdLock in Hres; auto.
        destruct Hinv as [_ _ Hinv _].
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        * subst. rewrite gssThreadRes.
          specialize (Hinv _ _ _ cnti Hres).
          intros b'' ofs''.
          specialize (Hinv b'' ofs'').
          destruct (Pos.eq_dec b b'').
          { subst b''.
            destruct (Z_le_dec ofs ofs'').
            destruct (Z_lt_dec ofs'' (ofs + Z.of_nat (lksize.LKSIZE_nat))).
            - erewrite setPermBlock_same by eauto.
              specialize (Hdrop ofs'' ltac:(auto)).
              eapply perm_union_lower; eauto.
              rewrite po_oo in Hdrop.
              eapply po_trans; eauto.
              constructor.
            - erewrite setPermBlock_other_1; eauto.
            - erewrite setPermBlock_other_1 by omega; eauto.
          }
          { erewrite setPermBlock_other_2; eauto. }
        * rewrite gsoThreadRes; auto.
          specialize (Hinv _ _ _ cntj Hres). auto.
    - intros (b', ofs') rmap Hres.
      rewrite <- lockSet_updLockSet.
      destruct (EqDec_address (b, ofs) (b', ofs')).
      + inversion e; subst.
        rewrite gsslockResUpdLock in Hres.
        inversion Hres; subst.
        apply empty_disjoint'.
      + rewrite gsolockResUpdLock in Hres; auto.
        destruct Hinv as [_ _ Hno_race Hinv].
        intros b'' ofs''.
        specialize (Hinv _ _ Hres b'' ofs'').
        destruct (Pos.eq_dec b b'').
        { subst b''.
          destruct (Z_le_dec ofs ofs'').
          destruct (Z_lt_dec ofs'' (ofs + Z.of_nat (lksize.LKSIZE_nat))).
          - erewrite gssLockSet; eauto.
            rewrite gsoThreadLPool in Hres.
            specialize (Hno_race _ _ _ cnti Hres b ofs'').
            specialize (Hdrop ofs'' ltac:(eauto)).
            clear Hinv.
            eapply perm_union_lower;
              by eauto.
          - erewrite gsoLockSet_1 by eauto.
            rewrite gsoThreadLPool in Hres.
            eauto.
          - erewrite gsoLockSet_1 by omega.
            rewrite gsoThreadLPool in Hres.
            eauto.
        }
        { erewrite gsoLockSet_2; eauto. }
    -  (* lr_valid *)
      intros b0 ofs0.
      destruct (lockRes
       (updLockSet
          (updThread cnti c
             (setPermBlock (Some Nonempty) b ofs 
                (getThreadR cnti) lksize.LKSIZE_nat)) 
          (b, ofs) empty_map) (b0, ofs0)) eqn:Hres0; auto.
      intros ofs1 Hofs1.
      pose proof (lockRes_valid HinvC) as HlrC'.
      destruct (Pos.eq_dec b0 b).
      { subst.
        destruct (Z.eq_dec ofs ofs1).
        - subst.
          specialize (HlrC' bc ofs0).
          erewrite gsolockResUpdLock in HlrC'
            by (intros Hcontra; inversion Hcontra; subst; omega).
          erewrite gsolockResUpdLock in Hres0
            by (intros Hcontra; inversion Hcontra; subst; omega).
          rewrite gsoThreadLPool in Hres0.
          rewrite gsoThreadLPool in HlrC'.
          specialize (snd (Hlock_if _ _ ofs0 Hf) ltac:(rewrite Hres0;auto)).
          intro HresC.
          destruct (lockRes tpc (bc, ofs0)); try by exfalso.
          specialize (HlrC' ofs1 Hofs1).
          rewrite gsslockResUpdLock in HlrC'.
          discriminate.
        - erewrite gsolockResUpdLock
            by (intros Hcontra; inversion Hcontra; subst; auto).
          rewrite gsoThreadLPool.
          destruct (Z.eq_dec ofs ofs0).
          + subst.
            specialize (HlrC' bc ofs0).
            rewrite gsslockResUpdLock in HlrC'.
            specialize (HlrC' ofs1 Hofs1).
            unfold lksize.LKSIZE in Hofs1. simpl in Hofs1.
            erewrite gsolockResUpdLock in HlrC'
              by (intro Hcontra; inversion Hcontra; subst; omega).
            rewrite gsoThreadLPool in HlrC'.
            destruct (lockRes tpf (b, ofs1)) eqn:HlockF; auto.
            specialize (snd (Hlock_if _ _ ofs1 Hf) ltac:(rewrite HlockF; auto)).
            intro Hcontra. rewrite HlrC' in Hcontra; by exfalso.
          + erewrite gsolockResUpdLock in Hres0
              by (intro Hcontra; inversion Hcontra; subst; omega).
            rewrite gsoThreadLPool in Hres0.
            pose proof (lockRes_valid Hinv).
            specialize (H b ofs0).
            rewrite Hres0 in H; eauto.
      }
      { erewrite gsolockResUpdLock
          by (intro Hcontra; inversion Hcontra; subst; auto).
        rewrite gsoThreadLPool.
        erewrite gsolockResUpdLock in Hres0
          by (intro Hcontra; inversion Hcontra; subst; auto).
        rewrite gsoThreadLPool in Hres0.
        pose proof (lockRes_valid Hinv).
        specialize (H b0 ofs0).
        rewrite Hres0 in H; eauto. 
      }
  Qed.
  

   
  Lemma gss_mem_obs_eq_unlock:
    forall  tpc tpf mc mf mc' mf'
       c cf i (f: memren)
       bl1 bl2 ofs v
       (virtueThread : delta_map) (virtueLP : access_map) 
       (pmap pmapF: dry_machine.LocksAndResources.lock_info)
       (pfc: containsThread tpc i)
       (pff: containsThread tpf i)
       (HmemCompC : mem_compatible tpc mc)
       (HmemCompF : mem_compatible tpf mf)
       (HmemCompC' : mem_compatible
                       (updLockSet
                          (updThread pfc (Kresume c Vundef)
                                     (computeMap (getThreadR pfc) virtueThread))
                          (bl1, ofs) virtueLP) mc')
       (HmemCompF'' : mem_compatible
                        (updLockSet
                           (updThread pff (Kresume cf Vundef)
                                      (computeMap (getThreadR pff)
                                                  (projectAngel f virtueThread)))
                           (bl2, ofs)
                           (projectMap f virtueLP)) mf')
       (pff' : containsThread
                 (updLockSet
                    (updThread pff (Kresume cf Vundef)
                               (computeMap (getThreadR pff)
                                           (projectAngel f virtueThread)))
                    (bl2, ofs) (projectMap f virtueLP)) i)
       (pfc' : containsThread
                 (updLockSet
                    (updThread pfc (Kresume c Vundef)
                               (computeMap (getThreadR pfc) virtueThread))
                    (bl1,  ofs) virtueLP) i)
       (Hf: f bl1 = Some bl2)
       (Hangel: relAngelSpec (getThreadR pfc) pmap (computeMap (getThreadR pfc) virtueThread)
                          virtueLP)
       (Hobs_eq: mem_obs_eq f (restrPermMap (HmemCompC i pfc))
                            (restrPermMap (HmemCompF i pff)))
       (Hstore: Mem.store Mint32 (restrPermMap (compat_ls HmemCompC)) bl1 
                          ofs (Vint v) = Some mc')
       (HstoreF: Mem.store Mint32 (restrPermMap (compat_ls HmemCompF)) bl2 
                           ofs (Vint v) = Some mf')
       (HinvC: invariant tpc)
       (HsimLock: strong_mem_obs_eq f
                                    (restrPermMap (compat_ls HmemCompC))
                                    (restrPermMap (compat_ls HmemCompF))),
      mem_obs_eq f (restrPermMap (HmemCompC' i pfc'))
                 (restrPermMap (HmemCompF'' i pff')).
  Proof.
    intros.
    inversion Hobs_eq.
    assert (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b)
      by (
          intros;
          erewrite <- restrPermMap_valid with (Hlt := compat_ls HmemCompC);
          split;
          [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
          eauto).
    assert (Hvb': forall b, ~ Mem.valid_block mc b <-> ~ Mem.valid_block mc' b)
      by (intros; split; intros Hinvalid Hcontra;
            by apply Hvb in Hcontra).
    assert (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b)
      by (
          intros;
          erewrite <- restrPermMap_valid with (Hlt := compat_ls HmemCompF);
          split;
          [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
          eauto).
    constructor.
    (*weak_obs_eq*)
    destruct weak_obs_eq0.
    constructor;
      try (intros b1; erewrite restrPermMap_valid);
      try (erewrite <- Hvb');
      try (erewrite <- Hvb);
      try by eauto.
    intros b1 b2 Hf1. erewrite restrPermMap_valid.
    erewrite <- HvbF.
    specialize (codomain_valid0 _ _ Hf1);
      by erewrite restrPermMap_valid in codomain_valid0.
    intros b1 b2 ofs0 Hf1.
    do 2 rewrite restrPermMap_Cur.
    do 2 rewrite gLockSetRes.
    do 2 rewrite gssThreadRes.
    erewrite computeMap_projection_1; eauto;
      by apply po_refl.
    constructor.
    intros b1 b2 ofs0 Hf1.
    do 2 rewrite restrPermMap_Cur.
    do 2 rewrite gLockSetRes.
    do 2 rewrite gssThreadRes.
    erewrite computeMap_projection_1; eauto;
      by apply po_refl.
    intros b1 b2 ofs0 Hf1 Hperm.
    destruct Hangel as [HangelIncr HangelDecr].
    unfold Mem.perm in *.
    assert (Hperm_eq := restrPermMap_Cur (HmemCompC' i pfc') b1 ofs0).
    unfold permission_at in Hperm_eq.
    rewrite Hperm_eq in Hperm.
    rewrite gLockSetRes in Hperm.
    rewrite gssThreadRes in Hperm.
    specialize (HangelDecr b1 ofs0).
    assert (Hgt: Mem.perm_order'' ((getThreadR pfc) # b1 ofs0) (Some Readable))
      by (eapply po_trans; eauto).
    simpl.
    assert (Hstable: ~ Mem.perm (restrPermMap (compat_ls HmemCompC)) b1 ofs0
                       Cur Writable).
    { intros Hperm'.
      unfold Mem.perm in *.
      assert (H := (lock_set_threads HinvC) _ pfc b1 ofs0).
      assert (Hls:= restrPermMap_Cur (compat_ls HmemCompC) b1 ofs0).
      unfold permission_at in Hls.
      eapply perm_order_clash; eauto.
      rewrite Hls.
        by rewrite perm_union_comm.
    }
    erewrite store_contents_other with (m := (restrPermMap (compat_ls HmemCompC)));
      eauto.
    simpl.
    assert (HstableF: ~ Mem.perm (restrPermMap (compat_ls HmemCompF)) b2 ofs0
                        Cur Writable).
    { intros Hcontra.
      destruct HsimLock as [HpermLock_eq _].
      specialize (HpermLock_eq b1 b2 ofs0 Hf1).
      unfold Mem.perm in *.
      unfold permission_at in *.
      rewrite HpermLock_eq in Hcontra.
        by auto.
    }
    erewrite store_contents_other with (m := (restrPermMap (compat_ls HmemCompF)))
                                         (m' := mf');
      eauto.
    simpl.
    destruct strong_obs_eq0.
    simpl in val_obs_eq0.
    unfold Mem.perm in *.
    rewrite <- po_oo in Hgt.
    assert (H1 := restrPermMap_Cur (HmemCompC i pfc) b1 ofs0).
    unfold permission_at in H1.
    specialize (val_obs_eq0 _ _ ofs0 Hf1 ltac:(rewrite H1; auto)).
      by eauto.
  Qed.


  Lemma setPermBlock_obs_eq:
    forall f bl1 bl2 ofsl b1 b2 ofs pmap pmap'
      (Hf: f b1 = Some b2)
      (Hfl: f bl1 = Some bl2)
      (Hinjective: forall b1 b1' b2 : block,
          f b1 = Some b2 -> f b1' = Some b2 -> b1 = b1')
      (Hperm: pmap # b1 ofs = pmap' # b2 ofs),
      (setPermBlock (Some Nonempty) bl1 ofsl pmap
                    lksize.LKSIZE_nat) # b1 ofs =
      (setPermBlock (Some Nonempty) bl2 ofsl pmap'
                    lksize.LKSIZE_nat) # b2 ofs.
  Proof.
    intros.
    destruct (Pos.eq_dec b1 bl1).
    - subst.
      assert (b2 = bl2)
        by (rewrite Hf in Hfl; inversion Hfl; subst; auto).
      subst.
      destruct (Intv.In_dec ofs (ofsl, (ofsl + lksize.LKSIZE)%Z)).
      + erewrite setPermBlock_same by eauto.
        erewrite setPermBlock_same by eauto.
        reflexivity.
      + apply Intv.range_notin in n.
        simpl in n.
        erewrite setPermBlock_other_1 by eauto.
        erewrite setPermBlock_other_1 by eauto.
        eauto.
        unfold lksize.LKSIZE. simpl. omega.
    - erewrite setPermBlock_other_2 by eauto.
      assert (b2 <> bl2)
        by (intros Hcontra;
             subst; specialize (Hinjective _ _ _ Hf Hfl); subst; auto).
      erewrite setPermBlock_other_2 by eauto.
      eauto.
  Qed.

  (** Maintating mem_obs_eq after makelock for the thread that created the lock*)  
  Lemma mem_obs_eq_makelock:
    forall  tpc tpf mc mf mc' mf' c cf i (f: memren)
       bl1 bl2 ofs v
       (pfc: containsThread tpc i)
       (pff: containsThread tpf i)
       (HmemCompC : mem_compatible tpc mc)
       (HmemCompF : mem_compatible tpf mf)
       (HmemCompC' : mem_compatible
                       (updLockSet
                          (updThread pfc (Kresume c Vundef)
                                     (setPermBlock (Some Nonempty) bl1
                                                   ofs (getThreadR pfc)
                                                   lksize.LKSIZE_nat))
                          (bl1, ofs)
                          empty_map) mc')
       (HmemCompF'' : mem_compatible
                        (updLockSet
                           (updThread pff (Kresume cf Vundef)
                                      (setPermBlock (Some Nonempty) bl2 
                                                    ofs (getThreadR pff)
                                                    lksize.LKSIZE_nat))
                           (bl2, ofs)
                           empty_map) mf')
       (pff' : containsThread
                 (updLockSet
                    (updThread pff (Kresume cf Vundef)
                               (setPermBlock (Some Nonempty) bl2 
                                             ofs (getThreadR pff)
                                             lksize.LKSIZE_nat))
                    (bl2, ofs) empty_map) i)
       (pfc' : containsThread
                 (updLockSet
                    (updThread pfc (Kresume c Vundef)
                               (setPermBlock (Some Nonempty) bl1
                                             ofs (getThreadR pfc)
                                             lksize.LKSIZE_nat))
                    (bl1, ofs) empty_map) i)
       (Hf: f bl1 = Some bl2)
       (Hobs_eq: mem_obs_eq f (restrPermMap (HmemCompC i pfc))
                            (restrPermMap (HmemCompF i pff)))
       (Hstore: Mem.store Mint32 (restrPermMap (HmemCompC i pfc)) bl1 
                          ofs (Vint v) = Some mc')
       (HstoreF: Mem.store Mint32 (restrPermMap (HmemCompF i pff)) bl2 
                           ofs (Vint v) = Some mf'),
      mem_obs_eq f (restrPermMap (HmemCompC' i pfc'))
                 (restrPermMap (HmemCompF'' i pff')).
  Proof.
    intros.
    inversion Hobs_eq.
    assert (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b)
      by (intros;
           erewrite <- restrPermMap_valid with (Hlt := HmemCompC _ pfc);
           split;
           [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
           eauto).
    assert (Hvb': forall b, ~ Mem.valid_block mc b <-> ~ Mem.valid_block mc' b)
      by (intros; split; intros Hinvalid Hcontra;
            by apply Hvb in Hcontra).
    assert (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b)
      by (
          intros;
          erewrite <- restrPermMap_valid with (Hlt := HmemCompF _ pff);
          split;
          [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
          eauto).
    destruct weak_obs_eq0.
    destruct strong_obs_eq0.
    constructor.
    - (*weak_obs_eq*)
      constructor;
      try (intros b1; erewrite restrPermMap_valid);
      try (erewrite <- Hvb');
      try (erewrite <- Hvb);
      try by eauto.
      intros b1 b2 Hf1. erewrite restrPermMap_valid.
      erewrite <- HvbF.
      specialize (codomain_valid0 _ _ Hf1);
        by erewrite restrPermMap_valid in codomain_valid0.
      intros b1 b2 ofs0 Hf1.
      do 2 rewrite restrPermMap_Cur gLockSetRes gssThreadRes.
      specialize (perm_obs_strong0 _ _ ofs0 Hf1).
      do 2 rewrite restrPermMap_Cur in perm_obs_strong0.
      erewrite setPermBlock_obs_eq by eauto.
      apply po_refl.
    - constructor.
      intros.
      specialize (perm_obs_strong0 _ _ ofs0 Hrenaming).
      do 2 rewrite restrPermMap_Cur in perm_obs_strong0.
      do 2 rewrite restrPermMap_Cur gLockSetRes gssThreadRes.
      erewrite <- setPermBlock_obs_eq; eauto.
      intros.
      simpl.
      unfold Mem.perm in *.
      assert (Heq := restrPermMap_Cur (HmemCompC' i pfc') b1 ofs0).
      unfold permission_at in Heq.
      erewrite gLockSetRes with (cnti' := pfc') (cnti := pfc) in Heq at 2 by eauto.
      rewrite gssThreadRes in Heq.
      rewrite Heq in Hperm.
      assert (Heq0 := restrPermMap_Cur (HmemCompC i pfc) b1 ofs0).
      unfold permission_at in Heq0.
      specialize (val_obs_eq0 _ _ ofs0 Hrenaming).
      rewrite Heq0 in val_obs_eq0.
      simpl in val_obs_eq0.
      erewrite Mem.store_mem_contents by eauto.
      erewrite Mem.store_mem_contents with (m2 := mf') by eauto.
      destruct (Pos.eq_dec bl1 b1).
      + subst.
        assert (b2 = bl2)
          by (rewrite Hf in Hrenaming; inversion Hrenaming; subst; auto).
        subst.
        rewrite Maps.PMap.gss.
        rewrite Maps.PMap.gss.
        destruct (Intv.In_dec ofs0 (ofs, (ofs + lksize.LKSIZE)%Z)).
        * erewrite setPermBlock_same in Hperm by eauto.
          simpl in Hperm. inversion Hperm.
        * apply Intv.range_notin in n.
          simpl in n.
          erewrite setPermBlock_other_1 in Hperm by eauto.
          simpl.
          erewrite Mem.setN_outside by eauto.
          erewrite Mem.setN_outside by eauto.
          eauto.
          unfold lksize.LKSIZE; simpl. omega.
      + erewrite Maps.PMap.gso by auto.
        assert (bl2 <> b2)
          by (intros Hcontra;
               subst; specialize (injective0 _ _ _ Hf Hrenaming); subst; auto).
        erewrite Maps.PMap.gso by eauto.
        simpl.
        erewrite setPermBlock_other_2 in Hperm by auto.
        eauto.
  Qed.

  (** Performing a store on some disjoint part of the memory, retains
  a strong simulation, using the id injection, for threads*)
  Lemma strong_tsim_store_id:
    forall tp tp' m m' i b ofs v pmap
      (pfi: containsThread tp i)
      (pfi': containsThread tp' i)
      (Hresi: getThreadR pfi' = getThreadR pfi)
      (Hcodei: getThreadC pfi' = getThreadC pfi)
      (Hcomp: mem_compatible tp m)
      (Hcomp': mem_compatible tp' m')
      (Hlt: permMapLt pmap (getMaxPerm m))
      (Hno_race: permMapsDisjoint (getThreadR pfi) pmap)
      (Hmem_wd: valid_mem m)
      (Htp_wd: tp_wd (id_ren m) tp)
      (Hstore: Mem.store Mint32
                         (restrPermMap Hlt) b ofs v = Some m'),
      (strong_tsim (id_ren m) pfi pfi' Hcomp Hcomp') /\
      (Mem.nextblock m = Mem.nextblock m').
  Proof.
    intros.
    split.
    constructor.
    { (* ctl_inj between threads *)
      rewrite Hcodei.
      specialize (Htp_wd _ pfi).
      destruct (getThreadC pfi); simpl in *;
      repeat match goal with
             | [|- core_inj _ _ _] =>
               apply core_inj_id; auto
             | [H: _ /\ _ |- _] => destruct H
             | [|- _ /\ _] => split
             | [|- val_obs _ _ _] =>
               apply val_obs_id; auto
             end;
      try (apply id_ren_correct).
    }
    { (* mem_obs_eq *)
      constructor.
      constructor.
      intros b0 Hinvalid. erewrite restrPermMap_valid in Hinvalid;
        by apply id_ren_invalidblock.
      intros b1 Hvalid. erewrite restrPermMap_valid in Hvalid.
      exists b1;
        by apply id_ren_validblock.
      intros b1 b2 Hf.
      erewrite restrPermMap_valid.
      eapply Mem.store_valid_block_1; eauto.
      erewrite restrPermMap_valid.
      unfold id_ren in Hf.
      destruct (valid_block_dec m b1);
        by [simpl in Hf; inversion Hf; by subst | by exfalso].
      intros b1 b1' b2 Hf1 Hf1'.
      apply id_ren_correct in Hf1.
      apply id_ren_correct in Hf1';
        by subst.
      intros b1 b2 ofs0 Hf.
      do 2 rewrite restrPermMap_Cur.
      rewrite Hresi.
      apply id_ren_correct in Hf; subst;
        by eapply po_refl.
      constructor.
      intros b1 b2 ofs0 Hf.
      do 2 rewrite restrPermMap_Cur.
      rewrite Hresi.
      apply id_ren_correct in Hf;
        by subst.
      intros b1 b2 ofs0 Hf Hperm.
      assert (Hvalid: Mem.valid_block m b1)
        by (assert (Hdomain := id_ren_domain m);
             apply Hdomain;
             by rewrite Hf).
      apply id_ren_correct in Hf; subst.
      assert (Hstable: ~ Mem.perm (restrPermMap Hlt) b2 ofs0 Cur Writable).
      { clear - Hperm Hno_race Hlt.
        intros Hcontra.
        specialize (Hno_race b2 ofs0).
        unfold Mem.perm in *.
        assert (Heq1 := restrPermMap_Cur (Hcomp i pfi) b2 ofs0).
        assert (Heq2 := restrPermMap_Cur Hlt b2 ofs0).
        unfold permission_at in *.
        rewrite Heq1 in Hperm.
        rewrite Heq2 in Hcontra.
        clear Heq1 Heq2.
        destruct ((getThreadR pfi) # b2 ofs0) as [pl|],
                                                 (pmap # b2 ofs0) as [pi|];
          try (destruct pl); try (destruct pi); simpl in *;
          destruct Hno_race as [? Hdisjoint]; inversion Hdisjoint; subst;
          try (by inversion Hperm); try (by inversion Hcontra).
      }
      simpl.
      replace (Mem.mem_contents m)
      with (Mem.mem_contents (restrPermMap Hlt))
        by reflexivity.
      erewrite store_contents_other with (m' := m'); eauto.
      eapply memval_obs_eq_id; try apply id_ren_correct.
      simpl.
      specialize (Hmem_wd b2 Hvalid ofs0 _ (Logic.eq_refl _)).
      destruct (Maps.ZMap.get ofs0 (Mem.mem_contents m) # b2);
        auto.
      unfold mem_wd.val_valid in Hmem_wd.
      unfold valid_memval, valid_val.
      destruct v0; auto.
      apply ((id_ren_domain m) b0) in Hmem_wd.
      destruct (id_ren m b0);
        [eexists; reflexivity | by exfalso].
    }
    erewrite Mem.nextblock_store with
    (m1 := (restrPermMap Hlt)) (m2 := m');
      by eauto.
  Qed.

  Lemma strong_tsim_id_trans:
    forall (tp1 tp1' tp2 : thread_pool) (m1 m1' m2 : mem)
      (f fid: memren) (i : tid)
      (pf1 : containsThread tp1 i)
      (pf1' : containsThread tp1' i)
      (pf2 : containsThread tp2 i)
      (Hcomp1 : mem_compatible tp1 m1)
      (Hcomp1' : mem_compatible tp1' m1')
      (Hcomp2 : mem_compatible tp2 m2)
      (Hvalid: forall b, Mem.valid_block m1 b <-> Mem.valid_block m1' b)
      (Htsim_id: strong_tsim (id_ren m1) pf1 pf1' Hcomp1 Hcomp1')
      (Htsim: strong_tsim f pf1 pf2 Hcomp1 Hcomp2),
      strong_tsim f pf1' pf2 Hcomp1' Hcomp2.
  Proof.
    intros.
    destruct Htsim_id as [code_eq_id obs_eq_id].
    destruct Htsim as [code_eq obs_eq].
    constructor.
    - destruct (getThreadC pf1'), (getThreadC pf1); simpl in *;
      try (by exfalso);
      destruct (getThreadC pf2); simpl in *; try (by exfalso);
      repeat match goal with
             | [H: _ /\ _ |- _] =>
               destruct H
             | [|- _ /\ _] => split
             | [|- core_inj _ _ _] =>
               eapply core_inj_trans; eauto
             | [|- val_obs _ _ _] =>
               eapply val_obs_trans; eauto
             | [|- forall _, _] =>
               intros b b' b'' Hf Hfid;
                 apply id_ren_correct in Hfid;
               subst
             end; subst; auto.
    - destruct obs_eq. destruct weak_obs_eq0.
      destruct obs_eq_id as [weak_obs_eq_id strong_obs_eq_id].
      destruct strong_obs_eq_id as [Hperm_id Hval_id].
      destruct weak_obs_eq_id.
      assert (Hinvalid: forall b, ~ Mem.valid_block m1 b <-> ~Mem.valid_block m1' b)
        by (intros b; specialize (Hvalid b); destruct Hvalid;
            split; intros; intro Hcontra; eauto).
      constructor.
      + constructor; eauto.
        intros b Hb.
        erewrite restrPermMap_valid in Hb.
        apply Hinvalid in Hb;
          by auto.
        intros b Hb.
        erewrite restrPermMap_valid in Hb.
        apply Hvalid in Hb;
          by auto.
        intros b1 b2 ofs Hf.
        specialize (perm_obs_weak0 _ _ ofs Hf).
        assert (Hb1: Mem.valid_block m1 b1)
          by (destruct (valid_block_dec m1 b1) as [? | Hcontra]; auto;
              apply domain_invalid0 in Hcontra;
                by congruence).
        apply domain_valid1 in Hb1.
        destruct Hb1 as [b2' Hfid].
        assert (b1 = b2')
          by (apply id_ren_correct in Hfid; by subst);
          subst b2'.
        specialize (Hperm_id _ _ ofs Hfid).
        rewrite Hperm_id;
          by auto.
      + destruct strong_obs_eq0.
        constructor.
        intros b1 b2 ofs Hf.
        specialize (perm_obs_strong0 _ _ ofs Hf).
        assert (Hb1: Mem.valid_block m1 b1)
          by (destruct (valid_block_dec m1 b1) as [? | Hcontra]; auto;
              apply domain_invalid0 in Hcontra;
                by congruence).
        apply domain_valid1 in Hb1.
        destruct Hb1 as [b2' Hfid].
        assert (b1 = b2')
          by (apply id_ren_correct in Hfid; by subst);
          subst b2'.
        specialize (Hperm_id _ _ ofs Hfid).
        rewrite Hperm_id;
          by auto.
      + intros b1 b2 ofs Hf Hperm.
        clear - Hperm Hf val_obs_eq0 domain_invalid0 Hval_id
                      Hperm_id domain_valid1.
        assert (Hb1: Mem.valid_block m1 b1)
          by (destruct (valid_block_dec m1 b1) as [? | Hcontra]; auto;
              apply domain_invalid0 in Hcontra;
                by congruence).
        apply domain_valid1 in Hb1.
        destruct Hb1 as [b2' Hfid].
        assert (b1 = b2')
          by (apply id_ren_correct in Hfid; by subst);
          subst b2'.
        specialize (Hperm_id _ _ ofs Hfid).
        unfold permission_at in Hperm_id.
        unfold Mem.perm in *.
        rewrite Hperm_id in Hperm.
        specialize (val_obs_eq0 _ _ _ Hf Hperm).
        specialize (Hval_id _ _ _ Hfid Hperm).
        eapply memval_obs_trans; eauto.
        intros b b' b'' Hf' Hfid'.
        apply id_ren_correct in Hfid';
          by subst.
  Qed.
   
  Lemma step_schedule:
    forall tpc tpc' mc mc' i U U'
      (Hstep: DryConc.MachStep the_ge (i :: U, [::], tpc) mc (U, [::], tpc') mc'),
      DryConc.MachStep the_ge (i :: U', [::], tpc) mc (U', [::], tpc') mc'.
  Proof.
    intros.
    inversion Hstep; subst; simpl in *;
    try match goal with
        | [H: ?X :: ?U = ?U |- _] =>
          exfalso; eapply list_cons_irrefl; eauto
        | [H: Some ?X = Some ?Y |- _] =>
          inversion H; subst; clear H
        end.
    econstructor 4; simpl; eauto.
    econstructor 5; simpl; eauto.
    econstructor 6; simpl; eauto.
    econstructor 7; simpl; eauto.
  Qed.
    
  Lemma safeC_invariant:
    forall tpc mc n
      (Hn: n > 0)
      (Hsafe: forall (U : Sch),
          @csafe the_ge (U,[::],tpc) mc n),
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
    forall tpc mc n
      (Hn: n > 0)
      (Hsafe: forall (U : Sch),
          csafe the_ge (U,[::],tpc) mc n),
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
    inversion HschedN; subst.
    unfold containsThread in Htid.
    exfalso.
    clear - Htid.
    destruct num_threads.
    simpl in *.
    apply Htid.
    ssromega.
  Qed.

  (*NOTE: violating the interface a bit, to create a super ugly proof*)
  Lemma contains_iff_num:
    forall tp tp'
      (Hcnt: forall i, containsThread tp i <-> containsThread tp' i),
      num_threads tp = num_threads tp'.
  Proof.
    intros.
    unfold containsThread in *.
    remember (num_threads tp).
    remember (num_threads tp').
    destruct p, p0; simpl in *.
    assert (n = n0).
    clear - Hcnt.
    generalize dependent n0.
    induction n; intros.
    destruct n0; auto.
    destruct (Hcnt 0).
    exfalso.
    specialize (H0 ltac:(ssromega));
      by ssromega.
    destruct n0.
    exfalso.
    destruct (Hcnt 0).
    specialize (H ltac:(ssromega));
      by ssromega.
    erewrite IHn; eauto.
    intros; split; intro H.
    assert (i.+1 < n.+1) by ssromega.
    specialize (fst (Hcnt (i.+1)) H0).
    intros.
    clear -H1;
      by ssromega.
    assert (i.+1 < n0.+1) by ssromega.
    specialize (snd (Hcnt (i.+1)) H0).
    intros.
    clear -H1;
      by ssromega.
    subst.
      by erewrite proof_irr with (a1 := N_pos) (a2 := N_pos0).
  Qed.
    
  
  Lemma invariant_add:
    forall tp i (cnti: containsThread tp i) c pmap1 pmap2 vf arg
      (Hinv: invariant
               (addThread
                  (updThread cnti c pmap1)
                  vf arg pmap2)),
      invariant (updThread cnti c pmap1).
  Proof.
    intros.
    constructor.
    - intros k j cntk cntj Hneq.
      assert (cntk' := cntAdd vf arg pmap2 cntk).
      assert (cntj' := cntAdd vf arg pmap2 cntj).
      pose proof ((no_race Hinv) _ _ cntk' cntj' Hneq).
      erewrite @gsoAddRes with (cntj := cntk) in H; eauto.
      erewrite @gsoAddRes with (cntj := cntj) in H; eauto.
    - intros j cntj.
      assert (cntj' := cntAdd vf arg pmap2 cntj).
      pose proof ((lock_set_threads Hinv) _ cntj').
      rewrite gsoAddLock in H.
      erewrite @gsoAddRes with (cntj := cntj) in H; eauto.
    - intros l rmap j cntj Hres.
      assert (cntj' := cntAdd vf arg pmap2 cntj).
      erewrite <- gsoAddLPool
      with (vf := vf) (arg := arg) (p := pmap2) in Hres.
      
      pose proof ((lock_res_threads Hinv) _ _ _ cntj' Hres).
      erewrite @gsoAddRes with (cntj := cntj) in H; eauto.
    - intros l rmap Hres.
      erewrite <- gsoAddLPool
      with (vf := vf) (arg := arg) (p := pmap2) in Hres.
      erewrite <- gsoAddLock with (vf := vf) (arg := arg) (p := pmap2);
        by pose proof ((lock_res_set Hinv) _ _ Hres).
    - (* lr_valid *)
      intros b0 ofs0.
      pose proof (lockRes_valid Hinv).
      specialize (H b0 ofs0).
      rewrite gsoAddLPool in H. auto.
  Qed.
  
  Lemma invariant_project_spawn:
    forall (tpc tpf : thread_pool) (mc mf : mem) f 
      (i : tid) (pff : containsThread tpf i) (pfc : containsThread tpc i)
      (HmemCompC : mem_compatible tpc mc)
      (HmemCompF : mem_compatible tpf mf)
      (virtue1 virtue2 : delta_map) c cf vf vff arg arg'
      (HinvF: invariant tpf)
      (HinvC': invariant
                 (addThread
                    (updThread pfc c
                               (computeMap (getThreadR pfc) virtue1)) vf arg
                    (computeMap empty_map virtue2)))
      (HsimWeak: forall (tid : tid) (pfc0 : containsThread tpc tid)
                   (pff0 : containsThread tpf tid),
          weak_tsim f pfc0 pff0 HmemCompC HmemCompF)
      (Htsim: mem_obs_eq f (restrPermMap (HmemCompC i pfc))
                         (restrPermMap (HmemCompF i pff)))
      (HnumThreads: forall i, containsThread tpc i <-> containsThread tpf i)
      (HsimLP: strong_mem_obs_eq f
                                 (restrPermMap (compat_ls HmemCompC))
                                 (restrPermMap (compat_ls HmemCompF)))
      (Hlocks: forall (bl2 : block) (ofs : Z),
          lockRes tpf (bl2, ofs) ->
          exists bl1 : block, f bl1 = Some bl2)
      (HsimRes:
         forall (bl1 bl2 : block) (ofs : Z)
           (rmap1 rmap2 : dry_machine.LocksAndResources.lock_info),
           f bl1 = Some bl2 ->
           forall (Hl1 : lockRes tpc (bl1, ofs) = Some rmap1)
             (Hl2 : lockRes tpf (bl2, ofs) = Some rmap2),
             strong_mem_obs_eq f
                               (restrPermMap (compat_lp HmemCompC (bl1, ofs) Hl1))
                               (restrPermMap (compat_lp HmemCompF (bl2, ofs) Hl2)))
       (Hlock_if: forall (bl1 bl2 : block) (ofs : Z),
                  f bl1 = Some bl2 ->
                  lockRes tpc (bl1, ofs) <-> lockRes tpf (bl2, ofs)),
      invariant
        (addThread
           (updThread pff cf
                      (computeMap (getThreadR pff) (projectAngel f virtue1)))
           vff arg' (computeMap empty_map (projectAngel f virtue2))).
  Proof.
    intros.
    pose proof (injective (weak_obs_eq Htsim)) as Hinjective.
    constructor.
    { (* no race for coarse-grained state*)
      assert (Hno_raceC:= no_race HinvC').
      intros k j pffk' pffj' Hkj.
      assert (pfck': containsThread
                       (addThread
                          (updThread pfc c
                                     (computeMap (getThreadR pfc) virtue1)) vf
                          arg (computeMap empty_map virtue2)) k).
      { assert (H := cntAdd' _ _ _ pffk').
        destruct H as [[pffk Hneqj] | Hj].
        apply cntAdd; auto.
        apply cntUpdate; apply cntUpdate' in pffk;
        eapply HnumThreads; eauto.
        subst. simpl.
        unfold containsThread in *. simpl in *.
        erewrite <- contains_iff_num; eauto.
      }
      assert (pfcj': containsThread
                       (addThread
                          (updThread pfc c
                                     (computeMap (getThreadR pfc) virtue1)) vf
                          arg (computeMap empty_map virtue2)) j).
      { assert (H := cntAdd' _ _ _ pffj').
        destruct H as [[pffj Hneqj] | Hj].
        apply cntAdd; auto.
        apply cntUpdate; apply cntUpdate' in pffj;
        eapply HnumThreads; eauto.
        subst. simpl.
        unfold containsThread in *. simpl in *.
        erewrite <- contains_iff_num; eauto.
      }
      assert (H := cntAdd' _ _ _ pffk').
      destruct H as [[pffk Hneqk] | Hk].
      - erewrite gsoAddRes with (cntj := pffk); eauto.
        assert (H := cntAdd' _ _ _ pffj').
        destruct H as [[pffj Hneqj] | Hj].
        + erewrite gsoAddRes with (cntj' := pffj') (cntj := pffj); eauto.
          specialize (no_race HinvF).
          intros H_noraceF.
          destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik;
            first by (subst;
                       eapply disjoint_angel_project with (c := c);
                       eauto;
                       eapply invariant_add; eauto).
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij;
            first by (apply permMapsDisjoint_comm; subst;
                      eapply disjoint_angel_project; eauto;
                      eapply invariant_add; eauto).
          rewrite gsoThreadRes; auto.
          rewrite gsoThreadRes; auto.
        + (*case j is the new thread *)
          assert (pfck: containsThread
                          (updThread pfc c (computeMap
                                              (getThreadR pfc) virtue1)) k)
            by (apply cntUpdate; apply cntUpdate' in pffk;
                eapply HnumThreads; eauto).
          subst j.
          erewrite gssAddRes; eauto.
          specialize (Hno_raceC _ _ pfck' pfcj' Hneqk).
          erewrite gssAddRes with (cnt' := pfcj') in Hno_raceC; eauto.        
          intros b2 ofs.
          erewrite gsoAddRes with (cntj' := pfck') (cntj := pfck)
            in Hno_raceC; eauto.
          destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik; subst.
          * rewrite gssThreadRes.
            rewrite gssThreadRes in Hno_raceC.
            assert (Hb2: (exists b1, f b1 = Some b2) \/
                         ~ (exists b1, f b1 = Some b2))
              by eapply em.
            destruct Hb2 as [[b1 Hf] | Hunmapped].
            erewrite computeMap_projection_3; eauto.
            erewrite computeMap_projection_1;
              by eauto.
            erewrite computeMap_projection_2; eauto.
            erewrite computeMap_projection_2; eauto.
            rewrite perm_union_comm.
            rewrite empty_map_spec.
            eapply not_racy_union;
              by constructor.
          * rewrite gsoThreadRes in Hno_raceC; auto.
            rewrite gsoThreadRes; auto.
            assert (Hb2: (exists b1, f b1 = Some b2) \/
                         ~ (exists b1, f b1 = Some b2))
              by eapply em.
            destruct Hb2 as [[b1 Hf] | Hunmapped].
            erewrite computeMap_projection_3; eauto.
            pose proof (perm_obs_weak (HsimWeak _ pfck pffk)) as Hlt.
            specialize (Hno_raceC b1 ofs).
            rewrite perm_union_comm in Hno_raceC.
            rewrite perm_union_comm.
            specialize (Hlt _ _ ofs Hf).
            do 2 rewrite restrPermMap_Cur in Hlt.
            eapply perm_union_lower;
              by eauto.
            erewrite computeMap_projection_2; eauto.
            rewrite perm_union_comm.
            rewrite empty_map_spec.
            eapply not_racy_union;
              by eauto.
            unfold latestThread; symmetry; simpl;
            erewrite contains_iff_num; eauto.
      - (*case k is the new thread*)
        subst k.
        assert (H := cntAdd' _ _ _ pffj').
        destruct H as [[pffj Hneqj] | Hj];
          try (subst; by exfalso).
        assert (pfcj: containsThread
                        (updThread pfc c (computeMap
                                            (getThreadR pfc) virtue1)) j)
          by (apply cntUpdate; apply cntUpdate' in pffj;
              eapply HnumThreads; eauto).
        erewrite gssAddRes; eauto.
        specialize (Hno_raceC _ _ pfck' pfcj' ltac:(eauto)).
        erewrite gssAddRes with (cnt' := pfck') in Hno_raceC; eauto.
        intros b2 ofs.
        erewrite gsoAddRes with (cntj' := pfcj') (cntj := pfcj)
          in Hno_raceC; eauto.
        erewrite gsoAddRes with (cntj' := pffj') (cntj := pffj); eauto.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
        + rewrite gssThreadRes.
          rewrite gssThreadRes in Hno_raceC.
          assert (Hb2: (exists b1, f b1 = Some b2) \/
                       ~ (exists b1, f b1 = Some b2))
            by eapply em.
          destruct Hb2 as [[b1 Hf] | Hunmapped].
          erewrite computeMap_projection_3; eauto.
          erewrite computeMap_projection_1;
            by eauto.
          erewrite computeMap_projection_2; eauto.
          erewrite computeMap_projection_2; eauto.
          rewrite empty_map_spec.
          eapply not_racy_union;
            by constructor.
          * rewrite gsoThreadRes in Hno_raceC; auto.
            rewrite gsoThreadRes; auto.
            assert (Hb2: (exists b1, f b1 = Some b2) \/
                         ~ (exists b1, f b1 = Some b2))
              by eapply em.
            destruct Hb2 as [[b1 Hf] | Hunmapped].
            erewrite computeMap_projection_3; eauto.
            pose proof (perm_obs_weak (HsimWeak _ pfcj pffj)) as Hlt.
            specialize (Hno_raceC b1 ofs).
            specialize (Hlt _ _ ofs Hf).
            do 2 rewrite restrPermMap_Cur in Hlt.
            eapply perm_union_lower;
              by eauto.
            erewrite computeMap_projection_2; eauto.
            rewrite empty_map_spec.
            eapply not_racy_union;
              by eauto.
            unfold latestThread; symmetry; simpl;
            erewrite contains_iff_num; eauto.
    }
    { intros j pffj''.
      assert (pfcj'': containsThread
                        (addThread
                           (updThread pfc c
                                      (computeMap (getThreadR pfc) virtue1)) vf
                           arg (computeMap empty_map virtue2)) j).
      { assert (H := cntAdd' _ _ _ pffj'').
        destruct H as [[pffj Hneqj] | Hj].
        apply cntAdd; auto.
        apply cntUpdate; apply cntUpdate' in pffj;
        eapply HnumThreads; eauto.
        subst. simpl.
        unfold containsThread in *. simpl in *.
        erewrite <- contains_iff_num; eauto.
      }
      pose proof (lock_set_threads HinvC') as Hno_raceC.
      erewrite gsoAddLock.
      erewrite gsoThreadLock.
      erewrite gsoAddLock in Hno_raceC.
      erewrite gsoThreadLock in Hno_raceC.
      assert (H := cntAdd' _ _ _ pffj'').
      destruct H as [[pffj Hneqj] | Hj].
      - assert (pfcj: containsThread
                        (updThread pfc c (computeMap
                                            (getThreadR pfc) virtue1)) j)
          by (apply cntUpdate; apply cntUpdate' in pffj;
              eapply HnumThreads; eauto).
        erewrite gsoAddRes with (cntj := pffj); eauto.
        specialize (Hno_raceC _ pfcj'').
        erewrite gsoAddRes with (cntj' := pfcj'') (cntj := pfcj) in Hno_raceC;
          eauto.
        destruct HsimLP as [HpermLP _].
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hi; subst.
        + rewrite gssThreadRes. rewrite gssThreadRes in Hno_raceC.
          intros b2 ofs.
          assert (Hb2: (exists b1, f b1 = Some b2) \/
                       ~ (exists b1, f b1 = Some b2))
            by eapply em.
          destruct Hb2 as [[b1 Hf] | Hunmapped].
          erewrite computeMap_projection_1; eauto.
          specialize (HpermLP _ _ ofs Hf).
          do 2 rewrite restrPermMap_Cur in HpermLP.
          rewrite HpermLP;
            by auto.
          erewrite computeMap_projection_2; eauto.
          destruct HinvF as [_ HinvF _ _];
            eapply HinvF; eauto.
        + rewrite gsoThreadRes; auto.
          rewrite gsoThreadRes in Hno_raceC; auto.
          intros b2 ofs.
          destruct HinvF as [_ HinvF _ _].
          eapply HinvF.
      - (*case j is the new thread *)
        subst j.
        erewrite gssAddRes; eauto.
        specialize (Hno_raceC _ pfcj'').
        erewrite gssAddRes in Hno_raceC; eauto.
        destruct HsimLP as [HpermLP _].
        intros b2 ofs.
        assert (Hb2: (exists b1, f b1 = Some b2) \/
                     ~ (exists b1, f b1 = Some b2))
          by eapply em.
        destruct Hb2 as [[b1 Hf] | Hunmapped].
        erewrite computeMap_projection_3; eauto.
        specialize (HpermLP _ _ ofs Hf).
        do 2 rewrite restrPermMap_Cur in HpermLP.
        rewrite HpermLP;
          by eauto.
        erewrite computeMap_projection_2; eauto.
        rewrite empty_map_spec.
        rewrite perm_union_comm.
        eapply not_racy_union;
          by constructor.
        unfold latestThread. simpl.
        erewrite <- contains_iff_num; eauto.
    }
    { intros (bl2 & ofsl) rmap j pffj''.
      assert (pfcj'': containsThread
                        (addThread
                           (updThread pfc c
                                      (computeMap (getThreadR pfc) virtue1)) vf
                           arg (computeMap empty_map virtue2)) j).
      { assert (H := cntAdd' _ _ _ pffj'').
        destruct H as [[pffj Hneqj] | Hj].
        apply cntAdd; auto.
        apply cntUpdate; apply cntUpdate' in pffj;
        eapply HnumThreads; eauto.
        subst. simpl.
        unfold containsThread in *. simpl in *.
        erewrite <- contains_iff_num; eauto.
      }
      erewrite gsoAddLPool.
      erewrite gsoThreadLPool.
      intros Hres.
      specialize (Hlocks bl2 ofsl ltac:(rewrite Hres; auto)).
      destruct Hlocks as [bl1 Hfl1].
      destruct HsimLP as [HpermLP _].
      specialize (HpermLP _ _ ofsl Hfl1).
      do 2 rewrite restrPermMap_Cur in HpermLP.
      assert (HresC: exists rmap1, lockRes tpc (bl1, ofsl) = Some rmap1).
      { specialize (snd (Hlock_if _ _ ofsl Hfl1) ltac:(unfold isSome; rewrite Hres; auto)).
        intro H.
        destruct (lockRes tpc (bl1, ofsl)); try by exfalso.
        eexists; eauto.
      }
      destruct HresC as [rmap1 HresC].
      pose proof ((lock_res_threads HinvC') (bl1,ofsl) _ j pfcj'' HresC)
        as Hno_raceC.
      specialize (HsimRes _ _ _ _ _ Hfl1 HresC Hres).
      destruct HsimRes as [HpermRes _].
      intros b2 ofs. 
      assert (H := cntAdd' _ _ _ pffj'').
      destruct H as [[pffj Hneqj] | Hj].
      - assert (pfcj: containsThread
                        (updThread pfc c (computeMap
                                            (getThreadR pfc) virtue1)) j)
          by (apply cntUpdate; apply cntUpdate' in pffj;
              eapply HnumThreads; eauto).
        erewrite gsoAddRes with (cntj := pffj); eauto.
        erewrite gsoAddRes with (cntj' := pfcj'') (cntj := pfcj) in Hno_raceC;
          eauto.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hi; subst.
        + rewrite gssThreadRes. rewrite gssThreadRes in Hno_raceC.
          assert (Hb2: (exists b1, f b1 = Some b2) \/
                       ~ (exists b1, f b1 = Some b2))
            by eapply em.
          destruct Hb2 as [[b1 Hf] | Hunmapped].
          erewrite computeMap_projection_1; eauto.
          specialize (HpermRes _ _ ofs Hf).
          do 2 rewrite restrPermMap_Cur in HpermRes.
          rewrite HpermRes;
            by auto.
          erewrite computeMap_projection_2; eauto.
          destruct HinvF as [_ _ HinvF _];
            eapply HinvF; eauto.
        + rewrite gsoThreadRes; auto.
          rewrite gsoThreadRes in Hno_raceC; auto.
          destruct HinvF as [_ _ HinvF _].
          eapply HinvF; eauto.
      - (*case j is the new thread *)
        subst j.
        erewrite gssAddRes; eauto.
        erewrite gssAddRes in Hno_raceC; eauto.
        assert (Hb2: (exists b1, f b1 = Some b2) \/
                     ~ (exists b1, f b1 = Some b2))
          by eapply em.
        destruct Hb2 as [[b1 Hf] | Hunmapped].
        erewrite computeMap_projection_3; eauto.
        specialize (HpermRes _ _ ofs Hf).
        do 2 rewrite restrPermMap_Cur in HpermRes.
        rewrite HpermRes;
          by eauto.
        erewrite computeMap_projection_2; eauto.
        rewrite empty_map_spec.
        rewrite perm_union_comm.
        eapply not_racy_union;
          by constructor.
        unfold latestThread. simpl.
        erewrite <- contains_iff_num; eauto.
    }
    { rewrite gsoAddLock gsoThreadLock.
      intros.
      rewrite gsoAddLPool in H.
      rewrite gsoThreadLPool in H.
      destruct HinvF as [_ _ _ HinvF].
      eauto.
    }
    { intros b ofs.
      rewrite gsoAddLPool.
      rewrite gsoThreadLPool.
      pose proof (lockRes_valid HinvF).
      specialize (H b ofs). eauto.
    }
  Qed.    

  Lemma store_compatible:
    forall tpf mf pmap chunk b ofs v mf' (Hlt: permMapLt pmap (getMaxPerm mf))
      (Hcomp: mem_compatible tpf mf)
      (Hstore: Mem.store chunk (restrPermMap Hlt) b ofs v = Some mf'),
      mem_compatible tpf mf'.
  Proof.
    intros.
    inversion Hcomp.
    constructor.
    - intros. intros b' ofs'.
      apply mem_store_max with (b' := b') (ofs' := ofs') in Hstore.
      rewrite getMax_restr in Hstore.
      rewrite <- Hstore. eapply compat_th0.
    - intros l rmap Hres b' ofs'.
      apply mem_store_max with (b' := b') (ofs' := ofs') in Hstore.
      rewrite getMax_restr in Hstore.
      rewrite <- Hstore. eapply compat_lp0; eauto.
    - intros b' ofs'.
      apply mem_store_max with (b' := b') (ofs' := ofs') in Hstore.
      rewrite getMax_restr in Hstore.
      rewrite <- Hstore. eapply compat_ls0; eauto.
  Qed.
  
  Lemma mem_compatible_sync:
    forall tpf mf cf virtue1 virtue2 f bl1 bl2 ofsl i
      (pff: containsThread tpf i)
      (Hcanonical: isCanonical virtue2)
      (Hf: f bl1 = Some bl2)
      (HmaxF: max_inv mf)
      (HmemCompF: mem_compatible tpf mf)
      (Hcodomain_valid : forall b1 b2 : block,
          f b1 = Some b2 -> Mem.valid_block mf b2),
      mem_compatible
        (updLockSet
           (updThread pff cf
                      (computeMap (getThreadR pff)
                                  (projectAngel f virtue1)))
           (bl2, ofsl) (projectMap f virtue2)) mf.
  Proof.
    intros.
    constructor.
    { intros j pffj.
      rewrite gLockSetRes.
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
      - subst.
        rewrite gssThreadRes.
        intros b2 ofs.
        assert (Hb2: (exists b', f b' = Some b2) \/
                     ~ (exists b', f b' = Some b2))
          by eapply em.
        destruct Hb2 as [Hbm | Hbu].
        (*case b2 is mapped by f*)
        destruct Hbm as [b1 Hfb1].
        apply Hcodomain_valid in Hfb1.
        specialize (HmaxF _ ofs Hfb1).
        rewrite getMaxPerm_correct.
        rewrite HmaxF.
        simpl.
        destruct ((computeMap (getThreadR pff) (projectAngel f virtue1)) # b2 ofs);
          constructor.
        erewrite computeMap_projection_2 by eauto.
        eapply HmemCompF.
      - rewrite gsoThreadRes; auto.
        eapply HmemCompF.
    }
    { intros (bl', ofsl') rmap Hres.
      destruct (EqDec_address (bl2, ofsl) (bl', ofsl')).
      - inversion e; subst.
        rewrite gssLockRes in Hres. inversion Hres; subst.
        intros b2 ofs.
        assert (Hb2: (exists b', f b' = Some b2) \/
                     ~ (exists b', f b' = Some b2))
          by eapply em.
        destruct Hb2 as [Hbm | Hbu].
        (*case b2 is mapped by f*)
        destruct Hbm as [b1 Hfb1].
        apply Hcodomain_valid in Hfb1.
        specialize (HmaxF _ ofs Hfb1).
        rewrite getMaxPerm_correct.
        rewrite HmaxF.
        simpl.
        destruct ((projectMap f virtue2) # b2 ofs);
          constructor.
        erewrite projectMap_correct_2 by eauto.
        rewrite Hcanonical.
        destruct ((getMaxPerm mf) # b2 ofs); simpl; auto.
      - rewrite gsoLockRes in Hres; auto.
        rewrite gsoThreadLPool in Hres.
        eapply HmemCompF; eauto.
    }
    { rewrite <- lockSet_updLockSet.
      intros b2 ofs.
      assert (Hb2: (exists b', f b' = Some b2) \/
                   ~ (exists b', f b' = Some b2))
        by eapply em.
      destruct Hb2 as [Hbm | Hbu].
      (*case b2 is mapped by f*)
      destruct Hbm as [b1 Hfb1].
      apply Hcodomain_valid in Hfb1.
      specialize (HmaxF _ ofs Hfb1).
      rewrite getMaxPerm_correct.
      rewrite HmaxF.
      simpl.
      destruct ((lockSet (updLockSet tpf (bl2, ofsl) (projectMap f virtue2))) # b2
                                                                              ofs);
        constructor.
      destruct (Pos.eq_dec b2 bl2); subst.
      eapply Hcodomain_valid in Hf.
      rewrite getMaxPerm_correct.
      specialize (HmaxF _ ofs Hf).
      rewrite HmaxF. simpl.
      destruct ((lockSet (updLockSet tpf (bl2, ofsl) (projectMap f virtue2))) # bl2
                                                                              ofs);
        constructor.
      rewrite gsoLockSet_2; auto.
      eapply (compat_ls HmemCompF); eauto.
    }
  Qed.

  Lemma mem_compatible_spawn :
    forall (tpf : thread_pool) (mf : mem) (cf : ctl) 
      (virtue1 virtue2 : delta_map) (f : block -> option block)
      vf args (i : tid) (pff : containsThread tpf i)
      (Hmax_inv: max_inv mf)
      (HmemCompF: mem_compatible tpf mf)
      (Hcodomain: forall b1 b2 : block, f b1 = Some b2 -> Mem.valid_block mf b2),
      mem_compatible
        (addThread
           (updThread pff cf
                      (computeMap (getThreadR pff) (projectAngel f virtue1)))
           vf args (computeMap empty_map (projectAngel f virtue2))) mf.
  Proof.
    intros.
    constructor.
    { intros j pffj''.
      assert (pffj' := cntAdd' _ _ _ pffj'').
      destruct pffj' as [[pffj' Hneq] | Heq].
      - (*case it's an old thread *)
        erewrite gsoAddRes with (cntj := pffj') by eauto.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        + subst.
          rewrite gssThreadRes.
          intros b2 ofs.
          assert (Hb2: (exists b', f b' = Some b2) \/
                       ~ (exists b', f b' = Some b2))
            by eapply em.
          destruct Hb2 as [Hbm | Hbu].
          (*case b2 is mapped by f*)
          destruct Hbm as [b1 Hfb1].
          apply Hcodomain in Hfb1.
          specialize (Hmax_inv _ ofs Hfb1).
          rewrite getMaxPerm_correct.
          rewrite Hmax_inv.
          simpl.
          destruct ((computeMap (getThreadR pff) (projectAngel f virtue1)) # b2 ofs);
            constructor.
          erewrite computeMap_projection_2 by eauto.
          eapply HmemCompF.
        + rewrite gsoThreadRes; auto.
          eapply HmemCompF.
      - (*case it's the new thread*)
        subst.
        erewrite gssAddRes; eauto.
        intros b2 ofs.
        assert (Hb2: (exists b', f b' = Some b2) \/
                     ~ (exists b', f b' = Some b2))
          by eapply em.
        destruct Hb2 as [Hbm | Hbu].
        (*case b2 is mapped by f*)
        destruct Hbm as [b1 Hfb1].
        apply Hcodomain in Hfb1.
        specialize (Hmax_inv _ ofs Hfb1).
        rewrite getMaxPerm_correct.
        rewrite Hmax_inv.
        simpl.
        destruct ((computeMap empty_map (projectAngel f virtue2)) # b2 ofs);
          constructor.
        erewrite computeMap_projection_2 by eauto.
        rewrite empty_map_spec.
        destruct ((getMaxPerm mf) # b2 ofs); simpl; auto.
    }
    { intros (bl', ofsl') rmap Hres.
      rewrite gsoAddLPool in Hres.
      rewrite gsoThreadLPool in Hres.
      eapply HmemCompF; eauto.
    }
    { rewrite gsoAddLock.
      rewrite gsoThreadLock.
      eapply (compat_ls HmemCompF).
    }
  Qed.
  
  Lemma sim_external: sim_external_def.
  Proof.
    unfold sim_external_def.
    intros.
    inversion Hsim as
        [HnumThreads HmemCompC HmemCompF HsafeC HsimWeak HfpSep HsimStrong
                     [HsimLocks HLocksInv] [HsimRes Hlock_if] HinvF HmaxF
                     Hmemc_wd Htpc_wd Hge_wd [Hge_incr Hfg] Hxs].
    (* Thread i is in the coarse-grained machine*)
    assert (pfc: containsThread tpc i)
      by (eapply HnumThreads; eauto).
    (* Since thread i is synced, the coarse machine doesn't need to take any steps*)
    apply @not_in_filter with (xs := xs) in Hsynced.
    destruct (HsimStrong i pfc pff)
      as [tpc' [mc' [Hincr [Hsyncf [Hexec [Htsim [Hownedi Hownedi_ls]]]]]]];
      clear HsimStrong.
    (* Hence tpc = tpc' and mc = mc' *)
    rewrite Hsynced in Hexec.
    assert (Heq: tpc = tpc' /\ mc = mc')
      by (clear -Hexec; inversion Hexec; subst; auto; simpl in HschedN; discriminate).
    destruct Heq; subst tpc' mc'; clear Hexec.
    (* And also f won't change, i.e. f = fi *)
    specialize (Hsyncf Hsynced); subst f.
    clear Hincr.
    (* We know there is a strong simulation for thread i*)
    specialize (Htsim pfc HmemCompC).
    (* Since the fine grained machine is at an external step so is
      the coarse-grained machine*)
    assert (HexternalC: pfc @ E)
      by (by erewrite (stepType_inj _ _ _ (code_eq Htsim))).
    (* It's safe to step the coarse grained machine for one more step on i*)
    specialize (HsafeC (buildSched [:: i])).
    destruct (csafe_pop_step pfc ltac:(eauto) HsafeC) as
        (tpc' & mc' & Hstep' & Hsafe').
    (*the invariant for tpc is implied by safety*)
    assert (Hsafe := safeCoarse Hsim).
    assert (HinvC: invariant tpc)
      by (eapply safeC_invariant with (n := (fuelF.+2 + size xs)); eauto).
    (* An external step pops the schedule and executes a concurrent call *)
    assert (HconcC: exists ev, syncStep the_ge pfc HmemCompC tpc' mc' ev)
      by (eapply external_step_inverse; eauto).
    destruct HconcC as [ev HconcC].
    (*TODO: we must deduce that fact from safety of coarse-grained machine*)
    assert (HmemCompC': mem_compatible tpc' mc').
      by (eapply safeC_compatible with (n := (fuelF.+1 + size xs)); eauto).
    (*domain of f*)
    assert (Hdomain_f: domain_memren (fp i pfc) mc)
      by (apply (weak_obs_eq_domain_ren (HsimWeak _ pfc pff))).
    pose proof (injective (HsimWeak _ pfc pff)) as Hinjective.
    (* Useful facts about the global env*)
    assert (Hge_incr_id: ren_incr fg (id_ren mc))
      by (clear - Hge_incr Hfg Hdomain_f;
           eapply incr_domain_id; eauto).

    exists tpc', mc'.
    (* We proceed by case analysis on the concurrent call *)
    inversion HconcC; try subst tp' tp''; try subst m'.
    { (* Lock Acquire *)
        (* In order to construct the new memory we have to perform the
        load and store of the lock, after setting the correct permissions*)
        (*We prove that b is valid in m1 (and mc)*)
        assert (Hvalidb: Mem.valid_block m1 b)
          by (eapply load_valid_block; eauto).
        rewrite <- Hrestrict_pmap in Hvalidb.
        (*  and compute the corresponding block in mf *)
        destruct ((domain_valid (weak_obs_eq (obs_eq Htsim))) _ Hvalidb)
          as [b2 Hfb].
        assert (Hvalidb2 := (codomain_valid (weak_obs_eq (obs_eq Htsim))) _ _ Hfb).
        erewrite restrPermMap_valid in Hvalidb2.
        remember (restrPermMap (compat_ls HmemCompF)) as mf1 eqn:Hrestrict_pmapF.
        subst m1.
        (* and prove that loading from that block in mf gives us the
        same value as in mc, i.e. unlocked*)
        assert (HloadF: Mem.load Mint32 mf1 b2 (Int.intval ofs) = Some (Vint Int.one)).
        { destruct (load_val_obs _ _ _ Hload Hfb Hinjective HsimLocks)
            as [v2 [Hloadf Hobs_eq]].
          inversion Hobs_eq; subst.
            by auto.
        }
        assert (Hval_obs: val_obs (fp i pfc) (Vint Int.zero) (Vint Int.zero))
          by constructor.
        (* and then storing gives us related memories*)
        assert (Hlocks_obs_eq: mem_obs_eq (fp i pfc)
                                          (restrPermMap (compat_ls HmemCompC)) mf1)
          by (subst mf1;
               destruct Htsim as [_ [? ?]];
               eapply mem_obs_eq_of_weak_strong; eauto).      
        assert (HstoreF := store_val_obs _ _ _ Hstore Hfb Hval_obs Hlocks_obs_eq).
        destruct HstoreF as [mf' [HstoreF HsimLocks']].
        (* We have that the code of the fine grained execution
        is related to the one of the coarse-grained*)
        assert (Hcore_inj:= code_eq Htsim).
        rewrite Hcode in Hcore_inj.
        simpl in Hcore_inj.
        destruct (getThreadC pff) as [? | cf |? | ?] eqn:HcodeF;
          try by exfalso.
        (* And now we can prove that cf is also at external *)
        assert (Hat_external_spec := core_inj_ext Hcore_inj).
        rewrite Hat_external in Hat_external_spec.
        destruct (at_external SEM.Sem cf) as [[[? ?] vsf]|] eqn:Hat_externalF;
          try by exfalso.
        (* and moreover that it's the same external and their
        arguments are related by the injection*)
        destruct Hat_external_spec as [? [? Harg_obs]]; subst.
        inversion Harg_obs as [|? ? ? ? Hptr_obs Hl]; subst.
        inversion Hl; subst.
        inversion Hptr_obs as [| | | |b1 bf ofs0 Hf|];
          subst b1 ofs0 v'.
        assert (bf = b2)
          by (rewrite Hf in Hfb; by inversion Hfb);
          subst bf.
        (* To compute the new fine grained state, we apply the
        renaming to the resources the angel provided us*)
        remember (projectAngel (fp i pfc) virtueThread) as virtueF eqn:HvirtueF.
        remember (updThread pff (Kresume cf Vundef)
                            (computeMap (getThreadR pff) virtueF))
          as tpf' eqn:Htpf'.
        (* We prove that the mapped block is a lock*)
        assert (HresF: lockRes tpf (b2, Int.intval ofs))
          by (eapply Hlock_if; eauto; rewrite HisLock; auto).
        destruct (lockRes tpf (b2, Int.intval ofs)) as [pmapF|] eqn:HisLockF;
          try by exfalso.
        (* and then prove that the projected angel satisfies the angelSpec*)
        assert (HangelF: acqAngelSpec pmapF (getThreadR pff) (projectMap (fp i pfc)
                                                                      empty_map)
                                      (computeMap (getThreadR pff) virtueF))
          by (subst; eapply acqAngelSpec_project; eauto).
        (* and finally build the final fine-grained state*)
        remember (updLockSet tpf' (b2, Int.intval ofs)
                             (projectMap (fp i pfc) empty_map)) as tpf'' eqn:Htpf'';
          symmetry in Htpf''.
        exists tpf'', mf', (fp i pfc), fp,
        (tr ++ [:: (external i (acquire (b2, Int.intval ofs)
                                       (Some (projectMap (fp i pfc) empty_map,
                                        virtueF))))]).
        split.
        (* proof that the fine grained machine can step*)
        intros U.
        assert (HsyncStepF: syncStep the_ge pff HmemCompF tpf'' mf'
                                     (acquire (b2, Int.intval ofs)
                                              (Some (projectMap (fp i pfc) empty_map,
                                                     virtueF))))
          by (eapply step_acquire with (b:=b2); eauto).
        econstructor; simpl;
          by eauto.
        (* Proof that the new coarse and fine state are in simulation*)
        assert (HinvC':
                  invariant (updLockSet
                               (updThread pfc (Kresume c Vundef)
                                          (computeMap (getThreadR pfc) virtueThread)) 
                               (b, Int.intval ofs) empty_map))
          by  (eapply safeC_invariant with (n := fuelF.+1 + size xs); eauto).
        assert (HmaxF': max_inv mf')
          by (eapply max_inv_store; eauto).
        (*TODO: lemma : max_inv implies compatible*)
        assert (HmemCompF'' : mem_compatible tpf'' mf').
        { subst.
          eapply store_compatible; eauto.
          eapply mem_compatible_sync; eauto.
          unfold isCanonical. reflexivity.
          eapply (codomain_valid (weak_obs_eq (obs_eq Htsim))).
        }
        subst.
        eapply Build_sim with (mem_compc := HmemCompC') (mem_compf := HmemCompF'').
        - (* containsThread *)
          clear - HnumThreads.
          intros j.
          split; intros cntj;
          eapply cntUpdateL;
          eapply cntUpdate;
          apply cntUpdateL' in cntj;
          apply cntUpdate' in cntj;
            by eapply HnumThreads.
        - (*safety of coarse machine*)
            by assumption.
        - (* weak simulation between the two machines*)
          (*TODO: factor this out as a lemma*)
          intros j pfcj' pffj'.
          assert (pfcj: containsThread tpc j)
            by auto.
          assert (pffj: containsThread tpf j)
            by auto.
          specialize (HsimWeak _ pfcj pffj).
          assert (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b)
            by (
                intros;
                erewrite <- restrPermMap_valid with (Hlt := compat_ls HmemCompC);
                split;
                [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
                eauto).
          assert (Hvb': forall b, ~ Mem.valid_block mc b <-> ~ Mem.valid_block mc' b)
            by (intros; split; intros Hinvalid Hcontra;
                  by apply Hvb in Hcontra).
          assert (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b)
            by (
                intros;
                erewrite <- restrPermMap_valid with (Hlt := compat_ls HmemCompF);
                split;
                [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
                eauto).
          clear - Hvb Hvb' HvbF HstoreF Hstore HsimWeak Hsim.
          destruct HsimWeak.
          constructor; intros;
          repeat
            (match goal with
             | [H: context[Mem.valid_block (restrPermMap _) _] |- _] =>
               erewrite restrPermMap_valid in H
             | [H: ~ Mem.valid_block _ _ |- _] =>
               apply Hvb' in H; clear Hvb'
             | [H: Mem.valid_block _ _ |- _] =>
               apply Hvb in H; clear Hvb
             | [|- Mem.valid_block (restrPermMap _) _] =>
               erewrite restrPermMap_valid
             | [|- Mem.valid_block _ _] =>
               eapply HvbF; clear HvbF
             end); eauto;
          try by specialize (codomain_valid0 _ _ H).
          { (* Permissions on coarse machine are higher than permissions on fine*)
            destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
            - (*this is the case where the angel has replaced some permissions*)
              subst j. 
              do 2 rewrite restrPermMap_Cur.
              do 2 rewrite gLockSetRes.
              do 2 rewrite gssThreadRes.
              (*by case analysis on whether the angel changed the
              permission at this address*)
              assert (Hproject: Maps.PTree.get b0 (projectAngel (fp i pfc) virtueThread) =
                                Maps.PTree.get b1 virtueThread)
                by (symmetry; eapply projectAngel_correct; eauto).
              pf_cleanup.
              specialize (perm_obs_weak0 _ _ ofs0 Hrenaming).
              destruct (Maps.PTree.get b1 virtueThread) as [df|] eqn:Hdelta.
              + destruct (df ofs0) as [pnew |] eqn:Hdf.
                rewrite (computeMap_1 _ _ _ _ Hdelta Hdf).
                rewrite (computeMap_1 _ _ _ _ Hproject Hdf);
                  by eapply po_refl.
                rewrite (computeMap_2 _ _ _ _ Hdelta Hdf).
                rewrite (computeMap_2 _ _ _ _ Hproject Hdf);
                  by do 2 rewrite restrPermMap_Cur in perm_obs_weak0.
              + rewrite (computeMap_3 _ _ _ _ Hdelta).
                rewrite (computeMap_3 _ _ _ _ Hproject);
                  by do 2 rewrite restrPermMap_Cur in perm_obs_weak0.
            - do 2 erewrite restrPermMap_Cur.
              do 2 rewrite gLockSetRes.
              erewrite gsoThreadRes with (cntj := pfcj); eauto.
              erewrite gsoThreadRes with (cntj := pffj); eauto.
              specialize (perm_obs_weak0 _ _ ofs0 Hrenaming).
              do 2 erewrite restrPermMap_Cur in perm_obs_weak0;
                by assumption. }
          (* Proof of seperation of injections *)
          intros k j cntk' cntj' Hkj b0 b0' b3 b3' Hf0 Hf0' Hfk' Hfj'.
          assert (cntk: containsThread tpc k)
            by auto.
          assert (cntj: containsThread tpc j)
            by auto.
          erewrite cnt_irr with (cnt1 := cntk') (cnt2 := cntk) in Hfk'.
          erewrite cnt_irr with (cnt1 := cntj') (cnt2 := cntj) in Hfj'.
          eapply (HfpSep _ _ cntk cntj Hkj b0 b0');
            by eauto.
          (* Proof of strong simulations after executing some thread*)
          intros.
          destruct (tid == i) eqn:Htid; move/eqP:Htid=>Htid; subst.
          { (*case of strong simulation for the thread that took the external*)
            exists (updLockSet
                 (updThread pfc (Kresume c Vundef)
                            (computeMap (getThreadR pfc) virtueThread)) 
                 (b, Int.intval ofs) empty_map), mc'.
            assert (pfc0 = pfc)
              by (eapply cnt_irr; eauto); subst pfc0.
            rewrite Hsynced.
            repeat (split; (auto || constructor)).
            split; first by apply ren_incr_refl.
            split; first by auto.
            split; first by constructor.
            split.
            intros.
            constructor.
            do 2 rewrite gLockSetCode.
            do 2 rewrite gssThreadCode;
              by (split; [assumption | constructor]).
            destruct Htsim;
               by (eapply gss_mem_obs_eq_lock; eauto).
            repeat split;
              by congruence.
          }
          { (*strong simulation for another thread*)
            assert (Hstrong_sim := simStrong Hsim).
            assert (pfcj: containsThread tpc tid)
              by (eapply cntUpdateL' in pfc0;
                   eapply cntUpdate' in pfc0;
                   eauto).
            assert (pffj: containsThread tpf tid)
              by (eapply cntUpdateL' in pff0;
                   eapply cntUpdate' in pff0;
                   eauto).
            specialize (Hstrong_sim _ pfcj pffj).
            destruct Hstrong_sim
              as (tpcj & mcj & Hincrj & Hsyncedj & Hexecj & Htsimj
                  & Hownedj & Hownedj_ls & Hownedj_lp).
            (* first we prove that i is a valid thread after executing thread j*)
            assert (pfcij:= containsThread_internal_execution Hexecj pfc).

            (*Proof Sketch: Basically the proof we want is that
            changing some non-observable part of the state/memory
            should not affect the execution of thread j. To avoid
            giving yet another definition of equivalence of the
            observable state we re-use our strong injections. Steps:
            
            1. The original state <tpc,mc> will strongly inject with
            the id injection in the state <tpc', mc'> where we have
            updated the value of the lock and the resource maps
            according to the angel.

            2. Hence if <tpc,mc> takes internal steps to get to <tpcj,
            mcj> so will <tpc',mc'> to go to a new state
            <tpcj',mcj'>. Moreover <tpcj,mcj> will inject to
            <tpcj',mcj'> with the id injection. We had to strengthen
            our lemmas and corestep_obs_eq to obtain that last part.

            3. We use [strong_tsim_id_trans] to get that <tpcj',mcj'>
               will strongly inject in <tpf,mf> with the same
               injection as <tpcj,mcj>.

            4. Finally we prove that changing the state/memory
            in (TODO: add lemma name) non-observable parts retains the
            [strong_tsim] relation. *)

            (* Step 1*)
            assert (pfcjj: containsThread tpcj tid)
              by (eapply containsThread_internal_execution; eauto).
            assert (Hcompj: mem_compatible tpcj mcj)
              by (eapply internal_execution_compatible with (tp := tpc); eauto).
            specialize (Htsimj pfcjj Hcompj).
            (* We prove that thread tid on the original state injects
            in thread tid after updating the lockpool and storing the
            lock value*)
            assert (Htsimj_id:
                      (strong_tsim (id_ren mc) pfcj pfc0 HmemCompC HmemCompC') /\
                      (Mem.nextblock mc = Mem.nextblock mc')).
            { eapply strong_tsim_store_id; eauto.
              erewrite gLockSetRes.
              rewrite gsoThreadRes; eauto.
              erewrite gLockSetCode.
              rewrite gsoThreadCode; eauto.
              destruct HinvC.
              apply permMapsDisjoint_comm.
              eapply lock_set_threads0; eauto.
              assert (domain_memren (id_ren mc) mc)
                by (apply id_ren_domain).
              assert (domain_memren (fp i pfc) mc)
                by (apply (mem_obs_eq_domain_ren (obs_eq Htsim))).
              eapply tp_wd_domain;
                by eauto.
            }
            destruct Htsimj_id as [Htsimj_id Hnextblock].
            
            (* Step 2.*)
            assert (H := strong_tsim_execution _ HinvC' Hfg Hge_wd Hge_incr_id
                                               Htsimj_id Hexecj).
            destruct H as
                (tp2' & m2' & f' & Hexecj'& Hincrj' & Hsepj'
                 & Hnextblock' & Hinvj' & Htsimj' & Hid').
            destruct Htsimj' as (pf2j & pf2j' & Hcomp2 & Hcomp2' & Htsimj').
            specialize (Hid' Hnextblock (id_ren_correct mc)).
            assert (f' = id_ren mcj)
              by ( pose ((mem_obs_eq_domain_ren (obs_eq Htsimj')));
                   eapply is_id_ren; eauto); subst f'.
            exists tp2', m2'.
            erewrite cnt_irr with (cnt1 := pfc0) (cnt2 := pfcj).
            split; first by auto.
            split; first by auto.
            split; first by auto.
            split.
            (*strong thread simulation for j*)
            intros.
            pf_cleanup.
            (* Step 3, we use transitivity of strong_tsim *)
            assert (Htsim2j: strong_tsim (fp tid pfcj) pf2j' pffj Hcomp2'
                                         (mem_compf Hsim)).
            { eapply strong_tsim_id_trans
              with (f := fp tid pfcj) (Hcomp1 := Hcompj) (Hcomp1' := Hcomp2');
              eauto.
              destruct Hnextblock' as [[p [Hmcj Hm2']] | [Hmcj Hm2']];
              unfold Mem.valid_block;
              rewrite Hmcj Hm2' Hnextblock;
                by tauto.
            }
            (* Step 4*)
            destruct Htsim2j as [Hcodeq2j Hmem_obs_eq2j].
            constructor.
            rewrite gLockSetCode.
            rewrite gsoThreadCode;
              by auto.
            clear - Hmem_obs_eq2j HstoreF HinvF Htid.
            assert (HeqRes: getThreadR pff0 = getThreadR pffj)
              by (rewrite gLockSetRes;
                   rewrite gsoThreadRes; auto).
            assert (Hlt : permMapLt (getThreadR pff0)(getMaxPerm mf))
              by (rewrite HeqRes; destruct HmemCompF; eauto).
            eapply mem_obs_eq_storeF with (mf := mf) (Hlt :=  Hlt);
              eauto.
            destruct HinvF.
            specialize (lock_set_threads0 _ pffj).
            rewrite HeqRes;
              by eapply permMapsDisjoint_comm.
            erewrite restrPermMap_irr' with (Hlt := Hlt)
                                             (Hlt' := (mem_compf Hsim) tid pffj);
              by eauto.
            split.
            (*thread ownership*)
            intros k pff2k Hjk b1 b0 ofs0 Hfj Hfi.
            destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
            { subst k.
              rewrite gLockSetRes.
              rewrite gssThreadRes; auto.
              assert (Hunmapped: ~ (exists b, (fp i pfc) b = Some b0)).
              { intros Hcontra.
                destruct Hcontra as [b3 Hcontra].
                assert (Hfj' := Hincrj _ _ Hcontra).
                assert (Heq := injective (weak_obs_eq (obs_eq Htsimj)) _ _ Hfj Hfj');
                  subst b3.
                  by congruence.
              }
              erewrite computeMap_projection_2;
                by eauto.
            }
            { rewrite gLockSetRes.
              rewrite gsoThreadRes; auto.
              eapply Hownedj;
                by eauto.
            }
            split.
            (* lockset ownership*)
            intros b1 b0 ofs0 Hfj Hfi.
            assert (b2 <> b0).
            { intros ?; subst b0.
              assert (Hfbj := Hincrj _ _ Hfb).
              assert (Heq := injective (weak_obs_eq (obs_eq Htsimj)) _ _ Hfj Hfbj);
                subst b.
                by congruence.
            }
            replace ((lockSet
                        (updLockSet
                           (updThread pff (Kresume cf Vundef)
                                      (computeMap (getThreadR pff)
                                                  (projectAngel
                                                     (fp i pfc) virtueThread)))
                           (b2, Int.intval ofs)
                           (projectMap (fp i pfc) empty_map))) # b0 ofs0) with
            ((lockSet tpf) # b0 ofs0)
              by (erewrite gsoLockSet_2
                   by (intros Hcontra; inversion Hcontra; by subst);
                   eauto).
            eapply Hownedj_ls;
              by eauto.
            (* lockpool ownership*)
            intros bl ofsl rmap b1 b0 ofs0 Hfj Hfi Hres.
            destruct (EqDec_address (b2, Int.intval ofs) (bl, ofsl)) as [Heq | Hneq].
            (* case rmap is the resource map updated by the angel*)
            inversion Heq; subst.
            rewrite gssLockRes in Hres. inversion Hres.
            assert (~ exists b, fp i pfc b = Some b0).
            { intros Hcontra.
              destruct Hcontra as [b' Hfb'].
              assert (Hfb'' := Hincrj _ _ Hfb').
              assert (b' = b1)
                by (eapply (injective (weak_obs_eq (obs_eq Htsimj)));
                     eauto). subst b'.
                by congruence.
            }
            rewrite projectMap_correct_2; auto.
            (*case it is another resource map*)
            rewrite gsoLockRes in Hres; auto.
            rewrite gsoThreadLPool in Hres;
              by eauto.
          }
          (* Proof of [strong_mem_obs_eq] for lock set*)
          specialize (HsimWeak _ pfc pff).
          split.
          eapply sync_locks_mem_obs_eq with (tpc := tpc) (tpf := tpf)
                                                         (mc := mc) (mf := mf); eauto.
          erewrite lockSet_updLockSet. reflexivity.
          erewrite lockSet_updLockSet. reflexivity.
          intros bl2 ofs0 Hres.
          destruct (EqDec_address (bl2, ofs0) (b2, Int.intval ofs)) as [Heq | Hneq].
          inversion Heq; subst.
          eexists;
            by eauto.
          rewrite gsoLockRes in Hres; auto.
          rewrite gsoThreadLPool in Hres.
          eapply HLocksInv;
            by eauto.
          (* Proof of [strong_mem_obs_eq] for lock pool*)
          (* The lock case is easy because the resources are set to empty*)
          split.
          { intros bl1 bl2 ofs0 rmap1 rmap2 Hfi Hres1 Hres2.
            destruct (EqDec_address (b, Int.intval ofs) (bl1, ofs0)) as [Heq | Hneq].
            { (*case it is the acquired lock *)
              inversion Heq; subst.
              assert (bl2 = b2)
                by (rewrite Hfi in Hfb; by inversion Hfb).
              subst bl2.
              constructor.
              intros b1 b0 ofs0 Hf1.
              do 2 rewrite restrPermMap_Cur.
              rewrite gssLockRes in Hres1.
              rewrite gssLockRes in Hres2.
              inversion Hres1; inversion Hres2.
              unfold Maps.PMap.get.
              do 2 rewrite Maps.PTree.gempty;
                by reflexivity.
              intros b1 b0 ofs0 Hf1 Hperm.
              assert (H:= restrPermMap_Cur (compat_lp HmemCompC' (bl1, Int.intval ofs)
                                                      Hres1) b1 ofs0).
              unfold permission_at in H.
              unfold Mem.perm in Hperm.
              rewrite H in Hperm.
              clear H.
              exfalso.
              rewrite gssLockRes in Hres1.
              inversion Hres1; subst.
              unfold Maps.PMap.get in Hperm.
              rewrite Maps.PTree.gempty in Hperm.
              simpl in Hperm;
                by auto.
            }
            { (*case it's another lock*)
              assert ((b2, Int.intval ofs) <> (bl2, ofs0)).
              { clear - Hneq Hfi Hf Hfb Htsim.
                intros Hcontra; inversion Hcontra; subst.
                assert (b = bl1)
                  by (eapply (injective (weak_obs_eq (obs_eq Htsim))); eauto).
                subst;
                  by auto.
              }
              constructor.
              intros b1 b0 ofs1 Hf1.
              do 2 rewrite restrPermMap_Cur.
              rewrite gsoLockRes in Hres1; auto.
              rewrite gsoLockRes in Hres2; auto.
              rewrite gsoThreadLPool in Hres1.
              rewrite gsoThreadLPool in Hres2.
              specialize (HsimRes _ _ _ _ _ Hfi Hres1 Hres2).
              destruct HsimRes as [HpermRes HvalRes].
              specialize (HpermRes _ _ ofs1 Hf1);
                by do 2 rewrite restrPermMap_Cur in HpermRes.
              intros b1 b0 ofs1 Hf1 Hperm.
              unfold Mem.perm in *.
              assert (Hperm_eq:= restrPermMap_Cur
                                   (compat_lp HmemCompC' (bl1, ofs0) Hres1) b1 ofs1).
              unfold permission_at in Hperm_eq.
              rewrite Hperm_eq in Hperm.
              clear Hperm_eq.
              simpl.
              rewrite gsoLockRes in Hres1; auto.
              rewrite gsoLockRes in Hres2; auto.
              rewrite gsoThreadLPool in Hres1.
              rewrite gsoThreadLPool in Hres2.
              specialize (HsimRes _ _ _ _ _ Hfi Hres1 Hres2).
              destruct HsimRes as [HpermRes HvalRes].
              unfold Mem.perm in HvalRes.
              assert (Hperm_eq:= restrPermMap_Cur
                                   (compat_lp HmemCompC (bl1, ofs0) Hres1) b1 ofs1).
              unfold permission_at in Hperm_eq.
              specialize (HvalRes _ _ ofs1 Hf1).
              rewrite Hperm_eq in HvalRes.
              specialize (HvalRes Hperm). simpl in HvalRes.
              eapply gsoMem_obs_eq with (HltC := compat_ls HmemCompC)
                                          (HltF := compat_ls HmemCompF)
                                          (bl1 := b) (bl2 := b2); eauto.
              apply permMapsDisjoint_comm.
              eapply (lock_res_set HinvC); eauto.
            }
          }
          { intros bl1 bl2 ofs0 Hfl1.
            destruct (EqDec_address (b, Int.intval ofs) (bl1, ofs0)).
            - inversion e; subst.
              assert (b2 = bl2)
                by (rewrite Hf in Hfl1; inversion Hfl1; subst; auto).
              subst.
              do 2 rewrite gsslockResUpdLock.
              split;
              auto.
            - erewrite gsolockResUpdLock by auto.
              assert ((b2, Int.intval ofs) <> (bl2, ofs0)).
              { intros Hcontra.
                inversion Hcontra; subst.
                specialize (Hinjective _ _ _ Hfl1 Hfb).
                subst; auto.
              }
              erewrite gsolockResUpdLock by eauto.
              do 2 rewrite gsoThreadLPool.
              eauto.
          }
        - (* Proof of invariant preservation for fine-grained machine*)
          destruct Htsim.
          eapply invariant_project; by eauto.
        - (* Max permission invariant*)
            by assumption.
        - (* new memory is well-defined*)
          eapply store_wd_domain with
          (m := (restrPermMap (compat_ls HmemCompC))); eauto.
            by simpl.
        - (* new tpc well defined*)
          apply tp_wd_lockSet.
          intros j cntj'.
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          subst. rewrite gssThreadCode.
          specialize (Htpc_wd _ pfc).
          rewrite Hcode in Htpc_wd.
          simpl in *;
            by auto.
          assert (cntj := cntUpdate' _ _ _ cntj').
          erewrite @gsoThreadCode with (cntj := cntj) by assumption.
          specialize (Htpc_wd _ cntj).
            by auto.
        - (*ge well defined*)
          assumption.
        - (*ge spec*)
          split; assumption.
        - intros.
          apply cntUpdateL;
            apply cntUpdate;
              by eauto.
    }
    { (*lock release case *)
      (* In order to construct the new memory we have to perform the
        load and store of the lock, after setting the correct permissions*)
      (*We prove that b is valid in m1 (and mc)*)
      assert (Hvalidb: Mem.valid_block m1 b)
        by (eapply load_valid_block; eauto).
      rewrite <- Hrestrict_pmap in Hvalidb.
      (*  and compute the corresponding block in mf *)
      destruct ((domain_valid (weak_obs_eq (obs_eq Htsim))) _ Hvalidb)
        as [b2 Hfb].
      assert (Hvalidb2 := (codomain_valid (weak_obs_eq (obs_eq Htsim))) _ _ Hfb).
      erewrite restrPermMap_valid in Hvalidb2.
      remember (restrPermMap (compat_ls HmemCompF)) as mf1 eqn:Hrestrict_pmapF.
      subst m1.
      (* and prove that loading from that block in mf gives us the
        same value as in mc, i.e. unlocked*)
      assert (HloadF: Mem.load Mint32 mf1 b2 (Int.intval ofs) = Some (Vint Int.zero)).
      {
        destruct (load_val_obs _ _ _ Hload Hfb Hinjective HsimLocks)
          as [v2 [Hloadf Hobs_eq]].
        inversion Hobs_eq; subst.
          by auto.
      }
      assert (Hval_obs: val_obs (fp i pfc) (Vint Int.one) (Vint Int.one))
        by constructor.
      (* and then storing gives us related memories*)
      assert (Hlocks_obs_eq: mem_obs_eq (fp i pfc)
                                        (restrPermMap (compat_ls HmemCompC)) mf1)
        by (subst mf1;
             destruct Htsim as [_ [? ?]];
             eapply mem_obs_eq_of_weak_strong; eauto).
      assert (HstoreF := store_val_obs _ _ _ Hstore Hfb Hval_obs Hlocks_obs_eq).
      destruct HstoreF as [mf' [HstoreF HsimLocks']].
      (* We have that the code of the fine grained execution
        is related to the one of the coarse-grained*)
      assert (Hcore_inj:= code_eq Htsim).
      rewrite Hcode in Hcore_inj.
      simpl in Hcore_inj.
      destruct (getThreadC pff) as [? | cf |? | ?] eqn:HcodeF;
        try by exfalso.
      (* And now we can prove that cf is also at external *)
      assert (Hat_external_spec := core_inj_ext Hcore_inj).
      rewrite Hat_external in Hat_external_spec.
      destruct (at_external SEM.Sem cf) as [[[? ?] vsf]|] eqn:Hat_externalF;
        try by exfalso.
      (* and moreover that it's the same external and their
        arguments are related by the injection*)
      destruct Hat_external_spec as [? [? Harg_obs]]; subst.
      inversion Harg_obs as [|? ? ? ? Hptr_obs Hl]; subst.
      inversion Hl; subst.
      inversion Hptr_obs as [| | | |b1 bf ofs0 Hf|];
        subst b1 ofs0 v'.
      assert (bf = b2)
        by (rewrite Hf in Hfb; by inversion Hfb);
        subst bf.
      (* To compute the new fine grained state, we apply the
        renaming to the resources the angel provided us*)
      remember (projectAngel (fp i pfc) virtueThread) as virtueF eqn:HvirtueF.
      remember (updThread pff (Kresume cf Vundef)
                          (computeMap (getThreadR pff) virtueF))
        as tpf' eqn:Htpf'.
      (* And also apply the renaming to the resources that go to the lockpool*)
      remember (projectMap (fp i pfc) virtueLP) as virtueLPF eqn:HvirtueLPF.
      (* We prove that the mapped block is a lock*)
      assert (HisLockF: exists pmapF, lockRes tpf (b2, Int.intval ofs) = Some pmapF).
      { specialize (fst (Hlock_if _ _ (Int.intval ofs) Hfb) ltac:(unfold isSome; rewrite HisLock; auto)).
        intro H.
        destruct (lockRes tpf (b2, Int.intval ofs)); try by exfalso.
        eexists; eauto.
      }
      destruct HisLockF as [pmapF HisLockF].
      (* and then prove that the projected angel satisfies the angelSpec*)
      assert (HangelF: relAngelSpec (getThreadR pff) pmapF
                                 (computeMap (getThreadR pff) virtueF) virtueLPF).
      { subst. eapply relAngelSpec_project; eauto.
        destruct HmemCompC'.
        specialize (compat_lp0 (b, Int.intval ofs) virtueLP
                               ltac:(rewrite gssLockRes; eauto)).
        eapply canonical_lt; eauto.
      }
      (* and finally build the final fine-grained state*)
      remember (updLockSet tpf' (b2, Int.intval ofs) virtueLPF) as tpf'' eqn:Htpf'';
        symmetry in Htpf''.
      exists tpf'', mf', (fp i pfc), fp,
      (tr ++ [:: (external i (release (b2, Int.intval ofs)
                                     (Some (virtueLPF, virtueF))))]).
      split.
      (* proof that the fine grained machine can step*)
      intros U.
      assert (HsyncStepF: syncStep the_ge pff HmemCompF tpf'' mf'
                                   (release (b2, Int.intval ofs)
                                            (Some (virtueLPF, virtueF))))
        by (eapply step_release with (b:=b2); eauto).
      econstructor; simpl;
        by eauto.
      (* Proof that the new coarse and fine state are in simulation*)
      assert (HinvC':
                invariant (updLockSet
                             (updThread pfc (Kresume c Vundef)
                                        (computeMap (getThreadR pfc) virtueThread)) 
                             (b, Int.intval ofs) virtueLP))
        by  (eapply safeC_invariant with (n := fuelF.+1 + size xs); eauto).
      assert (HmaxF': max_inv mf')
        by (eapply max_inv_store; eauto).
      (*A useful result is that the virtueLP will be canonical*)
      assert (Hcanonical: isCanonical virtueLP).
      { clear - HmemCompC'.
        destruct HmemCompC'.
        
        specialize (compat_lp0 (b, Int.intval ofs) virtueLP
                               ltac:(erewrite gssLockRes; eauto)).
        eapply canonical_lt; eauto.
      }
      assert (HmemCompF'' : mem_compatible tpf'' mf').
      { subst.
        eapply store_compatible; eauto.
        eapply mem_compatible_sync; eauto.
        eapply (codomain_valid (weak_obs_eq (obs_eq Htsim))).
      }
      subst.
      eapply Build_sim with (mem_compc := HmemCompC') (mem_compf := HmemCompF'').
      - (* containsThread *)
        clear - HnumThreads.
        intros j.
        split; intros cntj;
        eapply cntUpdateL;
        eapply cntUpdate;
        apply cntUpdateL' in cntj;
        apply cntUpdate' in cntj;
          by eapply HnumThreads.
      - (*safety of coarse machine*)
          by assumption.
      - (* weak simulation between the two machines*)
        (*TODO: factor this out as a lemma*)
        intros j pfcj' pffj'.
        assert (pfcj: containsThread tpc j)
          by auto.
        assert (pffj: containsThread tpf j)
          by auto.
        specialize (HsimWeak _ pfcj pffj).
        assert (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b)
          by (
              intros;
              erewrite <- restrPermMap_valid with (Hlt := compat_ls HmemCompC);
              split;
              [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
              eauto).
        assert (Hvb': forall b, ~ Mem.valid_block mc b <-> ~ Mem.valid_block mc' b)
          by (intros; split; intros Hinvalid Hcontra;
                by apply Hvb in Hcontra).
        assert (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b)
          by (
              intros;
              erewrite <- restrPermMap_valid with (Hlt := compat_ls HmemCompF);
              split;
              [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
              eauto).
        clear - Hvb Hvb' HvbF HstoreF Hstore HsimWeak Hsim.
        destruct HsimWeak.
        constructor; intros;
        repeat
          (match goal with
           | [H: context[Mem.valid_block (restrPermMap _) _] |- _] =>
             erewrite restrPermMap_valid in H
           | [H: ~ Mem.valid_block _ _ |- _] =>
             apply Hvb' in H; clear Hvb'
           | [H: Mem.valid_block _ _ |- _] =>
             apply Hvb in H; clear Hvb
           | [|- Mem.valid_block (restrPermMap _) _] =>
             erewrite restrPermMap_valid
           | [|- Mem.valid_block _ _] =>
             eapply HvbF; clear HvbF
           end); eauto;
        try by specialize (codomain_valid0 _ _ H).
        { (* Permissions on coarse machine are higher than permissions on fine*)
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          - (*this is the case where the angel has replaced some permissions*)
            subst j. 
            do 2 rewrite restrPermMap_Cur.
            do 2 rewrite gLockSetRes.
            do 2 rewrite gssThreadRes.
            (*by case analysis on whether the angel changed the
              permission at this address*)
            assert (Hproject: Maps.PTree.get b0 (projectAngel (fp i pfc) virtueThread) =
                              Maps.PTree.get b1 virtueThread)
              by (symmetry; eapply projectAngel_correct; eauto).
            pf_cleanup.
            specialize (perm_obs_weak0 _ _ ofs0 Hrenaming).
            destruct (Maps.PTree.get b1 virtueThread) as [df|] eqn:Hdelta.
            + destruct (df ofs0) as [pnew |] eqn:Hdf.
              rewrite (computeMap_1 _ _ _ _ Hdelta Hdf).
              rewrite (computeMap_1 _ _ _ _ Hproject Hdf);
                by eapply po_refl.
              rewrite (computeMap_2 _ _ _ _ Hdelta Hdf).
              rewrite (computeMap_2 _ _ _ _ Hproject Hdf);
                by do 2 rewrite restrPermMap_Cur in perm_obs_weak0.
            + rewrite (computeMap_3 _ _ _ _ Hdelta).
              rewrite (computeMap_3 _ _ _ _ Hproject);
                by do 2 rewrite restrPermMap_Cur in perm_obs_weak0.
          - do 2 erewrite restrPermMap_Cur.
            do 2 rewrite gLockSetRes.
            erewrite gsoThreadRes with (cntj := pfcj); eauto.
            erewrite gsoThreadRes with (cntj := pffj); eauto.
            specialize (perm_obs_weak0 _ _ ofs0 Hrenaming).
            do 2 erewrite restrPermMap_Cur in perm_obs_weak0;
              by assumption. }
      - (* Proof of seperation of injections *)
        intros k j cntk' cntj' Hkj b0 b0' b3 b3' Hf0 Hf0' Hfk' Hfj'.
        assert (cntk: containsThread tpc k)
          by auto.
        assert (cntj: containsThread tpc j)
          by auto.
        erewrite cnt_irr with (cnt1 := cntk') (cnt2 := cntk) in Hfk'.
        erewrite cnt_irr with (cnt1 := cntj') (cnt2 := cntj) in Hfj'.
        eapply (HfpSep _ _ cntk cntj Hkj b0 b0');
          by eauto.
      - (* Proof of strong simulations after executing some thread*)
        intros.
        destruct (tid == i) eqn:Htid; move/eqP:Htid=>Htid; subst.
        { (*case of strong simulation for the thread that took the external*)
          exists (updLockSet
              (updThread pfc (Kresume c Vundef)
                 (computeMap (getThreadR pfc) virtueThread))
              (b, Int.intval ofs) virtueLP), mc'.
          assert (pfc0 = pfc)
            by (eapply cnt_irr; eauto); subst pfc0.
          rewrite Hsynced.
          repeat (split; (auto || constructor)).
          split; first by apply ren_incr_refl.
          split; first by auto.
          split; first by constructor.
          split.
          intros.
          constructor.
          do 2 rewrite gLockSetCode.
          do 2 rewrite gssThreadCode;
            by (split; [assumption | constructor]).
          destruct Htsim;
            by (eapply gss_mem_obs_eq_unlock; eauto).
          repeat split;
            by congruence.
        }       

        { (*strong simulation for another thread*)
          (*TODO: This proof is very similar to the lock case, make a lemma*)
          assert (Hstrong_sim := simStrong Hsim).
          assert (pfcj: containsThread tpc tid)
            by (eapply cntUpdateL' in pfc0;
                 eapply cntUpdate' in pfc0;
                 eauto).
          assert (pffj: containsThread tpf tid)
            by (eapply cntUpdateL' in pff0;
                 eapply cntUpdate' in pff0;
                 eauto).
          specialize (Hstrong_sim _ pfcj pffj).
          destruct Hstrong_sim
            as (tpcj & mcj & Hincrj & Hsyncedj & Hexecj & Htsimj
                & Hownedj & Hownedj_ls & Hownedj_lp).
          (* first we prove that i is a valid thread after executing thread j*)
          assert (pfcij:= containsThread_internal_execution Hexecj pfc).

          (*Proof Sketch: Basically the proof we want is that
            changing some non-observable part of the state/memory
            should not affect the execution of thread j. To avoid
            giving yet another definition of equivalence of the
            observable state we re-use our strong injections. Steps:
            
            1. The original state <tpc,mc> will strongly inject with
            the id injection in the state <tpc', mc'> where we have
            updated the value of the lock and the resource maps
            according to the angel.

            2. Hence if <tpc,mc> takes internal steps to get to <tpcj,
            mcj> so will <tpc',mc'> to go to a new state
            <tpcj',mcj'>. Moreover <tpcj,mcj> will inject to
            <tpcj',mcj'> with the id injection. We had to strengthen
            our lemmas and corestep_obs_eq to obtain that last part.

            3. We use [strong_tsim_id_trans] to get that <tpcj',mcj'>
               will strongly inject in <tpf,mf> with the same
               injection as <tpcj,mcj>.

            4. Finally we prove that changing the state/memory
            in (TODO: add lemma name) non-observable parts retains the
            [strong_tsim] relation. *)

          (* Step 1*)
          assert (pfcjj: containsThread tpcj tid)
            by (eapply containsThread_internal_execution; eauto).
          assert (Hcompj: mem_compatible tpcj mcj)
            by (eapply internal_execution_compatible with (tp := tpc); eauto).
          specialize (Htsimj pfcjj Hcompj).
          (* We prove that thread tid on the original state injects
            in thread tid after updating the lockpool and storing the
            lock value*)
          assert (Htsimj_id:
                    (strong_tsim (id_ren mc) pfcj pfc0 HmemCompC HmemCompC') /\
                    (Mem.nextblock mc = Mem.nextblock mc')).
          { eapply strong_tsim_store_id; eauto.
            erewrite gLockSetRes.
            rewrite gsoThreadRes; eauto.
            erewrite gLockSetCode.
            rewrite gsoThreadCode; eauto.
            destruct HinvC.
            apply permMapsDisjoint_comm; eauto.
            assert (domain_memren (id_ren mc) mc)
              by (apply id_ren_domain).
            assert (domain_memren (fp i pfc) mc)
              by (apply (mem_obs_eq_domain_ren (obs_eq Htsim))).
            eapply tp_wd_domain;
              by eauto.
          }
          destruct Htsimj_id as [Htsimj_id Hnextblock].
          
          (* Step 2.*)
          assert (H := strong_tsim_execution _ HinvC' Hfg Hge_wd
                                             Hge_incr_id Htsimj_id Hexecj).
          destruct H as
              (tp2' & m2' & f' & Hexecj'& Hincrj' & Hsepj'
               & Hnextblock' & Hinvj' & Htsimj' & Hid').
          destruct Htsimj' as (pf2j & pf2j' & Hcomp2 & Hcomp2' & Htsimj').
          specialize (Hid' Hnextblock (id_ren_correct mc)).
          assert (f' = id_ren mcj)
            by ( pose ((mem_obs_eq_domain_ren (obs_eq Htsimj')));
                 eapply is_id_ren; eauto); subst f'.
          exists tp2', m2'.
          erewrite cnt_irr with (cnt1 := pfc0) (cnt2 := pfcj).
          split; first by auto.
          split; first by auto.
          split; first by auto.
          split.
          (*strong thread simulation for j*)
          intros.
          pf_cleanup.
          (* Step 3, we use transitivity of strong_tsim *)
          assert (Htsim2j: strong_tsim (fp tid pfcj) pf2j' pffj Hcomp2'
                                       (mem_compf Hsim)).
          { eapply strong_tsim_id_trans
            with (f := fp tid pfcj) (Hcomp1 := Hcompj) (Hcomp1' := Hcomp2');
            eauto.
            destruct Hnextblock' as [[p [Hmcj Hm2']] | [Hmcj Hm2']];
              unfold Mem.valid_block;
              rewrite Hmcj Hm2' Hnextblock;
                by tauto.
          }
          (* Step 4*)
          destruct Htsim2j as [Hcodeq2j Hmem_obs_eq2j].
          constructor.
          rewrite gLockSetCode.
          rewrite gsoThreadCode;
            by auto.
          clear - Hmem_obs_eq2j HstoreF HinvF Htid.
          assert (HeqRes: getThreadR pff0 = getThreadR pffj)
            by (rewrite gLockSetRes;
                 rewrite gsoThreadRes; auto).
          assert (Hlt : permMapLt (getThreadR pff0)(getMaxPerm mf))
            by (rewrite HeqRes; destruct HmemCompF; eauto).
          eapply mem_obs_eq_storeF with (mf := mf) (Hlt :=  Hlt);
            eauto.
          destruct HinvF.
          specialize (lock_set_threads0 _ pffj).
          rewrite HeqRes;
            by eapply permMapsDisjoint_comm.
          erewrite restrPermMap_irr' with (Hlt := Hlt)
                                           (Hlt' := (mem_compf Hsim) tid pffj);
            by eauto.
          split.
          (*thread ownership*)
          intros k pff2k Hjk b1 b0 ofs0 Hfj Hfi.
          destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
          { subst k.
            rewrite gLockSetRes.
            rewrite gssThreadRes; auto.
            assert (Hunmapped: ~ (exists b, (fp i pfc) b = Some b0)).
            { intros Hcontra.
              destruct Hcontra as [b3 Hcontra].
              assert (Hfj' := Hincrj _ _ Hcontra).
              assert (Heq := injective (weak_obs_eq (obs_eq Htsimj)) _ _ Hfj Hfj');
                subst b3.
                by congruence.
            }
            erewrite computeMap_projection_2;
              by eauto.
          }
          { rewrite gLockSetRes.
            rewrite gsoThreadRes; auto.
            eapply Hownedj;
              by eauto.
          }
          split.
          (* lockset ownership*)
          intros b1 b0 ofs0 Hfj Hfi.
          assert (b2 <> b0).
          { intros ?; subst b0.
            assert (Hfbj := Hincrj _ _ Hfb).
            assert (Heq := injective (weak_obs_eq (obs_eq Htsimj)) _ _ Hfj Hfbj);
              subst b.
              by congruence.
          }
          erewrite gsoLockSet_2 by (intros Hcontra; inversion Hcontra; by subst).
          eapply Hownedj_ls;
            by eauto.
          (* lockpool ownership*)
          intros bl ofsl rmap b1 b0 ofs0 Hfj Hfi Hres.
          destruct (EqDec_address (b2, Int.intval ofs) (bl, ofsl)) as [Heq | Hneq].
          (* case rmap is the resource map updated by the angel*)
          (*TODO: generalize this part and make the whole thing a lemma*)
          inversion Heq; subst.
          rewrite gssLockRes in Hres. inversion Hres.
          assert (~ exists b, fp i pfc b = Some b0).
          { intros Hcontra.
            destruct Hcontra as [b' Hfb'].
            assert (Hfb'' := Hincrj _ _ Hfb').
            assert (b' = b1)
              by (eapply (injective (weak_obs_eq (obs_eq Htsimj)));
                   eauto). subst b'.
              by congruence.
          }
          erewrite projectMap_correct_2; eauto.
            by rewrite Hcanonical.
          (*case it is another resource map*)
          rewrite gsoLockRes in Hres; auto.
          rewrite gsoThreadLPool in Hres;
            by eauto.
        }
      - (* Proof of [strong_mem_obs_eq] for lock set*)
        specialize (HsimWeak _ pfc pff).
        split.
        eapply sync_locks_mem_obs_eq with (tpc := tpc) (tpf := tpf)
                                                       (mc := mc) (mf := mf); eauto.
        erewrite <- lockSet_updLockSet. reflexivity.
        erewrite <- lockSet_updLockSet. reflexivity.
        intros bl2 ofs0 Hres.
        destruct (EqDec_address (bl2, ofs0) (b2, Int.intval ofs)) as [Heq | Hneq].
        inversion Heq; subst.
        eexists;
          by eauto.
        rewrite gsoLockRes in Hres; auto.
        rewrite gsoThreadLPool in Hres.
        eapply HLocksInv;
          by eauto.
      - (* Proof of [strong_mem_obs_eq] for lock pool*)
        split.
        { intros bl1 bl2 ofs0 rmap1 rmap2 Hfi Hres1 Hres2.
          destruct (EqDec_address (b, Int.intval ofs) (bl1, ofs0)) as [Heq | Hneq].
          { (*case it is the acquired lock *)
            inversion Heq; subst.
            assert (bl2 = b2)
              by (rewrite Hfi in Hfb; by inversion Hfb).
            subst bl2.
            constructor.
            intros b1 b0 ofs0 Hf1.
            do 2 rewrite restrPermMap_Cur.
            rewrite gssLockRes in Hres1.
            rewrite gssLockRes in Hres2.
            inversion Hres1; inversion Hres2; subst.
            erewrite <- projectMap_correct; eauto.
            intros b1 b0 ofs0 Hf1 Hperm.
            (* This case is more complicated than the respective acquire
          case, because resources are transfered to the
          lockpool. Hence permissions at some addresss may increase
          and we need to look at the angel spec to determine that *)
            destruct Hangel as [HangelIncr HangelDecr].
            assert (Hperm_lp :=
                      restrPermMap_Cur (compat_lp HmemCompC'
                                                  (bl1, Int.intval ofs) Hres1) b1 ofs0).
            unfold permission_at in Hperm_lp.
            assert (rmap1 = virtueLP)
              by (clear - Hres1;
                   rewrite gssLockRes in Hres1;
                     by  inversion Hres1); subst rmap1.
            unfold Mem.perm in *.
            rewrite Hperm_lp in Hperm.
            specialize (snd (HangelIncr b1 ofs0) ltac:(eauto)).
            intros Hreadable_thread.
            (* case the address was readable on the thread *)
            destruct Htsim as [_ HobsEq].
            destruct HobsEq as [_ [HpermEq HvalEq]].
            unfold Mem.perm in HvalEq.
            assert (Hperm_eq := restrPermMap_Cur (HmemCompC _ pfc) b1 ofs0).
            unfold permission_at in Hperm_eq.
            specialize (HvalEq _ _ ofs0 Hf1).
            rewrite Hperm_eq in HvalEq.
            specialize (HvalEq Hreadable_thread).
            (* again we need to prove that the store for the lock
            release on both the coarse and fine-grained machine did
            not change these values *)
            assert (Hstable: ~ Mem.perm (restrPermMap (compat_ls HmemCompC))
                               b1 ofs0 Cur Writable).
            { clear - HinvC Hreadable_thread.
              intro Hcontra.
              destruct HinvC.
              specialize (lock_set_threads0 _ pfc).
              eapply perm_order_clash; eauto.
              specialize (lock_set_threads0 b1 ofs0).
              assert (H := restrPermMap_Cur (compat_ls HmemCompC) b1 ofs0).
              unfold permission_at in H.
              rewrite H;
                by rewrite perm_union_comm.
            }
            (* by simulation of the thread the permission on pff will
            also be above readable *)
            assert (Hreadable_threadF: Mem.perm_order' ((getThreadR pff) # b0 ofs0)
                                                       Readable)
              by (specialize (HpermEq _ _ ofs0 Hf1);
                   do 2 rewrite restrPermMap_Cur in HpermEq;
                   rewrite HpermEq; auto).
            (* and hence it must be below writable*)
            assert (HstableF: ~ Mem.perm (restrPermMap (compat_ls HmemCompF))
                                b0 ofs0 Cur Writable).
            { clear - HinvF Hreadable_threadF.
              intro Hcontra.
              destruct HinvF.
              specialize (lock_set_threads0 _ pff).
              eapply perm_order_clash; eauto.
              specialize (lock_set_threads0 b0 ofs0).
              assert (H := restrPermMap_Cur (compat_ls HmemCompF) b0 ofs0).
              unfold permission_at in H.
              rewrite H;
                by rewrite perm_union_comm.
            }
            simpl.
            erewrite store_contents_other; eauto.
            erewrite store_contents_other with
            (m := restrPermMap (compat_ls HmemCompF)) (m' := mf') (b := b2);
              by eauto.         
          }
          { (*case it's another lock*)
            assert ((b2, Int.intval ofs) <> (bl2, ofs0)).
            { clear - Hneq Hfi Hf Hfb Htsim.
              intros Hcontra; inversion Hcontra; subst.
              assert (b = bl1)
                by (eapply (injective (weak_obs_eq (obs_eq Htsim))); eauto).
              subst;
                by auto.
            }
            constructor.
            intros b1 b0 ofs1 Hf1.
            do 2 rewrite restrPermMap_Cur.
            rewrite gsoLockRes in Hres1; auto.
            rewrite gsoLockRes in Hres2; auto.
            rewrite gsoThreadLPool in Hres1.
            rewrite gsoThreadLPool in Hres2.
            specialize (HsimRes _ _ _ _ _ Hfi Hres1 Hres2).
            destruct HsimRes as [HpermRes HvalRes].
            specialize (HpermRes _ _ ofs1 Hf1);
              by do 2 rewrite restrPermMap_Cur in HpermRes.
            intros b1 b0 ofs1 Hf1 Hperm.
            unfold Mem.perm in *.
            assert (Hperm_eq:= restrPermMap_Cur
                                 (compat_lp HmemCompC' (bl1, ofs0) Hres1) b1 ofs1).
            unfold permission_at in Hperm_eq.
            rewrite Hperm_eq in Hperm.
            clear Hperm_eq.
            simpl.
            rewrite gsoLockRes in Hres1; auto.
            rewrite gsoLockRes in Hres2; auto.
            rewrite gsoThreadLPool in Hres1.
            rewrite gsoThreadLPool in Hres2.
            specialize (HsimRes _ _ _ _ _ Hfi Hres1 Hres2).
            destruct HsimRes as [HpermRes HvalRes].
            unfold Mem.perm in HvalRes.
            assert (Hperm_eq:= restrPermMap_Cur
                                 (compat_lp HmemCompC (bl1, ofs0) Hres1) b1 ofs1).
            unfold permission_at in Hperm_eq.
            specialize (HvalRes _ _ ofs1 Hf1).
            rewrite Hperm_eq in HvalRes.
            specialize (HvalRes Hperm). simpl in HvalRes.
            eapply gsoMem_obs_eq with (HltC := compat_ls HmemCompC)
                                        (HltF := compat_ls HmemCompF)
                                        (bl1 := b) (bl2 := b2); eauto.
            apply permMapsDisjoint_comm.
            eapply (lock_res_set HinvC); eauto.
          }
        }
        { intros bl1 bl2 ofs0 Hfl1.
          destruct (EqDec_address (b, Int.intval ofs) (bl1, ofs0)).
          - inversion e; subst.
            assert (b2 = bl2)
              by (rewrite Hf in Hfl1; inversion Hfl1; subst; auto).
            subst.
            do 2 rewrite gsslockResUpdLock.
            split;
            auto.
          - erewrite gsolockResUpdLock by eauto.
            assert ((b2, Int.intval ofs) <> (bl2, ofs0)).
            { intros Hcontra.
              inversion Hcontra; subst.
              specialize (Hinjective _ _ _ Hfl1 Hf).
              subst; auto.
            }
            erewrite gsolockResUpdLock by eauto.
            do 2 rewrite gsoThreadLPool.
            eauto.
        }
        - (* Proof of invariant preservation for fine-grained machine*)
          destruct Htsim.
          eapply invariant_project; by eauto.
        - (* Max permission invariant*)
            by assumption.
        - (* new memory is well-defined*)
          eapply store_wd_domain
          with (m := (restrPermMap (compat_ls HmemCompC))); eauto.
            by simpl.
        - (* new tpc well defined*)
          apply tp_wd_lockSet.
          intros j cntj'.
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          subst. rewrite gssThreadCode.
          specialize (Htpc_wd _ pfc).
          rewrite Hcode in Htpc_wd.
          simpl in *;
            by auto.
          assert (cntj := cntUpdate' _ _ _ cntj').
          erewrite @gsoThreadCode with (cntj := cntj) by assumption.
          specialize (Htpc_wd _ cntj).
            by auto.
        - (*ge well defined*)
          assumption.
        - (*ge spec *)
          split; assumption.
        - (*xs invariant*)
          intros;
          eapply cntUpdateL;
          eapply cntUpdate;
            by eauto.
    }
    { (* Thread Spawn *)
      subst.
      (* We have that the core of the fine grained execution
        is related to the one of the coarse-grained*)
      assert (Hcore_inj:= code_eq Htsim).
      rewrite Hcode in Hcore_inj.
      simpl in Hcore_inj.
      destruct (getThreadC pff) as [? | cf |? | ?] eqn:HcodeF;
        try by exfalso.
      (* And now we can prove that cf is also at external *)
      assert (Hat_external_spec := core_inj_ext Hcore_inj).
      rewrite Hat_external in Hat_external_spec.
      destruct (at_external SEM.Sem cf) as [[[? ?] vsf]|] eqn:Hat_externalF;
        try by exfalso.
      (* and moreover that it's the same external and their
        arguments are related by the injection*)
      destruct Hat_external_spec as [? [? Harg_obs]]; subst.
      inversion Harg_obs as [|? vff argf vsf' Hptr_obs Hl]; subst.
      inversion Hl; subst.
      inversion H3; subst. clear H3.
      inversion Hptr_obs; subst.
      (* To compute the new fine grained state, we apply the
        renaming to the resources the angel provided us*)
      remember (projectAngel (fp i pfc) virtue1) as virtue1F eqn:Hvirtue1F.
      remember (projectAngel (fp i pfc) virtue2) as virtue2F eqn:Hvirtue2F.
      remember (updThread pff (Kresume cf Vundef)
                          (computeMap (getThreadR pff) virtue1F))
        as tpf_upd eqn:Htpf_upd.
      remember (addThread tpf_upd (Vptr b2 ofs) v'
                          (computeMap empty_map virtue2F))
        as tpf' eqn:Htpf'.
      (* we prove that the projected angel satisfies the angelSpec*)
      assert (HangelDecrF: forall b ofs,
                 Mem.perm_order'' ((getThreadR pff) # b ofs)
                                  ((computeMap (getThreadR pff) virtue1F) # b ofs)).
      { intros b2' ofs'.
        subst.
        destruct Htsim.
        assert (Hem: (exists b, (fp i pfc) b = Some b2') \/ ~ exists b, (fp i pfc) b = Some b2')
          by  eapply em.
        destruct Hem as [[? Hf] | Hunmapped].
        erewrite computeMap_projection_1; eauto.
        destruct obs_eq0 as [_ [HpermEq _]].
        specialize (HpermEq _ _ ofs' Hf).
        do 2 rewrite restrPermMap_Cur in HpermEq.
        rewrite HpermEq;
          by eauto.
        erewrite computeMap_projection_2; eauto.
          by apply po_refl.
      }
        
      assert (HangelIncrF: forall (b : positive) (ofs : Z),
                 Mem.perm_order'' (Some Nonempty)
                                  ((computeMap empty_map virtue2F) # b ofs)).
      { intros b2' ofs'.
        subst.
        destruct Htsim as [_ [Hweak _]].
        destruct Hweak.
        assert (Hem: (exists b, (fp i pfc) b = Some b2') \/ ~ exists b, (fp i pfc) b = Some b2')
          by  eapply em.
        destruct Hem as [[? Hf] | Hunmapped].
        erewrite computeMap_projection_3;
          by eauto.
        erewrite computeMap_projection_2; eauto.
        simpl;
          by rewrite empty_map_spec.
      } 
      (* we augment the renamings pool by assigning the ''generic''
      renaming (fp i pfc) to the new thread *)
      exists tpf', mf, (fp i pfc),
      (@addFP _ fp (fp i pfc) (Vptr b ofs) arg (computeMap empty_map virtue2)),
      (tr ++ [:: (external i (spawn (b2,Int.intval ofs)))]). 
      split.
      (* proof that the fine grained machine can step*)
      intros U.
      assert (HsyncStepF: syncStep the_ge pff HmemCompF tpf' mf
                                   (spawn (b2, Int.intval ofs)))
        by (eapply step_create; eauto).
      econstructor; simpl;
        by eauto.
      (* Proof that the new coarse and fine state are in simulation*)
      assert (HinvC': invariant
                        (addThread
                           (updThread pfc (Kresume c Vundef)
                                      (computeMap (getThreadR pfc) virtue1))
                           (Vptr b ofs) arg
                           (computeMap empty_map virtue2)))
        by  (eapply safeC_invariant with (n := fuelF.+1 + size xs); eauto).
      assert (HmemCompF'' : mem_compatible tpf' mf)
        by (pose proof (codomain_valid (weak_obs_eq (obs_eq Htsim))); subst;
            eapply mem_compatible_spawn; eauto).
      subst.
      assert (Hnum: num_threads tpc = num_threads tpf)
          by (eapply contains_iff_num; eauto).
      eapply Build_sim with (mem_compc := HmemCompC') (mem_compf := HmemCompF'').
        - (* containsThread *)
          clear - HnumThreads Hnum.
          intros j.
          split;
            intros cntj;
            apply cntAdd' in cntj;
            destruct cntj as [[cntj _] | Heq];
            try (apply cntAdd;
                  apply cntUpdate;
                  apply HnumThreads;
                    by apply cntUpdate' in cntj);
            try (unfold containsThread;
                  subst; simpl; rewrite Hnum;
                  simpl;
                    by ssromega).
        - (*safety of coarse machine*)
            by assumption.
        - (* weak simulation between the two machines*)
          intros j pfcj' pffj'.
          destruct (HsimWeak _ pfc pff) as [? ? ? ? _].
          constructor; intros;
          repeat
            (match goal with
             | [H: context[Mem.valid_block (restrPermMap _) _] |- _] =>
               erewrite restrPermMap_valid in H
             | [|- Mem.valid_block (restrPermMap _) _] =>
               erewrite restrPermMap_valid
             end); eauto;
          try by specialize (codomain_valid0 _ _ H).
          { (* Permissions on coarse machine are higher than permissions on fine*)
            (* there are three cases now, the thread that spawned, the
            spawned thread and any other thread *)
            do 2 rewrite restrPermMap_Cur.
            assert (pfcj := cntAdd' _ _ _ pfcj').
            destruct pfcj as [[pfcj _] | pfcj].

            { (* case it's not the new thread *)
              assert (pffj: containsThread
                              (updThread pff (Kresume cf Vundef)
                                         (computeMap (getThreadR pff)
                                                     (projectAngel (fp i pfc)
                                                                   virtue1))) j)
                by (apply cntUpdate;
                     apply cntUpdate' in pfcj;
                       by eapply HnumThreads).
              erewrite gsoAddRes with (cntj := pfcj); eauto.
              erewrite gsoAddRes with (cntj := pffj); eauto.
              (* By case analysis on whether j is the spawning thread
              or some other thread *)
              destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
              - subst i.
                rewrite gssThreadRes.
                rewrite gssThreadRes.
                destruct Htsim.
                erewrite computeMap_projection_1; eauto.
                  by apply po_refl.
              - assert (pfcj0 := cntUpdate' _ _ _ pfcj).
                assert (pffj0 := cntUpdate' _ _ _ pffj).
                erewrite gsoThreadRes with (cntj := pfcj0); eauto.
                erewrite gsoThreadRes with (cntj := pffj0); eauto.
                specialize (HsimWeak _ pfcj0 pffj0).
                clear - HsimWeak Hrenaming.
                destruct HsimWeak.
                specialize (perm_obs_weak0 _ _ ofs0 Hrenaming).
                do 2 rewrite restrPermMap_Cur in perm_obs_weak0;
                  by assumption.
            }
            { (*case j is the new thread *)
              assert (pffj := cntAdd' _ _ _ pffj').
              destruct pffj as [[_ Hcontra] | pffj].
              subst. simpl in Hcontra.
              rewrite Hnum in Hcontra;
                by exfalso.
              subst.
              erewrite gssAddRes; eauto.
              erewrite gssAddRes; eauto.
              erewrite computeMap_projection_3; eauto.
                by apply po_refl.
            }
          }
        - (* Proof of seperation of injections *)
          intros k j cntk' cntj' Hkj b0 b0' b3 b3' Hf0 Hf0' Hfk' Hfj'.
          (* By a very annoying case analyses on thread j and k*)
          (* since thread i is already in the renamings pool we can
              derive a contradiction*)
          destruct (i == j) eqn:Hij; move/eqP:Hij=> Hij;
            first by (subst j; rewrite gsoAddFP in Hfj'; by congruence).
          (* likewise for thread k*)
          destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik;
            first by (subst k; rewrite gsoAddFP in Hfk'; by congruence).
          (* we now check whether j is the new thread or not*)
          assert (cntj := cntAdd' _ _ _ cntj').
          destruct cntj as [[cntj _] | cntj].
          + (*case j is an existing thread *)
            rewrite gsoAddFP in Hfj'.
            assert (cntk := cntAdd' _ _ _ cntk').
            destruct cntk as [[cntk _] | cntk].
            * (* case k is an existing thread *)
              rewrite gsoAddFP in Hfk'.
              eapply (HfpSep k j cntk cntj Hkj b0 b0');
                by eauto.
            * (*case k is the new thread *)
              subst k.
              erewrite gssAddFP in Hfk'; auto.
                by congruence.
          + (*case j is the new thread *)
            subst.
            erewrite gssAddFP in Hfj'; auto.
              by congruence.
        - (* Proof of strong simulations after executing some thread*)
          intros j pfcj' pffj'.
          (* we now check whether tid is the new thread or not*)
          assert (pfcj := cntAdd' _ _ _ pfcj').
          destruct pfcj as [[pfcj _] | pfcj].
          assert (pffj: containsThread
                          (updThread pff (Kresume cf Vundef)
                                     (computeMap (getThreadR pff)
                                                 (projectAngel (fp i pfc)
                                                               virtue1))) j)
            by (apply cntUpdate;
                 apply cntUpdate' in pfcj;
                 eapply HnumThreads; eauto).
          + (*case j is an old thread*)
            destruct (j == i) eqn:Hj; move/eqP:Hj=>Hj; subst.
            { (*case of strong simulation for the thread that did the spawn*)
              exists (addThread
                   (updThread pfc (Kresume c Vundef)
                              (computeMap (getThreadR pfc) virtue1)) (Vptr b ofs) arg
                   (computeMap empty_map virtue2)), mc'.
              rewrite Hsynced.
              rewrite gsoAddFP.
              repeat (split; (auto || constructor)).
              split; first by apply ren_incr_refl.
              split; first by auto.
              split; first by constructor.
              split.
              intros.
              destruct Htsim as [HcodeEq Hmem_obs_eq].
              constructor.
              erewrite gsoAddCode with (cntj := pfcj); eauto.
              erewrite gsoAddCode with (cntj := pffj); eauto.
              rewrite Hcode HcodeF in HcodeEq.
              do 2 rewrite gssThreadCode.
              simpl in *;
                by (split; [auto | constructor]).
              (* Some of the resources of thread i will have decreased now*)
              inversion Hmem_obs_eq as [Hweak_obs_eq Hstrong_obs_eq].
              destruct Hweak_obs_eq.
              constructor.
              constructor; intros;
              repeat
                (match goal with
                 | [H: context[Mem.valid_block (restrPermMap _) _] |- _] =>
                   erewrite restrPermMap_valid in H
                 | [|- Mem.valid_block (restrPermMap _) _] =>
                   erewrite restrPermMap_valid
                 end); eauto;
              try (specialize (codomain_valid0 _ _ H); eauto).
              (* permissions of coarse grained state are higher*)
              do 2 rewrite restrPermMap_Cur.
              erewrite gsoAddRes with (cntj := pfcj); eauto.
              erewrite gsoAddRes with (cntj := pffj); eauto.
              do 2 rewrite gssThreadRes.
              erewrite computeMap_projection_1 by eauto;
                by apply po_refl.
              (* strong obs eq for thread i*)
              constructor.
              intros.
              do 2 rewrite restrPermMap_Cur.
              erewrite gsoAddRes with (cntj := pfcj); eauto.
              erewrite gsoAddRes with (cntj := pffj); eauto.
              do 2 rewrite gssThreadRes.
              erewrite computeMap_projection_1;
                by eauto.
              intros.
              simpl.
              (*since the reduced permissions on thread i are above
              readable then the previous permissions was also above
              readable*)
              clear - Hstrong_obs_eq Hperm Hrenaming HangelDecr pfcj.
              assert (H := restrPermMap_Cur (mem_compc' i pfc') b1 ofs0).
              unfold Mem.perm in Hperm.
              unfold permission_at in H.
              rewrite H in Hperm.
              replace (getThreadR pfc') with (getThreadR pfcj) in Hperm
                by (erewrite gsoAddRes; eauto).
              replace ((getThreadR pfcj)) with
              (computeMap (getThreadR pfc) virtue1) in Hperm
                by  (erewrite gssThreadRes; eauto).
              specialize (HangelDecr b1 ofs0).
              destruct Hstrong_obs_eq.
              unfold Mem.perm in *.
              specialize (val_obs_eq0 _ _ ofs0 Hrenaming).
              rewrite po_oo in val_obs_eq0.
              erewrite <- restrPermMap_Cur with (Hlt := HmemCompC i pfc) in HangelDecr.
              specialize (val_obs_eq0 ltac:(eapply po_trans; eauto));
                by simpl in val_obs_eq0.
              (* block ownership for thread i*)
              repeat (split; try (intros; by congruence)). 
            }
            { (* case j is a thread different than i*)
              (* this case should be straight forward because the
              state for thread j was not altered in any way*)
               assert (Hstrong_sim := simStrong Hsim).
               assert (pfcj0: containsThread tpc j)
                 by ( eapply cntUpdate' in pfcj;
                      eauto).
               assert (pffj0: containsThread tpf j)
                 by (eapply HnumThreads; eauto).
               specialize (Hstrong_sim _ pfcj0 pffj0).
               destruct Hstrong_sim
                 as (tpcj & mcj & Hincrj & Hsyncedj & Hexecj & Htsimj
                     & Hownedj & Hownedj_ls & Hownedj_lp).
               rewrite gsoAddFP.
               (* we prove that thread i will still be valid after executing thread j*)
               assert (pfcji := containsThread_internal_execution Hexecj pfc).
               (* the state will be the same as tpcj but with an extra thread*)
               exists (addThread (updThread pfcji
                                       (Kresume c Vundef)
                                       (computeMap (getThreadR pfc) virtue1))
                            (Vptr b ofs) arg (computeMap empty_map virtue2)), mcj.
               assert (pfcjj := containsThread_internal_execution Hexecj pfcj0).
               assert (Hcompj: mem_compatible tpcj mcj)
                 by (eapply internal_execution_compatible with (tp := tpc); eauto).
               specialize (Htsimj pfcjj Hcompj).
               destruct Htsimj as [Hcode_eqj Hobs_eqj].
               split; eauto.
               split; eauto.
               split.
               eapply addThread_internal_execution; eauto.
               apply updThread_internal_execution; eauto.
               eapply ThreadPoolWF.invariant_decr;
                 by eauto.
               eapply mem_compatible_add;
                 by eauto.
               split.
               pf_cleanup.
               intros.
               assert (pfcjj': containsThread
                                 (updThread pfcji (Kresume c Vundef)
                                            (computeMap (getThreadR pfc) virtue1)) j)
                 by  (apply cntUpdate; auto).
               assert (pffj: containsThread
                               (updThread pff (Kresume cf Vundef)
                                          (computeMap (getThreadR pff)
                                                      (projectAngel (fp i pfc)
                                                                 virtue1))) j)
              by (apply cntUpdate; auto).
            constructor.
            (* the simulation of cores is straightforward, we just
            need to massage the containsThread proofs a bit *)
            erewrite gsoAddCode with (cntj := pfcjj'); eauto.
            rewrite gsoThreadCode; eauto.
            erewrite gsoAddCode with (cntj := pffj); eauto.
            rewrite gsoThreadCode;
              by auto.
            (* weak_mem_obs_eq simulation*)
            constructor.
            destruct Hobs_eqj.
            destruct weak_obs_eq0.
            constructor; eauto.
            (* permissions on the coarse-grained are higher than on the fine*)
            intros b0 b2' ofs0 Hfj.
            do 2 rewrite restrPermMap_Cur.
            specialize (perm_obs_weak0 b0 b2' ofs0 Hfj).
            do 2 rewrite restrPermMap_Cur in perm_obs_weak0.
            erewrite gsoAddRes with (cntj := pfcjj'); eauto.
            rewrite gsoThreadRes; eauto.
            erewrite gsoAddRes with (cntj := pffj); eauto.
            rewrite gsoThreadRes;
              by auto.
            (*strong_mem_obs_eq simulation*)
            destruct Hobs_eqj as [_ [Hperm_eqj Hval_eqj]].
            constructor.
            intros b0 b2' ofs0 Hfj.
            do 2 rewrite restrPermMap_Cur.
            specialize (Hperm_eqj b0 b2' ofs0 Hfj).
            do 2 rewrite restrPermMap_Cur in Hperm_eqj.
            erewrite gsoAddRes with (cntj := pfcjj'); eauto.
            rewrite gsoThreadRes; eauto.
            erewrite gsoAddRes with (cntj := pffj); eauto.
            rewrite gsoThreadRes;
              by auto.
            clear - Hval_eqj HangelDecr pfcjj' Hj.
            intros b0 b2' ofs0 Hfj Hperm.
            specialize (Hval_eqj b0 b2' ofs0 Hfj).
            simpl.
            simpl in Hval_eqj.
            unfold Mem.perm in *.
            (* this is where we use the fact that permissions decreased*)
            assert (H1 := restrPermMap_Cur (Hcompj _ pfcjj) b0 ofs0).
            assert (H2 := restrPermMap_Cur (mem_compc' _ pfc') b0 ofs0).
            unfold permission_at in *.
            rewrite H2 in Hperm.
            rewrite H1 in Hval_eqj.
            erewrite gsoAddRes with (cntj := pfcjj') in Hperm; eauto.
            rewrite gsoThreadRes in Hperm;
              by eauto.
            (* block ownership*)
            split.
            intros k pffk' Hjk b0 b2' ofs0 Hfk Hfi.
            (* block b2 won't be mapped by fi*)
            assert (Hunmapped: ~ (exists b, (fp i pfc) b = Some b2')).
            { intros Hcontra.
              destruct Hcontra as [b3 Hcontra].
              assert (Hfj' := Hincrj _ _ Hcontra).
              assert (Heq := injective (weak_obs_eq Hobs_eqj) _ _ Hfk Hfj');
                subst b3.
                by congruence.
            }
            assert (pfck := cntAdd' _ _ _ pffk').
            destruct pfck as [[pfck _] | pfck].
            (* case k is an old thread*)
            assert (pffk: containsThread
                            (updThread pff (Kresume cf Vundef)
                                       (computeMap (getThreadR pff)
                                                   (projectAngel (fp i pfc)
                                                                 virtue1))) j)
              by (apply cntUpdate; auto).
            erewrite gsoAddRes with (cntj := pfck); eauto.
            destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
            subst k.
            rewrite gssThreadRes.
            erewrite computeMap_projection_2;
              by eauto.
            rewrite gsoThreadRes; auto.
            eapply Hownedj;
              by eauto.
            (*case k is the new thread*)
            subst k.
            erewrite gssAddRes; eauto.
            erewrite computeMap_projection_2 by eauto;
              by apply empty_map_spec.
            split.
            intros b0 b2' ofs0 Hfj Hfi.
            rewrite gsoAddLock.
            rewrite gsoThreadLock;
              by eauto.
            intros bl ofsl rmap b0 b2' ofs0 Hfj Hfi Hres.
            rewrite gsoAddLPool in Hres.
            rewrite gsoThreadLPool in Hres;
              by eauto.
            }
          + (*case j is the new thread*)
            (* in this case there will not be any internal steps, from
            invariant Hxs*)
            exists (addThread
                 (updThread pfc (Kresume c Vundef)
                            (computeMap (getThreadR pfc) virtue1)) (Vptr b ofs) arg
                 (computeMap empty_map virtue2)), mc'.
            subst j.
            rewrite gssAddFP; eauto.
            split; first by eapply ren_incr_refl.
            simpl.
            split; eauto.
            rewrite not_in_filter.
            split; first by constructor.
            split.
            (*strong_tsim for the new thread*)
            intros ? Hcompj'.
            pf_cleanup.
            constructor.
            erewrite gssAddCode; eauto.
            erewrite gssAddCode; eauto.
            simpl; eauto.
            unfold latestThread. simpl.
            apply f_equal;
              by auto.
            (*mem_obs_eq for the new thread*)
            destruct (HsimWeak _ pfc pff).
            constructor.
            constructor; eauto.
            (*permissions on coarse are higher*)
            intros b0 b2' ofs0 Hf.
            do 2 rewrite restrPermMap_Cur.
            erewrite gssAddRes; eauto.
            erewrite gssAddRes; eauto.
            erewrite computeMap_projection_3 by eauto;
              by apply po_refl.
            unfold latestThread; simpl;
              by apply f_equal.
            constructor.
            intros b0 b2' ofs0 Hf.
            do 2 rewrite restrPermMap_Cur.
            erewrite gssAddRes; eauto.
            erewrite gssAddRes; eauto.
            erewrite computeMap_projection_3;
              by eauto.
            unfold latestThread; simpl;
              by apply f_equal.
            intros b0 b2' ofs0 Hf Hperm.
            (* by the angel specification we derive a contradiction,
            no address has more than nonempty permission *)
            exfalso.
            clear - Hperm HangelIncr.
            specialize (HangelIncr b0 ofs0).
            assert (H := restrPermMap_Cur (HmemCompC' _ pfcj') b0 ofs0).
            unfold permission_at in H.
            unfold Mem.perm in Hperm.
            rewrite H in Hperm.
            erewrite gssAddRes in Hperm; eauto.
            clear - Hperm HangelIncr.
            simpl in *.
            destruct ((computeMap empty_map virtue2) # b0 ofs0);
            inversion HangelIncr; subst;
            simpl in Hperm;
              by inversion Hperm.
            (* block ownership*)
            repeat (split);
              intros; by congruence.
            intros Hin.
            specialize (Hxs _ Hin).
            clear - Hxs.
            unfold containsThread in Hxs.
              by ssromega.
        - (* lockset simulation *)
          split.
          destruct HsimLocks.
          constructor.
          intros.
          do 2 rewrite restrPermMap_Cur.
          do 2 rewrite gsoAddLock.
          do 2 rewrite gsoThreadLock.
          specialize (perm_obs_strong0 _ _ ofs0 Hrenaming).
          do 2 rewrite restrPermMap_Cur in perm_obs_strong0;
            by assumption.
          intros.
          simpl.
          unfold Mem.perm.
          assert (H := restrPermMap_Cur (compat_ls HmemCompC') b1 ofs0).
          unfold permission_at in H.
          unfold Mem.perm in *.
          specialize (val_obs_eq0 _ _ ofs0 Hrenaming).
          clear - Hperm H val_obs_eq0.
          rewrite H in Hperm.
          assert (H2 := restrPermMap_Cur (compat_ls HmemCompC) b1 ofs0).
          unfold permission_at in H2.
          rewrite H2 in val_obs_eq0.
          replace ((lockSet
                     (addThread
                        (updThread pfc (Kresume c Vundef)
                                   (computeMap (getThreadR pfc) virtue1))
                        (Vptr b ofs) arg
                        (computeMap empty_map virtue2))) # b1 ofs0)
          with ((lockSet tpc) # b1 ofs0) in *;
            by eauto.
          intros bl2 ofs0 Hres.
          rewrite gsoAddLPool in Hres.
          rewrite gsoThreadLPool in Hres;
            by eauto.
        - (* lock resource simulation *)
          split.
          + intros bl1 bl2 ofs0 rmap1 rmap2 Hf Hl1 Hl2.
            assert (Hl1' : lockRes tpc (bl1, ofs0) = Some rmap1)
              by (rewrite gsoAddLPool gsoThreadLPool in Hl1; auto).
            assert (Hl2' : lockRes tpf (bl2, ofs0) = Some rmap2)
              by (rewrite gsoAddLPool gsoThreadLPool in Hl2; auto).
            specialize (HsimRes _ _ _ _ _ Hf Hl1' Hl2').
            destruct HsimRes as [HpermRes HvalRes].
            constructor.
            intros.
            do 2 rewrite restrPermMap_Cur.
            specialize (HpermRes _ _ ofs1 Hrenaming).
            do 2 rewrite restrPermMap_Cur in HpermRes;
              by auto.
            intros.
            specialize (HvalRes _ _ ofs1 Hrenaming).
            unfold Mem.perm in *.
            assert (Hp1 := restrPermMap_Cur (compat_lp HmemCompC' (bl1, ofs0) Hl1) b1 ofs1).
            assert (Hp2 := restrPermMap_Cur (compat_lp HmemCompC (bl1, ofs0) Hl1') b1 ofs1).
            unfold permission_at in *.
            rewrite Hp1 in Hperm.
            rewrite Hp2 in HvalRes.
            simpl in *;
              by eauto.
          + intros bl1 bl2 ofs0 Hfl1.
            do 2 rewrite gsoAddLPool gsoThreadLPool.
            eauto.
        - (* proof of invariant *)
          destruct Htsim.
          eapply invariant_project_spawn;
          eauto.
        - assumption.
        - assumption.
        - clear - Htpc_wd Hcode Hat_external.
          intros j cntj'.
          assert (cntj := cntAdd' _ _ _ cntj').
          destruct cntj as [[cntj _] | cntj].
          assert (cntj0 := cntUpdate' _ _ pfc cntj).
          erewrite @gsoAddCode with (cntj := cntj); eauto.
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          subst.
          rewrite gssThreadCode.
          specialize (Htpc_wd _ cntj0).
          pf_cleanup.
          rewrite Hcode in Htpc_wd.
          simpl in *;
            by auto.
          rewrite gsoThreadCode;
            by auto.
          subst.
          erewrite gssAddCode; eauto.
          simpl.
          assert (Hcore_wd := Htpc_wd _ pfc).
          rewrite Hcode in Hcore_wd. simpl in Hcore_wd.
          eapply at_external_wd in Hat_external; eauto.
          inversion Hat_external; subst.
          inversion H2; subst.
            by auto.
        - (*ge_wd *)
          assumption.
        - (* ge_spec *)
          split; assumption.
        - intros j Hin.
          specialize (Hxs _ Hin).
          apply cntAdd;
            by apply cntUpdate.
    }
    { (* mklock case *)
      assert (Hvalidb: Mem.valid_block m1 b).
      { eapply Mem.store_valid_access_3 in Hstore.
        eapply Mem.valid_access_valid_block; eauto.
        eapply Mem.valid_access_implies; eauto.
        constructor.
      }
      rewrite <- Hrestrict_pmap in Hvalidb.
      (*  and compute the corresponding block in mf *)
      destruct ((domain_valid (weak_obs_eq (obs_eq Htsim))) _ Hvalidb)
        as [b2 Hfb].
      assert (Hvalidb2 := (codomain_valid (weak_obs_eq (obs_eq Htsim))) _ _ Hfb).
      erewrite restrPermMap_valid in Hvalidb2.
      remember (restrPermMap (compat_ls HmemCompF)) as mf1 eqn:Hrestrict_pmapF.
      assert (Hval_obs: val_obs (fp i pfc) (Vint Int.zero) (Vint Int.zero))
        by constructor.
      (* and storing gives us related memories*)
      subst m1.
      destruct Htsim as [Hcore_inj Hmem_obs_eq].
      assert (HstoreF := store_val_obs _ _ _ Hstore Hfb Hval_obs Hmem_obs_eq).
      destruct HstoreF as [mf' [HstoreF Hmem_obs_eq']].
      (* We have that the code of the fine grained execution
        is related to the one of the coarse-grained*)
      rewrite Hcode in Hcore_inj.
      simpl in Hcore_inj.
      destruct (getThreadC pff) as [? | cf |? | ?] eqn:HcodeF;
        try by exfalso.
      (* And now we can prove that cf is also at external *)
      assert (Hat_external_spec := core_inj_ext Hcore_inj).
      rewrite Hat_external in Hat_external_spec.
      destruct (at_external SEM.Sem cf) as [[[? ?] vsf]|] eqn:Hat_externalF;
        try by exfalso.
      (* and moreover that it's the same external and their
        arguments are related by the injection*)
      destruct Hat_external_spec as [? [? Harg_obs]]; subst.
      inversion Harg_obs as [|? ? ? ? Hptr_obs Hl]; subst.
      inversion Hl; subst.
      inversion Hptr_obs as [| | | |b1 bf ofs0 Hf|];
        subst b1 ofs0 v'.
      assert (bf = b2)
        by (rewrite Hf in Hfb; by inversion Hfb);
        subst bf.
      (* we compute the new permissions on the thread*)
      remember (setPermBlock (Some Nonempty) b2 (Int.intval ofs) (getThreadR pff)
                             lksize.LKSIZE_nat) as pmap_tidF' eqn:Hdrop_permF.
      symmetry in Hdrop_permF.
      (* To compute the new fine grained state, we first update the thread*)
      remember (updThread pff (Kresume cf Vundef) pmap_tidF') as tpf' eqn:Htpf'.
      (* And also update the lockset to build the final fine-grained
      state*)
      remember (updLockSet tpf' (b2, Int.intval ofs) empty_map) as tpf'' eqn:Htpf'';
        symmetry in Htpf''.
      exists tpf'', mf', (fp i pfc), fp, (tr ++ [:: (external i (mklock (b2, Int.intval ofs)))]).
      split.
      (* proof that the fine grained machine can step*)
      intros U.
      assert (HsyncStepF: syncStep the_ge pff HmemCompF tpf'' mf' (mklock (b2, Int.intval ofs)))
        by (eapply step_mklock with (b:=b2); eauto).
      econstructor; simpl;
        by eauto.
      (* Proof that the new coarse and fine state are in simulation*)
      assert (HinvC':
                invariant (updLockSet
                          (updThread pfc (Kresume c Vundef)
                                     (setPermBlock (Some Nonempty) b (Int.intval ofs) 
                                                   (getThreadR pfc)
                                                   lksize.LKSIZE_nat))
                          (b, Int.intval ofs) empty_map))
        by  (eapply safeC_invariant with (n := fuelF.+1 + size xs); eauto).
      assert (HmaxF': max_inv mf')
        by (eapply max_inv_store; eauto).
      assert (HmemCompF'': mem_compatible tpf'' mf').
      { subst.
        clear - HmemCompF HmaxF' Hf Hmem_obs_eq Hvalidb2 HstoreF.
        constructor.
        - intros.
          rewrite gLockSetRes.
          destruct (i == tid) eqn:Heq; move/eqP:Heq=>Heq.
          + subst. rewrite gssThreadRes.
            intros b' ofs'.
            destruct (Pos.eq_dec b2 b').
            * subst.
              assert (Hvalidb2' := Mem.store_valid_block_1 _ _ _ _ _ _
                                                           HstoreF b' Hvalidb2).
              specialize (HmaxF' _ ofs' Hvalidb2').
              rewrite getMaxPerm_correct.
              rewrite HmaxF'.
              destruct ((setPermBlock (Some Nonempty) b' (Int.intval ofs) 
                                      (getThreadR pff) lksize.LKSIZE_nat) # b' ofs');
                simpl; constructor.
            * rewrite setPermBlock_other_2; auto.
              erewrite <- mem_store_max by eauto.
              rewrite getMax_restr.
              eapply HmemCompF.
          + intros b' ofs'.
            erewrite <- mem_store_max by eauto.
            rewrite getMax_restr.
            rewrite gsoThreadRes; auto.
            eapply HmemCompF.
        - intros l rmap Hres.
          destruct (EqDec_address (b2, Int.intval ofs) l).
          + inversion e; subst.
            rewrite gsslockResUpdLock in Hres.
            inversion Hres.
            intros b' ofs'.
            rewrite empty_map_spec.
            destruct ((getMaxPerm mf') # b' ofs'); simpl; auto.
          + erewrite gsolockResUpdLock in Hres by eauto.
            intros b' ofs'.
            erewrite <- mem_store_max by eauto.
            rewrite gsoThreadLPool in Hres.
            rewrite getMax_restr.
            eapply (compat_lp HmemCompF); eauto.
        - intros b' ofs'.
          destruct (Pos.eq_dec b2 b').
          * subst.
            assert (Hvalidb2' := Mem.store_valid_block_1 _ _ _ _ _ _
                                                         HstoreF b' Hvalidb2).
            specialize (HmaxF' _ ofs' Hvalidb2').
            rewrite getMaxPerm_correct.
            rewrite HmaxF'.
            simpl.
            match goal with
              [|- match ?Expr with _ => _ end] => destruct Expr
            end; constructor.
            rewrite gsoLockSet_2; auto.
            rewrite gsoThreadLock.
            erewrite <- mem_store_max by eauto.
            rewrite getMax_restr.
            eapply (compat_ls HmemCompF).
      }
      subst.
      eapply Build_sim with (mem_compc := HmemCompC') (mem_compf := HmemCompF'').
      - (* containsThread *)
        clear - HnumThreads.
        intros j.
        split; intros cntj;
        eapply cntUpdateL;
        eapply cntUpdate;
        apply cntUpdateL' in cntj;
        apply cntUpdate' in cntj;
          by eapply HnumThreads.
      - (*safety of coarse machine*)
          by assumption.
      - (* weak simulation between the two machines*)
        intros j pfcj' pffj'.
        assert (pfcj: containsThread tpc j)
          by auto.
        assert (pffj: containsThread tpf j)
          by auto.
        specialize (HsimWeak _ pfcj pffj).
        assert (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b)
          by (
              intros;
              erewrite <- restrPermMap_valid with (Hlt := HmemCompC _ pfc);
              split;
              [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
              eauto).
        assert (Hvb': forall b, ~ Mem.valid_block mc b <-> ~ Mem.valid_block mc' b)
          by (intros; split; intros Hinvalid Hcontra;
                by apply Hvb in Hcontra).
        assert (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b)
          by (
              intros;
              erewrite <- restrPermMap_valid with (Hlt := HmemCompF _ pff);
              split;
              [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
              eauto).
        clear - Hvb Hvb' HvbF HstoreF Hstore HsimWeak Hsim Hfb.
        destruct HsimWeak.
        constructor; intros;
        repeat
          (match goal with
           | [H: context[Mem.valid_block (restrPermMap _) _] |- _] =>
             erewrite restrPermMap_valid in H
           | [H: ~ Mem.valid_block _ _ |- _] =>
             apply Hvb' in H; clear Hvb'
           | [H: Mem.valid_block _ _ |- _] =>
             apply Hvb in H; clear Hvb
           | [|- Mem.valid_block (restrPermMap _) _] =>
             erewrite restrPermMap_valid
           | [|- Mem.valid_block _ _] =>
             eapply HvbF; clear HvbF
           end); eauto;
        try by specialize (codomain_valid0 _ _ H).
        { (* Permissions on coarse machine are higher than permissions on fine*)
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          - (*this is the case where we have reduced some permissions*)
            subst j. 
            do 2 rewrite restrPermMap_Cur.
            do 2 rewrite gLockSetRes.
            do 2 rewrite gssThreadRes.
            (*by case analysis on whether the changed permission are
              at this address*)
            pf_cleanup.
            specialize (perm_obs_weak0 _ _ ofs0 Hrenaming).
            do 2 rewrite restrPermMap_Cur in perm_obs_weak0.
            destruct (Pos.eq_dec b b1) as [? | Hneq].
            + subst.
              assert (b0 = b2)
                by (rewrite Hrenaming in Hfb; inversion Hfb; subst; auto).
              subst b0.
              destruct (Z_le_dec (Int.intval ofs) ofs0).
              * destruct (Z_lt_dec ofs0 ((Int.intval ofs) +
                                         Z.of_nat (lksize.LKSIZE_nat))).
                erewrite setPermBlock_same; eauto.
                erewrite setPermBlock_same; eauto.
                apply po_refl.
                erewrite setPermBlock_other_1; eauto.
                erewrite setPermBlock_other_1; eauto.
              * erewrite setPermBlock_other_1 by (zify; omega); eauto.
                erewrite setPermBlock_other_1 by (zify; omega); eauto.
            +  assert (b0 <> b2)
                by (intros Hcontra; subst;
                    specialize (injective0 _ _ _ Hrenaming Hfb); subst; auto).
              rewrite setPermBlock_other_2; auto.
              rewrite setPermBlock_other_2; auto.
          - do 2 rewrite restrPermMap_Cur.
            rewrite gLockSetRes.
            rewrite gLockSetRes.
            rewrite gsoThreadRes; auto.
            rewrite gsoThreadRes; auto.
            specialize (perm_obs_weak0 _ _ ofs0 Hrenaming).
            do 2 rewrite restrPermMap_Cur in perm_obs_weak0.
            auto.
        }
      - (* Proof of seperation of injections *)
        intros k j cntk' cntj' Hkj b0 b0' b3 b3' Hf0 Hf0' Hfk' Hfj'.
        assert (cntk: containsThread tpc k)
          by auto.
        assert (cntj: containsThread tpc j)
          by auto.
        erewrite cnt_irr with (cnt1 := cntk') (cnt2 := cntk) in Hfk'.
        erewrite cnt_irr with (cnt1 := cntj') (cnt2 := cntj) in Hfj'.
        eapply (HfpSep _ _ cntk cntj Hkj b0 b0');
          by eauto.
      - (* Proof of strong simulations after executing some thread*)
        intros.
        destruct (tid == i) eqn:Htid; move/eqP:Htid=>Htid; subst.
        { (*case of strong simulation for the thread that took the external*)
          exists (updLockSet
               (updThread pfc (Kresume c Vundef)
                          (setPermBlock (Some Nonempty) b (Int.intval ofs)
                                        (getThreadR pfc) lksize.LKSIZE_nat)) 
               (b, Int.intval ofs) empty_map), mc'.
          assert (pfc0 = pfc)
            by (eapply cnt_irr; eauto); subst pfc0.
          rewrite Hsynced.
          repeat (split; (auto || constructor)).
          split; first by apply ren_incr_refl.
          split; first by auto.
          split; first by constructor.
          split.
          intros.
          constructor.
          do 2 rewrite gLockSetCode.
          do 2 rewrite gssThreadCode;
            by (split; [assumption | constructor]).
          eapply mem_obs_eq_makelock; eauto.
          repeat split;
            by congruence.
        }       
        { (*strong simulation for another thread*)
          assert (Hstrong_sim := simStrong Hsim).
          assert (pfcj: containsThread tpc tid)
            by (eapply cntUpdateL' in pfc0;
                 eapply cntUpdate' in pfc0;
                 eauto).
          assert (pffj: containsThread tpf tid)
            by (eapply cntUpdateL' in pff0;
                 eapply cntUpdate' in pff0;
                 eauto).
          specialize (Hstrong_sim _ pfcj pffj).
          destruct Hstrong_sim
            as (tpcj & mcj & Hincrj & Hsyncedj & Hexecj & Htsimj
                & Hownedj & Hownedj_ls & Hownedj_lp).
          (* first we prove that i is a valid thread after executing thread j*)
          assert (pfcij:= containsThread_internal_execution Hexecj pfc).

          (*Proof Sketch: Basically the proof we want is that
            changing some non-observable part of the state/memory
            should not affect the execution of thread j. To avoid
            giving yet another definition of equivalence of the
            observable state we re-use our strong injections. Steps:
            
            1. The original state <tpc,mc> will strongly inject with
            the id injection in the state <tpc', mc'> where we have
            updated the value of the lock and the resource maps
            according to the angel.

            2. Hence if <tpc,mc> takes internal steps to get to <tpcj,
            mcj> so will <tpc',mc'> to go to a new state
            <tpcj',mcj'>. Moreover <tpcj,mcj> will inject to
            <tpcj',mcj'> with the id injection. We had to strengthen
            our lemmas and corestep_obs_eq to obtain that last part.

            3. We use [strong_tsim_id_trans] to get that <tpcj',mcj'>
               will strongly inject in <tpf,mf> with the same
               injection as <tpcj,mcj>.

            4. Finally we prove that changing the state/memory
            in (TODO: add lemma name) non-observable parts retains the
            [strong_tsim] relation. *)

          (* Step 1*)
          assert (pfcjj: containsThread tpcj tid)
            by (eapply containsThread_internal_execution; eauto).
          assert (Hcompj: mem_compatible tpcj mcj)
            by (eapply internal_execution_compatible with (tp := tpc); eauto).
          specialize (Htsimj pfcjj Hcompj).
          (* We prove that thread tid on the original state injects
            in thread tid after updating the lockpool and storing the
            lock value*)
          assert (Htsimj_id:
                    (strong_tsim (id_ren mc) pfcj pfc0 HmemCompC HmemCompC') /\
                    (Mem.nextblock mc = Mem.nextblock mc')).
          { eapply strong_tsim_store_id; eauto.
            erewrite gLockSetRes.
            rewrite gsoThreadRes; eauto.
            erewrite gLockSetCode.
            rewrite gsoThreadCode; eauto.
            destruct HinvC; eauto.
            assert (domain_memren (id_ren mc) mc)
              by (apply id_ren_domain).
            assert (domain_memren (fp i pfc) mc)
              by (apply (mem_obs_eq_domain_ren Hmem_obs_eq)).
            eapply tp_wd_domain;
              by eauto.
          }
          destruct Htsimj_id as [Htsimj_id Hnextblock].
          
          (* Step 2.*)
          assert (H := strong_tsim_execution _ HinvC' Hfg Hge_wd
                                             Hge_incr_id Htsimj_id Hexecj).
          destruct H as
              (tp2' & m2' & f' & Hexecj'& Hincrj' & Hsepj'
               & Hnextblock' & Hinvj' & Htsimj' & Hid').
          destruct Htsimj' as (pf2j & pf2j' & Hcomp2 & Hcomp2' & Htsimj').
          specialize (Hid' Hnextblock (id_ren_correct mc)).
          assert (f' = id_ren mcj)
            by ( pose ((mem_obs_eq_domain_ren (obs_eq Htsimj')));
                 eapply is_id_ren; eauto); subst f'.
          exists tp2', m2'.
          erewrite cnt_irr with (cnt1 := pfc0) (cnt2 := pfcj).
          split; first by auto.
          split; first by auto.
          split; first by auto.
          split.
          (*strong thread simulation for j*)
          intros.
          pf_cleanup.
          (* Step 3, we use transitivity of strong_tsim *)
          assert (Htsim2j: strong_tsim (fp tid pfcj) pf2j' pffj Hcomp2'
                                       (mem_compf Hsim)).
          { eapply strong_tsim_id_trans
            with (f := fp tid pfcj) (Hcomp1 := Hcompj) (Hcomp1' := Hcomp2');
            eauto.
            destruct Hnextblock' as [[p [Hmcj Hm2']] | [Hmcj Hm2']];
              unfold Mem.valid_block;
              rewrite Hmcj Hm2' Hnextblock;
                by tauto.
          }
          (* Step 4*)
          destruct Htsim2j as [Hcodeq2j Hmem_obs_eq2j].
          constructor.
          rewrite gLockSetCode.
          rewrite gsoThreadCode;
            by auto.
          clear - Hmem_obs_eq2j HstoreF HinvF Htid.
          assert (HeqRes: getThreadR pff0 = getThreadR pffj)
            by (rewrite gLockSetRes;
                 rewrite gsoThreadRes; auto).
          assert (Hlt : permMapLt (getThreadR pff0)(getMaxPerm mf))
            by (rewrite HeqRes; destruct HmemCompF; eauto).
          eapply mem_obs_eq_storeF with (mf := mf) (Hlt :=  Hlt);
            eauto.
          destruct HinvF.
          rewrite HeqRes.
          eauto.
          erewrite restrPermMap_irr' with (Hlt := Hlt)
                                           (Hlt' := (mem_compf Hsim) tid pffj);
            by eauto.
          split.
          (*thread ownership*)
          intros k pff2k Hjk b1 b0 ofs0 Hfj Hfi.
          destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
          { subst k.
            rewrite gLockSetRes.
            rewrite gssThreadRes; auto.
            destruct (Pos.eq_dec b0 b2).
            + subst.
              exfalso.
              apply Hincrj in Hfb.
              pose proof ((injective (weak_obs_eq (obs_eq Htsimj))) _ _ _ Hfj Hfb).
              subst b.
              congruence.
            + rewrite setPermBlock_other_2; auto.
              eauto.
          }
          { rewrite gLockSetRes.
            rewrite gsoThreadRes; auto.
            eapply Hownedj;
              by eauto.
          }
          split.
          (* lockset ownership*)
          intros b1 b0 ofs0 Hfj Hfi.
          assert (b2 <> b0).
          { intros ?; subst b0.
            assert (Hfbj := Hincrj _ _ Hfb).
            assert (Heq := injective (weak_obs_eq (obs_eq Htsimj)) _ _ Hfj Hfbj);
              subst b.
              by congruence.
          }
          erewrite <- lockSet_updLockSet; eauto.
          erewrite gsoLockSet_2 by eauto.
          eapply Hownedj_ls;
            by eauto.
          (* lockpool ownership*)
          intros bl ofsl rmap b1 b0 ofs0 Hfj Hfi Hres.
          destruct (EqDec_address (b2, Int.intval ofs) (bl, ofsl)) as [Heq | Hneq].
          (* case rmap is the new resource map*)
          inversion Heq; subst.
          rewrite gssLockRes in Hres.
          inversion Hres;
            by rewrite empty_map_spec.
          (*case it is another resource map*)
          rewrite gsoLockRes in Hres; auto.
          rewrite gsoThreadLPool in Hres;
            by eauto.
          }
      - (* Proof of [strong_mem_obs_eq] for lock set*)
        specialize (HsimWeak _ pfc pff).
        split.
        eapply sync_locks_mem_obs_eq with
        (tpc := tpc) (tpf := tpf) (mc := mc) (mf := mf) (rmap := empty_map); eauto.
        erewrite <- lockSet_updLockSet; eauto.
        erewrite <- lockSet_updLockSet; eauto.
        intros bl2 ofs0 Hres.
        destruct (EqDec_address (bl2, ofs0) (b2, Int.intval ofs)) as [Heq | Hneq].
        inversion Heq; subst.
        eexists;
          by eauto.
        rewrite gsoLockRes in Hres; auto.
        rewrite gsoThreadLPool in Hres.
        eapply HLocksInv;
          by eauto.
      - (* Proof of [strong_mem_obs_eq] for lock pool*)
        split.
        + intros bl1 bl2 ofs0 rmap1 rmap2 Hfi Hres1 Hres2.
          destruct (EqDec_address (b, Int.intval ofs) (bl1, ofs0)) as [Heq | Hneq].
          { (*case it is the new lock *)
            inversion Heq; subst.
            assert (bl2 = b2)
              by (rewrite Hfi in Hfb; by inversion Hfb).
            subst bl2.
            constructor.
            intros b1 b0 ofs0 Hf1.
            do 2 rewrite restrPermMap_Cur.
            rewrite gssLockRes in Hres1.
            rewrite gssLockRes in Hres2.
            inversion Hres1; inversion Hres2.
            do 2 rewrite empty_map_spec;
              by reflexivity.
            intros b1 b0 ofs0 Hf1 Hperm.
            assert (H:= restrPermMap_Cur (compat_lp HmemCompC' (bl1, Int.intval ofs)
                                                    Hres1) b1 ofs0).
            unfold permission_at in H.
            unfold Mem.perm in Hperm.
            rewrite H in Hperm.
            clear H.
            exfalso.
            rewrite gssLockRes in Hres1.
            inversion Hres1; subst.
            rewrite empty_map_spec in Hperm.
            simpl in Hperm;
              by auto.
          }
          { (*case it's another lock*)
            assert ((b2, Int.intval ofs) <> (bl2, ofs0)).
            { clear - Hneq Hfi Hf Hfb Hmem_obs_eq.
              intros Hcontra; inversion Hcontra; subst.
              assert (b = bl1)
                by (eapply (injective (weak_obs_eq Hmem_obs_eq)); eauto).
              subst;
                by auto.
            }
            constructor.
            intros b1 b0 ofs1 Hf1.
            do 2 rewrite restrPermMap_Cur.
            rewrite gsoLockRes in Hres1; auto.
            rewrite gsoLockRes in Hres2; auto.
            rewrite gsoThreadLPool in Hres1.
            rewrite gsoThreadLPool in Hres2.
            specialize (HsimRes _ _ _ _ _ Hfi Hres1 Hres2).
            destruct HsimRes as [HpermRes HvalRes].
            specialize (HpermRes _ _ ofs1 Hf1);
              by do 2 rewrite restrPermMap_Cur in HpermRes.
            intros b1 b0 ofs1 Hf1 Hperm.
            unfold Mem.perm in *.
            assert (Hperm_eq:= restrPermMap_Cur
                                 (compat_lp HmemCompC' (bl1, ofs0) Hres1) b1 ofs1).
            unfold permission_at in Hperm_eq.
            rewrite Hperm_eq in Hperm.
            clear Hperm_eq.
            simpl.
            rewrite gsoLockRes in Hres1; auto.
            rewrite gsoLockRes in Hres2; auto.
            rewrite gsoThreadLPool in Hres1.
            rewrite gsoThreadLPool in Hres2.
            specialize (HsimRes _ _ _ _ _ Hfi Hres1 Hres2).
            destruct HsimRes as [HpermRes HvalRes].
            unfold Mem.perm in HvalRes.
            assert (Hperm_eq:= restrPermMap_Cur
                                 (compat_lp HmemCompC (bl1, ofs0) Hres1) b1 ofs1).
            unfold permission_at in Hperm_eq.
            specialize (HvalRes _ _ ofs1 Hf1).
            rewrite Hperm_eq in HvalRes.
            specialize (HvalRes Hperm). simpl in HvalRes.
            eapply gsoMem_obs_eq with (HltC := HmemCompC _ pfc)
                                        (HltF := HmemCompF _ pff)
                                        (bl1 := b) (bl2 := b2); eauto.
            apply permMapsDisjoint_comm.
            eapply (lock_res_threads HinvC); eauto.
          }
        + intros bl1 bl2 ofs0 Hfl1.
          destruct (EqDec_address (b, Int.intval ofs) (bl1, ofs0)).
          * inversion e; subst.
            assert (b2 = bl2)
              by (rewrite Hf in Hfl1; inversion Hfl1; subst; auto).
            subst.
            do 2 rewrite gsslockResUpdLock.
            split;
            auto.
          * erewrite gsolockResUpdLock by eauto.
            assert ((b2, Int.intval ofs) <> (bl2, ofs0)).
            { intros Hcontra; inversion Hcontra; subst.
              specialize (Hinjective _ _ _ Hfb Hfl1).
              subst; auto.
            }
            erewrite gsolockResUpdLock by eauto.
            do 2 rewrite gsoThreadLPool.
            eapply Hlock_if;
            eauto.
        - (* Proof of invariant preservation for fine-grained machine*)
          clear - HinvF HstoreF HinvC' Hlock_if Hf.
          eapply invariant_mklock; eauto.
          apply Mem.store_valid_access_3 in HstoreF.
          destruct HstoreF.
          intros ofs0 Hin.
          simpl in *.
          specialize (H ofs0 Hin).
          unfold Mem.perm in H.
          erewrite <- restrPermMap_Cur with (Hlt := HmemCompF i pff).
          unfold permission_at.
          auto.
        - (* Max permission invariant*)
            by assumption.
        - (* new memory is well-defined*)
          eapply store_wd_domain
          with (m := (restrPermMap (HmemCompC i pfc))); eauto.
            by simpl.
        - (* new tpc well defined*)
          apply tp_wd_lockSet.
          intros j cntj'.
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          subst. rewrite gssThreadCode.
          specialize (Htpc_wd _ pfc).
          rewrite Hcode in Htpc_wd.
          simpl in *;
            by auto.
          assert (cntj := cntUpdate' _ _ _ cntj').
          erewrite @gsoThreadCode with (cntj := cntj) by assumption.
          specialize (Htpc_wd _ cntj).
            by auto.
        - (*ge well defined*)
          assumption.
        - (*ge spec*)
          split; assumption.
        - intros.
          apply cntUpdateL;
            apply cntUpdate;
              by eauto.
    }
    { (* Freelock case*)
      subst mc'.
      destruct Htsim as [Hcore_inj Hmem_obs_eq].
      (* We have that the code of the fine grained execution
        is related to the one of the coarse-grained*)
      rewrite Hcode in Hcore_inj.
      simpl in Hcore_inj.
      destruct (getThreadC pff) as [? | cf |? | ?] eqn:HcodeF;
        try by exfalso.
      (* And now we can prove that cf is also at external *)
      assert (Hat_external_spec := core_inj_ext Hcore_inj).
      rewrite Hat_external in Hat_external_spec.
      destruct (at_external SEM.Sem cf) as [[[? ?] vsf]|] eqn:Hat_externalF;
        try by exfalso.
      (* and moreover that it's the same external and their
        arguments are related by the injection*)
      destruct Hat_external_spec as [? [? Harg_obs]]; subst.
      inversion Harg_obs as [|? ? ? ? Hptr_obs Hl]; subst.
      inversion Hl; subst.
      inversion Hptr_obs as [| | | |b1 b2 ofs0 Hf|];
        subst b1 ofs0 v'.
      
      (* The permission at the lock location will be writable*)
      assert (Hlock_perm := lockSet_spec_1 _ _ _ His_lock).
      (* The fine-grain execution will also have a writable permission
      at the mapped address *)
      destruct HsimLocks as [HpermLS HvalLS].
      assert (His_lockF := HpermLS _ _ (Int.intval ofs) Hf).
      do 2 rewrite restrPermMap_Cur in His_lockF.
      rewrite Hlock_perm in His_lockF.
      specialize (fst (Hlock_if _ _ (Int.intval ofs) Hf) His_lock).
      destruct (lockRes tpf (b2, Int.intval ofs)) as [rmap2|] eqn:HresF;
        try discriminate.
      (* To compute the new fine grained state, we apply the
        renaming to the resources the angel provided us*)
      remember (projectAngel (fp i pfc) virtue) as virtueF eqn:HvirtueF.
      remember (updThread pff (Kresume cf Vundef)
                          (computeMap (getThreadR pff) virtueF))
        as tpf' eqn:Htpf'.
      (* We prove the specification for the new permissions that the
      angel installed*)
      assert (HchangedF: forall ofs' : Z,
                 Intv.In ofs'
                             (Int.intval ofs,
                              (Int.intval ofs + Z.of_nat lksize.LKSIZE_nat)%Z) ->
                 Mem.perm_order'
                   ((computeMap (getThreadR pff) virtueF) # b2 ofs') Writable).
      { intros ofs' Hofs'.
        subst.
        specialize (Hchanged _ Hofs').
        erewrite computeMap_projection_1; eauto.
      }
      assert (HunchangedF: forall (b' : block) (ofs' : Z),
                 b2 = b' /\
                 ~
                   Intv.In ofs'
                   (Int.intval ofs,
                    (Int.intval ofs + Z.of_nat lksize.LKSIZE_nat)%Z) \/ 
                 b2 <> b' ->
                 (computeMap (getThreadR pff) virtueF) # b' ofs' =
                 (getThreadR pff) # b' ofs').
      { intros b' ofs' Hb_ofs.
        inversion Hmem_obs_eq as [? [Hperm_eq Hval_eq]].
        destruct Hb_ofs as [[Hb Hofs'] | Hb].
        - specialize (Hunchanged b ofs' (or_introl (conj Logic.eq_refl Hofs'))).
          subst.
          erewrite computeMap_projection_1; eauto.
          specialize (Hperm_eq _ _ ofs' Hf).
          do 2 rewrite restrPermMap_Cur in Hperm_eq.
          rewrite Hperm_eq; auto.
        - assert (Hb': (exists b1, (fp i pfc) b1 = Some b') \/
                       ~ (exists b1, (fp i pfc) b1 = Some b'))
            by eapply em.
          subst.
          destruct Hb' as [Hbm' | Hbu'].
          + destruct Hbm' as [b1' Hf'].
            assert (b <> b1')
              by (intros Hcontra; subst;
                  rewrite Hf in Hf'; inversion Hf'; auto).
            specialize (Hunchanged b1' ofs' (or_intror H)).
            erewrite computeMap_projection_1; eauto.
            specialize (Hperm_eq _ _ ofs' Hf').
            do 2 rewrite restrPermMap_Cur in Hperm_eq.
            rewrite Hperm_eq; auto.
          + erewrite computeMap_projection_2; eauto.
      }
      (* we remove the lock from the fine-grained machine*)
      remember (remLockSet tpf' (b2, Int.intval ofs)) as tpf'' eqn:Htpf''.
      exists tpf'', mf, (fp i pfc), fp, (tr ++ [:: (external i (freelock (b2, Int.intval ofs)))]).
      split.
      (* proof that the fine grained machine can step*)
      intros U.
      assert (HsyncStepF: syncStep the_ge pff HmemCompF tpf'' mf (freelock (b2, Int.intval ofs)))
        by (eapply step_freelock with (b:=b2); eauto;
            rewrite HresF; eauto).
      econstructor; simpl;
        by eauto.
      (* Proof that the new coarse and fine state are in simulation*)
      assert (HinvC':
                invariant (remLockSet
                             (updThread pfc (Kresume c Vundef)
                                        (computeMap (getThreadR pfc) virtue)) 
                             (b, Int.intval ofs)))
        by  (eapply safeC_invariant with (n := fuelF.+1 + size xs); eauto).
      assert (HlockRes_valid:  lr_valid
                                 (lockRes
                                    (updThread pff (Kresume cf Vundef)
                                               (computeMap (getThreadR pff) (projectAngel (fp i pfc) virtue))))).
      { intros b0 ofs0.
        rewrite gsoThreadLPool.
        pose proof (lockRes_valid HinvF).
        specialize (H0 b0 ofs0). eauto.
        }
                    
      (* mem_compatible is easily derived as permissions only changed
      at the lock permission and will always be below freeable*)
      assert (HmemCompF' : mem_compatible tpf'' mf).
      { subst.
        constructor.
        {intros j pffj.
         rewrite gRemLockSetRes.
         destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
         - subst j.
           rewrite gssThreadRes.
           intros b' ofs'.
           destruct (Pos.eq_dec b2 b').
           + subst.
             apply (codomain_valid (weak_obs_eq Hmem_obs_eq)) in Hf.
             erewrite restrPermMap_valid in Hf.
             specialize (HmaxF _ ofs' Hf).
             rewrite getMaxPerm_correct HmaxF; simpl.
             destruct ((computeMap (getThreadR pff)
                                   (projectAngel (fp i pfc) virtue)) # b'
                                                                     ofs');
               constructor.
           + specialize (HunchangedF b' ofs' (or_intror n)).
             rewrite HunchangedF.
             pose proof (HmemCompF _ pff b' ofs'); auto.
         - rewrite gsoThreadRes; auto.
           pose proof (HmemCompF _ pffj); auto.
        }
        { intros (bl' & ofsl') rmap' Hres'.
          destruct (EqDec_address (b2, Int.intval ofs) (bl', ofsl')) as [Heq |Hneq].
          - inversion Heq; subst.
            rewrite gsslockResRemLock in Hres';
              by discriminate.
          - rewrite gsolockResRemLock in Hres'; auto.
            rewrite gsoThreadLPool in Hres'.
            eapply (compat_lp HmemCompF); eauto.
        }
        { intros bl' ofsl'.
          destruct (Pos.eq_dec b2 bl') as [Heq | Hneq].
          - subst.
            destruct (Intv.In_dec ofsl' (Int.intval ofs,
                                         ((Int.intval ofs) + lksize.LKSIZE)%Z)).
            + erewrite gsslockSet_rem; eauto.
              destruct ((getMaxPerm mf) # bl' ofsl'); simpl; auto.
              rewrite gsoThreadLPool.
              rewrite HresF; auto.
            + erewrite gsolockSet_rem2 by eauto.
              rewrite gsoThreadLock.
              eapply (compat_ls HmemCompF).
          - erewrite gsolockSet_rem1; eauto.
            rewrite gsoThreadLock.
            eapply (compat_ls HmemCompF).
        }
      }
      subst.
      (* The permissions for mapped block for thread i will remain equal*)
      assert (Hpermi_eq:
                forall (pfci': containsThread
                            (remLockSet
                               (updThread pfc (Kresume c Vundef)
                                          (computeMap (getThreadR pfc) virtue)) 
                               (b, Int.intval ofs)) i)
                  (pffi': containsThread
                            (remLockSet
                               (updThread pff (Kresume cf Vundef)
                                          (computeMap (getThreadR pff)
                                                      (projectAngel (fp i pfc) virtue))) 
                               (b2, Int.intval ofs)) i)
                  b1 b2 ofs,
                  fp i pfc b1 = Some b2 ->
                  permission_at (restrPermMap (HmemCompC' _ pfci')) b1 ofs Cur =
                  permission_at (restrPermMap (HmemCompF' _ pffi')) b2 ofs Cur).
      { clear - Hf HchangedF HunchangedF Hunchanged Hchanged Hmem_obs_eq.
        intros pfci' pffi' b0 b0' ofs' Hf0.
        do 2 rewrite restrPermMap_Cur gRemLockSetRes gssThreadRes.
        erewrite computeMap_projection_1; eauto.
      }
      eapply Build_sim with (mem_compc := HmemCompC') (mem_compf := HmemCompF').
      - (* containsThread *)
        clear - HnumThreads.
        intros j.
        split; intros cntj;
        eapply cntRemoveL;
        eapply cntUpdate;
        apply cntRemoveL' in cntj;
        apply cntUpdate' in cntj;
          by eapply HnumThreads.
      - (*safety of coarse machine*)
          by assumption.
      - (* weak simulation between the two machines*)
        intros j pfcj' pffj'.
        assert (pfcj: containsThread tpc j)
          by auto.
        assert (pffj: containsThread tpf j)
          by auto.
        specialize (HsimWeak _ pfcj pffj).
        clear - HsimWeak Hsim Hf Hpermi_eq.
        destruct HsimWeak.
        constructor; intros;
        repeat
          (match goal with
           | [H: context[Mem.valid_block (restrPermMap _) _] |- _] =>
             erewrite restrPermMap_valid in H
           | [|- Mem.valid_block (restrPermMap _) _] =>
             erewrite restrPermMap_valid
           end); eauto;
        try by specialize (codomain_valid0 _ _ H).
        (* Permissions on coarse machine are higher than permissions on fine*)
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        + (*this is the case where we have increased some permissions*)
          subst j.
          erewrite Hpermi_eq with (pffi' := pffj') by eauto.
          apply po_refl.
        + do 2 rewrite restrPermMap_Cur gRemLockSetRes.
          erewrite gsoThreadRes with (cntj := pfcj) by eauto.
          erewrite gsoThreadRes with (cntj := pffj) by eauto.
          specialize (perm_obs_weak0 _ _ ofs0 Hrenaming).
          do 2 rewrite restrPermMap_Cur in perm_obs_weak0;
            auto.
      - (* Proof of seperation of injections *)
        intros k j cntk' cntj' Hkj b0 b0' b3 b3' Hf0 Hf0' Hfk' Hfj'.
        assert (cntk: containsThread tpc k)
          by auto.
        assert (cntj: containsThread tpc j)
          by auto.
        erewrite cnt_irr with (cnt1 := cntk') (cnt2 := cntk) in Hfk'.
        erewrite cnt_irr with (cnt1 := cntj') (cnt2 := cntj) in Hfj'.
        eapply (HfpSep _ _ cntk cntj Hkj b0 b0');
          by eauto.
      - (* Proof of strong simulations after executing some thread*)
        intros.
        destruct (tid == i) eqn:Htid; move/eqP:Htid=>Htid; subst.
        { (*case of strong simulation for the thread that took the external*)
          exists (remLockSet
                (updThread pfc (Kresume c Vundef)
                   (computeMap (getThreadR pfc) virtue)) 
                (b, Int.intval ofs)), mc.
          assert (pfc0 = pfc)
            by (eapply cnt_irr; eauto); subst pfc0.
          assert (pff0 = pff)
            by (eapply cnt_irr; eauto); subst pff0.
          rewrite Hsynced.
          repeat (split; (auto || constructor)).
          split; first by apply ren_incr_refl.
          split; first by auto.
          split; first by constructor.
          split.
          intros.
          constructor.
          do 2 rewrite gRemLockSetCode.
          do 2 rewrite gssThreadCode;
            by (split; [assumption | constructor]).
          (* proof of mem_obs_eq *)
          constructor.
          specialize (HsimWeak _ pfc pff).
          clear - HsimWeak Hsim Hf Hpermi_eq.
          destruct HsimWeak.
          constructor; intros;
          repeat
            (match goal with
             | [H: context[Mem.valid_block (restrPermMap _) _] |- _] =>
               erewrite restrPermMap_valid in H
             | [|- Mem.valid_block (restrPermMap _) _] =>
               erewrite restrPermMap_valid
             end); eauto;
          try by specialize (codomain_valid0 _ _ H).
          (* Permissions on coarse machine are higher than permissions on fine*)
          specialize (Hpermi_eq pfc' pff b1 b0 ofs0 Hrenaming).
          pf_cleanup.
          erewrite Hpermi_eq by eauto.
          apply po_refl.
          constructor.
          intros.
          specialize (Hpermi_eq pfc' pff b1 b0 ofs0 Hrenaming).
          pf_cleanup.
          erewrite Hpermi_eq by eauto.
          reflexivity.
          (* val_obs_eq proof *)
          (* For this one, we have to do a case analysis to see
          whether the addr is one that has been increased. If so, it
          implies that it was above readable in the lockset and hence
          we can get the val_obs_eq property from there. *)
          clear - Hmem_obs_eq Hsim Hf Hpermi_eq Hchanged His_lock HresF
                              Hunchanged Hlock_perm HpermLS HvalLS.
          intros.
          simpl.
          assert (Hperm_eq := restrPermMap_Cur (mem_compc' i pfc') b1 ofs0).
          unfold permission_at in Hperm_eq.
          unfold Mem.perm in *.
          rewrite Hperm_eq in Hperm.
          destruct (Pos.eq_dec b b1) as [Heq | Hneq].
          - subst.
            destruct (Intv.In_dec ofs0
                                  (Int.intval ofs,
                                   (Int.intval ofs + Z.of_nat lksize.LKSIZE_nat)%Z)).
            + (* look at lockset*)
              eapply lockSet_spec_2 in His_lock; eauto.
              specialize (HvalLS _ _ ofs0 Hrenaming).
              rewrite <- restrPermMap_Cur with (Hlt := compat_ls HmemCompC)
                in His_lock.
              unfold permission_at in His_lock.
              rewrite His_lock in HvalLS.
              simpl in HvalLS.
              eapply HvalLS; constructor.
            + (* at this address, the thread permissions are unchanged so use that*)
              specialize (Hunchanged b1 ofs0 (or_introl (conj Logic.eq_refl n))).
              rewrite gRemLockSetRes gssThreadRes Hunchanged in Hperm.
              pose proof (val_obs_eq (strong_obs_eq Hmem_obs_eq)).
              simpl in H.
              rewrite <- restrPermMap_Cur with (Hlt := HmemCompC _ pfc) in Hperm.
              unfold Mem.perm in H.
              eapply H; eauto.
          - specialize (Hunchanged b1 ofs0 (or_intror Hneq)).
            rewrite gRemLockSetRes gssThreadRes Hunchanged in Hperm.
            pose proof (val_obs_eq (strong_obs_eq Hmem_obs_eq)).
            simpl in H.
            rewrite <- restrPermMap_Cur with (Hlt := HmemCompC _ pfc) in Hperm.
            unfold Mem.perm in H.
            eapply H; eauto.              
            repeat split;
              by congruence.
        }       
        { (*strong simulation for another thread*)
          assert (Hstrong_sim := simStrong Hsim).
          assert (pfcj: containsThread tpc tid)
            by (eapply cntRemoveL' in pfc0;
                 eapply cntUpdate' in pfc0;
                 eauto).
          assert (pffj: containsThread tpf tid)
            by (eapply cntRemoveL' in pff0;
                 eapply cntUpdate' in pff0;
                 eauto).
          specialize (Hstrong_sim _ pfc0 pffj).
          destruct Hstrong_sim
            as (tpcj & mcj & Hincrj & Hsyncedj & Hexecj & Htsimj
                & Hownedj & Hownedj_ls & Hownedj_lp).
          (* first we prove that i is a valid thread after executing thread j*)
          assert (pfcij:= containsThread_internal_execution Hexecj pfc).
          exists (remLockSet
                (updThread pfcij (Kresume c Vundef)
                           (computeMap (getThreadR pfc) virtue)) 
                (b, Int.intval ofs)), mcj.
          split; eauto.
          split; eauto.
          split.
          do 2 rewrite remLock_updThread_comm.
          eapply updThread_internal_execution; eauto.
          eapply remLock_internal_execution; eauto.
          apply mem_compatible_remlock; auto.
            by pose proof (lockRes_valid HinvC).
          split.
          (* strong_tsim *)
          intros.
          assert (Hcompj: mem_compatible tpcj mcj)
            by (eapply internal_execution_compatible with (tp := tpc); eauto).
          specialize (Htsimj pfc' Hcompj).
          destruct Htsimj as [Hcorej Hmem_obs_eqj].
          constructor.

          rewrite gRemLockSetCode.
          rewrite gsoThreadCode; auto.
          rewrite gRemLockSetCode.
          rewrite gsoThreadCode; auto.
          erewrite restrPermMap_irr' with (Hlt := mem_compc' tid pfc')
                                            (Hlt' := Hcompj tid pfc').
          erewrite restrPermMap_irr' with (Hlt := HmemCompF' tid pff0)
                                            (Hlt' := (mem_compf Hsim) tid pffj).
          eauto.
          rewrite gRemLockSetRes; auto.
          rewrite gsoThreadRes; auto.
          rewrite gRemLockSetRes; auto.
          rewrite gsoThreadRes; auto.
          split.
          intros.
          rewrite gRemLockSetRes.
          destruct (i == tid2) eqn:Hi2; move/eqP:Hi2=>Hi2.
          { subst tid2.
            rewrite gssThreadRes.
            destruct (Pos.eq_dec b2 b0).
            - subst.
              assert (b = b1).
              { apply Hincrj in Hf.
                assert (HmemCompCj: mem_compatible tpcj mcj).
                eapply internal_execution_compatible with (tp := tpc); eauto.
                specialize (Htsimj (containsThread_internal_execution Hexecj pfcj)
                                   HmemCompCj).
                destruct Htsimj as [_ [Hweakj Hstrongj]].
                destruct Hweakj.
                eapply injective0; eauto.
              }
              subst b1. congruence.
            - specialize (HunchangedF _ ofs0 (or_intror n)).
              rewrite HunchangedF.
              eapply Hownedj; eauto.
          }
          { rewrite gsoThreadRes; auto.
            eapply Hownedj; eauto.
          }
          split.
          (*lockset ownership*)
          { intros.
            destruct (Pos.eq_dec b2 b0).
            - subst.
              destruct (Intv.In_dec ofs0 (Int.intval ofs,
                                          ((Int.intval ofs) + lksize.LKSIZE)%Z)).
              + erewrite gsslockSet_rem; eauto.
                rewrite gsoThreadLPool.
                rewrite HresF; auto.
              + rewrite gsolockSet_rem2; auto.
                rewrite gsoThreadLock.
                eauto.
            - rewrite gsolockSet_rem1; auto.
              rewrite gsoThreadLock;
                eauto.
          }
          (*lockRes ownership*)
          { intros.
            destruct (EqDec_address (b2, Int.intval ofs) (bl, ofsl)).
            - inversion e; subst.
              rewrite gsslockResRemLock in H2.
              discriminate.
            - rewrite gsolockResRemLock in H2; auto.
              rewrite gsoThreadLPool in H2.
              eauto.
          }
        }
        split.
      - (* Proof of [strong_mem_obs_eq] for lock set*)
        specialize (HsimWeak _ pfc pff).
        clear - HpermLS HvalLS Hf HsimWeak HlockRes_valid HinvC HresF His_lock.
        pose proof (lockRes_valid HinvC).
        constructor.
        { intros.
          do 2 rewrite restrPermMap_Cur.
          destruct (Pos.eq_dec b2 b0).
          + subst.
            assert (b = b1)
              by (pose proof ((injective HsimWeak) _ _ _ Hf Hrenaming); by subst).
            subst b1.
            destruct (Intv.In_dec ofs0 (Int.intval ofs,
                                        ((Int.intval ofs) + lksize.LKSIZE)%Z)).
            * rewrite gsslockSet_rem; auto.
              rewrite gsslockSet_rem; auto.
              rewrite gsoThreadLPool.
              rewrite HresF; auto.
            * rewrite gsolockSet_rem2; auto.
              rewrite gsoThreadLock.
              rewrite gsolockSet_rem2; auto.
              rewrite gsoThreadLock.
              specialize (HpermLS _ _ ofs0 Hrenaming).
              do 2 rewrite restrPermMap_Cur in HpermLS.
              auto.
          + assert (b <> b1)
              by (intros Hcontra; subst;
                  rewrite Hrenaming in Hf; inversion Hf; by subst).
            rewrite gsolockSet_rem1; auto.
            rewrite gsoThreadLock.
            rewrite gsolockSet_rem1; auto.
            rewrite gsoThreadLock.
            specialize (HpermLS _ _ ofs0 Hrenaming).
            do 2 rewrite restrPermMap_Cur in HpermLS.
            auto.
        }
        { intros.
          simpl.
          unfold Mem.perm in *.
          assert (Hperm_eq' := restrPermMap_Cur (compat_ls HmemCompC') b1 ofs0).
          assert (Hperm_eq := restrPermMap_Cur (compat_ls HmemCompC) b1 ofs0).
          unfold permission_at in *.
          rewrite Hperm_eq' in Hperm.
          specialize (HvalLS _ _ ofs0 Hrenaming).
          rewrite Hperm_eq in HvalLS.
          destruct (Pos.eq_dec b1 b).
          - subst.
            destruct (Intv.In_dec ofs0 (Int.intval ofs,
                                        ((Int.intval ofs) + lksize.LKSIZE)%Z)).
            * rewrite gsslockSet_rem in Hperm; auto.
              simpl in Hperm; by exfalso.
            * rewrite gsolockSet_rem2 in Hperm; auto.
          - rewrite gsolockSet_rem1 in Hperm; auto.
        }
        { (* lockRes mapped*)
        intros bl2 ofs0 Hres.
        destruct (EqDec_address (b2, Int.intval ofs) (bl2, ofs0)).
        - inversion e; subst.
          eexists; eauto.
        - rewrite gsolockResRemLock in Hres; auto.
          rewrite gsoThreadLPool in Hres.
          eauto.
        }
        split.
      - (* Proof of [strong_mem_obs_eq] for lock pool*)
        intros bl1 bl2 ofs0 rmap1' rmap2' Hfi Hres1' Hres2'.
        destruct (EqDec_address (b, Int.intval ofs) (bl1, ofs0)) as [Heq | Hneq].
        { (*case it is the  removed lock *)
          exfalso.
          inversion Heq; subst.
          rewrite gsslockResRemLock in Hres1'.
          discriminate.
        }
        { assert (Hneq2: (b2, Int.intval ofs) <> (bl2, ofs0)).
          { intros Hcontra; inversion Hcontra; subst.
            rewrite gsslockResRemLock in Hres2'.
            discriminate. }
          assert (Hres1: lockRes tpc (bl1, ofs0) = Some rmap1')
            by ( rewrite gsolockResRemLock in Hres1'; auto;
                 rewrite gsoThreadLPool in Hres1'; auto).
          assert (Hres2: lockRes tpf (bl2, ofs0) = Some rmap2')
            by ( rewrite gsolockResRemLock in Hres2'; auto;
                 rewrite gsoThreadLPool in Hres2'; auto).
          assert (Heq: restrPermMap (compat_lp HmemCompC' (bl1, ofs0) Hres1') =
                       restrPermMap (compat_lp HmemCompC (bl1, ofs0) Hres1))
            by (erewrite restrPermMap_irr'; eauto).
          assert (HeqF: restrPermMap (compat_lp HmemCompF' (bl2, ofs0) Hres2') =
                       restrPermMap (compat_lp HmemCompF (bl2, ofs0) Hres2))
            by (erewrite restrPermMap_irr'; eauto).
          rewrite Heq HeqF.
          eauto.
        }
        { intros bl1 bl2 ofs0 Hrenaming.
          destruct (EqDec_address (b, Int.intval ofs) (bl1, ofs0)) as [Heq | Hneq].
          - (*case it is the  removed lock *)
            inversion Heq; subst.
            assert (b2 = bl2)
              by (rewrite Hf in Hrenaming; inversion Hrenaming; by subst).
            subst bl2.
            split; intro Hcontra;
            inversion Heq; subst;
            rewrite gsslockResRemLock in Hcontra;
              by exfalso.
          - assert (Hneq2: (b2, Int.intval ofs) <> (bl2, ofs0))
              by (intros Hcontra; inversion Hcontra; subst;
                  specialize (Hinjective _ _ _ Hf Hrenaming); by subst).
            rewrite gsolockResRemLock; auto.
            rewrite gsoThreadLPool.
            rewrite gsolockResRemLock; auto.
            rewrite gsoThreadLPool.
            eauto.
        }
      - (* Proof of invariant preservation for fine-grained machine*)
        clear - HinvF HresF  His_lock HinvC' Hf HunchangedF HchangedF HnumThreads
                      HsimWeak HsimRes HpermLS Hpermi_eq Hmem_obs_eq
                      Hlock_if HLocksInv HlockRes_valid HinvC.
        assert (HlockRes_validC:  lr_valid
                                   (lockRes
                                      (updThread pfc (Kresume c Vundef)
                                                 (computeMap (getThreadR pfc) virtue)))).
        { intros b0 ofs0.
          rewrite gsoThreadLPool.
          pose proof (lockRes_valid HinvC).
          specialize (H b0 ofs0). eauto.
        }
        constructor.
        { (* threads don't race *)
          intros j k cntj cntk Hjk.
          assert (pfck : containsThread tpc k)
            by (eapply HnumThreads; eauto).
          assert (pfcj : containsThread tpc j)
            by (eapply HnumThreads; eauto).
          destruct HinvC' as [HinvC' _ _ _].
          rewrite gRemLockSetRes.
          rewrite gRemLockSetRes.
          assert (forall (pffi' :
                       containsThread (updThread
                                            pff (Kresume cf Vundef)
                                            (computeMap (getThreadR pff)
                                                        (projectAngel (fp i pfc)
                                                                      virtue))) i) x
                    (pffx':
                       containsThread (updThread
                                            pff (Kresume cf Vundef)
                                            (computeMap (getThreadR pff)
                                                        (projectAngel (fp i pfc)
                                                                      virtue))) x),
                     i <> x ->
                     permMapsDisjoint (getThreadR pffi') (getThreadR pffx')).
          { intros.
            rewrite gssThreadRes.
            rewrite gsoThreadRes; auto.
            assert (pfcx : containsThread tpc x)
              by (eapply cntUpdate' in pffx'; eauto;
                   eapply HnumThreads; auto).
            specialize (HsimWeak _ pfcx pffx').
            intros b2' ofs'.
            destruct (Pos.eq_dec b2' b2).
            + subst.
              destruct (Intv.In_dec ofs' (Int.intval ofs,
                                          ((Int.intval ofs) + lksize.LKSIZE)%Z)).
              * specialize (Hpermi_eq pfc pffi' _ _ ofs' Hf).
                erewrite computeMap_projection_1; eauto.
                do 2 rewrite restrPermMap_Cur in Hpermi_eq.
                rewrite gRemLockSetRes in Hpermi_eq.
                rewrite gssThreadRes in Hpermi_eq.
                pose proof ((perm_obs_weak HsimWeak) _ _ ofs' Hf) as Hlt.
                do 2 rewrite restrPermMap_Cur in Hlt.
                specialize (HinvC' _ _ pfc pfcx H b ofs').
                rewrite gRemLockSetRes in HinvC'.
                rewrite gssThreadRes in HinvC'.
                eapply perm_union_lower; eauto.
                rewrite gRemLockSetRes; rewrite gsoThreadRes; auto.
              * erewrite HunchangedF; eauto.
                pose proof ((no_race HinvF) _ _ pff pffx' H).
                eauto.
            + erewrite HunchangedF; eauto.
              pose proof ((no_race HinvF) _ _ pff pffx' H).
              eauto.
          }
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          - subst.
            eapply H; eauto.
          - destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
            + subst.
              apply permMapsDisjoint_comm.
              eapply H; eauto.
            + rewrite gsoThreadRes; auto.
              rewrite gsoThreadRes; auto.
              eapply HinvF; eauto.
        }
        { intros j pffj'.
          intros b2' ofs'.
          destruct HinvC' as [_ HinvC' _ _].
          assert (pffj: containsThread tpf j)
            by eauto.
          assert (pfcj: containsThread tpc j)
            by (eapply HnumThreads; eauto).
          assert (pfcj': containsThread
                           (remLockSet
                              (updThread pfc (Kresume c Vundef)
                                         (computeMap (getThreadR pfc) virtue))
                              (b, Int.intval ofs)) j)
            by (eapply cntRemoveL; eapply cntRemoveL' in pffj';
                eapply cntUpdate' in pffj'; eauto).
          rewrite gRemLockSetRes.
          destruct (Pos.eq_dec b2 b2').
          - subst.
            destruct (Intv.In_dec ofs' (Int.intval ofs,
                                        ((Int.intval ofs) + lksize.LKSIZE)%Z)).
            + erewrite gsslockSet_rem; eauto.
              eapply not_racy_union; constructor.
              rewrite gsoThreadLPool.
              rewrite HresF; auto.
            + erewrite gsolockSet_rem2 by eauto.
              rewrite gsoThreadLock.
              specialize (HpermLS _ _ ofs' Hf).
              do 2 rewrite restrPermMap_Cur in HpermLS.
              rewrite HpermLS.
              specialize (HinvC' _ pfcj' b ofs').
              rewrite gRemLockSetRes in HinvC'.
              erewrite gsolockSet_rem2 in HinvC' by eauto.
              rewrite gsoThreadLock in HinvC'.
              destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
              * subst.
                rewrite gssThreadRes.
                specialize (Hpermi_eq pfcj' pffj' _ _ ofs' Hf).
                do 2 rewrite restrPermMap_Cur in Hpermi_eq.
                rewrite gRemLockSetRes in Hpermi_eq.
                rewrite gRemLockSetRes in Hpermi_eq.
                rewrite gssThreadRes in Hpermi_eq.
                rewrite gssThreadRes in Hpermi_eq.
                rewrite <- Hpermi_eq.
                rewrite gssThreadRes in HinvC'.
                eauto.
              * rewrite gsoThreadRes; auto.
                rewrite gsoThreadRes in HinvC'; auto.
                specialize (HsimWeak _ pfcj pffj).
                pose proof ((perm_obs_weak HsimWeak) _ _ ofs' Hf).
                do 2 rewrite restrPermMap_Cur in H.
                eapply perm_union_lower; eauto.
          - erewrite gsolockSet_rem1 by eauto.
            rewrite gsoThreadLock.
            specialize ((lock_set_threads HinvF) _ pffj b2' ofs');
              eauto.
            destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
            + subst. rewrite gssThreadRes.
              specialize (HunchangedF b2' ofs' (or_intror n)).
              rewrite HunchangedF. eauto.
              pf_cleanup; auto.
            + rewrite gsoThreadRes; eauto.
        }
        { intros (bl' & ofsl') rmap' j pffj' Hres'.
          destruct HinvC' as [_ _ HinvC' _].
          assert (pffj: containsThread tpf j)
            by auto.
          assert (pfcj: containsThread tpc j)
            by ( eapply HnumThreads; eauto).
          assert (pfcj': containsThread
                           (remLockSet
                              (updThread pfc (Kresume c Vundef)
                                         (computeMap (getThreadR pfc) virtue))
                              (b, Int.intval ofs)) j)
            by (eapply cntRemoveL; eapply cntRemoveL' in pffj';
                eapply cntUpdate' in pffj'; eauto).
          rewrite gRemLockSetRes.
          destruct (EqDec_address (b2, Int.intval ofs) (bl', ofsl')).
          - inversion e;
            subst.
            rewrite gsslockResRemLock in Hres';
              discriminate.
          - rewrite gsolockResRemLock in Hres'; auto.
            rewrite gsoThreadLPool in Hres'; auto.
            specialize (HLocksInv bl' ofsl'
                                  ltac:(unfold isSome; rewrite Hres'; auto)).
            destruct HLocksInv as [bl1' Hf'].
            specialize (proj2 (Hlock_if _ _ ofsl' Hf')
                              ltac:(unfold isSome; rewrite Hres'; auto)).
            intros HresC'.
            destruct (lockRes tpc (bl1', ofsl')) as [rmap1'|] eqn:Hres1';
              try by exfalso.
            specialize (HsimRes _ _ _ _ _ Hf' Hres1' Hres').            
            destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
            + subst. rewrite gssThreadRes.
              intros b' ofs'.
              destruct (Pos.eq_dec b2 b').
              * subst.
                specialize (Hpermi_eq pfcj' pffj' _ _ ofs' Hf).
                do 2 rewrite restrPermMap_Cur in Hpermi_eq.
                rewrite gRemLockSetRes in Hpermi_eq.
                rewrite gRemLockSetRes in Hpermi_eq.
                rewrite gssThreadRes in Hpermi_eq.
                rewrite gssThreadRes in Hpermi_eq.
                rewrite <- Hpermi_eq.
                destruct HsimRes as [HpermRes _].
                specialize (HpermRes _ _ ofs' Hf).
                do 2 rewrite restrPermMap_Cur in HpermRes.
                rewrite HpermRes.
                specialize (HinvC' (bl1', ofsl') rmap1' j pfcj').
                assert ((b, Int.intval ofs) <> (bl1', ofsl'))
                  by (intros Hcontra;
                       inversion Hcontra; subst;
                       clear - Hf Hf' n;
                       rewrite Hf' in Hf; inversion Hf; subst; auto).              
                erewrite gsolockResRemLock in HinvC' by eauto.
                rewrite gsoThreadLPool in HinvC'.
                specialize (HinvC' Hres1' b ofs').
                rewrite gRemLockSetRes in HinvC'.
                rewrite gssThreadRes in HinvC';
                  eauto.
              * specialize (HunchangedF _ ofs' (or_intror n0)).
                rewrite HunchangedF.
                pose proof ((lock_res_threads HinvF) _ _ _ pff Hres' b' ofs').
                eauto.
            + rewrite gsoThreadRes; auto.
              pose proof ((lock_res_threads HinvF) _ _ _ pffj Hres').
              eauto.
        }
        { intros (bl & ofsl) rmap Hres.
          destruct (EqDec_address (b2, Int.intval ofs) (bl, ofsl)).
          - inversion e; subst.
            rewrite gsslockResRemLock in Hres; discriminate.
          - erewrite gsolockResRemLock in Hres by eauto.
            rewrite gsoThreadLPool in Hres.
            intros b' ofs'.
            destruct HinvF as [_ _ _ HinvF].
            destruct (Pos.eq_dec b2 b').
            + subst.
              destruct (Intv.In_dec ofs' (Int.intval ofs,
                                          ((Int.intval ofs) + lksize.LKSIZE)%Z)).
              * rewrite gsslockSet_rem; auto.
                rewrite perm_union_comm.
                eapply not_racy_union; constructor.
                rewrite gsoThreadLPool; rewrite HresF; auto.
              * erewrite gsolockSet_rem2 by eauto.
                rewrite gsoThreadLock.
                eapply HinvF; eauto.
            + erewrite gsolockSet_rem1 by eauto.
              rewrite gsoThreadLock.
              eapply HinvF; eauto.
        }
      { subst.
        intros b0 ofs0.
        destruct (lockRes
                    (remLockSet
                       (updThread pff (Kresume cf Vundef)
                                  (computeMap (getThreadR pff)
                                              (projectAngel (fp i pfc) virtue)))
                       (b2, Int.intval ofs)) (b0, ofs0)) eqn:Hres0; auto.
      intros ofs1 Hofs1.
      pose proof (lockRes_valid HinvC') as HlrC'.
      destruct (Pos.eq_dec b0 b2).
      { subst.
        destruct (Z.eq_dec (Int.intval ofs) ofs1).
        - subst.
          specialize (HlrC' b ofs0).
          rewrite gsslockResRemLock. auto.
        - erewrite gsolockResRemLock by
              (intro Hcontra; inversion Hcontra; subst; auto).
          rewrite gsoThreadLPool.
          specialize (HlrC' b2 ofs0).
          destruct (Z.eq_dec (Int.intval ofs) ofs0).
          + subst.
            erewrite gsslockResRemLock in Hres0; discriminate.
          + erewrite gsolockResRemLock in Hres0
              by (intro Hcontra; inversion Hcontra; subst; auto).
            rewrite gsoThreadLPool in Hres0.
            pose proof (lockRes_valid HinvF) as HresValidF.
            specialize (HresValidF b2 ofs0).
            rewrite Hres0 in HresValidF.
            eauto.
      }
      { erewrite gsolockResRemLock
          by (intros Hcontra; inversion Hcontra; subst; auto).
        rewrite gsoThreadLPool.
        erewrite gsolockResRemLock in Hres0
          by (intros Hcontra; inversion Hcontra; subst; auto).
        rewrite gsoThreadLPool in Hres0.
        pose proof (lockRes_valid HinvF) as HresValidF.
        specialize (HresValidF b0 ofs0).
        rewrite Hres0 in HresValidF;
          eauto.
      }
      }
      - (* Max permission invariant*)
          by assumption.
      - (* new memory is well-defined*)
        assumption.
      - (* new tpc well defined*)
        eapply tp_wd_remLock.
        intros j cntj'.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        subst. rewrite gssThreadCode.
        specialize (Htpc_wd _ pfc).
        rewrite Hcode in Htpc_wd.
        simpl in *;
          by auto.
        assert (cntj := cntUpdate' _ _ _ cntj').
        erewrite @gsoThreadCode with (cntj := cntj) by assumption.
        specialize (Htpc_wd _ cntj).
          by auto.
      - (*ge well defined*)
        assumption.
      - (*ge spec*)
        split; assumption.
      - intros.
        apply cntRemoveL;
          apply cntUpdate;
            by eauto.
    }
    { subst tpc' mc'.
      (* We have that the code of the fine grained execution
        is related to the one of the coarse-grained*)
      assert (Hcore_inj:= code_eq Htsim).
      rewrite Hcode in Hcore_inj.
      simpl in Hcore_inj.
      destruct (getThreadC pff) as [? | cf |? | ?] eqn:HcodeF;
        try by exfalso.
      (* And now we can prove that cf is also at external *)
      assert (Hat_external_spec := core_inj_ext Hcore_inj).
      rewrite Hat_external in Hat_external_spec.
      destruct (at_external SEM.Sem cf) as [[[? ?] vsf]|] eqn:Hat_externalF;
        try by exfalso.
      (* and moreover that it's the same external and their
        arguments are related by the injection*)
      destruct Hat_external_spec as [? [? Harg_obs]]; subst.
      inversion Harg_obs as [|? ? ? ? Hptr_obs Hl]; subst.
      inversion Hl; subst.
      inversion Hptr_obs as [| | | |b1 b2 ofs0 Hf|];
        subst b1 ofs0 v'.
      (*We prove that b is valid in m1 (and mc)*)
      remember (restrPermMap (compat_ls HmemCompF)) as mf1 eqn:Hrestrict_pmapF.
      (* and prove that loading from that block in mf gives us the
        same value as in mc, i.e. unlocked*)
      assert (HloadF: Mem.load Mint32 mf1 b2 (Int.intval ofs) = Some (Vint Int.zero)).
      { destruct (load_val_obs _ _ _ Hload Hf Hinjective HsimLocks)
          as [v2 [Hloadf Hobs_eq]].
        inversion Hobs_eq; subst.
          by auto.
      }
      (* The state is not changed by a failed load*)
      exists tpf, mf, (fp i pfc), fp, (tr ++ [:: (external i (failacq (b2, Int.intval ofs)))]).
      split.
      intros U.
      subst.
      econstructor 5; simpl; eauto.
      econstructor 6; eauto.
      (* Proof that the new coarse and fine state are in simulation*)
      eapply sim_reduce; eauto. }
      Unshelve. all:eauto.
Qed.
      
  
End SimProofs.
