(** * DryConc to FineConc simulation*)

Require Import compcert.lib.Axioms.

Require Import VST.concurrency.common.sepcomp.
Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.common.pos.

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
Require Import VST.concurrency.common.addressFiniteMap.
Require Import compcert.lib.Integers.
Require Import VST.concurrency.common.tactics.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.ClassicalFacts.
 

Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.permjoin_def.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.dry_machine_step_lemmas.
Require Import VST.concurrency.common.dry_context.
Require Import VST.concurrency.memory_lemmas.
Require Import VST.concurrency.sc_drf.mem_obs_eq.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Import ThreadPool CoreLanguage AsmContext
       HybridMachine DryHybridMachine HybridMachineSig.
Import CoreInjections ThreadPoolInjections.
(** Step Type Imports*)
Import StepType InternalSteps.
(** Memory Imports*)
Import MemObsEq ValObsEq MemoryLemmas.
Import CoreInjections ValueWD MemoryWD Renamings.

Module SimDefs.

  Section SimDefs.
  Context {asmSem : Semantics}
          {semAxioms : SemAxioms}
          {semDet : SemDet}
          {CI: CoreInj}
          {initU : seq nat}.

  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance DryHybridMachine.DryHybridMachineSig.
  Existing Instance dryFineMach.
  Existing Instance dryCoarseMach.


  (* Machine and Context Imports*)
  (* Import Machine DryMachine ThreadPool AsmContext HybridMachine.Concur.mySchedule. *)
  (* Machine and Context Imports*)

  Notation Sch := schedule.
  Notation CoarseSem := coarse_semantics.


  Notation threadStep := (HybridMachineSig.threadStep the_ge).
  Notation cmachine_step := ((corestep (AsmContext.coarse_semantics initU))).
  Notation fmachine_step := ((corestep (AsmContext.fine_semantics initU))).

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
  Record weak_tsim {tpc tpf : t} (mc mf : Mem.mem)
             {i} (f: memren) (pfc : containsThread tpc i)
             (pff : containsThread tpf i) (compc: mem_compatible tpc mc)
             (compf: mem_compatible tpf mf) : Prop :=
    { weak_tsim_data:
        weak_mem_obs_eq f (restrPermMap (((compat_th _ _ compc) pfc).1))
                        (restrPermMap (((compat_th _ _ compf) pff).1));
      weak_tsim_locks:
        weak_mem_obs_eq f (restrPermMap (((compat_th _ _ compc) pfc).2))
                        (restrPermMap (((compat_th _ _ compf) pff).2))}.

  Record strong_tsim {tpc tpf : threadPool.ThreadPool.t} (mc mf : Mem.mem) {i}
         (f: memren) (pfc : containsThread tpc i)
         (pff : containsThread tpf i) (compc: mem_compatible tpc mc)
         (compf: mem_compatible tpf mf) : Prop :=
    { code_eq: ctl_inj f (getThreadC pfc) (getThreadC pff);
      obs_eq_data: mem_obs_eq f (restrPermMap ((fst (compc i pfc))))
                         (restrPermMap (fst (compf i pff)));
      obs_eq_locks: mem_obs_eq f (restrPermMap ((snd (compc i pfc))))
                         (restrPermMap (snd (compf i pff)));
    }.

  (** *** Simulation between events *)

  Definition pmap_inj f (pmap1 pmap2 : access_map) :=
    (forall b1 b2,
        f b1 = Some b2 ->
        Maps.PMap.get b1 pmap1 = Maps.PMap.get b2 pmap2) /\
    (forall b1, f b1 = None ->
           Maps.PMap.get b1 pmap1 = fun _ => None) /\
    (forall b2, (exists ofs, Maps.PMap.get b2 pmap2 ofs <> None) ->
           exists b1, f b1 = Some b2).      

  Definition isProjection (f : memren) (deltaMap deltaMap' : delta_map) : Prop :=
    (forall b b',
      f b = Some b' ->
      Maps.PTree.get b deltaMap = Maps.PTree.get b' deltaMap').

   Definition delta_inj (f : memren) (deltaMap deltaMap' : delta_map) : Prop :=
    (forall b b',
        f b = Some b' ->
        match Maps.PTree.get b deltaMap, Maps.PTree.get b' deltaMap' with
        | Some d1, Some d2 => d1 = d2
        | Some d1, None => forall ofs, d1 ofs = None \/ d1 ofs = Some None
        | None, None => True
        | _, _ => False
        end) /\
    (forall b, f b = None ->
          match Maps.PTree.get b deltaMap with
          | None => True
          | Some d => forall ofs, d ofs = None \/ d ofs = Some None
          end ) /\
    (forall b', (~exists b, f b = Some b') ->
           Maps.PTree.get b' deltaMap' = None).

   
  Definition delta_content_inj (f : memren) (deltaMap deltaMap' : delta_content) : Prop :=
    (forall b b',
        f b = Some b' ->
        match Maps.PTree.get b deltaMap, Maps.PTree.get b' deltaMap' with
        | Some d1, Some d2 => forall ofs, match d1 ofs, d2 ofs with
                                    | Some mv1, Some mv2 =>
                                      memval_obs_eq f mv1 mv2
                                    | None, None => True
                                    | _, _ => False
                                    end  
        | None, None => True
        | Some d1, None => forall ofs, d1 ofs = None
        | None, Some d2 => False
        end) /\
    (forall b, f b = None ->
          match Maps.PTree.get b deltaMap with
          | None => True
          | Some d => forall ofs, d ofs = None
          end ) /\
    (forall b', (~exists b, f b = Some b') ->
           Maps.PTree.get b' deltaMap' = None).
  

  
  Inductive event_sim (f:memren) : Events.machine_event -> Events.machine_event -> Prop :=
  | ReleaseSim : forall i b1 b2 ofs dc1 dc2
                   (Hf: f b1 = Some b2)
                   (Hdelta_inj: delta_content_inj f dc1 dc2),
      event_sim f (Events.external i (Events.release (b1,ofs) (Some dc1)))
                (Events.external i (Events.release (b2,ofs) (Some dc2)))
  | AcquireSim : forall i b1 b2 ofs dc1 dc2
                   (Hf: f b1 = Some b2)
                   (Hpmap1_inj: delta_content_inj f dc1 dc2),
      event_sim f (Events.external i (Events.acquire (b1,ofs) (Some dc1)))
                (Events.external i (Events.acquire (b2,ofs) (Some dc2)))
  | MkLockSim : forall i b1 b2 ofs
                   (Hf: f b1 = Some b2),
      event_sim f (Events.external i (Events.mklock (b1,ofs)))
                (Events.external i (Events.mklock (b2, ofs)))
  | FreeLockSim : forall i b1 b2 ofs
                  (Hf: f b1 = Some b2),
      event_sim f (Events.external i (Events.freelock (b1,ofs)))
                (Events.external i (Events.freelock (b2, ofs)))
  | SpawnSim : forall i b1 b2 ofs dc1a dc2a dc1b dc2b
                 (Hf: f b1 = Some b2)
                 (Hinj1: delta_content_inj f dc1a dc2a)
                 (Hinj2: delta_content_inj f dc1b dc2b),
      event_sim f (Events.external i (Events.spawn (b1, ofs) (Some dc1a) (Some dc1b)))
                (Events.external i (Events.spawn (b2, ofs) (Some dc2a) (Some dc2b)))
  | FAcqSim: forall i b1 b2 ofs
               (Hf: f b1 = Some b2),
      event_sim f (Events.external i (Events.failacq (b1,ofs)))
                (Events.external i (Events.failacq (b2, ofs))).
      
  Inductive trace_sim (f:memren) : event_trace -> event_trace -> Prop :=
  | TraceEmpty : trace_sim f [::] [::]
  | TraceCons : forall ev ev' tr tr'
                  (Hev: event_sim f ev ev')
                  (Htr: trace_sim f tr tr'),
      trace_sim f (tr ++ [:: ev]) (tr' ++ [:: ev']).

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
- Every thread in the DryConc machine can be stepped as mandated by the delta [xs] until the DryCo   nc machine reaches a state for which this thread is in [strong_tsim] between the two machines.
- Lock resources are related by the global renaming and the two machines have equivalent [lockRes] for mapped blocks
- The [invariant] holds for the FineConc machine
- The [Max] permissions on the memory of the FineConc machine are always set to [Freeable]
- The state, memory, and genv of DryConc are well-formed (no dangling pointers)
- the delta list [xs] contains only valid thread ids. *)

  Record sim tpc trc mc tpf (trf : event_trace) mf (xs : seq nat) (f fg: memren) (fp: fpool tpc) fuelF : Prop :=
    { numThreads : forall i, containsThread tpc i <-> containsThread tpf i;
      mem_compc: mem_compatible tpc mc;
      mem_compf: mem_compatible tpf mf;
      safeCoarse: forall sched tr,
          HybridCoarseMachine.csafe (sched,tr,tpc) mc (fuelF + size xs);
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
                    internal_execution ([seq x <- xs | x == tid])
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
                        rmap.1 # b2 ofs = None /\ rmap.2 # b2 ofs = None) /\
                    (forall b2, (~exists b1, fp _ pfc b1 = Some b2) ->
                            forall ofs, (getThreadR pff).1 # b2 ofs = None /\
                                   (getThreadR pff).2 # b2 ofs = None);
      simLockRes: (forall bl1 bl2 ofs rmap1 rmap2
                    (Hf: f bl1 = Some bl2)
                    (Hl1: lockRes tpc (bl1,ofs) = Some rmap1)
                    (Hl2: lockRes tpf (bl2,ofs) = Some rmap2),
                      strong_mem_obs_eq f (restrPermMap (fst ((compat_lp _ _ mem_compc) _ _ Hl1)))
                                        (restrPermMap (fst ((compat_lp _ _ mem_compf) _ _ Hl2))) /\
                      strong_mem_obs_eq f (restrPermMap (snd ((compat_lp _ _ mem_compc) _ _ Hl1)))
                                        (restrPermMap (snd ((compat_lp _ _ mem_compf) _ _ Hl2)))) /\
                  (forall bl2 ofs,
                    lockRes tpf (bl2, ofs) ->
                    exists bl1, f bl1 = Some bl2) /\
                  (forall bl1 bl2 ofs,
                      f bl1 = Some bl2 ->
                      lockRes tpc (bl1, ofs) <-> lockRes tpf (bl2, ofs));
      unmappedRes:
        forall bl ofsl rmap,
          lockRes tpf (bl, ofsl) = Some rmap ->
        forall b2, (~exists b1, f b1 = Some b2) ->
                forall ofs, rmap.1 # b2 ofs = None /\
                       rmap.2 # b2 ofs = None;
      invF: invariant tpf;
      maxF: max_inv mf;
      memc_wd: valid_mem mc;
      tpc_wd: tp_wd f tpc;
      thege_wd: ge_wd fg the_ge;
      fg_spec: ren_incr fg f /\ forall b b', fg b = Some b' -> b = b';
      xs_wd: forall i, List.In i xs -> containsThread tpc i;
      (* traceWD: trace_wd f trc; *)
      traceSim: trace_sim f trc trf
    }.

  Arguments sim : clear implicits.
  Notation "cnt '$' m '@'  'I'" := (getStepType cnt m Internal) (at level 80).
  Notation "cnt '$' m '@'  'E'" := (getStepType cnt m Concurrent) (at level 80).
  Notation "cnt '$' m '@'  'S'" := (getStepType cnt m Suspend) (at level 80).

  (** *** Simulations Diagrams *)

  Definition sim_internal_def :=
    forall tpc trc tpf trf (mc mf : Mem.mem) fuelF
      (xs : Sch) (f fg : memren) (fp : fpool tpc) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hsim: sim tpc trc mc tpf trf mf xs f fg fp (S (S fuelF))),
      let mrestr := restrPermMap (((compat_th _ _ (mem_compf Hsim)) pff).1) in
      forall (Hinternal: pff$mrestr @ I),
      exists tpf' mf' fp' tr',
        (forall U, fmachine_step (i :: U, trf, tpf) mf (U, tr', tpf') mf') /\
        sim tpc trc mc tpf' trf mf' (i :: xs) f fg fp' (S fuelF).

  Definition sim_external_def :=
    forall tpc trc tpf trf (mc mf : Mem.mem) fuelF
      (xs : Sch) (f fg : memren) (fp : fpool tpc) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hsynced: ~ List.In i xs)
      (Hsim: sim tpc trc mc tpf trf mf xs f fg fp (S (S fuelF))),
      let mrestr := restrPermMap (((compat_th _ _ (mem_compf Hsim)) pff).1) in
      forall (Hexternal: pff$mrestr @ E),
    exists tpc' trc' mc' tpf' mf' f' fp' tr',
      (forall U, fmachine_step (i :: U, trf, tpf) mf (U, tr', tpf') mf') /\
      sim tpc' trc' mc' tpf' tr' mf' xs f' fg fp' (S fuelF).

  (** When we reach a suspend step, we can ``synchronize'' the two
  machines by executing on the coarse machine the internal steps of
  the thread that reached the suspend step. The injection of this
  thread will now serve as the new injection. *)

  Definition sim_suspend_def :=
    forall tpc trc tpf trf (mc mf : Mem.mem) fuelF
      (xs : Sch) (f fg : memren) (fp : fpool tpc) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hsim: sim tpc trc mc tpf trf mf xs f fg fp (S (S fuelF))),
      let mrestr := restrPermMap (((compat_th _ _ (mem_compf Hsim)) pff).1) in
      forall (Hsuspend: pff$mrestr @ S),
    exists tpc' trc' mc' tpf' mf' f' fp' tr',
      (forall U, fmachine_step (i :: U, trf, tpf) mf (U, tr', tpf') mf') /\
      sim tpc' (trc ++ trc') mc' tpf' trf mf' [seq x <- xs | x != i] f' fg fp'
          (S fuelF).

  Definition sim_fail_def :=
    forall tpc trc tpf trf (mc mf : Mem.mem) fuelF
      (xs : Sch) (f fg : memren) (fp : fpool tpc) (i : NatTID.tid)
      (pff: ~ containsThread tpf i)
      (Hsim: sim tpc trc mc tpf trf mf xs f fg fp (S (S fuelF))),
    exists tr',
      (forall U, fmachine_step (i :: U, trf, tpf) mf (U, tr', tpf) mf) /\
      sim tpc trc mc tpf trf mf xs f fg fp (S fuelF).

  End SimDefs.

  Arguments sim {asmSem} {CI} tpc trc mc tpf trf mf xs f fg fp fuelF.

End SimDefs.

(** ** Proofs *)
Module SimProofs.

  Section SimProofs.
    Context {asmSem : Semantics}
            {semAxioms : SemAxioms}
            {semDet : SemDet}
            {CI: CoreInj}
            {initU : seq nat}.

    Existing Instance OrdinalPool.OrdinalThreadPool.
    Existing Instance DryHybridMachine.DryHybridMachineSig.
    Existing Instance dryFineMach.
    Existing Instance FineDilMem.
    Existing Instance dryCoarseMach.
    Existing Instance HybridFineMachine.scheduler.
    Existing Instance HybridCoarseMachine.scheduler.
    Existing Instance FineDilMem.
    Existing Instance HybridCoarseMachine.DilMem.

    Import SimDefs ThreadPoolWF.
    Import event_semantics Events.

  Notation csafe := (HybridCoarseMachine.csafe).
  Notation sim_fail_def := (@sim_fail_def _ _ initU).
  Notation threadStep := (HybridMachineSig.threadStep).
  Notation cmachine_step := ((corestep (AsmContext.coarse_semantics initU))).
  Notation fmachine_step := ((corestep (AsmContext.fine_semantics initU))).
  Notation "cnt '$' m '@'  'I'" := (getStepType cnt m Internal) (at level 80).
  Notation "cnt '$' m '@'  'E'" := (getStepType cnt m Concurrent) (at level 80).
  Notation "cnt '$' m '@'  'S'" := (getStepType cnt m Suspend) (at level 80).

  Notation internal_step := (internal_step).
  Notation internal_execution := (internal_execution).
  Notation fyield := (@yield HybridFineMachine.scheduler).
  Notation fdiluteMem := (@diluteMem FineDilMem).

  Notation sim_internal_def := (@sim_internal_def _ _ initU).
  Notation sim_suspend_def := (@sim_suspend_def _ _ initU).
  Notation sim_external_def := (@sim_external_def _ _ initU).

  (** NOTE: this is only needed to find out if a block is in the
    codomain of f, which is decidable *)
  Hypothesis em : excluded_middle.

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
  
  Lemma pmap_inj_incr:
    forall f f' pmap pmap'
      (Hincr: ren_incr f f')
      (Hinjective: forall b1 b1' b2,
          f' b1 = Some b2 ->
          f' b1' = Some b2 ->
          b1 = b1')
      (Hinj: pmap_inj f pmap pmap'),
      pmap_inj f' pmap pmap'.
  Proof.
    intros.
    destruct Hinj as [H1 [H2 H3]].
    repeat split.
    - intros b1 b2 Hf'.
      destruct (f b1) eqn:Hf.
      + eapply H1.
        pose proof (Hincr _ _ Hf) as Hf2.
        rewrite Hf2 in Hf'; inversion Hf'; subst.
        assumption.
      + rewrite H2; auto.
        apply extensionality.
        intros ofs.
        destruct (pmap' # b2 ofs) eqn:Hpmap'; auto.
        exfalso.
        specialize (H3 b2 ltac:(exists ofs; rewrite Hpmap'; intros Hcontra; congruence)).
        destruct H3.
        pose proof (Hincr _ _ H).
        specialize (Hinjective _ _ _ H0 Hf'); subst.
        congruence.
    - intros b1 Hf'.
      eapply H2.
      destruct (f b1) eqn:Hf; auto.
      eapply Hincr in Hf.
      congruence.
    - intros b2 Hnonempty.
      specialize (H3 _ Hnonempty).
      destruct H3.
      eapply Hincr in H.
      eexists; eauto.
  Qed.

  Lemma delta_inj_incr:
    forall f f' pmap pmap'
      (Hincr: ren_incr f f')
      (Hinjective: forall b1 b1' b2,
          f' b1 = Some b2 ->
          f' b1' = Some b2 ->
          b1 = b1')
      (Hinj: delta_inj f pmap pmap'),
      delta_inj f' pmap pmap'.
  Proof.
    intros.
    repeat split.
    - intros b b' Hf'.
      destruct (f b) eqn:Hfb.
      + pose proof (Hincr _ _ Hfb) as Hf'b.
        rewrite Hf'b in Hf'.
        inversion Hf'; subst.
        eapply Hinj;
          now auto.
      + destruct Hinj as [H0 [H1 H2]].
        specialize (H1 b Hfb).
        destruct (pmap ! b) eqn:Hpmap.
        * assert ((exists b, f b = Some b') \/ (~ exists b, f b = Some b'))
            by (eapply em).
          destruct H as [H | H].
          ** destruct H as [b0 Hf0].
             pose proof (Hincr _ _ Hf0) as Hf0'.
             specialize (Hinjective _ _ _ Hf' Hf0'); subst.
             congruence.
          ** erewrite H2 by eauto.
             assumption.
        * erewrite H2.
          auto.
          intros (b0 & Hf0).
          pose proof (Hincr _ _ Hf0) as Hf0'.
          specialize (Hinjective _ _ _ Hf' Hf0'); subst.
          congruence.
    - intros b Hf'.
      destruct (f b) eqn:Hfb.
      +  eapply Hincr in Hfb.
         congruence.
      +  eapply Hinj;
           eauto.
    - intros b' Hf'.
      eapply Hinj.
      intros Hcontra.
      eapply Hf'.
      destruct Hcontra as [b0 Hf0].
      exists b0.
      eapply Hincr;
        now eauto.
  Qed.

  Lemma memval_obs_eq_incr:
    forall (f f': memren) mv1 mv2
      (Hincr: ren_incr f f')
      (Hobs_eq: memval_obs_eq f mv1 mv2),
      memval_obs_eq f' mv1 mv2.
  Proof.
    intros.
    inversion Hobs_eq;
      constructor.
    inversion Hval_obs; subst; constructor.
    apply Hincr in H1.
      by auto.
  Qed.

  Lemma delta_content_inj_incr:
    forall f f' pmap pmap'
      (Hincr: ren_incr f f')
      (Hinjective: forall b1 b1' b2,
          f' b1 = Some b2 ->
          f' b1' = Some b2 ->
          b1 = b1')
      (Hinj: delta_content_inj f pmap pmap'),
      delta_content_inj f' pmap pmap'.
  Proof.
    intros.
    unfold delta_content_inj in *.
    repeat split.
    - intros b b' Hf'.
      destruct (f b) eqn:Hfb.
      + pose proof (Hincr _ _ Hfb) as Hf'b.
        rewrite Hf'b in Hf'.
        inversion Hf'; subst.
        destruct Hinj as [H0 [H1 H2]].
        specialize (H0 _ _ Hfb).
        repeat match goal with
               |[ |- match ?Expr with _ => _ end] =>
                destruct Expr eqn:?
               | [|- forall _, _] => intros
               end; auto;
        specialize (H0 ofs);
        rewrite Heqo1 Heqo2 in H0;
        auto.
        eapply memval_obs_eq_incr;
          eauto.
      + destruct Hinj as [H0 [H1 H2]].
        specialize (H1 b Hfb).
        destruct (pmap ! b) eqn:Hpmap.
        * assert ((exists b, f b = Some b') \/ (~ exists b, f b = Some b'))
            by (eapply em).
          destruct H as [H | H].
          ** destruct H as [b0 Hf0].
             pose proof (Hincr _ _ Hf0) as Hf0'.
             specialize (Hinjective _ _ _ Hf' Hf0'); subst.
             congruence.
          ** specialize (H2 _ H).
             rewrite H2.
             now auto.
        * erewrite H2.
          auto.
          intros (b0 & Hf0).
          pose proof (Hincr _ _ Hf0) as Hf0'.
          specialize (Hinjective _ _ _ Hf' Hf0'); subst.
          congruence.
    - intros b Hf'.
      destruct (f b) eqn:Hfb.
      +  eapply Hincr in Hfb.
         congruence.
      +  eapply Hinj;
           eauto.
    - intros b' Hf'.
      eapply Hinj.
      intros Hcontra.
      eapply Hf'.
      destruct Hcontra as [b0 Hf0].
      exists b0.
      eapply Hincr;
        now eauto.
  Qed.

  Lemma delta_content_inj_correct:
    forall f pmapc pmapf dmap mc mf
      (Hf_injective: forall b1 b1' b2,
          f b1 = Some b2 ->
          f b1' = Some b2 ->
          b1 = b1')
      (Hdelta_inj: delta_inj f dmap (projectAngel f dmap))
      (Hltc: permMapLt (computeMap pmapc dmap) (getMaxPerm mc))
      (Hltf: permMapLt (computeMap pmapf (projectAngel f dmap)) (getMaxPerm mf))
      (Hobs_eq: mem_obs_eq f (restrPermMap Hltc) (restrPermMap Hltf)),
      delta_content_inj f (build_delta_content dmap mc)
                        (build_delta_content (projectAngel f dmap) mf).
  Proof.
    intros.
    repeat (split).
    - intros.
      inversion Hobs_eq.
      destruct strong_obs_eq0.
      destruct ((build_delta_content dmap mc) ! b) eqn:Hdeltac.
      + destruct ((build_delta_content (projectAngel f dmap) mf) ! b') eqn:Hdeltaf.
        * intros.
          unfold build_delta_content in *.
          rewrite PTree.gmap in Hdeltac.
          rewrite PTree.gmap in Hdeltaf.
          unfold Coqlib.option_map in *.
          erewrite <- projectAngel_correct in Hdeltaf by eauto.
          (* specialize (perm_obs_strong0 b b' ofs H). *)
          (* rewrite! restrPermMap_Cur in perm_obs_strong0. *)
          destruct (dmap ! b) eqn:Hdmap.
          ** rewrite Hdmap in Hdeltac.
             inversion Hdeltac; subst.
             inversion Hdeltaf; subst. clear Hdeltac Hdeltaf.
             destruct (o1 ofs) as [o|] eqn:Ho1; auto.
             destruct o as [p|]; auto.
             specialize (val_obs_eq0 _ _ ofs H).
             unfold Mem.perm in val_obs_eq0.
             assert (permission_at (restrPermMap Hltc) b ofs Cur =
                     (Mem.mem_access (restrPermMap Hltc)) # b ofs Cur)
               by reflexivity.
             rewrite <- H0 in val_obs_eq0.
             rewrite restrPermMap_Cur in val_obs_eq0.
             erewrite computeMap_1 in val_obs_eq0 by eauto.
             simpl in val_obs_eq0.
             destruct p;
               now eauto using perm_order.
          ** rewrite Hdmap in Hdeltac.
             inversion Hdeltac.
        * unfold build_delta_content in *.
          rewrite PTree.gmap in Hdeltac.
          rewrite PTree.gmap in Hdeltaf.
          unfold Coqlib.option_map in *.
          erewrite <- projectAngel_correct in Hdeltaf by eauto.
          destruct (dmap ! b) eqn:Hdmap.
          ** rewrite Hdmap in Hdeltac.
             discriminate.
          ** rewrite Hdmap in Hdeltac.
             discriminate.
      + unfold build_delta_content in *.
        erewrite PTree.gmap in *.
        unfold Coqlib.option_map in *.
        erewrite <- projectAngel_correct by eauto.
        destruct (dmap ! b) eqn:Hdmap.
        * rewrite Hdmap in Hdeltac.
          discriminate.
        * auto.
    - destruct Hdelta_inj as [_ [Heq _]].
      intros.
      specialize (Heq b H).
      destruct ((build_delta_content dmap mc) ! b) eqn:Hbuild; auto.
      unfold build_delta_content in Hbuild.
      erewrite PTree.gmap in *.
      unfold Coqlib.option_map in *.
      destruct (dmap ! b) eqn:Hdmap;
        rewrite Hdmap in Hbuild; try discriminate.
      inversion Hbuild.
      intros ofs.
      specialize (Heq ofs).
      destruct Heq as [Heq| Heq]; rewrite Heq;
        auto.
    - intros.
      unfold build_delta_content.
      erewrite PTree.gmap in *.
      unfold Coqlib.option_map in *.
      erewrite projectAngel_correct_2;
        now eauto.
  Qed.
      
  
  Lemma ev_sim_incr:
    forall f f' ev ev'
      (Hincr: ren_incr f f')
      (Hinjective: forall b1 b1' b2,
          f' b1 = Some b2 ->
          f' b1' = Some b2 ->
          b1 = b1')
      (Hev_sim: event_sim f ev ev'),
      event_sim f' ev ev'.
  Proof.
    intros.
    inversion Hev_sim;
      econstructor; eauto using pmap_inj_incr, delta_content_inj_incr.
  Qed.
  
  Lemma trace_sim_incr:
    forall f f' trc trf
      (Hincr: ren_incr f f')
      (Hinjective: forall b1 b1' b2,
          f' b1 = Some b2 ->
          f' b1' = Some b2 ->
          b1 = b1')
      (Htr: trace_sim f trc trf),
      trace_sim f' trc trf.
  Proof.
    intros.
    induction Htr;
      econstructor;
      eauto using ev_sim_incr.
  Qed.       
  
  Lemma ctlType_inj :
    forall st c c' m m' (f fg: memren)
      (Hfg:forall b1 b2 : block, fg b1 = Some b2 -> b1 = b2)
      (Hincr: ren_incr fg f)
      (Hge_wd: ge_wd fg the_ge)
      (Hvalid: valid_mem m)
      (Hmem: mem_obs_eq f m m')
      (Hinj: ctl_inj f c c'),
      ctlType c m st <-> ctlType c' m' st.
  Proof.
    intros. unfold ctl_inj in Hinj.
    destruct c; destruct c'; try (by exfalso);
      unfold ctlType in *; try tauto.
    assert (Hat_ext := core_inj_ext _ _  Hfg Hge_wd Hincr Hvalid Hinj Hmem).
    destruct (at_external semSem s m) as [[? ?]|] eqn:Hext; simpl in *.
    - destruct (at_external semSem s0 m') as [[? ?]|];
        now tauto.
    - destruct (at_external semSem s0 m') as [[? ?]|]; [tauto|].
      split; auto.
  Qed.

  Lemma stepType_inj:
    forall tpc tpf i (pffi:containsThread tpf i) (pfci: containsThread tpc i) m m' f fg st
      (Hfg:forall b1 b2 : block, fg b1 = Some b2 -> b1 = b2)
      (Hincr: ren_incr fg f)
      (Hge_wd: ge_wd fg the_ge)
      (Hvalid_mem: valid_mem m)
      (Hmem_obs_eq: mem_obs_eq f m m'),
      ctl_inj f (getThreadC pfci) (getThreadC pffi) ->
      getStepType pfci m st <-> getStepType pffi m' st.
  Proof.
    intros.
    eapply ctlType_inj;
      try eauto.
  Qed.

  Lemma sim_reduce:
    forall tpc trc mc tpf trf mf xs f fg fp n m,
      sim tpc trc mc tpf trf mf xs f fg fp n ->
      m <= n ->
      sim tpc trc mc tpf trf mf xs f fg fp m.
  Proof.
    intros.
    inversion H.
    econstructor; eauto.
    intros.
    eapply HybridCoarseMachine.csafe_reduce; eauto.
    ssromega.
  Qed.


  Lemma sim_fail: sim_fail_def.
  Proof.
    unfold sim_fail_def.
    intros.
    exists trf.
    split.
    intros. econstructor 6; simpl; eauto.
    eapply (invF Hsim); eauto.
    eapply (mem_compf Hsim); eauto.
    eapply sim_reduce; eauto.
  Qed.

  (** Proofs about [internal_execution] and [internal_step] *)
  Existing Instance HybridCoarseMachine.DilMem.
  Existing Instance HybridCoarseMachine.scheduler.
  

  Lemma internal_step_cmachine_step :
    forall (i : NatTID.tid) (tp tp' : thread_pool) (m m' : mem)
      (U : list nat) tr
      (Hcnt: containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (Hstep_internal: internal_step Hcnt Hcomp tp' m'),
      exists tr',
      cmachine_step (((i :: U)), tr, tp) m
                    (((i :: U)), tr ++ tr', tp') m' /\
      (forall tp'' tr'' m'' U',
          cmachine_step (((i :: U)), tr,tp) m
                        ((U'), tr ++ tr'', tp'') m'' ->
          tp' = tp'' /\ m' = m'' /\ i :: U = U').
  Proof.
    intros.
    inversion Hstep_internal as [[? Hcore] | [[Hresume ?] | Hstart]]; subst;
      autounfold.
    - exists (List.map (fun mev => internal i mev) x).
      split.
      + replace m' with (diluteMem m') by reflexivity.
        assert (Heq: i :: U = @yield HybridCoarseMachine.scheduler (i :: U)) by reflexivity.
        rewrite Heq.
        eapply thread_step.
        reflexivity.
        simpl.
        eapply Hcore.
      + intros tp'' tr'' m'' U' Hstep.
        Opaque mem_compatible.
        assert (Hstep_internal': internal_step Hcnt Hcomp tp'' m'' /\ i :: U = U').
        { inversion Hstep; subst; clear Hstep; Tactics.pf_cleanup;
          simpl in *;
          inversion HschedN; subst;
          Tactics.pf_cleanup;
          unfold internal_step; try (by eexists; eauto);
            eapply internal_step_type in Hstep_internal;
          exfalso; simpl in *;
          unfold getStepType, ctlType in Hstep_internal;
            try inversion Htstep;
            try (inversion Hhalted); subst; Tactics.pf_cleanup;
              try inversion Hperm; subst;
          repeat match goal with
                 | [H1: context[match ?Expr with | _ => _ end],
                        H2: ?Expr = _ |- _] =>
                   rewrite H2 in H1
                 end; try discriminate;
            try (match goal with
                 | [H: match at_external ?A ?B ?C with _ => _ end |- _] =>
                   destruct (at_external A B C) eqn:Hext
                 end);
            try discriminate.
        }
        destruct Hstep_internal' as [Hstep_internal' Heq]; subst.
        destruct (internal_step_det Hstep_internal Hstep_internal'); subst;
          now auto.
    - exists [::].
      rewrite cats0.
      split.
      + assert (Heq: i :: U = @yield HybridCoarseMachine.scheduler (i :: U)) by reflexivity.
        rewrite Heq.
        eapply resume_step;
          now eauto.
      + intros tp'' tr'' m'' U' Hstep.
        Opaque mem_compatible.
        assert (Hstep_internal': internal_step Hcnt Hcomp tp'' m'' /\ i :: U = U').
        { inversion Hstep; subst; clear Hstep; Tactics.pf_cleanup;
            simpl in *;
            inversion HschedN; subst;
              Tactics.pf_cleanup;
              unfold internal_step; try (by eexists; eauto);
                eapply internal_step_type in Hstep_internal;
                exfalso; simpl in *;
                  unfold getStepType, ctlType in Hstep_internal;
                  try inversion Htstep;
                  try (inversion Hhalted); subst; Tactics.pf_cleanup;
                    try inversion Hperm; subst;
                      repeat match goal with
                             | [H1: context[match ?Expr with | _ => _ end],
                                    H2: ?Expr = _ |- _] =>
                               rewrite H2 in H1
                             end; try discriminate;
                        try (match goal with
                             | [H: match at_external ?A ?B ?C with _ => _ end |- _] =>
                               destruct (at_external A B C) eqn:Hext
                             end);
                        try discriminate.
        }
        destruct Hstep_internal' as [Hstep_internal' Heq]; subst.
        destruct (internal_step_det Hstep_internal Hstep_internal'); subst;
          now auto.
    - exists [::].
      rewrite cats0.
      split.
      + assert (Heq: i :: U = @yield HybridCoarseMachine.scheduler (i :: U)) by reflexivity.
        rewrite Heq.
        replace m' with (@diluteMem HybridCoarseMachine.DilMem m') by reflexivity.
        eapply start_step;
          now eauto.
      + intros tp'' tr'' m'' U' Hstep.
        Opaque mem_compatible.
        assert (Hstep_internal': internal_step Hcnt Hcomp tp'' m'' /\ i :: U = U').
        { inversion Hstep; subst; clear Hstep; Tactics.pf_cleanup;
            simpl in *;
            inversion HschedN; subst;
              Tactics.pf_cleanup;
              unfold internal_step; try (by eexists; eauto);
                eapply internal_step_type in Hstep_internal;
                exfalso; simpl in *;
                  unfold getStepType, ctlType in Hstep_internal;
                  try inversion Htstep;
                  try (inversion Hhalted); subst; Tactics.pf_cleanup;
                    try inversion Hperm; subst;
                      repeat match goal with
                             | [H1: context[match ?Expr with | _ => _ end],
                                    H2: ?Expr = _ |- _] =>
                               rewrite H2 in H1
                             end; try discriminate;
                        try (match goal with
                             | [H: match at_external ?A ?B ?C with _ => _ end |- _] =>
                               destruct (at_external A B C) eqn:Hext
                             end);
                        try discriminate.
        }
        destruct Hstep_internal' as [Hstep_internal' Heq]; subst.
        destruct (internal_step_det Hstep_internal Hstep_internal'); subst;
          now auto.
  Qed.

  Notation corestepN := (corestepN (AsmContext.coarse_semantics initU)).
  Lemma safety_det_corestepN_internal:
    forall xs i U tpc trc mc tpc' mc' fuelF
      (Hsafe : csafe ((i :: U),trc,tpc) mc
                     (fuelF.+1 + size xs))
      (Hexec : internal_execution [seq x <- xs | x == i] tpc mc tpc' mc'),
      exists trc',
      corestepN (size [seq x <- xs | x == i])
                ((i :: U), trc, tpc) mc ((i :: U), trc ++ trc', tpc') mc'
      /\ csafe ((i :: U),trc ++ trc',tpc') mc'
              (fuelF.+1 + size [seq x <- xs | x != i]).
  Proof.
    intros xs.
    induction xs as [ | x xs]; intros.
    { simpl in *. inversion Hexec; subst.
      exists [::]; rewrite cats0;
        now eauto.
      simpl in HschedN. discriminate.
    }
    { simpl in *.
      destruct (x == i) eqn:Hx; move/eqP:Hx=>Hx; subst.
      - inversion Hsafe.
        + simpl in H; by exfalso.
        + simpl in *.
          subst.
          inversion Hexec; subst; simpl in *; clear Hexec;
          inversion HschedN; subst i.
          assert (Hmach_step_det :=
                    internal_step_cmachine_step U trc Hstep0).
          destruct Hmach_step_det as [tr' [Hmach_step' Hmach_det]].
          specialize (Hmach_det _ _ _ _ Hstep).
          destruct Hmach_det as [? [? ?]]; subst.
          rewrite <- addSnnS in Hsafe0.
          destruct (IHxs tid U tp' _ m' tpc' mc' _ Hsafe0 Htrans)
            as [trc' [HcorestepN Hsafe']].
          exists (tr ++ trc').
          rewrite catA.
          split;
            now eauto.
        + exfalso.
          inversion Hexec; subst; simpl in *; clear Hexec;
          inversion HschedN; subst i.
          assert (Hmach_step_det := internal_step_cmachine_step U trc Hstep0).
          destruct Hmach_step_det as [tr' [Hmach_step' Hmach_det]].
          specialize (Hmach_det _ _ _ _ Hstep).
          destruct Hmach_det as [? [? ?]]; subst.
          exfalso;
            eapply list_cons_irrefl;
            now eauto.
      - simpl.
        rewrite <- addSnnS in Hsafe.
        destruct (IHxs i U tpc trc mc tpc' mc' (fuelF.+1) Hsafe Hexec) as [? [? ?]].
        eexists; split;
          [now eauto| rewrite <- addSnnS; now eauto].
    }
  Qed.

  (*NOTE: how can we have tactics inside sections? *)
  (** Solves absurd cases from fine-grained internal steps *)
  Ltac absurd_internal Hstep :=
    inversion Hstep; try inversion Htstep; subst; simpl in *; Tactics.pf_cleanup;
    try match goal with
        | [H: Some _ = Some _ |- _] => inversion H; subst
        end; Tactics.pf_cleanup;
    repeat match goal with
           | [H: OrdinalPool.getThreadC ?Pf = _, Hint: ?Pf$_ @ I |- _] =>
             unfold getStepType, ctlType in Hint; simpl in *;
             rewrite H in Hint; simpl in Hint
           | [H: getThreadC ?Pf = _, Hint: ?Pf$_ @ I |- _] =>
             unfold getStepType, ctlType in Hint; simpl in *;
             rewrite H in Hint; simpl in Hint
           | [H1: match ?Expr with _ => _ end = _,
                  H2: ?Expr = _ |- _] => rewrite H2 in H1
           (*     | [H1: is_true (isSome (halted ?Sem ?C)),
                  H2: match at_external _ _ _ with _ => _ end = _ |- _] =>
             destruct (at_external_halted_excl Sem C) as [Hext | Hcontra];
               [rewrite Hext in H2;
                 destruct (halted Sem C) eqn:Hh;
                 [discriminate | by exfalso] |
                rewrite Hcontra in H1; by exfalso]*)
           end; try discriminate; try (exfalso; by auto).

  Lemma at_internal_cmachine_step :
    forall i U U' tp tr tr' tp' m m'
      (cnt: containsThread tp i)
      (Hcomp: mem_compatible tp m),
      let mrestr := restrPermMap (((compat_th _ _ Hcomp) cnt).1) in
      forall (Hinternal: cnt$mrestr @ I)
      (Hstep: cmachine_step ((i :: U), tr,tp) m (U', tr ++ tr', tp') m'),
        internal_step cnt Hcomp tp' m' /\ U' = (i :: U).
  Proof.
    intros.
    absurd_internal Hstep.
    - split; auto.
      do 2 right;
        by auto.
    - split; auto.
      right; left;
        by auto.
    - split; auto.
      left; now eauto.
    - inversion Hperm; subst.
      subst mrestr.
      rewrite Hat_external in Hinternal.
      discriminate.
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
    inversion Hstep as [[? Htstep] | [[Htstep ?] | Htstep]].
    - inversion Htstep; subst.
      erewrite restrPermMap_mem_valid with (Hlt := fst (compat_th _ _ Hcomp cnti)) in Hmem_wd.
      eapply ev_step_ax1 in Hcorestep.
      eapply @corestep_wd with (f := f) (fg := fg) in Hcorestep;
        eauto.
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
        Tactics.pf_cleanup.
        specialize (Htp_wd _ ctn).
        rewrite Hcode in Htp_wd.
      destruct X as [? ?].
      simpl in *.
      destruct Htp_wd as [Hcore_wd _].
      inversion Hperm; subst.
      erewrite restrPermMap_domain with (Hlt := (compat_th _ _ Hcomp ctn)#1) in Hdomain.
      erewrite restrPermMap_mem_valid with (Hlt := (compat_th _ _ Hcomp ctn)#1) in Hmem_wd.
      assert (Hargs:= at_external_wd _ Hmem_wd Hdomain Hcore_wd Hat_external).
      eapply after_external_wd; eauto.
      eapply core_wd_incr; eauto.
      eapply valid_val_list_incr;
        by eauto.
      simpl; auto.
      + erewrite <- @gsoThreadCC with (cntj := cntj); eauto.
        specialize (Htp_wd _ cntj).
        eapply ctl_wd_incr;
          by eauto.
    - inversion Htstep; subst.
      Tactics.pf_cleanup.
      inversion Hperm; subst.
      erewrite restrPermMap_mem_valid with (Hlt := fst (compat_th _ _ Hcomp cnti)) in Hmem_wd.
      eapply @initial_core_wd with (f := f) in Hinitial; eauto.
      destruct Hinitial as [Hmem_Wd' [Hf' Hcore_wd']].
      destruct Hf' as [f' [Hincr Hdomain']].
      assert (Hcore_wd_f' := Hcore_wd' _ Hdomain').
      split; auto.
      split; first by (eexists; eauto).
      intros f'' Hdomain''.
      intros j cntj.
      specialize (Hcore_wd' f'' Hdomain'').
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
      rewrite gssThreadCode.
      simpl.
      apply Hcore_wd'.
      assert (cntj' := containsThread_internal_step' Hstep cntj).
      erewrite @gsoThreadCode with (cntj := cntj') by eauto.
      specialize (Htp_wd _ cntj').
      assert (Hincr': ren_domain_incr f f'').
        by (eapply domain_memren_incr with (f' := f'); eauto).
      eapply ctl_wd_incr;
        by eauto.
      specialize (Htp_wd _ cnti).
      rewrite Hcode in Htp_wd;
        simpl in Htp_wd.
      econstructor.
      destruct Htp_wd; now auto.
      now econstructor.
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
    - simpl in Hexec; inversion Hexec; subst;
        [idtac| simpl in HschedN; by discriminate];
        split; auto;
          split; [exists f; split; unfold ren_domain_incr; auto | eauto].
      intros.
      eapply tp_wd_domain;
        by eauto.
    - simpl in Hexec.
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
    forall m tpc tpc' (f : memren) i (pfc : containsThread tpc i)
      (Hsuspend: suspend_thread m pfc tpc')
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
      (Hmem_wd: valid_mem mc)
      (Hstep_internal: internal_step pfc Hcompc tpc' mc'),
    exists tpf' mf' fi' tr',
      (forall U, fmachine_step (i :: U, tr, tpf) mf (U, tr', tpf') mf') /\
      max_inv mf' /\
      ren_incr fi fi' /\
      ren_separated fi fi' mc mf /\
      (forall (pfc': containsThread tpc' i) (pff': containsThread tpf' i)
         (Hcompc': mem_compatible tpc' mc') (Hcompf': mem_compatible tpf' mf'),
          strong_tsim fi' pfc' pff' Hcompc' Hcompf' /\
          (forall b2, (~exists b1, fi' b1 = Some b2) ->
                 forall ofs, (getThreadR pff').1 # b2 ofs = (getThreadR pff).1 # b2 ofs /\
                        (getThreadR pff').2 # b2 ofs = (getThreadR pff).2 # b2 ofs)) /\
      (forall j (pffj : containsThread tpf j),
          i <> j ->
          forall (b1 b2 : block),
            fi' b1 = Some b2 ->
            fi b1 = None ->
            forall ofs, (getThreadR pffj).1 # b2 ofs = None /\ (getThreadR pffj).2 # b2 ofs = None) /\
      (forall (bl : block) (ofsl : Z)
         rmap
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
      simpl in Hcode_eq.
      destruct (OrdinalPool.getThreadC pff) as [cf| ? | ? | ?] eqn:Hcodef;
        try (by exfalso).
      assert (H' := Hcorestep).
      apply ev_step_ax1 in Hcorestep.
      eapply corestep_obs_eq in Hcorestep; eauto. 
      destruct Hcorestep as
          (cf' & mf' & fi' & HcorestepF & Hcode_eq'
           & Hobs_eq' & Hincr & Hseparated
           & Hblocks & _ & _ & Hperm_unmapped).
      remember (restrPermMap (fst (compat_th _ _ Hcompf pff))) as mf1 eqn:Hrestrict.
      symmetry in Hrestrict.
      remember (updThread pff (Krun cf') (getCurPerm mf', (getThreadR pff).2))
        as tpf' eqn:Hupd.
      assert (Hevent_stepF:=ev_step_ax2 _ _ _ _ _ HcorestepF).
      destruct Hevent_stepF as [evF Hev_stepF].
      exists tpf', (setMaxPerm mf'), fi', (tr ++ (List.map (fun mev => internal i mev) evF)).
      split.
      { (* FineConc machine steps *)
        intros U.
        simpl.
        unfold MachStep. simpl.

        replace U with (fyield (i :: U)) at 2 by reflexivity.
        replace (setMaxPerm mf') with (fdiluteMem mf') by reflexivity.
        eapply thread_step; simpl; eauto.
        econstructor;
          now eauto.
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
        { intros. split.
          - (** Proof of strong simulation*)
            intros.
            econstructor;
              first by (subst tpf'; by do 2 erewrite gssThreadCode).
            + (* mem_obs_eq for data permissions *)
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
            + (** mem_obs_eq for lock permissions *)
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
              pose proof (fst (thread_data_lock_coh _ Hinv _ pfc) _ pfc).
              apply ev_step_ax1 in H'.
              eapply CoreLanguageDry.corestep_stable_val with (Hlt2 := Hlt); eauto.
              rewrite gssThreadRes; simpl;
                by eauto.
              (* stability of contents of FineConc *)
              intros.
              pose proof (fst (thread_data_lock_coh _ HinvF _ pff) _ pff).
              simpl.
              eapply CoreLanguageDry.corestep_stable_val with (Hlt2 := HltF); eauto.
              rewrite gssThreadRes; simpl;
                by eauto.
          - (** unmapped blocks*)
            intros b2 Hfi' ofs.
            subst.
            rewrite gssThreadRes. simpl.
            specialize (Hperm_unmapped _ Hfi' ofs).
            rewrite! restrPermMap_Cur in Hperm_unmapped.
            rewrite Hperm_unmapped.
            rewrite getCurPerm_correct;
              by auto.
        }
        (* block ownership*)
        (*sketch: the invariant is maintanted by coresteps hence it
           will hold for tpf'. Moreover we know that the new blocks in
           mc'|i will be mapped to new blocks in mf' by inject separated,
           where the permissions are empty for other threads. *)
        split.
        * intros j pffj Hij b1 b2 Hfi' Hfi ofs.
          specialize (Hseparated _ _ Hfi Hfi').
          destruct Hseparated as [Hinvalidmc1 Hinvalidmf1].
          subst mf1.
          erewrite restrPermMap_valid in Hinvalidmf1.
          pose proof (invalid_block_empty (fst (compat_th _ _ Hcompf pffj)) Hinvalidmf1 ofs).
          pose proof (invalid_block_empty (snd (compat_th _ _ Hcompf pffj)) Hinvalidmf1 ofs);
            split; by assumption.
        * intros bl ofsl rmap b1 b2 ofs Hfi' Hfi Hres.
          specialize (Hseparated _ _ Hfi Hfi').
          destruct Hseparated as [Hinvalidmc1 Hinvalidmf1].
          subst mf1.
          erewrite restrPermMap_valid in Hinvalidmf1.
          pose proof (invalid_block_empty (fst (compat_lp _ _ Hcompf _ _ Hres)) Hinvalidmf1 ofs).
          pose proof (invalid_block_empty (snd (compat_lp _ _ Hcompf _ _ Hres)) Hinvalidmf1 ofs);
            split; by assumption.
      }
    }
    { destruct Hresume as [Hresume Heq]; subst.
      inversion Hresume; subst; clear Hresume; Tactics.pf_cleanup.
      destruct Hstrong_sim as [Hcode_eq memObsEq].
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (OrdinalPool.getThreadC pff) as [?|?|cf |? ] eqn:HcodeF;
        try (by exfalso).
      destruct Hcode_eq as [Hcode_eq Hval_eq].
      inversion Hval_eq; subst.
      (* After external for cf*)
      assert (Hvalid_val: match (Some (Vint Int.zero)) with
                          | Some v1 => valid_val fi v1
                          | None => True
                          end)
        by (by simpl).
      inversion Hperm; subst.
      assert (Hafter_externalF :=
                core_inj_after_ext _ _ None Hfg Hge_wd Hren_incr Hcode_eq
                                   memObsEq Hvalid_val Hafter_external).
      destruct Hafter_externalF as [ov2 [cf' [Hafter_externalF [Hcode_eq' Hval_obs]]]].
      destruct ov2 as [v2 |]; try by exfalso.
      inversion Hval_obs; subst.
      erewrite restrPermMap_mem_valid with (Hlt := (compat_th _ _ Hcompc pfc)#1) in Hmem_wd.
      (* cf is at external*)
      assert (Hat_externalF_spec := core_inj_ext _ _  Hfg Hge_wd Hren_incr Hmem_wd Hcode_eq memObsEq).
      rewrite Hat_external in Hat_externalF_spec.
      simpl in Hat_externalF_spec.
      destruct X as [ef val].
      destruct (at_external semSem cf (restrPermMap (proj1 (compat_th _ _ Hcompf pff))))
        as [[ef' val']|] eqn:Hat_externalF;
        rewrite Hat_externalF in Hat_externalF_spec;
        try by exfalso.
      destruct Hat_externalF_spec as [? Harg_obs]; subst.
      remember (updThreadC pff (Krun cf')) as tpf' eqn:Hupd.
      exists tpf', mf, fi, tr.
      split.
      { (* The fine-grained machine steps *)
        intros.
        simpl.
        unfold MachStep. simpl.
        replace U with (fyield (i :: U)) at 2 by reflexivity.
        eapply @resume_step with (Htid := pff); simpl; eauto.
        subst.

        eapply @ResumeThread with (c := cf);
          eauto.
        simpl. unfold DryHybridMachine.install_perm.
        reflexivity.
      }
      { split; first by auto.
        split; first by auto.
        split; first by congruence.
        split.
        intros.
        split.
        constructor;
          first by (subst tpf';
                    do 2 rewrite gssThreadCC; by simpl).
        erewrite restrPermMap_irr' with
        (Hlt' := fst (compat_th _ _ Hcompf pff)) by (subst; by erewrite @gThreadCR with (cntj := pff)).
        erewrite restrPermMap_irr; eauto;
          by rewrite gThreadCR.
        erewrite restrPermMap_irr' with
        (Hlt' := snd (compat_th _ _ Hcompf pff)) by (subst; by erewrite @gThreadCR with (cntj := pff)).
        erewrite restrPermMap_irr; eauto;
          by rewrite gThreadCR.
        intros. subst. rewrite gThreadCR; auto.
        split; [ | split]; intros; by congruence.
      }
    }
    { inversion Hstart; subst; clear Hstart; Tactics.pf_cleanup.
      destruct Hstrong_sim as [Hcode_eq memObsEq].
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (OrdinalPool.getThreadC pff) as [?|?|? |vf' arg'] eqn:HcodeF;
        try (by exfalso).
      destruct Hcode_eq as [Hvf Harg_obs].
      assert (Harg_obs_list: val_obs_list fi [:: arg] [:: arg'])
        by (constructor; auto; constructor).
      inversion Hperm; subst.
      assert (HinitF := core_inj_init _ _ i  Hge_wd Hfg Hren_incr Harg_obs_list Hvf memObsEq Hinitial).
      destruct HinitF as
          (cf' & mf' & fi' & HcorestepF & Hcode_eq'
           & Hobs_eq' & Hincr & Hseparated
           & Hblocks & _ & _ & Hperm_unmapped).
      remember (updThread pff (Krun cf') (add_block Hcompf pff mf')) as tpf' eqn:Hupd.
      exists tpf', (@diluteMem FineDilMem mf'), fi', tr.
      split.
      { (* The fine-grained machine steps *)
        intros.
        simpl.
        unfold MachStep; simpl.
        replace U with (fyield (i :: U)) at 2 by reflexivity.
        eapply @start_step; simpl; eauto.
        eapply @StartThread with (c_new := cf') (Hcmpt := Hcompf);
          try eauto.
        simpl.
        unfold DryHybridMachine.install_perm.
        reflexivity.
      }
      { repeat match goal with
                 [|- _ /\ _] => split
               end; auto.
        - intros b ofs Hvalid.
          rewrite setMaxPerm_MaxV;
            by auto.
        - intros. split.
          + (** Proof of strong simulation*)
            intros.
            econstructor;
              first by (subst tpf'; by do 2 erewrite gssThreadCode).
            * (* mem_obs_eq for data permissions *)
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
            * (** mem_obs_eq for lock permissions *)
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
              pose proof (weak_obs_eq obs_eq_locks0) as Hobs_weak_locks.
              erewrite restrPermMap_irr' with (Hlt' := Hlt) in Hobs_weak_locks by (rewrite gssThreadRes; simpl; auto).
              erewrite restrPermMap_irr' with (Hlt' := HltF) in Hobs_weak_locks by (rewrite gssThreadRes; simpl; auto).
              (* apply the lemma *)
              eapply weak_mem_obs_eq_restrEq with (Hlt := Hlt) (HltF := HltF); eauto.
              erewrite <- weak_obs_eq_setMax; now eapply (weak_obs_eq Hobs_eq').
              (* proof of strong_mem_obs_eq*)
              erewrite restrPermMap_irr' with (Hlt' := Hlt) in obs_eq_locks0 by (rewrite gssThreadRes; simpl; auto).
              erewrite restrPermMap_irr' with (Hlt' := HltF) in obs_eq_locks0 by (rewrite gssThreadRes; simpl; auto).
              eapply strong_mem_obs_eq_disjoint_step; eauto.
              (* stability of contents of DryConc *)
              intros.
              pose proof (fst (thread_data_lock_coh _ Hinv _ pfc) _ pfc).
              eapply CoreLanguageDry.initial_core_stable_val with (Hlt2 := Hlt); eauto.
              rewrite gssThreadRes; simpl;
                by eauto.
              (* stability of contents of FineConc *)
              intros.
              pose proof (fst (thread_data_lock_coh _ HinvF _ pff) _ pff).
              simpl.
              eapply CoreLanguageDry.initial_core_stable_val with (Hlt2 := HltF); eauto.
              rewrite gssThreadRes; simpl;
                by eauto.
          + (** unmapped blocks*)
            intros b2 Hfi' ofs.
            subst.
            rewrite gssThreadRes. simpl.
            specialize (Hperm_unmapped _ Hfi' ofs).
            rewrite! restrPermMap_Cur in Hperm_unmapped.
            rewrite Hperm_unmapped.
            rewrite getCurPerm_correct;
              by auto.
        - (* block ownership*)
          (*sketch: the invariant is maintanted by coresteps hence it
            will hold for tpf'. Moreover we know that the new blocks in
            mc'|i will be mapped to new blocks in mf' by inject separated,
                where the permissions are empty for other threads. *)
          intros j pffj Hij b1 b2 Hfi' Hfi ofs.
          specialize (Hseparated _ _ Hfi Hfi').
          destruct Hseparated as [Hinvalidmc1 Hinvalidmf1].

            erewrite restrPermMap_valid in Hinvalidmf1.
            pose proof (invalid_block_empty (fst (compat_th _ _ Hcompf pffj)) Hinvalidmf1 ofs).
            pose proof (invalid_block_empty (snd (compat_th _ _ Hcompf pffj)) Hinvalidmf1 ofs);
              split; by assumption.
        - intros bl ofsl rmap b1 b2 ofs Hfi' Hfi Hres.
          specialize (Hseparated _ _ Hfi Hfi').
          destruct Hseparated as [Hinvalidmc1 Hinvalidmf1].
          erewrite restrPermMap_valid in Hinvalidmf1.
          pose proof (invalid_block_empty (fst (compat_lp _ _ Hcompf _ _ Hres)) Hinvalidmf1 ofs).
          pose proof (invalid_block_empty (snd (compat_lp _ _ Hcompf _ _ Hres)) Hinvalidmf1 ofs);
            split; by assumption.
      }
    }
  Qed.

  (*TODO: move this *)
  Lemma setMaxPerm_valid:
    forall m b, Mem.valid_block m b <-> Mem.valid_block (setMaxPerm m) b.
  Proof.
    intros.
    unfold Mem.valid_block, setMaxPerm. simpl.
    now auto.
  Qed.

  Lemma weak_tsim_fstep:
    forall tpc tpf tpf' mc mf mf' i j f U tr tr'
      (pffi: containsThread tpf i)
      (pfcj: containsThread tpc j) (pffj: containsThread tpf j)
      (pffj': containsThread tpf' j)
      (Hcompc: mem_compatible tpc mc)
      (Hcompf: mem_compatible tpf mf)
      (Hcompf': mem_compatible tpf' mf')
      (HinvF: invariant tpf),
      let mrestr := restrPermMap (((compat_th _ _ Hcompf) pffi).1) in
      forall (Hinternal: pffi$mrestr @ I)
        (Hstep: fmachine_step (i :: U, tr, tpf) mf (U, tr',tpf') mf')
        (HweakSim: weak_tsim f pfcj pffj Hcompc Hcompf),
      weak_tsim f pfcj pffj' Hcompc Hcompf'.
  Proof.
    intros.
    Opaque OrdinalPool.containsThread OrdinalPool.getThreadR.
    destruct HweakSim as [Hweak_data Hweak_locks].
    destruct Hweak_data
      as [Hdomain_invalid Hdomain_valid Hcodomain_valid Hinjective Hperm_obs_weak_data].
    pose proof (perm_obs_weak Hweak_locks) as Hperm_obs_weak_lock.
    absurd_internal Hstep;
      do 2 constructor; auto.
    - (* Case of start step*)
      intros b1 b2 Hf.
      erewrite restrPermMap_valid.
      erewrite <- diluteMem_valid.
      specialize (Hcodomain_valid b1 b2 Hf).
      erewrite restrPermMap_valid in Hcodomain_valid.
      simpl.
      inversion Hperm; subst.
      erewrite <- setMaxPerm_valid.
      eapply initial_core_validblock;
        now eauto.
    - (* Case of start step *)
      intros b1 b2 ofs Hf.
      specialize (Hperm_obs_weak_data _ _ ofs Hf).
      clear - Hinitial Hperm Hf Hcodomain_valid Hperm_obs_weak_data semAxioms.
      inversion Hperm; subst.
      destruct (j == tid) eqn:Hjtid; move/eqP:Hjtid=>Hjtid.
      + subst.
        eapply initial_core_decay in Hinitial.
        specialize (Hinitial b2 ofs).
        destruct Hinitial as [_ Hold].
        apply Hcodomain_valid in Hf.
        specialize (Hold Hf).
        unfold permission_at in Hperm_obs_weak_data.
        do 2 erewrite restrPermMap_Cur.
        rewrite gssThreadRes.
        rewrite getCurPerm_correct.
        unfold permission_at.
        rewrite <- Hold.
        rewrite <- restrPermMap_Cur with (Hlt := fst (compat_th _ _ Hcompc pfcj)).
        unfold permission_at.
        Tactics.pf_cleanup.
        assumption.
      + do 2 rewrite restrPermMap_Cur.
        simpl in *.
        erewrite OrdinalPool.gsoThreadRes with (cntj := pffj); eauto.
        do 2 rewrite restrPermMap_Cur in Hperm_obs_weak_data;
          by assumption.
    - (* case of start step, valid_block *)
      intros b1 b2 Hf.
      erewrite restrPermMap_valid.
      erewrite <- diluteMem_valid.
      specialize (Hcodomain_valid b1 b2 Hf).
      erewrite restrPermMap_valid in Hcodomain_valid.
      simpl.
      inversion Hperm; subst.
      erewrite <- setMaxPerm_valid.
      eapply initial_core_validblock;
        now eauto.
    - intros b1 b2 ofs Hf.
      specialize (Hperm_obs_weak_lock _ _ ofs Hf).
      clear - Hinitial Hperm Hf Hcodomain_valid Hperm_obs_weak_lock.
      inversion Hperm; subst.
      rewrite! restrPermMap_Cur in Hperm_obs_weak_lock.
      do 2 rewrite restrPermMap_Cur.
      destruct (j == tid) eqn:Hjtid; move/eqP:Hjtid=>Hjtid.
      + subst.
        simpl. erewrite OrdinalPool.gssThreadRes. simpl.
        Tactics.pf_cleanup.
        assumption.
      + simpl.
        erewrite OrdinalPool.gsoThreadRes with (cntj := pffj) by eauto.
        assumption.
    - (* Case of resume step*)
      intros b1 b2 ofs Hf.
      specialize (Hperm_obs_weak_data b1 b2 ofs Hf).
      do 2 rewrite restrPermMap_Cur.
      do 2 rewrite restrPermMap_Cur in Hperm_obs_weak_data.
      simpl in *.
      erewrite OrdinalPool.gThreadCR with (cntj := pffj);
        by assumption.
    - intros b1 b2 ofs Hf.
      specialize (Hperm_obs_weak_lock b1 b2 ofs Hf).
      do 2 rewrite restrPermMap_Cur.
      do 2 rewrite restrPermMap_Cur in Hperm_obs_weak_lock.
      simpl in *.
      erewrite OrdinalPool.gThreadCR with (cntj := pffj);
        by assumption.
    - (*Case of corestep*)
      intros b1 b2 Hf.
      erewrite restrPermMap_valid.
      erewrite <- diluteMem_valid.
      specialize (Hcodomain_valid b1 b2 Hf).
      erewrite restrPermMap_valid in Hcodomain_valid.
      simpl.
      erewrite <- setMaxPerm_valid.
      eapply ev_step_validblock;
        by eauto.
    - intros b1 b2 ofs Hf.
      specialize (Hperm_obs_weak_data _ _ ofs Hf).
      clear - Hcorestep Hf Hcodomain_valid Hperm_obs_weak_data semAxioms.
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
          simpl in *.
          destruct ((OrdinalPool.getThreadR pfcj).1 # b1 ofs); simpl;
            by constructor.
        * rewrite <- Heq.
          rewrite <- restrPermMap_Cur with (Hlt := fst (compat_th _ _ Hcompc pfcj)).
          unfold permission_at.
          Tactics.pf_cleanup.
            by assumption.
      + do 2 rewrite restrPermMap_Cur.
        simpl in *.
        erewrite OrdinalPool.gsoThreadRes with (cntj := pffj); eauto.
        do 2 rewrite restrPermMap_Cur in Hperm_obs_weak_data;
          by assumption.
    - intros b1 b2 Hf.
      erewrite restrPermMap_valid.
      erewrite <- diluteMem_valid.
      specialize (Hcodomain_valid b1 b2 Hf).
      erewrite restrPermMap_valid in Hcodomain_valid.
      simpl.
      erewrite <- setMaxPerm_valid.
      eapply ev_step_validblock;
        by eauto.
    - intros b1 b2 ofs Hf.
      specialize (Hperm_obs_weak_lock _ _ ofs Hf).
      clear - Hcorestep Hf Hcodomain_valid Hperm_obs_weak_lock.
      rewrite! restrPermMap_Cur in Hperm_obs_weak_lock.
      do 2 rewrite restrPermMap_Cur.
      destruct (j == tid) eqn:Hjtid; move/eqP:Hjtid=>Hjtid.
      + subst.
        simpl. erewrite OrdinalPool.gssThreadRes. simpl.
        Tactics.pf_cleanup.
        assumption.
      + simpl.
        erewrite OrdinalPool.gsoThreadRes with (cntj := pffj) by eauto.
        assumption.
    - inversion Hperm; subst.
      unfold mrestr in Hinternal.
      rewrite Hat_external in Hinternal.
      discriminate.
    - inversion Hperm; subst.
      unfold mrestr in Hinternal.
      rewrite Hat_external in Hinternal.
      discriminate.
  Qed.

  Lemma cmachine_step_invariant:
    forall tpc mc trc tpc' mc' trc' tpc'' trc'' mc'' U U' U'' n
      (HstepN: corestepN n
                         (U, trc, tpc) mc (U', trc',tpc') mc')
      (Hstep: cmachine_step (U', trc', tpc') mc' (U'',trc'', tpc'') mc''),
      invariant tpc.
  Proof.
    intros. destruct n; simpl in HstepN. inversion HstepN; subst.
    inversion Hstep; subst; try inversion Htstep; auto.
    simpl in *; subst; auto.
    destruct HstepN as [tpc''' [mc''' [Hstep0 _]]].
    clear Hstep.
    inversion Hstep0; subst; try inversion Htstep; auto.
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
              match unlift (ordinal_pos_incr (OrdinalPool.num_threads tp)) n with
              | Some (Ordinal _ cntj') => _
              | None => f'
              end).
    simpl in *.
    eapply (fp n0 cntj').
  Defined.

  Transparent OrdinalPool.containsThread.
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
    unfold OrdinalPool.containsThread in cnti.
    simpl in cnti;
      by Tactics.pf_cleanup.
    exfalso.
    simpl in *.
    unfold OrdinalPool.containsThread in *.
    simpl in *.
    assert (Hcontra: (ordinal_pos_incr (OrdinalPool.num_threads tp))
                       != (Ordinal (n:=(OrdinalPool.num_threads tp).+1) (m:=i) cnti')).
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
    destruct (unlift (ordinal_pos_incr (OrdinalPool.num_threads tp))
                     (Ordinal (n:=(OrdinalPool.num_threads tp).+1)
                              (m:=OrdinalPool.num_threads tp) cnt')) eqn:H.
    apply unlift_m_inv in H.
    destruct o. simpl in *.
    subst. exfalso;
      ssromega.
    rewrite H.
      by reflexivity.
  Qed.
  Opaque OrdinalPool.containsThread.

  (** *** Safety and simulation lemmas *)

  (** If some state is [csafe] then it can take a [cmachine_step]*)
  Lemma csafe_internal_step:
    forall tp tr m i (cnti: containsThread tp i) U n
      (Hn: n > 0)
      (Hcmpt: mem_compatible tp m),
      let mrestr := restrPermMap ((compat_th _ _ Hcmpt cnti).1) in
      forall (Hinternal: cnti$mrestr @ I)
        (Hsafe: csafe ((i :: U),tr,tp) m n),
    exists tp' tr' m', cmachine_step ((i :: U), tr, tp) m
                            ((i :: U), tr ++ tr', tp') m'.
  Proof.
    intros.
    inversion Hsafe; simpl in *.
    - subst; by exfalso.
    - subst; by exfalso.
    - do 3 eexists; eauto.
    - inversion Hstep; progress subst;
      simpl in *;
      try match goal with
          | [H: ?X :: ?Y = ?Y |- _] =>
            exfalso; eapply list_cons_irrefl; eauto
          end;
      subst; (try by exfalso);
      unfold getStepType in Hinternal; inversion HschedN; subst.
      inversion Htstep; subst.
      Tactics.pf_cleanup.
      rewrite Hcode in Hinternal.
      simpl in Hinternal.
      inversion Hperm; subst.
      unfold mrestr in Hinternal.
      rewrite Hat_external in Hinternal;
        by discriminate.
      inversion Htstep;
      Tactics.pf_cleanup;
      rewrite Hcode in Hinternal;
      simpl in Hinternal;
        by discriminate.
      exfalso;
        now eauto.
  Qed.

  (** Proof of simulation for internal steps*)
  Lemma sim_internal : sim_internal_def.
  Proof.
    unfold sim_internal_def.
    intros.
    inversion Hsim as
        [HnumThreads HmemCompC HmemCompF HsafeC
                     HsimWeak Hfpsep HsimStrong HsimRes HunmappedRes
                     HinvF HmaxF Hmemc_wd Htpc_wd Hge_wd Hge_spec Hxs HtraceSim].
    assert (pfc: containsThread tpc i)
      by (eapply HnumThreads; eauto).
    (** Strong simulation for thread i*)
    destruct (HsimStrong i pfc pff)
      as (tpc' &  mc' & Hincr & Hsynced & Hexec & Htsim &
          Hownedi & Hownedi_lp & Hunmapped);
      clear HsimStrong.
    assert (pfc': containsThread tpc' i)
      by (clear - Hexec pfc;
           eapply containsThread_internal_execution in pfc; eauto).
    specialize (Htsim pfc').
    assert (HmemCompF = mem_compf Hsim)
      by (eapply proof_irr).
    subst.
    (** The coarse machine is also at internal*)
    assert (memCompC' := internal_execution_compatible HmemCompC Hexec).
    specialize (Htsim memCompC').
    assert (Hdomainf: domain_memren f mc)
      by (destruct (HsimWeak _ pfc pff) as [HsimWeak' _];
          eapply weak_obs_eq_domain_ren in HsimWeak'; eauto).
    assert (Hwd := internal_execution_wd _ _ Hdomainf Hmemc_wd Htpc_wd
                                         Hge_wd(ren_incr_domain_incr
                                                  (Hge_spec).1) Hexec).
    destruct Hwd as [Hwd_mem' [[f' [Hincrf' Hdomainf']] Htp_wd']].
    assert (Hinternal_pfc': pfc' $ (restrPermMap ((compat_th _ _ memCompC') pfc')#1) @ I).
    { assert(Hmemc_wd': valid_mem (restrPermMap ((compat_th _ _ memCompC') pfc')#1))
        by (erewrite <- restrPermMap_mem_valid; now eauto).
      assert (Hincr_ge': ren_incr fg (fp i pfc))
        by (eapply ren_incr_trans; eauto; now destruct Hge_spec).
      erewrite (stepType_inj pff pfc' Internal Hge_spec.2 Hincr_ge' Hge_wd
                             Hmemc_wd' (obs_eq_data Htsim) (code_eq Htsim)).
      assumption.
    }
    (** It's safe to step the coarse grained machine for one more step on i*)
    specialize (HsafeC ([:: i]) trc).
    assert (HcoreN := safety_det_corestepN_internal xs HsafeC Hexec).
    destruct HcoreN as [trc' [HcorestepN Hsafety]].
    destruct (@csafe_internal_step _ _ _ _ pfc' _ (fuelF.+2 + size [seq x <- xs | x != i])
                                   ltac:(ssromega) memCompC' Hinternal_pfc' Hsafety) as
        (tpc'' & trc'' & mc'' & Hstep').
    assert (HinvC: invariant tpc)
      by (eapply cmachine_step_invariant; eauto).
    eapply at_internal_cmachine_step with (cnt := pfc') in Hstep'; eauto.
    destruct Hstep' as [Hstep' _].
    assert (Hge_incr': ren_incr fg (fp i pfc))
      by (destruct Hge_spec; eapply ren_incr_trans; eauto).
    (** And from this we derive safety for 1 step for FineConc*)
    destruct (tsim_fstep_safe trf HmaxF HinvF Hge_wd (snd Hge_spec)
                              Hge_incr' Htsim Hwd_mem' Hstep')
      as (tpf' & mf' & fi' & tr' & HstepF & HmaxF' & Hincr' & Hsepi & Htsim'
          & Howned' & Hownedlp').
    assert (HstepF_empty := HstepF [::]).
    assert (pfc'': containsThread tpc'' i)
      by (eapply containsThread_internal_step; eauto).
    assert (pff': containsThread tpf' i).
    { eapply (@StepLemmas.step_containsThread _  HybridFineMachine.scheduler
                                              FineDilMem _ _ _ _ _ _ _ _ _  pff); eauto.
      unfold fmachine_step in *. simpl in HstepF_empty.
      now eapply HstepF_empty.
    }
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
    - unfold fmachine_step in HstepF_empty. simpl in HstepF_empty.
      intros k;
      split;
      intro pfk;
      [apply HnumThreads in pfk | apply HnumThreads]; eauto.
      eapply (@StepLemmas.step_containsThread _  HybridFineMachine.scheduler
                                              FineDilMem _ _ _ _ _ _ _ _ _ pfk);
        now eauto.
      eapply fstep_containsThread';
        now eauto.
    - intros.
      simpl.
      rewrite <- addSnnS.
      apply (safeCoarse Hsim).
    - (** Proof of weak simulation between threads *)
      intros j pfcj pffj'.
      assert (pffj: containsThread tpf j)
        by (eapply fstep_containsThread';
            now eauto).
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
      + Tactics.pf_cleanup.
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
      + Tactics.pf_cleanup.
        rewrite gssFP.
        rewrite gsoFP; auto.
        intros b b' b2 b2' Hf Hf' Hfk' Hfj'.
        destruct (fp j pfc b') as [b2''|] eqn:Hfj.
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
        Tactics.pf_cleanup. rewrite gssFP.
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
          by (eapply fstep_containsThread';
              now eauto).
        erewrite <- @StepLemmas.gsoThreadR_step with (Sch:= HybridFineMachine.scheduler)
                                                    (DilMem := FineDilMem) (pfj := pffk)
          by (eauto; unfold fmachine_step in HstepF_empty; simpl in HstepF_empty;
              eapply HstepF_empty).
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
        split.
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
        specialize (Hfb1 Hinvalidmc'b1);
          by eauto.
        (** Proof of empty unmapped blocks*)
        intros b2 Hfi' ofs.
        destruct (Htsim' pfc'' pff' memCompC'' memCompF') as [_ Hunmapped'].
        specialize (Hunmapped' b2 Hfi' ofs).
        erewrite Hunmapped'.1, Hunmapped'.2.
        eapply Hunmapped.
        intros (b1 & Hf).
        apply Hincr' in Hf.
        eapply Hfi'; by eexists; eauto.
      }
      { (** Proof of strong simulation for threads different than i*)
        simpl.
        rewrite gsoFP; auto.
        erewrite if_false by (apply/eqP; intros Hcontra; auto).
        clear HsimWeak Htsim Hincr Hincr'.
        assert (HsimStrong := simStrong Hsim).
        assert (pffj: containsThread tpf j)
          by (eapply (fstep_containsThread' pff pffj'); now eauto).
        destruct (HsimStrong j pfcj pffj)
          as (tpcj' & mcj' & Hincrj & Hsyncedj & Hexecj & Htsimj & Hownedj
              & Hownedj_lp & Hunmappedj).
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
              pose proof (StepLemmas.permission_at_step Heq pffj pffj' (mem_compf Hsim)
                                                        memCompF' HstepF_empty b2 ofs) as Hperm_eq.
              rewrite <- Hperm_eq.
                now apply (perm_obs_weak (weak_obs_eq memObsEqj)).
          }
          constructor. (*strong_obs_eq proof *)
          { intros b1 b2 ofs.
            pose proof (StepLemmas.permission_at_step Heq pffj pffj' (mem_compf Hsim)
                                                      memCompF' HstepF_empty b2 ofs) as Hperm_eq.
            rewrite <- Hperm_eq.
              now apply (perm_obs_strong (strong_obs_eq memObsEqj)).
          }
          { intros b1 b2 ofs Hfj Hperm. unfold restrPermMap. simpl.
            assert (Hval := val_obs_eq (strong_obs_eq memObsEqj)).
            specialize (Hval b1 b2 ofs Hfj Hperm).
            unfold restrPermMap in Hval. simpl in Hval.
            assert (Hpermf: Mem.perm (restrPermMap (fst (compat_th _ _ (mem_compf Hsim) pffj)))
                                     b2 ofs Cur Readable).
            { specialize (HstepF [::]).
              assert (Hperm_eqf :=
                        StepLemmas.permission_at_step Heq pffj pffj' (mem_compf Hsim) memCompF'
                                            HstepF b2 ofs).
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
            specialize (HstepF [::]).
            erewrite <- @fmachine_step_disjoint_val with
            (tp := tpf) (i := i) (j := j) (m' := mf')
                        (m := mf) (tp' := tpf') (U := [::]);
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
              erewrite <- @StepLemmas.gsoThreadR_step with (Sch := HybridFineMachine.scheduler)
                                                          (DilMem := FineDilMem)
                                                          (pfj := pffj) (pfj' := pffj');
                eauto.
              rewrite <- restrPermMap_Cur with (Hlt := snd (compat_th _ _ memCompCj' pfcj')).
              rewrite <- restrPermMap_Cur with (Hlt := snd (compat_th _ _ (mem_compf Hsim) pffj)).
              now apply (perm_obs_weak (weak_obs_eq memObsEqj_locks)).
              now eapply HstepF_empty.
          }
          constructor. (*strong_obs_eq proof *)
          { intros b1 b2 ofs.
            rewrite !restrPermMap_Cur.
            erewrite <- @StepLemmas.gsoThreadR_step with (Sch := HybridFineMachine.scheduler)
                                                        (DilMem := FineDilMem)
                                                        (pfj := pffj) (pfj' := pffj');
              eauto.
            rewrite <- restrPermMap_Cur with (Hlt := snd (compat_th _ _ memCompCj' pfcj')).
            rewrite <- restrPermMap_Cur with (Hlt := snd (compat_th _ _ (mem_compf Hsim) pffj)).
            now apply (perm_obs_strong (strong_obs_eq memObsEqj_locks)).
            now eapply HstepF_empty.
          }
          { intros b1 b2 ofs Hfj Hperm. unfold restrPermMap. simpl.
            assert (Hval := val_obs_eq (strong_obs_eq memObsEqj_locks)).
            specialize (Hval b1 b2 ofs Hfj Hperm).
            unfold restrPermMap in Hval. simpl in Hval.
            assert (Hpermf: Mem.perm (restrPermMap (snd (compat_th _ _ (mem_compf Hsim) pffj)))
                                     b2 ofs Cur Readable).
            { specialize (HstepF [::]).
              assert (Hperm_eqf :=
                        StepLemmas.permission_at_step Heq pffj pffj' (mem_compf Hsim) memCompF'
                                            HstepF b2 ofs).
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
            specialize (HstepF [::]).
            erewrite <- @fmachine_step_disjoint_val with
            (tp := tpf) (i := i) (j := j) (m' := mf')
                        (m := mf) (tp' := tpf') (U := [::]);
              by eauto.
          }
        }
        split.
        (** block ownership *)
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
                                                (obs_eq_data Htsimj)))). {
        specialize (Hcodomain _ _ Hfj).
        erewrite restrPermMap_valid in Hcodomain.
        clear - Hownedj Hcodomain Hjk HstepF_empty Hinternal semAxioms.
        absurd_internal HstepF_empty;
          try by erewrite OrdinalPool.gThreadCR with (cntj := pff).
        (* initial_core case *)
        inversion Hperm; subst.
        apply initial_core_decay in Hinitial.
        destruct (Hinitial b2 ofs) as [_ Hdecay_valid].
        assert (Hp := restrPermMap_Cur (fst (compat_th _ _ (mem_compf Hsim) pff)) b2 ofs).
        unfold permission_at in Hp.
        specialize (Hdecay_valid Hcodomain).
        specialize (Hdecay_valid Cur).
        rewrite Hp in Hdecay_valid.
        destruct Hownedj as [Hownedj1 Hownedj2].
        rewrite Hownedj1 in Hdecay_valid.
        erewrite OrdinalPool.gssThreadRes.
        rewrite getCurPerm_correct;
          by auto.
        (* corestep case*)
        apply ev_step_ax1 in Hcorestep.
        apply corestep_decay in Hcorestep.
        destruct (Hcorestep b2 ofs) as [_ Hdecay_valid].
        assert (Hp := restrPermMap_Cur (fst (compat_th _ _ (mem_compf Hsim) pff)) b2 ofs).
        unfold permission_at in Hp.
        destruct (Hdecay_valid Hcodomain) as [Hnew | Hstable].
        destruct (Hnew Cur) as [Hcontra _].
        rewrite Hp in Hcontra.
        destruct Hownedj; simpl in *;
          by congruence.
        specialize (Hstable Cur).
        rewrite Hp in Hstable.
        destruct Hownedj as [Hownedj1 Hownedj2].
        rewrite Hownedj1 in Hstable.
        erewrite OrdinalPool.gssThreadRes.
        rewrite getCurPerm_correct;
          by auto.
        }
        (** case k is another thread*)
        replace (OrdinalPool.getThreadR pffk') with (getThreadR pffk') by reflexivity.
        erewrite <- @StepLemmas.gsoThreadR_step with (Sch := HybridFineMachine.scheduler)
                                                   (DilMem := FineDilMem)
                                                   (pfj := pffk);
          eauto.
        now eapply HstepF_empty.
        split.
        (** block ownership for lockres*)
        intros bl ofsl rmap b1 b2 ofs Hfj Hf Hres.
        replace (OrdinalPool.lockRes) with lockRes in Hres by reflexivity.
        erewrite gsoLockRes_fstepI with (tp := tpf) in Hres;
          by eauto.
        (** unmapped blocks*)
        intros b2 Hfj ofs.
        specialize (Hunmappedj _ Hfj ofs).
        replace (OrdinalPool.getThreadR pffj') with (getThreadR pffj') by reflexivity.
        erewrite <- @StepLemmas.gsoThreadR_step with  (Sch := HybridFineMachine.scheduler)
                                          (DilMem := FineDilMem)
                                          (pfj := pffj); eauto.
        now apply HstepF_empty.
      }
    - (** lock resources sim*)
        destruct HsimRes as [HsimRes [Hlock_mapped Hlock_if]].
        split.
        + intros.
          assert (Hl_eq := gsoLockRes_fstepI pff (mem_compf Hsim) Hinternal HstepF_empty).
          assert (Hl2': lockRes tpf (bl2, ofs) = Some rmap2)
            by (rewrite <- Hl_eq; assumption).
          destruct (HsimRes _ _ _ _ _ Hf Hl1 Hl2') as [HsimRes1 HsimRes2].
          split.
          * destruct HsimRes1 as [HpermRes1 HvalRes1].
            constructor.
            intros b1 b2 ofs0 Hf1.
            do 2 rewrite restrPermMap_Cur.
            specialize (HpermRes1 _ _ ofs0 Hf1);
              by do 2 rewrite restrPermMap_Cur in HpermRes1.
            intros b1 b2 ofs0 Hf1 Hperm.
            simpl in *.
            specialize (HvalRes1 _ _ ofs0 Hf1 Hperm).
            assert (HpermF: Mem.perm (restrPermMap (fst (compat_lp _ _ (mem_compf Hsim)
                                                                   (bl2,ofs) _ Hl2')))
                                     b2 ofs0 Cur Readable).
            { unfold Mem.perm in *.
              specialize (HpermRes1 _ _ ofs0 Hf1).
              unfold permission_at in HpermRes1.
                by rewrite HpermRes1.
            }
            absurd_internal HstepF_empty; auto.
            (* initial_core case *)
            inversion Hperm0; subst.
            assert (Hcmpt = mem_compf Hsim)
              by (eapply proof_irr); subst.
            erewrite <- @CoreLanguageDry.initial_core_disjoint_val_lockpool with (m := mf) (m' := m');
              simpl; eauto. eapply Hinitial.
            (* corestep case *)
            apply ev_step_ax1 in Hcorestep.
            assert (Hcmpt = mem_compf Hsim)
              by (eapply proof_irr).
            subst.
            erewrite <- @CoreLanguageDry.corestep_disjoint_val_lockpool with (m := mf) (m' := m');
              simpl; now eauto.
          * destruct HsimRes2 as [HpermRes2 HvalRes2].
            constructor.
            intros b1 b2 ofs0 Hf1.
            do 2 rewrite restrPermMap_Cur.
            specialize (HpermRes2 _ _ ofs0 Hf1);
              by do 2 rewrite restrPermMap_Cur in HpermRes2.
            intros b1 b2 ofs0 Hf1 Hperm.
            simpl in *.
            specialize (HvalRes2 _ _ ofs0 Hf1 Hperm).
            assert (HpermF: Mem.perm (restrPermMap (snd (compat_lp _ _ (mem_compf Hsim)
                                                                   (bl2,ofs) _ Hl2')))
                                     b2 ofs0 Cur Readable).
            { unfold Mem.perm in *.
              specialize (HpermRes2 _ _ ofs0 Hf1).
              unfold permission_at in HpermRes2.
                by rewrite HpermRes2.
            }
            absurd_internal HstepF_empty; auto.
            (* initial_core case *)
            inversion Hperm0; subst.
            assert (Hcmpt = mem_compf Hsim)
              by (eapply proof_irr); subst.
            erewrite <- @CoreLanguageDry.initial_core_disjoint_val_lockpool with (m := mf) (m' := m');
              simpl; eauto. eapply Hinitial.
            (* corestep case *)
            apply ev_step_ax1 in Hcorestep.
            assert (Hcmpt = mem_compf Hsim)
              by (eapply proof_irr).
            subst.
            erewrite <- @CoreLanguageDry.corestep_disjoint_val_lockpool with (m := mf) (m' := m');
              simpl; now eauto.
        +  split.
           intros bl2 ofs Hres.
           erewrite gsoLockRes_fstepI with (tp := tpf) (tp' := tpf') in Hres; eauto.
           intros bl1 bl2 ofs Hf.
           erewrite gsoLockRes_fstepI with (tp' := tpf');
             now eauto.
    - (** unmapped blocks are empty on resources*)
      intros bl ofsl rmap Hres b2 Hf ofs.
      erewrite gsoLockRes_fstepI with (tp := tpf) in Hres by eauto.
      eapply HunmappedRes;
        now eauto.
    - (*invariant tpf' *)
      eapply fmachine_step_invariant with (tp := tpf);
        now eauto.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - assumption.
    - intros j Hin.
      inversion Hin; subst;
        now auto.
    - assumption.
      Unshelve. all:eauto.     
  Qed.

  Opaque containsThread getThreadC getThreadR.
  (** ** Proof of simulation for stop steps *)
  Lemma suspend_step_inverse:
    forall i U U' tpc trc tpc' trc' mc mc'
      (cnt: containsThread tpc i)
      (Hcompc: mem_compatible tpc mc),
      let mrestr := restrPermMap (((compat_th _ _ Hcompc) cnt).1) in
      forall (Hsuspend: cnt$mrestr @ S)
        (Hstep: cmachine_step (i :: U, trc, tpc) mc (U', trc', tpc') mc'),
        U = U' /\ mc = mc' /\ trc = trc' /\ mem_compatible tpc mc /\
        suspend_thread mc cnt tpc'.
  Proof.
    intros.
    inversion Hstep; simpl in *; subst; inversion HschedN; subst;
      try (inversion Htstep || inversion Hhalted); subst; Tactics.pf_cleanup;
    unfold getStepType in Hsuspend;
    try rewrite Hcode in Hsuspend; simpl in Hsuspend;
    try match goal with
        | [H: match ?Expr with _ => _ end = _, H2: ?Expr = _ |- _] =>
          rewrite H2 in H
        end; try discriminate;
    try match goal with
        | [H: ~ containsThread _ _, H2: containsThread _ _ |- _] =>
          exfalso; by auto
        | [H: halted _ _ _  |- _] =>
          destruct (at_external_halted_excl c mrestr) as [Hnot_ext | Hcontra];
            [rewrite Hnot_ext in Hsuspend;
             destruct Hsuspend as [[_ ?] | [? _]]; discriminate |
             exfalso; eapply Hcontra; now eauto]
        end.
    apply ev_step_ax1 in Hcorestep.
    eapply corestep_not_at_external in Hcorestep.
    rewrite Hcorestep in Hsuspend.
    discriminate.
    inversion Hperm; subst.
    repeat (split; eauto).
  Qed.

  Lemma mem_obs_eq_step:
    forall tp1 tp2 tp1' m1 m2 m1' j f fg
      (pf1j: containsThread tp1 j)
      (pf1j': containsThread tp1' j)
      (Hcomp1: mem_compatible tp1 m1)
      (Hcomp1': mem_compatible tp1' m1')
      (Hinv: invariant tp1')
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg the_ge)
      (Hge_incr: ren_incr fg f)
      (Hvalid_mem: valid_mem m1)
      (Hcode_eq: ctl_inj f (getThreadC pf1j) (getThreadC pf1j'))
      (Hmem_obs_eq: mem_obs_eq f (restrPermMap (compat_th _ _ Hcomp1 pf1j).1)
                               (restrPermMap (compat_th _ _ Hcomp1' pf1j').1))
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
          ctl_inj f' (getThreadC pf2j) (getThreadC pf2j') /\
          mem_obs_eq f' (restrPermMap (compat_th _ _ Hcomp2 pf2j).1)
                     (restrPermMap (compat_th _ _ Hcomp2' pf2j').1)) /\
      (Mem.nextblock m1 = Mem.nextblock m1' ->
       (forall b1 b2 : block, f b1 = Some b2 -> b1 = b2) ->
       forall b1 b2 : block, f' b1 = Some b2 -> b1 = b2).
  Proof.
    intros.
    inversion Hstep as [[? Hcstep] | [[Hresume ?] | Hstart]].
    - inversion Hcstep; subst.
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pf1j') as [c1' | | |] eqn:Hcodej'; try by exfalso.
      apply ev_step_ax1 in Hcorestep.
      assert (H := corestep_obs_eq _ _ _ _ Hmem_obs_eq Hcode_eq Hfg Hge_wd
                                   Hge_incr Hcorestep).
      destruct H
        as (c2' & m2' & f' & Hcorestep' & Hcode_eq'
            & Hobs_eq & Hincr & Hseparated
            & Hnextblock & Hinverse & Hid & Hunmapped).
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
        destruct Hobs_eq as [[Hinvalid' Hvalid' ? ? Hweak_perm] [Hstrong_perm Hval]].
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
            assert (H:= restrPermMap_Cur (fst (compat_th _ _ Hcomp2 pf2j)) b1 ofs).
            unfold permission_at in H.
            rewrite H in Hreadable.
            rewrite gssThreadRes in Hreadable;
              rewrite getCurPerm_correct in Hreadable.
              by assumption.
      }
      do 2 erewrite restrPermMap_nextblock in Hid;
        by eauto.
    - {(* Case internal step is a resume step*)
      subst m2.
      inversion Hresume; subst.
      Tactics.pf_cleanup.
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pf1j') as [ | |c1'|] eqn:Hcode'; try by exfalso.
      destruct Hcode_eq as [Hcode_eq Hval_eq].
      inversion Hval_eq; subst.
      inversion Hperm; subst.
      assert (Hvalid_mem': valid_mem (restrPermMap (compat_th _ _ Hcomp1 pf1j)#1))
        by (erewrite <- restrPermMap_mem_valid; eauto).
      assert (Hat_external_spec := core_inj_ext _ _ Hfg Hge_wd Hge_incr Hvalid_mem'
                                                Hcode_eq Hmem_obs_eq).
      rewrite Hat_external in Hat_external_spec.
      destruct X as [ef vs].
      destruct (at_external semSem c1' (restrPermMap (compat_th _ _ Hcomp1' pf1j')#1))
        as [[? ?] | ] eqn:Hat_external';
        try by exfalso.
      destruct Hat_external_spec as [? ?]; subst.
      assert (Hvalid_val: match (Some (Vint Int.zero)) with
                          | Some v1 => valid_val f v1
                          | None => True
                          end)
        by (now simpl).
      assert (Hafter_external' :=
                core_inj_after_ext _ _ None Hfg Hge_wd Hge_incr
                                   Hcode_eq Hmem_obs_eq Hvalid_val Hafter_external).
      destruct Hafter_external' as [ov2 [c2' [Hafter_external'
                                                [Hcore_inj' Hval_obs]]]].
      destruct ov2 as [? |]; try by exfalso.
      inversion Hval_obs; subst.
      exists (updThreadC pf1j' (Krun c2')), m1', f.
      assert (Hinternal':
                internal_step pf1j' Hcomp1' (updThreadC pf1j' (Krun c2')) m1'). {
          clear - Hat_external' Hafter_external' Hcode' Hinv.
          right; left; split; econstructor; eauto.
          simpl; unfold DryHybridMachine.install_perm.
          reflexivity.
     }
      { split;
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
       erewrite restrPermMap_irr' with (Hlt' := fst (compat_th _ _ Hcomp1 pf1j)) by (rewrite gThreadCR; eauto).
       erewrite restrPermMap_irr' with (Hlt' := fst (compat_th _ _ Hcomp1' pf1j')) by (rewrite gThreadCR; eauto);
         by eauto.
      }
      }
    - (*case it's a start step*)
      inversion Hstart; subst.
      Tactics.pf_cleanup.
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pf1j') as [| | |vf' arg'] eqn:Hcodej'; try by exfalso.
      destruct Hcode_eq as [Hval_obs Harg_obs].
      inversion Hperm; subst.
      assert (Hargs_obs: val_obs_list f [:: arg] [:: arg'])
             by (econstructor; eauto using val_obs_list).
      assert (H := core_inj_init _ _ _ Hge_wd Hfg Hge_incr Hargs_obs Hval_obs Hmem_obs_eq Hinitial).
      destruct H
        as (c_new' & m2' & f' & Hinitial' & Hcode_eq'
            & Hobs_eq & Hincr & Hseparated
            & Hnextblock & Hinverse & Hid & Hunmapped).
      exists (updThread pf1j' (Krun c_new') (getCurPerm m2', (getThreadR pf1j').2)), m2', f'.
      assert (Hinternal':
                internal_step pf1j' Hcomp1'
                              (updThread pf1j' (Krun c_new') (getCurPerm m2', (getThreadR pf1j').2)) m2').
      { right. right. econstructor; eauto. simpl.
        unfold DryHybridMachine.install_perm. reflexivity.
      }
      split; first by assumption.
      split; first by assumption.
      split; first by assumption.
      split.
      erewrite! restrPermMap_nextblock in Hnextblock.
      left; assumption.
      split; first by assumption.
      split.
      { assert (pf2j := containsThread_internal_step Hstep pf1j).
        assert (pf2j' := containsThread_internal_step Hinternal' pf1j').
        assert (Hcomp2 := internal_step_compatible Hstep).
        assert (Hcomp2' := internal_step_compatible Hinternal').
        exists pf2j, pf2j', Hcomp2, Hcomp2'.
        constructor; first by do 2 rewrite gssThreadCode.
        destruct Hobs_eq as [[Hinvalid' Hvalid' ? ? Hweak_perm] [Hstrong_perm Hval]].
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
            assert (H:= restrPermMap_Cur (fst (compat_th _ _ Hcomp2 pf2j)) b1 ofs).
            unfold permission_at in H.
            rewrite H in Hreadable.
            rewrite gssThreadRes in Hreadable;
              rewrite getCurPerm_correct in Hreadable.
              by assumption.
      }
      do 2 erewrite restrPermMap_nextblock in Hid;
        by eauto.
  Qed.

  Lemma mem_obs_eq_execution:
    forall tp1 tp2 tp1' m1 m2 m1' j xs f fg
      (pf1j: containsThread tp1 j)
      (pf1j': containsThread tp1' j)
      (Hcomp1: mem_compatible tp1 m1)
      (Hcomp1': mem_compatible tp1' m1')
      (Hinv: invariant tp1')
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg the_ge)
      (Hge_incr: ren_incr fg f)
      (Hvalid_mem: valid_mem m1)
      (Htp_wd: tp_wd f tp1)
      (Hcode_eq: ctl_inj f (getThreadC pf1j) (getThreadC pf1j'))
      (Hmem_obs_eq: mem_obs_eq f (restrPermMap (compat_th _ _ Hcomp1 pf1j).1)
                               (restrPermMap (compat_th _ _ Hcomp1' pf1j').1))
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
          ctl_inj f' (getThreadC pf2j) (getThreadC pf2j') /\
          mem_obs_eq f' (restrPermMap (compat_th _ _ Hcomp2 pf2j).1)
                     (restrPermMap (compat_th _ _ Hcomp2' pf2j').1)) /\
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
      + exists tp1', m1', f.
        split; first by constructor.
        split; first by auto.
        split; first by congruence.
        split; first by auto.
        split; first by (intros; by exfalso).
        split; eauto.
        do 4 eexists; split; eauto.
     + simpl in HschedN;
        by inversion HschedN.
    - destruct (x == j) eqn:Hxj; move/eqP:Hxj=>Hxj.
      + subst x. inversion Hexec as [|tid U U' tp1a m1a tp0 m0].
        subst U U' tp1a m1a tp'' m''.
        simpl in Htrans. simpl in HschedN;
                           inversion HschedN; subst tid; clear HschedN Hexec.
        Tactics.pf_cleanup.
        assert (Htsim := mem_obs_eq_step _ _ Hinv Hfg Hge_wd Hge_incr Hvalid_mem Hcode_eq Hmem_obs_eq Hstep).
        destruct Htsim as
            (tp0' & m0' & f0 & Hstep0' & Hincr0' & Hsep0'
             & Hnextblock0' & Hinverse0' & Htsim0' & Hid0').
        destruct Htsim0' as [pfj' [pfj0' [Hcomp' [Hcomp0' [Hcode_eq0 Hmem_obs_eq0]]]]].
        Tactics.pf_cleanup.
        assert (Hinv0': invariant tp0')
          by (eapply internal_step_invariant; eauto).
        assert (Hge_incr0': ren_incr fg f0)
          by (eapply ren_incr_trans; eauto).
        assert (H_wd0: valid_mem m0 /\ tp_wd f0 tp0).
        { pose proof (internal_step_wd Hvalid_mem
                                       ltac:(erewrite restrPermMap_domain;
                                             eapply mem_obs_eq_domain_ren; eauto)
                                              Htp_wd Hge_wd
                                              ltac:(eapply ren_incr_domain_incr; eauto)
                                                     Hstep) as [? [? Htp_wd0]].
          split; [assumption |].
          eapply Htp_wd0;
            eauto.
          erewrite restrPermMap_domain;
            eapply mem_obs_eq_domain_ren;
            now eauto.
        }
        destruct H_wd0 as [Hvalid_mem0 Htp_wd0].
        destruct (IHxs _ _ _ _ Hinv0' _ Hge_incr0' _  Hvalid_mem0 _ _ _ Htp_wd0
                       Hcode_eq0 Hmem_obs_eq0 Htrans)
          as (tp2' & m2' & f2' & Hexec & Hincr2 & Hsep2
              & Hnextblock2 & Hinverse2 & Hsim2 & Hid2);
          exists tp2', m2', f2'.
        destruct Hsim2 as [pf2j [pf2j' [Hcomp2 [Hcomp2' [Hcode_eq2 Hmem_obs_eq2]]]]].
        split; first by (econstructor; simpl; eauto).
        split; first by (eapply ren_incr_trans; eauto).
        split.
        { (*injection separated *)
          intros b1 b2 Hf Hf2'.
          unfold ren_separated in *.
          destruct (valid_block_dec m0 b1) as [Hvalidm0 | Hinvalidm0].
          * apply (domain_valid (weak_obs_eq Hmem_obs_eq0)) in Hvalidm0.
            destruct Hvalidm0 as [x Hf0].
            assert (b2 = x).
            {  assert (Hf2'' : f2' b1 = Some x)
                by (eapply Hincr2; eauto).
               rewrite Hf2' in Hf2''. inversion Hf2''; by subst. }
            subst x.
            eapply Hsep0';
              by eauto.
          * apply (domain_invalid (weak_obs_eq Hmem_obs_eq0)) in Hinvalidm0.
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
        split; first by (do 4 eexists; simpl in *; split; eauto).
        intros Hnb1 Hf.
        specialize (Hid0' Hnb1 Hf).
        assert (Hnb0: Mem.nextblock m0 = Mem.nextblock m0')
          by (destruct Hnextblock0' as [[p [Hnb0 Hnb0']] | [Hnb0 Hnb0']];
                by rewrite Hnb0 Hnb0' Hnb1).
        specialize (Hid2 Hnb0 Hid0').
          by assumption.
    + destruct (IHxs _ _ _ _ Hinv _ Hge_incr _ Hvalid_mem _ _ _ Htp_wd Hcode_eq Hmem_obs_eq Hexec)
        as
          [tp2' [m2' [f2' [Hexec2
                             [Hincr2
                                [Hsep2 [Hnextblock2 [Hinverse2 [Hsim2 Hid2]]]]]]]]];
        exists tp2', m2', f2'.
      repeat (split; auto).
  Qed.

  (*TODO: this is a stronger version of the above, I should reuse the above
  proof as much as possible, but for now I am just copy-pasting*)
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
      (Hvalid_mem: valid_mem m1)
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
    inversion Hstep as [[? Hcstep] | [[Hresume ?] | Hstart]].
    - inversion Hcstep; subst.
      inversion Hsim as [Hcode_eq Hmem_obs_eq Hmem_obs_locks].
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pf1j') as [c1' | | |] eqn:Hcodej'; try by exfalso.
      apply ev_step_ax1 in Hcorestep.
      assert (H := corestep_obs_eq _ _ _ _ Hmem_obs_eq Hcode_eq Hfg Hge_wd
                                   Hge_incr Hcorestep).
      destruct H
        as (c2' & m2' & f' & Hcorestep' & Hcode_eq'
            & Hobs_eq & Hincr & Hseparated
            & Hnextblock & Hinverse & Hid & Hunmapped).
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
              assert (H:= restrPermMap_Cur (fst (compat_th _ _ Hcomp2 pf2j)) b1 ofs).
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
          eapply CoreLanguageDry.corestep_stable_val with (Hlt2 := Hlt); eauto.
          rewrite gssThreadRes; simpl; right;
            by (eapply (fst ((thread_data_lock_coh _ Hinv0) _ pf1j) _ pf1j)).
          (* stability of contents of FineConc *)
          intros.
          simpl.
          apply ev_step_ax1 in Hcorestep'.
          eapply CoreLanguageDry.corestep_stable_val with (Hlt2 := Hlt'); eauto.
          rewrite gssThreadRes; simpl; right;
            by (eapply (fst ((thread_data_lock_coh _ Hinv) _ pf1j') _ pf1j')).
      }
      do 2 erewrite restrPermMap_nextblock in Hid;
        by eauto.
    - (* Case internal step is a resume step*)
      subst m2.
      inversion Hsim as [Hcode_eq Hmem_obs_eq].
      inversion Hresume; subst.
      Tactics.pf_cleanup.
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pf1j') as [ | |c1'|] eqn:Hcode'; try by exfalso.
      destruct Hcode_eq as [Hcode_eq Hval_eq].
      inversion Hval_eq; subst.
      assert (Hvalid_mem': valid_mem (restrPermMap (compat_th _ _ Hcomp1 pf1j)#1))
        by (erewrite <- restrPermMap_mem_valid; eauto).
      assert (Hat_external_spec := core_inj_ext _ _  Hfg Hge_wd Hge_incr Hvalid_mem' Hcode_eq Hmem_obs_eq).
      inversion Hperm; subst.
      rewrite Hat_external in Hat_external_spec.
      destruct X as [? vs].
      destruct (at_external semSem c1' (restrPermMap (compat_th _ _ Hcomp1' pf1j')#1))
        as [[? ?] | ] eqn:Hat_external';
        try by exfalso.
      destruct Hat_external_spec as [?  ?]; subst.
      assert (Hvalid_val: match (Some (Vint Int.zero)) with
                          | Some v1 => valid_val f v1
                          | None => True
                          end)
        by (now simpl).
      assert (Hafter_external' :=
                core_inj_after_ext _ _  None
                                    Hfg Hge_wd Hge_incr Hcode_eq Hmem_obs_eq Hvalid_val Hafter_external).
      destruct Hafter_external' as [ov2 [c2' [Hafter_external'
                                                [Hcore_inj' Hval_obs]]]].
      destruct ov2 as [? |]; try by exfalso.
      inversion Hval_obs; subst.
      exists (updThreadC pf1j' (Krun c2')), m1', f.
      assert (Hinternal':
                internal_step pf1j' Hcomp1' (updThreadC pf1j' (Krun c2')) m1'). {
         { clear - Hat_external' Hafter_external' Hcode' Hinv.
             right; left; econstructor; eauto.
             eapply ResumeThread with (Hcmpt := Hcomp1');
               now eauto.
         }
      }
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
      erewrite restrPermMap_irr' with (Hlt' := fst (compat_th _ _ Hcomp1 pf1j)) by (rewrite gThreadCR; eauto).
      erewrite restrPermMap_irr' with (Hlt' := fst (compat_th _ _ Hcomp1' pf1j')) by (rewrite gThreadCR; eauto);
        by eauto.
      erewrite restrPermMap_irr' with (Hlt' := snd (compat_th _ _ Hcomp1 pf1j)) by (rewrite gThreadCR; eauto).
      erewrite restrPermMap_irr' with (Hlt' := snd (compat_th _ _ Hcomp1' pf1j')) by (rewrite gThreadCR; eauto);
        by eauto.
    - (*case it's a start step*)
      inversion Hsim as [Hcode_eq Hmem_obs_eq Hmem_obs_locks].
      inversion Hstart; subst.
      Tactics.pf_cleanup.
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pf1j') as [| | |vf' arg'] eqn:Hcodej'; try by exfalso.
      destruct Hcode_eq as [Hval_obs Harg_obs].
      inversion Hperm; subst.
      assert (Hargs_obs: val_obs_list f [:: arg] [:: arg'])
        by (econstructor; eauto using val_obs_list).
      assert (H := core_inj_init _ _ _ Hge_wd Hfg Hge_incr Hargs_obs Hval_obs Hmem_obs_eq Hinitial).
      destruct H
        as (c_new' & m2' & f' & Hinitial' & Hcode_eq'
            & Hobs_eq & Hincr & Hseparated
            & Hnextblock & Hinverse & Hid & Hunmapped).
      exists (updThread pf1j' (Krun c_new') (getCurPerm m2', (getThreadR pf1j').2)), m2', f'.
      assert (Hinternal':
                internal_step pf1j' Hcomp1'
                              (updThread pf1j' (Krun c_new') (getCurPerm m2', (getThreadR pf1j').2)) m2').
      { right. right. econstructor; eauto. simpl.
        unfold DryHybridMachine.install_perm. reflexivity.
      }
      split; first by assumption.
      split; first by assumption.
      split; first by assumption.
      split.
      erewrite! restrPermMap_nextblock in Hnextblock.
      left; assumption.
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
              assert (H:= restrPermMap_Cur (fst (compat_th _ _ Hcomp2 pf2j)) b1 ofs).
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
          eapply CoreLanguageDry.initial_core_stable_val with (Hlt2 := Hlt); eauto.
          rewrite gssThreadRes; simpl; right;
            by (eapply (fst ((thread_data_lock_coh _ Hinv0) _ pf1j) _ pf1j)).
          (* stability of contents of FineConc *)
          intros.
          simpl.
          eapply CoreLanguageDry.initial_core_stable_val with (Hlt2 := Hlt'); eauto.
          rewrite gssThreadRes; simpl; right;
            by (eapply (fst ((thread_data_lock_coh _ Hinv) _ pf1j') _ pf1j')).
      }
      do 2 erewrite restrPermMap_nextblock in Hid;
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
      (Hvalid_mem: valid_mem m1)
      (Htp_wd: tp_wd f tp1)
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
        Tactics.pf_cleanup.
        assert (Htsim := strong_tsim_step Hinv Hfg Hge_wd Hge_incr Hvalid_mem Hsim Hstep).
        destruct Htsim as
            (tp0' & m0' & f0 & Hstep0' & Hincr0' & Hsep0'
             & Hnextblock0' & Hinverse0' & Htsim0' & Hid0').
        destruct Htsim0' as [pfj' [pfj0' [Hcomp' [Hcomp0' Htsim0]]]].
        Tactics.pf_cleanup.
        assert (Hinv0': invariant tp0')
          by (eapply internal_step_invariant; eauto).
        assert (Hge_incr0': ren_incr fg f0)
          by (eapply ren_incr_trans; eauto).
        assert (H_wd0: valid_mem m0 /\ tp_wd f0 tp0).
        { destruct Hsim.
          pose proof (internal_step_wd Hvalid_mem
                                       ltac:(erewrite restrPermMap_domain;
                                             eapply mem_obs_eq_domain_ren; eauto)
                                              Htp_wd Hge_wd
                                              ltac:(eapply ren_incr_domain_incr; eauto)
                                                     Hstep) as [? [? Htp_wd0]].
          split; [assumption |].
          eapply Htp_wd0;
            eauto.
          destruct Htsim0.
          erewrite restrPermMap_domain;
            eapply mem_obs_eq_domain_ren;
            now eauto.
        }
        destruct H_wd0 as [Hvalid_mem0 Htp_wd0].
        destruct (IHxs _ _ _ _ Hinv0' _ Hge_incr0' _ Hvalid_mem0 _ _ _ Htp_wd0 Htsim0 Htrans)
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
      + destruct (IHxs _ _ _ _ Hinv f Hge_incr _ Hvalid_mem _ _ _ Htp_wd Hsim Hexec)
        as
          [tp2' [m2' [f2' [Hexec2
                             [Hincr2
                                [Hsep2 [Hnextblock2 [Hinverse2 [Hsim2 Hid2]]]]]]]]];
      exists tp2', m2', f2'.
      repeat (split; auto).
  Qed.

  Lemma strong_tsim_stop:
    forall tpc trc tpc' trc' tpf mc mc' mf i fi fg
      (pfc: containsThread tpc i) (pff: containsThread tpf i)
      (Hcompc: mem_compatible tpc mc) (Hcompf: mem_compatible tpf mf)
      (Hfg: forall b1 b2, fg b1 = Some b2 -> b1 = b2)
      (Hge_wd: ge_wd fg the_ge)
      (Hge_incr: ren_incr fg fi)
      (HinvF: invariant tpf)
      (Hstrong_sim: strong_tsim fi pfc pff Hcompc Hcompf)
      (Hmem_wd: valid_mem mc)
      (Hstep: cmachine_step ([:: i], trc, tpc) mc ([::], trc', tpc') mc'),
      let mrestr := restrPermMap ((compat_th _ _ Hcompc pfc).1) in
      forall (Hsuspend: pfc$mrestr @ S),
    exists tpf',
      suspend_thread mf pff tpf' /\
      forall (Hcompc': mem_compatible tpc' mc') (Hcompf' : mem_compatible tpf' mf)
        (pfc': containsThread tpc' i) (pff': containsThread tpf' i),
        strong_tsim fi pfc' pff' Hcompc' Hcompf'.
  Proof.
    intros.
    inversion Hstep; simpl in *; subst; inversion HschedN; subst;
      try (inversion Htstep || inversion Hhalted); subst; Tactics.pf_cleanup;
    unfold getStepType in Hsuspend;
    try rewrite Hcode in Hsuspend; simpl in Hsuspend;
    try match goal with
        | [H: match ?Expr with _ => _ end = _, H2: ?Expr = _ |- _] =>
          rewrite H2 in H
        end; try discriminate;
    try match goal with
        | [H: ~ containsThread _ _, H2: containsThread _ _ |- _] =>
          exfalso; by auto
        | [H: halted _ _ _  |- _] =>
          destruct (at_external_halted_excl c mrestr) as [Hnot_ext | Hcontra];
            [rewrite Hnot_ext in Hsuspend;
             destruct Hsuspend as [[_ ?] | [? _]]; discriminate |
             exfalso; eapply Hcontra; now eauto]
        end.
    destruct Hstrong_sim as [Hcode_eq memObsEq].
    rewrite Hcode in Hcode_eq.
    simpl in Hcode_eq.
    destruct (getThreadC pff) as [c'| | |] eqn:Hcode';
      try by exfalso.
    assert (Hat_external_spec := core_inj_ext _ _ Hfg Hge_wd Hge_incr
                                              ltac:(erewrite <- restrPermMap_mem_valid; eauto)
                                                         Hcode_eq memObsEq).
    inversion Hperm; subst.
    rewrite Hat_external in Hat_external_spec.
    destruct X as [? ?].
    destruct (at_external semSem c' (restrPermMap (compat_th _ _ Hcompf pff)#1))
      as [[? ?]|] eqn:Hat_external';
      try by exfalso.
    destruct Hat_external_spec as [? ?]; subst.
    exists (updThreadC pff (Kblocked c')).
    split.
    eapply SuspendThread with (Hcmpt := Hcompf); now eauto.
    intros.
    constructor;
      first by do 2 rewrite gssThreadCC.
    erewrite restrPermMap_irr' with
    (Hlt := fst (compat_th _ _ Hcompc' pfc')) (Hlt' := fst (compat_th _ _ Hcompc pfc))
      by (erewrite gThreadCR with (cntj := pfc); reflexivity).
    erewrite restrPermMap_irr' with
    (Hlt := fst (compat_th _ _ Hcompf' pff')) (Hlt' := fst (compat_th _ _ Hcompf pff))
      by (erewrite gThreadCR with (cntj := pff); reflexivity);
      by assumption.
    erewrite restrPermMap_irr' with
    (Hlt := snd (compat_th _ _ Hcompc' pfc')) (Hlt' := snd (compat_th _ _ Hcompc pfc))
      by (erewrite gThreadCR with (cntj := pfc); reflexivity).
    erewrite restrPermMap_irr' with
    (Hlt := snd (compat_th _ _ Hcompf' pff')) (Hlt' := snd (compat_th _ _ Hcompf pff))
      by (erewrite gThreadCR with (cntj := pff); reflexivity);
      by assumption.
  Qed.

  Opaque lockRes.
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
      (Hsuspend: suspend_thread m' pfi' tp'')
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
      by (erewrite @gsoThreadR_execution with (pfj' := pfj') by eauto;
          erewrite @StepLemmas.gsoThreadR_suspend with (cntj' := pfj'') by eauto;
          reflexivity).
    constructor.
    - (* cores are related*)
      assert (Hcore := StepLemmas.gsoThreadC_suspend pfj' pfj'' Hij Hsuspend).
      rewrite <- Hcore.
      erewrite <- @gsoThreadC_exec with (pfj := pfj) (pfj' := pfj'); eauto.
      specialize (Htp_wd_id _ pfj).
      eapply ctl_inj_id;
        by eauto.
    - (** [mem_obs_eq] for data *)
      assert (Hlt : permMapLt ((getThreadR pfj'').1) (getMaxPerm m))
        by (rewrite <- Heq; by  (eapply (fst (compat_th _ _ Hcomp pfj)))).
      assert (mem_obs_eq (id_ren m) (restrPermMap (fst (compat_th _ _ Hcomp pfj)))
                         (restrPermMap (fst (compat_th _ _ Hcomp pfj))))
        by (erewrite id_ren_restr with (Hlt := (compat_th _ _ Hcomp pfj).1); apply mem_obs_eq_id; eauto).
      erewrite restrPermMap_irr' with (Hlt' := Hlt) in H at 2 by (rewrite Heq; auto).
      eapply mem_obs_eq_extend; eauto using internal_execution_valid.
      intros.
      eapply @internal_exec_disjoint_val with (Hcomp := Hcomp) (pfj := pfj) (tp' := tp'); eauto using containsThread_internal_execution'.
      left.
      unfold Mem.perm in *.
      erewrite restrPermMap_irr' with (Hlt' := Hlt) by (rewrite Heq; eauto).
      assumption.
    - (** [mem_obs_eq] for locks *)
      assert (Hlt : permMapLt ((getThreadR pfj'').2) (getMaxPerm m))
        by (rewrite <- Heq; by  (eapply (compat_th _ _ Hcomp pfj).2)).
      assert (mem_obs_eq (id_ren m) (restrPermMap (compat_th _ _ Hcomp pfj).2)
                         (restrPermMap (compat_th _ _ Hcomp pfj).2))
        by (erewrite id_ren_restr with (Hlt := (compat_th _ _ Hcomp pfj).2); eapply mem_obs_eq_id; eauto).
      erewrite restrPermMap_irr' with (Hlt' := Hlt) in H at 2 by (rewrite Heq; auto).
      eapply mem_obs_eq_extend; eauto using internal_execution_valid.
      intros.
      eapply @internal_exec_disjoint_val with (Hcomp := Hcomp) (pfj := pfj) (tp' := tp'); eauto using containsThread_internal_execution'.
      right.
      unfold Mem.perm in *.
      erewrite restrPermMap_irr' with (Hlt' := Hlt) by (rewrite Heq; eauto).
      assumption.
  Qed.

  Lemma csafe_pop_step :
    forall (tp : thread_pool) tr (m : mem) i (cnti : containsThread tp i)
      U n
      (Hcomp: mem_compatible tp m),
      let mrestr := restrPermMap ((compat_th _ _ Hcomp cnti).1) in
      forall (Hpop: cnti$mrestr @ E \/ cnti$mrestr @ S)
        (Hsafe: csafe ((i :: U),tr,tp) m (S n)),
      exists (tp' : thread_pool) tr' (m' : mem),
         (cnti$mrestr @ S -> tr' = [::]) /\
        cmachine_step ((i :: U), tr,tp) m (U, tr++tr',tp') m' /\
        forall U'', csafe (U'',tr ++ tr',tp') m' n.
  Proof.
    intros.
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
      Tactics.pf_cleanup.
      rewrite Hcode in Hpop. simpl in Hpop.
      destruct Hpop;
        by discriminate.
      inversion Htstep; subst.
      Tactics.pf_cleanup.
      rewrite Hcode in Hpop; simpl in Hpop.
      destruct Hpop;
        by discriminate.
      inversion Htstep; subst; Tactics.pf_cleanup.
      rewrite Hcode in Hpop. simpl in Hpop.
      apply ev_step_ax1 in Hcorestep.
      apply corestep_not_at_external in Hcorestep.
      rewrite Hcorestep in Hpop.
      destruct Hpop as [?|?];
        discriminate.
    - subst.
      exists tp', tr0, m'; split; eauto.
      intros.
      subst mrestr.
      eapply @suspend_step_inverse with (cnt := cnti) (Hcompc := Hcomp) in Hstep; eauto.
      destruct Hstep as [_ [_ [Heq _]]].
      rewrite <- List.app_nil_r in Heq at 1.
      eapply List.app_inv_head in Heq;
        now auto.
  Qed.

  Lemma sim_suspend : sim_suspend_def.
  Proof.
    unfold sim_suspend_def.
    intros.
    inversion Hsim as
        [HnumThreads HmemCompC HmemCompF HsafeC HsimWeak Hfpsep
                     HsimStrong HsimRes HunmappedRes HinvF HmaxF
                     Hwd_mem Htp_wd Hge_wd [Hge_incr Hfg] Hxs HtraceSim].
    assert (pfc: containsThread tpc i)
      by (eapply HnumThreads; eauto).
    destruct (HsimStrong i pfc pff)
      as (tpc' & mc' & Hincr & Hsynced & Hexec & Htsim & Hownedi & Hownedi_lp & Hunmappedi);
      clear HsimStrong.
    (** The coarse machine is also at suspend*)
    assert (pfc': containsThread tpc' i)
      by (clear - Hexec pfc; eapply containsThread_internal_execution in pfc;
          eauto).
    assert (memCompC' := internal_execution_compatible HmemCompC Hexec).
    specialize (Htsim pfc' memCompC').
    assert (HmemCompF = mem_compf Hsim)
      by (eapply proof_irr); subst.
    assert (Hincr_ge': ren_incr fg (fp i pfc))
      by (eapply ren_incr_trans; eauto; now destruct Hge_spec).
    assert (Hstop_pfc': pfc'$(restrPermMap (compat_th _ _ memCompC' pfc').1)@ S)
      by (erewrite (stepType_inj pff pfc' _ Hfg Hincr_ge' Hge_wd _ 
                           (obs_eq_data Htsim) (code_eq Htsim)); eauto).
    (** It's safe to step the coarse grained machine for one more step on i*)
    specialize (HsafeC ([:: i]) trc).
    assert (HcoreN := safety_det_corestepN_internal xs HsafeC Hexec).
    destruct HcoreN as [trc' [HcorestepN Hsafety]].
    destruct (csafe_pop_step pfc' _ ltac:(eauto) Hsafety) as
        (tpc'' & trc'' & mc'' & Htrc'' & Hstep' & Hsafe').
    specialize (Htrc'' Hstop_pfc'); subst.
    assert (HinvC: invariant tpc)
      by (eapply cmachine_step_invariant; eauto).
    (** A suspend step pops the schedule and does not touch the memory *)
    assert (Heq : mc' = mc'' /\ trc ++ trc' = (trc ++ trc') ++ [::] /\ mem_compatible tpc' mc' /\
                  suspend_thread mc' pfc' tpc'')
      by (eapply suspend_step_inverse; eauto).
    destruct Heq as [? [Heq_tr [Hcomp' HsuspendC]]]; subst mc'.
    rewrite <- List.app_nil_r  in Heq_tr at 1.
    eapply List.app_inv_head in Heq_tr; subst.
    assert (memCompC'': mem_compatible tpc'' mc'')
      by (eapply StepLemmas.suspend_compatible; eauto).
    assert (Hwd_mem'': valid_mem mc'').
    { destruct (HsimWeak _ pfc pff).
      eapply internal_execution_wd; eauto.
      erewrite restrPermMap_domain.
      eapply weak_obs_eq_domain_ren;
        eauto.
      eapply ren_incr_domain_incr;
        now assumption.
    }
    assert (HstepF := strong_tsim_stop Hfg Hge_wd Hincr_ge' HinvF Htsim Hwd_mem'' Hstep' Hstop_pfc').
    destruct HstepF as [tpf' [HstepF Htsim']].
    assert (memCompF': mem_compatible tpf' mf).
      by (destruct Hsim; eapply StepLemmas.suspend_compatible; eauto).
    exists tpc'', [::], mc'', tpf', mf.
    (** since thread i commits, the new global renaming will be fi *)
    exists (fp i pfc).
    assert (pfci': containsThread tpc' i)
      by (eapply containsThread_internal_execution; eauto).
    assert (pfci'': containsThread tpc'' i)
      by (eapply StepLemmas.suspend_containsThread with (tp := tpc'); eauto).
    (** and we need to shift all other mappings..*)
    exists (fun j (cntj'': containsThread tpc'' j) =>
         let cntj := (containsThread_internal_execution'
                        Hexec ((snd (StepLemmas.suspend_containsThread j HsuspendC)) cntj'')) in
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
                 (fp j cntj) (Z.to_pos bz)), trf.
    split.
    { (** the fine-grained machine takes a suspend step *)
      intros U; eapply suspend_step; simpl; eauto.
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
        by (eapply StepLemmas.suspend_containsThread with (cnti := pff); eauto).
      specialize (Htsim' memCompC'' memCompF' pfci'' pffi').
      assert (Hdomain_fi: domain_memren (fp i pfc) mc'')
        by (eapply (mem_obs_eq_domain_ren (obs_eq_data Htsim')); eauto).
      specialize (Htp_wd' _ Hdomain_fi).
      eapply @Build_sim with (mem_compc := memCompC'') (mem_compf := memCompF').
      { (** number of threads *)
        clear - HnumThreads Hexec HsuspendC HstepF.
        intros j. assert (Hpffj := StepLemmas.suspend_containsThread j HstepF).
        assert (Hpfcj' := StepLemmas.suspend_containsThread j HsuspendC).
        split; intros;
        [apply Hpffj; apply HnumThreads;
         destruct Hpfcj'; eapply containsThread_internal_execution'; eauto
        |  apply Hpfcj';
          destruct Hpffj;
          eapply containsThread_internal_execution; eauto;
          destruct (HnumThreads j); by auto].
      }
      { (** safety of coarse state *)
        intros.
        rewrite cats0 in Hsafe'.
        specialize (Hsafe' sched).
        eapply HybridCoarseMachine.csafe_trace with (tr' := tr) in Hsafe'.
        assumption.
      }
      { (** Proof of weak simulation between the threadpools and memories *)
        clear HsafeC. Tactics.pf_cleanup.
        intros j pfcj'' pffj'.
        pose proof (weak_obs_eq (obs_eq_data Htsim)) as Hweak_obs_eq_data.
        (** We will proof the two complicated weak_mem_obs_eq (for locks and data) goals at the same time*)
        assert (Hperm_weak: forall (b1 b2 : block) (ofs : Z),
                   fp i pfc b1 = Some b2 ->
                   Mem.perm_order'' (permission_at (restrPermMap (fst (compat_th _ _ memCompC'' pfcj''))) b1 ofs Cur)
                                    (permission_at (restrPermMap (fst (compat_th _ _ memCompF' pffj'))) b2 ofs Cur) /\
                   Mem.perm_order'' (permission_at (restrPermMap (snd (compat_th _ _ memCompC'' pfcj''))) b1 ofs Cur)
                                    (permission_at (restrPermMap (snd (compat_th _ _ memCompF' pffj'))) b2 ofs Cur)).
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
            by (eapply StepLemmas.suspend_containsThread; eauto).
          assert (Hperm_eqF: permission_at (restrPermMap (compat_th _ _ memCompF' pffj').1)
                                           b2 ofs Cur =
                             permission_at (restrPermMap (compat_th _ _ (mem_compf Hsim) pffj).1)
                                           b2 ofs Cur)
            by (do 2 rewrite restrPermMap_Cur;
                erewrite <- StepLemmas.gsoThreadR_suspend with (cntj := pffj); eauto).
          assert (Hperm_eqF_locks: permission_at (restrPermMap (compat_th _ _ memCompF' pffj').2)
                                           b2 ofs Cur =
                             permission_at (restrPermMap (compat_th _ _ (mem_compf Hsim) pffj).2)
                                           b2 ofs Cur)
            by (do 2 rewrite restrPermMap_Cur;
                erewrite <- StepLemmas.gsoThreadR_suspend with (cntj := pffj); eauto).
          rewrite Hperm_eqF Hperm_eqF_locks.
          (** Likewise for the DryConc machine*)
          assert (pfcj': containsThread tpc' j)
            by (eapply StepLemmas.suspend_containsThread; eauto).
          assert (Hperm_eqC: permission_at (restrPermMap (compat_th _ _ memCompC'' pfcj'').1)
                                           b1 ofs Cur =
                             permission_at (restrPermMap (compat_th _ _ memCompC' pfcj').1)
                                           b1 ofs Cur)
            by (do 2 rewrite restrPermMap_Cur;
                erewrite <- StepLemmas.gsoThreadR_suspend with (cntj := pfcj'); eauto).
          assert (Hperm_eqC_locks: permission_at (restrPermMap (compat_th _ _ memCompC'' pfcj'').2)
                                           b1 ofs Cur =
                             permission_at (restrPermMap (compat_th _ _ memCompC' pfcj').2)
                                           b1 ofs Cur)
            by (do 2 rewrite restrPermMap_Cur;
                erewrite <- StepLemmas.gsoThreadR_suspend with (cntj := pfcj'); eauto).
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
              by Tactics.pf_cleanup.
          }
          { (** Case j <> i *)
            assert (pfcj: containsThread tpc j)
              by (eapply containsThread_internal_execution'; eauto).
            destruct (HsimWeak _ pfcj pffj) as [Hweak_data Hweak_locks].
            destruct Hweak_data as [Hinvdomain Hdomain Hcodomain Hinjective Hobs_weak_data].
            destruct Hweak_locks as [_ _ _ _ Hobs_weak_locks].
            destruct (valid_block_dec mc b1) as [Hvalid_mc | Hinvalid_mc].
            - (** b1 is a block that's valid in mc, i.e. not allocated by i *)
              assert (Hvalid: Mem.valid_block (restrPermMap (compat_th _ _ HmemCompC pfcj).1) b1)
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
          split; first by (intros; Tactics.pf_cleanup; auto).
          split; first by congruence.
          split; first by congruence.
          intros b2 Hfi ofs.
          erewrite <- StepLemmas.gsoThreadR_suspend with (cntj := pff);
            by eauto.
        }
        { (** case j <> i *)
          assert (pfc'j: containsThread tpc' j)
            by (eapply StepLemmas.suspend_containsThread with (cnti := pfc'); eauto).
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
                        Hexec (snd (StepLemmas.suspend_containsThread
                                        j HsuspendC) pfcj'') = pfcj) by
              (erewrite proof_irr
               with (a1 := (containsThread_internal_execution'
                              Hexec (snd (StepLemmas.suspend_containsThread j HsuspendC)
                                           pfcj'')))
                      (a2 := pfcj); auto).
          rewrite H; clear H.
          (** The original <tpc, mc> strongly injects into <tpc'',mc''> where
               <tpc, mc> -->i+ <tpc', mc'> -->iS <tpc'',mc'>  with the id map*)
          assert (Hsim_c_ci: strong_tsim (id_ren mc)
                                         pfcj pfcj'' HmemCompC memCompC'')
            by (eapply strong_tsim_id with (f := id_ren mc) (pfi' := pfc'); eauto).
          assert (pffj: containsThread tpf j)
            by (eapply StepLemmas.suspend_containsThread; eauto).
          assert (Htsimj := (simStrong Hsim) j pfcj pffj).
          (** executing the internal steps for thread j gives us a strong
              simulation between the coarse and fine-grained states. *)
          destruct Htsimj as
              (tpcj & mcj & Hincrj & Hsyncedj & Hexecj & Htsimj
               & Hownedj & Hownedj_lp & Hunmappedj).
          (** by the strong simulation on mc and mc'' (via id) we can
              obtain a strong simulation between mcj and mcj', where
              mcj' mc -->i --> mci -->j mcj' *)
          assert (Hinv'': invariant tpc'')
            by (eapply StepLemmas.suspend_invariant with (tp := tpc');
                 [eapply internal_execution_invariant with (tp := tpc);
                   eauto | eauto]).
          assert (Hge_incr_id: ren_incr fg (id_ren mc))
            by (clear - Hge_incr Hfg Hdomain_f;
                 eapply incr_domain_id; eauto).
          assert (Hsimjj':= strong_tsim_execution xs Hinv'' Hfg Hge_wd
                                                  Hge_incr_id Hwd_mem Htp_wd_id Hsim_c_ci Hexecj).
          destruct Hsimjj'
            as (tpcj' & mcj' & fij & Hexecij
                & Hincr' & Hsep  & Hnextblockj' & Hinverse & Hsimjj').
          destruct Hsimjj' as [[pfcjj [pfij [Hcompjj [Hcompij Hsimij]]]] Hid_case].
          Tactics.pf_cleanup.
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
            Tactics.pf_cleanup.
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
                                       (compat_th _ _ HmemCompC pfc).1 b1)) Hvalidmc)).
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
                                    (restrPermMap (compat_th _ _ memCompC'' pfci'').1) b1)
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
                        ~ Mem.valid_block (restrPermMap (compat_th _ _ memCompC' pfc').1) b)
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
            intros pfcj' Hcompcj'. Tactics.pf_cleanup.
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
                         permission_at (restrPermMap (compat_th _ _ Hcompij pfij).1)
                                       b1 ofs Cur =
                         permission_at (restrPermMap (compat_th _ _ Hcompjj pfcjj).1)
                                       b1 ofs Cur /\
                         permission_at (restrPermMap (compat_th _ _ Hcompij pfij).2)
                                       b1 ofs Cur =
                         permission_at (restrPermMap (compat_th _ _ Hcompjj pfcjj).2)
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
                          permission_at (restrPermMap (compat_th _ _  memCompC'' pfcj'').1)
                                        b1 ofs Cur = None /\
                          permission_at (restrPermMap (compat_th _ _ memCompC'' pfcj'').2)
                                        b1 ofs Cur = None).
              { intros b1 ofs Hinvalidmc Hvalidmc''.
                (** Proof that the permission at b1 in mc|j is empty *)
                assert (Hinitp:
                          permission_at (restrPermMap (compat_th _ _ HmemCompC pfcj).1) b1 ofs Cur = None /\
                          permission_at (restrPermMap (compat_th _ _ HmemCompC pfcj).2) b1 ofs Cur = None).
                { apply Mem.nextblock_noaccess with (k := Max) (ofs := ofs)
                    in Hinvalidmc.
                  assert (Hlt := (compat_th _ _ HmemCompC pfcj).1 b1 ofs).
                  assert (Hlt_lock := (compat_th _ _ HmemCompC pfcj).2 b1 ofs).
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
                assert (Hp': permission_at (restrPermMap (compat_th _ _ memCompC' pfcj').1) b1 ofs Cur = None /\
                             permission_at (restrPermMap (compat_th _ _ memCompC' pfcj').2) b1 ofs Cur = None).
                { rewrite! restrPermMap_Cur.
                  erewrite <- gsoThreadR_execution with (pfj := pfcj); eauto.
                  rewrite! restrPermMap_Cur in Hinitp. by assumption.
                }
                rewrite! restrPermMap_Cur.
                erewrite <- StepLemmas.gsoThreadR_suspend with (cntj:= pfcj'); eauto.
                rewrite! restrPermMap_Cur in Hp'.
                  by assumption.
              }

              (** The permission of j at an i-block in mcij/mcj' is empty*)
              assert (Hpermj_mcj': forall b1 ofs,
                         ~ Mem.valid_block mc b1 ->
                         Mem.valid_block mc'' b1 ->
                         permission_at (restrPermMap (compat_th _ _ Hcompij pfij).1) b1 ofs Cur = None /\
                         permission_at (restrPermMap (compat_th _ _ Hcompij pfij).2) b1 ofs Cur = None).
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
                assert (Hdecay := @InternalSteps.internal_execution_decay _ _).
                specialize (Hdecay _ _ _ _ _ _ pfcj'' pfij memCompC''
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
                assert (Hperm_at := restrPermMap_Cur (compat_th _ _ Hcompij pfij).1 b1 ofs).
                unfold permission_at in Hperm_at. rewrite Hperm_at in Heq.
                rewrite <- Heq.
                (** proof of equality for lock permissions*)
                pose proof (internal_execution_locks_eq Hexecij pfcj'' pfij) as Heq_locks.
                rewrite <- Heq_locks.
                assert (Hperm_at_locks := restrPermMap_Cur (compat_th _ _ memCompC'' pfcj'').2 b1 ofs).
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
                         permission_at (restrPermMap (compat_th _ _ memCompF' pffj').1) b2 ofs Cur = None /\
                         permission_at (restrPermMap (compat_th _ _ memCompF' pffj').2) b2 ofs Cur = None).
              { (** Proof is straightforward by the blocks owned by i invariant*)
                intros b1 b2 ofs Hinvalidmc Hvalidmc'' Hfi.
                rewrite! restrPermMap_Cur.
                erewrite <- StepLemmas.gsoThreadR_suspend with (cntj := pffj) by eauto.
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
                         permission_at (restrPermMap (compat_th _ _ Hcompjj pfcjj).1)
                                       b1' ofs Cur =
                         permission_at (restrPermMap (compat_th _ _ Hcompij pfij).1)
                                       b1 ofs Cur /\
                         permission_at (restrPermMap (compat_th _ _ Hcompjj pfcjj).2)
                                       b1' ofs Cur =
                         permission_at (restrPermMap (compat_th _ _ Hcompij pfij).2)
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
                          Mem.perm_order'' (permission_at (restrPermMap (fst (compat_th _ _ Hcompij pfij))) b1 ofs Cur)
                                           (permission_at (restrPermMap (fst (compat_th _ _ memCompF' pffj'))) b2 ofs Cur) /\
                          Mem.perm_order'' (permission_at (restrPermMap (snd (compat_th _ _ Hcompij pfij))) b1 ofs Cur)
                                           (permission_at (restrPermMap (snd (compat_th _ _ memCompF' pffj'))) b2 ofs Cur)).
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
                  erewrite <- StepLemmas.gsoThreadR_suspend
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
                  replace (permission_at (restrPermMap (fst (compat_th _ _ memCompF' pffj'))) b2 ofs Cur)
                  with ((getThreadR pffj').1 # b2 ofs)
                    by (rewrite restrPermMap_Cur; reflexivity).
                  replace (permission_at (restrPermMap (snd (compat_th _ _ memCompF' pffj'))) b2 ofs Cur)
                  with ((getThreadR pffj').2 # b2 ofs)
                    by (rewrite restrPermMap_Cur; reflexivity).
                  erewrite <- StepLemmas.gsoThreadR_suspend with (cntj := pffj) (cntj' := pffj'); eauto.
                  replace ((getThreadR pffj).1 # b2 ofs) with
                  (permission_at (restrPermMap (fst (compat_th _ _ (mem_compf Hsim) pffj))) b2 ofs Cur)
                    by (rewrite restrPermMap_Cur; reflexivity).
                  replace ((getThreadR pffj).2 # b2 ofs) with
                  (permission_at (restrPermMap (snd (compat_th _ _ (mem_compf Hsim) pffj))) b2 ofs Cur)
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
                         permission_at (restrPermMap (compat_th _ _  memCompF' pffj').1) b2 ofs Cur =
                         permission_at (restrPermMap (compat_th _ _ Hcompij pfij).1) b1 ofs Cur /\
                         permission_at (restrPermMap (compat_th _ _ memCompF'  pffj').2) b2 ofs Cur =
                         permission_at (restrPermMap (compat_th _ _ Hcompij pfij).2) b1 ofs Cur).
              { intros b1 b2 ofs Hf'.
                (** the permissions of mf' and mf are the same,
                     suspend step does not touch the memory*)
                rewrite! restrPermMap_Cur.
                erewrite <- StepLemmas.gsoThreadR_suspend
                with (cntj := pffj) (cntj' := pffj'); eauto.
                rewrite <- restrPermMap_Cur with (Hlt := (compat_th _ _ (mem_compf Hsim) pffj).1).
                rewrite <- restrPermMap_Cur with (Hlt := (compat_th _ _ (mem_compf Hsim) pffj).2).
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
                    rewrite <- restrPermMap_Cur with (Hlt := (compat_th _ _ Hcompij pfij).1).
                    rewrite <- restrPermMap_Cur with (Hlt := (compat_th _ _ Hcompij pfij).2).
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
                         (Mem.perm (restrPermMap (fst (compat_th _ _ Hcompij pfij))) b1 ofs Cur Readable \/
                          Mem.perm (restrPermMap (snd (compat_th _ _ Hcompij pfij))) b1 ofs Cur Readable) ->
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
                  + rewrite <- Hundef_mcj in Hvalmcj_mf_b1.
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
                  { assert (Hreadable': Mem.perm (restrPermMap (compat_th _ _ Hcompjj pfcjj).1)
                                                 ((Z.to_pos
                                                     match
                                                       (- Z.pos_sub (Mem.nextblock mc'')
                                                                    (Mem.nextblock mc))%Z
                                                     with
                                                     | 0%Z => Z.pos b1
                                                     | Z.pos y' => Z.pos (b1 + y')
                                                     | Z.neg y' => Z.pos_sub b1 y'
                                                     end)) ofs Cur Readable \/
                                        Mem.perm (restrPermMap (compat_th _ _ Hcompjj pfcjj).2)
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
                  + rewrite <- Hundef_mcj in Hvalmcj_mf.
                    inversion Hvalmcj_mf.
                      by constructor.
                }
                constructor.
            - (** code injection between thread j on tpj' and tpf'*)
              assert (Hctlij := code_eq Hsimij).
              assert (Hctljj := code_eq Htsimj).
              erewrite <- StepLemmas.gsoThreadC_suspend with (cntj := pffj) (cntj' := pffj');
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
            - do 2 constructor; intros; eauto.
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
                by (eapply StepLemmas.suspend_containsThread with (cnti := pff); eauto).
              specialize (Hownedj _ pffk Hjk _ _ ofs Hf' Hinvalidb0).
              erewrite <- StepLemmas.gsoThreadR_suspend with (cntj := pffk);
                by eauto.
          }
          split.
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
              erewrite <- StepLemmas.suspend_lockPool with (tp := tpf) in Hres;
                eauto.
          }
          { intros b2 Hf ofs.
            erewrite <- StepLemmas.gsoThreadR_suspend with (cntj := pffj); eauto.
            assert  (Hmappedi: (exists b1, fp j pfcj b1 = Some b2) \/ ~exists b1, fp j pfcj b1 = Some b2) by (eapply em; eauto).
            (** We proceed by case analysis on whether b2 is mapped by a block in the domain of fj*)
            destruct Hmappedi as [Hfj | Hfj].
            - destruct Hfj as [b1 Hfj].
              (** if it is mapped we can derive a contradiction by hypothesis Hf*)
              exfalso.
              apply Hf.
              destruct (valid_block_dec mc b1).
              + (** if [b1] is in mc then [f] ought to map it to [b2]*)
                exists b1.
                erewrite if_true by (by apply/Coqlib.proj_sumbool_is_true).
                apply (domain_valid (weak_tsim_data HsimWeak)) in v.
                destruct v as [b2' Hf0].
                assert (b2 = b2') by (apply Hincrj in Hf0; rewrite Hf0 in Hfj; inversion Hfj; by subst).
                subst; auto.
              + (** if [b1] is not in [mc] we proceed by case analysis on Hle*)
                apply Pos.le_lteq in Hle.
                destruct Hle as [Hlt | Heq].
                * rewrite Z.pos_sub_opp.
                  erewrite Z.pos_sub_lt by eauto.
                  (** we pick [b1] plus the difference between [mc''] and [mc]*)
                  exists (b1 + (Mem.nextblock mc'' - Mem.nextblock mc))%positive.
                  erewrite if_false
                    by (apply negbT;
                        eapply proj_sumbool_is_false;
                        intros Hcontra;
                        clear - Hcontra Hlt n;
                        unfold Mem.valid_block, Coqlib.Plt in *; zify; omega).
                  erewrite if_false
                    by (apply negbT;
                        eapply proj_sumbool_is_false;
                        intros Hcontra;
                        clear - Hcontra Hlt n;
                        unfold Mem.valid_block, Coqlib.Plt in *;
                        zify;
                        destruct H2 as [[? ?] | [? ?]];
                        subst;
                        omega).
                  erewrite Z.pos_sub_gt by (zify; omega).
                  rewrite Pos.add_sub.
                  simpl.
                  assumption.
                * rewrite Heq.
                  rewrite Z.pos_sub_diag. simpl.
                  exists b1.
                  erewrite! if_false by
                      (apply negbT; apply proj_sumbool_is_false;
                       unfold Mem.valid_block in *;
                       auto; try (rewrite <- Heq; auto)).
                  assumption.
            - (** if it is not mapped we can use hypothesis [Hunmappedj]*)
              apply Hunmappedj; auto.
            }
        }
      }
      { (** Proof of strong simulation of resources *)
        clear - HstepF Hexec HsuspendC HsimRes Hincr Htsim
                       HsimWeak Hownedi_lp semAxioms.
        destruct HsimRes as [HsimRes [Hlock_mapped Hlock_if]].
        split.
        - intros bl1 bl2 ofs rmap1 rmap2 Hfl Hl1'' Hl2'.
          (** The [lockRes] of the DryConc machine remained unchanged*)
          assert (Hl1: lockRes tpc (bl1,ofs) = Some rmap1)
            by (erewrite <- @StepLemmas.suspend_lockPool with (pfc := pfc') in Hl1''; eauto;
                erewrite <- gsoLockPool_execution in Hl1''; eauto).

          (** The [lockRes] of the FineConc machine remained unchanged*)
          assert (Hl2: lockRes tpf (bl2,ofs) = Some rmap2)
            by (erewrite <- @StepLemmas.suspend_lockPool with (pfc := pff) in Hl2'; eauto).

          assert (pff': containsThread tpf' i)
            by (eapply StepLemmas.suspend_containsThread with (cnti := pff); eauto).

          assert (Hperm_eq: forall b ofs,
                     permission_at (restrPermMap (compat_lp _ _ memCompC'' _ _ Hl1'').1) b ofs Cur =
                     permission_at (restrPermMap (compat_lp _ _ HmemCompC _ _ Hl1).1) b ofs Cur /\
                     permission_at (restrPermMap (compat_lp _ _ memCompC'' _ _ Hl1'').2) b ofs Cur =
                     permission_at (restrPermMap (compat_lp _ _ HmemCompC _ _ Hl1).2) b ofs Cur)
            by (intros; split; by rewrite! restrPermMap_Cur).


          assert (Hvalid: Mem.valid_block mc (bl1, ofs).1)
            by (eapply (lockRes_blocks _ _ HmemCompC); eauto).
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
                      permission_at (restrPermMap (compat_lp _ _ memCompF' (bl2', ofs) _ Hl2')#1) b2 ofs0 Cur =
                      permission_at (restrPermMap (compat_lp _ _ memCompC'' (bl1, ofs) _ Hl1'')#1) b1 ofs0 Cur /\
                      permission_at (restrPermMap (compat_lp _ _ memCompF' (bl2', ofs) _ Hl2')#2) b2 ofs0 Cur =
                      permission_at (restrPermMap (compat_lp _ _ memCompC'' (bl1, ofs) _ Hl1'')#2) b1 ofs0 Cur).
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
              assert (Hlt1:= ((compat_lp _ _ HmemCompC _ _ Hl1).1 b1 ofs0)).
              assert (Hlt2:= ((compat_lp _ _ HmemCompC _ _ Hl1).2 b1 ofs0)).
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
                      (Mem.perm (restrPermMap (proj1 (compat_lp _ _ memCompC'' (bl1, ofs) _ Hl1''))) b1 ofs0 Cur Readable \/
                      Mem.perm (restrPermMap (proj2 (compat_lp _ _ memCompC'' (bl1, ofs) _ Hl1''))) b1 ofs0 Cur Readable) ->
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
              assert (Hlt1:= (compat_lp _ _ HmemCompC _ _ Hl1).1 b1 ofs0).
              assert (Hlt2:= (compat_lp _ _ HmemCompC _ _ Hl1).2 b1 ofs0).
              rewrite getMaxPerm_correct in Hlt1 Hlt2. unfold permission_at in Hlt1, Hlt2.
              rewrite Hempty in Hlt1 Hlt2. simpl in Hlt1, Hlt2.
              apply (domain_invalid (weak_tsim_data HsimWeak)) in Hinvalidmc.
              assert (Hcontra1:= restrPermMap_Cur (compat_lp _ _ HmemCompC _ _ Hl1).1 b1 ofs0).
              assert (Hcontra2:= restrPermMap_Cur (compat_lp _ _ HmemCompC _ _ Hl1).2 b1 ofs0).
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
        - split.
          + (** lockRes on the FineConc machine are always mapped*)
            intros bl2 ofs Hres.
            erewrite <- StepLemmas.suspend_lockRes with (tp := tpf) in Hres by eauto.
            specialize (Hlock_mapped _ _ Hres).
            destruct Hlock_mapped as [bl1 Hf].
            eapply Hincr in Hf.
            eexists; eauto.
          + (** the two machines have the same [lockRes]*)
            intros bl1 bl2 ofs Hf.
            erewrite <- StepLemmas.suspend_lockRes with (tp' := tpf') (tp := tpf) by eauto.
            erewrite <- StepLemmas.suspend_lockPool with (tp := tpc') (tp' := tpc'') by eauto.
            erewrite <- gsoLockPool_execution; eauto.
            specialize (HsimWeak _ pfc pff).
            split; intros Hres.
            eapply Hlock_if; eauto.
            destruct (lockRes tpc (bl1, ofs)) eqn:Hres'; try by exfalso.
            apply (lockRes_blocks _ _ HmemCompC) in Hres'.
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
      { (** Proof of unmapped blocks on lock resources*)
        intros  bl ofsl rmap Hres b2 Hf ofs.
        erewrite <- StepLemmas.suspend_lockRes with (tp := tpf) in Hres by eauto.
        eapply HunmappedRes;
          eauto.
        intros (b1 & Hcontra).
        apply Hincr in Hcontra.
        eapply Hf; by eauto.
      }
      { (* Proof that the fine grained invariant is preserved *)
          by eapply @StepLemmas.suspend_invariant with (pff := pff); eauto.
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
        eapply StepLemmas.suspend_containsThread with (tp := tpc'); eauto.
        eapply containsThread_internal_execution;
          by eauto.
      }
      { rewrite cats0.
        assert (ren_incr f (fp i pfc)).
        auto.
        assert (Hinjective:
                  forall b1 b1' b2,
                    (fp i pfc) b1 = Some b2 ->
                    (fp i pfc) b1' = Some b2 ->
                    b1 = b1')
          by (destruct Htsim';
              destruct obs_eq_data0;
              destruct weak_obs_eq0;
              eauto).
        eapply trace_sim_incr;
          eauto.
      } 
    }
    Unshelve. all: eauto.
    erewrite <- restrPermMap_mem_valid.
    eapply internal_execution_wd; eauto.
    destruct (HsimWeak _ pfc pff).
    erewrite restrPermMap_domain.
    eapply weak_obs_eq_domain_ren;
      eauto.
    eapply ren_incr_domain_incr;
      now eauto.
  Qed.

  (** ** Proofs about external steps*)

  Lemma external_step_inverse :
    forall U U' tp tr m tp' tr' m' i (cnti: containsThread tp i)
      (Hcomp: mem_compatible tp m),
      let mrestr := restrPermMap (((compat_th _ _ Hcomp) cnti).1) in
      forall (Hexternal: cnti$mrestr @ E)
        (Hstep: MachStep (i :: U, tr, tp) m (U', tr ++ tr', tp') m'),
        U = U' /\ exists ev, syncStep true cnti Hcomp tp' m' ev /\ tr' = [:: external i ev].
  Proof.
    intros.
    inversion Hstep;
      try inversion Htstep; subst; simpl in *;
        unfold mrestr in *;
        try match goal with
            | [H: Some _ = Some _ |- _] => inversion H; subst
            end; Tactics.pf_cleanup;
          repeat match goal with
                 | [H: getThreadC ?Pf = _, Hext: ?Pf$_ @ E |- _] =>
                   unfold getStepType in Hext;
                     rewrite H in Hext; simpl in Hext
                 | [H: DryHybridMachine.install_perm _ _ _ _ _ _ |- _] =>
                   inversion H; subst
                 | [H: ev_step _ _ _ _ _ _ |- _] =>
                   eapply ev_step_ax1 in H;
                     eapply corestep_not_at_external in Hcorestep;
                     rewrite Hcorestep in Hexternal;
                     destruct Hexternal as [[_ ?]|[? _]]; try discriminate
                 | [H: _ ++ _ = _ ++ _ |- _] =>
                   apply List.app_inv_head in H; subst
                 end; try rewrite Hat_external in Hexternal; try discriminate;
            try (now exfalso; eauto);
            try (now (split; eexists; split; eauto)).
    destruct (at_external semSem c (restrPermMap (proj1 (compat_th _ _ Hcomp cnti))));
      [discriminate|].
    discriminate.
  Qed.
    

  (** Performing a store on some disjoint (coherent) part of the memory, retains
  a [mem_obs_eq] for data and [ctl_inj], using the id injection, for threads*)
  Lemma strong_tsim_store_id:
    forall tp tp' m m' i b ofs v pmap
      (pfi: containsThread tp i)
      (pfi': containsThread tp' i)
      (Hresi: getThreadR pfi' = getThreadR pfi)
      (Hcodei: getThreadC pfi' = getThreadC pfi)
      (Hcomp: mem_compatible tp m)
      (Hcomp': mem_compatible tp' m')
      (Hlt: permMapLt pmap (getMaxPerm m))
      (Hno_race: permMapCoherence (getThreadR pfi).1 pmap \/
                 permMapsDisjoint (getThreadR pfi).1 pmap)
      (Hmem_wd: valid_mem m)
      (Htp_wd: tp_wd (id_ren m) tp)
      (Hstore: Mem.store Mint32 (restrPermMap Hlt) b ofs v = Some m'),
      (ctl_inj (id_ren m) (getThreadC pfi) (getThreadC pfi')) /\
      (mem_obs_eq (id_ren m) (restrPermMap (compat_th _ _ Hcomp pfi).1)
                  (restrPermMap ((compat_th _ _ Hcomp' pfi').1))) /\
      (Mem.nextblock m = Mem.nextblock m').
  Proof.
    intros.
    split.
    { (** ctl_inj between threads *)
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
    split.
    { (** mem_obs_eq for data *)
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
      simpl.
      destruct (Pos.eq_dec b b2).
      - subst.
        destruct (Intv.In_dec ofs0 (ofs, ofs + size_chunk Mint32)%Z).
        + exfalso.
          apply Mem.store_valid_access_3 in Hstore.
          destruct Hstore as [Hstore _].
          pose proof (restrPermMap_Cur (compat_th _ _ Hcomp pfi).1 b2 ofs0) as Heq_perm.
          unfold permission_at in Heq_perm.
          pose proof (restrPermMap_Cur Hlt b2 ofs0) as Heq_perm_lock.
          specialize (Hstore ofs0 i0).
          unfold permission_at, Mem.perm in *.
          rewrite Heq_perm in Hperm.
          rewrite Heq_perm_lock in Hstore.
          destruct Hno_race as [Hno_race | Hno_race];
          specialize (Hno_race b2 ofs0).
          * destruct ((getThreadR pfi).1 # b2 ofs0) as [p|]; simpl in Hperm; auto;
              inversion Hperm; subst;
                simpl in Hno_race; destruct (pmap # b2 ofs0); auto.
          * eapply perm_order_clash; now eauto.
        + eapply Mem.store_mem_contents in Hstore.
          rewrite Hstore. simpl.
          rewrite Maps.PMap.gss.
          erewrite Mem.setN_outside.
          eapply memval_obs_eq_id; eauto using id_ren_correct.
          specialize (Hmem_wd b2 Hvalid ofs0 _ (Logic.eq_refl _)).
          destruct (Maps.ZMap.get ofs0 (Mem.mem_contents m) # b2);
            auto.
          unfold mem_wd.val_valid in Hmem_wd.
          unfold valid_memval, valid_val.
          destruct v0; eauto.
          exists b.
          apply id_ren_validblock; auto.
          eapply Intv.range_notin in n.
          rewrite encode_val_length. eauto.
          simpl. omega.
      - eapply Mem.store_mem_contents in Hstore.
        rewrite Hstore. simpl.
        erewrite Maps.PMap.gso by eauto.
        eapply memval_obs_eq_id; eauto using id_ren_correct.
          specialize (Hmem_wd b2 Hvalid ofs0 _ (Logic.eq_refl _)).
          destruct (Maps.ZMap.get ofs0 (Mem.mem_contents m) # b2);
            auto.
          unfold mem_wd.val_valid in Hmem_wd.
          unfold valid_memval, valid_val.
          destruct v0; eauto.
          exists b0.
          apply id_ren_validblock; auto.
    }
    { erewrite Mem.nextblock_store with
      (m1 := (restrPermMap Hlt)) (m2 := m');
        by eauto.
    }
  Qed.

  Lemma strong_tsim_id_trans:
    forall (tp1 tp1' tp2 : thread_pool) (m1 m1' m2 : mem)
      (f : memren) i
      (pf1 : containsThread tp1 i)
      (pf1' : containsThread tp1' i)
      (pf2 : containsThread tp2 i)
      (Hcomp1 : mem_compatible tp1 m1)
      (Hcomp1' : mem_compatible tp1' m1')
      (Hcomp2 : mem_compatible tp2 m2)
      (Hvalid: forall b, Mem.valid_block m1 b <-> Mem.valid_block m1' b)
      (Hctl_id: ctl_inj (id_ren m1) (getThreadC pf1) (getThreadC pf1'))
      (Hobs_eq_id: mem_obs_eq (id_ren m1) (restrPermMap (compat_th _ _ Hcomp1 pf1).1)
                              (restrPermMap (compat_th _ _ Hcomp1' pf1').1))
      (Hctl_eq: ctl_inj f (getThreadC pf1) (getThreadC pf2))
      (Hmem_obs_eq: mem_obs_eq f (restrPermMap (compat_th _ _ Hcomp1 pf1).1)
                               (restrPermMap (compat_th _ _ Hcomp2 pf2).1)),
      ctl_inj f (getThreadC pf1') (getThreadC pf2) /\
      mem_obs_eq f (restrPermMap (compat_th _ _ Hcomp1' pf1').1) (restrPermMap (compat_th _ _ Hcomp2 pf2).1).
  Proof.
    intros.
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
    - destruct Hmem_obs_eq. destruct weak_obs_eq0.
      destruct Hobs_eq_id as [weak_obs_eq_id strong_obs_eq_id].
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
        * intros b1 b2 ofs Hf.
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
        *  intros b1 b2 ofs Hf Hperm.
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

  (** If the [invariant] holds for the DryConc machine then it also holds for
the FineConc machine provided that the two machines are related by a renaming
relation*)
  Lemma invariant_project:
    forall (tpc tpf : thread_pool) (mc mf : mem) f rmap1 b1 b2 ofs
      i (pff : containsThread tpf i) (pfc : containsThread tpc i)
      (HmemCompC : mem_compatible tpc mc)
      (HmemCompF : mem_compatible tpf mf)
      (Hcanonical: isCanonical rmap1.1)
      (Hcanonical2: isCanonical rmap1.2)
      virtue c cf
      (HinvF: invariant tpf)
      (Hf: f b1 = Some b2),
      let tpc' := updLockSet
                    (updThread pfc c (computeMap (getThreadR pfc)#1 virtue#1,
                                      computeMap (getThreadR pfc)#2 virtue#2))
                    (b1, ofs) rmap1 in
      let tpf' := updLockSet (updThread pff cf
                                        (computeMap (getThreadR pff).1
                                                    (projectAngel f virtue.1),
                                         computeMap (getThreadR pff).2
                                                    (projectAngel f virtue.2))) (b2, ofs)
                             (projectMap f rmap1.1, projectMap f rmap1.2) in
      forall
        (HinvC': invariant tpc')
        (HsimWeak: forall tid (pfc0 : containsThread tpc tid)
                     (pff0 : containsThread tpf tid),
            weak_tsim f pfc0 pff0 HmemCompC HmemCompF)
        (Htsim: mem_obs_eq f (restrPermMap (compat_th _ _ HmemCompC pfc).1)
                           (restrPermMap (compat_th _ _ HmemCompF pff).1))
        (HtsimL: mem_obs_eq f (restrPermMap (compat_th _ _ HmemCompC pfc).2)
                            (restrPermMap (compat_th _ _ HmemCompF pff).2))
        (Hlocks: forall (bl2 : block) (ofs : Z),
            lockRes tpf (bl2, ofs) ->
            exists bl1 : block, f bl1 = Some bl2)
        (HsimRes:
           forall (bl1 bl2 : block) (ofs : Z)
             rmap1 rmap2,
             f bl1 = Some bl2 ->
             forall (Hl1 : lockRes tpc (bl1, ofs) = Some rmap1)
               (Hl2 : lockRes tpf (bl2, ofs) = Some rmap2),
               strong_mem_obs_eq f
                                 (restrPermMap (compat_lp _ _ HmemCompC (bl1, ofs) _ Hl1).1)
                                 (restrPermMap (compat_lp _ _ HmemCompF (bl2, ofs) _ Hl2).1) /\
               strong_mem_obs_eq f
                                 (restrPermMap (compat_lp _ _ HmemCompC (bl1, ofs) _ Hl1).2)
                                 (restrPermMap (compat_lp _ _ HmemCompF (bl2, ofs) _ Hl2).2))
        (Hlock_if: forall (bl1 bl2 : block) (ofs : Z),
            f bl1 = Some bl2 ->
            lockRes tpc (bl1, ofs) <-> lockRes tpf (bl2, ofs))
        (HnumThreads: forall i, containsThread tpc i <-> containsThread tpf i),
        invariant tpf'.
  Proof.
    intros.
    assert (HnumThreads': forall i, containsThread tpc' i <-> containsThread tpf' i)
      by (intros; subst tpc' tpf'; split; intros Hcnt;
          apply cntUpdateL; apply cntUpdate;
          apply cntUpdateL' in Hcnt; apply cntUpdate' in Hcnt;
          apply HnumThreads; now auto).
    assert (Hthread_mapped: forall k (pfck': containsThread tpc' k) (pffk': containsThread tpf' k),
               forall b1 b2 ofs,
                 f b1 = Some b2 ->
                 Mem.perm_order'' ((getThreadR pfck').1 # b1 ofs) ((getThreadR pffk').1 # b2 ofs) /\
                 Mem.perm_order'' ((getThreadR pfck').2 # b1 ofs) ((getThreadR pffk').2 # b2 ofs)).
    { intros.
      rewrite! gLockSetRes.
      destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik; subst.
      - rewrite! gssThreadRes.
        simpl.
        erewrite! computeMap_projection_1 by eauto.
        split; now apply po_refl.
      - assert (pfck := cntUpdate' _ _ _ (cntUpdateL' _ _ pfck')).
        assert (pffk := cntUpdate' _ _ _ (cntUpdateL' _ _ pffk')).
        erewrite! gsoThreadRes with (cntj := pfck) by eauto.
        erewrite! gsoThreadRes with (cntj := pffk) by eauto.
        destruct (HsimWeak _ pfck pffk).
        destruct weak_tsim_data0.
        destruct weak_tsim_locks0.
        specialize (perm_obs_weak0 _ _ ofs0 H).
        specialize (perm_obs_weak1 _ _ ofs0 H).
        rewrite! restrPermMap_Cur in perm_obs_weak0.
        rewrite! restrPermMap_Cur in perm_obs_weak1.
        split; now assumption.
    }
    assert (Hthread_unmapped: forall k (pffk: containsThread tpf k)(pffk': containsThread tpf' k),
               forall b2 ofs,
                 (~exists b1, f b1 = Some b2) ->
                 ((getThreadR pffk').1 # b2 ofs = (getThreadR pffk).1 # b2 ofs) /\
                 ((getThreadR pffk').2 # b2 ofs = (getThreadR pffk).2 # b2 ofs)).
    { intros k pffk pffk' b0 ofs0 Hunmmaped.
      rewrite! gLockSetRes.
      destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik; subst.
      - rewrite! gssThreadRes.
        simpl.
        erewrite! computeMap_projection_2 by eauto.
        Tactics.pf_cleanup.
        split; reflexivity.
      - erewrite! gsoThreadRes with (cntj := pffk) by eauto.
        split; reflexivity.
    }

    assert (Hlock_mapped: forall laddrF rmapF (HresF: lockRes tpf' laddrF = Some rmapF),
               exists bc rmap,
                 lockRes tpc' (bc, laddrF.2) = Some rmap /\ f bc = Some laddrF.1 /\
                 forall b1 b2 ofs,
                   f b1 = Some b2 ->
                   Mem.perm_order'' (rmap.1 # b1 ofs) (rmapF.1 # b2 ofs) /\
                   Mem.perm_order'' (rmap.2 # b1 ofs) (rmapF.2 # b2 ofs)).
    { intros.
      subst tpf' tpc'.
      destruct (EqDec_address (b2, ofs) laddrF).
      - subst.
        rewrite gsslockResUpdLock in HresF.
        exists b1, rmap1.
        split. rewrite gsslockResUpdLock; reflexivity.
        split; auto.
        intros.
        inversion HresF.
        simpl.
        pose proof (injective (weak_obs_eq Htsim)).
        erewrite <- projectMap_correct by eauto.
        erewrite <- projectMap_correct by eauto.
        split; now apply po_refl.
      - erewrite gsolockResUpdLock in HresF by eauto.
        erewrite gsoThreadLPool in HresF.
        destruct laddrF as [bl ofsl].
        specialize (Hlocks bl ofsl).
        unfold isSome in Hlocks.
        rewrite HresF in Hlocks.
        specialize (Hlocks (Logic.eq_refl _)).
        destruct Hlocks as [bl1 Hfbl1].
        assert (Hneq: (b1, ofs) <> (bl1, ofsl))
          by (intros Hcontra; inversion Hcontra; subst;
              rewrite Hfbl1 in Hf; inversion Hf; subst; auto).
        specialize (Hlock_if _ _ ofsl Hfbl1).
        destruct (lockRes tpc (bl1, ofsl)) as [rmapC |] eqn:Hres.
        + exists bl1, rmapC.
          erewrite gsolockResUpdLock by eauto.
          erewrite gsoThreadLPool by eauto.
          split; auto. split; auto.
          intros b0 b3 ofs0 Hrenaming.
          specialize (HsimRes _ _ _ _ _ Hfbl1 Hres HresF).
          destruct HsimRes as [[Hperm1 _] [Hperm2 _]].
          specialize (Hperm1 _ _ ofs0 Hrenaming).
          specialize (Hperm2 _ _ ofs0 Hrenaming).
          rewrite! restrPermMap_Cur in Hperm1 Hperm2.
          rewrite Hperm1 Hperm2.
          split; now apply po_refl.
        + exfalso. erewrite HresF in Hlock_if.
          simpl in Hlock_if.
          destruct Hlock_if; now auto.
    }

    assert (Hlock_unmapped: forall laddrF rmapF (HresF: lockRes tpf' laddrF = Some rmapF),
               lockRes tpf laddrF = Some rmapF \/
               forall b2, ~ (exists b1, f b1 = Some b2) -> forall ofs, rmapF.1 # b2 ofs = None
                                                       /\ rmapF.2 # b2 ofs = None).
    { intros (bl & ofsl) rmapF HresF'.
      subst tpf'.
      destruct (EqDec_address (b2, ofs) (bl, ofsl)).
      - inversion e; subst.
        rewrite gsslockResUpdLock in HresF'.
        right.
        intros b2 Hunmapped ofs.
        inversion HresF'; subst.
        simpl.
        erewrite! projectMap_correct_2 by eauto.
        rewrite Hcanonical Hcanonical2;
          split; reflexivity.
      - erewrite gsolockResUpdLock in HresF' by eassumption.
        erewrite gsoThreadLPool in HresF'.
        left; assumption.
    }
    constructor.
    { (** disjointness between threads *)
      (** no race for coarse-grained state*)
      assert (Hno_raceC:= no_race_thr _ HinvC').
      assert (Hno_raceF:= no_race_thr _ HinvF).
      intros k j pffk' pffj' Hkj.
      unfold permMapsDisjoint2, permMapsDisjoint.
      erewrite <- forall2_and.
      intros bf ofs0.
      assert (Hbf: (exists b1, f b1 = Some bf) \/
                   ~ (exists b1, f b1 = Some bf))
        by eapply em.
      destruct Hbf as [[b Hbfm] | Hbfu].
      - assert (pfck': containsThread tpc' k)
          by (apply HnumThreads' in pffk'; auto).
        assert (pfcj': containsThread tpc' j)
          by (apply HnumThreads' in pffj'; auto).
        specialize (Hno_raceC _ _ pfck' pfcj' Hkj).
        unfold permMapsDisjoint2, permMapsDisjoint in Hno_raceC.
        erewrite <- forall2_and in Hno_raceC.
        destruct (Hno_raceC b ofs0) as [HpermD HpermL].
        pose proof (Hthread_mapped _ pfck' pffk' b bf ofs0 Hbfm) as Hk.
        destruct Hk as [HkD HkL].
        pose proof (Hthread_mapped _ pfcj' pffj' b bf ofs0 Hbfm) as Hj.
        destruct Hj as [HjD HjL].
        split;
          eapply perm_union_lower; eauto;
            rewrite perm_union_comm;
            eapply perm_union_lower; eauto;
              rewrite perm_union_comm; eauto.
      - assert (pffk: containsThread tpf k)
          by (apply cntUpdateL' in pffk';
              apply cntUpdate' in pffk'; auto).
        assert (pffj: containsThread tpf j)
          by (apply cntUpdateL' in pffj';
              apply cntUpdate' in pffj'; auto).
        erewrite (Hthread_unmapped _ pffk pffk' bf ofs0 Hbfu).1.
        erewrite (Hthread_unmapped _ pffk pffk' bf ofs0 Hbfu).2.
        erewrite (Hthread_unmapped _ pffj pffj' bf ofs0 Hbfu).1.
        erewrite (Hthread_unmapped _ pffj pffj' bf ofs0 Hbfu).2.
        specialize (Hno_raceF _ _ pffk pffj Hkj).
        unfold permMapsDisjoint2, permMapsDisjoint in Hno_raceF.
        erewrite <- forall2_and in Hno_raceF.
        now eauto.
    }
    { (** disjointness between lock resources*)
      intros laddr1 laddr2 rmap0 rmap2 Hneq Hres0 Hres2.
      unfold permMapsDisjoint2, permMapsDisjoint.
      erewrite <- forall2_and.
      intros bf ofs0.
      assert (Hbf: (exists b1, f b1 = Some bf) \/
                   ~ (exists b1, f b1 = Some bf))
        by eapply em.
      destruct Hbf as [[b Hbfm] | Hbfu].
      - destruct (Hlock_mapped _ _ Hres0) as [bc1 [rmap0C [HresC [Hfl1 Hperm0]]]].
        destruct (Hperm0 _ _ ofs0 Hbfm).
        destruct (Hlock_mapped _ _ Hres2) as [bc2 [rmap2C [Hres2C [Hfl2 Hperm2]]]].
        destruct (Hperm2 _ _ ofs0 Hbfm).
        assert (HneqC: (bc1, laddr1.2) <> (bc2, laddr2.2)) by
            (intros Hcontra;
             inversion Hcontra; subst;
             rewrite Hfl1 in Hfl2; inversion Hfl2;
             destruct laddr1, laddr2; simpl in *; subst;
             now auto).
        pose proof (no_race_lr _ HinvC' _ _ _ _ HneqC HresC Hres2C) as Hdisjoint.
        unfold permMapsDisjoint2, permMapsDisjoint in Hdisjoint.
        erewrite <- forall2_and in Hdisjoint.
        destruct (Hdisjoint b ofs0).
        split;
          eapply perm_union_lower; eauto;
            rewrite perm_union_comm;
            eapply perm_union_lower; eauto;
              rewrite perm_union_comm; now eauto.
      - subst tpf'.
        destruct (Hlock_unmapped _ _ Hres0) as [Heq0 | Hempty0].
        + destruct (Hlock_unmapped _ _ Hres2) as [Heq2 | Hempty2].
          * pose proof (no_race_lr _ HinvF  _ _ _ _ Hneq Heq0 Heq2) as Hdisjoint.
            unfold permMapsDisjoint2, permMapsDisjoint in Hdisjoint.
            erewrite <- forall2_and in Hdisjoint.
            now eauto.
          * specialize (Hempty2 _ Hbfu ofs0).
            destruct Hempty2 as [H1 H2].
            rewrite H1 H2.
            split; rewrite perm_union_comm; apply not_racy_union;
              now constructor.
        + specialize (Hempty0 _ Hbfu ofs0).
          destruct Hempty0 as [H1 H2].
          rewrite H1 H2.
          split; apply not_racy_union;
            now constructor.
    }
    { (**disjointness between lock resources and threads*)
      intros k laddrF pffk' rmapF HresF.
      unfold permMapsDisjoint2, permMapsDisjoint.
      erewrite <- forall2_and.
      intros b0 ofs0.
      assert (Hbf: (exists b1, f b1 = Some b0) \/
                   ~ (exists b1, f b1 = Some b0))
        by eapply em.
      destruct Hbf as [[b Hbfm] | Hbfu].
      - assert (pfck': containsThread tpc' k)
          by (apply HnumThreads' in pffk'; auto).
        destruct (Hlock_mapped _ _ HresF) as [bc [rmapC [HresC [Hfl HpermC]]]].
        destruct (HpermC _ _ ofs0 Hbfm).
        pose proof (Hthread_mapped _ pfck' pffk' b b0 ofs0 Hbfm) as Hk.
        destruct Hk as [HkD HkL].
        pose proof (no_race _ HinvC' _ _ pfck' _ HresC).
        unfold permMapsDisjoint2, permMapsDisjoint in H1.
        erewrite <- forall2_and in H1.
        destruct (H1 b ofs0).
        split;
          eapply perm_union_lower; eauto;
            rewrite perm_union_comm;
            eapply perm_union_lower; eauto;
              rewrite perm_union_comm; eauto.
      - assert (pffk: containsThread tpf k)
          by (apply cntUpdateL' in pffk';
              apply cntUpdate' in pffk'; auto).
        erewrite (Hthread_unmapped _ pffk pffk' b0 ofs0 Hbfu).1.
        erewrite (Hthread_unmapped _ pffk pffk' b0 ofs0 Hbfu).2.
        subst tpf'.
        destruct (Hlock_unmapped _ _ HresF) as [Heq0 | Hempty0].
        + pose proof ((no_race _ HinvF) _ _ pffk _ Heq0) as Hno_race.
          unfold permMapsDisjoint2, permMapsDisjoint in Hno_race.
          erewrite <- forall2_and in Hno_race.
          now eauto.
        + erewrite (Hempty0 _ Hbfu ofs0).1.
          erewrite (Hempty0 _ Hbfu ofs0).2.
          split;
            rewrite perm_union_comm;
            apply not_racy_union;
            now constructor.
    }
    { (** coherence between lock resources data and thread locks*)
      intros k pffk'.
      split.
      - intros j pffj' b0 ofs0.
        assert (Hbf: (exists b1, f b1 = Some b0) \/
                     ~ (exists b1, f b1 = Some b0))
          by eapply em.
        destruct Hbf as [[b Hbfm] | Hbfu].
        + assert (pfck': containsThread tpc' k)
            by (apply HnumThreads' in pffk'; auto).
          assert (pfcj': containsThread tpc' j)
            by (apply HnumThreads' in pffj'; auto).
          pose proof (Hthread_mapped _ pfck' pffk' b b0 ofs0 Hbfm) as Hk.
          destruct Hk as [_ HkL].
          pose proof (Hthread_mapped _ pfcj' pffj' b b0 ofs0 Hbfm) as Hj.
          destruct Hj as [HjD].
          pose proof ((thread_data_lock_coh _ HinvC' _ pfck').1 _ pfcj' b ofs0).
          eapply perm_coh_lower;
            now eauto.
        + assert (pffj: containsThread tpf j)
            by (apply cntUpdateL' in pffj';
                apply cntUpdate' in pffj'; auto).
          erewrite (Hthread_unmapped _ pffj pffj' b0 ofs0 Hbfu).1.
          assert (pffk: containsThread tpf k)
            by (apply cntUpdateL' in pffk';
                apply cntUpdate' in pffk'; auto).
          erewrite (Hthread_unmapped _ pffk pffk' b0 ofs0 Hbfu).2.
          now eapply ((thread_data_lock_coh _ HinvF _ pffk).1 _ pffj b0 ofs0).
      - intros laddrF rmapF HresF b0 ofs0.
        assert (Hbf: (exists b1, f b1 = Some b0) \/
                     ~ (exists b1, f b1 = Some b0))
          by eapply em.
        destruct Hbf as [[b Hbfm] | Hbfu].
        + assert (pfck': containsThread tpc' k)
            by (apply HnumThreads' in pffk'; auto).
          pose proof (Hthread_mapped _ pfck' pffk' b b0 ofs0 Hbfm) as Hk.
          destruct Hk as [_ HkL].
          destruct (Hlock_mapped _ _ HresF) as [bc [rmapC [HresC [Hfl HpermC]]]].
          destruct (HpermC _ _ ofs0 Hbfm).
          pose proof ((thread_data_lock_coh _ HinvC' _ pfck').2 _ _ HresC b ofs0).
          eapply perm_coh_lower;
            now eauto.
        + assert (pffk: containsThread tpf k)
            by (apply cntUpdateL' in pffk';
                apply cntUpdate' in pffk'; auto).
          erewrite (Hthread_unmapped _ pffk pffk' b0 ofs0 Hbfu).2.
          subst tpf'.
          destruct (Hlock_unmapped _ _ HresF) as [Heq0 | Hempty0].
          pose proof ((thread_data_lock_coh _ HinvF _ pffk).2 _ _ Heq0 b0 ofs0) as Hno_race.
          now eauto.
          erewrite (Hempty0 _ Hbfu ofs0).1.
          simpl.
          pose proof ((invariant_not_freeable HinvF b0 ofs0).1 _ pffk).
          destruct ((getThreadR pffk).2 # b0 ofs0) as [p|];
            try (destruct p); auto.
    }
    { (** locks in lock resources are coherent with thread data*)
      intros laddrF rmapF HresF.
      split.
      - intros j pffj' b0 ofs0.
        assert (Hbf: (exists b1, f b1 = Some b0) \/
                     ~ (exists b1, f b1 = Some b0))
          by eapply em.
        destruct Hbf as [[b Hbfm] | Hbfu].
        + assert (pfcj': containsThread tpc' j)
            by (apply HnumThreads' in pffj'; auto).
          pose proof (Hthread_mapped _ pfcj' pffj' b b0 ofs0 Hbfm).1 as Hj.
          destruct (Hlock_mapped _ _ HresF) as [bc [rmapC [HresC [Hfl HpermC]]]].
          destruct (HpermC _ _ ofs0 Hbfm).
          pose proof ((locks_data_lock_coh _ HinvC' _ _ HresC).1 _ pfcj' b ofs0).
          eapply perm_coh_lower;
            now eauto.
        +  assert (pffj: containsThread tpf j)
            by (apply cntUpdateL' in pffj';
                apply cntUpdate' in pffj'; auto).
           erewrite (Hthread_unmapped _ pffj pffj' b0 ofs0 Hbfu).1.
           subst tpf'.
           destruct (Hlock_unmapped _ _ HresF) as [Heq0 | Hempty0].
           * pose proof ((locks_data_lock_coh _ HinvF _ _ Heq0).1 _ pffj) as Hno_race.
             now eauto.
           * erewrite (Hempty0 _ Hbfu ofs0).2.
             now apply perm_coh_empty_1.
      - intros laddr2F' rmap2F' Hres2F' b0 ofs0.
        subst tpf'.
        assert (Hbf: (exists b1, f b1 = Some b0) \/
                     ~ (exists b1, f b1 = Some b0))
          by eapply em.
        destruct Hbf as [[b Hbfm] | Hbfu].
        + destruct (Hlock_mapped _ _ HresF) as [bc [rmapC [HresC [Hfl HpermC]]]].
          destruct (HpermC _ _ ofs0 Hbfm).
          destruct (Hlock_mapped _ _ Hres2F') as [bc2 [rmapC2 [HresC2 [Hfl2 HpermC2]]]].
          destruct (HpermC2 _ _ ofs0 Hbfm).
          pose proof ((locks_data_lock_coh _ HinvC' _ _ HresC).2 _ _ HresC2 b ofs0).
          eapply perm_coh_lower;
            now eauto.
        + destruct (Hlock_unmapped _ _ HresF) as [Heq0 | Hempty0].
          * destruct (Hlock_unmapped _ _ Hres2F') as [Heq2 | Hempty2];
              first by (eapply ((locks_data_lock_coh _ HinvF _ _ Heq0).2 _ _ Heq2 b0 ofs0)).
            erewrite (Hempty2 _ Hbfu ofs0).1.
            pose proof ((invariant_not_freeable HinvF b0 ofs0).2 _ _ Heq0).
            destruct (rmapF.2 # b0 ofs0) as [p|];
              try (destruct p); simpl;
              now auto.
          * erewrite (Hempty0 _ Hbfu ofs0).2.
            now apply perm_coh_empty_1.
    }
    { (** Proof of [lr_valid] *)
      intros b0 ofs0.
      destruct (lockRes tpf') eqn:Hres0; auto.
      intros ofs1 Hofs1.
      pose proof (lockRes_valid _ HinvC') as HlrC'.
      subst tpc' tpf'.
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
            pose proof (lockRes_valid _ HinvF).
            specialize (H b2 ofs0).
            rewrite Hres0 in H; eauto.
      }
      { erewrite gsolockResUpdLock
          by (intro Hcontra; inversion Hcontra; subst; auto).
        rewrite gsoThreadLPool.
        erewrite gsolockResUpdLock in Hres0
          by (intro Hcontra; inversion Hcontra; subst; auto).
        rewrite gsoThreadLPool in Hres0.
        pose proof (lockRes_valid _ HinvF).
        specialize (H b0 ofs0).
        rewrite Hres0 in H; eauto.
      }
    }
  Qed.

  Lemma gss_mem_obs_eq_lock:
    forall mc mf mc' mf' rmap rmapF bl1 bl2 ofsl f v
      rmap' rmapF' virtue
      (Hlt: permMapLt rmap (getMaxPerm mc))
      (HltF: permMapLt rmapF (getMaxPerm mf))
      (Hlt': permMapLt rmap' (getMaxPerm mc))
      (HltF': permMapLt rmapF' (getMaxPerm mf))
      (Hlt2: permMapLt (computeMap rmap virtue) (getMaxPerm mc'))
      (Hlt2F: permMapLt (computeMap rmapF (projectAngel f virtue)) (getMaxPerm mf'))
      (Hf: f bl1 = Some bl2)
      (Hobs_eq: mem_obs_eq f (restrPermMap Hlt) (restrPermMap HltF))
      (Hobs_eq': strong_mem_obs_eq f (restrPermMap Hlt') (restrPermMap HltF'))
      (Hstore: Mem.mem_contents mc' = PMap.set bl1 (Mem.setN (encode_val Mint32 (Vint v)) ofsl (Mem.mem_contents mc) # bl1)
                                               (Mem.mem_contents mc))
      (HstoreF: Mem.mem_contents mf' = PMap.set bl2 (Mem.setN (encode_val Mint32 (Vint v)) ofsl (Mem.mem_contents mf) # bl2)
                                                (Mem.mem_contents mf))
      (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b)
      (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b)
      (Hjoin: permMapJoin rmap' rmap (computeMap rmap virtue)),
      mem_obs_eq f (restrPermMap Hlt2) (restrPermMap Hlt2F).
  Proof.
    intros.
    inversion Hobs_eq.
    destruct weak_obs_eq0.
    assert (Hvb': forall b, ~ Mem.valid_block mc b <-> ~ Mem.valid_block mc' b)
      by (intros; split; intros Hinvalid Hcontra;
            by apply Hvb in Hcontra).
    constructor.
    { (** weak_obs_eq*)
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
      specialize (perm_obs_weak0 _ _ ofs0 Hf1).
      erewrite computeMap_projection_1; eauto;
        by apply po_refl.
    }
    { (** proof of [strong_mem_obs_eq]*)
      constructor.
      - intros b1 b2 ofs0 Hf1.
        do 2 rewrite restrPermMap_Cur.
        erewrite computeMap_projection_1; eauto;
          by apply po_refl.
      - intros b1 b2 ofs0 Hf1 Hperm.
        unfold Mem.perm in *.
        assert (Hperm_eq := restrPermMap_Cur Hlt2 b1 ofs0).
        unfold permission_at in Hperm_eq.
        rewrite Hperm_eq in Hperm.
        (** We first prove that the values on location [(b1, ofs0)] and [(b2, ofs0)] are related by [memval_obs_eq]*)
        assert (Hval_eq: memval_obs_eq f (ZMap.get ofs0 (Mem.mem_contents mc) # b1) (ZMap.get ofs0 (Mem.mem_contents mf) # b2)).
        {(** Since the new permissions on [(b1,ofs0)] are above
                        [Readable] it must be that it is also above [Readable]
                        on [rmap'] or [rmap] by [permjoin_readable_iff]*)
          specialize (Hjoin b1 ofs0).
          apply permjoin_readable_iff in Hjoin.
          apply Hjoin in Hperm.
          simpl.
          (** And hence we can derive the goal from the premises*)
          destruct Hperm as [Hperm | Hperm];
            [assert (Heq := restrPermMap_Cur Hlt' b1 ofs0);
             pose proof ((val_obs_eq Hobs_eq') b1 b2 ofs0 Hf1) as Hval_eq|
             assert (Heq := restrPermMap_Cur Hlt b1 ofs0);
             pose proof ((val_obs_eq strong_obs_eq0) b1 b2 ofs0 Hf1) as Hval_eq];
            unfold Mem.perm, permission_at in *;
            rewrite Heq in Hval_eq;
            specialize (Hval_eq Hperm);
            simpl in Hval_eq;
            assumption.
        }

        simpl.
        rewrite Hstore HstoreF.

        destruct (Pos.eq_dec b1 bl1) as [Heq | Hneq];
          [| assert (b2 <> bl2)
             by (intros Hcontra; subst;
                 apply Hneq; eapply injective0; eauto);
             subst;
             erewrite! Maps.PMap.gso by auto;
             assumption].
        subst bl1.
        assert (b2 = bl2)
          by (rewrite Hf1 in Hf; inversion Hf; by subst); subst bl2.
        rewrite! Maps.PMap.gss.
        destruct (Z_lt_le_dec ofs0 ofsl) as [Hofs_lt | Hofs_ge].
        erewrite! Mem.setN_outside by (left; auto);
          by assumption.
        destruct (Z_lt_ge_dec
                    ofs0 (ofsl + (size_chunk Mint32)))
          as [Hofs_lt | Hofs_ge'].

        apply setN_obs_eq with (access := fun q => q = ofs0);
          eauto using encode_val_obs_eq, val_obs.
        intros; subst; assumption.
        erewrite! Mem.setN_outside by (right; rewrite size_chunk_conv in Hofs_ge';
                                         by rewrite encode_val_length);
          by auto.
    }
  Qed.


  Lemma gss_mem_obs_eq_unlock:
    forall mc mf mc' mf' rmap rmapF bl1 bl2 ofsl f v
      rmap' rmapF' rmap2 rmap2F
      (Hlt': permMapLt rmap' (getMaxPerm mc'))
      (HltF': permMapLt rmapF' (getMaxPerm mf'))
      (Hlt2: permMapLt rmap2 (getMaxPerm mc))
      (Hlt2F: permMapLt rmap2F (getMaxPerm mf))
      (Hf: f bl1 = Some bl2)
      (Hobs_eq2: mem_obs_eq f (restrPermMap Hlt2) (restrPermMap Hlt2F))
      (Hstore: Mem.mem_contents mc' = PMap.set bl1 (Mem.setN (encode_val Mint32 (Vint v)) ofsl (Mem.mem_contents mc) # bl1)
                                               (Mem.mem_contents mc))
      (HstoreF: Mem.mem_contents mf' = PMap.set bl2 (Mem.setN (encode_val Mint32 (Vint v)) ofsl (Mem.mem_contents mf) # bl2)
                                                (Mem.mem_contents mf))
      (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b)
      (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b)
      (Hjoin: permMapJoin rmap' rmap rmap2)
      (HpmapF: forall b, (~exists b', f b' = Some b) ->
                    forall ofs, (rmapF # b ofs = None /\ rmap2F # b ofs = rmapF' # b ofs) \/
                           (rmapF' # b ofs = None /\ rmap2F # b ofs = rmapF # b ofs))
      (Hrmap': forall b1 b2 ofs, f b1 = Some b2 -> (rmap' # b1) ofs = (rmapF' # b2) ofs)
      (Hrmap': forall b1 b2 ofs, f b1 = Some b2 -> (rmap # b1) ofs = (rmapF # b2) ofs),
      mem_obs_eq f (restrPermMap Hlt') (restrPermMap HltF').
  Proof.
     intros.
     inversion Hobs_eq2.
     destruct weak_obs_eq0.
     assert (Hvb': forall b, ~ Mem.valid_block mc b <-> ~ Mem.valid_block mc' b)
       by (intros; split; intros Hinvalid Hcontra;
             by apply Hvb in Hcontra).
     constructor.
     { (** weak_obs_eq*)
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
       specialize (perm_obs_weak0 _ _ ofs0 Hf1).
       erewrite Hrmap';
         eauto using po_refl.
     }
     { (** proof of [strong_mem_obs_eq]*)
       constructor.
       - intros b1 b2 ofs0 Hf1.
         do 2 rewrite restrPermMap_Cur.
         erewrite Hrmap';
           by eauto.
       - intros b1 b2 ofs0 Hf1 Hperm.
         unfold Mem.perm in *.
         assert (Hperm_eq := restrPermMap_Cur Hlt' b1 ofs0).
         unfold permission_at in Hperm_eq.
         rewrite Hperm_eq in Hperm.
         (** We first prove that the values on location [(b1, ofs0)] and [(b2, ofs0)] are related by [memval_obs_eq]*)
         assert (Hval_eq: memval_obs_eq f (ZMap.get ofs0 (Mem.mem_contents mc) # b1) (ZMap.get ofs0 (Mem.mem_contents mf) # b2)).
         {(** Since the new permissions on [(b1,ofs0)] are above [Readable] it
              must be that it is also above [Readable] on [rmap2]
              [permjoin_readable_iff]*)
           specialize (Hjoin b1 ofs0).
           apply permjoin_readable_iff in Hjoin.
           pose proof (Hjoin.2 (or_introl Hperm)) as Hreadable.
           assert (Heq:= restrPermMap_Cur Hlt2 b1 ofs0).
           pose proof ((val_obs_eq strong_obs_eq0) b1 b2 ofs0 Hf1) as Hval_eq.
           unfold Mem.perm, permission_at in *.
           rewrite Heq in Hval_eq.
           simpl in Hval_eq.
           now eauto.
         }

         simpl.
         rewrite Hstore HstoreF.
         destruct (Pos.eq_dec b1 bl1) as [Heq | Hneq];
           [| assert (b2 <> bl2)
              by (intros Hcontra; subst;
                  apply Hneq; eapply injective0; eauto);
              subst;
              erewrite! Maps.PMap.gso by auto;
              assumption].
         subst bl1.
         assert (b2 = bl2)
           by (rewrite Hf1 in Hf; inversion Hf; by subst); subst bl2.
         rewrite! Maps.PMap.gss.
         destruct (Z_lt_le_dec ofs0 ofsl) as [Hofs_lt | Hofs_ge].
         erewrite! Mem.setN_outside by (left; auto);
           by assumption.
         destruct (Z_lt_ge_dec
                     ofs0 (ofsl + (size_chunk Mint32)))
           as [Hofs_lt | Hofs_ge'].

         apply setN_obs_eq with (access := fun q => q = ofs0);
           eauto using encode_val_obs_eq, val_obs.
         intros; subst; assumption.
         erewrite! Mem.setN_outside by (right; rewrite size_chunk_conv in Hofs_ge';
                                          by rewrite encode_val_length);
           by auto.
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
    - intros.
      unfold permMapLt.
      erewrite <- forall2_and.
      intros b' ofs'.
      erewrite <- mem_store_max by eauto.
      rewrite getMax_restr.
      destruct (compat_th0 _ cnt).
      split; eauto.
    - intros l rmap Hres.
      unfold permMapLt.
      erewrite <- forall2_and.
      intros b' ofs'.
      erewrite <- mem_store_max with (b' := b') (ofs' := ofs') by eauto.
      rewrite getMax_restr.
      destruct (compat_lp0 _ _ Hres).
      split; eauto.
    - intros.
      eapply Mem.store_valid_block_1; eauto.
      rewrite restrPermMap_valid.
      eauto.
  Qed.

  Lemma mem_compatible_sync:
    forall tpf mf cf virtue1 virtue2 f bl1 bl2 ofsl i
      (pff: containsThread tpf i)
      (Hcanonical1: isCanonical virtue2.1)
      (Hcanonical2: isCanonical virtue2.2)
      (Hf: f bl1 = Some bl2)
      (HmaxF: max_inv mf)
      (HmemCompF: mem_compatible tpf mf)
      (Hcodomain_valid : forall b1 b2 : block,
          f b1 = Some b2 -> Mem.valid_block mf b2),
      let newPermMap := (computeMap (getThreadR pff).1 (projectAngel f virtue1.1),
                         computeMap (getThreadR pff).2 (projectAngel f virtue1.2)) in
      let newLockMap := (projectMap f virtue2.1, projectMap f virtue2.2) in
      mem_compatible (updLockSet (updThread pff cf newPermMap)
                                            (bl2, ofsl) newLockMap) mf.
  Proof.
    intros.
    constructor.
    { intros j pffj.
      rewrite gLockSetRes.
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
      - subst.
        rewrite gssThreadRes.
        unfold permMapLt.
        rewrite <- forall2_and.
        intros b2 ofs.
        simpl.
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
        split;
          match goal with
          | [|- match ?Expr with _ => _ end] =>
            destruct Expr
          end; constructor.
        erewrite! computeMap_projection_2 by eauto.
        destruct (compat_th _ _ HmemCompF pff);
          auto.
      - rewrite gsoThreadRes; auto.
        eapply HmemCompF.
    }
    { intros (bl', ofsl') rmap Hres.
      destruct (EqDec_address (bl2, ofsl) (bl', ofsl')).
      - inversion e; subst.
        rewrite gssLockRes in Hres. inversion Hres; subst.
        unfold permMapLt.
        rewrite <- forall2_and.
        simpl.
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
        split;
          match goal with
          | [|- match ?Expr with _ => _ end] =>
            destruct Expr
          end; constructor.
        erewrite! projectMap_correct_2 by eauto.
        rewrite Hcanonical1 Hcanonical2.
        split;
          by apply po_None.
      - rewrite gsoLockRes in Hres; auto.
        rewrite gsoThreadLPool in Hres.
        eapply HmemCompF; eauto.
    }
    { intros (bl' & ofsl') rmap Hres.
      destruct (EqDec_address (bl2, ofsl) (bl', ofsl')).
      - inversion e; subst.
        eapply Hcodomain_valid; eauto.
      - erewrite gsoLockRes in Hres by assumption.
        rewrite gsoThreadLPool in Hres.
        eapply (lockRes_blocks _ _ HmemCompF);
          by eassumption.
    }
  Qed.

  Lemma mem_compatible_spawn :
    forall (tpf : thread_pool) (mf : mem) (cf : ctl)
      virtue1 virtue2 (f : block -> option block)
      vf args i (pff : containsThread tpf i)
      (Hmax_inv: max_inv mf)
      (HmemCompF: mem_compatible tpf mf)
      (Hcodomain: forall b1 b2 : block, f b1 = Some b2 -> Mem.valid_block mf b2),
      mem_compatible
        (addThread
           (updThread pff cf
                      (computeMap (getThreadR pff).1 (projectAngel f virtue1.1),
                       computeMap (getThreadR pff).2 (projectAngel f virtue1.2)))
                      vf args (computeMap empty_map (projectAngel f virtue2.1),
                               computeMap empty_map (projectAngel f virtue2.2))) mf.
  Proof.
    intros.
    constructor.
    { intros j pffj''.
      assert (pffj' := cntAdd' _ _ _ pffj'').
      destruct pffj' as [[pffj' Hneq] | Heq].
      - (** case it's an old thread *)
        erewrite gsoAddRes with (cntj := pffj') by eauto.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        + subst.
          rewrite gssThreadRes.
          unfold permMapLt.
          erewrite <- forall2_and.
          intros b2 ofs.
          assert (Hb2: (exists b', f b' = Some b2) \/
                       ~ (exists b', f b' = Some b2))
            by eapply em.
          destruct Hb2 as [Hbm | Hbu].
          * (** case b2 is mapped by f*)
            destruct Hbm as [b1 Hfb1].
            apply Hcodomain in Hfb1.
            specialize (Hmax_inv _ ofs Hfb1).
            rewrite getMaxPerm_correct.
            rewrite Hmax_inv.
            simpl.
            split;
              match goal with
            | [ |- match ?Expr with _ => _ end] =>
              destruct Expr
              end;
              now constructor.
          * simpl.
            erewrite! computeMap_projection_2 by eauto.
            split;
            now eapply HmemCompF.
        + rewrite gsoThreadRes; auto.
          split;
            now eapply HmemCompF.
      - (** case it's the new thread*)
        subst.
        erewrite gssAddRes; eauto.
        unfold permMapLt.
        erewrite <- forall2_and.
        intros b2 ofs.
        assert (Hb2: (exists b', f b' = Some b2) \/
                     ~ (exists b', f b' = Some b2))
          by eapply em.
        destruct Hb2 as [Hbm | Hbu].
        + (** case b2 is mapped by f*)
          destruct Hbm as [b1 Hfb1].
          apply Hcodomain in Hfb1.
          specialize (Hmax_inv _ ofs Hfb1).
          rewrite getMaxPerm_correct.
          rewrite Hmax_inv.
          simpl.
          split;
            match goal with
            | [|- match ?Expr with _ => _ end] =>
              destruct Expr
            end;
            now constructor.
        + simpl.
          erewrite! computeMap_projection_2 by eauto.
          rewrite empty_map_spec.
          split;
            now apply po_None.
    }
    { intros (bl', ofsl') rmap Hres.
      rewrite gsoAddLPool in Hres.
      rewrite gsoThreadLPool in Hres.
      eapply HmemCompF; eauto.
    }
    { intros l rmap Hres.
      rewrite gsoAddLPool in Hres.
      rewrite gsoThreadLPool in Hres.
      eapply (lockRes_blocks _ _ HmemCompF);
        now eassumption.
    }
  Qed.

  (** [permMapJoin] is preserved through block renamings*)
  Lemma permMapJoin_project:
    forall (f : memren)
      pmap pmapF pmap' pmapF' pmapR pmapRF
      (HpmapF: forall b, (~exists b', f b' = Some b) ->
                    forall ofs, (pmapF # b ofs = None /\ pmapRF # b ofs = pmapF' # b ofs) \/
                           (pmapF' # b ofs = None /\ pmapRF # b ofs = pmapF # b ofs))
      (Hangel: permMapJoin pmap pmap' pmapR)
      (Hpmap: forall b1 b2 ofs, f b1 = Some b2 -> (pmap # b1) ofs = (pmapF # b2) ofs)
      (Hpmap': forall b1 b2 ofs, f b1 = Some b2 -> (pmap' # b1) ofs = (pmapF' # b2) ofs)
      (HpmapR: forall b1 b2 ofs, f b1 = Some b2 -> (pmapR # b1) ofs = (pmapRF # b2) ofs),
      permMapJoin pmapF pmapF' pmapRF.
  Proof.
    intros.
    intros b2 ofs.
    (**NOTE: this is actually decidable*)
    assert (Hb2: (exists b1, f b1 = Some b2) \/
                 ~ (exists b1, f b1 = Some b2))
      by eapply em.
    destruct Hb2 as [[b1 Hf1] | Hunmapped].
    - specialize (Hangel b1 ofs).
      erewrite <- Hpmap, <- Hpmap', <- HpmapR
        by eassumption.
      assumption.
    - destruct (HpmapF _ Hunmapped ofs) as [[Hempty Heq] | [Hempty Heq]];
        rewrite Hempty Heq;
        now constructor.
  Qed.

  Lemma invariant_mklock:
    forall tp c b ofs  i (cnti: containsThread tp i)
      (Hinv: invariant tp)
      (Hperm: forall ofs', Intv.In ofs' (ofs, ofs + Z.of_nat lksize.LKSIZE_nat)%Z ->
                      Mem.perm_order' ((getThreadR cnti)#1 # b ofs') Writable),
      let tp' := (updThread cnti c
                            (setPermBlock (Some Nonempty) b ofs (getThreadR cnti)#1 lksize.LKSIZE_nat,
                             setPermBlock (Some Writable) b ofs
                                          (getThreadR cnti)#2 lksize.LKSIZE_nat)) in
      invariant tp'.
  Proof.
    intros.
    inversion Hinv.
    assert (Hperm_thr1: forall k (cntk: containsThread tp k) (Hik: i <> k) ofs',
               Intv.In ofs' (ofs, ofs + Z.of_nat lksize.LKSIZE_nat)%Z ->
               Mem.perm_order'' (Some Nonempty) ((getThreadR cntk).1 # b ofs')).
    { intros.
      specialize ((no_race_thr0 _ _ cnti cntk Hik).1 b ofs').
      intros.
      specialize (Hperm ofs' H).
      destruct ((getThreadR cnti).1 # b ofs'); simpl in Hperm;
        inversion Hperm; subst; simpl in H0;
          destruct (((getThreadR cntk)#1) # b ofs');
          simpl; try (destruct p); auto using perm_order;
            destruct H0; discriminate.
    }
    assert (Hperm_thr2: forall k (cntk: containsThread tp k) ofs',
               Intv.In ofs' (ofs, ofs + Z.of_nat lksize.LKSIZE_nat)%Z ->
               (getThreadR cntk).2 # b ofs' = None).
    { intros.
      specialize ((thread_data_lock_coh0 _ cntk).1 _ cnti b ofs').
      intros.
      specialize (Hperm ofs' H).
      destruct ((getThreadR cnti).1 # b ofs'); simpl in Hperm;
        inversion Hperm; subst; simpl in H0;
          destruct (((getThreadR cntk)#2) # b ofs');
          simpl; tauto.
    }

    assert (Hperm_res1: forall laddr rmap (Hres: lockRes tp laddr = Some rmap) ofs',
               Intv.In ofs' (ofs, ofs + Z.of_nat lksize.LKSIZE_nat)%Z ->
               Mem.perm_order'' (Some Nonempty) (rmap.1 # b ofs')).
    { intros.
      specialize ((no_race0 _ _ cnti _ Hres).1 b ofs').
      intros.
      specialize (Hperm ofs' H).
      destruct ((getThreadR cnti).1 # b ofs'); simpl in Hperm;
        inversion Hperm; subst; simpl in H0;
          destruct (rmap#1 # b ofs');
          simpl; try (destruct p); auto using perm_order;
            destruct H0; discriminate.
    }
    assert (Hperm_res2: forall laddr rmap (Hres: lockRes tp laddr = Some rmap) ofs',
               Intv.In ofs' (ofs, ofs + Z.of_nat lksize.LKSIZE_nat)%Z ->
               rmap.2 # b ofs' = None).
    { intros.
      specialize ((locks_data_lock_coh0 _ _ Hres).1 _ cnti b ofs').
      intros.
      specialize (Hperm ofs' H).
      destruct ((getThreadR cnti).1 # b ofs'); simpl in Hperm;
        inversion Hperm; subst; simpl in H0;
          destruct (rmap.2 # b ofs');
          simpl; tauto.
    }

    constructor.

    { intros k j cntk' cntj' Hkj.
      pose proof (cntUpdate c ((setPermBlock (Some Nonempty) b ofs (getThreadR cnti)#1 lksize.LKSIZE_nat,
                                setPermBlock (Some Writable) b ofs
                                             (getThreadR cnti)#2 lksize.LKSIZE_nat)) cnti cnti) as cnti'.
      assert (Hdisjoint_i': forall x (cntx': containsThread tp' x), i <> x -> permMapsDisjoint2 (getThreadR cnti') (getThreadR cntx')).
      { intros.
        rewrite gssThreadRes.
        pose proof (cntUpdate' _ _ _ cntx') as cntx.
        unfold permMapsDisjoint2, permMapsDisjoint.
        erewrite <- forall2_and.
        intros b' ofs'.
        subst tp'.
        destruct (Pos.eq_dec b b').
        + subst.
          destruct (Intv.In_dec ofs' (ofs, ofs + Z.of_nat (lksize.LKSIZE_nat))%Z).
          * rewrite! setPermBlock_same; auto.
            erewrite @gsoThreadRes with (cntj := cntx) by eauto.
            split.
            specialize (Hperm_thr1 _ cntx ltac:(auto) ofs' i0).
            destruct (((getThreadR cntx)#1) # b' ofs'); simpl in Hperm_thr1;
              inversion Hperm_thr1; subst; simpl;
                now eauto.
            specialize (Hperm_thr2 _ cntx ofs' i0).
            erewrite Hperm_thr2.
            rewrite perm_union_comm;
              eapply not_racy_union;
              now constructor.
          * apply Intv.range_notin in n;
              try (simpl; eapply Z.lt_add_pos_r; now apply lksize.LKSIZE_pos).
            rewrite! setPermBlock_other_1; eauto.
            erewrite @gsoThreadRes with (cntj := cntx) by eauto.
            destruct (no_race_thr0 _ _ cnti cntx ltac:(auto));
              now eauto.
        + rewrite! setPermBlock_other_2; eauto.
          erewrite @gsoThreadRes with (cntj := cntx) by eauto.
          destruct (no_race_thr0 _ _ cnti cntx ltac:(auto));
            now eauto.
      }
      destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
      - subst tp' k. Tactics.pf_cleanup.
        eapply Hdisjoint_i';
          now eauto.
      - destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        + subst.
          Tactics.pf_cleanup.
          destruct (Hdisjoint_i' k cntk'); eauto.
          split; apply permMapsDisjoint_comm;
            eauto using permMapsDisjoint_comm.
        + subst tp'.
          pose proof (cntUpdate' _ _ _ cntj') as cntj.
          pose proof (cntUpdate' _ _ _ cntk') as cntk.
          erewrite @gsoThreadRes with (cntj := cntk) by eauto.
          erewrite @gsoThreadRes with (cntj := cntj) by eauto.
          now eauto.
    }
    { intros.
      subst tp'.
      erewrite gsoThreadLPool in Hres1, Hres2.
      now eauto.
    }
    { intros.
      subst tp'.
      erewrite gsoThreadLPool in Hres.
      destruct (i == i0) eqn:Heq; move/eqP:Heq=>Heq.
      - subst.
        unfold permMapsDisjoint2, permMapsDisjoint.
        erewrite <- forall2_and.
        intros b' ofs'.
        erewrite gssThreadRes.
        destruct (Pos.eq_dec b b').
        + subst.
          destruct (Intv.In_dec ofs' (ofs, ofs + Z.of_nat (lksize.LKSIZE_nat))%Z).
          * rewrite! setPermBlock_same; auto.
            split.
            specialize (Hperm_res1 _ _ Hres  ofs' i).
            simpl in Hperm_res1.
            destruct (rmap.1 # b' ofs'); inversion Hperm_res1; subst;
              simpl; now eauto.
            specialize (Hperm_res2 _ _ Hres ofs' i).
            rewrite Hperm_res2.
            rewrite perm_union_comm;
              eapply not_racy_union;
              now constructor.
          * apply Intv.range_notin in n;
              try (simpl; eapply Z.lt_add_pos_r; now apply lksize.LKSIZE_pos).
            rewrite! setPermBlock_other_1; eauto.
            destruct (no_race0 _ _ cnti _ Hres);
              now eauto.
        + rewrite! setPermBlock_other_2; eauto.
          destruct (no_race0 _ _ cnti _ Hres);
            now eauto.
      - pose proof (cntUpdate' _ _ _ cnti0) as cnti00.
        erewrite gsoThreadRes with (cntj := cnti00) by eauto.
        eauto.
    }
    { intros k cntk'.
      split.
      { intros j cntj'.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        - subst.
          intros b' ofs'.
          rewrite gssThreadRes.
          destruct (j == k) eqn:Hjk; move/eqP:Hjk=>Hjk.
          { subst.
            rewrite gssThreadRes.
            destruct (Pos.eq_dec b b').
            - subst.
              destruct (Intv.In_dec ofs' (ofs, ofs + Z.of_nat (lksize.LKSIZE_nat))%Z).
              + rewrite! setPermBlock_same; auto.

                simpl; auto.
              + apply Intv.range_notin in n;
                  try (simpl; eapply Z.lt_add_pos_r; now apply lksize.LKSIZE_pos).
                rewrite! setPermBlock_other_1; eauto.
                specialize ((thread_data_lock_coh0 _ cnti).1 _ cnti b' ofs');
                  now eauto.
            - rewrite! setPermBlock_other_2; eauto.
              specialize ((thread_data_lock_coh0 _ cnti).1 _ cnti b' ofs');
                now eauto.
          }
          { subst tp'.
            pose proof (cntUpdate' _ _ _ cntk') as cntk.
            erewrite gsoThreadRes with (cntj := cntk) by eauto.
            destruct (Pos.eq_dec b b').
            - subst.
              destruct (Intv.In_dec ofs' (ofs, ofs + Z.of_nat (lksize.LKSIZE_nat))%Z).
              + rewrite! setPermBlock_same; auto.
                simpl.
                pose proof ((invariant_not_freeable Hinv b' ofs').1 _ cntk).
                destruct ((getThreadR cntk).2 # b' ofs') as [p|];
                  try (destruct p); simpl; auto.
              + apply Intv.range_notin in n;
                  try (simpl; eapply Z.lt_add_pos_r; now apply lksize.LKSIZE_pos).
                rewrite! setPermBlock_other_1; eauto.
                specialize ((thread_data_lock_coh0 _ cntk).1 _ cnti b' ofs');
                  now eauto.
            - rewrite! setPermBlock_other_2; eauto.
              specialize ((thread_data_lock_coh0 _ cntk).1 _ cnti b' ofs');
                now eauto.
          }
        - subst tp'.
          pose proof (cntUpdate' _ _ _ cntj') as cntj.
          erewrite @gsoThreadRes with (cntj := cntj) by eauto.
          intros b' ofs'.
          destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
          + subst.
            rewrite gssThreadRes.
            destruct (Pos.eq_dec b b').
            * subst.
              destruct (Intv.In_dec ofs' (ofs, ofs + Z.of_nat (lksize.LKSIZE_nat))%Z).
              rewrite! setPermBlock_same; auto.
              specialize (Hperm_thr1 _ cntj Hij ofs' i).
              simpl in Hperm_thr1.
              destruct ((getThreadR cntj).1 # b' ofs'); simpl; auto;
                inversion Hperm_thr1; subst;
                  now auto.
              apply Intv.range_notin in n;
                try (simpl; eapply Z.lt_add_pos_r; now apply lksize.LKSIZE_pos).
              rewrite! setPermBlock_other_1; eauto.
              specialize ((thread_data_lock_coh0 _ cnti).1 _ cntj b' ofs');
                now eauto.
            * rewrite! setPermBlock_other_2; eauto.
              specialize ((thread_data_lock_coh0 _ cnti).1 _ cntj b' ofs');
                now eauto.
          + pose proof (cntUpdate' _ _ _ cntk') as cntk.
            rewrite gsoThreadRes; eauto.
            now eapply ((thread_data_lock_coh0 _ cntk).1 _ cntj b' ofs').
      }
      { intros laddr rmap Hres.
        subst tp'.
        rewrite gsoThreadLPool in Hres.
        intros b' ofs'.
        destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik; subst.
        - rewrite gssThreadRes.
          destruct (Pos.eq_dec b b').
          + subst.
            destruct (Intv.In_dec ofs' (ofs, ofs + Z.of_nat (lksize.LKSIZE_nat))%Z).
            * rewrite! setPermBlock_same; auto.
              specialize (Hperm_res1 _ _ Hres ofs' i).
              simpl in Hperm_res1.
              destruct (rmap.1 # b' ofs'); simpl; auto;
                inversion Hperm_res1; subst;
                  now auto.
            * apply Intv.range_notin in n;
                try (simpl; eapply Z.lt_add_pos_r; now apply lksize.LKSIZE_pos).
              rewrite! setPermBlock_other_1; eauto.
              specialize ((thread_data_lock_coh0 _ cnti).2 _ _ Hres b' ofs');
                now eauto.
          + rewrite! setPermBlock_other_2; eauto.
            specialize ((thread_data_lock_coh0 _ cnti).2 _ _ Hres b' ofs');
              now eauto.
        - pose proof (cntUpdate' _ _ _ cntk') as cntk.
          erewrite gsoThreadRes with (cntj := cntk) by eauto.
          now eapply ((thread_data_lock_coh0 _ cntk).2 _ _ Hres b' ofs').
      }
    }
    { intros laddr rmap Hres.
      subst tp'.
      rewrite gsoThreadLPool in Hres.
      split.
      - intros j cntj'.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
        + rewrite gssThreadRes.
          intros b' ofs'.
          destruct (Pos.eq_dec b b').
          * subst.
            destruct (Intv.In_dec ofs' (ofs, ofs + Z.of_nat (lksize.LKSIZE_nat))%Z).
            rewrite! setPermBlock_same; auto.
            pose proof ((invariant_not_freeable Hinv b' ofs').2 _ _ Hres).
            simpl;
              destruct (rmap.2 # b' ofs') as [p|];
              try (destruct p);
              by auto.
            apply Intv.range_notin in n;
              try (simpl; eapply Z.lt_add_pos_r; now apply lksize.LKSIZE_pos).
            rewrite! setPermBlock_other_1; eauto.
            specialize ((locks_data_lock_coh0 _ _ Hres).1 _ cnti b' ofs');
              now eauto.
          * rewrite! setPermBlock_other_2; eauto.
            specialize ((locks_data_lock_coh0 _ _ Hres).1 _ cnti b' ofs');
              now eauto.
        + pose proof (cntUpdate' _ _ _ cntj') as cntj.
          erewrite @gsoThreadRes with (cntj := cntj) by eauto.
          now eapply ((locks_data_lock_coh0 _ _ Hres).1 _ cntj).
      - intros laddr' rmap' Hres'.
        rewrite gsoThreadLPool in Hres'.
        eapply locks_data_lock_coh0;
          by eauto.
    }
    { subst tp'.
      intros b' ofs'.
      rewrite gsoThreadLPool.
      destruct (lockRes tp (b', ofs')) eqn:Hres; auto.
      specialize (lockRes_valid0 b' ofs').
      rewrite Hres in lockRes_valid0.
      intros.
      rewrite gsoThreadLPool.
      now eauto.
    }
  Qed.

  Lemma invariant_spawn:
    forall (tpc tpf : thread_pool) (mc mf : mem) f
      i (pff : containsThread tpf i) (pfc : containsThread tpc i)
      (HmemCompC : mem_compatible tpc mc)
      (HmemCompF : mem_compatible tpf mf)
      virtue1 virtue2  c cf vf vff arg arg',
      let threadPerm' := (computeMap (getThreadR pfc).1 virtue1.1,
                          computeMap (getThreadR pfc).2 virtue1.2) in
      let threadPermF' := (computeMap (getThreadR pff).1 (projectAngel f virtue1.1),
                           computeMap (getThreadR pff).2 (projectAngel f virtue1.2)) in
      let newThreadPerm := (computeMap empty_map virtue2#1, computeMap empty_map virtue2#2) in
      let newThreadPermF := (computeMap empty_map (projectAngel f virtue2#1),
                             computeMap empty_map (projectAngel f virtue2#2)) in
      forall
        (HinvF: invariant tpf)
        (HinvC': invariant
                   (addThread
                      (updThread pfc c threadPerm') vf arg newThreadPerm))
        (HsimWeak: forall tid (pfc0 : containsThread tpc tid)
                     (pff0 : containsThread tpf tid),
            weak_tsim f pfc0 pff0 HmemCompC HmemCompF)
        (Htsim_data: mem_obs_eq f (restrPermMap (compat_th _ _ HmemCompC pfc).1)
                                (restrPermMap (compat_th _ _ HmemCompF pff).1))
        (Htsim_locks: mem_obs_eq f (restrPermMap (compat_th _ _ HmemCompC pfc).2)
                                 (restrPermMap (compat_th _ _ HmemCompF pff).2))
        (HnumThreads: forall i, containsThread tpc i <-> containsThread tpf i)
        (Hlock_mapped: forall (bl2 : block) (ofs : Z),
            lockRes tpf (bl2, ofs) ->
            exists bl1 : block, f bl1 = Some bl2)
        (HsimRes:
           forall (bl1 bl2 : block) (ofs : Z)
             rmap1 rmap2,
             f bl1 = Some bl2 ->
             forall (Hl1 : lockRes tpc (bl1, ofs) = Some rmap1)
               (Hl2 : lockRes tpf (bl2, ofs) = Some rmap2),
               strong_mem_obs_eq f
                                 (restrPermMap (compat_lp _ _ HmemCompC (bl1, ofs) _ Hl1).1)
                                 (restrPermMap (compat_lp _ _ HmemCompF (bl2, ofs) _ Hl2).1) /\
               strong_mem_obs_eq f
                                 (restrPermMap (compat_lp _ _ HmemCompC (bl1, ofs) _ Hl1).2)
                                 (restrPermMap (compat_lp _ _ HmemCompF (bl2, ofs) _ Hl2).2))
        (Hunmapped_res: forall (bl : block) (ofsl : Z) rmap,
            lockRes tpf (bl, ofsl) = Some rmap ->
            forall b2 : block,
              ~ (exists b1 : block, f b1 = Some b2) ->
              forall ofs : Z,
                (rmap#1) # b2 ofs = None /\ (rmap#2) # b2 ofs = None)
        (Hlock_if: forall (bl1 bl2 : block) (ofs : Z),
            f bl1 = Some bl2 ->
            lockRes tpc (bl1, ofs) <-> lockRes tpf (bl2, ofs)),
        invariant
          (addThread
             (updThread pff cf threadPermF') vff arg'
             newThreadPermF).
  Proof.
    intros.
    pose proof (injective (weak_obs_eq Htsim_data)) as Hinjective.
    assert (Hnum: OrdinalPool.num_threads tpc = OrdinalPool.num_threads tpf)
      by (eapply OrdinalPool.contains_iff_num; eauto).
    Transparent containsThread OrdinalPool.containsThread.
    assert (Hthreads: forall k, containsThread (addThread (updThread pff cf threadPermF')
                                                     vff arg' newThreadPermF) k <->
                           containsThread (addThread (updThread pfc c threadPerm') vf arg newThreadPerm) k)
      by (intros j;
          split;
            intros cntj;
            apply cntAdd' in cntj;
            destruct cntj as [[cntj _] | Heq];
            try (apply cntAdd;
                  apply cntUpdate;
                  apply HnumThreads;
                    by apply cntUpdate' in cntj);
            try (unfold containsThread;
                 subst; simpl; unfold OrdinalPool.containsThread;
                 unfold OrdinalPool.latestThread, OrdinalPool.updThread;
                 simpl; rewrite Hnum;
                   by ssromega)).
    Opaque containsThread OrdinalPool.containsThread.
    assert (Hthread_mapped:
              forall k (pfck': containsThread (addThread (updThread pfc c threadPerm') vf arg newThreadPerm) k)
                (pffk': containsThread (addThread (updThread pff cf threadPermF') vff arg' newThreadPermF) k),
              forall b1 b2 ofs,
                f b1 = Some b2 ->
                Mem.perm_order'' ((getThreadR pfck').1 # b1 ofs) ((getThreadR pffk').1 # b2 ofs) /\
                Mem.perm_order'' ((getThreadR pfck').2 # b1 ofs) ((getThreadR pffk').2 # b2 ofs)).
    { intros.
      assert (Hcnt := cntAdd' _ _ _ pffk').
      destruct Hcnt as [[pffk Hneqk] | Hk].
      - erewrite gsoAddRes with (cntj := pffk); eauto.
        assert (pfck: containsThread (updThread pfc c threadPerm') k)
          by (eapply cntUpdate; eauto; eapply HnumThreads; eauto).
        erewrite gsoAddRes with (cntj := pfck).
        destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
        + subst.
          rewrite! gssThreadRes.
          simpl.
          erewrite! computeMap_projection_1 by eauto.
          split; now apply po_refl.
        + rewrite! gsoThreadRes; auto.
          destruct (HsimWeak _ pfck pffk).
          destruct weak_tsim_data0.
          specialize (perm_obs_weak0 _ _ ofs H).
          rewrite! restrPermMap_Cur in perm_obs_weak0.
          destruct weak_tsim_locks0.
          specialize (perm_obs_weak1 _ _ ofs H).
          rewrite! restrPermMap_Cur in perm_obs_weak1;
            by eauto.
      - subst.
        erewrite gssAddRes by
            (unfold latestThread; simpl; unfold OrdinalPool.latestThread, OrdinalPool.updThread; simpl; by rewrite Hnum).
        erewrite gssAddRes by
            reflexivity.
        simpl.
        erewrite! computeMap_projection_3 by eauto;
          split;
          now apply po_refl.
    }
    assert (Hthread_unmapped:
              forall k
                (pffk': containsThread (addThread (updThread pff cf threadPermF') vff arg' newThreadPermF) k),
               forall b2 ofs,
                 (~exists b1, f b1 = Some b2) ->
                 (exists (pffk: containsThread tpf k),
                  ((getThreadR pffk').1 # b2 ofs = (getThreadR pffk).1 # b2 ofs) /\
                  ((getThreadR pffk').2 # b2 ofs = (getThreadR pffk).2 # b2 ofs)) \/
                 ((getThreadR pffk').1 # b2 ofs = None /\ (getThreadR pffk').2 # b2 ofs = None)).
    { intros k pffk' b0 ofs0 Hunmmaped.
      assert (Hcnt := cntAdd' _ _ _ pffk').
      destruct Hcnt as [[pffk Hneqk] | Hk].
      - erewrite gsoAddRes with (cntj := pffk); eauto.
        destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
        + subst.
          rewrite! gssThreadRes.
          simpl.
          Tactics.pf_cleanup.
          left. exists pff.
          erewrite! computeMap_projection_2 by eauto.
          split;
            reflexivity.
        + left.
          exists pffk.
          rewrite! gsoThreadRes;
            by auto.
      - subst.
        right.
        erewrite gssAddRes
          by (unfold latestThread; reflexivity).
        simpl.
        erewrite! computeMap_projection_2 by eauto.
        split;
          now apply empty_map_spec.
    }
    destruct HinvC'.
    assert (Hlocks: forall laddrF rmapF (HresF: lockRes tpf laddrF = Some rmapF),
               exists bc rmap,
                 lockRes tpc (bc, laddrF.2) = Some rmap /\ f bc = Some laddrF.1 /\
                 forall b1 b2 ofs,
                   f b1 = Some b2 ->
                   Mem.perm_order'' (rmap.1 # b1 ofs) (rmapF.1 # b2 ofs) /\
                   Mem.perm_order'' (rmap.2 # b1 ofs) (rmapF.2 # b2 ofs)).
    { intros.
      destruct laddrF as [bl ofsl].
      specialize (Hlock_mapped bl ofsl).
      unfold isSome in Hlock_mapped.
      rewrite HresF in Hlock_mapped.
      specialize (Hlock_mapped (Logic.eq_refl _)).
      destruct Hlock_mapped as [bl1 Hfbl1].
      specialize (Hlock_if _ _ ofsl Hfbl1).
      destruct (lockRes tpc (bl1, ofsl)) as [rmapC |] eqn:Hres.
      + exists bl1, rmapC.
        split; auto. split; auto.
        intros b0 b3 ofs0 Hrenaming.
        specialize (HsimRes _ _ _ _ _ Hfbl1 Hres HresF).
        destruct HsimRes as [[Hperm1 _] [Hperm2 _]].
        specialize (Hperm1 _ _ ofs0 Hrenaming).
        specialize (Hperm2 _ _ ofs0 Hrenaming).
        rewrite! restrPermMap_Cur in Hperm1 Hperm2.
        rewrite Hperm1 Hperm2.
        split; now apply po_refl.
      + exfalso. erewrite HresF in Hlock_if.
        simpl in Hlock_if.
        destruct Hlock_if; now auto.
    }

    constructor.
    { (** no_race *)
      intros.
      unfold permMapsDisjoint2, permMapsDisjoint.
      erewrite <- forall2_and.
      intros b2 ofs.
      assert (Hb2: (exists b1, f b1 = Some b2) \/
                   ~ (exists b1, f b1 = Some b2))
        by eapply em.
      destruct Hb2 as [[b1 Hf] | Hunmapped].
      - pose proof ((Hthreads i0).1 cnti) as pfci0.
        pose proof ((Hthreads j).1 cntj) as pfcj0.
        specialize (no_race_thr0 _ _ pfci0 pfcj0 Hneq).
        unfold permMapsDisjoint2, permMapsDisjoint in no_race_thr0.
        erewrite <- forall2_and in no_race_thr0.
        destruct (no_race_thr0 b1 ofs).
        destruct (Hthread_mapped _ pfci0 cnti b1 b2 ofs Hf).
        destruct (Hthread_mapped _ pfcj0 cntj b1 b2 ofs Hf).
        split.
        eapply perm_union_lower_2
        with (p1 := ((getThreadR pfci0)#1) # b1 ofs); eauto.
        eapply perm_union_lower_2
        with (p1 := ((getThreadR pfci0)#2) # b1 ofs); eauto.
      - destruct (Hthread_unmapped i0 cnti b2 ofs Hunmapped) as [[pffi0 [Heq1 Heq2]]| [Heq1 Heq2]].
        + destruct (Hthread_unmapped j cntj b2 ofs Hunmapped) as [[pffj0 [Heq3 Heq4]]| [Heq3 Heq4]].
          rewrite Heq1 Heq2 Heq3 Heq4.
          pose proof (no_race_thr _ HinvF _ _ pffi0 pffj0 Hneq) as Hno_race.
          unfold permMapsDisjoint2, permMapsDisjoint in Hno_race.
          destruct Hno_race.
          now eauto.
          rewrite Heq3 Heq4.
          split;
            rewrite perm_union_comm;
            apply not_racy_union;
            now constructor.
        + rewrite Heq1 Heq2.
          split; apply not_racy_union;
          now constructor.
    }
    { (** disjointness between lock resources*)
      intros.
      erewrite gsoAddLPool, gsoThreadLPool in Hres1, Hres2.
      eapply HinvF;
        by eauto.
    }
    { intros.
      rewrite gsoAddLPool gsoThreadLPool in Hres.
      unfold permMapsDisjoint2, permMapsDisjoint.
      erewrite <- forall2_and. intros b2 ofs.
      assert (Hb2: (exists b1, f b1 = Some b2) \/
                   ~ (exists b1, f b1 = Some b2))
        by eapply em.
      destruct Hb2 as [[b1 Hf] | Hunmapped].
      - destruct (Hlocks _ _ Hres) as [bc [rmapC [HresC [Hfl Hperm]]]].
        destruct (Hperm _ _ ofs Hf).
        pose proof ((Hthreads i0).1 cnti) as pfci0.
        destruct (Hthread_mapped _ pfci0 cnti _ _ ofs Hf).
        pose proof (no_race0 _ _ pfci0 _ HresC) as Hno_race.
        unfold permMapsDisjoint2, permMapsDisjoint in Hno_race.
        erewrite <- forall2_and in Hno_race.
        destruct (Hno_race b1 ofs).
        split.
        eapply perm_union_lower_2 with (p1 := (getThreadR pfci0).1 # b1 ofs); eauto.
        eapply perm_union_lower_2 with (p1 := (getThreadR pfci0).2 # b1 ofs); eauto.
      - destruct laddr.
        rewrite (Hunmapped_res _ _ _ Hres _ Hunmapped ofs).1.
        rewrite (Hunmapped_res _ _ _ Hres _ Hunmapped ofs).2.
        split; rewrite perm_union_comm; eapply not_racy_union;
        now constructor.
    }
    { (** thread locks coherence *)
      intros.
      split.
      - intros.
        intros b2 ofs.
        assert (Hb2: (exists b1, f b1 = Some b2) \/
                     ~ (exists b1, f b1 = Some b2))
          by eapply em.
        destruct Hb2 as [[b1 Hf] | Hunmapped].
        + pose proof ((Hthreads i0).1 cnti) as pfci0.
          pose proof ((Hthreads j).1 cntj) as pfcj0.
          destruct (Hthread_mapped _ pfci0 cnti _ _ ofs Hf).
          destruct (Hthread_mapped _ pfcj0 cntj _ _ ofs Hf).
          pose proof ((thread_data_lock_coh0 _ pfci0).1 _ pfcj0 b1 ofs).
          eapply perm_coh_lower; eauto.
        + destruct (Hthread_unmapped i0 cnti b2 ofs Hunmapped) as [[pffi0 [Heq1 Heq2]]| [Heq1 Heq2]].
          * destruct (Hthread_unmapped j cntj b2 ofs Hunmapped)
              as [[pffj0 [Heq3 Heq4]]| [Heq3 Heq4]].
            rewrite Heq2 Heq3.
            pose proof ((thread_data_lock_coh _ HinvF _ pffi0).1 _ pffj0) as Hno_race.
            now eauto.
            rewrite Heq2 Heq3.
            pose proof ((invariant_not_freeable HinvF b2 ofs).1 _ pffi0).
            simpl.
            destruct ((getThreadR pffi0).2 # b2 ofs) as [p|];
              try (destruct p); auto.
          * rewrite Heq2.
            now apply perm_coh_empty_1.
      - intros.
        intros b2 ofs.
        rewrite gsoAddLPool gsoThreadLPool in H.
        assert (Hb2: (exists b1, f b1 = Some b2) \/
                     ~ (exists b1, f b1 = Some b2))
          by eapply em.
        destruct Hb2 as [[b1 Hf] | Hunmapped].
        + pose proof ((Hthreads i0).1 cnti) as pfci0.
          destruct (Hthread_mapped _ pfci0 cnti _ _ ofs Hf).
          destruct (Hlocks _ _ H) as [bc [rmapC [HresC [Hfl Hperm]]]].
          destruct (Hperm _ _ ofs Hf).
          pose proof ((thread_data_lock_coh0 _ pfci0).2 _ _ HresC b1 ofs) as Hno_race.
          eapply perm_coh_lower; eauto.
        + destruct laddr.
          rewrite (Hunmapped_res _ _ _ H _ Hunmapped ofs).1.
          destruct (Hthread_unmapped i0 cnti b2 ofs Hunmapped) as [[pffi0 [Heq1 Heq2]]
                                                                  | [Heq1 Heq2]].
          * rewrite Heq2.
            pose proof ((invariant_not_freeable HinvF b2 ofs).1 _ pffi0).
            destruct ((getThreadR pffi0).2 # b2 ofs) as [p|];
              try (destruct p); by auto.
          * rewrite Heq2.
            now apply perm_coh_empty_1.
    }
    { (** lock resourecs locks coherence*)
      intros.
      rewrite gsoAddLPool gsoThreadLPool in Hres.
      split.
      - intros j cntj b2 ofs.
        pose proof ((Hthreads j).1 cntj) as pfcj0.
        assert (Hb2: (exists b1, f b1 = Some b2) \/
                     ~ (exists b1, f b1 = Some b2))
          by eapply em.
        destruct Hb2 as [[b1 Hf] | Hunmapped].
        + destruct (Hthread_mapped _ pfcj0 cntj _ _ ofs Hf).
          destruct (Hlocks _ _ Hres) as [bc [rmapC [HresC [Hfl Hperm]]]].
          destruct (Hperm _ _ ofs Hf).
          pose proof ((locks_data_lock_coh0 _ _ HresC).1 _ pfcj0 b1 ofs).
          eapply perm_coh_lower; eauto.
        + destruct laddr.
          rewrite (Hunmapped_res _ _ _ Hres _ Hunmapped ofs).2.
          now apply perm_coh_empty_1.
      - intros laddr' rmap' Hres'.
        rewrite gsoAddLPool gsoThreadLPool in Hres'.
        eapply HinvF; eauto.
    }
    { (** lockRes valid*)
      intros b ofs.
      rewrite gsoAddLPool gsoThreadLPool.
      pose proof (lockRes_valid _ HinvF).
      specialize (H b ofs).
      now eauto.
    }
  Qed.

  Lemma invariant_freelock:
    forall tpc tpf mc mf f c cf b1 b2 ofs pdata i
      (Hf: f b1 = Some b2)
      (pfc: containsThread tpc i)
      (pff: containsThread tpf i),
      let tpc' := remLockSet
                    (updThread pfc c
                               (setPermBlock_var pdata b1 ofs (getThreadR pfc)#1 lksize.LKSIZE_nat,
                                setPermBlock None b1 ofs
                                             (getThreadR pfc)#2 lksize.LKSIZE_nat)) (b1,ofs) in
      let tpf' := remLockSet (updThread pff cf
                                        (setPermBlock_var pdata b2 ofs (getThreadR pff)#1 lksize.LKSIZE_nat,
                                         setPermBlock None b2 ofs
                                                      (getThreadR pff)#2 lksize.LKSIZE_nat)) (b2, ofs) in
      forall
        (HinvF: invariant tpf)
        (HinvC': invariant tpc')
        (HmemCompC: mem_compatible tpc mc)
        (HmemCompF: mem_compatible tpf mf)
        (HsimWeak: forall tid (pfc0 : containsThread tpc tid)
                     (pff0 : containsThread tpf tid),
            weak_tsim f pfc0 pff0 HmemCompC HmemCompF)
        (Htsim: mem_obs_eq f (restrPermMap (compat_th _ _ HmemCompC pfc).1)
                           (restrPermMap (compat_th _ _ HmemCompF pff).1))
        (HtsimL: mem_obs_eq f (restrPermMap (compat_th _ _ HmemCompC pfc).2)
                            (restrPermMap (compat_th _ _ HmemCompF pff).2))
        (Hneq_perms: forall i,
            (0 <= Z.of_nat i < lksize.LKSIZE)%Z ->
            Mem.perm_order'' (pdata (S i)) (Some Writable)
        )
        (Hlocks: forall (bl2 : block) (ofs : Z),
            lockRes tpf (bl2, ofs) ->
            exists bl1 : block, f bl1 = Some bl2)
        (HsimRes:
           forall (bl1 bl2 : block) (ofs : Z)
             rmap1 rmap2,
             f bl1 = Some bl2 ->
             forall (Hl1 : lockRes tpc (bl1, ofs) = Some rmap1)
               (Hl2 : lockRes tpf (bl2, ofs) = Some rmap2),
               strong_mem_obs_eq f
                                 (restrPermMap (compat_lp _ _ HmemCompC (bl1, ofs) _ Hl1).1)
                                 (restrPermMap (compat_lp _ _ HmemCompF (bl2, ofs) _ Hl2).1) /\
               strong_mem_obs_eq f
                                 (restrPermMap (compat_lp _ _ HmemCompC (bl1, ofs) _ Hl1).2)
                                 (restrPermMap (compat_lp _ _ HmemCompF (bl2, ofs) _ Hl2).2))
        (Hlock_if: forall (bl1 bl2 : block) (ofs : Z),
            f bl1 = Some bl2 ->
            lockRes tpc (bl1, ofs) <-> lockRes tpf (bl2, ofs))
        (HnumThreads: forall i, containsThread tpc i <-> containsThread tpf i),
        invariant tpf'.
  Proof.
    intros.
    assert (HnumThreads': forall i, containsThread tpc' i <-> containsThread tpf' i)
      by (intros; subst tpc' tpf'; split; intros Hcnt; apply cntRemoveL;
          apply cntUpdate;
          apply cntRemoveL' in Hcnt;
          apply cntUpdate' in Hcnt; apply HnumThreads; now auto).
    assert (Hthread_mapped: forall k (pfck': containsThread tpc' k) (pffk': containsThread tpf' k),
               forall b1 b2 ofs,
                 f b1 = Some b2 ->
                 Mem.perm_order'' ((getThreadR pfck').1 # b1 ofs) ((getThreadR pffk').1 # b2 ofs) /\
                 Mem.perm_order'' ((getThreadR pfck').2 # b1 ofs) ((getThreadR pffk').2 # b2 ofs)).
    { intros.
      destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik; subst.
      - rewrite! gRemLockSetRes.
        rewrite! gssThreadRes.
        destruct (HsimWeak _ pfc pff).
        destruct weak_tsim_data0.
        destruct weak_tsim_locks0.
        specialize (perm_obs_weak0 _ _ ofs0 H).
        specialize (perm_obs_weak1 _ _ ofs0 H).
        rewrite! restrPermMap_Cur in perm_obs_weak0.
        rewrite! restrPermMap_Cur in perm_obs_weak1.
        destruct (Pos.eq_dec b1 b0).
        + subst.
          assert (b2 = b3)
            by (rewrite Hf in H; inversion H; subst; auto); subst.
          destruct (Intv.In_dec ofs0 (ofs, ofs + Z.of_nat (lksize.LKSIZE_nat))%Z).
          * rewrite! setPermBlock_same; auto.
            rewrite! setPermBlock_var_same; auto.
            split; now apply po_refl.
          * apply Intv.range_notin in n;
              try (simpl; eapply Z.lt_add_pos_r; now apply lksize.LKSIZE_pos).
            rewrite! setPermBlock_other_1; auto.
            rewrite! setPermBlock_var_other_1; auto.
        + assert (b2 <> b3)
            by (intros Hcontra; subst;
                specialize (injective1 _ _ _ Hf H);
                auto).
          rewrite! setPermBlock_other_2; auto.
          rewrite! setPermBlock_var_other_2; now auto.
      - assert (pfck :=cntUpdate' _  _ _ (cntRemoveL' _ pfck')).
        subst tpf' tpc'.
        assert (pffk := cntUpdate' _ _ _ (cntRemoveL' _ pffk')).
        rewrite! gRemLockSetRes.
        erewrite! gsoThreadRes with (cntj := pfck) by eauto.
        erewrite! gsoThreadRes with (cntj := pffk) by eauto.
        destruct (HsimWeak _ pfck pffk).
        destruct weak_tsim_data0.
        destruct weak_tsim_locks0.
        specialize (perm_obs_weak0 _ _ ofs0 H).
        specialize (perm_obs_weak1 _ _ ofs0 H).
        rewrite! restrPermMap_Cur in perm_obs_weak0.
        rewrite! restrPermMap_Cur in perm_obs_weak1.
        split; now assumption.
    }
    assert (Hthread_unmapped: forall k (pffk: containsThread tpf k)(pffk': containsThread tpf' k),
               forall b2 ofs,
                 (~exists b1, f b1 = Some b2) ->
                 ((getThreadR pffk').1 # b2 ofs = (getThreadR pffk).1 # b2 ofs) /\
                 ((getThreadR pffk').2 # b2 ofs = (getThreadR pffk).2 # b2 ofs)).
    { intros k pffk pffk' b0 ofs0 Hunmmaped.
      rewrite gRemLockSetRes.
      destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik; subst.
      - rewrite! gssThreadRes.
        assert (b2 <> b0)
          by (intros Hcontra; subst; eauto).
        rewrite! setPermBlock_other_2; auto.
        rewrite! setPermBlock_var_other_2; auto.
        Tactics.pf_cleanup.
        split; reflexivity.
      - subst tpf'. erewrite! gsoThreadRes with (cntj := pffk) by eauto.
        split; reflexivity.
    }

    assert (Hlock_mapped: forall laddrF rmapF (HresF: lockRes tpf' laddrF = Some rmapF),
               exists bc rmap,
                 lockRes tpc' (bc, laddrF.2) = Some rmap /\ f bc = Some laddrF.1 /\
                 forall b1 b2 ofs,
                   f b1 = Some b2 ->
                   rmap.1 # b1 ofs = rmapF.1 # b2 ofs /\
                   rmap.2 # b1 ofs = rmapF.2 # b2 ofs).
    { intros.
      subst tpf' tpc'.
      destruct laddrF as [bl ofsl].
      destruct (EqDec_address (b2, ofs) (bl, ofsl)).
      - inversion e; subst.
        rewrite gsslockResRemLock in HresF.
        discriminate.
      - erewrite gsolockResRemLock in HresF by eauto.
        erewrite gsoThreadLPool in HresF.
        specialize (Hlocks bl ofsl).
        unfold isSome in Hlocks.
        rewrite HresF in Hlocks.
        specialize (Hlocks (Logic.eq_refl _)).
        destruct Hlocks as [bl1 Hfbl1].
        specialize (Hlock_if _ _ ofsl Hfbl1).
        destruct (lockRes tpc (bl1, ofsl)) as [rmapC |] eqn:Hres.
        + exists bl1, rmapC.
          assert ((b1, ofs) <> (bl1, ofsl))
            by (intros Hcontra; inversion Hcontra; subst;
                rewrite Hfbl1 in Hf; inversion Hf; subst; auto).
          erewrite gsolockResRemLock by eauto.
          erewrite gsoThreadLPool by eauto.
          split; auto. split; auto.
          intros b0 b3 ofs0 Hrenaming.
          specialize (HsimRes _ _ _ _ _ Hfbl1 Hres HresF).
          destruct HsimRes as [[Hperm1 _] [Hperm2 _]].
          specialize (Hperm1 _ _ ofs0 Hrenaming).
          specialize (Hperm2 _ _ ofs0 Hrenaming).
          rewrite! restrPermMap_Cur in Hperm1 Hperm2.
          rewrite Hperm1 Hperm2.
          split; reflexivity.
        + exfalso. erewrite HresF in Hlock_if.
          simpl in Hlock_if.
          destruct Hlock_if; now auto.
    }

    assert (Hlock_eq: forall laddrF rmapF (HresF: lockRes tpf' laddrF = Some rmapF),
               lockRes tpf laddrF = Some rmapF).
    { intros (bl & ofsl) rmapF HresF'.
      subst tpf'.
      destruct (EqDec_address (b2, ofs) (bl, ofsl)).
      inversion e; subst. rewrite gsslockResRemLock in HresF'.
      discriminate.
      erewrite gsolockResRemLock in HresF' by eauto.
      erewrite gsoThreadLPool in HresF'.
      assumption.
    }
    constructor.
    { (** disjointness between threads *)
      (** no race for coarse-grained state*)
      assert (Hno_raceC:= no_race_thr _ HinvC').
      assert (Hno_raceF:= no_race_thr _ HinvF).
      intros k j pffk' pffj' Hkj.
      unfold permMapsDisjoint2, permMapsDisjoint.
      erewrite <- forall2_and.
      intros bf ofs0.
      assert (Hbf: (exists b1, f b1 = Some bf) \/
                   ~ (exists b1, f b1 = Some bf))
        by eapply em.
      destruct Hbf as [[b Hbfm] | Hbfu].
      - assert (pfck': containsThread tpc' k)
          by (apply HnumThreads' in pffk'; auto).
        assert (pfcj': containsThread tpc' j)
          by (apply HnumThreads' in pffj'; auto).
        specialize (Hno_raceC _ _ pfck' pfcj' Hkj).
        unfold permMapsDisjoint2, permMapsDisjoint in Hno_raceC.
        erewrite <- forall2_and in Hno_raceC.
        destruct (Hno_raceC b ofs0) as [HpermD HpermL].
        pose proof (Hthread_mapped _ pfck' pffk' b bf ofs0 Hbfm) as Hk.
        destruct Hk as [HkD HkL].
        pose proof (Hthread_mapped _ pfcj' pffj' b bf ofs0 Hbfm) as Hj.
        destruct Hj as [HjD HjL].
        split;
          eapply perm_union_lower; eauto;
            rewrite perm_union_comm;
            eapply perm_union_lower; eauto;
              rewrite perm_union_comm; eauto.
      - assert (pffk: containsThread tpf k)
          by (apply cntRemoveL' in pffk';
              apply cntUpdate' in pffk'; auto).
        assert (pffj: containsThread tpf j)
          by (apply cntRemoveL' in pffj';
              apply cntUpdate' in pffj'; auto).
        erewrite (Hthread_unmapped _ pffk pffk' bf ofs0 Hbfu).1.
        erewrite (Hthread_unmapped _ pffk pffk' bf ofs0 Hbfu).2.
        erewrite (Hthread_unmapped _ pffj pffj' bf ofs0 Hbfu).1.
        erewrite (Hthread_unmapped _ pffj pffj' bf ofs0 Hbfu).2.
        specialize (Hno_raceF _ _ pffk pffj Hkj).
        unfold permMapsDisjoint2, permMapsDisjoint in Hno_raceF.
        erewrite <- forall2_and in Hno_raceF.
        now eauto.
    }
    { (** disjointness between lock resources*)
      intros laddr1 laddr2 rmap0 rmap2 Hneq Hres0 Hres2.
      unfold permMapsDisjoint2, permMapsDisjoint.
      erewrite <- forall2_and.
      intros bf ofs0.
      assert (Hbf: (exists b1, f b1 = Some bf) \/
                   ~ (exists b1, f b1 = Some bf))
        by eapply em.
      destruct Hbf as [[b Hbfm] | Hbfu].
      - destruct (Hlock_mapped _ _ Hres0) as [bc1 [rmap0C [HresC [Hfl1 Hperm0]]]].
        destruct (Hperm0 _ _ ofs0 Hbfm) as [H1 H2].
        destruct (Hlock_mapped _ _ Hres2) as [bc2 [rmap2C [Hres2C [Hfl2 Hperm2]]]].
        destruct (Hperm2 _ _ ofs0 Hbfm) as [H3 H4].
        assert (HneqC: (bc1, laddr1.2) <> (bc2, laddr2.2)) by
            (intros Hcontra;
             inversion Hcontra; subst;
             rewrite Hfl1 in Hfl2; inversion Hfl2;
             destruct laddr1, laddr2; simpl in *; subst;
             now auto).
        pose proof (no_race_lr _ HinvC' _ _ _ _ HneqC HresC Hres2C) as Hdisjoint.
        unfold permMapsDisjoint2, permMapsDisjoint in Hdisjoint.
        erewrite <- forall2_and in Hdisjoint.
        rewrite <- H1, <- H2, <- H3, <- H4.
        destruct (Hdisjoint b ofs0).
        now auto.
      - subst tpf'.
        pose proof (Hlock_eq _ _ Hres0) as Heq0.
        pose proof (Hlock_eq _ _ Hres2) as Heq2.
        pose proof (no_race_lr _ HinvF  _ _ _ _ Hneq Heq0 Heq2) as Hdisjoint.
        unfold permMapsDisjoint2, permMapsDisjoint in Hdisjoint.
        erewrite <- forall2_and in Hdisjoint.
        now eauto.
    }
    { (**disjointness between lock resources and threads*)
      intros k laddrF pffk' rmapF HresF.
      unfold permMapsDisjoint2, permMapsDisjoint.
      erewrite <- forall2_and.
      intros b0 ofs0.
      assert (Hbf: (exists b1, f b1 = Some b0) \/
                   ~ (exists b1, f b1 = Some b0))
        by eapply em.
      destruct Hbf as [[b Hbfm] | Hbfu].
      - assert (pfck': containsThread tpc' k)
          by (apply HnumThreads' in pffk'; auto).
        destruct (Hlock_mapped _ _ HresF) as [bc [rmapC [HresC [Hfl HpermC]]]].
        destruct (HpermC _ _ ofs0 Hbfm).
        pose proof (Hthread_mapped _ pfck' pffk' b b0 ofs0 Hbfm) as Hk.
        destruct Hk as [HkD HkL].
        pose proof (no_race _ HinvC' _ _ pfck' _ HresC).
        unfold permMapsDisjoint2, permMapsDisjoint in H1.
        erewrite <- forall2_and in H1.
        destruct (H1 b ofs0).
        rewrite <- H, <- H0.
        split.
        eapply perm_union_lower_2 with (p1 := (getThreadR pfck').1 # b ofs0); eauto using po_refl.
        eapply perm_union_lower_2 with (p1 := (getThreadR pfck').2 # b ofs0); eauto using po_refl.
      - assert (pffk: containsThread tpf k)
          by (apply cntRemoveL' in pffk';
              apply cntUpdate' in pffk'; auto).
        erewrite (Hthread_unmapped _ pffk pffk' b0 ofs0 Hbfu).1.
        erewrite (Hthread_unmapped _ pffk pffk' b0 ofs0 Hbfu).2.
        subst tpf'.
        pose proof (Hlock_eq _ _ HresF) as Heq0.
        pose proof ((no_race _ HinvF) _ _ pffk _ Heq0) as Hno_race.
        unfold permMapsDisjoint2, permMapsDisjoint in Hno_race.
        erewrite <- forall2_and in Hno_race.
        now eauto.
    }
    { (** coherence between lock resources data and thread locks*)
      intros k pffk'.
      split.
      - intros j pffj' b0 ofs0.
        assert (Hbf: (exists b1, f b1 = Some b0) \/
                     ~ (exists b1, f b1 = Some b0))
          by eapply em.
        destruct Hbf as [[b Hbfm] | Hbfu].
        + assert (pfck': containsThread tpc' k)
            by (apply HnumThreads' in pffk'; auto).
          assert (pfcj': containsThread tpc' j)
            by (apply HnumThreads' in pffj'; auto).
          pose proof (Hthread_mapped _ pfck' pffk' b b0 ofs0 Hbfm) as Hk.
          destruct Hk as [_ HkL].
          pose proof (Hthread_mapped _ pfcj' pffj' b b0 ofs0 Hbfm) as Hj.
          destruct Hj as [HjD].
          pose proof ((thread_data_lock_coh _ HinvC' _ pfck').1 _ pfcj' b ofs0).
          eapply perm_coh_lower;
            now eauto.
        + assert (pffj: containsThread tpf j)
            by (apply cntRemoveL' in pffj';
                apply cntUpdate' in pffj'; auto).
          erewrite (Hthread_unmapped _ pffj pffj' b0 ofs0 Hbfu).1.
          assert (pffk: containsThread tpf k)
            by (apply cntRemoveL' in pffk';
                apply cntUpdate' in pffk'; auto).
          erewrite (Hthread_unmapped _ pffk pffk' b0 ofs0 Hbfu).2.
          now eapply ((thread_data_lock_coh _ HinvF _ pffk).1 _ pffj b0 ofs0).
      - intros laddrF rmapF HresF b0 ofs0.
        assert (Hbf: (exists b1, f b1 = Some b0) \/
                     ~ (exists b1, f b1 = Some b0))
          by eapply em.
        destruct Hbf as [[b Hbfm] | Hbfu].
        + assert (pfck': containsThread tpc' k)
            by (apply HnumThreads' in pffk'; auto).
          pose proof (Hthread_mapped _ pfck' pffk' b b0 ofs0 Hbfm) as Hk.
          destruct Hk as [_ HkL].
          destruct (Hlock_mapped _ _ HresF) as [bc [rmapC [HresC [Hfl HpermC]]]].
          destruct (HpermC _ _ ofs0 Hbfm).
          pose proof ((thread_data_lock_coh _ HinvC' _ pfck').2 _ _ HresC b ofs0).
          rewrite <- H.
          eapply perm_coh_lower with (p2 := (getThreadR pfck').2 # b ofs0);
            now eauto using po_refl.
        + assert (pffk: containsThread tpf k)
            by (apply cntRemoveL' in pffk';
                apply cntUpdate' in pffk'; auto).
          erewrite (Hthread_unmapped _ pffk pffk' b0 ofs0 Hbfu).2.
          subst tpf'.
          pose proof (Hlock_eq _ _ HresF) as Heq0.
          pose proof ((thread_data_lock_coh _ HinvF _ pffk).2 _ _ Heq0 b0 ofs0) as Hno_race.
          now eauto.
    }
    { (** locks in lock resources are coherent with thread data*)
      intros laddrF rmapF HresF.
      split.
      - intros j pffj' b0 ofs0.
        assert (Hbf: (exists b1, f b1 = Some b0) \/
                     ~ (exists b1, f b1 = Some b0))
          by eapply em.
        destruct Hbf as [[b Hbfm] | Hbfu].
        + assert (pfcj': containsThread tpc' j)
            by (apply HnumThreads' in pffj'; auto).
          pose proof (Hthread_mapped _ pfcj' pffj' b b0 ofs0 Hbfm).1 as Hj.
          destruct (Hlock_mapped _ _ HresF) as [bc [rmapC [HresC [Hfl HpermC]]]].
          destruct (HpermC _ _ ofs0 Hbfm).
          pose proof ((locks_data_lock_coh _ HinvC' _ _ HresC).1 _ pfcj' b ofs0).
          rewrite <- H0.
          eapply perm_coh_lower;
            now eauto using po_refl.
        + assert (pffj: containsThread tpf j)
            by (apply cntRemoveL' in pffj';
                apply cntUpdate' in pffj'; auto).
          erewrite (Hthread_unmapped _ pffj pffj' b0 ofs0 Hbfu).1.
          subst tpf'.
          pose proof (Hlock_eq _ _ HresF) as Heq0.
          pose proof ((locks_data_lock_coh _ HinvF _ _ Heq0).1 _ pffj) as Hno_race.
          now eauto.
      - intros laddr2F' rmap2F' Hres2F' b0 ofs0.
        subst tpf'.
        assert (Hbf: (exists b1, f b1 = Some b0) \/
                     ~ (exists b1, f b1 = Some b0))
          by eapply em.
        destruct Hbf as [[b Hbfm] | Hbfu].
        + destruct (Hlock_mapped _ _ HresF) as [bc [rmapC [HresC [Hfl HpermC]]]].
          destruct (HpermC _ _ ofs0 Hbfm).
          destruct (Hlock_mapped _ _ Hres2F') as [bc2 [rmapC2 [HresC2 [Hfl2 HpermC2]]]].
          destruct (HpermC2 _ _ ofs0 Hbfm).
          pose proof ((locks_data_lock_coh _ HinvC' _ _ HresC).2 _ _ HresC2 b ofs0).
          rewrite <- H1, <- H0.
          assumption.
        + pose proof (Hlock_eq _ _ HresF) as Heq0.
          pose proof (Hlock_eq _ _ Hres2F') as Heq2.
          now apply ((locks_data_lock_coh _ HinvF _ _ Heq0).2 _ _ Heq2 b0 ofs0).
    }
    { subst tpc' tpf'.
      intros b' ofs'.
      destruct (EqDec_address (b2, ofs) (b', ofs')).
      - inversion e; subst.
        rewrite gsslockResRemLock. auto.
      - erewrite gsolockResRemLock by eauto.
        rewrite gsoThreadLPool.
        destruct (lockRes tpf (b', ofs')) eqn:Hres; auto.
        intros.
        pose proof (lockRes_valid _ HinvF) as Hvalid.
        specialize (Hvalid b' ofs').
        rewrite Hres in Hvalid.
        destruct (EqDec_address (b2, ofs) (b', ofs0)).
        + inversion e; subst.
          rewrite gsslockResRemLock.
          reflexivity.
        + erewrite gsolockResRemLock by eauto.
          rewrite gsoThreadLPool.
          now eauto.
    }
  Qed.

  Lemma sim_external: sim_external_def.
  Proof.
    unfold sim_external_def.
    intros.
    inversion Hsim as
        [HnumThreads HmemCompC HmemCompF HsafeC HsimWeak HfpSep HsimStrong
                     [HsimRes [Hlock_mapped Hlock_if]] HunmappedRes HinvF HmaxF
                     Hmemc_wd Htpc_wd Hge_wd [Hge_incr Hfg] Hxs HtraceSim].
    (** Thread i is in the coarse-grained machine*)
    assert (pfc: containsThread tpc i)
      by (eapply HnumThreads; eauto).
    (** Since thread i is synced, the coarse machine doesn't need to take any steps*)
    apply @not_in_filter with (xs := xs) in Hsynced.
    destruct (HsimStrong i pfc pff)
      as [tpc' [mc' [Hincr [Hsyncf [Hexec [Htsim [Hownedi [Hownedi_ls Hunmapped_ls]]]]]]]];
      clear HsimStrong.
    (** Hence tpc = tpc' and mc = mc' *)
    rewrite Hsynced in Hexec.
    assert (Heq: tpc = tpc' /\ mc = mc')
      by (clear -Hexec; inversion Hexec; subst; auto; simpl in HschedN; discriminate).
    destruct Heq; subst tpc' mc'; clear Hexec.
    (** And also f won't change, i.e. f = fi *)
    specialize (Hsyncf Hsynced); subst f.
    clear Hincr.
    (** We know there is a strong simulation for thread i*)
    specialize (Htsim pfc HmemCompC).
    (** Since the fine grained machine is at an external step so is
      the coarse-grained machine*)
    assert (HmemCompF = mem_compf Hsim)
      by (eapply proof_irr); subst.
    assert (Hvalid_mem': valid_mem (restrPermMap (compat_th _ _ HmemCompC pfc)#1))
      by (erewrite <- restrPermMap_mem_valid; eauto).
    assert (HexternalC: pfc$(restrPermMap (compat_th _ _ HmemCompC pfc).1)@ E)
      by (erewrite (stepType_inj pff pfc _  Hfg Hge_incr Hge_wd Hvalid_mem'
                           (obs_eq_data Htsim) (code_eq Htsim)); eauto).
    (** It's safe to step the coarse grained machine for one more step on i*)
    specialize (HsafeC ([:: i]) trc).
    destruct (csafe_pop_step pfc _ ltac:(eauto) HsafeC) as
        (tpc' & trc' & mc' & _ & Hstep' & Hsafe').
    (** the invariant for tpc is implied by safety*)
    assert (Hsafe := safeCoarse Hsim).
    assert (HinvC: invariant tpc)
      by (eapply StepLemmas.safeC_invariant with (n := (fuelF.+2 + size xs)); eauto).
    (** An external step pops the schedule and executes a concurrent call *)
    assert (HconcC: exists ev, syncStep true pfc HmemCompC tpc' mc' ev /\ trc' = [:: external i ev])
      by (destruct (external_step_inverse _ _ _ HexternalC Hstep') as [_ [? [? ?]]];
          eexists; eauto).
    destruct HconcC as [ev [HconcC ?]]; subst.
    assert (HmemCompC': mem_compatible tpc' mc')
      by (eapply StepLemmas.safeC_compatible with (n := (fuelF.+1 + size xs)); eauto).
    (** domain of f*)
    assert (Hdomain_f: domain_memren (fp i pfc) mc)
      by (apply (weak_obs_eq_domain_ren (weak_tsim_data (HsimWeak _ pfc pff)))).
    pose proof (injective (weak_tsim_data (HsimWeak _ pfc pff))) as Hinjective.
    (** Useful fact about the global env*)
    assert (Hge_incr_id: ren_incr fg (id_ren mc))
      by (clear - Hge_incr Hfg Hdomain_f;
           eapply incr_domain_id; eauto).

    exists tpc', (trc ++ [:: external i ev]), mc'.
    (** We proceed by case analysis on the concurrent call *)
    inversion HconcC; try subst tp' tp''; try subst m'.
    { (** Lock Acquire *)
      (** In order to construct the new memory we have to perform the
         load and store of the lock, after setting the correct permissions*)
      (** We prove that b is valid in m1 (and mc)*)
        assert (Hvalidb: Mem.valid_block m0 b)
          by (subst; eapply load_valid_block; eauto).
        rewrite <- Hrestrict_pmap0 in Hvalidb.
        (**  and compute the corresponding block in mf *)
        destruct ((domain_valid (weak_obs_eq (obs_eq_data Htsim))) _ Hvalidb)
          as [b2 Hfb].
        assert (Hvalidb2 := (codomain_valid (weak_obs_eq (obs_eq_data Htsim))) _ _ Hfb).
        erewrite restrPermMap_valid in Hvalidb2.
        (** we compute the [access_map] that we will use to perform the load*)
        remember (restrPermMap (compat_th _ _ (mem_compf Hsim) pff).2) as mf0 eqn:Hrestrict_pmapF.
        subst m0 m1.
        (** and prove that loading from that block in mf gives us the
        same value as in mc, i.e. unlocked*)
        assert (HloadF: Mem.load Mint32 mf0 b2 (Ptrofs.intval ofs) = Some (Vint Int.one)).
        { subst mf0.
          destruct (load_val_obs _ _ _ Hload Hfb Hinjective ((strong_obs_eq (obs_eq_locks Htsim))))
            as [v2 [Hloadf Hobs_eq]].
          inversion Hobs_eq; subst.
            by auto.
        }
        assert (Hval_obs: val_obs (fp i pfc) (Vint Int.zero) (Vint Int.zero))
          by constructor.
        (** we then compute the [access_map] used to perform the store*)
        remember (setPermBlock (Some Writable) b2 (Ptrofs.intval ofs) (getThreadR pff).2 lksize.LKSIZE_nat)
          as pmap_tidF' eqn:Hset_permF.
        (** prove that this map is below the [Max] [access_map] of the memory*)
        assert (HltF': permMapLt pmap_tidF' (getMaxPerm mf)).
        {
          subst.
          eapply setPermBlock_lt; eauto.
          eapply (compat_th _ _ (mem_compf Hsim) pff).2.
        }

        (** the updated (with [Writable] permissions on the lock location) map is in [mem_obs_eq]*)
        assert (Hobs_eq_locks: mem_obs_eq (fp i pfc) (restrPermMap Hlt') (restrPermMap HltF')).
        { subst.
          apply Mem.load_valid_access in Hload.
          destruct Hload as [Hload _]. simpl in Hload.
          pose proof (obs_eq_locks Htsim).
          eapply setPermBlock_obs_eq with (Hlt := (compat_th _ _ HmemCompC pfc).2); eauto.
          intros.
          eapply (val_obs_eq (strong_obs_eq H));
            by eauto. 
        }


        (** and then storing gives us related memories*)
        assert (HstoreF := store_val_obs _ _ _ Hstore Hfb Hval_obs Hobs_eq_locks).
        destruct HstoreF as [mf' [HstoreF HsimLocks']].
        (** We have that the core of the fine grained execution
            is related to the one of the coarse-grained*)
        assert (Hcore_inj:= code_eq Htsim).
        rewrite Hcode in Hcore_inj.
        simpl in Hcore_inj.
        destruct (getThreadC pff) as [? | cf |? | ?] eqn:HcodeF;
          try by exfalso.
        subst.
        (** And now we can prove that cf is also at external *)
        assert (Hat_external_spec := core_inj_ext _ _  Hfg Hge_wd Hge_incr Hvalid_mem' Hcore_inj (obs_eq_data Htsim)).
        rewrite Hat_external in Hat_external_spec.
        destruct (at_external semSem cf (restrPermMap (compat_th _ _ (mem_compf Hsim) pff)#1))
          as [[? vsf] | ] eqn:Hat_externalF;
          try by exfalso.
        (** and moreover that it's the same external and their
            arguments are related by the injection*)
        destruct Hat_external_spec as [? Harg_obs]; subst.
        inversion Harg_obs as [|? ? ? ? Hptr_obs Hl]; subst.
        inversion Hl; subst.
        inversion Hptr_obs as [| | | |b1 bf ofs0 Hf|];
          subst b1 ofs0 v'.
        assert (bf = b2)
          by (rewrite Hf in Hfb; by inversion Hfb);
          subst bf.
        (** To compute the new fine grained state, we apply the
        renaming to the resources the angel provided us*)
        pose (projectAngel (fp i pfc) virtueThread.1, projectAngel (fp i pfc) virtueThread.2) as virtueF.
        remember (updThread pff (Kresume cf Vundef)
                            (computeMap (getThreadR pff).1 virtueF.1, computeMap (getThreadR pff).2 virtueF.2))
          as tpf' eqn:Htpf'.
        (** We prove that the mapped block is a lock*)
        assert (HresF: lockRes tpf (b2, Ptrofs.intval ofs))
          by (eapply Hlock_if; eauto; rewrite HisLock; auto).
        destruct (lockRes tpf (b2, Ptrofs.intval ofs)) as [pmapF|] eqn:HisLockF;
          try by exfalso.
        clear HresF.
        (** and then prove that the projected angel satisfies [permMapJoin]*)
        destruct (HsimRes _ _ _ _ _ Hfb HisLock HisLockF) as [HsimRes1 HsimRes2].

        assert (HangelF1: permMapJoin pmapF.1 (getThreadR pff).1
                                      (computeMap (getThreadR pff).1 virtueF.1)).
        { pose proof (obs_eq_data Htsim) as Hmem_obs_eq.
          eapply permMapJoin_project with (f := fp i pfc) (pmap := pmap.1) (pmap' := (getThreadR pfc).1); eauto.
          intros b0 Hunmapped ofs0. subst.
          simpl. erewrite computeMap_projection_2 by eauto.
          left; split; [eapply HunmappedRes|]; now eauto.
          intros.
          pose proof (perm_obs_strong HsimRes1 _ ofs0 H) as Heq.
          rewrite! restrPermMap_Cur in Heq. now auto.
          intros.
          pose proof (perm_obs_strong (strong_obs_eq Hmem_obs_eq)) as Hperm_eq.
          specialize (Hperm_eq _ _ ofs0 H).
          rewrite! restrPermMap_Cur in Hperm_eq.
          now auto.
          intros. subst. simpl.
          erewrite computeMap_projection_1 by eauto.
          reflexivity.
        }
        assert (HangelF2: permMapJoin pmapF.2 (getThreadR pff).2
                                      (computeMap (getThreadR pff).2 virtueF.2)).
        { pose proof (obs_eq_locks Htsim) as Hmem_obs_eq.
          eapply permMapJoin_project with (f := fp i pfc) (pmap := pmap.2) (pmap' := (getThreadR pfc).2); eauto.
          intros b0 Hunmapped ofs0. subst.
          simpl. erewrite computeMap_projection_2 by eauto.
          left; split; [eapply HunmappedRes|]; now eauto.
          intros.
          pose proof (perm_obs_strong HsimRes2 _ ofs0 H) as Heq.
          rewrite! restrPermMap_Cur in Heq. now auto.
          intros.
          pose proof (perm_obs_strong (strong_obs_eq Hmem_obs_eq)) as Hperm_eq.
          specialize (Hperm_eq _ _ ofs0 H).
          rewrite! restrPermMap_Cur in Hperm_eq.
          now auto.
          intros. subst. simpl.
          erewrite computeMap_projection_1 by eauto.
          reflexivity.
        }
        (** and that the thread has sufficient access permissions to the lock*)
        assert(HaccessF : Mem.range_perm (restrPermMap (compat_th _ _ (mem_compf Hsim) pff)#2) b2 (Ptrofs.intval ofs)
                                         (Ptrofs.intval ofs + lksize.LKSIZE) Cur Readable).
        { destruct Htsim.
          intros ofs' Hrange.
          destruct obs_eq_locks0 as [_ [Hperm_eq _]].
          unfold Mem.range_perm, permission_at, Mem.perm in *.
          erewrite Hperm_eq;
            by eauto.
        }        
        (** and finally build the final fine-grained state*)
        pose (empty_map, empty_map) as emptyRes.
        remember (updLockSet tpf' (b2, Ptrofs.intval ofs) (projectMap (fp i pfc) emptyRes.1, projectMap (fp i pfc) emptyRes.2))
          as tpf'' eqn:Htpf'';
          symmetry in Htpf''.
        exists tpf'', mf' , (fp i pfc), fp,
        (trf ++ [:: (external i (acquire (b2, Ptrofs.intval ofs)
                                       (Some (build_delta_content virtueF#1 mf'))))]).
        split.
        (** proof that the fine grained machine can step*)
        intros U.
        assert (HsyncStepF: syncStep false pff (mem_compf Hsim) tpf'' mf'
                                     (acquire (b2, Ptrofs.intval ofs)
                                              (Some (build_delta_content virtueF#1 mf'))))
          by (eapply step_acquire with (b0:=b2); eauto).
        econstructor;
           now eauto.
        (** Proof that the new coarse and fine state are in simulation*)
        assert (HinvC':
                  invariant (updLockSet
                               (updThread pfc (Kresume c Vundef) newThreadPerm)
                               (b, Ptrofs.intval ofs) (emptyRes.1,  emptyRes.2)))
          by  (eapply StepLemmas.safeC_invariant with (n := fuelF.+1 + size xs); eauto).

        (** The new FineConc memory after storing still satisfies the [max_inv] invariant*)
        assert (HmaxF': max_inv mf')
          by (eapply max_inv_store; eauto).

        (** And the new FineConc threadPool and memory are [mem_compatible]*)
        assert (HmemCompF'' : mem_compatible tpf'' mf').
        { subst tpf' tpf'' newThreadPerm virtueF.
          eapply store_compatible; eauto.
          eapply mem_compatible_sync; eauto.
          unfold isCanonical. reflexivity.
          unfold isCanonical. reflexivity.
          eapply (mem_compf Hsim).
          eapply (codomain_valid (weak_obs_eq (obs_eq_data Htsim))).
        }
        subst.

        (** [mc] and [mc'] have the same valid blocks *)
        assert (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b).
        intros.
          by (intros;
              erewrite <- restrPermMap_valid with (Hlt := Hlt');
              split;
              [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
                by eauto).
        assert (Hvb': forall b, ~ Mem.valid_block mc b <-> ~ Mem.valid_block mc' b)
          by (intros; split; intros Hinvalid Hcontra;
                by apply Hvb in Hcontra).

        (** [mf] and [mf'] have the same valid blocks *)
        assert (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b)
          by (
              intros;
              erewrite <- restrPermMap_valid with (Hlt := HltF');
              split;
              [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
                by eauto).

        (** * Proof of strong thread simulations *)
        assert (Hstrong_tsim:
                  forall (tid : nat)
                    (pfc0 : containsThread
                              (updLockSet (updThread pfc (Kresume c Vundef) newThreadPerm)
                                          (b, Ptrofs.intval ofs) (empty_map, empty_map)) tid)
                    (pff0 : containsThread
                              (updLockSet
                                 (updThread pff (Kresume cf Vundef)
                                            (computeMap (getThreadR pff)#1 virtueF#1,
                                             computeMap (getThreadR pff)#2 virtueF#2)) (b2, Ptrofs.intval ofs)
                                 (projectMap (fp i pfc) emptyRes#1, projectMap (fp i pfc) emptyRes#2)) tid),
                  exists (tpc' : t) (mc'0 : mem),
                    ren_incr (fp i pfc) (fp tid pfc0) /\
                    ([seq x <- xs | x == tid] = [::] -> fp i pfc = fp tid pfc0) /\
                    internal_execution [seq x <- xs | x == tid]
                                       (updLockSet (updThread pfc (Kresume c Vundef) newThreadPerm) 
                                                   (b, Ptrofs.intval ofs) (empty_map, empty_map)) mc' tpc' mc'0 /\
                    (forall (pfc' : containsThread tpc' tid) (mem_compc' : mem_compatible tpc' mc'0),
                        strong_tsim (fp tid pfc0) pfc' pff0 mem_compc' HmemCompF'') /\
                    (forall (tid2 : nat)
                       (pff2 : containsThread
                                 (updLockSet
                                    (updThread pff (Kresume cf Vundef)
                                               (computeMap (getThreadR pff)#1 virtueF#1,
                                                computeMap (getThreadR pff)#2 virtueF#2)) 
                                    (b2, Ptrofs.intval ofs)
                                    (projectMap (fp i pfc) emptyRes#1, projectMap (fp i pfc) emptyRes#2))
                                 tid2),
                        tid <> tid2 ->
                        forall (b1 b0 : block) (ofs0 : Z),
                          fp tid pfc0 b1 = Some b0 ->
                          fp i pfc b1 = None ->
                          ((getThreadR pff2)#1) # b0 ofs0 = None /\ ((getThreadR pff2)#2) # b0 ofs0 = None) /\
                    (forall (bl : block) (ofsl : Z) (rmap : lock_info) (b1 b0 : block) (ofs0 : Z),
                        fp tid pfc0 b1 = Some b0 ->
                        fp i pfc b1 = None ->
                        lockRes
                          (updLockSet
                             (updThread pff (Kresume cf Vundef)
                                        (computeMap (getThreadR pff)#1 virtueF#1,
                                         computeMap (getThreadR pff)#2 virtueF#2)) (b2, Ptrofs.intval ofs)
                             (projectMap (fp i pfc) emptyRes#1, projectMap (fp i pfc) emptyRes#2)) 
                          (bl, ofsl) = Some rmap -> (rmap#1) # b0 ofs0 = None /\ (rmap#2) # b0 ofs0 = None) /\
                    (forall b0 : block,
                        ~ (exists b1 : block, fp tid pfc0 b1 = Some b0) ->
                        forall ofs0 : Z,
                          ((getThreadR pff0)#1) # b0 ofs0 = None /\ ((getThreadR pff0)#2) # b0 ofs0 = None)).
        { (** Proof of strong simulations after executing some thread*)
          intros.
          destruct (tid == i) eqn:Htid; move/eqP:Htid=>Htid; subst.
          { (** case of strong simulation for the thread that stepped*)
            exists (updLockSet
                 (updThread pfc (Kresume c Vundef)
                            (computeMap (getThreadR pfc).1 virtueThread.1,
                             computeMap (getThreadR pfc).2 virtueThread.2))
                 (b, Ptrofs.intval ofs) (emptyRes.1, emptyRes.2)), mc'.
            assert (pfc0 = pfc)
              by (eapply cnt_irr; eauto); subst pfc0.
            rewrite Hsynced.
            (* repeat (split; (auto || constructor)). *)
            split; first by apply ren_incr_refl.
            split; first by auto.
            split; first by constructor.
            split.
            (** prof of [strong_tsim]*)
            intros.
            destruct Htsim as [_ Hmem_obs_eq_data Hmem_obs_eq_locks].
            constructor.
            rewrite! gLockSetCode.
            do 2 rewrite gssThreadCode;
              by (split; [assumption | constructor]).

            (** [mem_obs_eq] for data*)
            (** Need to massage goal a bit*)
            assert (Hlt1: permMapLt (computeMap (getThreadR pfc).1 virtueThread.1) (getMaxPerm mc')).
            { destruct mem_compc'.
              destruct (compat_th0 _ pfc').
              rewrite gLockSetRes  gssThreadRes in H.
              eauto.
            }
            erewrite restrPermMap_irr' with (Hlt' := Hlt1)
              by (rewrite gLockSetRes gssThreadRes; eauto).

            assert (Hlt1F: permMapLt (computeMap (getThreadR pff).1 virtueF.1) (getMaxPerm mf')).
            { destruct HmemCompF''.
              destruct (compat_th0 _ pff0).
              rewrite gLockSetRes  gssThreadRes in H.
              eauto.
            }
            erewrite restrPermMap_irr' with (Hlt' := Hlt1F)
              by (rewrite gLockSetRes gssThreadRes; eauto).
            eapply gss_mem_obs_eq_lock with (Hlt' := ((compat_lp _ _ HmemCompC) _ _ HisLock).1); simpl;
              try (erewrite! Mem.store_mem_contents by eauto);
              eauto; try reflexivity.

            (** [mem_obs_eq] for locks*)

            (** Need to massage goal a bit*)
            assert (Hlt2: permMapLt (computeMap (getThreadR pfc).2 virtueThread.2) (getMaxPerm mc')).
            { destruct mem_compc'.
              destruct (compat_th0 _ pfc').
              rewrite gLockSetRes  gssThreadRes in H0.
              eauto.
            }
            erewrite restrPermMap_irr' with (Hlt' := Hlt2)
              by (rewrite gLockSetRes gssThreadRes; eauto).

            assert (Hlt2F: permMapLt (computeMap (getThreadR pff).2 virtueF.2) (getMaxPerm mf')).
            { destruct HmemCompF''.
              destruct (compat_th0 _ pff0).
              rewrite gLockSetRes  gssThreadRes in H0.
              eauto.
            }
            erewrite restrPermMap_irr' with (Hlt' := Hlt2F)
              by (rewrite gLockSetRes gssThreadRes; eauto).
            eapply gss_mem_obs_eq_lock with (Hlt' := ((compat_lp _ _ HmemCompC) _ _ HisLock).2); simpl;
              try (erewrite! Mem.store_mem_contents by eauto);
              eauto; try reflexivity.

            (** rest of strong sim*)
            split; first by congruence.
            split; first by congruence.
            rewrite gLockSetRes gssThreadRes;
              simpl; intros; rewrite! computeMap_projection_2;
                eauto.
          }
          { (**strong simulation for another thread*)
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
                  & Hownedj & Hownedj_lp & Hunmapped_j).
            (** first we prove that i is a valid thread after executing thread j*)
            assert (pfcij:= containsThread_internal_execution Hexecj pfc).

            (** Proof Sketch: Basically the proof we want is that changing some
            non-observable part of the state/memory should not affect the
            execution of thread j. To avoid giving yet another definition of
            equivalence of the observable state we re-use our strong
            injections/renamings. Steps:

            1. For the core and data resources, the original state <tpc,mc> will
            strongly inject with the id injection in the state <tpc', mc'> where
            we have updated the value of the lock and the resource maps
            according to the angel.

            2. Hence if <tpc,mc> takes internal steps to get to <tpcj, mcj> so
            will <tpc',mc'> to go to a new state <tpcj',mcj'>. Moreover
            <tpcj,mcj> will inject to <tpcj',mcj'> with the id injection. We had
            to strengthen our lemmas and corestep_obs_eq to obtain that last
            part.

            3. We use [strong_tsim_id_trans] to get that <tpcj',mcj'> will
               strongly inject in <tpf,mf> with the same injection as
               <tpcj,mcj>.

            4. Finally we prove that changing the state/memory in (TODO: add
            lemma name) non-observable parts retains the [strong_tsim] relation.
             *)

            (** Step 1*)
            assert (pfcjj: containsThread tpcj tid)
              by (eapply containsThread_internal_execution; eauto).
            assert (Hcompj: mem_compatible tpcj mcj)
              by (eapply internal_execution_compatible with (tp := tpc); eauto).
            specialize (Htsimj pfcjj Hcompj).

            (** We prove that thread tid on the original state injects
            in thread tid after updating the lockpool and storing the
            lock value*)
            assert (Htsimj_id:
                      tp_wd (id_ren mc) tpc /\
                      ctl_inj (id_ren mc) (getThreadC pfcj) (getThreadC pfc0) /\
                      mem_obs_eq (id_ren mc) (restrPermMap (compat_th _ _ HmemCompC pfcj).1) (restrPermMap (compat_th _ _ HmemCompC' pfc0).1) /\
                      Mem.nextblock mc = Mem.nextblock mc').
            { split.
              eapply tp_wd_domain;
                by eauto using id_ren_domain.
              eapply strong_tsim_store_id; eauto.
              erewrite gLockSetRes.
              rewrite gsoThreadRes; eauto.
              erewrite gLockSetCode.
              rewrite gsoThreadCode; eauto.
              destruct HinvC.
              pose proof ((thread_data_lock_coh0 _ pfc ).1 _ pfcj) as Hcoh.
              left.
              eapply permMapCoherence_increase; eauto.
              apply Mem.load_valid_access in Hload.
              destruct Hload as [Hload _].
              intros.
              specialize (Haccess ofs' H).
              unfold Mem.perm in Haccess.
              pose proof (restrPermMap_Cur (compat_th _ _ HmemCompC pfc).2 b ofs') as Hperm_at.
              unfold permission_at in Hperm_at.
              rewrite Hperm_at in Haccess.
              assumption.
              eapply tp_wd_domain;
                by eauto using id_ren_domain.
            }
            destruct Htsimj_id as [Htpc_id_wd [Hctlj_id [Hmem_obs_eqj_id Hnextblock]]].

            (** Step 2.*)
            assert (H := mem_obs_eq_execution _ _ _ _ _ HinvC' Hfg Hge_wd Hge_incr_id
                                              Hmemc_wd Htpc_id_wd Hctlj_id Hmem_obs_eqj_id Hexecj).
            destruct H as
                (tp2' & m2' & f' & Hexecj'& Hincrj' & Hsepj'
                 & Hnextblock' & Hinvj' & Htsimj' & Hid').
            destruct Htsimj' as (pf2j & pf2j' & Hcomp2 & Hcomp2' & Hctl_eqj' & Hmem_obs_eq').
            specialize (Hid' Hnextblock (id_ren_correct mc)).
            assert (f' = id_ren mcj)
              by ( pose ((mem_obs_eq_domain_ren Hmem_obs_eq'));
                   eapply is_id_ren; eauto); subst f'.
            exists tp2', m2'.
            erewrite cnt_irr with (cnt1 := pfc0) (cnt2 := pfcj).
            split; first by auto.
            split; first by auto.
            split; first by auto.
            split.
            (** strong thread simulation for j*)
            intros.
            Tactics.pf_cleanup.
            (** Step 3, we use transitivity of [mem_obs_eq] and [ctl_inj] *)
            assert (Htsim2j: ctl_inj (fp tid pfcj) (getThreadC pf2j') (getThreadC pffj) /\
                             mem_obs_eq (fp tid pfcj) (restrPermMap (compat_th _ _ Hcomp2' pf2j').1)
                                        (restrPermMap (compat_th _ _ (mem_compf Hsim) pffj).1)).
            { destruct Htsimj.
              eapply strong_tsim_id_trans
                with (f := fp tid pfcj) (Hcomp1 := Hcompj) (Hcomp1' := Hcomp2');
                eauto.
              destruct Hnextblock' as [[p [Hmcj Hm2']] | [Hmcj Hm2']];
                unfold Mem.valid_block;
                rewrite Hmcj Hm2' Hnextblock;
                  by tauto.
            }

            (** Step 4*)
            destruct Htsim2j as [Hcodeq2j Hmem_obs_eq2j].
            constructor.
            rewrite gLockSetCode.
            rewrite gsoThreadCode;
              by auto.
            clear - Hmem_obs_eq2j HstoreF HinvF Htid HloadF HaccessF.
            assert (HeqRes: getThreadR pff0 = getThreadR pffj)
              by (rewrite gLockSetRes;
                  rewrite gsoThreadRes; auto).
            assert (Hlt : permMapLt (getThreadR pff0).1 (getMaxPerm mf))
              by (rewrite HeqRes; eapply (compat_th _ _ (mem_compf Hsim) pffj).1).
            eapply mem_obs_eq_storeF with (mf := mf) (Hlt :=  Hlt);
              eauto. (*TODO: change mem_obs_eq_storeF to use coherence instead of disjointness*)
            apply Mem.load_valid_access in HloadF.
            pose proof (((thread_data_lock_coh _ HinvF) _ pff).1 _ pffj).
            pose proof (cntUpdateL' _ _ pff0) as pffj'.
            erewrite gLockSetRes with (cnti := pffj').
            erewrite gsoThreadRes with (cntj := pffj) by eauto.
            left.
            apply setPermBlock_coherent; eauto.
            intros ofs' Hrange Hcontra.
            specialize (HaccessF ofs' Hrange).
            unfold Mem.perm in HaccessF.
            specialize (H b2 ofs').
            pose proof (restrPermMap_Cur (compat_th _ _ (mem_compf Hsim) pff).2 b2 ofs') as Heq.
            unfold permission_at in Heq.
            rewrite Heq in HaccessF.
            destruct ((getThreadR pffj).1 # b2 ofs') as [p1|]; simpl in Hcontra;
              [| assumption];
              inversion Hcontra; subst;
                destruct ((getThreadR pff).2 # b2 ofs') as [p2|]; simpl in HaccessF;
                  now auto.
            erewrite restrPermMap_irr' with (Hlt := Hlt)
                                            (Hlt' := (compat_th _ _ (mem_compf Hsim) pffj).1); eauto.
            rewrite HeqRes. reflexivity.

            pose proof (obs_eq_locks Htsimj).

            assert (HRj_eq: (getThreadR pf2j').2 = (getThreadR pfcjj).2).
            { erewrite <- internal_execution_locks_eq with (cntj := pfc0) by eauto.
              erewrite <- internal_execution_locks_eq with (cntj' := pfcjj) (cntj := pfcj) by eauto.
              rewrite gLockSetRes.
              erewrite gsoThreadRes by eauto;
                reflexivity.
            }

            assert (Hlt2C: permMapLt (getThreadR pfcjj).2 (getMaxPerm m2'))
              by ( rewrite <- HRj_eq;
                   eapply (compat_th _ _ Hcomp2' pf2j').2).
            erewrite restrPermMap_irr' with (Hlt' := Hlt2C) by eauto.

            assert (HRj_eqF: (getThreadR pff0)#2 = (getThreadR pffj)#2)
              by (rewrite gLockSetRes; erewrite gsoThreadRes with (cntj := pffj) by eauto;
                  reflexivity).

            assert (Hlt2F: permMapLt (getThreadR pffj).2 (getMaxPerm mf'))
              by (rewrite <- HRj_eqF; eapply (compat_th _ _ HmemCompF'' pff0).2).
            erewrite restrPermMap_irr' with (Hlt' := Hlt2F) by eassumption.

            (** some useful results*)

            (** the contents of [m2'] are equal to the contents of [mc'] for locations [Readable] by locks on thread [tid]*)
            assert (Hstable_mc2': forall b1 ofs1, Mem.perm_order' ((getThreadR pfcj).2 # b1 ofs1) Readable ->
                                             ZMap.get ofs1 (Mem.mem_contents mc') # b1 = ZMap.get ofs1 (Mem.mem_contents m2') # b1).
            { intros.
              erewrite <- internal_exec_disjoint_locks with (Hcomp := HmemCompC') (m := mc') (m' := m2') (pfj := pfc0); eauto.
              unfold Mem.perm.
              pose proof (restrPermMap_Cur (compat_th _ _ HmemCompC' pfc0).2 b1 ofs1) as Hpermj.
              unfold permission_at in Hpermj.
              rewrite Hpermj.
              rewrite gLockSetRes.
              erewrite gsoThreadRes with (cntj := pfcj) by eauto.
              assumption.
            }

            (** the contents of [mcj] are equal to the contents of [mc] for locations [Readable] by locks on thread [tid]*)
            assert (Hstable_mcj: forall b1 ofs1, Mem.perm_order' ((getThreadR pfcj).2 # b1 ofs1) Readable ->
                                            ZMap.get ofs1 (Mem.mem_contents mc) # b1 =
                                            ZMap.get ofs1 (Mem.mem_contents mcj) # b1).
            { intros.
              erewrite internal_exec_disjoint_locks
                with (Hcomp := HmemCompC) (pfj := pfcj) (m := mc) (tp := tpc) (tp' := tpcj); eauto.
              unfold Mem.perm in *.

              pose proof (restrPermMap_Cur (compat_th _ _ HmemCompC pfcj).2 b1 ofs1) as Hpermj.
              unfold permission_at in *.
              rewrite Hpermj. assumption.
            }

            assert (Hperm_eqj: forall b1 ofs1, (Mem.mem_access (restrPermMap (compat_th _ _ Hcompj pfcjj).2)) # b1 ofs1 Cur =
                                          (getThreadR pfcj).2 # b1 ofs1).
            { intros.
              pose proof (restrPermMap_Cur (compat_th _ _ Hcompj pfcjj).2 b1 ofs1) as Hpermjj.
              unfold permission_at in Hpermjj.
              rewrite Hpermjj.
              erewrite <- internal_execution_locks_eq with (cntj' := pfcjj) (cntj := pfcj) at 1
                by eauto.
              reflexivity.
            }


            (** **** We now apply [mem_obs_eq_disjoint_lock]*)
            eapply mem_obs_eq_disjoint_lock
              with (ofsl := Ptrofs.intval ofs) (bl1 := b)
                   (bl2 := b2) (sz := size_chunk Mint32); eauto.
            (** valid blocks of [mcj] are the same [m2']*)
            intros. unfold Mem.valid_block in *.
            destruct Hnextblock' as [[p [Hnextj Hnext2]] | [Hnextj Hnext2]];
              rewrite Hnextj Hnext2 Hnextblock;
              split; now auto.

            (** [memval_obs_eq] of contents on updated lock*)
            intros ofs0 Hrange.
            (** thread i has lock access on this location by the read it
            succesfully performed, hence by coherence thread j cannot have
            [Writable] data permission on that location*)
            assert (Hlock_unwrittable: ~ Mem.perm (restrPermMap (compat_th _ _ HmemCompC' pfc0)#1) b ofs0 Cur Writable).
            { clear - Hload HinvC Hrange pfcj Htid.
              pose proof (((thread_data_lock_coh _ HinvC _ pfc).1) _ pfcj b ofs0) as Hcoh.
              apply Mem.load_valid_access in Hload.
              destruct Hload as [Hperm _].
              specialize (Hperm ofs0 Hrange).
              unfold Mem.perm in *.
              pose proof ((restrPermMap_Cur (compat_th _ _ HmemCompC' pfc0).1) b ofs0) as Hpermj'.
              pose proof ((restrPermMap_Cur (compat_th _ _ HmemCompC pfc).2) b ofs0) as Hpermi.
              unfold permission_at in *.
              rewrite Hpermi in Hperm.
              rewrite Hpermj'.
              rewrite gLockSetRes.
              erewrite gsoThreadRes with (cntj := pfcj) by eauto.
              intros Hcontra.
              destruct ((getThreadR pfcj).1 # b ofs0) as [p|]; try (by exfalso);
                destruct p; simpl in Hcontra; inversion Hcontra; subst;
                  destruct ((getThreadR pfc).2 # b ofs0) as [p|];
                  try (by exfalso); inversion Hcontra; subst.
            }

            (** and thus by [internal_exec_stable]*)
            erewrite <- internal_exec_stable with (m := mc') (Hcomp := HmemCompC') (pfi := pfc0); eauto.
            erewrite Mem.store_mem_contents with (m2 := mc') by eauto.
            erewrite Mem.store_mem_contents with (m2 := mf') by eauto.
            rewrite! Maps.PMap.gss.
            erewrite! setN_inside
              by (simpl; eauto).
            (* by (rewrite length_inj_bytes encode_int_length; simpl in Hrange; auto). *)
            destruct ((List.nth_in_or_default (Z.to_nat (ofs0 - Ptrofs.intval ofs)) (encode_val Mint32 (Vint Int.zero)) Undef)).
            apply inj_bytes_type in i0.
            destruct (List.nth (Z.to_nat (ofs0 - Ptrofs.intval ofs)) (encode_val Mint32 (Vint Int.zero)) Undef);
              now constructor.
            rewrite e. now constructor.
            eapply Mem.store_valid_block_1; eauto.
            (** the contents of [mcj] are equal to the contents of [mc] for locations [Readable] by locks on thread [tid]*)
            intros.
            unfold Mem.perm in H1.
            erewrite Hperm_eqj in H1.
            erewrite <- Hstable_mc2' by eauto.
            erewrite <- Hstable_mcj by eauto.
            (** we can now prove that for all lock locations that tid can access, other than the one updated, the contents will be equal*)
            erewrite Mem.store_mem_contents with (m2 := mc') by eauto.
            destruct H0 as [Hb_neq | [? Hofs_neq]].
            (** if b0 is not the block that was updated*)
            erewrite Maps.PMap.gso by eauto.
            reflexivity.
            (** if b0 is the updated block but ofs0 is not in the updated range*)
            subst.
            rewrite Maps.PMap.gss.
            erewrite Mem.setN_outside
              by (rewrite encode_val_length; eapply Intv.range_notin in Hofs_neq; eauto; simpl; omega).
            reflexivity.

            (** stability for contents of [mf] and [mf']*)
            intros b0 ofs0 Hneq Hreadable.
            erewrite Mem.store_mem_contents with (m2 := mf') by eauto.
            destruct Hneq as [Hb_neq | [? Hofs_neq]].
            (** if b0 is not the block that was updated*)
            erewrite Maps.PMap.gso by eauto.
            reflexivity.
            (** if b0 is the updated block but ofs0 is not in the updated range*)
            subst.
            rewrite Maps.PMap.gss.
            erewrite Mem.setN_outside
              by (rewrite encode_val_length; eapply Intv.range_notin in Hofs_neq; eauto; simpl; omega).
            reflexivity.
            eauto.
            split.
            (** thread ownership*)
            intros k pff2k Hjk b1 b0 ofs0 Hfj Hfi.
            destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
            { subst k.
              rewrite gLockSetRes.
              rewrite gssThreadRes; auto.
              assert (Hunmapped: ~ (exists b, (fp i pfc) b = Some b0)).
              { intros Hcontra.
                destruct Hcontra as [b3 Hcontra].
                assert (Hfj' := Hincrj _ _ Hcontra).
                assert (Heq := injective (weak_obs_eq (obs_eq_data Htsimj)) _ _ Hfj Hfj');
                  subst b3.
                  by congruence.
              }
              simpl.
              erewrite! computeMap_projection_2;
                by eauto.
            }
            { rewrite gLockSetRes.
              rewrite gsoThreadRes; auto.
              eapply Hownedj;
                by eauto.
            }
            split.
            (** lockpool ownership*)
            intros bl ofsl rmap b1 b0 ofs0 Hfj Hfi Hres.
            destruct (EqDec_address (b2, Ptrofs.intval ofs) (bl, ofsl)) as [Heq | Hneq].
            (** case rmap is the resource map updated by the angel*)
            inversion Heq; subst.
            rewrite gssLockRes in Hres. inversion Hres.
            assert (~ exists b, fp i pfc b = Some b0).
            { intros Hcontra.
              destruct Hcontra as [b' Hfb'].
              assert (Hfb'' := Hincrj _ _ Hfb').
              assert (b' = b1)
                by (eapply (injective (weak_obs_eq (obs_eq_data Htsimj)));
                    eauto). subst b'.
                by congruence.
            }
            rewrite! projectMap_correct_2; auto.
            (** case it is another resource map*)
            rewrite gsoLockRes in Hres; auto.
            rewrite gsoThreadLPool in Hres;
              by eauto.
            (** unmapped blocks are empty*)
            intros b0 Hunmapped ofs0.
            rewrite gLockSetRes.
            erewrite gsoThreadRes with (cntj := pffj) by eauto.
            eapply Hunmapped_j;
              by eauto.
          }
        }
        
        eapply Build_sim with (mem_compc := HmemCompC') (mem_compf := HmemCompF'').
        - (** containsThread *)
          clear - HnumThreads.
          intros j.
          split; intros cntj;
          eapply cntUpdateL;
          eapply cntUpdate;
          apply cntUpdateL' in cntj;
          apply cntUpdate' in cntj;
            by eapply HnumThreads.
        - (** safety of coarse machine*)
          intros sched tr.
          eapply HybridCoarseMachine.csafe_trace;
            now eauto.
        - (** weak simulation between the two machines*)
          (*NOTE: pointless to factor this out as a lemma, since acquire/release virtue types do not match*)

          intros j pfcj' pffj'.
          assert (pfcj: containsThread tpc j)
            by auto.
          assert (pffj: containsThread tpf j)
            by auto.
          specialize (HsimWeak _ pfcj pffj).

          clear - Hvb Hvb' HvbF HsimWeak Hsim.

          (** Permissions on DryConc machine are higher than permissions on FineConc*)
          assert (Hlt:
                    forall (b1 b0 : block) (ofs0 : Z),
                      fp i pfc b1 = Some b0 ->
                      Mem.perm_order'' (permission_at (restrPermMap (compat_th _ _ HmemCompC' pfcj')#1) b1 ofs0 Cur)
                                       (permission_at (restrPermMap (compat_th _ _ HmemCompF'' pffj').1) b0 ofs0 Cur) /\
                      Mem.perm_order'' (permission_at (restrPermMap (compat_th _ _ HmemCompC' pfcj')#2) b1 ofs0 Cur)
                                       (permission_at (restrPermMap (compat_th _ _ HmemCompF'' pffj').2) b0 ofs0 Cur)).
          { intros b1 b0 ofs0 Hrenaming.
            pose proof (perm_obs_weak (weak_tsim_data HsimWeak)) as Hperm_data.
            pose proof (perm_obs_weak (weak_tsim_locks HsimWeak)) as Hperm_locks.
            specialize (Hperm_data _ _ ofs0 Hrenaming).
            specialize (Hperm_locks _ _ ofs0 Hrenaming).
            destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
            - (** this is the case where the angel has replaced some permissions*)
              subst j.
              Tactics.pf_cleanup.
              rewrite! restrPermMap_Cur gLockSetRes gssThreadRes;
                rewrite! gLockSetRes gssThreadRes.
              pose proof (injective (weak_tsim_data HsimWeak)).

              (** by case analysis on whether the angel changed the
              permission at this address*)
              assert (Hproject1: Maps.PTree.get b0 (projectAngel (fp i pfc) virtueThread.1) =
                                 Maps.PTree.get b1 virtueThread.1)
                by (symmetry; eapply projectAngel_correct; eauto).
              assert (Hproject2: Maps.PTree.get b0 (projectAngel (fp i pfc) virtueThread.2) =
                                 Maps.PTree.get b1 virtueThread.2)
                by (symmetry; eapply projectAngel_correct; eauto).
              split; simpl in *.
              + destruct (Maps.PTree.get b1 virtueThread.1) as [df|] eqn:Hdelta.
                * destruct (df ofs0) as [pnew |] eqn:Hdf.
                  rewrite (computeMap_1 _ _ _ _ Hdelta Hdf).
                  rewrite (computeMap_1 _ _ _ _ Hproject1 Hdf);
                    by eapply po_refl.
                rewrite (computeMap_2 _ _ _ _ Hdelta Hdf).
                rewrite (computeMap_2 _ _ _ _ Hproject1 Hdf);
                  by do 2 rewrite restrPermMap_Cur in Hperm_data.
                *  rewrite (computeMap_3 _ _ _ _ Hdelta).
                rewrite (computeMap_3 _ _ _ _ Hproject1);
                  by do 2 rewrite restrPermMap_Cur in Hperm_data.
              + destruct (Maps.PTree.get b1 virtueThread.2) as [df|] eqn:Hdelta.
                * destruct (df ofs0) as [pnew |] eqn:Hdf.
                  rewrite (computeMap_1 _ _ _ _ Hdelta Hdf).
                  rewrite (computeMap_1 _ _ _ _ Hproject2 Hdf);
                    by eapply po_refl.
                  rewrite (computeMap_2 _ _ _ _ Hdelta Hdf).
                  rewrite (computeMap_2 _ _ _ _ Hproject2 Hdf);
                    by do 2 rewrite restrPermMap_Cur in Hperm_locks.
                *  rewrite (computeMap_3 _ _ _ _ Hdelta).
                   rewrite (computeMap_3 _ _ _ _ Hproject2);
                     by do 2 rewrite restrPermMap_Cur in Hperm_locks.
            - erewrite! restrPermMap_Cur.
              assert (pfcj0: containsThread (updThread pfc (Kresume c Vundef) newThreadPerm) j)
                by (apply cntUpdate; auto).
              assert (pffj0: containsThread (updThread pff (Kresume cf Vundef)
                                                       (computeMap (getThreadR pff)#1 virtueF#1, computeMap (getThreadR pff)#2 virtueF#2)) j)
                by (apply cntUpdate; auto).
              erewrite gLockSetRes with (cnti := pfcj0).
              erewrite gLockSetRes with (cnti := pffj0).
              erewrite gsoThreadRes with (cntj := pfcj); eauto.
              erewrite gsoThreadRes with (cntj := pffj); eauto.
              split;
                [do 2 erewrite restrPermMap_Cur in Hperm_data |
                 do 2 erewrite restrPermMap_Cur in Hperm_locks];
                  by assumption. }

          destruct HsimWeak. destruct weak_tsim_data0.
          constructor; intros; constructor; intros; simpl;
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
            try (by specialize (codomain_valid0 _ _ H));
            destruct (Hlt _ _ ofs0 Hrenaming);
            eauto.
        - (** Proof of seperation of injections *)
          intros k j cntk' cntj' Hkj b0 b0' b3 b3' Hf0 Hf0' Hfk' Hfj'.
          assert (cntk: containsThread tpc k)
            by auto.
          assert (cntj: containsThread tpc j)
            by auto.
          erewrite cnt_irr with (cnt1 := cntk') (cnt2 := cntk) in Hfk'.
          erewrite cnt_irr with (cnt1 := cntj') (cnt2 := cntj) in Hfj'.
          eapply (HfpSep _ _ cntk cntj Hkj b0 b0');
            by eauto.
        - eauto.
        - (** Proof of [strong_mem_obs_eq] for lock pool*)
          (** The lock case is easy because the resources are set to empty*)
          split.
          { intros bl1 bl2 ofs0 rmap1 rmap2 Hfi Hres1 Hres2.
            destruct (EqDec_address (b, Ptrofs.intval ofs) (bl1, ofs0)) as [Heq | Hneq].
            { (** case it is the acquired lock *)
              inversion Heq; subst.
              assert (bl2 = b2)
                by (rewrite Hfi in Hfb; by inversion Hfb).
              subst bl2.
              assert (Hperm_eq: forall b1 b0 ofs0, fp i pfc b1 = Some b0 ->
                                    permission_at (restrPermMap (compat_lp _ _ HmemCompF'' (b2, Ptrofs.intval ofs) _ Hres2)#1) b0 ofs0 Cur =
                                    permission_at (restrPermMap (compat_lp _ _ HmemCompC' (bl1, Ptrofs.intval ofs) _ Hres1)#1) b1 ofs0 Cur /\
                                    permission_at (restrPermMap (compat_lp _ _ HmemCompF'' (b2, Ptrofs.intval ofs) _ Hres2)#2) b0 ofs0 Cur =
                                    permission_at (restrPermMap (compat_lp _ _ HmemCompC' (bl1, Ptrofs.intval ofs) _ Hres1)#2) b1 ofs0 Cur).
              { intros.
                rewrite! restrPermMap_Cur.
                rewrite gssLockRes in Hres1.
                rewrite gssLockRes in Hres2.
                inversion Hres1; inversion Hres2.
                unfold Maps.PMap.get.
                rewrite! Maps.PTree.gempty;
                  split;
                    by reflexivity.
              }
              split;
                constructor; intros;
                  try (destruct (Hperm_eq b1 b0 ofs0 Hrenaming); by auto).
              assert (H:= restrPermMap_Cur (compat_lp _ _ HmemCompC' (bl1, Ptrofs.intval ofs)
                                                      _ Hres1).1 b1 ofs0).
              unfold permission_at in H.
              unfold Mem.perm in Hperm.
              rewrite H in Hperm.
              clear H Hperm_eq.
              exfalso.
              rewrite gssLockRes in Hres1.
              inversion Hres1; subst.
              unfold Maps.PMap.get in Hperm.
              rewrite Maps.PTree.gempty in Hperm.
              simpl in Hperm;
                by auto.
              assert (H:= restrPermMap_Cur (compat_lp _ _ HmemCompC' (bl1, Ptrofs.intval ofs)
                                                      _ Hres1).2 b1 ofs0).
              unfold permission_at in H.
              unfold Mem.perm in Hperm.
              rewrite H in Hperm.
              clear H Hperm_eq.
              exfalso.
              rewrite gssLockRes in Hres1.
              inversion Hres1; subst.
              unfold Maps.PMap.get in Hperm.
              rewrite Maps.PTree.gempty in Hperm.
              simpl in Hperm;
                by auto.
            }
            { (** case it's another lock*)
              assert ((b2, Ptrofs.intval ofs) <> (bl2, ofs0)).
              { clear - Hneq Hfi Hf Hfb Htsim.
                intros Hcontra; inversion Hcontra; subst.
                assert (b = bl1)
                  by (eapply (injective (weak_obs_eq (obs_eq_data Htsim))); eauto).
                subst;
                  by auto.
              }
                pose proof Hres1 as Hres1';
                  pose proof Hres2 as Hres2'.
                erewrite gsoLockRes, gsoThreadLPool in Hres1' by auto.
                erewrite gsoLockRes, gsoThreadLPool in Hres2' by auto.
                destruct (HsimRes _ _ _ _ _ Hfi Hres1' Hres2') as [Hsim1 Hsim2].
                split;
                  eapply strong_mem_obs_eq_store with (bl1 := b) (bl2 := b2); eauto;
                    try (erewrite Mem.store_mem_contents by eauto; reflexivity).
            }
          }
          split.
          (** proof that locks are mapped*)
          intros bl2 ofs0 Hres.
          destruct (EqDec_address (bl2, ofs0) (b2, Ptrofs.intval ofs)) as [Heq | Hneq].
          inversion Heq; subst.
          eexists;
            by eauto.
          erewrite gsoLockRes, gsoThreadLPool in Hres by auto.
          eapply Hlock_mapped;
            by eauto.
          (** proof that the two machines have the same locks*)
          { intros bl1 bl2 ofs0 Hfl1.
            destruct (EqDec_address (b, Ptrofs.intval ofs) (bl1, ofs0)).
            - inversion e; subst.
              assert (b2 = bl2)
                by (rewrite Hf in Hfl1; inversion Hfl1; subst; auto).
              subst.
              do 2 rewrite gsslockResUpdLock.
              split;
              auto.
            - erewrite gsolockResUpdLock by auto.
              assert ((b2, Ptrofs.intval ofs) <> (bl2, ofs0)).
              { intros Hcontra.
                inversion Hcontra; subst.
                specialize (Hinjective _ _ _ Hfl1 Hfb).
                subst; auto.
              }
              erewrite gsolockResUpdLock by eauto.
              do 2 rewrite gsoThreadLPool.
              eauto.
          }
        - (** proof that unmapped blocks are empty*)
          intros bl ofsl rmap Hres b0 Hunmapped ofs0.
          destruct (EqDec_address (b2, Ptrofs.intval ofs) (bl, ofsl)).
          + inversion e; subst.
            rewrite gsslockResUpdLock in Hres.
            inversion Hres; subst.
            simpl.
            erewrite! projectMap_correct_2 by auto.
            split; reflexivity.
          + erewrite gsolockResUpdLock in Hres by auto.
            rewrite gsoThreadLPool in Hres.
            eapply HunmappedRes; eauto.
        - (** Proof of invariant preservation for fine-grained machine*)
          destruct Htsim.
          eapply invariant_project; by eauto.
        - (** Max permission invariant*)
          assumption.
        - (** new memory is well-defined*)
          eapply store_wd_domain with
          (m := (restrPermMap Hlt')); eauto.
            by simpl.
        - (** new tpc is well-defined*)
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
          specialize (Htpc_wd _ cntj);
            by auto.
        - (** ge is well-defined*)
          assumption.
        - (** ge spec*)
          split; assumption.
        - intros.
          apply cntUpdateL;
            apply cntUpdate;
              by eauto.
        - econstructor 2;
            eauto.
          unfold virtueF.
          destruct virtueThread as [vT1 vT2].
          econstructor; eauto.
          + simpl.
            assert (cnti': containsThread
                             (updLockSet (updThread pfc (Kresume c Vundef) newThreadPerm)
                                         (b, Ptrofs.intval ofs) (emptyRes#1, emptyRes#2)) i)
              by (eapply cntUpdateL; eapply cntUpdate; now eauto).
            assert (cntiF': containsThread
                              (updLockSet
                                 (updThread pff (Kresume cf Vundef)
                                            (computeMap (getThreadR pff)#1 virtueF#1,
                                             computeMap (getThreadR pff)#2 virtueF#2))
                                 (b2, Ptrofs.intval ofs)
                                 (projectMap (fp i pfc) emptyRes#1,
                                  projectMap (fp i pfc) emptyRes#2)) i)
              by (eapply cntUpdateL; eapply cntUpdate; now eauto).
            pose proof (compat_th _ _ HmemCompC' cnti').1 as Hltc.
            rewrite gLockSetRes in Hltc.
            rewrite gssThreadRes in Hltc.
            simpl in Hltc.
            pose proof (compat_th _ _ HmemCompF'' cntiF').1 as HltF.
            rewrite gLockSetRes in HltF.
            rewrite gssThreadRes in HltF.
            simpl in HltF.
            specialize (Hstrong_tsim i cnti' cntiF').
            rewrite Hsynced in Hstrong_tsim.
            destruct Hstrong_tsim as [tpc' [mc'0 [_ [Heq [Hexec_eq [Hstrong_tsim _]]]]]].
            specialize (Heq ltac:(reflexivity)).
            erewrite <- Heq in *.
            inversion Hexec_eq; subst. clear Hexec_eq.
            specialize (Hstrong_tsim cnti' HmemCompC').
            destruct Hstrong_tsim as [_ ?].
            
            eapply @delta_content_inj_correct with (Hltc := Hltc)
                                                   (Hltf := HltF);
              eauto.
            (* Proof of delta_inj *)
            { repeat (split).
            * intros.
              erewrite <- projectAngel_correct with (b := b0) by eauto.
              simpl.
              destruct (vT1 ! b0) eqn:HvT1; auto.
            * intros b0 Hf0.
              assert (Hinvalid: ~ Mem.valid_block mc b0).
              { destruct (HsimWeak _ pfc pff).
                destruct weak_tsim_data0.
                intros Hcontra.
                eapply domain_valid0 in Hcontra.
                destruct Hcontra.
                congruence.
              }
              destruct (vT1 ! b0) eqn:HvT1; auto.
              intros ofs0.
              destruct (o ofs0) eqn:Hofs0; auto.
              eapply Hvb' in Hinvalid.
              eapply @mem_compatible_invalid_block with (ofs := ofs0) in Hinvalid; eauto.
              destruct Hinvalid.
              assert (pfc': containsThread
                              (updLockSet (updThread pfc (Kresume c Vundef) newThreadPerm)
                                          (b, Ptrofs.intval ofs) (empty_map, empty_map)) i).
              { eapply cntUpdateL; eapply cntUpdate; eauto. }
              specialize (H _ pfc').
              rewrite gLockSetRes gssThreadRes in H.
              simpl in H.
              erewrite computeMap_1 in H by eauto.
              destruct H. subst.
              auto.
            * intros.
              erewrite projectAngel_correct_2 by eauto.
              reflexivity.
            }
            assert (HeqC:restrPermMap Hltc = (restrPermMap (compat_th _ _ HmemCompC' cnti')#1)).
            { erewrite restrPermMap_irr; eauto.
              rewrite gLockSetRes gssThreadRes.
              reflexivity.
            }
            assert (HeqF:restrPermMap HltF = (restrPermMap (compat_th _ _ HmemCompF'' cntiF')#1)).
            { erewrite restrPermMap_irr; eauto.
              rewrite gLockSetRes gssThreadRes.
              reflexivity.
            }
            rewrite HeqC HeqF.
            assumption.
            simpl in HschedN.
            discriminate.
    }
    { (** Lock release case *)
      (** In order to construct the new memory we have to perform the
        load and store of the lock, after setting the correct permissions*)
      (** We prove that b is valid in m1 (and mc)*)
      assert (Hvalidb: Mem.valid_block m0 b)
        by (eapply load_valid_block; eauto).
      rewrite <- Hrestrict_pmap0 in Hvalidb.
      (** and compute the corresponding block in mf *)
      destruct ((domain_valid (weak_obs_eq (obs_eq_data Htsim))) _ Hvalidb)
        as [b2 Hfb].
      assert (Hvalidb2 := (codomain_valid (weak_obs_eq (obs_eq_data Htsim))) _ _ Hfb).
      erewrite restrPermMap_valid in Hvalidb2.
      (** we compute the [access_map] that we will use to perform the load*)
      remember (restrPermMap (compat_th _ _ (mem_compf Hsim) pff).2) as mf0 eqn:Hrestrict_pmapF.
      subst m1 m0.
      (** and prove that loading from that block in mf gives us the
        same value as in mc, i.e. unlocked*)
      assert (HloadF: Mem.load Mint32 mf0 b2 (Ptrofs.intval ofs) = Some (Vint Int.zero)).
      { subst mf0.
        destruct (load_val_obs _ _ _ Hload Hfb Hinjective ((strong_obs_eq (obs_eq_locks Htsim))))
          as [v2 [Hloadf Hobs_eq]].
        inversion Hobs_eq; subst.
          by auto.
      }
      assert (Hval_obs: val_obs (fp i pfc) (Vint Int.one) (Vint Int.one))
        by constructor.
      (** we then compute the [access_map] used to perform the store*)
      remember (setPermBlock (Some Writable) b2 (Ptrofs.intval ofs) (getThreadR pff).2 lksize.LKSIZE_nat)
        as pmap_tidF' eqn:Hset_permF.
      (** prove that this map is below the [Max] [access_map] of the memory*)
      assert (HltF': permMapLt pmap_tidF' (getMaxPerm mf)).
      {
        subst.
        eapply setPermBlock_lt; eauto.
        eapply (compat_th _ _ (mem_compf Hsim) pff).2.
      }

      (** the updated (with [Writable] permissions on the lock location) map is in [mem_obs_eq]*)
      assert (Hobs_eq_locks: mem_obs_eq (fp i pfc) (restrPermMap Hlt') (restrPermMap HltF')).
      { subst.
        apply Mem.load_valid_access in Hload.
        destruct Hload as [Hload _]. simpl in Hload.
        pose proof (obs_eq_locks Htsim).
        eapply setPermBlock_obs_eq with (Hlt := (compat_th _ _ HmemCompC pfc).2); eauto.
        intros.
        eapply (val_obs_eq (strong_obs_eq H));
          by eauto.
      }

      (** and then storing gives us related memories*)
      assert (HstoreF := store_val_obs _ _ _ Hstore Hfb Hval_obs Hobs_eq_locks).
      destruct HstoreF as [mf' [HstoreF HsimLocks']].
      (** We have that the core of the fine grained execution
            is related to the one of the coarse-grained*)
      assert (Hcore_inj:= code_eq Htsim).
      rewrite Hcode in Hcore_inj.
      simpl in Hcore_inj.
      subst.
      destruct (getThreadC pff) as [? | cf |? | ?] eqn:HcodeF;
        try by exfalso.
      (** And now we can prove that cf is also at external *)
      assert (Hat_external_spec := core_inj_ext _ _  Hfg Hge_wd Hge_incr Hvalid_mem' Hcore_inj (obs_eq_data Htsim)).
      rewrite Hat_external in Hat_external_spec.
      destruct (at_external semSem cf (restrPermMap (compat_th _ _ (mem_compf Hsim) pff)#1))
        as [[?  vsf] | ] eqn:Hat_externalF;
        try by exfalso.
      (** and moreover that it's the same external and their
            arguments are related by the injection*)
      destruct Hat_external_spec as [? Harg_obs]; subst.
      inversion Harg_obs as [|? ? ? ? Hptr_obs Hl]; subst.
      inversion Hl; subst.
      inversion Hptr_obs as [| | | |b1 bf ofs0 Hf|];
        subst b1 ofs0 v'.
      assert (bf = b2)
        by (rewrite Hf in Hfb; by inversion Hfb);
        subst bf.
      (** To compute the new fine grained state, we apply the
        renaming to the resources the angel provided us*)
      pose (projectAngel (fp i pfc) virtueThread.1, projectAngel (fp i pfc) virtueThread.2) as virtueF.
      remember (updThread pff (Kresume cf Vundef)
                          (computeMap (getThreadR pff).1 virtueF.1, computeMap (getThreadR pff).2 virtueF.2))
        as tpf' eqn:Htpf'.
      (** And also apply the renaming to the resources that go to the lockpool*)
      remember (projectMap (fp i pfc) virtueLP.1, projectMap (fp i pfc) virtueLP.2) as virtueLPF eqn:HvirtueLPF.
      (** We prove that the mapped block is a lock*)
      assert (HresF: lockRes tpf (b2, Ptrofs.intval ofs))
        by (eapply Hlock_if; eauto; rewrite HisLock; auto).
      destruct (lockRes tpf (b2, Ptrofs.intval ofs)) as [pmapF|] eqn:HisLockF;
        try by exfalso.
      destruct (HsimRes _ _ _ _ _ Hfb HisLock HisLockF) as [HsimRes1 HsimRes2].

      assert (HangelF1: permMapJoin (computeMap (getThreadR pff).1 virtueF.1) virtueLPF.1 (getThreadR pff).1).
      { assert (Hcanonical: isCanonical virtueLP.1)
          by (destruct (@compat_lp _ _ _ _ HmemCompC' (b, Ptrofs.intval ofs) virtueLP
                                   ltac:(rewrite gsslockResUpdLock; reflexivity));
              eapply canonical_lt; eauto).
        pose proof (obs_eq_data Htsim) as Hmem_obs_eq.
        pose proof (perm_obs_strong (strong_obs_eq Hmem_obs_eq)) as Hperm_eq.
        eapply permMapJoin_project with (f := fp i pfc) (pmap := newThreadPerm.1) (pmap' := virtueLP.1); eauto.
        unfold isCanonical in Hcanonical.
        intros b0 Hunmapped ofs0. subst.
        simpl. erewrite projectMap_correct_2 by eauto.
        erewrite computeMap_projection_2 by eauto.
        right.
        rewrite Hcanonical. split; reflexivity.
        subst virtueF.
        intros. simpl.
        erewrite computeMap_projection_1 by eauto;
          now reflexivity.
        intros. subst.
        erewrite projectMap_correct by eauto;
          now reflexivity.
        intros b1 b0 ofs0 Hrenaming;
          specialize (Hperm_eq _ _ ofs0 Hrenaming); rewrite! restrPermMap_Cur in Hperm_eq;
            auto.
      }

      assert (HangelF2: permMapJoin (computeMap (getThreadR pff).2 virtueF.2) virtueLPF.2 (getThreadR pff).2).
      { assert (Hcanonical: isCanonical virtueLP.2)
          by (destruct (@compat_lp _ _ _ _ HmemCompC' (b, Ptrofs.intval ofs) virtueLP
                                   ltac:(rewrite gsslockResUpdLock; reflexivity));
              eapply canonical_lt; eauto).
        pose proof (obs_eq_locks Htsim) as Hmem_obs_eq.
        pose proof (perm_obs_strong (strong_obs_eq Hmem_obs_eq)) as Hperm_eq.
        eapply permMapJoin_project with (f := fp i pfc) (pmap := newThreadPerm.2) (pmap' := virtueLP.2); eauto.
        unfold isCanonical in Hcanonical.
        intros b0 Hunmapped ofs0. subst.
        simpl. erewrite projectMap_correct_2 by eauto.
        erewrite computeMap_projection_2 by eauto.
        right.
        rewrite Hcanonical. split; reflexivity.
        subst virtueF.
        intros. simpl.
        erewrite computeMap_projection_1 by eauto;
          now reflexivity.
        intros. subst.
        erewrite projectMap_correct by eauto;
          now reflexivity.
        intros b1 b0 ofs0 Hrenaming;
          specialize (Hperm_eq _ _ ofs0 Hrenaming); rewrite! restrPermMap_Cur in Hperm_eq;
            auto.
      }

      (** for the release case we need to establish that the resources of the
      lock are empty*)
      assert(HpmapF: forall b ofs, pmapF.1 !! b ofs = None /\ pmapF.2 !! b ofs = None).
      { intros b0 ofs0.
        assert (Hb0: (exists b1, (fp i pfc) b1 = Some b0) \/
                     ~ (exists b1, (fp i pfc) b1 = Some b0))
          by eapply em.
        destruct Hb0 as [[b1 Hf1] | Hunmapped].
        - (** if b0 is mapped by some block*)
          pose proof (perm_obs_strong HsimRes1 _ ofs0 Hf1) as Hpmap1.
          pose proof (perm_obs_strong HsimRes2 _ ofs0 Hf1) as Hpmap2.
          rewrite! restrPermMap_Cur in Hpmap1 Hpmap2.
          erewrite Hpmap1, Hpmap2, (Hrmap b1 ofs0).1, (Hrmap b1 ofs0).2.
          split; reflexivity.
        - specialize (HunmappedRes _ _ _ HisLockF _ Hunmapped ofs0).
          assumption.
      }

      (** and that the thread has sufficient access permissions to the lock*)
      assert(HaccessF : Mem.range_perm (restrPermMap (compat_th _ _ (mem_compf Hsim) pff)#2) b2 (Ptrofs.intval ofs)
                                       (Ptrofs.intval ofs + lksize.LKSIZE) Cur Readable).
      { destruct Htsim.
        intros ofs' Hrange.
        destruct obs_eq_locks0 as [_ [Hperm_eq _]].
        unfold Mem.range_perm, permission_at, Mem.perm in *.
        erewrite Hperm_eq;
          by eauto.
      }
      
      (** and finally build the final fine-grained state*)
      remember (updLockSet tpf' (b2, Ptrofs.intval ofs) virtueLPF)
        as tpf'' eqn:Htpf'';
        symmetry in Htpf''.
      exists tpf'', mf', (fp i pfc), fp,
      (trf ++ [:: (external i (release (b2, Ptrofs.intval ofs)
                                     (Some (build_delta_content virtueF#1 mf'))))]).
      split.
      (** proof that the fine grained machine can step*)
      intros U.
      assert (HsyncStepF: syncStep false pff (mem_compf Hsim) tpf'' mf'
                                   (release (b2, Ptrofs.intval ofs)
                                            (Some (build_delta_content virtueF#1 mf'))))
        by (eapply step_release with (b0:=b2); now eauto).
      econstructor; simpl;
        by eauto.
      (* Proof that the new coarse and fine state are in simulation*)
      assert (HinvC':
                invariant (updLockSet
                             (updThread pfc (Kresume c Vundef) newThreadPerm)
                             (b, Ptrofs.intval ofs) virtueLP))
        by  (eapply StepLemmas.safeC_invariant with (n := fuelF.+1 + size xs); eauto).
      (** The new FineConc memory after storing still satisfies the [max_inv] invariant*)
      assert (HmaxF': max_inv mf')
        by (eapply max_inv_store; eauto).

      (** A useful result is that the virtueLP will be canonical*)
      assert (Hcanonical: isCanonical virtueLP.1 /\ isCanonical virtueLP.2).
      { clear - HmemCompC'.
        destruct HmemCompC'.
        destruct (compat_lp0 (b, Ptrofs.intval ofs) virtueLP
                               ltac:(erewrite gssLockRes; eauto)).
        split;
        eapply canonical_lt; eauto.
      }

      (** And the new FineConc threadPool and memory are [mem_compatible]*)
      assert (HmemCompF'' : mem_compatible tpf'' mf').
      { subst.
        eapply store_compatible; eauto.
        eapply mem_compatible_sync; eauto.
        unfold isCanonical.
        rewrite Hcanonical.1. reflexivity.
        unfold isCanonical.
        rewrite Hcanonical.2. reflexivity.
        eapply (mem_compf Hsim).
        eapply (codomain_valid (weak_obs_eq (obs_eq_data Htsim))).
      }
      subst.

      (** [mc] and [mc'] have the same valid blocks *)
      assert (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b).
      intros.
        by (intros;
            erewrite <- restrPermMap_valid with (Hlt := Hlt');
            split;
            [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
              by eauto).
        assert (Hvb': forall b, ~ Mem.valid_block mc b <-> ~ Mem.valid_block mc' b)
          by (intros; split; intros Hinvalid Hcontra;
                by apply Hvb in Hcontra).

        (** [mf] and [mf'] have the same valid blocks *)
        assert (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b)
          by (
              intros;
              erewrite <- restrPermMap_valid with (Hlt := HltF');
              split;
              [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
                by eauto).

      eapply Build_sim with (mem_compc := HmemCompC') (mem_compf := HmemCompF'').
      - (** containsThread *)
        clear - HnumThreads.
        intros j.
        split; intros cntj;
        eapply cntUpdateL;
        eapply cntUpdate;
        apply cntUpdateL' in cntj;
        apply cntUpdate' in cntj;
          by eapply HnumThreads.
      - (** safety of DryConc*)
        intros sched tr.
        eapply HybridCoarseMachine.csafe_trace;
          now eauto.
      - (** weak simulation between the two machines*)
        intros j pfcj' pffj'.
        assert (pfcj: containsThread tpc j)
          by auto.
        assert (pffj: containsThread tpf j)
          by auto.
        specialize (HsimWeak _ pfcj pffj).

        clear - Hvb Hvb' HvbF HstoreF Hstore HsimWeak Hsim newThreadPerm.
      (** Permissions on DryConc machine are higher than permissions on FineConc*)
          assert (Hlt:
                    forall (b1 b0 : block) (ofs0 : Z),
                      fp i pfc b1 = Some b0 ->
                      Mem.perm_order'' (permission_at (restrPermMap (compat_th _ _ HmemCompC' pfcj')#1) b1 ofs0 Cur)
                                       (permission_at (restrPermMap (compat_th _ _ HmemCompF'' pffj').1) b0 ofs0 Cur) /\
                      Mem.perm_order'' (permission_at (restrPermMap (compat_th _ _ HmemCompC' pfcj')#2) b1 ofs0 Cur)
                                       (permission_at (restrPermMap (compat_th _ _ HmemCompF'' pffj').2) b0 ofs0 Cur)).
          { intros b1 b0 ofs0 Hrenaming.
            pose proof (perm_obs_weak (weak_tsim_data HsimWeak)) as Hperm_data.
            pose proof (perm_obs_weak (weak_tsim_locks HsimWeak)) as Hperm_locks.
            specialize (Hperm_data _ _ ofs0 Hrenaming).
            specialize (Hperm_locks _ _ ofs0 Hrenaming).
            destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
            - (** this is the case where the angel has replaced some permissions*)
              subst j.
              Tactics.pf_cleanup.
              rewrite! restrPermMap_Cur gLockSetRes gssThreadRes;
                rewrite! gLockSetRes gssThreadRes.
              pose proof (injective (weak_tsim_data HsimWeak)).

              (** by case analysis on whether the angel changed the
              permission at this address*)
              assert (Hproject1: Maps.PTree.get b0 (projectAngel (fp i pfc) virtueThread.1) =
                                 Maps.PTree.get b1 virtueThread.1)
                by (symmetry; eapply projectAngel_correct; eauto).
              assert (Hproject2: Maps.PTree.get b0 (projectAngel (fp i pfc) virtueThread.2) =
                                 Maps.PTree.get b1 virtueThread.2)
                by (symmetry; eapply projectAngel_correct; eauto).
              split; simpl in *.
              + destruct (Maps.PTree.get b1 virtueThread.1) as [df|] eqn:Hdelta.
                * destruct (df ofs0) as [pnew |] eqn:Hdf.
                  rewrite (computeMap_1 _ _ _ _ Hdelta Hdf).
                  rewrite (computeMap_1 _ _ _ _ Hproject1 Hdf);
                    by eapply po_refl.
                rewrite (computeMap_2 _ _ _ _ Hdelta Hdf).
                rewrite (computeMap_2 _ _ _ _ Hproject1 Hdf);
                  by do 2 rewrite restrPermMap_Cur in Hperm_data.
                *  rewrite (computeMap_3 _ _ _ _ Hdelta).
                rewrite (computeMap_3 _ _ _ _ Hproject1);
                  by do 2 rewrite restrPermMap_Cur in Hperm_data.
              + destruct (Maps.PTree.get b1 virtueThread.2) as [df|] eqn:Hdelta.
                * destruct (df ofs0) as [pnew |] eqn:Hdf.
                  rewrite (computeMap_1 _ _ _ _ Hdelta Hdf).
                  rewrite (computeMap_1 _ _ _ _ Hproject2 Hdf);
                    by eapply po_refl.
                  rewrite (computeMap_2 _ _ _ _ Hdelta Hdf).
                  rewrite (computeMap_2 _ _ _ _ Hproject2 Hdf);
                    by do 2 rewrite restrPermMap_Cur in Hperm_locks.
                *  rewrite (computeMap_3 _ _ _ _ Hdelta).
                   rewrite (computeMap_3 _ _ _ _ Hproject2);
                     by do 2 rewrite restrPermMap_Cur in Hperm_locks.
            - erewrite! restrPermMap_Cur.
              assert (pfcj0: containsThread (updThread pfc (Kresume c Vundef) newThreadPerm) j)
                by (apply cntUpdate; auto).
              assert (pffj0: containsThread (updThread pff (Kresume cf Vundef)
                                                       (computeMap (getThreadR pff)#1 virtueF#1, computeMap (getThreadR pff)#2 virtueF#2)) j)
                by (apply cntUpdate; auto).
              erewrite gLockSetRes with (cnti := pfcj0).
              erewrite gLockSetRes with (cnti := pffj0).
              erewrite gsoThreadRes with (cntj := pfcj); eauto.
              erewrite gsoThreadRes with (cntj := pffj); eauto.
              split;
                [do 2 erewrite restrPermMap_Cur in Hperm_data |
                 do 2 erewrite restrPermMap_Cur in Hperm_locks];
                  by assumption. }

          destruct HsimWeak. destruct weak_tsim_data0.
          constructor; intros; constructor; intros; simpl;
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
            try (by specialize (codomain_valid0 _ _ H));
            destruct (Hlt _ _ ofs0 Hrenaming);
            eauto.
          (** Proof of seperation of injections *)
      - intros k j cntk' cntj' Hkj b0 b0' b3 b3' Hf0 Hf0' Hfk' Hfj'.
        assert (cntk: containsThread tpc k)
          by auto.
        assert (cntj: containsThread tpc j)
          by auto.
        erewrite cnt_irr with (cnt1 := cntk') (cnt2 := cntk) in Hfk'.
        erewrite cnt_irr with (cnt1 := cntj') (cnt2 := cntj) in Hfj'.
        eapply (HfpSep _ _ cntk cntj Hkj b0 b0');
          by eauto.
      - (** Proof of strong simulations after executing some thread*)
        intros.
        destruct (tid == i) eqn:Htid; move/eqP:Htid=>Htid; subst.
        { (** case of strong simulation for the thread that stepped*)
          exists (updLockSet
               (updThread pfc (Kresume c Vundef)
                          (computeMap (getThreadR pfc).1 virtueThread.1,
                           computeMap (getThreadR pfc).2 virtueThread.2))
               (b, Ptrofs.intval ofs) virtueLP), mc'.
          assert (pfc0 = pfc)
            by (eapply cnt_irr; eauto); subst pfc0.
          rewrite Hsynced.
          split; first by apply ren_incr_refl.
          split; first by auto.
          split; first by constructor.
          split.
          (** prof of [strong_tsim]*)
          intros.
          destruct Htsim as [_ Hmem_obs_eq_data Hmem_obs_eq_locks].
          constructor.
          rewrite! gLockSetCode.
          do 2 rewrite gssThreadCode;
            by (split; [assumption | constructor]).

          (** [mem_obs_eq] for data*)

          (** Need to massage goal a bit*)
          assert (Hlt1: permMapLt (computeMap (getThreadR pfc).1 virtueThread.1) (getMaxPerm mc')).
          { destruct mem_compc'.
            destruct (compat_th0 _ pfc').
            rewrite gLockSetRes  gssThreadRes in H.
            eauto.
          }

          erewrite restrPermMap_irr' with (Hlt' := Hlt1)
            by (rewrite gLockSetRes gssThreadRes; eauto).

          assert (Hlt1F: permMapLt (computeMap (getThreadR pff).1 virtueF.1) (getMaxPerm mf')).
          { destruct HmemCompF''.
            destruct (compat_th0 _ pff0).
            rewrite gLockSetRes  gssThreadRes in H.
            eauto.
          }
          erewrite restrPermMap_irr' with (Hlt' := Hlt1F)
            by (rewrite gLockSetRes gssThreadRes; eauto).

          eapply gss_mem_obs_eq_unlock with (Hlt2 := (compat_th _ _ HmemCompC pfc).1) (Hlt2F := (compat_th _ _ (mem_compf Hsim) pff).1)
                                                                          (rmapF := projectMap (fp i pfc) virtueLP#1);
            eauto; try reflexivity.
          try (erewrite! Mem.store_mem_contents by eauto).
          reflexivity.
          try (erewrite! Mem.store_mem_contents by eauto); reflexivity.
          intros b0 Hunmapped ofs0.
          erewrite projectMap_correct_2 by eauto.
          simpl.
          erewrite computeMap_projection_2 by eauto.
          rewrite Hcanonical.1. left; auto.
          intros; simpl; erewrite computeMap_projection_1 by eauto.
          reflexivity.
          intros; erewrite projectMap_correct by eauto.
          reflexivity.
          (** [mem_obs_eq] for locks*)

          (** Need to massage goal a bit*)
          assert (Hlt2: permMapLt (computeMap (getThreadR pfc).2 virtueThread.2) (getMaxPerm mc')).
          { destruct mem_compc'.
            destruct (compat_th0 _ pfc').
            rewrite gLockSetRes  gssThreadRes in H0.
            eauto.
          }
          erewrite restrPermMap_irr' with (Hlt' := Hlt2)
            by (rewrite gLockSetRes gssThreadRes; eauto).

          assert (Hlt2F: permMapLt (computeMap (getThreadR pff).2 virtueF.2) (getMaxPerm mf')).
          { destruct HmemCompF''.
            destruct (compat_th0 _ pff0).
            rewrite gLockSetRes  gssThreadRes in H0.
            eauto.
          }
          erewrite restrPermMap_irr' with (Hlt' := Hlt2F)
            by (rewrite gLockSetRes gssThreadRes; eauto).
          eapply gss_mem_obs_eq_unlock with
              (Hlt2 := (compat_th _ _ HmemCompC pfc).2)
              (Hlt2F := (compat_th _ _ (mem_compf Hsim) pff).2)
                                        (rmapF := projectMap (fp i pfc) virtueLP#2);
            try (erewrite! Mem.store_mem_contents by eauto);
            eauto; try reflexivity.
          intros b0 Hunmapped ofs0.
          erewrite projectMap_correct_2 by eauto.
          simpl.
          erewrite computeMap_projection_2 by eauto.
          rewrite Hcanonical.2. left; auto.
          intros; simpl; erewrite computeMap_projection_1 by eauto.
          reflexivity.
          intros; erewrite projectMap_correct by eauto.
          reflexivity.

          (** rest of strong sim*)
          split; first by congruence.
            split; first by congruence.
            rewrite gLockSetRes gssThreadRes;
              simpl; intros; rewrite! computeMap_projection_2;
            eauto.
          }
          { (**strong simulation for another thread*)
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
                  & Hownedj & Hownedj_lp & Hunmapped_j).
            (** first we prove that i is a valid thread after executing thread j*)
            assert (pfcij:= containsThread_internal_execution Hexecj pfc).

            (** Proof Sketch: Basically the proof we want is that changing some
            non-observable part of the state/memory should not affect the
            execution of thread j. To avoid giving yet another definition of
            equivalence of the observable state we re-use our strong
            injections/renamings. Steps:

            1. For the core and data resources, the original state <tpc,mc> will
            strongly inject with the id injection in the state <tpc', mc'> where
            we have updated the value of the lock and the resource maps
            according to the angel.

            2. Hence if <tpc,mc> takes internal steps to get to <tpcj, mcj> so
            will <tpc',mc'> to go to a new state <tpcj',mcj'>. Moreover
            <tpcj,mcj> will inject to <tpcj',mcj'> with the id injection. We had
            to strengthen our lemmas and corestep_obs_eq to obtain that last
            part.

            3. We use [strong_tsim_id_trans] to get that <tpcj',mcj'> will
               strongly inject in <tpf,mf> with the same injection as
               <tpcj,mcj>.

            4. Finally we prove that changing the state/memory in (TODO: add
            lemma name) non-observable parts retains the [strong_tsim] relation.
            *)

            (** Step 1*)
            assert (pfcjj: containsThread tpcj tid)
              by (eapply containsThread_internal_execution; eauto).
            assert (Hcompj: mem_compatible tpcj mcj)
              by (eapply internal_execution_compatible with (tp := tpc); eauto).
            specialize (Htsimj pfcjj Hcompj).

            (** We prove that thread tid on the original state injects
            in thread tid after updating the lockpool and storing the
            lock value*)
            assert (Htsimj_id:
                      tp_wd (id_ren mc) tpc /\
                      ctl_inj (id_ren mc) (getThreadC pfcj) (getThreadC pfc0) /\
                      mem_obs_eq (id_ren mc) (restrPermMap (compat_th _ _ HmemCompC pfcj).1) (restrPermMap (compat_th _ _ HmemCompC' pfc0).1) /\
                      (Mem.nextblock mc = Mem.nextblock mc')).
            { split.
              eapply tp_wd_domain;
                by eauto using id_ren_domain.
              eapply strong_tsim_store_id; eauto.
              erewrite gLockSetRes.
              rewrite gsoThreadRes; eauto.
              erewrite gLockSetCode.
              rewrite gsoThreadCode; eauto.
              destruct HinvC.
              pose proof ((no_race_thr0 _ _ pfcj pfc Htid).1) as Hdisjoint.
              pose proof ((thread_data_lock_coh0 _ pfc ).1 _ pfcj) as Hcoh.
              left.
              apply setPermBlock_coherent; eauto.
              (** since thread i had a [Writable] data permission no other can have above [Nonempty]*)
              apply Mem.load_valid_access in Hload.
              destruct Hload as [Hload _].
              intros.
              specialize (Haccess ofs' H).
              unfold Mem.perm in Haccess.
              intros Hcontra.
              pose proof (restrPermMap_Cur (compat_th _ _ HmemCompC pfc).2 b ofs') as Hperm_at.
              unfold permission_at in Hperm_at.
              rewrite Hperm_at in Haccess.
              specialize (Hcoh b ofs').
              destruct ((getThreadR pfcj).1 # b ofs') as [p1|];
                destruct ((getThreadR pfc).2 # b ofs') as [p2|];
                simpl in Hcontra, Haccess; auto;
                  inversion Hcontra; inversion Haccess; subst;
                    simpl in Hcoh;
                    now auto.
              eapply tp_wd_domain;
                by eauto using id_ren_domain.
            }
            destruct Htsimj_id as [Htpc_id_wd [Hctlj_id [Hmem_obs_eqj_id Hnextblock]]].

            (** Step 2.*)
            assert (H := mem_obs_eq_execution _ _ _ _ _ HinvC' Hfg Hge_wd Hge_incr_id
                                              Hmemc_wd Htpc_id_wd Hctlj_id Hmem_obs_eqj_id Hexecj).
            destruct H as
                (tp2' & m2' & f' & Hexecj'& Hincrj' & Hsepj'
                 & Hnextblock' & Hinvj' & Htsimj' & Hid').
            destruct Htsimj' as (pf2j & pf2j' & Hcomp2 & Hcomp2' & Hctl_eqj' & Hmem_obs_eq').
            specialize (Hid' Hnextblock (id_ren_correct mc)).
            assert (f' = id_ren mcj)
              by ( pose ((mem_obs_eq_domain_ren Hmem_obs_eq'));
                   eapply is_id_ren; eauto); subst f'.
            exists tp2', m2'.
            erewrite cnt_irr with (cnt1 := pfc0) (cnt2 := pfcj).
            split; first by auto.
            split; first by auto.
            split; first by auto.
            split.
            (** strong thread simulation for j*)
            intros.
            Tactics.pf_cleanup.
            (** Step 3, we use transitivity of [mem_obs_eq] and [ctl_inj] *)
            assert (Htsim2j: ctl_inj (fp tid pfcj) (getThreadC pf2j') (getThreadC pffj) /\
                             mem_obs_eq (fp tid pfcj) (restrPermMap (compat_th _ _ Hcomp2' pf2j').1)
                                        (restrPermMap (compat_th _ _ (mem_compf Hsim) pffj).1)).
            { destruct Htsimj.
              eapply strong_tsim_id_trans
              with (f := fp tid pfcj) (Hcomp1 := Hcompj) (Hcomp1' := Hcomp2');
              eauto.
              destruct Hnextblock' as [[p [Hmcj Hm2']] | [Hmcj Hm2']];
              unfold Mem.valid_block;
              rewrite Hmcj Hm2' Hnextblock;
                by tauto.
            }

            (** Step 4*)
            destruct Htsim2j as [Hcodeq2j Hmem_obs_eq2j].
            constructor.
            rewrite gLockSetCode.
            rewrite gsoThreadCode;
              by auto.
            clear - Hmem_obs_eq2j HstoreF HinvF Htid HloadF HaccessF.
            assert (HeqRes: getThreadR pff0 = getThreadR pffj)
              by (rewrite gLockSetRes;
                   rewrite gsoThreadRes; auto).
            assert (Hlt : permMapLt (getThreadR pff0).1 (getMaxPerm mf))
            by (rewrite HeqRes; eapply (compat_th _ _ (mem_compf Hsim) pffj).1).
            eapply mem_obs_eq_storeF with (mf := mf) (Hlt :=  Hlt);
              eauto.
            apply Mem.load_valid_access in HloadF.
            pose proof (((thread_data_lock_coh _ HinvF) _ pff).1 _ pffj).
            pose proof (cntUpdateL' _ _ pff0) as pffj'.
            erewrite gLockSetRes with (cnti := pffj').
            erewrite gsoThreadRes with (cntj := pffj) by eauto.
            left.
            apply setPermBlock_coherent; eauto.
            intros ofs' Hrange Hcontra.
            specialize (HaccessF ofs' Hrange).
            unfold Mem.perm in HaccessF.
            specialize (H b2 ofs').
            pose proof (restrPermMap_Cur (compat_th _ _ (mem_compf Hsim) pff).2 b2 ofs') as Heq.
            unfold permission_at in Heq.
            rewrite Heq in HaccessF.
            destruct ((getThreadR pffj).1 # b2 ofs') as [p1|]; simpl in Hcontra;
              [| assumption];
              inversion Hcontra; subst;
              destruct ((getThreadR pff).2 # b2 ofs') as [p2|]; simpl in HaccessF;
                now auto.
            erewrite restrPermMap_irr' with (Hlt := Hlt)
                                            (Hlt' := (compat_th _ _ (mem_compf Hsim) pffj).1);
              eauto.
            rewrite HeqRes. reflexivity.

            pose proof (obs_eq_locks Htsimj).

            assert (HRj_eq: (getThreadR pf2j').2 = (getThreadR pfcjj).2).
            { erewrite <- internal_execution_locks_eq with (cntj := pfc0) by eauto.
              erewrite <- internal_execution_locks_eq with (cntj' := pfcjj) (cntj := pfcj) by eauto.
              rewrite gLockSetRes.
              erewrite gsoThreadRes by eauto;
                reflexivity.
            }

            assert (Hlt2C: permMapLt (getThreadR pfcjj).2 (getMaxPerm m2'))
              by ( rewrite <- HRj_eq;
                   eapply (compat_th _ _ Hcomp2' pf2j').2).
            erewrite restrPermMap_irr' with (Hlt' := Hlt2C) by eauto.

            assert (HRj_eqF: (getThreadR pff0)#2 = (getThreadR pffj)#2)
              by (rewrite gLockSetRes; erewrite gsoThreadRes with (cntj := pffj) by eauto;
                  reflexivity).

            assert (Hlt2F: permMapLt (getThreadR pffj).2 (getMaxPerm mf'))
              by (rewrite <- HRj_eqF; eapply (compat_th _ _ HmemCompF'' pff0).2).
            erewrite restrPermMap_irr' with (Hlt' := Hlt2F) by eassumption.

            (** some useful results*)

            (** the contents of [m2'] are equal to the contents of [mc'] for locations [Readable] by locks on thread [tid]*)
            assert (Hstable_mc2': forall b1 ofs1, Mem.perm_order' ((getThreadR pfcj).2 # b1 ofs1) Readable ->
                                             ZMap.get ofs1 (Mem.mem_contents mc') # b1 = ZMap.get ofs1 (Mem.mem_contents m2') # b1).
            { intros.
              erewrite <- internal_exec_disjoint_locks with (Hcomp := HmemCompC') (m := mc') (m' := m2') (pfj := pfc0); eauto.
              unfold Mem.perm.
              pose proof (restrPermMap_Cur (compat_th _ _ HmemCompC' pfc0).2 b1 ofs1) as Hpermj.
              unfold permission_at in Hpermj.
              rewrite Hpermj.
              rewrite gLockSetRes.
              erewrite gsoThreadRes with (cntj := pfcj) by eauto.
              assumption.
            }

            (** the contents of [mcj] are equal to the contents of [mc] for locations [Readable] by locks on thread [tid]*)
            assert (Hstable_mcj: forall b1 ofs1, Mem.perm_order' ((getThreadR pfcj).2 # b1 ofs1) Readable ->
                                            ZMap.get ofs1 (Mem.mem_contents mc) # b1 =
                                            ZMap.get ofs1 (Mem.mem_contents mcj) # b1).
            { intros.
              erewrite internal_exec_disjoint_locks
              with (Hcomp := HmemCompC) (pfj := pfcj) (m := mc) (tp := tpc) (tp' := tpcj); eauto.
              unfold Mem.perm in *.

              pose proof (restrPermMap_Cur (compat_th _ _ HmemCompC pfcj).2 b1 ofs1) as Hpermj.
              unfold permission_at in *.
              rewrite Hpermj. assumption.
            }

            assert (Hperm_eqj: forall b1 ofs1, (Mem.mem_access (restrPermMap (compat_th _ _ Hcompj pfcjj).2)) # b1 ofs1 Cur =
                                          (getThreadR pfcj).2 # b1 ofs1).
            { intros.
              pose proof (restrPermMap_Cur (compat_th _ _ Hcompj pfcjj).2 b1 ofs1) as Hpermjj.
              unfold permission_at in Hpermjj.
              rewrite Hpermjj.
              erewrite <- internal_execution_locks_eq with (cntj' := pfcjj) (cntj := pfcj) at 1
                by eauto.
              reflexivity.
            }


            (** **** We now apply [mem_obs_eq_disjoint_lock]*)
            eapply mem_obs_eq_disjoint_lock
            with (ofsl := Ptrofs.intval ofs) (bl1 := b)
                                          (bl2 := b2) (sz := size_chunk Mint32); eauto.
            (** valid blocks of [mcj] are the same [m2']*)
            intros. unfold Mem.valid_block in *.
            destruct Hnextblock' as [[p [Hnextj Hnext2]] | [Hnextj Hnext2]];
              rewrite Hnextj Hnext2 Hnextblock;
              split; now auto.

            (** [memval_obs_eq] of contents on updated lock*)
            intros ofs0 Hrange.
            (** thread i has lock access on this location by the read it
            succesfully performed, hence by coherence thread j cannot have
            [Writable] data permission on that location*)
            assert (Hlock_unwrittable: ~ Mem.perm (restrPermMap (compat_th _ _ HmemCompC' pfc0)#1) b ofs0 Cur Writable).
            { clear - Hload HinvC Hrange pfcj Htid.
              pose proof (((thread_data_lock_coh _ HinvC _ pfc).1) _ pfcj b ofs0) as Hcoh.
              apply Mem.load_valid_access in Hload.
              destruct Hload as [Hperm _].
              specialize (Hperm ofs0 Hrange).
              unfold Mem.perm in *.
              pose proof ((restrPermMap_Cur (compat_th _ _ HmemCompC' pfc0).1) b ofs0) as Hpermj'.
              pose proof ((restrPermMap_Cur (compat_th _ _ HmemCompC pfc).2) b ofs0) as Hpermi.
              unfold permission_at in *.
              rewrite Hpermi in Hperm.
              rewrite Hpermj'.
              rewrite gLockSetRes.
              erewrite gsoThreadRes with (cntj := pfcj) by eauto.
              intros Hcontra.
              destruct ((getThreadR pfcj).1 # b ofs0) as [p|]; try (by exfalso);
                destruct p; simpl in Hcontra; inversion Hcontra; subst;
                  destruct ((getThreadR pfc).2 # b ofs0) as [p|];
                  try (by exfalso); inversion Hcontra; subst.
            }

            (** and thus by [internal_exec_stable]*)
            erewrite <- internal_exec_stable with (m := mc') (Hcomp := HmemCompC') (pfi := pfc0); eauto.
            erewrite Mem.store_mem_contents with (m2 := mc') by eauto.
            erewrite Mem.store_mem_contents with (m2 := mf') by eauto.
            simpl.
            rewrite! Maps.PMap.gss.
            erewrite! setN_inside
              by (rewrite length_inj_bytes encode_int_length; simpl in Hrange; auto).
            destruct (List.nth_in_or_default (Z.to_nat (ofs0 - Ptrofs.intval ofs)) (inj_bytes (encode_int 4 (Int.unsigned Int.one))) Undef).
            apply inj_bytes_type in i0.
            destruct (List.nth (Z.to_nat  (ofs0 - Ptrofs.intval ofs)) (inj_bytes (encode_int 4 (Int.unsigned Int.one))) Undef); try by exfalso.
            now constructor.
            rewrite e. now constructor.
            eapply Mem.store_valid_block_1; eauto.
            (** the contents of [mcj] are equal to the contents of [mc] for locations [Readable] by locks on thread [tid]*)
            intros.
            unfold Mem.perm in H1.
            erewrite Hperm_eqj in H1.
            erewrite <- Hstable_mc2' by eauto.
            erewrite <- Hstable_mcj by eauto.
            (** we can now prove that for all lock locations that tid can access, other than the one updated, the contents will be equal*)
            erewrite Mem.store_mem_contents with (m2 := mc') by eauto.
            destruct H0 as [Hb_neq | [? Hofs_neq]].
            (** if b0 is not the block that was updated*)
            erewrite Maps.PMap.gso by eauto.
            reflexivity.
            (** if b0 is the updated block but ofs0 is not in the updated range*)
            subst.
            rewrite Maps.PMap.gss.
            erewrite Mem.setN_outside
              by (rewrite encode_val_length; eapply Intv.range_notin in Hofs_neq; eauto; simpl; omega).
            reflexivity.

            (** stability for contents of [mf] and [mf']*)
            intros b0 ofs0 Hneq Hreadable.
            erewrite Mem.store_mem_contents with (m2 := mf') by eauto.
            destruct Hneq as [Hb_neq | [? Hofs_neq]].
            (** if b0 is not the block that was updated*)
            erewrite Maps.PMap.gso by eauto.
            reflexivity.
            (** if b0 is the updated block but ofs0 is not in the updated range*)
            subst.
            rewrite Maps.PMap.gss.
            erewrite Mem.setN_outside
              by (rewrite encode_val_length; eapply Intv.range_notin in Hofs_neq; eauto; simpl; omega).
            reflexivity.
            eauto.
            split.
            (** thread ownership*)
            intros k pff2k Hjk b1 b0 ofs0 Hfj Hfi.
            destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
            { subst k.
              rewrite gLockSetRes.
              rewrite gssThreadRes; auto.
              assert (Hunmapped: ~ (exists b, (fp i pfc) b = Some b0)).
              { intros Hcontra.
                destruct Hcontra as [b3 Hcontra].
                assert (Hfj' := Hincrj _ _ Hcontra).
                assert (Heq := injective (weak_obs_eq (obs_eq_data Htsimj)) _ _ Hfj Hfj');
                  subst b3.
                  by congruence.
              }
              simpl.
              erewrite! computeMap_projection_2;
                by eauto.
            }
            { rewrite gLockSetRes.
              rewrite gsoThreadRes; auto.
              eapply Hownedj;
                by eauto.
            }
            split.
            (** lockpool ownership*)
            intros bl ofsl rmap0 b1 b0 ofs0 Hfj Hfi Hres.
            destruct (EqDec_address (b2, Ptrofs.intval ofs) (bl, ofsl)) as [Heq | Hneq].
            (** case rmap is the resource map updated by the angel*)
            inversion Heq; subst.
            rewrite gssLockRes in Hres. inversion Hres.
            assert (~ exists b, fp i pfc b = Some b0).
            { intros Hcontra.
              destruct Hcontra as [b' Hfb'].
              assert (Hfb'' := Hincrj _ _ Hfb').
              assert (b' = b1)
                by (eapply (injective (weak_obs_eq (obs_eq_data Htsimj)));
                     eauto). subst b'.
                by congruence.
            }
            simpl.
            erewrite! projectMap_correct_2 by eauto.
            rewrite Hcanonical.1 Hcanonical.2.
            split;
              reflexivity.
            (** case it is another resource map*)
            rewrite gsoLockRes in Hres; auto.
            rewrite gsoThreadLPool in Hres;
              by eauto.
            (** unmapped blocks are empty*)
            intros b0 Hunmapped ofs0.
            rewrite gLockSetRes.
            erewrite gsoThreadRes with (cntj := pffj) by eauto.
            eapply Hunmapped_j;
              by eauto.
          }
          (** Proof of [strong_mem_obs_eq] for lock pool*)
      - split.
        { intros bl1 bl2 ofs0 rmap1 rmap2 Hfi Hres1 Hres2.
          destruct (EqDec_address (b, Ptrofs.intval ofs) (bl1, ofs0)) as [Heq | Hneq].
            { (** case it is the released lock *)
              inversion Heq; subst.
              assert (bl2 = b2)
                by (rewrite Hfi in Hfb; by inversion Hfb).
              subst bl2.
              assert (Hperm_eq: forall b1 b0 ofs0, fp i pfc b1 = Some b0 ->
                                    permission_at (restrPermMap (compat_lp _ _ HmemCompF'' (b2, Ptrofs.intval ofs) _ Hres2)#1) b0 ofs0 Cur =
                                    permission_at (restrPermMap (compat_lp _ _ HmemCompC' (bl1, Ptrofs.intval ofs) _ Hres1)#1) b1 ofs0 Cur /\
                                    permission_at (restrPermMap (compat_lp _ _ HmemCompF'' (b2, Ptrofs.intval ofs) _ Hres2)#2) b0 ofs0 Cur =
                                    permission_at (restrPermMap (compat_lp _ _ HmemCompC' (bl1, Ptrofs.intval ofs) _ Hres1)#2) b1 ofs0 Cur).
              { intros.
                rewrite! restrPermMap_Cur.
                rewrite gssLockRes in Hres1.
                rewrite gssLockRes in Hres2.
                inversion Hres1; inversion Hres2.
                subst. simpl.
                split;
                  erewrite <- projectMap_correct by eauto;
                  reflexivity.
              }

              (** proof that the contents will be related by [memval_obs_eq]*)
              (** This case is more complicated than the respective acquire
                 case, because resources are transfered to the lockpool. Hence
                 permissions at some addresss may increase. If however,
                 permissions at these addresses are [Readable] then we know that
                 they were [Readable] by thread i*)
              assert(forall b1 b0 ofs0,
                        (fp i pfc) b1 = Some b0 ->
                        (Mem.perm (restrPermMap (compat_lp _ _ HmemCompC' (bl1, Ptrofs.intval ofs) _ Hres1)#1) b1 ofs0 Cur Readable \/
                         Mem.perm (restrPermMap (compat_lp _ _ HmemCompC' (bl1, Ptrofs.intval ofs) _ Hres1)#2) b1 ofs0 Cur Readable) ->
                        memval_obs_eq (fp i pfc) (ZMap.get ofs0 (Mem.mem_contents mc') # b1) (ZMap.get ofs0 (Mem.mem_contents mf') # b0)).
              { intros b1 b0 ofs0 Hrenaming Hperm.
                pose proof Hres1 as Hres1b.
                rewrite gssLockRes in Hres1b.
                inversion Hres1b; subst.
                pose proof (restrPermMap_Cur (compat_lp _ _ HmemCompC' (bl1, Ptrofs.intval ofs) _ Hres1)#1 b1 ofs0) as Hperm_1.
                pose proof (restrPermMap_Cur (compat_lp _ _ HmemCompC' (bl1, Ptrofs.intval ofs) _ Hres1)#2 b1 ofs0) as Hperm_2.
                unfold permission_at, Mem.perm in Hperm_1, Hperm_2, Hperm.
                rewrite Hperm_1 Hperm_2 in Hperm.
                (** case analysis on which map (data or lock) is above [Readable]*)
                destruct Hperm as [Hperm | Hperm].
                - specialize (Hangel1 b1 ofs0).
                  apply permjoin_comm in Hangel1.
                  apply permjoin_readable_if in Hangel1.
                  (** hence now we can use [mem_obs_eq] for thread i*)
                  pose proof (strong_obs_eq (obs_eq_data Htsim)) as Hstrong_obs_eq.
                  pose proof ((compat_th _ _ (store_compatible _ _ _ _ _ HmemCompC Hstore) pfc).1) as Hlt.
                  eapply strong_mem_obs_eq_store with (bl1 := bl1) (Hlt2 := Hlt); eauto.
                  erewrite Mem.store_mem_contents by eauto; reflexivity.
                  erewrite Mem.store_mem_contents by eauto; reflexivity.
                  unfold Mem.perm.
                  rewrite <- restrPermMap_Cur with (Hlt := Hlt) in Hangel1.
                  assumption.
                  assumption.
                - specialize (Hangel2 b1 ofs0).
                  apply permjoin_comm in Hangel2.
                  apply permjoin_readable_if in Hangel2.
                  (** hence now we can use [mem_obs_eq] for thread i*)
                  pose proof (strong_obs_eq (obs_eq_locks Htsim)) as Hstrong_obs_eq.
                  pose proof ((compat_th _ _ (store_compatible _ _ _ _ _ HmemCompC Hstore) pfc).2) as Hlt.
                  eapply strong_mem_obs_eq_store with (bl1 := bl1) (Hlt2 := Hlt); eauto.
                  erewrite Mem.store_mem_contents by eauto; reflexivity.
                  erewrite Mem.store_mem_contents by eauto; reflexivity.
                  unfold Mem.perm.
                  rewrite <- restrPermMap_Cur with (Hlt := Hlt) in Hangel2.
                  assumption.
                  assumption.
              }
              split;
                constructor; intros;
                  try (destruct (Hperm_eq b1 b0 ofs0 Hrenaming); by auto).
            }
            { (** case it's another lock*)
              assert ((b2, Ptrofs.intval ofs) <> (bl2, ofs0)).
              { clear - Hneq Hfi Hf Hfb Htsim.
                intros Hcontra; inversion Hcontra; subst.
                assert (b = bl1)
                  by (eapply (injective (weak_obs_eq (obs_eq_data Htsim))); eauto).
                subst;
                  by auto.
              }
                pose proof Hres1 as Hres1';
                  pose proof Hres2 as Hres2'.
                erewrite gsoLockRes, gsoThreadLPool in Hres1' by auto.
                erewrite gsoLockRes, gsoThreadLPool in Hres2' by auto.
                destruct (HsimRes _ _ _ _ _ Hfi Hres1' Hres2') as [Hsim1 Hsim2].
                split;
                  eapply strong_mem_obs_eq_store with (bl1 := b) (bl2 := b2); eauto;
                    try (erewrite Mem.store_mem_contents by eauto; reflexivity).
            }
          }
          split.
          (** proof that locks are mapped*)
          intros bl2 ofs0 Hres.
          destruct (EqDec_address (bl2, ofs0) (b2, Ptrofs.intval ofs)) as [Heq | Hneq].
          inversion Heq; subst.
          eexists;
            by eauto.
          erewrite gsoLockRes, gsoThreadLPool in Hres by auto.
          eapply Hlock_mapped;
            by eauto.
          (** proof that the two machines have the same locks*)
          { intros bl1 bl2 ofs0 Hfl1.
            destruct (EqDec_address (b, Ptrofs.intval ofs) (bl1, ofs0)).
            - inversion e; subst.
              assert (b2 = bl2)
                by (rewrite Hf in Hfl1; inversion Hfl1; subst; auto).
              subst.
              do 2 rewrite gsslockResUpdLock.
              split;
              auto.
            - erewrite gsolockResUpdLock by auto.
              assert ((b2, Ptrofs.intval ofs) <> (bl2, ofs0)).
              { intros Hcontra.
                inversion Hcontra; subst.
                specialize (Hinjective _ _ _ Hfl1 Hfb).
                subst; auto.
              }
              erewrite gsolockResUpdLock by eauto.
              do 2 rewrite gsoThreadLPool.
              eauto.
          }
      - (** proof that unmapped blocks are empty*)
          intros bl ofsl rmap0 Hres b0 Hunmapped ofs0.
          destruct (EqDec_address (b2, Ptrofs.intval ofs) (bl, ofsl)).
          + inversion e; subst.
            rewrite gsslockResUpdLock in Hres.
            inversion Hres; subst.
            simpl.
            erewrite! projectMap_correct_2 by auto.
            rewrite Hcanonical.1 Hcanonical.2.
            split; reflexivity.
          + erewrite gsolockResUpdLock in Hres by auto.
            rewrite gsoThreadLPool in Hres.
            eapply HunmappedRes;
              now eauto.
        - (** Proof of invariant preservation for fine-grained machine*)
          destruct Htsim.
          eapply invariant_project; eauto;
            by destruct Hcanonical.
        - (** Max permission invariant*)
          assumption.
        - (** new memory is well-defined*)
          eapply store_wd_domain with
              (m := (restrPermMap Hlt')); eauto.
            by simpl.
        - (** new tpc is well-defined*)
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
          specialize (Htpc_wd _ cntj);
            by auto.
        - (** ge is well-defined*)
          assumption.
        - (** ge spec*)
          split; assumption.
        - intros.
          apply cntUpdateL;
            apply cntUpdate;
              by eauto.
        - econstructor 2;
            eauto.
          destruct virtueLP as [vLP1 vLP2].
          assert (Hempty: forall b1 ofs, fp i pfc b1 = None ->
                                    (getThreadR pfc)#1 # b1 ofs = None /\
                                    (getThreadR pfc)#2 # b1 ofs = None).
          { intros.
            assert (Hinvalid: ~ Mem.valid_block mc b1).
            { destruct (HsimWeak _ pfc pff).
              destruct weak_tsim_data0.
              intros Hcontra.
              eapply domain_valid0 in Hcontra.
              destruct Hcontra.
              congruence.
            }
            eapply @mem_compatible_invalid_block with (ofs := ofs0) in Hinvalid; eauto.
            destruct Hinvalid.
            now eauto.
          }
          econstructor; eauto using projectAngel_correct;
          repeat (split);
          try (now eapply projectMap_correct).
          (*
          intros.
          apply extensionality.
          intros ofs0.
          specialize (Hangel1 b1 ofs0).
          erewrite (Hempty _ ofs0 H).1 in Hangel1.
          inversion Hangel1; subst.
          reflexivity.
          reflexivity.
          intros b0 Hnone.
          destruct Hnone as [ofs0 HvLP1F].
          destruct (em (exists b1, fp i pfc b1 = Some b0)); auto.
          exfalso.
          eapply projectMap_correct_2 with (pmap := vLP1) in H.
          simpl in Hcanonical.
          unfold isCanonical in Hcanonical.
          rewrite Hcanonical.1 in H.
          rewrite H in HvLP1F.
          now auto.
          (* second map *)
          intros.
          apply extensionality.
          intros ofs0.
          specialize (Hangel2 b1 ofs0).
          erewrite (Hempty _ ofs0 H).2 in Hangel2.
          inversion Hangel2; subst.
          reflexivity.
          reflexivity.
          intros b0 Hnone.
          destruct Hnone as [ofs0 HvLP2F].
          destruct (em (exists b1, fp i pfc b1 = Some b0)); auto.
          exfalso.
          eapply projectMap_correct_2 with (pmap := vLP2) in H.
          simpl in Hcanonical.
          unfold isCanonical in Hcanonical.
          rewrite Hcanonical.2 in H.
          rewrite H in HvLP2F.
          now auto. *)
          admit.
          admit.
          admit.
    }
    { (** Thread Spawn case *)
      subst.
      (** We have that the core of the FineConc machine
        is related to the one of the DryConc*)
      assert (Hcore_inj:= code_eq Htsim).
      rewrite Hcode in Hcore_inj.
      simpl in Hcore_inj.
      subst.
      destruct (getThreadC pff) as [? | cf |? | ?] eqn:HcodeF;
        try by exfalso.
      (** And now we can prove that cf is also at external *)
      assert (Hat_external_spec := core_inj_ext _ _ Hfg Hge_wd Hge_incr Hvalid_mem' Hcore_inj (obs_eq_data Htsim)).
      rewrite Hat_external in Hat_external_spec.
      destruct (at_external semSem cf (restrPermMap (compat_th _ _ (mem_compf Hsim) pff)#1))
        as [[? vsf] | ] eqn:Hat_externalF;
        try by exfalso.
      (** and moreover that it's the same external and their
        arguments are related by the injection*)
      destruct Hat_external_spec as [? Harg_obs]; subst.
      inversion Harg_obs as [|? vff argf vsf' Hptr_obs Hl]; subst.
      inversion Hl; subst.
      inversion H3; subst. clear H3.
      inversion Hptr_obs; subst.
      (** To compute the new fine grained state, we apply the
        renaming to the resources the angel provided us*)
      remember (projectAngel (fp i pfc) virtue1.1, projectAngel (fp i pfc) virtue1.2)
        as virtue1F eqn:Hvirtue1F.
      remember (projectAngel (fp i pfc) virtue2.1, projectAngel (fp i pfc) virtue2.2)
        as virtue2F eqn:Hvirtue2F.
      pose (computeMap (getThreadR pff).1 virtue1F.1, computeMap (getThreadR pff).2 virtue1F.2)
        as threadPermF'.
      pose (computeMap empty_map virtue2F.1, computeMap empty_map virtue2F.2) as newThreadPermF.
      remember (updThread pff (Kresume cf Vundef) threadPermF')
        as tpf_upd eqn:Htpf_upd.
      remember (addThread tpf_upd (Vptr b2 ofs) v' newThreadPermF)
        as tpf' eqn:Htpf'.

      (** we prove that the projected angel satisfies [permMapJoin]*)
      assert (HangelF1: permMapJoin newThreadPermF.1 threadPermF'.1 (getThreadR pff).1).
      { pose proof (obs_eq_data Htsim) as Hmem_obs_eq.
        eapply permMapJoin_project with (f := fp i pfc) (pmap := newThreadPerm.1) (pmap' := threadPerm'.1);
          eauto.
        intros b0 Hunmapped ofs0.
        subst; simpl.
        erewrite! computeMap_projection_2 by eauto.
        left; split;
          by eauto using empty_map_spec.
        subst; simpl; intros;
          by erewrite computeMap_projection_3 by eauto.
        subst; simpl; intros;
          by erewrite computeMap_projection_1 by eauto.
        intros b1 b0 ofs0 Hrenaming.
        pose proof (perm_obs_strong (strong_obs_eq Hmem_obs_eq) b1 ofs0 Hrenaming) as Hperm_eq.
        rewrite! restrPermMap_Cur in Hperm_eq.
        now auto.
      }

      assert (HangelF2: permMapJoin newThreadPermF.2 threadPermF'.2 (getThreadR pff).2).
      { pose proof (obs_eq_locks Htsim) as Hmem_obs_eq.
        eapply permMapJoin_project with (f := fp i pfc) (pmap := newThreadPerm.2) (pmap' := threadPerm'.2);
          eauto.
        intros b0 Hunmapped ofs0.
        subst; simpl.
        erewrite! computeMap_projection_2 by eauto.
        left; split;
          by eauto using empty_map_spec.
        subst; simpl; intros;
          by erewrite computeMap_projection_3 by eauto.
        subst; simpl; intros;
          by erewrite computeMap_projection_1 by eauto.
        intros b1 b0 ofs0 Hrenaming.
        pose proof (perm_obs_strong (strong_obs_eq Hmem_obs_eq) b1 ofs0 Hrenaming) as Hperm_eq.
        rewrite! restrPermMap_Cur in Hperm_eq.
        now auto.
      }

       (** we augment the renamings pool by assigning the ''generic'' renaming
      (fp i pfc) to the new thread - this is sensible as the new thread has not
      made any allocations yet *)
      exists tpf', mf, (fp i pfc),
      (@addFP _ fp (fp i pfc) (Vptr b ofs) arg newThreadPerm),
      (trf ++ [:: (external i (spawn (b2,Ptrofs.intval ofs) (Some (build_delta_content virtue1F#1 mf)) (Some (build_delta_content virtue2F#1 mf))))]).
      split.
      (** proof that the fine grained machine can step*)
      intros U.
      (** the argument to the spawn function is well formed *)
      assert (HargF: val_inject (Mem.flat_inj (Mem.nextblock mf)) v' v').
      { inversion H1; subst; auto.
        eapply (codomain_valid (weak_tsim_data (HsimWeak _ pfc pff))) in H.
        erewrite restrPermMap_valid in H.
        unfold Mem.flat_inj.
        econstructor.
        destruct (Coqlib.plt b0 (Mem.nextblock mf));
          [reflexivity |
           unfold Mem.valid_block in H;
           now exfalso].
        now rewrite Ptrofs.add_zero.
      } 
      assert (HsyncStepF: syncStep false pff (mem_compf Hsim) tpf' mf
                                   (spawn (b2,Ptrofs.intval ofs) (Some ((build_delta_content virtue1F#1 mf))) (Some (build_delta_content virtue2F#1 mf))))
        by (eapply step_create;
            now eauto).

      econstructor; now eauto.
      (** Proof that the new coarse and fine state are in simulation*)
      assert (HinvC': invariant
                        (addThread (updThread pfc (Kresume c Vundef) threadPerm')
                                   (Vptr b ofs) arg newThreadPerm))
        by  (eapply StepLemmas.safeC_invariant with (n := fuelF.+1 + size xs); eauto).

      (** The new FineConc threadPool and memory are related by [mem_compatible]*)
      assert (HmemCompF'' : mem_compatible tpf' mf)
        by (pose proof (codomain_valid (weak_obs_eq (obs_eq_data Htsim))); subst;
            pose proof (mem_compf Hsim);
            eapply mem_compatible_spawn; eauto).
      subst.

      (** The two threadPools have the same number of threads*)
      assert (Hnum: OrdinalPool.num_threads tpc = OrdinalPool.num_threads tpf)
          by (eapply OrdinalPool.contains_iff_num; eauto).
      eapply Build_sim with (mem_compc := HmemCompC') (mem_compf := HmemCompF'').
        - (** containsThread *)
          clear - HnumThreads Hnum.
          intros j.
          Transparent containsThread OrdinalPool.containsThread.
          split;
            intros cntj;
            apply cntAdd' in cntj;
            destruct cntj as [[cntj _] | Heq];
            try (apply cntAdd;
                 apply cntUpdate;
                 apply HnumThreads;
                   by apply cntUpdate' in cntj);
            try (unfold containsThread;
                 subst; simpl; unfold OrdinalPool.containsThread;
                 unfold OrdinalPool.latestThread, OrdinalPool.updThread;
                 simpl; rewrite Hnum;
                   by ssromega).
          Opaque containsThread OrdinalPool.containsThread.
        - (** safety of coarse machine*)
          intros sched tr.
          eapply HybridCoarseMachine.csafe_trace;
            now eauto.
        - (** weak simulation between the two machines*)
          clear - HsimWeak HnumThreads Htsim Hnum.
          intros j pfcj' pffj'.
          destruct (HsimWeak _ pfc pff) as [Hweak_data Hweak_locks];
            destruct Hweak_data as [? ? ? ? _].
          (** Permissions on DryConc are higher than permissions on FineConc *)
          assert (Hperm: forall b1 b0 ofs0, fp i pfc b1 = Some b0 ->
                                       Mem.perm_order'' (permission_at (restrPermMap (compat_th _ _ HmemCompC' pfcj')#1) b1 ofs0 Cur)
                                                        (permission_at (restrPermMap (compat_th _ _ HmemCompF'' pffj')#1) b0 ofs0 Cur) /\
                                       Mem.perm_order'' (permission_at (restrPermMap (compat_th _ _ HmemCompC' pfcj')#2) b1 ofs0 Cur)
                                                        (permission_at (restrPermMap (compat_th _ _ HmemCompF'' pffj')#2) b0 ofs0 Cur)).
          { (** there are three cases now, the thread that spawned, the
            spawned thread and any other thread *)
            intros b1 b0 ofs0 Hrenaming.
            rewrite! restrPermMap_Cur.
            assert (pfcj := cntAdd' _ _ _ pfcj').
            destruct pfcj as [[pfcj _] | pfcj].
            { (** case it's not the new thread *)
              assert (pffj: containsThread
                              (updThread pff (Kresume cf Vundef) threadPermF') j)
                by (apply cntUpdate;
                    apply cntUpdate' in pfcj;
                      by eapply HnumThreads).
              erewrite gsoAddRes with (cntj := pfcj); eauto.
              erewrite gsoAddRes with (cntj := pffj); eauto.
              (** By case analysis on whether j is the spawning thread
                  or some other thread *)
              destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
              - subst i.
                rewrite gssThreadRes.
                rewrite gssThreadRes.
                destruct Htsim.
                simpl; subst.
                erewrite! computeMap_projection_1 by eauto.
                split;
                  now apply po_refl.
              - assert (pfcj0 := cntUpdate' _ _ _ pfcj).
                assert (pffj0 := cntUpdate' _ _ _ pffj).
                erewrite gsoThreadRes with (cntj := pfcj0); eauto.
                erewrite gsoThreadRes with (cntj := pffj0); eauto.
                specialize (HsimWeak _ pfcj0 pffj0).
                clear - HsimWeak Hrenaming.
                destruct HsimWeak as [Hweak_data Hweak_locks].
                destruct Hweak_locks, Hweak_data.
                specialize (perm_obs_weak0 _ _ ofs0 Hrenaming).
                specialize (perm_obs_weak1 _ _ ofs0 Hrenaming).
                rewrite! restrPermMap_Cur in perm_obs_weak0 perm_obs_weak1;
                  split;
                  now assumption.
            }
            { (** case j is the new thread *)
              assert (pffj := cntAdd' _ _ _ pffj').
              destruct pffj as [[_ Hcontra] | pffj].
              subst. simpl in Hcontra.
              unfold OrdinalPool.latestThread in Hcontra.
              rewrite Hnum in Hcontra;
                by exfalso.
              subst.
              erewrite gssAddRes by eauto.
              erewrite gssAddRes by eauto.
              simpl; subst.
              erewrite! computeMap_projection_3 by eauto.
              split;
                now apply po_refl.
            }
          }
          constructor;
          constructor; intros;
          repeat
            (match goal with
             | [H: context[Mem.valid_block (restrPermMap _) _] |- _] =>
               erewrite restrPermMap_valid in H
             | [|- Mem.valid_block (restrPermMap _) _] =>
               erewrite restrPermMap_valid
             end); eauto;
            try (by specialize (codomain_valid0 _ _ H));
            now eapply Hperm.
        - (** Proof of seperation of injections *)
          intros k j cntk' cntj' Hkj b0 b0' b3 b3' Hf0 Hf0' Hfk' Hfj'.
          (** By a very annoying case analyses on thread j and k*)
          (** since thread i is already in the renamings pool we can derive a
              contradiction*)
          destruct (i == j) eqn:Hij; move/eqP:Hij=> Hij;
            first by (subst j; rewrite gsoAddFP in Hfj'; by congruence).
          (** likewise for thread k*)
          destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik;
            first by (subst k; rewrite gsoAddFP in Hfk'; by congruence).
          (** we now check whether j is the new thread or not*)
          assert (cntj := cntAdd' _ _ _ cntj').
          destruct cntj as [[cntj _] | cntj].
          + (** case j is an existing thread *)
            rewrite gsoAddFP in Hfj'.
            assert (cntk := cntAdd' _ _ _ cntk').
            destruct cntk as [[cntk _] | cntk].
            * (** case k is an existing thread *)
              rewrite gsoAddFP in Hfk'.
              eapply (HfpSep k j cntk cntj Hkj b0 b0');
                by eauto.
            * (** case k is the new thread *)
              subst k.
              erewrite gssAddFP in Hfk'; auto.
                by congruence.
          + (** case j is the new thread *)
            subst.
            erewrite gssAddFP in Hfj'; auto.
              by congruence.
        - (** Proof of strong simulations after executing some thread*)
          intros j pfcj' pffj'.
          (** by case analysis on whether tid is the new thread or not*)
          assert (pfcj := cntAdd' _ _ _ pfcj').
          destruct pfcj as [[pfcj _] | pfcj].
          + (** case j is an old thread*)
            assert (pffj: containsThread
                            (updThread pff (Kresume cf Vundef) threadPermF') j)
              by (apply cntUpdate;
                  apply cntUpdate' in pfcj;
                  eapply HnumThreads; eauto).
            destruct (j == i) eqn:Hj; move/eqP:Hj=>Hj; subst.
            { (** case j is the thread that did the spawn*)
              exists (addThread
                   (updThread pfc (Kresume c Vundef) threadPerm') (Vptr b ofs)
                   arg newThreadPerm), mc'.
              rewrite Hsynced.
              rewrite gsoAddFP.
              assert (pfc'' : containsThread (updThread pfc (Kresume c Vundef) threadPerm') i)
                by (eapply cntUpdate; eauto).
              assert (pff'' : containsThread (updThread pff (Kresume cf Vundef) threadPermF') i)
                by (eapply cntUpdate; eauto).
              split; first by apply ren_incr_refl.
              split; first by auto.
              split; first by constructor.
              split.
              intros.
              (** proof of [strong_tsim]*)
              destruct Htsim as [HcodeEq Hmem_obs_eq_data Hmem_obs_eq_locks].
              constructor.
              erewrite gsoAddCode with (cntj := pfcj); eauto.
              erewrite gsoAddCode with (cntj := pffj); eauto.
              rewrite Hcode HcodeF in HcodeEq.
              do 2 rewrite gssThreadCode.
              simpl in *;
                by (split; [auto | constructor]).
              (** [mem_obs_eq] for data permissions of the thread that did the spawn*)
              eapply mem_obs_eq_changePerm with (Hlt := (compat_th _ _ HmemCompC pfc)#1)
                                                  (HltF := (compat_th _ _ (mem_compf Hsim) pff)#1); eauto.
              intros.
              erewrite gsoAddRes with (cntj := pfc'').
              erewrite gsoAddRes with (cntj := pff'').
              rewrite! gssThreadRes.
              simpl.
              erewrite computeMap_projection_1;
                by eauto.
              intros b0 ofs0 Hreadable'.
              erewrite gsoAddRes with (cntj := pfc'') in Hreadable'.
              rewrite gssThreadRes in Hreadable'.
              simpl in Hreadable'.
              specialize (Hangel1 b0 ofs0).
              apply permjoin_readable_iff in Hangel1.
              eapply Hangel1;
                 by eauto.

              (** [mem_obs_eq] for lock permissions of the thread that did the spawn*)
              eapply mem_obs_eq_changePerm with (Hlt := (compat_th _ _ HmemCompC pfc)#2)
                                                  (HltF := (compat_th _ _ (mem_compf Hsim) pff)#2); eauto.
              intros.
              erewrite gsoAddRes with (cntj := pfc'').
              erewrite gsoAddRes with (cntj := pff'').
              rewrite! gssThreadRes.
              simpl.
              erewrite computeMap_projection_1;
                by eauto.
              intros b0 ofs0 Hreadable'.
              erewrite gsoAddRes with (cntj := pfc'') in Hreadable'.
              rewrite gssThreadRes in Hreadable'.
              simpl in Hreadable'.
              specialize (Hangel2 b0 ofs0).
              apply permjoin_readable_iff in Hangel2.
              eapply Hangel2;
                by eauto.

              (** block ownership for thread i*)
              repeat (split; try (intros; by congruence));
              (** unmapped blocks are empty*)
              erewrite gsoAddRes with (cntj := pff'');
              rewrite gssThreadRes;
              simpl;
              erewrite computeMap_projection_2 by eauto;
              eapply Hunmapped_ls;
                by eauto.
            }
            { (** case j is a thread different than i*)
              (** this case should be straight forward because the
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
               (** we prove that thread i will still be valid after executing thread j*)
               assert (pfcji := containsThread_internal_execution Hexecj pfc).
               (** the state will be the same as tpcj but with an extra thread*)
               exists (addThread (updThread pfcji
                                       (Kresume c Vundef) threadPerm')
                            (Vptr b ofs) arg newThreadPerm), mcj.
               assert (pfcjj := containsThread_internal_execution Hexecj pfcj0).
               assert (Hcompj: mem_compatible tpcj mcj)
                 by (eapply internal_execution_compatible with (tp := tpc); eauto).
               specialize (Htsimj pfcjj Hcompj).
               destruct Htsimj as [Hcode_eqj Hobs_eqj_data Hobs_eqj_locks].
               split; eauto.
               split; eauto.
               split.
               eapply addThread_internal_execution; eauto.
               apply updThread_internal_execution; eauto.
               eapply ThreadPoolWF.invariant_decr; eauto;
                 try (eapply permMapJoin_order; eauto).
               eapply mem_compatible_add;
                 by eauto.
               split.
               (** [strong_tsim]*)
               Tactics.pf_cleanup.
               intros.
               assert (pfcjj': containsThread
                                 (updThread pfcji (Kresume c Vundef) threadPerm') j)
                 by  (apply cntUpdate; auto).
               constructor.
               (* the simulation of cores is straightforward, we just
                  need to massage the containsThread proofs a bit *)
               erewrite gsoAddCode with (cntj := pfcjj'); eauto.
               rewrite gsoThreadCode; eauto.
               erewrite gsoAddCode with (cntj := pffj); eauto.
               rewrite gsoThreadCode;
                 by auto.
               (** [mem_obs_eq] for data*)
               erewrite restrPermMap_irr' with (Hlt' := (compat_th _ _ Hcompj pfcjj).1)
                 by (rewrite gsoAddRes gsoThreadRes; auto).
               erewrite restrPermMap_irr' with (Hlt' := (compat_th _ _ (mem_compf Hsim) pffj0).1)
                 by (rewrite gsoAddRes gsoThreadRes; auto).
               assumption.
               (** [mem_obs_eq] for locks*)
               erewrite restrPermMap_irr' with (Hlt' := (compat_th _ _ Hcompj pfcjj).2)
                 by (rewrite gsoAddRes gsoThreadRes; auto).
               erewrite restrPermMap_irr' with (Hlt' := (compat_th _ _ (mem_compf Hsim) pffj0).2)
                 by (rewrite gsoAddRes gsoThreadRes; auto).
               assumption.
               split.
               (** block ownership*)
               intros k pffk' Hjk b0 b2' ofs0 Hfk Hfi.
               (** block b2 won't be mapped by fi*)
               assert (Hunmapped: ~ (exists b, (fp i pfc) b = Some b2')).
               { intros Hcontra.
                 destruct Hcontra as [b3 Hcontra].
                 assert (Hfj' := Hincrj _ _ Hcontra).
                 assert (Heq := injective (weak_obs_eq Hobs_eqj_data) _ _ Hfk Hfj');
                   subst b3.
                   by congruence.
               }
               assert (pfck := cntAdd' _ _ _ pffk').
               destruct pfck as [[pfck _] | pfck].
               (** case k is an old thread*)
               assert (pffk: containsThread
                               (updThread pff (Kresume cf Vundef) threadPermF') j)
                 by (apply cntUpdate; auto).
               erewrite gsoAddRes with (cntj := pfck); eauto.
               destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
               subst k.
               rewrite gssThreadRes.
               simpl.
               erewrite! computeMap_projection_2;
                 by eauto.
               rewrite gsoThreadRes; auto.
               eapply Hownedj;
                 by eauto.
               (** case k is the new thread*)
               subst k.
               erewrite gssAddRes; eauto.
               simpl.
               erewrite! computeMap_projection_2 by eauto;
                 split;
                   by apply empty_map_spec.
               split.
               intros b0 b2' ofs0 Hfj Hfi.
               intros ofs1 ? ? Hres.
               rewrite gsoAddLPool in Hres.
               rewrite gsoThreadLPool in Hres;
                 by eauto.
               (** unmapped blocks*)
               intros b0 Hunmapped ofs0.
               erewrite gsoAddRes with (cntj := pffj).
               erewrite gsoThreadRes with (cntj := pffj0) by eauto.
               now eauto.
            }
          + (** case j is the new thread*)
            (** in this case there will not be any internal steps, from
            invariant Hxs*)
            exists (addThread
                 (updThread pfc (Kresume c Vundef) threadPerm') (Vptr b ofs) arg
                 newThreadPerm), mc'.
            subst j.
            rewrite gssAddFP; eauto.
            split; first by eapply ren_incr_refl.
            split; eauto.
            rewrite not_in_filter.
            split; first by constructor.
            split.
            (** strong_tsim for the new thread*)
            intros ? Hcompj'.
            Tactics.pf_cleanup.
            constructor.
            erewrite gssAddCode; eauto.
            erewrite gssAddCode; eauto.
            simpl; eauto.
            unfold latestThread. simpl.
            unfold OrdinalPool.latestThread. simpl.
            apply f_equal;
              by auto.
            (** [mem_obs_eq] for data of new thread*)
            eapply mem_obs_eq_changePerm with (Hlt := (compat_th _ _ HmemCompC pfc).1)
                                              (HltF := (compat_th _ _ (mem_compf Hsim) pff).1).
            rewrite! gssAddRes.
            intros; simpl;
              erewrite computeMap_projection_3 by eauto.
            reflexivity.
            unfold latestThread. simpl.
            pose proof (OrdinalPool.contains_iff_num HnumThreads).
            unfold OrdinalPool.latestThread. simpl.
            apply f_equal; auto.
            unfold latestThread. simpl.
            unfold OrdinalPool.latestThread. reflexivity.
            now apply (obs_eq_data Htsim).
            intros.
            eapply permMapJoin_order with (b := b0) (ofs := ofs0) in Hangel1; eauto.
            erewrite gssAddRes in H by (unfold latestThread; reflexivity).
            destruct Hangel1 as [? _].
            erewrite po_oo in *.
            eapply po_trans;
              now eauto.
            (** [mem_obs_eq] for locks of new thread*)
            eapply mem_obs_eq_changePerm with (Hlt := (compat_th _ _ HmemCompC pfc).2)
                                              (HltF := (compat_th _ _ (mem_compf Hsim) pff).2).
            rewrite! gssAddRes.
            intros; simpl;
              erewrite computeMap_projection_3 by eauto.
            reflexivity.
            unfold latestThread. simpl.
            pose proof (OrdinalPool.contains_iff_num HnumThreads).
            unfold OrdinalPool.latestThread. simpl.
            apply f_equal; auto.
            reflexivity.
            now apply (obs_eq_locks Htsim).
            intros.
            eapply permMapJoin_order with (b := b0) (ofs := ofs0) in Hangel2; eauto.
            erewrite gssAddRes in H by (unfold latestThread; reflexivity).
            destruct Hangel2 as [? _].
            erewrite po_oo in *.
            eapply po_trans;
              now eauto.
            split.
            intros; by congruence.
            split.
            intros; by congruence.
            (** unmapped blocks *)
            intros.
            rewrite gssAddRes.
            simpl.
            erewrite! computeMap_projection_2 by eauto.
            split;
              now apply empty_map_spec.
            unfold latestThread. simpl.
            unfold OrdinalPool.latestThread. simpl.
            pose proof (OrdinalPool.contains_iff_num HnumThreads).
            apply f_equal; auto.
            intros Hin.
            specialize (Hxs _ Hin).
            clear - Hxs.
            Transparent containsThread OrdinalPool.containsThread.
            unfold containsThread in Hxs. simpl in Hxs.
            unfold OrdinalPool.containsThread, OrdinalPool.latestThread in Hxs.
            simpl in Hxs;
              by ssromega.
            Opaque containsThread  OrdinalPool.containsThread.
        - (** lock resource simulation *)
          split.
          + intros bl1 bl2 ofs0 rmap1 rmap2 Hf Hl1 Hl2.
            assert (Hl1' : lockRes tpc (bl1, ofs0) = Some rmap1)
              by (rewrite gsoAddLPool gsoThreadLPool in Hl1; auto).
            assert (Hl2' : lockRes tpf (bl2, ofs0) = Some rmap2)
              by (rewrite gsoAddLPool gsoThreadLPool in Hl2; auto).
            specialize (HsimRes _ _ _ _ _ Hf Hl1' Hl2').
            destruct HsimRes as [HsimRes1 HsimRes2].
            split.
            erewrite restrPermMap_irr' with (Hlt' := (compat_lp _ _ HmemCompC (bl1, ofs0) _ Hl1')#1) by eauto.
            erewrite restrPermMap_irr' with (Hlt' := (compat_lp _ _ (mem_compf Hsim) (bl2, ofs0) _ Hl2')#1) by eauto.
            now assumption.
            erewrite restrPermMap_irr' with (Hlt' := (compat_lp _ _ HmemCompC (bl1, ofs0) _ Hl1')#2) by eauto.
            erewrite restrPermMap_irr' with (Hlt' := (compat_lp _ _ (mem_compf Hsim) (bl2, ofs0) _ Hl2')#2) by eauto.
            now assumption.
          + split.
            * intros.
              rewrite gsoAddLPool gsoThreadLPool in H.
              eauto.
            * intros.
              do 2 rewrite gsoAddLPool gsoThreadLPool.
              eauto.
        - (** proof of unmapped blocks in resources*)
          intros.
          rewrite gsoAddLPool gsoThreadLPool in H.
          eauto.
        - (** proof of invariant *)
          destruct Htsim.
          eapply invariant_spawn;
          eauto.
        - assumption.
        - assumption.
        - clear - Htpc_wd Hcode Hat_external Hvalid_mem' Hdomain_f.
          intros j cntj'.
          assert (cntj := cntAdd' _ _ _ cntj').
          destruct cntj as [[cntj _] | cntj].
          + assert (cntj0 := cntUpdate' _ _ _ cntj).
            erewrite @gsoAddCode with (cntj := cntj); eauto.
            destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
            * subst.
              rewrite gssThreadCode.
              specialize (Htpc_wd _ cntj0).
              Tactics.pf_cleanup.
              rewrite Hcode in Htpc_wd.
              simpl in *;
                by auto.
            * rewrite gsoThreadCode;
                by auto.
          + subst.
            erewrite gssAddCode; eauto.
            simpl.
            assert (Hcore_wd := Htpc_wd _ pfc).
            rewrite Hcode in Hcore_wd. simpl in Hcore_wd.
            eapply at_external_wd in Hat_external; eauto.
            inversion Hat_external; subst.
            inversion H2; subst.
              by auto.
        - (** ge_wd *)
          assumption.
        - (** ge_spec *)
          split; assumption.
        - intros j Hin.
          specialize (Hxs _ Hin).
          apply cntAdd;
            by apply cntUpdate.
        - econstructor; eauto.
          econstructor; eauto.
          admit.
          (* + repeat (split).
            * intros.
              simpl.
              erewrite <- projectAngel_correct with (b := b0) by eauto.
              destruct (virtue2#1 ! b0) eqn:HvT1;
              rewrite HvT1.
              reflexivity.
              auto.
            * intros b0 Hf0.
              assert (Hinvalid: ~ Mem.valid_block mc' b0).
              { destruct (HsimWeak _ pfc pff).
                destruct weak_tsim_data0.
                intros Hcontra.
                eapply domain_valid0 in Hcontra.
                destruct Hcontra.
                congruence.
              }
              destruct (virtue2#1 ! b0) eqn:HvT1; rewrite HvT1; auto.
              intros ofs0.
              destruct (o ofs0) eqn:Hofs0; auto.
              eapply @mem_compatible_invalid_block with (ofs := ofs0) in Hinvalid; eauto.
              destruct Hinvalid.
              assert (pfc': containsThread
                              (addThread (updThread pfc (Kresume c Vundef) threadPerm')
                                         (Vptr b ofs) arg newThreadPerm)
                              (latestThread
                                 (updThread pfc (Kresume c Vundef) threadPerm')))
                by (eapply cntAddLatest).
               
              specialize (H  _ pfc').
              destruct H as [H _].
              erewrite gssAddRes in H by eauto.
              simpl in H.
              erewrite computeMap_1 in H by eauto.
              auto.
            * intros.
              simpl.
              erewrite projectAngel_correct_2 by eauto.
              reflexivity.
          +  repeat (split).
             * intros.
               simpl.
               erewrite <- projectAngel_correct with (b := b0) by eauto.
               destruct (virtue2#2 ! b0) eqn:HvT2;
                 rewrite HvT2.
               reflexivity.
               auto.
            * intros b0 Hf0.
              assert (Hinvalid: ~ Mem.valid_block mc' b0).
              { destruct (HsimWeak _ pfc pff).
                destruct weak_tsim_data0.
                intros Hcontra.
                eapply domain_valid0 in Hcontra.
                destruct Hcontra.
                congruence.
              }
              destruct (virtue2#2 ! b0) eqn:HvT2; rewrite HvT2; auto.
              intros ofs0.
              destruct (o ofs0) eqn:Hofs0; auto.
              eapply @mem_compatible_invalid_block with (ofs := ofs0) in Hinvalid; eauto.
              destruct Hinvalid.
              assert (pfc': containsThread
                              (addThread (updThread pfc (Kresume c Vundef) threadPerm')
                                         (Vptr b ofs) arg newThreadPerm)
                              (latestThread
                                 (updThread pfc (Kresume c Vundef) threadPerm')))
                by (eapply cntAddLatest).
               
              specialize (H  _ pfc').
              destruct H as [_ H].
              erewrite gssAddRes in H by eauto.
              simpl in H.
              erewrite computeMap_1 in H by eauto.
              auto.
            * intros.
              simpl.
              erewrite projectAngel_correct_2 by eauto.
              reflexivity.   *)
          admit.
    }
    { (** Makelock case *)
      Opaque updThread.
      (** [b] is valid in [m1] (and [mc])*)
      assert (Hvalidb: Mem.valid_block m1 b).
      { eapply Mem.store_valid_access_3 in Hstore.
        eapply Mem.valid_access_valid_block; eauto.
        eapply Mem.valid_access_implies; eauto.
        constructor.
      }
      rewrite <- Hrestrict_pmap in Hvalidb.

      (** We compute the corresponding block in mf *)
      destruct ((domain_valid (weak_obs_eq (obs_eq_data Htsim))) _ Hvalidb)
        as [b2 Hfb].
      assert (Hvalidb2 := (codomain_valid (weak_obs_eq (obs_eq_data Htsim))) _ _ Hfb).
      erewrite restrPermMap_valid in Hvalidb2.

      (** consider [mf] with the permissions of thread i on FineConc*)
      remember (restrPermMap (compat_th _ _ (mem_compf Hsim) pff).1) as mf1 eqn:Hrestrict_pmapF.
      assert (Hval_obs: val_obs (fp i pfc) (Vint Int.zero) (Vint Int.zero))
        by constructor.
      (** [m1] and [mf1] are related by [mem_obs_eq] and storing related by
      [val_obs] values gives us related memories*)
      subst m1.
      destruct Htsim as [Hcore_inj Hmem_obs_eq_data Hmem_obs_eq_locks].
      assert (HstoreF := store_val_obs _ _ _ Hstore Hfb Hval_obs Hmem_obs_eq_data).
      destruct HstoreF as [mf' [HstoreF Hmem_obs_eq_data']].
      (** We have that the code of FineConc
        is related to the one of DryConc*)
      rewrite Hcode in Hcore_inj.
      simpl in Hcore_inj.
      destruct (getThreadC pff) as [? | cf |? | ?] eqn:HcodeF;
        try by exfalso.
      subst.
      (** And now we can prove that cf is also at external *)
      assert (Hat_external_spec := core_inj_ext _ _ Hfg Hge_wd Hge_incr Hvalid_mem' Hcore_inj Hmem_obs_eq_data).
      rewrite Hat_external in Hat_external_spec.
        destruct (at_external semSem cf (restrPermMap (compat_th _ _ (mem_compf Hsim) pff)#1))
        as [[? vsf] | ] eqn:Hat_externalF;
        try by exfalso.
      (** and moreover that it's the same external and their
        arguments are related by the renaming [fp i pfc]*)
      destruct Hat_external_spec as [? Harg_obs]; subst.
      inversion Harg_obs as [|? ? ? ? Hptr_obs Hl]; subst.
      inversion Hl; subst.
      inversion Hptr_obs as [| | | |b1 bf ofs0 Hf|];
        subst b1 ofs0 v'.
      assert (bf = b2)
        by (rewrite Hf in Hfb; by inversion Hfb);
        subst bf.
      (** we compute the new permissions on the thread*)
      remember (setPermBlock (Some Nonempty) b2 (Ptrofs.intval ofs) (getThreadR pff).1
                             lksize.LKSIZE_nat) as pmap_tidF' eqn:Hdata_permF.
      symmetry in Hdata_permF.
      remember (setPermBlock (Some Writable) b2 (Ptrofs.intval ofs) (getThreadR pff).2
                             lksize.LKSIZE_nat) as pmap_tidF2' eqn:Hlock_permF.
      symmetry in Hlock_permF.
      (** We prove that [(b2, Ptrofs.intval ofs)] is in [lockRes] of FineConc*)
      assert (hresF: lockRes tpf (b2, Ptrofs.intval ofs) = None).
      { pose proof ((Hlock_if _ _ (Ptrofs.intval ofs) Hf).2) as Hlock.
        rewrite HlockRes in Hlock.
        destruct (lockRes tpf (b2, Ptrofs.intval ofs));
          [exfalso; auto | reflexivity].
      }

      (** and that the thread has sufficient access permissions to the lock*)
      assert(HaccessF : Mem.range_perm (restrPermMap (compat_th _ _ (mem_compf Hsim) pff)#1) b2 (Ptrofs.intval ofs)
                                       (Ptrofs.intval ofs + lksize.LKSIZE) Cur Writable).
      { destruct Hmem_obs_eq_data as [ _ [Hperm_eq _]].
        intros ofs' Hrange.
        unfold Mem.range_perm, permission_at, Mem.perm in *.
        erewrite Hperm_eq;
          by eauto.
      }
      
      (** To compute the new state of the FineConc machine, we first update the thread*)
      remember (updThread pff (Kresume cf Vundef) (pmap_tidF', pmap_tidF2')) as tpf' eqn:Htpf'.
      (** And then update the [lockRes] with empty resources on that address. *)
      remember (updLockSet tpf' (b2, Ptrofs.intval ofs) (empty_map, empty_map)) as tpf'' eqn:Htpf'';
        symmetry in Htpf''.
      exists tpf'', mf', (fp i pfc), fp, (trf ++ [:: (external i (mklock (b2, Ptrofs.intval ofs)))]).
      split.
      (** proof that the FineConc machine can step*)
      intros U.
      assert (HsyncStepF: syncStep false pff (mem_compf Hsim) tpf'' mf' (mklock (b2, Ptrofs.intval ofs))). {
         eapply step_mklock with (b0:=b2); subst pmap_tidF' pmap_tidF2'; eauto; try reflexivity.
      }
      econstructor;
        by eauto.

      (** The [invariant] holds in the new DryConc state*)
      assert (HinvC':
                invariant (updLockSet (updThread pfc (Kresume c Vundef) pmap_tid')
                                      (b, Ptrofs.intval ofs) (empty_map, empty_map)))
        by  (eapply StepLemmas.safeC_invariant with (n := fuelF.+1 + size xs); eauto).
      (** The [max_inv] holds for thew new memory of FineConc*)
      assert (HmaxF': max_inv mf')
        by (eapply max_inv_store; eauto).
      (** The updated state of FineCond and the new memory are related by [mem_compatible]*)
      assert (HmemCompF'': mem_compatible tpf'' mf').
      { subst.
        clear - HmaxF' Hf Hvalidb2 HstoreF.
        constructor.
        - intros.
          rewrite gLockSetRes.
          unfold permMapLt.
          erewrite <- forall2_and.
          intros b0 ofs0.
          destruct (i == tid) eqn:Heq; move/eqP:Heq=>Heq.
          + subst. rewrite gssThreadRes.
            destruct (Pos.eq_dec b2 b0).
            * subst.
              assert (Hvalidb2' := Mem.store_valid_block_1 _ _ _ _ _ _
                                                           HstoreF b0 Hvalidb2).
              specialize (HmaxF' _ ofs0 Hvalidb2').
              rewrite getMaxPerm_correct.
              rewrite HmaxF'.
              simpl; split;
                match goal with
                | [|-match ?Expr with _ => _ end] =>
                  destruct Expr
                end;
                now constructor.
            * rewrite! setPermBlock_other_2; auto.
              erewrite <- mem_store_max by eauto.
              rewrite getMax_restr.
              split;
              now eapply (mem_compf Hsim).
          + erewrite <- mem_store_max by eauto.
            rewrite getMax_restr.
            erewrite! gsoThreadRes with (cntj := cntUpdate' _ _ _ (cntUpdateL' _  _ cnt))  by eauto.
            split;
            now eapply (mem_compf Hsim).
        - intros l rmap Hres.
          unfold permMapLt.
          erewrite <- forall2_and.
          intros b0 ofs0.
          destruct (EqDec_address (b2, Ptrofs.intval ofs) l).
          + inversion e; subst.
            rewrite gsslockResUpdLock in Hres.
            inversion Hres.
            rewrite empty_map_spec.
            destruct ((getMaxPerm mf') # b0 ofs0); simpl; auto.
          + erewrite gsolockResUpdLock in Hres by eauto.
            erewrite <- mem_store_max by eauto.
            rewrite gsoThreadLPool in Hres.
            rewrite getMax_restr.
            split;
              eapply (mem_compf Hsim);
              now eassumption.
        - intros l rmap Hres.
          destruct (EqDec_address (b2, Ptrofs.intval ofs) l).
          + subst.
            simpl.
            eapply Mem.store_valid_block_1;
              now eauto.
          + erewrite gsolockResUpdLock in Hres by eauto.
            rewrite gsoThreadLPool in Hres.
            eapply Mem.store_valid_block_1; eauto.
            eapply (mem_compf Hsim);
              now eassumption.
      }
      subst.

      assert (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b)
        by (
            intros;
            erewrite <- restrPermMap_valid with (Hlt := (compat_th _ _ HmemCompC pfc).1);
            split;
            [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
            eauto).
      assert (Hvb': forall b, ~ Mem.valid_block mc b <-> ~ Mem.valid_block mc' b)
        by (intros; split; intros Hinvalid Hcontra;
              by apply Hvb in Hcontra).
      assert (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b)
        by (
            intros;
            erewrite <- restrPermMap_valid with (Hlt := (compat_th _ _ (mem_compf Hsim) pff).1);
            split;
            [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
            eauto).

      (** Proof that the DryCond and FineConc machines are in simulation*)
      eapply Build_sim with (mem_compc := HmemCompC') (mem_compf := HmemCompF'').
      - (** containsThread *)
        clear - HnumThreads.
        intros j.
        split; intros cntj;
        eapply cntUpdateL;
        eapply cntUpdate;
        apply cntUpdateL' in cntj;
        apply cntUpdate' in cntj;
          by eapply HnumThreads.
      - (** safety of coarse machine*)
        intros sched tr.
        eapply HybridCoarseMachine.csafe_trace;
          now eauto.
      - (** weak simulation between the two machines*)
        intros j pfcj' pffj'.
        assert (pfcj: containsThread tpc j)
          by auto.
        assert (pffj: containsThread tpf j)
          by auto.
        specialize (HsimWeak _ pfcj pffj).
        clear - Hvb Hvb' HvbF HstoreF Hstore HsimWeak Hsim Hfb Hdata_perm Hlock_perm.

        assert (Hlt1': permMapLt (getThreadR pfcj).1 (getMaxPerm mc'))
          by (intros b0 ofs0;
              erewrite <- mem_store_max by eauto;
              rewrite getMaxPerm_correct;
              rewrite restrPermMap_Max;
              now apply HmemCompC;
              unfold permission_at;
              erewrite Mem.store_access by eauto).

        assert (Hlt1F': permMapLt (getThreadR pffj).1 (getMaxPerm mf'))
          by (intros b0 ofs0;
              erewrite <- mem_store_max by eauto;
              rewrite getMaxPerm_correct;
              rewrite restrPermMap_Max;
              now apply (mem_compf Hsim);
              unfold permission_at;
              erewrite Mem.store_access by eauto).

        assert (HltL': permMapLt (getThreadR pfcj).2 (getMaxPerm mc'))
          by (intros b0 ofs0;
              erewrite <- mem_store_max by eauto;
              rewrite getMaxPerm_correct;
              rewrite restrPermMap_Max;
              now apply HmemCompC;
              unfold permission_at;
              erewrite Mem.store_access by eauto).

        assert (HltLF': permMapLt (getThreadR pffj).2 (getMaxPerm mf'))
          by (intros b0 ofs0;
              erewrite <- mem_store_max by eauto;
              rewrite getMaxPerm_correct;
              rewrite restrPermMap_Max;
              now apply (mem_compf Hsim);
              unfold permission_at;
              erewrite Mem.store_access by eauto).

        (** By case analysis on whether thread j is the one that created the lock*)
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        + subst.
          Tactics.pf_cleanup.
          constructor.
          * (** [weak_mem_obs_eq] for data*)
            subst.
            assert (Hlt1: permMapLt (setPermBlock (Some Nonempty) b (Ptrofs.intval ofs) (getThreadR pfc)#1 lksize.LKSIZE_nat) (getMaxPerm mc'))
              by (pose proof (compat_th _ _ HmemCompC' pfcj') as Hlt;
                  rewrite gLockSetRes gssThreadRes in Hlt;
                  rewrite <- Hdata_perm in Hlt;
                destruct Hlt; assumption).
            assert (Hlt1F: permMapLt (setPermBlock (Some Nonempty) b2 (Ptrofs.intval ofs) (getThreadR pff)#1 lksize.LKSIZE_nat) (getMaxPerm mf'))
              by (pose proof (compat_th _ _ HmemCompF'' pffj') as Hlt;
                  rewrite gLockSetRes gssThreadRes in Hlt;
                  destruct Hlt; assumption).
            erewrite restrPermMap_irr' with (Hlt' := Hlt1)
              by (rewrite gLockSetRes gssThreadRes; rewrite <- Hdata_perm; reflexivity).
            erewrite restrPermMap_irr' with (Hlt' := Hlt1F)
              by (rewrite gLockSetRes gssThreadRes; reflexivity).
            destruct HsimWeak.
            eapply weak_mem_obs_eq_store with (Hlt2 := Hlt1') (Hlt2F := Hlt1F') in weak_tsim_data0; eauto.
            eapply setPermBlock_weak_obs_eq; eauto.
            now eapply (injective (weak_tsim_data0)).
          * (** [weak_mem_obs_eq] for locks*)
            subst.
            assert (Hlt2: permMapLt (setPermBlock (Some Writable) b
                                                  (Ptrofs.intval ofs) (getThreadR pfc)#2 lksize.LKSIZE_nat) (getMaxPerm mc'))
              by (pose proof (compat_th _ _ HmemCompC' pfcj') as Hlt;
                  rewrite gLockSetRes gssThreadRes in Hlt;
                  rewrite <- Hlock_perm in Hlt;
                  destruct Hlt; assumption).

            assert (Hlt2F: permMapLt (setPermBlock (Some Writable)
                                                   b2 (Ptrofs.intval ofs) (getThreadR pff)#2 lksize.LKSIZE_nat) (getMaxPerm mf'))
              by (pose proof (compat_th _ _ HmemCompF'' pffj') as Hlt;
                  rewrite gLockSetRes gssThreadRes in Hlt;
                  destruct Hlt; assumption).

            assert (Hlt2': permMapLt (getThreadR pfc).2 (getMaxPerm mc'))
              by (intros b0 ofs0;
                  erewrite <- mem_store_max by eauto;
                  rewrite getMaxPerm_correct;
                  rewrite restrPermMap_Max;
                  now apply HmemCompC;
                  unfold permission_at;
                  erewrite Mem.store_access by eauto).

            assert (Hlt2F': permMapLt (getThreadR pff).2 (getMaxPerm mf'))
              by (intros b0 ofs0;
                  erewrite <- mem_store_max by eauto;
                  rewrite getMaxPerm_correct;
                  rewrite restrPermMap_Max;
                  now apply (mem_compf Hsim);
                  unfold permission_at;
                  erewrite Mem.store_access by eauto).

            erewrite restrPermMap_irr' with (Hlt' := Hlt2)
              by (rewrite gLockSetRes gssThreadRes; rewrite <- Hlock_perm; reflexivity).
            erewrite restrPermMap_irr' with (Hlt' := Hlt2F)
              by (rewrite gLockSetRes gssThreadRes; reflexivity).
            destruct HsimWeak.
            eapply weak_mem_obs_eq_store with (Hlt2 := Hlt2') (Hlt2F := Hlt2F') in weak_tsim_locks0; eauto.
            eapply setPermBlock_weak_obs_eq; eauto.
            now eapply (injective (weak_tsim_data0)).
        + (** [weak_tsim] for other threads*)
          destruct HsimWeak.
          constructor.
          * erewrite restrPermMap_irr' with (Hlt' := Hlt1')
              by (rewrite gLockSetRes; erewrite gsoThreadRes with (cntj := pfcj);
                  eauto).
            erewrite restrPermMap_irr' with (Hlt' := Hlt1F')
              by (rewrite gLockSetRes; erewrite gsoThreadRes with (cntj := pffj);
                  eauto).
            eapply weak_mem_obs_eq_store; eauto.
            now apply (injective weak_tsim_data0).
          * erewrite restrPermMap_irr' with (Hlt' := HltL')
              by (rewrite gLockSetRes; erewrite gsoThreadRes with (cntj := pfcj);
                  eauto).
            erewrite restrPermMap_irr' with (Hlt' := HltLF')
              by (rewrite gLockSetRes; erewrite gsoThreadRes with (cntj := pffj);
                  eauto).
            eapply weak_mem_obs_eq_store; eauto.
            now apply (injective weak_tsim_data0).
      - (** Proof of seperation of injections *)
        intros k j cntk' cntj' Hkj b0 b0' b3 b3' Hf0 Hf0' Hfk' Hfj'.
        assert (cntk: containsThread tpc k)
          by auto.
        assert (cntj: containsThread tpc j)
          by auto.
        erewrite cnt_irr with (cnt1 := cntk') (cnt2 := cntk) in Hfk'.
        erewrite cnt_irr with (cnt1 := cntj') (cnt2 := cntj) in Hfj'.
        eapply (HfpSep _ _ cntk cntj Hkj b0 b0');
          by eauto.
      - (** Proof of strong simulations after executing some thread*)
        intros.
        destruct (tid == i) eqn:Htid; move/eqP:Htid=>Htid; subst.
        { (** case of strong simulation for the thread that took the external*)
          exists  (updLockSet (updThread pfc (Kresume c Vundef) pmap_tid')
                         (b, Ptrofs.intval ofs) (empty_map, empty_map)), mc'.
          assert (pfc0 = pfc)
            by (eapply cnt_irr; eauto); subst pfc0.
          rewrite Hsynced.
          split; first by apply ren_incr_refl.
          split; first by auto.
          split; first by constructor.
          split.
          intros.
          constructor.
          do 2 rewrite gLockSetCode.
          do 2 rewrite gssThreadCode;
            by (split; [assumption | constructor]).
          (** [mem_obs_eq] for data*)
          Tactics.pf_cleanup.

          (** Need to massage goal a bit*)

          assert (Hlt1': permMapLt (getThreadR pfc).1 (getMaxPerm mc'))
            by (intros b0 ofs0;
                erewrite <- mem_store_max by eauto;
                rewrite getMaxPerm_correct;
                rewrite restrPermMap_Max;
                now apply HmemCompC;
                unfold permission_at;
                erewrite Mem.store_access by eauto).

          assert (Hlt1F': permMapLt (getThreadR pff).1 (getMaxPerm mf'))
            by (intros b0 ofs0;
                erewrite <- mem_store_max by eauto;
                rewrite getMaxPerm_correct;
                rewrite restrPermMap_Max;
                now apply (mem_compf Hsim);
                unfold permission_at;
                erewrite Mem.store_access by eauto).

          assert (Hlt1: permMapLt (setPermBlock (Some Nonempty) b (Ptrofs.intval ofs) (getThreadR pfc)#1 lksize.LKSIZE_nat) (getMaxPerm mc'))
            by (pose proof (compat_th _ _ HmemCompC' pfc') as Hlt;
                rewrite gLockSetRes gssThreadRes in Hlt;
                rewrite <- Hdata_perm in Hlt;
                destruct Hlt; assumption).
          assert (Hlt1F: permMapLt (setPermBlock (Some Nonempty) b2 (Ptrofs.intval ofs) (getThreadR pff)#1 lksize.LKSIZE_nat) (getMaxPerm mf'))
            by (pose proof (compat_th _ _ HmemCompF'' pff0) as Hlt;
                rewrite gLockSetRes gssThreadRes in Hlt;
                destruct Hlt; assumption).

          erewrite restrPermMap_irr' with (Hlt' := Hlt1)
            by (rewrite gLockSetRes gssThreadRes; rewrite <- Hdata_perm; reflexivity).
          erewrite restrPermMap_irr' with (Hlt' := Hlt1F)
            by (rewrite gLockSetRes gssThreadRes; reflexivity).

          eapply Mem.store_mem_contents in Hstore.
          eapply Mem.store_mem_contents in HstoreF.
          assert (Hmem_obs_eq_data_old := Hmem_obs_eq_data).
          eapply mem_obs_eq_store with (Hlt2 := Hlt1') (Hlt2F := Hlt1F') in Hmem_obs_eq_data; eauto.
          eapply setPermBlock_obs_eq; eauto.
          intros ofs0 Hrange.
          rewrite Hstore HstoreF. simpl.
          rewrite! Maps.PMap.gss.
          destruct (Intv.In_dec ofs0 (Ptrofs.intval ofs, (Ptrofs.intval ofs) + (Z.of_nat 4)))%Z.
          { erewrite! setN_inside by eauto.
            destruct (List.nth_in_or_default (Z.to_nat (ofs0 - Ptrofs.intval ofs)) (inj_bytes (encode_int 4 (Int.unsigned Int.zero))) Undef).
            apply inj_bytes_type in i1.
            destruct (List.nth (Z.to_nat  (ofs0 - Ptrofs.intval ofs)) (inj_bytes (encode_int 4 (Int.unsigned Int.zero))) Undef); try by exfalso.
            now constructor.
            rewrite e. now constructor.
          }
          { erewrite! Mem.setN_outside.
            destruct Hmem_obs_eq_data_old as [_ [_ Hval_obs_eq]].
            specialize (Hval_obs_eq _ _ ofs0 Hfb).
            simpl in Hval_obs_eq.
            eapply Hval_obs_eq.
            unfold Mem.range_perm, Mem.perm in *.
            replace (Z.of_nat lksize.LKSIZE_nat) with lksize.LKSIZE in Hrange
              by (unfold lksize.LKSIZE, lksize.LKSIZE_nat; reflexivity).
            specialize (Hfreeable ofs0 Hrange).
            erewrite po_oo in *.
            eapply po_trans; eauto.
            simpl; now constructor.
            rewrite length_inj_bytes encode_int_length.
            eapply Intv.range_notin in n; simpl in n;
              eauto.
            simpl. omega.
            rewrite length_inj_bytes encode_int_length.
            eapply Intv.range_notin in n; simpl in n;
              eauto.
            simpl. omega.
          }
          (** [mem_obs_eq] for locks*)
          assert (Hlt2: permMapLt (setPermBlock (Some Writable) b
                                                (Ptrofs.intval ofs) (getThreadR pfc)#2 lksize.LKSIZE_nat) (getMaxPerm mc'))
            by (pose proof (compat_th _ _ HmemCompC' pfc') as Hlt;
                rewrite gLockSetRes gssThreadRes in Hlt;
                rewrite <- Hlock_perm in Hlt;
                destruct Hlt; assumption).

          assert (Hlt2F: permMapLt (setPermBlock (Some Writable)
                                                 b2 (Ptrofs.intval ofs) (getThreadR pff)#2 lksize.LKSIZE_nat) (getMaxPerm mf'))
            by (pose proof (compat_th _ _ HmemCompF'' pff0) as Hlt;
                rewrite gLockSetRes gssThreadRes in Hlt;
                destruct Hlt; assumption).

          assert (Hlt2': permMapLt (getThreadR pfc).2 (getMaxPerm mc'))
            by (intros b0 ofs0;
                erewrite <- mem_store_max by eauto;
                rewrite getMaxPerm_correct;
                rewrite restrPermMap_Max;
                now apply HmemCompC;
                unfold permission_at;
                erewrite Mem.store_access by eauto).

          assert (Hlt2F': permMapLt (getThreadR pff).2 (getMaxPerm mf'))
            by (intros b0 ofs0;
                erewrite <- mem_store_max by eauto;
                rewrite getMaxPerm_correct;
                rewrite restrPermMap_Max;
                now apply (mem_compf Hsim);
                unfold permission_at;
                erewrite Mem.store_access by eauto).

          erewrite restrPermMap_irr' with (Hlt' := Hlt2)
            by (rewrite gLockSetRes gssThreadRes; rewrite <- Hlock_perm; reflexivity).
          erewrite restrPermMap_irr' with (Hlt' := Hlt2F)
            by (rewrite gLockSetRes gssThreadRes; reflexivity).
          eapply Mem.store_mem_contents in Hstore.
          eapply Mem.store_mem_contents in HstoreF.
          eapply mem_obs_eq_store with (Hlt2 := Hlt2') (Hlt2F := Hlt2F') in Hmem_obs_eq_locks; eauto.
          eapply setPermBlock_obs_eq; eauto.
          intros ofs0 Hrange.
          rewrite Hstore HstoreF.
          simpl.
          rewrite! Maps.PMap.gss.
          destruct (Intv.In_dec ofs0 (Ptrofs.intval ofs, (Ptrofs.intval ofs) + (Z.of_nat 4)))%Z.
          { erewrite! setN_inside by eauto.
            destruct (List.nth_in_or_default (Z.to_nat (ofs0 - Ptrofs.intval ofs)) (inj_bytes (encode_int 4 (Int.unsigned Int.zero))) Undef).
            apply inj_bytes_type in i1.
            destruct (List.nth (Z.to_nat  (ofs0 - Ptrofs.intval ofs)) (inj_bytes (encode_int 4 (Int.unsigned Int.zero))) Undef); try by exfalso.
            now constructor.
            rewrite e. now constructor.
          }
          { erewrite! Mem.setN_outside.
            destruct Hmem_obs_eq_data as [_ [_ Hval_obs_eq]].
            specialize (Hval_obs_eq _ _ ofs0 Hfb).
            simpl in Hval_obs_eq.
            eapply Hval_obs_eq.
            unfold Mem.range_perm, Mem.perm in *.
            replace (Z.of_nat lksize.LKSIZE_nat) with lksize.LKSIZE in Hrange
              by (unfold lksize.LKSIZE, lksize.LKSIZE_nat; reflexivity).
            specialize (Hfreeable ofs0 Hrange).
            erewrite po_oo in *.
            eapply po_trans; eauto.
            simpl; now constructor.
            rewrite length_inj_bytes encode_int_length.
            eapply Intv.range_notin in n; simpl in n;
              eauto.
            simpl. omega.
            rewrite length_inj_bytes encode_int_length.
            eapply Intv.range_notin in n; simpl in n;
              eauto.
            simpl. omega.
          }
          (** rest of strong sim*)
          split; first by congruence.
          split; first by congruence.
          rewrite gLockSetRes gssThreadRes.
          intros b0 Hunmapped ofs0.
          assert (b0 <> b2)
            by (intros Hcontra; inversion Hcontra; subst;
                eauto).
          rewrite! setPermBlock_other_2;
            now eauto.
        }
        { (** strong simulation for another thread*)
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
                  & Hownedj & Hownedj_lp & Hunmapped_j).
            (** first we prove that i is a valid thread after executing thread j*)
            assert (pfcij:= containsThread_internal_execution Hexecj pfc).

            (** Proof Sketch: Basically the proof we want is that changing some
            non-observable part of the state/memory should not affect the
            execution of thread j. To avoid giving yet another definition of
            equivalence of the observable state we re-use our strong
            injections/renamings. Steps:

            1. For the core and data resources, the original state <tpc,mc> will
            strongly inject with the id injection in the state <tpc', mc'> where
            we have updated the value of the lock and the resource maps
            according to the angel.

            2. Hence if <tpc,mc> takes internal steps to get to <tpcj, mcj> so
            will <tpc',mc'> to go to a new state <tpcj',mcj'>. Moreover
            <tpcj,mcj> will inject to <tpcj',mcj'> with the id injection. We had
            to strengthen our lemmas and corestep_obs_eq to obtain that last
            part.

            3. We use [strong_tsim_id_trans] to get that <tpcj',mcj'> will
               strongly inject in <tpf,mf> with the same injection as
               <tpcj,mcj>.

            4. Finally we prove that changing the state/memory in (TODO: add
            lemma name) non-observable parts retains the [strong_tsim] relation.
            *)

            (** Step 1*)
            assert (pfcjj: containsThread tpcj tid)
              by (eapply containsThread_internal_execution; eauto).
            assert (Hcompj: mem_compatible tpcj mcj)
              by (eapply internal_execution_compatible with (tp := tpc); eauto).
            specialize (Htsimj pfcjj Hcompj).

            (** We prove that thread tid on the original state injects
            in thread tid after updating the lockpool and storing the
            lock value*)
            assert (Htsimj_id:
                      tp_wd (id_ren mc) tpc /\
                      ctl_inj (id_ren mc) (getThreadC pfcj) (getThreadC pfc0) /\
                      mem_obs_eq (id_ren mc) (restrPermMap (compat_th _ _ HmemCompC pfcj).1)
                                 (restrPermMap (compat_th _ _ HmemCompC' pfc0).1) /\
                      (Mem.nextblock mc = Mem.nextblock mc')).
            { split.
              eapply tp_wd_domain;
                by eauto using id_ren_domain.
              eapply strong_tsim_store_id; eauto.
              erewrite gLockSetRes.
              rewrite gsoThreadRes; eauto.
              erewrite gLockSetCode.
              rewrite gsoThreadCode; eauto.
              destruct HinvC.
              pose proof ((thread_data_lock_coh0 _ pfc ).1 _ pfcj) as Hcoh.
              right.
              eapply Hinv; now eauto.
              eapply tp_wd_domain;
                by eauto using id_ren_domain.
            }
            destruct Htsimj_id as [Htpc_id_wd [Hctlj_id [Hmem_obs_eqj_id Hnextblock]]].

            (** Step 2.*)
            assert (H := mem_obs_eq_execution _ _ _ _ _ HinvC' Hfg Hge_wd Hge_incr_id
                                               Hmemc_wd Htpc_id_wd Hctlj_id Hmem_obs_eqj_id Hexecj).
            destruct H as
                (tp2' & m2' & f' & Hexecj'& Hincrj' & Hsepj'
                 & Hnextblock' & Hinvj' & Htsimj' & Hid').
            destruct Htsimj' as (pf2j & pf2j' & Hcomp2 & Hcomp2' & Hctl_eqj' & Hmem_obs_eq').
            specialize (Hid' Hnextblock (id_ren_correct mc)).
            assert (f' = id_ren mcj)
              by ( pose ((mem_obs_eq_domain_ren Hmem_obs_eq'));
                   eapply is_id_ren; eauto); subst f'.
            exists tp2', m2'.
            erewrite cnt_irr with (cnt1 := pfc0) (cnt2 := pfcj).
            split; first by auto.
            split; first by auto.
            split; first by auto.
            split.
            (** strong thread simulation for j*)
            intros.
            Tactics.pf_cleanup.
            (** Step 3, we use transitivity of [mem_obs_eq] and [ctl_inj] *)
            assert (Htsim2j: ctl_inj (fp tid pfcj) (getThreadC pf2j') (getThreadC pffj) /\
                             mem_obs_eq (fp tid pfcj) (restrPermMap (compat_th _ _ Hcomp2' pf2j').1)
                                        (restrPermMap (compat_th _ _ (mem_compf Hsim) pffj).1)).
            { destruct Htsimj.
              eapply strong_tsim_id_trans
              with (f := fp tid pfcj) (Hcomp1 := Hcompj) (Hcomp1' := Hcomp2');
              eauto.
              destruct Hnextblock' as [[p [Hmcj Hm2']] | [Hmcj Hm2']];
              unfold Mem.valid_block;
              rewrite Hmcj Hm2' Hnextblock;
                by tauto.
            }

            (** Step 4*)
            destruct Htsim2j as [Hcodeq2j Hmem_obs_eq2j].
            constructor.
            rewrite gLockSetCode.
            rewrite gsoThreadCode;
              by auto.
            clear - Hmem_obs_eq2j HstoreF HinvF Htid.
            assert (HeqRes: getThreadR pff0 = getThreadR pffj)
              by (rewrite gLockSetRes;
                   rewrite gsoThreadRes; auto).
            assert (Hlt : permMapLt (getThreadR pff0).1 (getMaxPerm mf))
            by (rewrite HeqRes; eapply (compat_th _ _ (mem_compf Hsim) pffj).1).
            eapply mem_obs_eq_storeF with (mf := mf) (Hlt :=  Hlt);
              eauto.
            right.
            apply Mem.store_valid_access_3 in HstoreF.
            pose proof (cntUpdateL' _ _ pff0) as pffj'.
            erewrite gLockSetRes with (cnti := pffj').
            erewrite gsoThreadRes with (cntj := pffj) by eauto.
            eapply HinvF;
              now eauto.

            erewrite restrPermMap_irr' with (Hlt := Hlt)
                                              (Hlt' := (compat_th _ _ (mem_compf Hsim) pffj).1); eauto.
            rewrite HeqRes. reflexivity.

            pose proof (obs_eq_locks Htsimj).

            assert (HRj_eq: (getThreadR pf2j').2 = (getThreadR pfcjj).2).
            { erewrite <- internal_execution_locks_eq with (cntj := pfc0) by eauto.
              erewrite <- internal_execution_locks_eq with (cntj' := pfcjj) (cntj := pfcj) by eauto.
              rewrite gLockSetRes.
              erewrite gsoThreadRes by eauto;
                reflexivity.
            }

            assert (Hlt2C: permMapLt (getThreadR pfcjj).2 (getMaxPerm m2'))
              by ( rewrite <- HRj_eq;
                   eapply (compat_th _ _ Hcomp2' pf2j').2).
            erewrite restrPermMap_irr' with (Hlt' := Hlt2C) by eauto.

            assert (HRj_eqF: (getThreadR pff0)#2 = (getThreadR pffj)#2)
              by (rewrite gLockSetRes; erewrite gsoThreadRes with (cntj := pffj) by eauto;
                  reflexivity).

            assert (Hlt2F: permMapLt (getThreadR pffj).2 (getMaxPerm mf'))
              by (rewrite <- HRj_eqF; eapply (compat_th _ _ HmemCompF'' pff0).2).
            erewrite restrPermMap_irr' with (Hlt' := Hlt2F) by eassumption.

            (** some useful results*)

            (** the contents of [m2'] are equal to the contents of [mc'] for locations [Readable] by locks on thread [tid]*)
            assert (Hstable_mc2': forall b1 ofs1, Mem.perm_order' ((getThreadR pfcj).2 # b1 ofs1) Readable ->
                                             ZMap.get ofs1 (Mem.mem_contents mc') # b1 = ZMap.get ofs1 (Mem.mem_contents m2') # b1).
            { intros.
              erewrite <- internal_exec_disjoint_locks with (Hcomp := HmemCompC') (m := mc') (m' := m2') (pfj := pfc0); eauto.
              unfold Mem.perm.
              pose proof (restrPermMap_Cur (compat_th _ _ HmemCompC' pfc0).2 b1 ofs1) as Hpermj.
              unfold permission_at in Hpermj.
              rewrite Hpermj.
              rewrite gLockSetRes.
              erewrite gsoThreadRes with (cntj := pfcj) by eauto.
              assumption.
            }

            (** the contents of [mcj] are equal to the contents of [mc] for locations [Readable] by locks on thread [tid]*)
            assert (Hstable_mcj: forall b1 ofs1, Mem.perm_order' ((getThreadR pfcj).2 # b1 ofs1) Readable ->
                                            ZMap.get ofs1 (Mem.mem_contents mc) # b1 =
                                            ZMap.get ofs1 (Mem.mem_contents mcj) # b1).
            { intros.
              erewrite internal_exec_disjoint_locks
              with (Hcomp := HmemCompC) (pfj := pfcj) (m := mc) (tp := tpc) (tp' := tpcj); eauto.
              unfold Mem.perm in *.

              pose proof (restrPermMap_Cur (compat_th _ _ HmemCompC pfcj).2 b1 ofs1) as Hpermj.
              unfold permission_at in *.
              rewrite Hpermj. assumption.
            }

            assert (Hperm_eqj: forall b1 ofs1, (Mem.mem_access (restrPermMap (compat_th _ _ Hcompj pfcjj).2)) # b1 ofs1 Cur =
                                          (getThreadR pfcj).2 # b1 ofs1).
            { intros.
              pose proof (restrPermMap_Cur (compat_th _ _ Hcompj pfcjj).2 b1 ofs1) as Hpermjj.
              unfold permission_at in Hpermjj.
              rewrite Hpermjj.
              erewrite <- internal_execution_locks_eq with (cntj' := pfcjj) (cntj := pfcj) at 1
                by eauto.
              reflexivity.
            }


            (** **** We now apply [mem_obs_eq_disjoint_lock]*)
            eapply mem_obs_eq_disjoint_lock
            with (ofsl := Ptrofs.intval ofs) (bl1 := b)
                                          (bl2 := b2) (sz := size_chunk Mint32); eauto.
            (** valid blocks of [mcj] are the same [m2']*)
            intros. unfold Mem.valid_block in *.
            destruct Hnextblock' as [[p [Hnextj Hnext2]] | [Hnextj Hnext2]];
              rewrite Hnextj Hnext2 Hnextblock;
              split; now auto.

            (** [memval_obs_eq] of contents on updated lock*)
            intros ofs0 Hrange.
            (** thread i has [Writable] access on this location by the read it
            succesfully performed, hence by disjointness thread j cannot have
            [Writable] data permission on that location*)
            assert (Hlock_unwrittable: ~ Mem.perm (restrPermMap (compat_th _ _ HmemCompC' pfc0)#1) b ofs0 Cur Writable).
            { clear - Hstore HinvC Hrange pfcj Htid.
              intros Hcontra.
              apply Mem.store_valid_access_3 in Hstore.
              destruct Hstore as [Hperm _].
              specialize (Hperm ofs0 Hrange).
              unfold Mem.perm in *.
              pose proof ((restrPermMap_Cur (compat_th _ _ HmemCompC' pfc0).1) b ofs0) as Hpermj'.
              pose proof ((restrPermMap_Cur (compat_th _ _ HmemCompC pfc).1) b ofs0) as Hpermi.
              unfold permission_at in *.
              rewrite Hpermi in Hperm.
              rewrite Hpermj' in Hcontra.
              rewrite gLockSetRes in Hcontra.
              erewrite gsoThreadRes with (cntj := pfcj) in Hcontra by eauto.
              pose proof ((no_race_thr _ HinvC _ _ pfcj pfc Htid).1 b ofs0).
              rewrite perm_union_comm in H.
              eapply perm_order_clash; eauto.
              erewrite po_oo in *.
              eapply po_trans; eauto.
              simpl; constructor.
            }

            (** and thus by [internal_exec_stable]*)
            erewrite <- internal_exec_stable with (m := mc') (Hcomp := HmemCompC') (pfi := pfc0); eauto.
            erewrite Mem.store_mem_contents with (m2 := mc') by eauto.
            erewrite Mem.store_mem_contents with (m2 := mf') by eauto.
            simpl.
            rewrite! Maps.PMap.gss.
            erewrite! setN_inside
              by (rewrite length_inj_bytes encode_int_length; simpl in Hrange; auto).
            destruct (List.nth_in_or_default (Z.to_nat (ofs0 - Ptrofs.intval ofs)) (inj_bytes (encode_int 4 (Int.unsigned Int.zero))) Undef).
            apply inj_bytes_type in i0.
            destruct (List.nth (Z.to_nat  (ofs0 - Ptrofs.intval ofs)) (inj_bytes (encode_int 4 (Int.unsigned Int.zero))) Undef); try by exfalso.
            now constructor.
            rewrite e. now constructor.
            eapply Mem.store_valid_block_1; eauto.
            (** the contents of [mcj] are equal to the contents of [mc] for locations [Readable] by locks on thread [tid]*)
            intros.
            unfold Mem.perm in H1.
            erewrite Hperm_eqj in H1.
            erewrite <- Hstable_mc2' by eauto.
            erewrite <- Hstable_mcj by eauto.
            (** we can now prove that for all lock locations that tid can access, other than the one updated, the contents will be equal*)
            erewrite Mem.store_mem_contents with (m2 := mc') by eauto.
            destruct H0 as [Hb_neq | [? Hofs_neq]].
            (** if b0 is not the block that was updated*)
            erewrite Maps.PMap.gso by eauto.
            reflexivity.
            (** if b0 is the updated block but ofs0 is not in the updated range*)
            subst.
            rewrite Maps.PMap.gss.
            erewrite Mem.setN_outside
              by (rewrite encode_val_length; eapply Intv.range_notin in Hofs_neq; eauto; simpl; omega).
            reflexivity.

            (** stability for contents of [mf] and [mf']*)
            intros b0 ofs0 Hneq Hreadable.
            erewrite Mem.store_mem_contents with (m2 := mf') by eauto.
            destruct Hneq as [Hb_neq | [? Hofs_neq]].
            (** if b0 is not the block that was updated*)
            erewrite Maps.PMap.gso by eauto.
            reflexivity.
            (** if b0 is the updated block but ofs0 is not in the updated range*)
            subst.
            rewrite Maps.PMap.gss.
            erewrite Mem.setN_outside
              by (rewrite encode_val_length; eapply Intv.range_notin in Hofs_neq; eauto; simpl; omega).
            reflexivity.
            eauto.
            split.
            (** thread ownership*)
            intros k pff2k Hjk b1 b0 ofs0 Hfj Hfi.
            destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
            { subst k.
              rewrite gLockSetRes.
              rewrite gssThreadRes; auto.
              assert (b0 <> b2).
              { intros Hcontra; subst.
                pose proof (Hincrj _ _ Hf) as Hf'.
                pose proof (injective (weak_obs_eq (obs_eq_data Htsimj)) _ _ Hfj Hf'); subst.
                now congruence.
              }

              rewrite! setPermBlock_other_2;
                by eauto.
            }
            { rewrite gLockSetRes.
              rewrite gsoThreadRes; auto.
              eapply Hownedj;
                by eauto.
            }
            split.
            (** lockpool ownership*)
            intros bl ofsl rmap b1 b0 ofs0 Hfj Hfi Hres.
            destruct (EqDec_address (b2, Ptrofs.intval ofs) (bl, ofsl)) as [Heq | Hneq].
            (** case rmap is the resource map updated by the angel*)
            inversion Heq; subst.
            rewrite gssLockRes in Hres. inversion Hres.
            simpl. split; now apply empty_map_spec.
            (** case it is another resource map*)
            rewrite gsoLockRes in Hres; auto.
            rewrite gsoThreadLPool in Hres;
              by eauto.
            (** unmapped blocks are empty*)
            intros b0 Hunmapped ofs0.
            rewrite gLockSetRes.
            erewrite gsoThreadRes with (cntj := pffj) by eauto.
            eapply Hunmapped_j;
              by eauto.
          }
      - split.
        {  (** Proof of [strong_mem_obs_eq] for lock pool*)
          intros bl1 bl2 ofs0 rmap1 rmap2 Hfi Hres1 Hres2.
          destruct (EqDec_address (b, Ptrofs.intval ofs) (bl1, ofs0)) as [Heq | Hneq].
          { (** case it's the newly created lock*)
            inversion Heq; subst.
            assert (bl2 = b2)
              by (rewrite Hfi in Hfb; by inversion Hfb).
            subst bl2.
            assert (Hperm_eq: forall b1 b0 ofs0, fp i pfc b1 = Some b0 ->
                                            permission_at (restrPermMap (compat_lp _ _ HmemCompF'' (b2, Ptrofs.intval ofs) _ Hres2)#1) b0 ofs0 Cur =
                                            permission_at (restrPermMap (compat_lp _ _ HmemCompC' (bl1, Ptrofs.intval ofs) _ Hres1)#1) b1 ofs0 Cur /\
                                            permission_at (restrPermMap (compat_lp _ _ HmemCompF'' (b2, Ptrofs.intval ofs) _ Hres2)#2) b0 ofs0 Cur =
                                            permission_at (restrPermMap (compat_lp _ _ HmemCompC' (bl1, Ptrofs.intval ofs) _ Hres1)#2) b1 ofs0 Cur).
            { intros.
              rewrite! restrPermMap_Cur.
              rewrite gssLockRes in Hres1.
              rewrite gssLockRes in Hres2.
              inversion Hres1; inversion Hres2.
              simpl;
                split; by rewrite! empty_map_spec.
            }
            split;
              constructor; intros;
                try (destruct (Hperm_eq b1 b0 ofs0 Hrenaming); by auto).
            assert (H:= restrPermMap_Cur (compat_lp _ _ HmemCompC' (bl1, Ptrofs.intval ofs)
                                                    _ Hres1).1 b1 ofs0).
            unfold permission_at in H.
            unfold Mem.perm in Hperm.
            rewrite H in Hperm.
            clear H Hperm_eq.
            exfalso.
            rewrite gssLockRes in Hres1.
            inversion Hres1; subst.
            unfold Maps.PMap.get in Hperm.
            rewrite Maps.PTree.gempty in Hperm.
            simpl in Hperm;
              by auto.
            assert (H:= restrPermMap_Cur (compat_lp _ _ HmemCompC' (bl1, Ptrofs.intval ofs)
                                                    _ Hres1).2 b1 ofs0).
            unfold permission_at in H.
            unfold Mem.perm in Hperm.
            rewrite H in Hperm.
            clear H Hperm_eq.
            exfalso.
            rewrite gssLockRes in Hres1.
            inversion Hres1; subst.
            unfold Maps.PMap.get in Hperm.
            rewrite Maps.PTree.gempty in Hperm.
            simpl in Hperm;
              by auto.
          }
          { (** case it's another lock*)
            assert ((b2, Ptrofs.intval ofs) <> (bl2, ofs0)).
            { clear - Hneq Hfi Hf Hfb Hmem_obs_eq_data.
              intros Hcontra; inversion Hcontra; subst.
              assert (b = bl1)
                by (eapply (injective (weak_obs_eq Hmem_obs_eq_data)); eauto).
              subst;
                by auto.
            }
            pose proof Hres1 as Hres1';
              pose proof Hres2 as Hres2'.
            erewrite gsoLockRes, gsoThreadLPool in Hres1' by auto.
            erewrite gsoLockRes, gsoThreadLPool in Hres2' by auto.
            destruct (HsimRes _ _ _ _ _ Hfi Hres1' Hres2') as [Hsim1 Hsim2].
            split;
              eapply strong_mem_obs_eq_store with (bl1 := b) (bl2 := b2); eauto;
                try (erewrite Mem.store_mem_contents by eauto; reflexivity).
          }
        }
        split.
        (** proof that locks are mapped*)
        intros bl2 ofs0 Hres.
        destruct (EqDec_address (bl2, ofs0) (b2, Ptrofs.intval ofs)) as [Heq | Hneq].
        inversion Heq; subst.
        eexists;
          by eauto.
        erewrite gsoLockRes, gsoThreadLPool in Hres by auto.
        eapply Hlock_mapped;
          by eauto.
        (** proof that the two machines have the same locks*)
        { intros bl1 bl2 ofs0 Hfl1.
          destruct (EqDec_address (b, Ptrofs.intval ofs) (bl1, ofs0)).
          - inversion e; subst.
            assert (b2 = bl2)
              by (rewrite Hf in Hfl1; inversion Hfl1; subst; auto).
            subst.
            do 2 rewrite gsslockResUpdLock.
            split;
              auto.
          - erewrite gsolockResUpdLock by auto.
            assert ((b2, Ptrofs.intval ofs) <> (bl2, ofs0)).
            { intros Hcontra.
              inversion Hcontra; subst.
              specialize (Hinjective _ _ _ Hfl1 Hfb).
              subst; auto.
            }
            erewrite gsolockResUpdLock by eauto.
            do 2 rewrite gsoThreadLPool.
            eauto.
        }
        (** proof that unmapped blocks are empty*)
      - intros bl ofsl rmap0 Hres b0 Hunmapped ofs0.
        destruct (EqDec_address (b2, Ptrofs.intval ofs) (bl, ofsl)).
        +  inversion e; subst.
           rewrite gsslockResUpdLock in Hres.
           inversion Hres; subst.
           simpl.
           split;
             now apply empty_map_spec.
        + erewrite gsolockResUpdLock in Hres by auto.
          rewrite gsoThreadLPool in Hres.
          eapply HunmappedRes;
            now eauto.
      - (** Proof of invariant preservation for fine-grained machine*)
        clear - HinvF HstoreF HinvC' Hlock_if Hf HaccessF.
        Opaque getThreadR.
        eapply updLock_inv;
          try (intros; simpl; split; intros ? ?; rewrite empty_map_spec; simpl; eauto);
          try (rewrite perm_union_comm; simpl; eauto);
          try (now apply perm_coh_empty_1).
        eapply invariant_mklock; eauto.
        apply Mem.store_valid_access_3 in HstoreF.
        intros ofs' Hrange.
        pose proof (restrPermMap_Cur (compat_th _ _ (mem_compf Hsim) pff).1 b2 ofs') as Heq.
        unfold permission_at in Heq.
        unfold Mem.range_perm, Mem.perm in HaccessF.
        specialize (HaccessF ofs' Hrange).
        rewrite Heq in HaccessF.
        now assumption.
        rewrite gsoThreadLPool in H0.
        pose proof ((invariant_not_freeable HinvF b0 ofs0).2 _ _ H0).
        destruct ((rmap').2 # b0 ofs0) as [p|];
          try (destruct p);
          by auto.
        intros ? ?.
        rewrite empty_map_spec;
          now apply perm_coh_empty_1.
        destruct (i == i0) eqn:Heq; move/eqP:Heq=>Heq.
        subst.
        rewrite gssThreadRes.
        destruct (setPermBlock_or (Some Writable) b2 (Ptrofs.intval ofs) (lksize.LKSIZE_nat)
                                  (getThreadR pff).2 b0 ofs0).
        simpl.
        rewrite H; auto.
        rewrite H.
        pose proof ((invariant_not_freeable HinvF b0 ofs0).1 _ pff).
        destruct ((getThreadR pff).2 # b0 ofs0) as [p|];
          try (destruct p); auto.
        pose proof (cntUpdate' _ _ _ cnti) as cnti0.
        pose proof ((invariant_not_freeable HinvF b0 ofs0).1 _ cnti0).
        erewrite gsoThreadRes with (cntj := cnti0) by eauto.
        destruct ((getThreadR cnti0).2 # b0 ofs0) as [p|];
          try (destruct p); auto.
        intros ofs' Hrange.
        rewrite gsoThreadLPool.
        destruct (lockRes tpf (b2, ofs')) eqn:HresF; auto.
        exfalso.
        specialize (Hlock_if _ _ ofs' Hf).
        pose proof (Hlock_if.2 ltac:(rewrite HresF; auto)) as Hres.
        pose proof (lockRes_valid _ HinvC' b (Ptrofs.intval ofs)) as HvalidC'.
        rewrite gssLockRes in HvalidC'.
        specialize (HvalidC' _ Hrange).
        erewrite gsoLockRes in HvalidC'
          by (intros Hcontra; inversion Hcontra; subst; omega).
        rewrite gsoThreadLPool in HvalidC'.
        rewrite HvalidC' in Hres.
        now auto.
        intros ofs' Hrange.
        rewrite gsoThreadLPool.
        pose proof (lockRes_valid _ HinvC' b ofs') as HvalidC'.
        erewrite gsoLockRes in HvalidC' by (intros Hcontra; inversion Hcontra; subst; omega).
        rewrite gsoThreadLPool in HvalidC'.
        destruct (lockRes tpf (b2, ofs')) eqn:HresF; auto.
        specialize (Hlock_if _ _ ofs' Hf).
        pose proof (Hlock_if.2 ltac:(rewrite HresF; auto)) as Hres.
        destruct (lockRes tpc (b, ofs')); try (by exfalso).
        specialize (HvalidC' _ Hrange).
        rewrite gssLockRes in HvalidC'.
        discriminate.
      - (** Max permission invariant*)
        assumption.
      - (** new memory is well-defined*)
        eapply store_wd_domain with (m := restrPermMap (compat_th _ _ HmemCompC pfc)#1); eauto.
          by simpl.
      - (** new tpc is well-defined*)
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
        specialize (Htpc_wd _ cntj);
          by auto.
      - (** ge is well-defined*)
        assumption.
      - (** ge spec*)
        split; assumption.
      - intros.
        apply cntUpdateL;
          apply cntUpdate;
            by eauto.
      - econstructor;
          eauto.
        econstructor;
          now eauto.
    }
    { (** Freelock case*)
      subst mc'.

      (** consider [mf] with the lock permissions of thread i on FineConc*)
      remember (restrPermMap (compat_th _ _ (mem_compf Hsim) pff).2) as mf1 eqn:Hrestrict_pmapF.

      destruct Htsim as [Hcore_inj Hmem_obs_eq_data Hmem_obs_eq_locks].
      (** We have that the core of the fine grained execution
        is related to the one of the coarse-grained*)
      rewrite Hcode in Hcore_inj.
      simpl in Hcore_inj.
      subst.
      destruct (getThreadC pff) as [? | cf |? | ?] eqn:HcodeF;
        try by exfalso.
      (** And now we can prove that cf is also at external *)
      assert (Hat_external_spec := core_inj_ext _ _ Hfg Hge_wd Hge_incr Hvalid_mem' Hcore_inj Hmem_obs_eq_data).
      rewrite Hat_external in Hat_external_spec.
      destruct (at_external semSem cf (restrPermMap (compat_th _ _ (mem_compf Hsim) pff)#1))
        as [[? vsf] | ] eqn:Hat_externalF;
          try by exfalso.
      (** and moreover that it's the same external and their
        arguments are related by the injection*)
      destruct Hat_external_spec as [? Harg_obs]; subst.
      inversion Harg_obs as [|? ? ? ? Hptr_obs Hl]; subst.
      inversion Hl; subst.
      inversion Hptr_obs as [| | | |b1 b2 ofs0 Hf|];
        subst b1 ofs0 v'.

      (** we compute the new permissions on the thread*)
      remember (setPermBlock None b2 (Ptrofs.intval ofs) (getThreadR pff).2
                             lksize.LKSIZE_nat) as pmap_tidF2' eqn:Hlock_permF.
      symmetry in Hlock_permF.
      remember (setPermBlock_var pdata b2 (Ptrofs.intval ofs) (getThreadR pff).1
                             lksize.LKSIZE_nat) as pmap_tidF' eqn:Hdata_permF.
      symmetry in Hdata_permF.
      (** The FineConc execution will also have above [Writable] permissions
      at the mapped address *)
      assert (HfreeableF: Mem.range_perm (restrPermMap (compat_th _ _ (mem_compf Hsim) pff).2) b2 (Ptrofs.intval ofs) ((Ptrofs.intval ofs) + lksize.LKSIZE) Cur Writable).
      { intros ofs' Hrange.
        pose proof ((perm_obs_strong (strong_obs_eq Hmem_obs_eq_locks)) _ _ ofs' Hf) as Hperm_eq.
        specialize (Hfreeable _ Hrange).
        unfold Mem.perm in *.
        unfold permission_at in Hperm_eq.
        rewrite Hperm_eq.
        now auto.
      }
      (** And [(b2, Ptrofs.intval ofs)] is in [lockRes] of the FineConc machine*)
      assert (Hsome_lockF: lockRes tpf (b2, Ptrofs.intval ofs))
        by (eapply Hlock_if; eauto; rewrite His_lock; eauto).
      destruct (lockRes tpf (b2, Ptrofs.intval ofs)) as [rmapF|] eqn:His_lockF;
        try (by exfalso).

      (** The resources of the lock are empty*)
      assert(HrmapF: forall b ofs, rmapF.1 !! b ofs = None /\ rmapF.2 !! b ofs = None).
      { intros b0 ofs0.
        assert (Hb0: (exists b1, (fp i pfc) b1 = Some b0) \/
                     ~ (exists b1, (fp i pfc) b1 = Some b0))
          by eapply em.
        destruct Hb0 as [[b1 Hf1] | Hunmapped].
        - (** if b0 is mapped by some block*)
          destruct (HsimRes _ _ _ _ _ Hf His_lock His_lockF) as [HsimRes1 HsimRes2].
          pose proof (perm_obs_strong HsimRes1 _ ofs0 Hf1) as Hpmap1.
          pose proof (perm_obs_strong HsimRes2 _ ofs0 Hf1) as Hpmap2.
          rewrite! restrPermMap_Cur in Hpmap1 Hpmap2.
          erewrite Hpmap1, Hpmap2, (Hrmap b1 ofs0).1, (Hrmap b1 ofs0).2.
          split; reflexivity.
        - specialize (HunmappedRes _ _ _ His_lockF _ Hunmapped ofs0).
          assumption.
      }

      remember (updThread pff (Kresume cf Vundef) (pmap_tidF', pmap_tidF2'))
        as tpf' eqn:Htpf'.
      (** Finally we remove the lock from the FineConc machine*)
      remember (remLockSet tpf' (b2, Ptrofs.intval ofs)) as tpf'' eqn:Htpf''.
      exists tpf'', mf, (fp i pfc), fp, (trf ++ [:: (external i (freelock (b2, Ptrofs.intval ofs)))]).
      split.
      (** proof that the FineConc machine can step*)
      intros U.
      assert (HsyncStepF: syncStep false pff (mem_compf Hsim) tpf'' mf (freelock (b2, Ptrofs.intval ofs)))
        by (eapply step_freelock with (b0 := b2); now eauto).
      econstructor;
        by eauto.

      (** Proof that the new DryConc and FineConc states are in simulation*)
      assert (HinvC':
                invariant (remLockSet
                             (updThread pfc (Kresume c Vundef) pmap_tid')
                             (b, Ptrofs.intval ofs)))
        by  (eapply StepLemmas.safeC_invariant with (n := fuelF.+1 + size xs); eauto).
      assert (HlockRes_valid:  lr_valid
                                 (lockRes
                                    (updThread pff (Kresume cf Vundef) (pmap_tidF', pmap_tidF2')))).
      { intros b0 ofs0.
        rewrite gsoThreadLPool.
        pose proof (lockRes_valid _ HinvF) as Hlr_valid.
        specialize (Hlr_valid b0 ofs0).
        now eauto.
      }

      (** [mem_compatible] is easily derived as permissions only changed
      at the lock permission and will always be below freeable*)
      assert (HmemCompF' : mem_compatible tpf'' mf).
      { subst.
        constructor.
        { intros j pffj.
          rewrite gRemLockSetRes.
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          - subst j.
            rewrite gssThreadRes.
            unfold permMapLt.
            erewrite <- forall2_and.
            intros b' ofs'.
            destruct (Pos.eq_dec b2 b').
            + subst.
              apply (codomain_valid (weak_obs_eq (Hmem_obs_eq_data))) in Hf.
              erewrite restrPermMap_valid in Hf.
              specialize (HmaxF _ ofs' Hf).
              rewrite getMaxPerm_correct HmaxF; simpl.
              simpl; split;
                match goal with
                | [|-match ?Expr with _ => _ end] =>
                  destruct Expr
                end;
                now constructor.
            + rewrite! setPermBlock_other_2; auto.
              rewrite setPermBlock_var_other_2; auto.
              pose proof ((compat_th _ _ (mem_compf Hsim) pff).1 b' ofs').
              pose proof ((compat_th _ _ (mem_compf Hsim) pff).2 b' ofs');
                split; now auto.
          - rewrite gsoThreadRes; auto.
            pose proof (compat_th _ _ (mem_compf Hsim) pffj); auto.
        }
        { intros (bl' & ofsl') rmap' Hres'.
          destruct (EqDec_address (b2, Ptrofs.intval ofs) (bl', ofsl')) as [Heq |Hneq].
          - inversion Heq; subst.
            rewrite gsslockResRemLock in Hres';
              by discriminate.
          - rewrite gsolockResRemLock in Hres'; auto.
            rewrite gsoThreadLPool in Hres'.
            eapply (compat_lp _ _ (mem_compf Hsim)); eauto.
        }
        { intros (bl' & ofsl') ? Hres.
          destruct (EqDec_address (b2, Ptrofs.intval ofs) (bl', ofsl')) as [Heq |Hneq].
          - inversion Heq; subst.
            rewrite gsslockResRemLock in Hres;
              by discriminate.
          - rewrite gsolockResRemLock in Hres; auto.
            rewrite gsoThreadLPool in Hres.
            eapply (lockRes_blocks _ _ (mem_compf Hsim)); eauto.
        }
      }
      subst.

      assert (Hlt1: forall (pfc': containsThread (remLockSet (updThread pfc (Kresume c Vundef) pmap_tid') (b, Ptrofs.intval ofs)) i),
                 permMapLt (setPermBlock_var pdata b (Ptrofs.intval ofs) (getThreadR pfc)#1 lksize.LKSIZE_nat) (getMaxPerm mc))
        by (intros; pose proof (compat_th _ _ HmemCompC' pfc') as Hlt;
            rewrite gRemLockSetRes gssThreadRes in Hlt;
            rewrite <- Hdata_perm in Hlt;
            destruct Hlt; assumption).
      assert (Hlt1F: forall (pff' : containsThread
                                 (remLockSet
                                    (updThread pff (Kresume cf Vundef)
                                               (setPermBlock (((getThreadR pff)#2) # b2 (Ptrofs.intval ofs)) b2 (Ptrofs.intval ofs) (getThreadR pff)#1 lksize.LKSIZE_nat,
                                                setPermBlock None b2 (Ptrofs.intval ofs) (getThreadR pff)#2 lksize.LKSIZE_nat)) (b2, Ptrofs.intval ofs)) i),
                 permMapLt (setPermBlock_var pdata b2 (Ptrofs.intval ofs)
                                         (getThreadR pff)#1 lksize.LKSIZE_nat) (getMaxPerm mf))
        by (intros; pose proof (compat_th _ _ HmemCompF' pff') as Hlt;
            rewrite gRemLockSetRes gssThreadRes in Hlt;
            destruct Hlt; assumption).

      assert (Hlt2:  forall (pfc': containsThread (remLockSet (updThread pfc (Kresume c Vundef) pmap_tid') (b, Ptrofs.intval ofs)) i),
                 permMapLt (setPermBlock None b (Ptrofs.intval ofs) (getThreadR pfc)#2 lksize.LKSIZE_nat) (getMaxPerm mc))
        by (intros; pose proof (compat_th _ _ HmemCompC' pfc') as Hlt;
            rewrite gRemLockSetRes gssThreadRes in Hlt;
            rewrite <- Hlock_perm in Hlt;
            destruct Hlt; eauto).
      assert (Hlt2F: forall (pff' : containsThread
                                 (remLockSet
                                    (updThread pff (Kresume cf Vundef)
                                               (setPermBlock (((getThreadR pff)#2) # b2 (Ptrofs.intval ofs)) b2 (Ptrofs.intval ofs) (getThreadR pff)#1 lksize.LKSIZE_nat,
                                                setPermBlock None b2 (Ptrofs.intval ofs) (getThreadR pff)#2 lksize.LKSIZE_nat)) (b2, Ptrofs.intval ofs)) i),
                 permMapLt (setPermBlock None b2 (Ptrofs.intval ofs)
                                         (getThreadR pff)#2 lksize.LKSIZE_nat) (getMaxPerm mf))
        by (intros; pose proof (compat_th _ _ HmemCompF' pff') as Hlt;
            rewrite gRemLockSetRes gssThreadRes in Hlt;
            destruct Hlt; assumption).

      eapply Build_sim with (mem_compc := HmemCompC') (mem_compf := HmemCompF').
      - (** containsThread *)
        clear - HnumThreads.
        intros j.
        split; intros cntj;
        eapply cntRemoveL;
        eapply cntUpdate;
        apply cntRemoveL' in cntj;
        apply cntUpdate' in cntj;
          by eapply HnumThreads.
      - (** safety of coarse machine*)
        intros sched tr.
        eapply HybridCoarseMachine.csafe_trace;
          now eauto.
      - (** weak simulation between the two machines*)
        intros j pfcj' pffj'.
        assert (pfcj: containsThread tpc j)
          by auto.
        assert (pffj: containsThread tpf j)
          by auto.
        specialize (HsimWeak _ pfcj pffj).
        clear - HsimWeak Hsim Hf Hdata_perm Hlock_perm Hmem_obs_eq_locks Hlt1 Hlt1F Hlt2 Hlt2F.
        (** By case analysis on whether thread j is the one that created the lock*)
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        + subst.
          Tactics.pf_cleanup.
          constructor.
          * (** [weak_mem_obs_eq] for data*)
            subst.
            erewrite restrPermMap_irr' with (Hlt' := (Hlt1 pfcj'))
              by (rewrite gRemLockSetRes gssThreadRes; rewrite <- Hdata_perm; reflexivity).
            erewrite restrPermMap_irr' with (Hlt' := (Hlt1F pffj'))
              by (rewrite gRemLockSetRes gssThreadRes; reflexivity).
            destruct HsimWeak.
            eapply setPermBlock_var_weak_obs_eq; eauto.
          * (** [weak_mem_obs_eq] for data*)
            subst.
            erewrite restrPermMap_irr' with (Hlt' := (Hlt2 pfcj'))
              by (rewrite gRemLockSetRes gssThreadRes; rewrite <- Hlock_perm; reflexivity).
            erewrite restrPermMap_irr' with (Hlt' := (Hlt2F pffj'))
              by (rewrite gRemLockSetRes gssThreadRes; reflexivity).
            destruct HsimWeak.
            eapply setPermBlock_weak_obs_eq;
              now eauto.
        + (** [weak_tsim] for other threads*)
          destruct HsimWeak.
          constructor.
          * erewrite restrPermMap_irr' with (Hlt' := (compat_th _ _ HmemCompC pfcj).1)
              by (rewrite gRemLockSetRes; erewrite gsoThreadRes with (cntj := pfcj);
                  eauto).
            erewrite restrPermMap_irr' with (Hlt' := (compat_th _ _ (mem_compf Hsim) pffj).1)
              by (rewrite gRemLockSetRes; erewrite gsoThreadRes with (cntj := pffj);
                  eauto).
            assumption.
          *  erewrite restrPermMap_irr' with (Hlt' := (compat_th _ _ HmemCompC pfcj).2)
              by (rewrite gRemLockSetRes; erewrite gsoThreadRes with (cntj := pfcj);
                  eauto).
            erewrite restrPermMap_irr' with (Hlt' := (compat_th _ _ (mem_compf Hsim) pffj).2)
              by (rewrite gRemLockSetRes; erewrite gsoThreadRes with (cntj := pffj);
                  eauto).
            assumption.
      - (** Proof of seperation of injections *)
        intros k j cntk' cntj' Hkj b0 b0' b3 b3' Hf0 Hf0' Hfk' Hfj'.
        assert (cntk: containsThread tpc k)
          by auto.
        assert (cntj: containsThread tpc j)
          by auto.
        erewrite cnt_irr with (cnt1 := cntk') (cnt2 := cntk) in Hfk'.
        erewrite cnt_irr with (cnt1 := cntj') (cnt2 := cntj) in Hfj'.
        eapply (HfpSep _ _ cntk cntj Hkj b0 b0');
          by eauto.
      - (** Proof of strong simulations after executing some thread*)
        intros.
        destruct (tid == i) eqn:Htid; move/eqP:Htid=>Htid; subst.
        { (** case of strong simulation for the thread that took the external*)
          exists (remLockSet
                (updThread pfc (Kresume c Vundef) pmap_tid')
                (b, Ptrofs.intval ofs)), mc.
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
          (** proof of [mem_obs_eq] for data *)
          erewrite restrPermMap_irr' with (Hlt' := (Hlt1 pfc'))
            by (rewrite gRemLockSetRes gssThreadRes; rewrite <- Hdata_perm; reflexivity).
          erewrite restrPermMap_irr' with (Hlt' := (Hlt1F pff))
            by (rewrite gRemLockSetRes gssThreadRes; reflexivity).
          eapply setPermBlock_var_obs_eq; eauto.
          intros ofs0 Hrange.
          pose proof (val_obs_eq (strong_obs_eq Hmem_obs_eq_locks)  _ ofs0 Hf) as Hval.
          specialize (Hfreeable _ Hrange).
          simpl in Hval.
          eapply Hval.
          unfold Mem.perm in *.
          erewrite po_oo in *.
          eapply po_trans; eauto.
          simpl; eauto using perm_order.
          (** proof of [mem_obs_eq] for data *)
          erewrite restrPermMap_irr' with (Hlt' := (Hlt2 pfc'))
            by (rewrite gRemLockSetRes gssThreadRes; rewrite <- Hlock_perm; reflexivity).
          erewrite restrPermMap_irr' with (Hlt' := (Hlt2F pff))
            by (rewrite gRemLockSetRes gssThreadRes; reflexivity).
          eapply setPermBlock_obs_eq; eauto.
          intros ofs0 Hrange.
          pose proof (val_obs_eq (strong_obs_eq Hmem_obs_eq_locks)  _ ofs0 Hf) as Hval.
          specialize (Hfreeable _ Hrange).
          simpl in Hval.
          eapply Hval.
          unfold Mem.perm in *.
          erewrite po_oo in *.
          eapply po_trans; eauto.
          simpl; eauto using perm_order.
          repeat split;
            try (by congruence);
          destruct (Hunmapped_ls _ H ofs0).
          rewrite gRemLockSetRes gssThreadRes.
          rewrite setPermBlock_var_other_2.
          assumption.
            by (intros Hcontra; subst;
                eapply H; eexists; eauto).
            rewrite gRemLockSetRes gssThreadRes.
            rewrite setPermBlock_other_2.
            assumption.
              by (intros Hcontra; subst;
                  eapply H; eexists; eauto).
        }
        { (** strong simulation for another thread*)
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
                & Hownedj & Hownedj_lp & Hunmappedj).
          (** first we prove that i is a valid thread after executing thread j*)
          assert (pfcij:= containsThread_internal_execution Hexecj pfc).
          exists (remLockSet
                (updThread pfcij (Kresume c Vundef) pmap_tid')
                (b, Ptrofs.intval ofs)), mcj.
          split; eauto.
          split; eauto.
          split.
          do 2 rewrite remLock_updThread_comm.
          eapply updThread_internal_execution; eauto.
          eapply remLock_internal_execution; eauto.
          apply mem_compatible_remlock; auto.
          now apply (lockRes_valid _ HinvC).
          split.
          (** proof of [strong_tsim] *)
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
          erewrite restrPermMap_irr' with (Hlt := (compat_th _ _ mem_compc' pfc').1)
                                            (Hlt' := (compat_th _ _ Hcompj pfc').1)
            by (rewrite gRemLockSetRes gsoThreadRes; auto).
          erewrite restrPermMap_irr' with (Hlt := (compat_th _ _ HmemCompF' pff0).1)
                                            (Hlt' := (compat_th _ _ (mem_compf Hsim) pffj).1)
            by (rewrite gRemLockSetRes gsoThreadRes; auto).
          eauto.
          erewrite restrPermMap_irr' with (Hlt := (compat_th _ _ mem_compc' pfc').2)
                                            (Hlt' := (compat_th _ _ Hcompj pfc').2)
            by (rewrite gRemLockSetRes gsoThreadRes; auto).
          erewrite restrPermMap_irr' with (Hlt := (compat_th _ _ HmemCompF' pff0).2)
                                            (Hlt' := (compat_th _ _ (mem_compf Hsim) pffj).2)
            by (rewrite gRemLockSetRes gsoThreadRes; auto).
          eauto.
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
                assert (HmemCompCj: mem_compatible tpcj mcj)
                  by (eapply internal_execution_compatible with (tp := tpc); eauto).
                specialize (Htsimj (containsThread_internal_execution Hexecj pfcj)
                                   HmemCompCj).
                eapply (injective (weak_obs_eq (obs_eq_data Htsimj)));
                  by eauto.
              }
              subst b1. congruence.
            - rewrite! setPermBlock_other_2; auto.
              rewrite! setPermBlock_var_other_2; auto.
              eapply Hownedj; eauto.
          }
          { rewrite gsoThreadRes; auto.
            eapply Hownedj; eauto.
          }
          split.
          (** lockRes ownership*)
          { intros.
            destruct (EqDec_address (b2, Ptrofs.intval ofs) (bl, ofsl)).
            - inversion e; subst.
              rewrite gsslockResRemLock in H1.
              discriminate.
            - rewrite gsolockResRemLock in H1; auto.
              rewrite gsoThreadLPool in H1.
              now eauto.
          }
          (** unmapped blocks*)
          intros.
          rewrite gRemLockSetRes.
          rewrite gsoThreadRes;
            now eauto.
        }
      - split.
        (** Proof of [strong_mem_obs_eq] for lock pool*)
        intros bl1 bl2 ofs0 rmap1' rmap2' Hfi Hres1' Hres2'.
        destruct (EqDec_address (b, Ptrofs.intval ofs) (bl1, ofs0)) as [Heql1 | Hneql1].
        { (** case it is the  removed lock *)
          exfalso.
          inversion Heql1; subst.
          rewrite gsslockResRemLock in Hres1'.
          discriminate.
        }
        { assert (Hneq2: (b2, Ptrofs.intval ofs) <> (bl2, ofs0)).
          { intros Hcontra; inversion Hcontra; subst.
            rewrite gsslockResRemLock in Hres2'.
            discriminate.
          }
          assert (Hres1: lockRes tpc (bl1, ofs0) = Some rmap1')
            by ( rewrite gsolockResRemLock in Hres1'; auto;
                 rewrite gsoThreadLPool in Hres1'; auto).
          assert (Hres2: lockRes tpf (bl2, ofs0) = Some rmap2')
            by ( rewrite gsolockResRemLock in Hres2'; auto;
                 rewrite gsoThreadLPool in Hres2'; auto).
          assert (Heq1: restrPermMap ((compat_lp _ _ HmemCompC' (bl1, ofs0) _ Hres1').1) =
                       restrPermMap ((compat_lp _ _ HmemCompC (bl1, ofs0) _ Hres1).1))
            by (erewrite restrPermMap_irr'; eauto).
          assert (HeqF: restrPermMap ((compat_lp _ _  HmemCompF' (bl2, ofs0) _ Hres2').1) =
                       restrPermMap ((compat_lp _ _ (mem_compf Hsim) (bl2, ofs0) _ Hres2).1))
            by (erewrite restrPermMap_irr'; eauto).
          assert (Heq2: restrPermMap ((compat_lp _ _ HmemCompC' (bl1, ofs0) _ Hres1').2) =
                        restrPermMap ((compat_lp _ _ HmemCompC (bl1, ofs0) _ Hres1).2))
            by (erewrite restrPermMap_irr'; eauto).
          assert (Heq2F: restrPermMap ((compat_lp _ _ HmemCompF' (bl2, ofs0) _ Hres2').2) =
                        restrPermMap ((compat_lp _ _ (mem_compf Hsim) (bl2, ofs0) _ Hres2).2))
            by (erewrite restrPermMap_irr'; eauto).
          rewrite Heq1 HeqF Heq2 Heq2F.
          eauto.
        }
        split.
        { (** proof that lockRes are mapped *)
          intros bl2 ofs0 Hres.
          destruct (EqDec_address (b2, Ptrofs.intval ofs) (bl2, ofs0)).
          - inversion e; subst.
            eexists; eauto.
          - rewrite gsolockResRemLock in Hres; auto.
            rewrite gsoThreadLPool in Hres;
            eauto.
        }
        { (** the two machines have the same [lockRes]*)
          intros bl1 bl2 ofs0 Hrenaming.
          destruct (EqDec_address (b, Ptrofs.intval ofs) (bl1, ofs0)) as [Heql1 | Hneql1].
          - (**case it is the  removed lock *)
            inversion Heql1; subst.
            assert (b2 = bl2)
              by (rewrite Hf in Hrenaming; inversion Hrenaming; by subst).
            subst bl2.
            split; intro Hcontra;
            rewrite gsslockResRemLock in Hcontra;
              by exfalso.
          - assert (Hneq2: (b2, Ptrofs.intval ofs) <> (bl2, ofs0))
              by (intros Hcontra; inversion Hcontra; subst;
                  specialize (Hinjective _ _ _ Hf Hrenaming); by subst).
            rewrite gsolockResRemLock; auto.
            rewrite gsoThreadLPool.
            rewrite gsolockResRemLock; auto.
            rewrite gsoThreadLPool.
            eauto.
        }
      - (** unmapped blocks in lock resources *)
        intros.
        destruct (EqDec_address (b2, Ptrofs.intval ofs) (bl, ofsl)) as [Heql1 | Hneql1].
        + inversion Heql1; subst.
          rewrite gsslockResRemLock in H.
          discriminate.
        + rewrite gsolockResRemLock in H; auto.
          rewrite gsoThreadLPool in H.
          now eauto.
      - (** Proof of invariant preservation for fine-grained *)
        destruct pmap_tid'. simpl in Hdata_perm, Hlock_perm.
        subst.
        eapply invariant_freelock;
          now eauto.
      - (** Max permission invariant*)
          by assumption.
      - (** new memory is well-defined*)
        assumption.
      - (** new tpc well defined*)
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
      - (** ge well defined*)
        assumption.
      - (** ge spec*)
        split; assumption.
      - intros.
        apply cntRemoveL;
          apply cntUpdate;
            by eauto.
      - econstructor;
          eauto.
        econstructor;
          now eauto.
    }
    { (** Failed lock acquire case*)
      subst tpc' mc'.
      (** We have that the code of the fine grained execution
        is related to the one of the coarse-grained*)
      assert (Hcore_inj:= code_eq Htsim).
      rewrite Hcode in Hcore_inj.
      simpl in Hcore_inj.
      subst.
      destruct (getThreadC pff) as [? | cf |? | ?] eqn:HcodeF;
        try by exfalso.
      (** And now we can prove that cf is also at external *)
      assert (Hat_external_spec := core_inj_ext _ _ Hfg Hge_wd Hge_incr Hvalid_mem' Hcore_inj (obs_eq_data Htsim)).
      rewrite Hat_external in Hat_external_spec.
      destruct (at_external semSem cf (restrPermMap (compat_th _ _ (mem_compf Hsim) pff)#1))
        as [[? vsf] | ] eqn:Hat_externalF;
        try by exfalso.
      (** and moreover that it's the same external and their
        arguments are related by the injection*)
      destruct Hat_external_spec as [? Harg_obs]; subst.
      inversion Harg_obs as [|? ? ? ? Hptr_obs Hl]; subst.
      inversion Hl; subst.
      inversion Hptr_obs as [| | | |b1 b2 ofs0 Hf|];
        subst b1 ofs0 v'.
      (** We prove that b is valid in m1 (and mc)*)
      remember (restrPermMap (compat_th _ _ (mem_compf Hsim) pff).2) as mf1 eqn:Hrestrict_pmapF.
      (** and prove that loading from that block in mf gives us the
        same value as in mc, i.e. unlocked*)
      assert (HloadF: Mem.load Mint32 mf1 b2 (Ptrofs.intval ofs) = Some (Vint Int.zero)).
      { destruct (load_val_obs _ _ _ Hload Hf Hinjective (strong_obs_eq (obs_eq_locks Htsim)))
          as [v2 [Hloadf Hobs_eq]].
        inversion Hobs_eq; subst.
          by auto.
      }
      (** The state is not changed by a failed load*)
      exists tpf, mf, (fp i pfc), fp, (trf ++ [:: (external i (failacq (b2, Ptrofs.intval ofs)))]).
      split.
      intros U.
      subst.
      econstructor 5; simpl; eauto.
      econstructor 6; eauto.
      destruct Htsim.
      destruct obs_eq_locks0 as [_ [Hperm_eq ?]].
      unfold Mem.range_perm, Mem.perm, permission_at in *.
      intros.
      erewrite Hperm_eq;
        now eauto.
      (** Proof that the new coarse and fine state are in simulation*)
      eapply sim_reduce; eauto.
      econstructor; eauto.
      destruct Hsim.
      eauto.
      econstructor;
        eauto.
      econstructor;
        now eauto.
    }
    Unshelve. all:eauto.
    eapply store_compatible; eauto. eapply (mem_compf Hsim).
    eapply store_compatible; eauto. eapply (mem_compf Hsim).
Admitted.

End SimProofs.

End SimProofs.
