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
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import concurrency.mem_obs_eq.
Require Import concurrency.x86_inj.
Require Import concurrency.compcert_threads_lemmas.
Require Import concurrency.dry_context.
Require Import sepcomp.closed_safety.

Import dry_context SEM mySchedule DryMachine DryMachine.ThreadPool.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

(** ** Safety for X86 interleaving semantics *)
Module X86Safe.

  Module SimDefs := SimDefs X86Inj.
  Module SimProofs := SimProofs X86Inj.
  Import SimDefs SimProofs X86Inj dry_machine_lemmas.
  Import Renamings MemObsEq ValObsEq ValueWD.

Section CSPEC.
  Context {cspec: CoreLanguage.corestepSpec}.
  
  Import Asm Asm_coop event_semantics.

Require Import Coqlib.
Require Import msl.Coqlib2.

Lemma x86_corestep_fun:  corestep_fun Sem.
Proof.
  hnf; intros.
  inv H; inv H0;
  repeat 
    match goal with
    | H: ?A = _, H':?A=_ |- _ => inversion2 H H' 
    | H: ?A, H': ?A |- _ => clear H'
    end;
  try congruence; try now (split; auto).
  pose proof (extcall_arguments_determ _ _ _ _ _ H3 H10).
  subst args0; auto.
Qed.

Lemma mem_step_decay:
  forall m m',
     mem_step m m' ->
    decay m m'.
Proof.
 induction 1.
*
 split; intros.
 contradiction H0; clear H0.
 eapply Mem.storebytes_valid_block_2; eauto.
 right. intros.
 apply Mem.storebytes_access in H.
 rewrite H; auto.
*
 split; intros.
+
 assert (b=b').
 pose proof (Mem.nextblock_alloc _ _ _ _ _ H).
 apply Mem.alloc_result in H. subst.
 unfold Mem.valid_block in *.
 rewrite H2 in H1; clear H2.
 apply Plt_succ_inv in H1. destruct H1; auto.
 contradiction. subst b'. clear - H.
 Transparent Mem.alloc. unfold Mem.alloc in H. Opaque Mem.alloc.
  inv H. simpl.
 destruct (base.range_dec lo ofs hi); [left | right]; intros.
 rewrite PMap.gss. destruct (zle lo ofs); try omega. destruct (zlt ofs hi); try omega.
 reflexivity.
 rewrite PMap.gss.
 destruct (zle lo ofs), (zlt ofs hi); try reflexivity.
 omega.
 +
 assert (b<>b').
 intro. subst b'. apply Mem.alloc_result in H. subst b.
 unfold Mem.valid_block in H0. apply Plt_ne in H0.
 contradiction H0; auto.
 right. intro.
 Transparent Mem.alloc. unfold Mem.alloc in H. Opaque Mem.alloc.
  inv H. simpl.
  erewrite PMap.gso by auto. auto.
*
 revert m H; induction l; intros. inv H. apply decay_refl.
 simpl in H. destruct a. destruct p. 
 destruct (Mem.free m b z0 z) eqn:?H; inv H.
 apply decay_trans with m0; [ | | eapply IHl; eauto].
 eapply Mem.valid_block_free_1; eauto.
 clear  - H0. rename m0 into m'. rename z0 into lo. rename z into hi.
 Transparent Mem.free. unfold Mem.free in H0. Opaque Mem.free.
 if_tac in H0; inv H0.
 unfold Mem.unchecked_free; hnf; unfold Mem.valid_block; simpl.
 split; intros; simpl. contradiction.
 destruct (adr_range_dec (b,lo) (hi-lo) (b0,ofs)).
 destruct a. subst b0. rewrite !PMap.gss. specialize (H ofs).
 left; intro.
 destruct (zle lo ofs); try omega. destruct (zlt ofs hi); try omega.
 split; simpl; auto. spec H; [omega |].
 hnf in H. match type of H with match ?A with _ => _ end => destruct A eqn:?H end; try contradiction.
 assert (p=Freeable). inv H; auto. subst p. clear H.
 destruct k; auto.
 pose proof (Mem.access_max m b ofs).
 rewrite H1 in H.
 match goal with |- ?A = _ => destruct A; inv H end; auto.
 clear H.
 right. intros.
 destruct (peq b b0); auto. subst b0. rewrite PMap.gss.
 unfold adr_range in n.
 assert (~ (lo <= ofs < hi)) by (contradict n; split; auto; omega).
 destruct (zle lo ofs); try reflexivity.
 destruct (zlt ofs hi); try reflexivity. omega.
 erewrite PMap.gso by auto. auto.
*
 apply decay_trans with m''; auto.
 apply mem_step_nextblock in H.
 unfold Mem.valid_block; intros.
 eapply Plt_Ple_trans; try apply H1. apply H.
Qed.

Lemma exec_load_same_mem:
  forall ge ch m a rs rd rs' m',
   exec_load ge ch m a rs rd = Next rs' m' ->
   m=m'.
Proof.
intros.
unfold exec_load in H.
destruct (Mem.loadv ch m (eval_addrmode ge a rs)) eqn:?; inv H.
reflexivity.
Qed.

Lemma exec_store_obeys_cur_write:
  forall ge ch m a rs rs0 d rs' m',
   exec_store ge ch m a rs rs0 d = Next rs' m' ->
   forall b ofs, 
     Mem.valid_block m b ->
     ~ Mem.perm m b ofs Cur Writable ->
  ZMap.get ofs (PMap.get b (Mem.mem_contents m)) =
  ZMap.get ofs (PMap.get b (Mem.mem_contents m')).
Proof.
intros.
 unfold exec_store in H.
 destruct (Mem.storev ch m (eval_addrmode ge a rs) (rs rs0)) eqn:?; inv H.
 unfold Mem.storev in Heqo.
 destruct (eval_addrmode ge a rs); inv Heqo.
 symmetry;
 eapply MemoryLemmas.store_contents_other; eauto.
Qed.

Lemma mem_step_obeys_cur_write:
  forall m b ofs m',
    Mem.valid_block m b ->
   ~ Mem.perm m b ofs Cur Writable ->
   mem_step m m' ->
 ZMap.get ofs (PMap.get b (Mem.mem_contents m)) =
 ZMap.get ofs (PMap.get b (Mem.mem_contents m')).
Proof.
 intros.
 induction H1.
*
  revert m ofs0 H H0 H1; induction bytes; intros.
 Transparent Mem.storebytes.
 unfold Mem.storebytes in H1.
 destruct (Mem.range_perm_dec m b0 ofs0
         (ofs0 + Z.of_nat (length nil)) Cur Writable);
  inv H1; simpl.
 destruct (peq b b0). subst b0.
 rewrite PMap.gss. auto.
 rewrite PMap.gso; auto.
 change (a::bytes) with ((a::nil)++bytes) in H1.
 apply Mem.storebytes_split in H1.
 destruct H1 as [m1 [? ?]].
 etransitivity.
 2: eapply IHbytes; try apply H2.
 clear H2 IHbytes.
 unfold Mem.storebytes in H1. 
Opaque Mem.storebytes.
 destruct (Mem.range_perm_dec m b0 ofs0
         (ofs0 + Z.of_nat (length (a :: nil))) Cur Writable);
 inv H1; simpl.
 destruct (peq b b0). subst b0.
 rewrite PMap.gss.
 destruct (zeq ofs0 ofs). subst.
 contradiction H0. apply r. simpl. omega.
 rewrite ZMap.gso; auto. 
 rewrite PMap.gso; auto.
 clear - H H1.
 eapply Mem.storebytes_valid_block_1; eauto.
 contradict H0. clear - H1 H0.
 eapply Mem.perm_storebytes_2; eauto.
*
 apply AllocContentsOther with (b':=b) in H1.
 rewrite H1. auto. intro; subst.
 apply Mem.alloc_result in H1; unfold Mem.valid_block in H.
 subst. apply Plt_strict in H; auto.
*
 revert m H H0 H1; induction l; simpl; intros.
 inv H1; auto.
 destruct a. destruct p.
 destruct (Mem.free m b0 z0 z) eqn:?; inv H1.
 rewrite <- (IHl m0); auto.
 eapply free_contents; eauto.
 intros [? ?]. subst b0. apply H0.
 apply Mem.free_range_perm in Heqo.
   specialize (Heqo ofs).
   spec Heqo; [omega | ].
   eapply Mem.perm_implies; eauto. constructor.
 clear - H Heqo.
 unfold Mem.valid_block in *.
 apply Mem.nextblock_free in Heqo. rewrite Heqo.
 auto.
 clear - H0 Heqo.
 contradict H0.
 eapply Mem.perm_free_3; eauto.
*
 assert (Mem.valid_block m'' b). {
   apply mem_step_nextblock in H1_.
   unfold Mem.valid_block in *.
   eapply Plt_le_trans; eauto.
 }
 erewrite IHmem_step1 by auto. apply IHmem_step2; auto.
 contradict H0.
 clear - H H1_ H0.
 revert H H0; induction H1_; intros.
 eapply Mem.perm_storebytes_2; eauto.
 pose proof (Mem.perm_alloc_inv _ _ _ _ _ H _ _ _ _ H1).
 if_tac in H2; auto. subst b'.
 pose proof (Mem.alloc_result _ _ _ _ _ H).
 subst. apply Plt_strict in H0. contradiction.
 eapply Mem.perm_free_list in H; try apply H1.
 destruct H; auto.
 eapply IHH1_1; auto. eapply IHH1_2; eauto.
 apply mem_step_nextblock in H1_1.
 unfold Mem.valid_block in *.
 eapply Plt_le_trans; eauto.
Qed.

Instance x86Spec : CoreLanguage.corestepSpec.
  Proof.
    split.
    intros m m' m'' ge c c' c'' Hstep Hstep'.
    *
      eapply x86_corestep_fun; eauto.
    * 
      intros.
      hnf in Hstep. 
      apply asm_mem_step in Hstep.
      eapply mem_step_obeys_cur_write; auto.
    * 
      intros.
      apply mem_step_decay.
      apply asm_mem_step in H; auto.
    *
      intros.
      apply mem_step_nextblock.
      apply asm_mem_step in H; auto.
  Qed.

End CSPEC.

Import MemoryWD SimDefs ThreadPoolInjections StepLemmas event_semantics.
Definition tpc_init f arg := initial_core coarse_semantics the_ge f arg.
Definition tpf_init f arg := initial_core fine_semantics the_ge f arg.

(** For now, we assume that the initial memory has no invalid
pointers, but it should be provable*)
Axiom init_mem_wd:
  forall m, init_mem = Some m -> valid_mem m.

(** Also assuming that the initial core will be well-defined*)
Axiom init_core_wd:
  forall v args m,
    init_mem = Some m ->
    match initial_core SEM.Sem the_ge v args with
    | Some c => core_wd (id_ren m) c
    | None => True
    end.

(** Excluded middle is required, but can be easily lifted*)
Axiom em : ClassicalFacts.excluded_middle.

Lemma init_tp_wd:
  forall v args m tp,
    init_mem = Some m ->
    init_mach init_perm the_ge v args = Some tp ->
    tp_wd (id_ren m) tp.
Proof.
  intros.
  intros i cnti.
  unfold init_mach in H0.
  destruct (initial_core SEM.Sem the_ge v args) eqn:?, init_perm; try discriminate.
  inversion H0; subst.
  simpl. split; auto.
  pose proof (init_core_wd v args H).
  rewrite Heqo in H1; auto.
Qed.
    
(** Assuming safety of cooperative concurrency*)
Axiom init_coarse_safe:
  forall f arg U tpc mem sched n,
    init_mem = Some mem ->
    tpc_init f arg = Some (U, [::], tpc) ->
    csafe the_ge (sched,[::],tpc) mem n.

(** If the initial state is defined then the initial memory was also
defined*)
Lemma tpc_init_mem_defined:
  forall f arg U tpc,
    tpc_init f arg = Some (U, tpc) ->
    exists m, init_mem = Some m.
Proof.
  unfold tpc_init. simpl.
  unfold myCoarseSemantics.init_machine.
  unfold init_mach. intros.
  destruct init_perm eqn:?.
  unfold init_perm in *.
  destruct init_mem; try discriminate.
  eexists; reflexivity.
  destruct (initial_core SEM.Sem the_ge f arg); try discriminate.
Qed.

(** The global env is well-defined *)
Lemma the_ge_wd:
  forall m,
    init_mem = Some m ->
    ge_wd (id_ren m) the_ge.
Proof.
  intros. unfold init_mem in H.
  unfold the_ge.
  constructor.
  - intros b Hfuns.
    destruct ((Genv.genv_funs (Genv.globalenv the_program)) ! b) eqn:Hget;
      try by exfalso.
    apply Genv.genv_funs_range in Hget.
    erewrite Genv.init_mem_genv_next in Hget by eauto.
    apply id_ren_validblock in Hget.
    rewrite Hget; auto.
  - split; intros.
    destruct ((Genv.genv_vars (Genv.globalenv the_program)) ! b) eqn:Hget;
      try by exfalso.
    apply Genv.genv_vars_range in Hget.
    erewrite Genv.init_mem_genv_next in Hget by eauto.
    apply id_ren_validblock in Hget.
    rewrite Hget; auto.
    unfold Senv.symbol_address in H0.
    destruct (Senv.find_symbol (Genv.globalenv the_program) id) eqn:Hfind.
    apply Senv.find_symbol_below in Hfind.
    unfold Senv.nextblock in Hfind. simpl in Hfind.
    erewrite Genv.init_mem_genv_next in Hfind by eauto.
    unfold valid_val. rewrite <- H0.
    apply id_ren_validblock in Hfind. eexists; eauto.
    subst. simpl; auto.
Qed.

(** Simulation relation with id renaming for initial memory*)
Lemma init_mem_obs_eq :
  forall m tp f args i (cnti : containsThread tp i)
    (Hcomp: mem_compatible tp m)
    (HcompF: mem_compatible tp (diluteMem m)),
    init_mem = Some m ->
    init_mach init_perm the_ge f args = Some tp ->
    mem_obs_eq (id_ren m) (restrPermMap (Hcomp _ cnti))
               (restrPermMap (HcompF _ cnti)).
Proof.
  intros.
  pose proof (mem_obs_eq_id (init_mem_wd H)) as Hobs_eq_id.
  unfold init_mach in H0.
  destruct (initial_core SEM.Sem the_ge f args), init_perm eqn:Hinit_perm;
    try discriminate.
  inversion H0; subst.
  unfold init_perm in Hinit_perm.
  rewrite H in Hinit_perm.
  inversion Hinit_perm. subst.
  destruct Hobs_eq_id.
  constructor.
  - constructor;
    destruct weak_obs_eq0; eauto.
    intros.
    do 2 rewrite restrPermMap_Cur.
    simpl.
    apply id_ren_correct in Hrenaming. subst.
    apply po_refl.
  - constructor.
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
Qed.
    
Lemma init_compatible:
  forall tp f arg m,
    init_mem = Some m ->
    init_mach init_perm the_ge f arg = Some tp ->
    mem_compatible tp m.
Proof.
  intros.
  unfold init_mach in *.
  destruct (initial_core SEM.Sem the_ge f arg); try discriminate.
  unfold init_perm in *. rewrite H in H0.
  inversion H0; subst.
  constructor.
  intros j cntj.
  simpl.
  unfold permMapLt; intros.
  apply po_refl.
  unfold initial_machine. simpl. intros.
  unfold lockRes in H1.
  simpl in H1.
  rewrite threadPool.find_empty in H1. discriminate.
  unfold initial_machine, lockSet.
  simpl. unfold addressFiniteMap.A2PMap.
  simpl.
  intros b ofs. rewrite Maps.PMap.gi.
  destruct ((getMaxPerm m) # b ofs); simpl; auto.
Qed.

Lemma init_thread:
  forall f arg tp i,
    init_mach init_perm the_ge f arg = Some tp ->
    containsThread tp i ->
    containsThread tp 0.
Proof.
  intros.
  unfold init_mach in *.
  unfold initial_machine in *.
  repeat match goal with
         | [H: match ?Expr with _ => _ end = _ |- _] =>
           destruct Expr eqn:?; try discriminate
         end.
  simpl in H. inversion H; subst.
  unfold containsThread. simpl.
  ssromega.
Qed.

Lemma strong_tsim_refl:
  forall tp f args m i (cnti: containsThread tp i)
    (Hcomp: mem_compatible tp m)
    (HcompF: mem_compatible tp (diluteMem m)),
    init_mem = Some m ->
    init_mach init_perm the_ge f args = Some tp ->
    strong_tsim (id_ren m) cnti cnti Hcomp HcompF.
Proof.
  intros.
  constructor.
  eapply ctl_inj_id; eauto.
  pose proof (init_tp_wd f args).
  specialize (H1 _ _ H H0 i cnti).
  auto.
  apply id_ren_correct.
  eapply init_mem_obs_eq; eauto.
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
  forall f arg U U' tpc tpf m n,
    tpc_init f arg = Some (U, [::], tpc) ->
    tpf_init f arg = Some (U', [::], tpf) ->
    init_mem = Some m ->
    sim tpc m tpf (diluteMem m) nil (id_ren m) (id_ren m) (fun i cnti => id_ren m) n.
Proof.
  intros.
  unfold tpc_init, tpf_init in *. simpl in *.
  unfold myCoarseSemantics.init_machine, myFineSemantics.init_machine in *.
  destruct (init_mach init_perm the_ge f arg) eqn:Hinit; try discriminate.
  inversion H; subst. inversion H0; subst.
  clear H H0.
  assert (HmemComp := init_compatible f arg H1 Hinit).
  assert (HmemCompF: mem_compatible tpf (diluteMem m))
    by (eapply mem_compatible_setMaxPerm; eauto).
  eapply Build_sim with (mem_compc := HmemComp) (mem_compf := HmemCompF).
  - intros; split; auto.
  - simpl. rewrite addn0.
    intros.
    eapply init_coarse_safe with (f := f) (arg := arg) (n := n); eauto.
    unfold tpc_init. simpl. unfold myCoarseSemantics.init_machine.
    rewrite Hinit. reflexivity. 
  - intros i cnti cnti'.
    pose proof (strong_tsim_refl _ _ cnti HmemComp HmemCompF H1 Hinit).
    pf_cleanup.
    destruct H. destruct obs_eq0.
    eauto.
  - intros; by congruence.
  - intros.
    exists tpf, m.
    split; eauto with renamings.
    split; eauto.
    split; first by constructor.
    split.
    intros; pf_cleanup.
    eapply strong_tsim_refl; eauto.
    repeat (split; intros); congruence.
  - unfold init_mach in *.
    unfold init_perm in Hinit.
    rewrite H1 in Hinit.
    destruct (initial_core SEM.Sem the_ge f arg); try discriminate.
    inversion Hinit; subst.
    split.
    constructor.
    intros.
    do 2 rewrite restrPermMap_Cur.
    unfold initial_machine, lockSet. simpl.
    unfold addressFiniteMap.A2PMap. simpl.
    do 2 rewrite Maps.PMap.gi; reflexivity.
    intros.
    assert (Heq := restrPermMap_Cur (compat_ls HmemComp) b1 ofs).
    unfold permission_at in Heq.
    unfold Mem.perm in Hperm.
    rewrite Heq in Hperm.
    unfold lockSet, initial_machine, addressFiniteMap.A2PMap in Hperm.
    simpl in Hperm.
    rewrite Maps.PMap.gi in Hperm.
    simpl in Hperm. exfalso; auto.
    intros. unfold lockRes, initial_machine in H. simpl in H.
      by exfalso.
  - unfold init_mach, init_perm in Hinit.
    rewrite H1 in Hinit.
    destruct (initial_core SEM.Sem the_ge f arg); try discriminate.
    inversion Hinit; subst.
    unfold lockRes, initial_machine. simpl.
    split; intros.
    exfalso.
    rewrite threadPool.find_empty in Hl1; discriminate.
    split; auto.
  - unfold init_mach, init_perm in Hinit.
    rewrite H1 in Hinit.
    destruct (initial_core SEM.Sem the_ge f arg); try discriminate.
    inversion Hinit; subst.
    apply DryMachineLemmas.initial_invariant.
  - apply setMaxPerm_inv; auto.
  - apply init_mem_wd; auto.
  - eapply init_tp_wd; eauto.
  - unfold the_ge.
    eapply the_ge_wd; eauto.
  - split; eauto with renamings.
    apply id_ren_correct.
  - simpl. tauto.
Qed.

(** Safety of the FineConc machine*)

Import StepType.

Notation fsafe := (myFineSemantics.fsafe the_ge).

(*TODO: Put in threadpool*)
Definition containsThread_dec:
  forall i tp, {containsThread tp i} + { ~ containsThread tp i}.
Proof.
  intros.
  unfold containsThread.
  destruct (leq (S i) (num_threads tp)) eqn:Hleq;
    by auto.
Qed.

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


Lemma fine_safe:
  forall tpf tpc mf mc (f fg : memren) fp (xs : Sch) sched
    (Hsim: sim tpc mc tpf mf xs f fg fp (S (size sched))),
    exists tr,
    fsafe tpf mf sched tr (S (size sched)).
Proof.
  intros.
  generalize dependent xs.
  generalize dependent mf.
  generalize dependent tpf.
  generalize dependent fp.
  generalize dependent tpc.
  generalize dependent mc.
  generalize dependent f.
  induction sched as [|i sched]; intros; simpl; auto.
  exists [::].
  econstructor. simpl; eauto.
  destruct (containsThread_dec i tpf) as [cnti | invalid].
  - (* By case analysis on the step type *)
    destruct (getStepType cnti) eqn:Htype.
    + pose proof (sim_internal [::] cnti Htype Hsim) as (tpf' & m' & fp' & tr' & Hstep & Hsim').
      specialize (Hstep sched).
      destruct (IHsched _ _ _ _ _ _ _ Hsim') as [tr'' Hsafe''].
      exists (tr' ++ tr'').
      econstructor 3; simpl; eauto.
    + assert (~ List.In i xs)
        by (eapply at_external_not_in_xs; eauto).
      pose proof (sim_external em [::] cnti Htype H Hsim) as Hsim'.
      destruct Hsim' as (? & ? & ? & ? & ? & ? & tr' & Hstep & Hsim'').
      destruct (IHsched _ _ _ _ _ _ _ Hsim'') as [tr'' Hsafe''].
      specialize (Hstep sched).
      exists (tr' ++ tr'').
      econstructor 3; simpl; eauto.
    + pose proof (sim_halted [::] cnti Htype Hsim) as Hsim'.
      destruct Hsim' as (tr' & Hstep & Hsim'').
      destruct (IHsched _ _ _ _ _ _ _ Hsim'') as [tr'' Hsafe''].
      specialize (Hstep sched).
      exists (tr' ++ tr'').
      econstructor 3;
      eauto.
    + pose proof (sim_suspend [::] cnti Htype Hsim) as
          (? & ? & tpf' & m' & ? & ? & tr' & Hstep & Hsim').
      destruct (IHsched _ _ _ _ _ _ _ Hsim') as [tr'' Hsafe''].
      specialize (Hstep sched).
      exists (tr' ++ tr'').
      econstructor 3; simpl; eauto.
  -  pose proof (sim_fail [::] invalid Hsim) as
      (tr' & Hstep & Hsim').
    destruct (IHsched _ _ _ _ _ _ _ Hsim') as [tr Hsafe].
    exists ([::] ++ tr).
    econstructor 3; eauto.
    econstructor 7; simpl; eauto.
Qed.


(** Safety preservation for the FineConc machine*)
Theorem init_fine_safe:
  forall f arg U tpf m
    (Hmem: init_mem = Some m)
    (Hinit: tpf_init f arg = Some (U, [::], tpf)),
  forall (sched : Sch),
    exists tr,
      fsafe tpf (diluteMem m) sched tr (size sched).+1.
Proof.
  intros.
  assert (Hsim := init_sim f arg (size sched).+1 Hinit Hinit Hmem).
  clear - Hsim.
  eapply fine_safe; eauto.
Qed.
  
End X86Safe.

  
  



