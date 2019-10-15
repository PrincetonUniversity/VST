(* Clight Safety*)

(**
   Prove that csafety in Clight_new implies safety in Clight. 
*)
Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.cfrontend.Ctypes.
Require Import VST.concurrency.common.core_semantics.
Require Import VST.concurrency.common.bounded_maps.
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.ClightSemanticsForMachines.
Require Import VST.concurrency.common.ClightMachine.
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.juicy.semax_simlemmas.
Require Import VST.concurrency.juicy.semax_to_juicy_machine.
Require Import VST.concurrency.juicy.mem_wd2.
Require Import VST.concurrency.juicy.Clight_mem_ok.
(*Require Import VST.veric.Clight_sim.*)
Require Import VST.msl.eq_dec.
Require Import VST.concurrency.memsem_lemmas.
Require Import BinNums.
Require Import List.

Import HybridMachineSig.
Import HybridMachine.
Import HybridCoarseMachine.
Import ListNotations.
Import ThreadPool.
Import event_semantics.

Set Bullet Behavior "Strict Subproofs".
Set Nested Proofs Allowed.

Section Clight_safety_equivalence.
Context (CPROOF : semax_to_juicy_machine.CSL_proof).
Definition prog:= CPROOF.(CSL_prog).
Definition ge:= Clight.globalenv prog.
Definition init_mem:= proj1_sig (init_mem CPROOF).

(*We should be able to construct a Clight.state from the proof... *)
Definition f_main : {f | Genv.find_funct_ptr (Clight.genv_genv ge) (projT1 (spr CPROOF)) = Some f}.
Proof.
  destruct (spr CPROOF) as (b & q & [? Hinit] & s); simpl in *.
  unfold juicy_extspec.j_initial_core in Hinit; simpl semantics.initial_core in Hinit.
  destruct (s O) as (jm & Hjm & _).
  specialize (Hinit _ Hjm); simpl Genv.find_funct_ptr in Hinit.
  unfold prog, semax_to_juicy_machine.prog in *.
  destruct (Genv.find_funct_ptr _ _); eauto.
  exfalso.
  destruct Hinit as (? & ? & ? & ?). contradiction.
Defined.

(* Clight_new starts a step earlier than Clight, with a sequence of the initial call to main and
   an infinite loop. *)
(* stub for the "function" that provides main's arguments on the stack *)
Definition main_handler : Clight.function :=
  {| Clight.fn_return := Ctypes.Tvoid; Clight.fn_callconv := AST.cc_default; Clight.fn_params := nil;
     Clight.fn_vars := nil; Clight.fn_temps := nil; Clight.fn_body := Clight.Sskip |}.

(* This could be simplified if we made some assumptions about main (e.g., that it has no arguments). *)
Definition initial_Clight_state : Clight.state :=
  let f := proj1_sig f_main in
  Clight.Callstate f [Vptr (projT1 (spr CPROOF)) Ptrofs.zero] (Clight.Kstop Tnil) init_mem.
(*
  Clight.State main_handler (Clight.Scall None (Clight.Etempvar 1%positive (Clight.type_of_fundef f))
             (map (fun x => Clight.Etempvar (fst x) (snd x))
             (Clight_core.params_of_types 2 (Clight_core.params_of_fundef f))))
               (Clight.Kseq (Clight.Sloop Clight.Sskip Clight.Sskip) Clight.Kstop) Clight.empty_env
             (temp_bindings 1 [Vptr (projT1 (spr CPROOF)) Ptrofs.zero]) init_mem.
*)

(*
(*...And we should be able to construct an initial state from the Clight_new and mem.*)
(* See also veric/Clight_sim.v. *)
Fixpoint make_cont k :=
  match k with
  | nil => Clight.Kstop
  | Clight_new.Kseq s :: k' => Clight.Kseq s (make_cont k')
  | Clight_new.Kloop1 s1 s2 :: k' => Clight.Kloop1 s1 s2 (make_cont k')
  | Clight_new.Kloop2 s1 s2 :: k' => Clight.Kloop2 s1 s2 (make_cont k')
  | Clight_new.Kswitch :: k' => Clight.Kswitch (make_cont k')
  | Clight_new.Kcall r f e te :: k' => Clight.Kcall r f e te (make_cont k')
  end.

(* This function assumes that q is an initial state. *)
Definition new2Clight_state (q : Clight_core.state) (m : mem) : option Clight.state :=
  match q with
  | Clight_new.State e te (Clight_new.Kseq s :: k) =>
      Some (Clight.State main_handler s (make_cont k) e te m)
(*  | Clight_new.ExtCall f args _ e te k => Some (Clight.Callstate (External f tyargs tyret cc) args (make_cont k) m)*)
(* main shouldn't be an extcall anyway *)
  | _ => None
  end.

(*The two constructions coincide.*)
Lemma initial_Clight_state_correct:
  new2Clight_state
    (initial_corestate CPROOF)
    init_mem = Some initial_Clight_state.
Proof.
  unfold initial_corestate, initial_Clight_state.
  destruct f_main as [f Hf].
  destruct spr as (b & q & [? Hinit] & H); simpl.
  destruct (H O tt) as (jm & Hjm & ?).
  destruct (Hinit _ Hjm) as (? & ? & Hinit' & ?); subst.
  simpl in Hinit', Hf.
  unfold prog, semax_to_juicy_machine.prog in *.
  rewrite Hf in Hinit'.
  destruct (Clight.type_of_fundef f); try contradiction.
  destruct Hinit' as (? & ? & ? & ?); subst; auto.
Qed.
*)

Inductive match_ctl : ctl -> ctl -> Prop :=
| match_Krun c c' :  c = (fst (veric.Clight_core.CC_state_to_CC_core c')) -> match_ctl (Krun c) (Krun c')
| match_Kblocked c c' : c = (fst (veric.Clight_core.CC_state_to_CC_core c')) -> match_ctl (Kblocked c) (Kblocked c')
| match_Kresume c c' v : c = (fst (veric.Clight_core.CC_state_to_CC_core c')) -> match_ctl (Kresume c v) (Kresume c' v)
| match_Kinit v v' : match_ctl (Kinit v v') (Kinit v v').

(* This should essentially reproduce Clight_sim at the hybrid machine level. *)
Inductive match_st (tp : ThreadPool.t(resources := dryResources)(ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=Clight_newSem ge)))
  (tp' : ThreadPool.t(resources := dryResources)(ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))) : Prop :=
    MATCH_ST: forall (mtch_cnt: forall {tid},  containsThread tp tid -> containsThread tp' tid)
                (mtch_cnt': forall {tid}, containsThread tp' tid -> containsThread tp tid)
                (mtch_gtc: forall {tid} (Htid:containsThread tp tid)(Htid':containsThread tp' tid),
                    match_ctl (getThreadC Htid) (getThreadC Htid'))
                (mtch_gtr1: forall {tid} (Htid:containsThread tp tid)(Htid':containsThread tp' tid)
                    b ofs,
                    (fst (getThreadR Htid)) !! b ofs = (fst (getThreadR Htid')) !! b ofs)
                (mtch_gtr2: forall {tid} (Htid:containsThread tp tid)(Htid':containsThread tp' tid),
                    snd (getThreadR Htid) = snd (getThreadR Htid'))
                (mtch_locks: forall a, lockRes tp a = lockRes tp' a)
                (mtch_latest: latestThread tp = latestThread tp'),
      match_st tp tp'.

Lemma MTCH_compat: forall js ds m,
    match_st js ds ->
    mem_compatible js m ->
    mem_compatible ds m.
Proof.
  intros ? ? ? MTCH mc.
  inversion MTCH; inv mc; constructor; intros.
  - specialize (compat_th0 _ (mtch_cnt' _ cnt)) as [Hlt ?].
    rewrite mtch_gtr2 with (Htid' := cnt) in *; split; auto.
    intros ??; erewrite <- mtch_gtr1; eauto.
  - rewrite <- mtch_locks in H; eauto.
  - rewrite <- mtch_locks in H; eauto.
Qed.

Lemma MTCH_install_perm:
  forall js ds m m' tid (MATCH : match_st js ds)
    (Hcmpt : mem_compatible js m) (Htid : containsThread js tid) (Htid' : containsThread ds tid)
    (Hperm : install_perm _ _ _ Hcmpt Htid m'),
    install_perm _ _ _ (MTCH_compat _ _ _ MATCH Hcmpt) Htid' m'.
Proof.
  simpl; intros.
  hnf in *; subst.
  apply restrPermMap_ext; intro.
  inv MATCH.
  extensionality ofs.
  rewrite mtch_gtr1 with (Htid' := Htid'); auto.
Qed.

Lemma MTCH_invariant:
  forall js ds (MATCH : match_st js ds) (Hinv : invariant js), invariant ds.
Proof.
  intros; inversion MATCH; inv Hinv; constructor; intros.
  - split.
    + intros ??; erewrite <- !mtch_gtr1; apply no_race_thr0; auto.
    + erewrite <- !mtch_gtr2; apply no_race_thr0; auto.
  - rewrite <- mtch_locks in *; eauto.
  - rewrite <- mtch_locks in *; split.
    + intros ??; erewrite <- mtch_gtr1; eapply no_race0; eauto.
    + erewrite <- mtch_gtr2; eapply no_race0; eauto.
  - specialize (thread_data_lock_coh0 _ (mtch_cnt' _ cnti)) as [].
    split; intros.
    + erewrite <- mtch_gtr2.
      intros ??; erewrite <- mtch_gtr1; apply H.
    + erewrite <- mtch_gtr2.
      rewrite <- mtch_locks in *; eauto.
  - rewrite <- mtch_locks in *.
    specialize (locks_data_lock_coh0 _ _ Hres) as [].
    split; intros.
    + intros ??; erewrite <- mtch_gtr1; apply H.
    + rewrite <- mtch_locks in *; eauto.
  - hnf in *.
    intros; rewrite <- mtch_locks.
    specialize (lockRes_valid0 b ofs).
    destruct (lockRes(ThreadPool := OrdinalPool.OrdinalThreadPool) js (b, ofs)) eqn: Hl; auto.
    intros; rewrite <- mtch_locks; auto.
  Unshelve.
  all: auto.
Qed.

Lemma MTCH_updThread:
  forall tp tp' tid c c' r r' (MATCH : match_st tp tp')
    (Htid : containsThread tp tid) (Htid' : containsThread tp' tid) (Hctl : match_ctl c c')
    (Hr1: forall b ofs, (fst r) !! b ofs = (fst r') !! b ofs) (Hr2: snd r = snd r'),
  match_st (updThread Htid c r) (updThread Htid' c' r').
Proof.
  inversion 1; intros; constructor; auto; intros.
  - destruct (eq_dec tid0 tid).
    + subst; rewrite !gssThreadCode; auto.
    + unshelve erewrite !gsoThreadCode; auto.
  - destruct (eq_dec tid0 tid).
    + subst; rewrite !gssThreadRes; auto.
    + unshelve erewrite !gsoThreadRes; auto.
  - destruct (eq_dec tid0 tid).
    + subst; rewrite !gssThreadRes; auto.
    + unshelve erewrite !gsoThreadRes; auto.
Qed.

Lemma MTCH_updThreadC:
  forall tp tp' tid c c' (MATCH : match_st tp tp')
    (Htid : containsThread tp tid) (Htid' : containsThread tp' tid) (Hctl : match_ctl c c'),
  match_st (updThreadC Htid c) (updThreadC Htid' c').
Proof.
  inversion 1; intros; constructor; auto; intros.
  destruct (eq_dec tid0 tid).
  + subst; rewrite !gssThreadCC; auto.
  + unshelve erewrite <- !gsoThreadCC; auto.
Qed.

Lemma MTCH_updLockSet:
  forall tp tp' a l (MATCH : match_st tp tp'),
  match_st (updLockSet tp a l) (updLockSet tp' a l).
Proof.
  inversion 1; intros; constructor; auto; intros.
  destruct (eq_dec a0 a).
  - subst; rewrite !gssLockRes; auto.
  - rewrite !gsoLockRes; auto.
Qed.

Lemma MTCH_remLockSet:
  forall tp tp' a (MATCH : match_st tp tp'),
  match_st (remLockSet tp a) (remLockSet tp' a).
Proof.
  inversion 1; intros; constructor; auto; intros.
  destruct (eq_dec a0 a).
  - subst; rewrite !gsslockResRemLock; auto.
  - rewrite !gsolockResRemLock; auto.
Qed.

Lemma MTCH_addThread:
  forall tp tp' vf arg r (MATCH : match_st tp tp'),
  match_st (addThread tp vf arg r) (addThread tp' vf arg r).
Proof.
  inversion 1; intros; constructor; auto; intros.
  - apply cntAdd' in H as [[]|].
    + apply cntAdd; auto.
    + subst; rewrite mtch_latest.
      apply cntAddLatest.
  - apply cntAdd' in H as [[]|].
    + apply cntAdd; auto.
    + subst; rewrite <- mtch_latest.
      apply cntAddLatest.
  - destruct (cntAdd' _ _ _ Htid) as [[]|], (cntAdd' _ _ _ Htid') as [[]|]; try congruence.
    + unshelve erewrite !gsoAddCode; eauto.
    + subst; rewrite !gssAddCode; auto.
      constructor.
  - destruct (cntAdd' _ _ _ Htid) as [[]|], (cntAdd' _ _ _ Htid') as [[]|]; try congruence.
    + unshelve erewrite !gsoAddRes; eauto.
    + subst; rewrite !gssAddRes; auto.
  - destruct (cntAdd' _ _ _ Htid) as [[]|], (cntAdd' _ _ _ Htid') as [[]|]; try congruence.
    + unshelve erewrite !gsoAddRes; eauto.
    + subst; rewrite !gssAddRes; auto.
  - simpl in *.
    unfold OrdinalPool.latestThread, OrdinalPool.addThread in *; simpl.
    congruence.
Qed.

Existing Instance scheduler.
Existing Instance DilMem.

Lemma updThread_twice : forall {res sem} (tp : @OrdinalPool.t res sem) i
  (cnti : containsThread(ThreadPool := OrdinalPool.OrdinalThreadPool) tp i) c c' r r'
  (cnti' : containsThread (updThread cnti c r) i),
  updThread cnti' c' r' = updThread cnti c' r'.
Proof.
  intros; apply OrdinalPool.updThread_twice.
Qed.

Lemma mem_ext: forall m1 m2,
  Mem.mem_contents m1 = Mem.mem_contents m2 ->
  Mem.mem_access m1 = Mem.mem_access m2 ->
  Mem.nextblock m1 = Mem.nextblock m2 ->
  m1 = m2.
Proof.
  destruct m1, m2; simpl; intros; subst.
  f_equal; apply Axioms.proof_irr.
Qed.

Lemma restrPermMap_twice: forall p1 p2 m Hlt1 Hlt2 Hlt',
  @restrPermMap p2 (@restrPermMap p1 m Hlt1) Hlt2 = @restrPermMap p2 m Hlt'.
Proof.
  intros; apply mem_ext; try reflexivity.
  simpl.
  f_equal.
  + repeat (apply Axioms.functional_extensionality; intro).
    destruct x0; auto.
  + remember (snd (Mem.mem_access m)) as t.
    unfold PTree.map.
    remember 1%positive as n.
    clear.
    revert n; induction t; auto; intro; simpl; f_equal; eauto.
    destruct o; reflexivity.
Qed.

Lemma restrPermMap_compat: forall {Sem} (tp : t(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=Sem)))
  m p Hlt, mem_compatible tp (@restrPermMap p m Hlt) -> mem_compatible tp m.
Proof.
  destruct 1; constructor.
  + split; repeat intro; eapply juicy_mem.perm_order''_trans; try apply compat_th0;
      rewrite getMax_restr; apply po_refl.
  + split; repeat intro; eapply juicy_mem.perm_order''_trans; try eapply compat_lp0; eauto;
      rewrite getMax_restr; apply po_refl.
  + intros; rewrite <- restrPermMap_valid; eauto.
Qed.

Lemma restrPerm_sub_map: forall m p Hlt,
  sub_map (snd (getMaxPerm (@restrPermMap p m Hlt))) (snd (getMaxPerm m)).
Proof.
  intros; simpl; apply sub_map_and_shape.
  { unfold PTree.map.
    remember (snd (Mem.mem_access m)) as t; remember 1%positive as i; clear.
    revert i; unfold same_shape; induction t; simpl; auto; intros.
    repeat split; auto.
    destruct o; simpl; auto. }
  intros ??.
  rewrite !PTree.gmap1, PTree.gmap.
  intro H; destruct ((snd (Mem.mem_access m)) ! _); inv H.
  simpl; do 2 eexists; eauto.
  intro; auto.
Qed.

Lemma csafe_restr: forall {Sem} n st m p' Hlt
  (Hext: forall c m m' e, at_external (msem semSem) c m = Some e -> at_external (msem semSem) c m' = Some e),
  @csafe _ Sem OrdinalPool.OrdinalThreadPool DryHybridMachineSig st (@restrPermMap p' m Hlt) n ->
  @csafe _ Sem OrdinalPool.OrdinalThreadPool DryHybridMachineSig st m n.
Proof.
  induction n; intros; [constructor|].
  destruct st as ((U, tr), tp).
  inv H; [constructor; auto | inv Hstep; simpl in *; try inv Htstep; try (apply schedSkip_id in HschedS; subst);
      try discriminate | inv Hstep; simpl in *; try inv Htstep; try match goal with H : U = schedSkip U |- _ =>
      symmetry in H; apply schedSkip_id in H; subst end; try discriminate];
      pose proof (restrPermMap_compat _ _ _ _ Hcmpt) as Hcmpt'.
  - hnf in Hperm; subst.
    erewrite restrPermMap_twice in *.
    eapply CoreSafe; eauto.
    hnf; simpl.
    change U with (yield U) at 2.
    change m'0 with (diluteMem m'0) at 2.
    rewrite <- H4.
    eapply start_step; eauto.
    econstructor; eauto.
    instantiate (2 := Hcmpt').
    hnf; eauto.
  - hnf in Hperm; subst.
    erewrite restrPermMap_twice in *.
    eapply CoreSafe, IHn; eauto.
    hnf; simpl.
    change U with (yield U) at 2.
    change m with (diluteMem m) at 2.
    rewrite <- H4.
    eapply resume_step; eauto.
    econstructor; eauto.
    instantiate (2 := Hcmpt').
    hnf; eauto.
  - erewrite restrPermMap_twice in *.
    eapply CoreSafe; eauto.
    hnf; simpl.
    change U with (yield U) at 2.
    change m'0 with (diluteMem m'0) at 2.
    rewrite <- H5.
    eapply thread_step; eauto.
    instantiate (1 := Hcmpt').
    econstructor; eauto.
  - hnf in Hperm; subst.
    erewrite restrPermMap_twice in *.
    eapply AngelSafe; [|intro; eapply IHn; eauto].
    hnf; simpl.
    rewrite <- H4.
    eapply suspend_step; eauto.
    econstructor; eauto.
    instantiate (2 := Hcmpt').
    hnf; eauto.
  - assert (permMapLt (setPermBlock (Some Writable) b (Ptrofs.intval ofs)
      (snd (getThreadR(ThreadPool := OrdinalPool.OrdinalThreadPool) Htid)) LKSIZE_nat)
      (getMaxPerm m)) as H.
    { repeat intro; eapply juicy_mem.perm_order''_trans, Hlt'; rewrite getMax_restr; apply po_refl. }
    erewrite restrPermMap_twice in *.
    instantiate (1 := H) in Hstore.
    eapply AngelSafe; eauto.
    hnf; simpl.
    rewrite <- H5.
    eapply sync_step; auto.
    instantiate (1 := Hcmpt').
    pose proof (restrPerm_sub_map _ _ Hlt).
    eapply step_acquire; eauto.
    destruct Hbounded; split; eapply sub_map_trans; eauto.
    simpl.
    + destruct Hlt_new as [Hlt_new1 Hlt_new2].
      split.
      * subst newThreadPerm; simpl in Hlt_new1.
        intros b0 ofs0.
        specialize (Hlt_new1 b0 ofs0).
        rewrite getMax_restr in Hlt_new1; auto.
        
      * subst newThreadPerm; simpl in Hlt_new2.
        intros b0 ofs0.
        specialize (Hlt_new2 b0 ofs0).
        rewrite getMax_restr in Hlt_new2; auto.
  - assert (permMapLt (setPermBlock (Some Writable) b (Ptrofs.intval ofs)
      (snd (getThreadR(ThreadPool := OrdinalPool.OrdinalThreadPool) Htid)) LKSIZE_nat)
      (getMaxPerm m)) as H.
    { repeat intro; eapply juicy_mem.perm_order''_trans, Hlt'; rewrite getMax_restr; apply po_refl. }
    erewrite restrPermMap_twice in *.
    instantiate (1 := H) in Hstore.
    eapply AngelSafe; eauto.
    hnf; simpl.
    rewrite <- H5.
    eapply sync_step; auto.
    instantiate (1 := Hcmpt').
    pose proof (restrPerm_sub_map _ _ Hlt).
    destruct Hbounded, HboundedLP as (? & ? & ? & ?).
    eapply step_release; eauto; repeat split; auto; eapply sub_map_trans; eauto.
  - eapply AngelSafe; [|intro; eapply IHn; eauto].
    hnf; simpl.
    rewrite <- H5.
    eapply sync_step; auto.
    instantiate (1 := Hcmpt').
    pose proof (restrPerm_sub_map _ _ Hlt).
    destruct Hbounded, Hbounded_new.
    rewrite !build_delta_content_restr.
    eapply step_create; eauto; simpl; auto; split; eapply sub_map_trans; eauto.
  - erewrite restrPermMap_twice in *.
    eapply AngelSafe; eauto.
    hnf; simpl.
    rewrite <- H5.
    eapply sync_step; auto.
    instantiate (1 := Hcmpt').
    eapply step_mklock; eauto.
  - erewrite restrPermMap_twice in *.
    eapply AngelSafe; [|intro; eapply IHn; eauto].
    hnf; simpl.
    rewrite <- H5.
    eapply sync_step; auto.
    instantiate (1 := Hcmpt').
    eapply step_freelock; eauto; simpl; auto.
  - erewrite restrPermMap_twice in *.
    eapply AngelSafe; [|intro; eapply IHn; eauto].
    hnf; simpl.
    rewrite <- H5.
    eapply sync_step; auto.
    instantiate (1 := Hcmpt').
    eapply step_acqfail; eauto.
(*  - eapply AngelSafe; [|intro; eapply IHn; eauto].
    hnf; simpl.
    subst; rewrite <- H4.
    eapply halted_step; eauto.*)
  - eapply AngelSafe; [|intro; eapply IHn; eauto].
    hnf; simpl.
    subst; rewrite <- H4.
    eapply schedfail; eauto.
Qed.

Lemma restr_Cur: forall p m Hlt, p = getCurPerm m -> @restrPermMap p m Hlt = m.
Proof.
  intros; subst; apply mem_ext; auto; simpl.
  pose proof Clight_bounds.Mem_canonical_useful m.
  destruct (Mem.mem_access m) eqn: Hm; simpl in *; f_equal.
  - extensionality ofs; extensionality k; rewrite H.
    destruct k; auto.
  - apply sync_preds.PTree_map_self; intros.
    extensionality ofs; extensionality k.
    destruct k; auto.
    rewrite getCurPerm_correct; unfold permission_at.
    rewrite Hm; simpl.
    unfold PMap.get; simpl.
    rewrite H0; auto.
Qed.

Corollary csafe_restr': forall n st m p' Hlt,
  csafe(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig) st m n ->
  csafe(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig) st (@restrPermMap p' m Hlt) n.
Proof.
  intros.
  unshelve eapply csafe_restr; [.. | unshelve erewrite restrPermMap_twice, restr_Cur; auto].
  - intros ??; rewrite getMax_restr.
    apply getCur_Max.
  - simpl.
    destruct c; auto.
  - intros ??; apply getCur_Max.
Qed.

Lemma invariant_updThreadC: forall (tp : t(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge)))
  tid c (cnti : containsThread tp tid),
  invariant tp -> invariant (updThreadC cnti c).
Proof.
  destruct 1; constructor; auto.
Qed.

Instance ClightAxioms : @CoreLanguage.SemAxioms (ClightSem ge).
Proof.
  constructor.
  - intros.
    apply memsem_lemmas.mem_step_obeys_cur_write; auto.
    eapply corestep_mem; eauto.
  - intros.
    apply ev_step_ax2 in H as [].
    eapply CLC_step_decay; simpl in *; eauto.
  - intros.
    apply mem_forward_nextblock, memsem_lemmas.mem_step_forward.
    eapply corestep_mem; eauto.
  - intros; simpl.
    destruct q; auto.
    right; repeat intro.
    inv H.
  - intros.
    inv Hstep.
    inv H; simpl. reflexivity.
    (* eapply mem_step_alloc; eauto. *) 
  - intros.
    inv H.
    inv H0; simpl.
    split; intros; eauto.
    + (*contradiction. *)
      exfalso; eauto.
  - intros.
    inv H.
    inv H0; simpl. reflexivity.
Qed.

Lemma CoreSafe_star: forall n U tr tp m tid (c : @semC (ClightSem ge)) c' tp' m' ev
  (HschedN: schedPeek U = Some tid)
  (Htid: containsThread tp tid)
  (Hm: fst (getThreadR(resources:=dryResources) Htid) = getCurPerm m)
  (Hcmpt: mem_compatible tp m)
  (Hinv: invariant tp)
  (Hcode: getThreadC Htid = Krun c)
  (Hcoresteps: ev_star ge c m ev c' m')
  (Htp': tp' = updThread Htid (Krun c') (getCurPerm m', snd (getThreadR Htid)))
  (Hsafe: csafe(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    (yield U, seq.cat tr (map (fun mev => Events.internal tid mev) ev), tp') (diluteMem m') n),
  csafe(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    (U, tr, tp) m n.
Proof.
  intros.
  revert dependent tp'.
  revert dependent tp.
  revert n tr.
  induction Hcoresteps; intros.
  - subst.
    rewrite app_nil_r in Hsafe.
    rewrite <- Hm in Hsafe.
    destruct (getThreadR Htid) eqn: Hget; simpl in *.
    rewrite <- Hcode, <- Hget, OrdinalPool.updThread_same in Hsafe; auto.
  - rewrite map_app, app_assoc in Hsafe.
    eapply IHHcoresteps in Hsafe.
    + eapply csafe_reduce; [eapply CoreSafe; eauto | auto].
      hnf; simpl.
      change U with (yield U) at 2.
      change m2 with (diluteMem m2) at 2.
      eapply thread_step with (Hcmpt0 := Hcmpt); auto; simpl.
      econstructor; try apply H; eauto.
      apply restr_Cur; auto.
    + rewrite gssThreadRes; auto.
    + erewrite <- (restr_Cur _ m1) in H by eauto.
      eapply CoreLanguageDry.corestep_compatible, H; auto.
    + apply ev_step_ax1 in H.
      erewrite <- (restr_Cur _ m1) in H by eauto.
      eapply CoreLanguageDry.corestep_invariant.
      3: apply H.
      all: auto.
    + apply gssThreadCode.
    + rewrite updThread_twice, gssThreadRes; auto.
  Unshelve.
  apply cntUpdate; auto.
  all: auto.
Qed.

Lemma CoreSafe_plus : forall n U tr tp m tid (c : @semC (ClightSem ge)) c' tp' m' ev m1
  (HschedN: schedPeek U = Some tid)
  (Htid: containsThread tp tid)
  (Hcmpt: mem_compatible tp m)
  (Hrestrict_pmap: restrPermMap (proj1 (compat_th _ _ Hcmpt Htid)) = m1)
  (Hinv: invariant tp)
  (Hcode: getThreadC Htid = Krun c)
  (Hcoresteps: ev_plus ge c m1 ev c' m')
  (Htp': tp' = updThread Htid (Krun c') (getCurPerm m', snd (getThreadR Htid)))
  (Hsafe: csafe(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    (yield U, seq.cat tr (map (fun mev => Events.internal tid mev) ev), tp') (diluteMem m') n),
  csafe(ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    (U, tr, tp) m (S n).
Proof.
  intros.
  inv Hcoresteps.
  rewrite map_app, app_assoc in Hsafe.
  eapply CoreSafe_star in Hsafe; try apply H0.
  - eapply CoreSafe; eauto.
    hnf; simpl.
    change U with (yield U) at 2.
    change m2 with (diluteMem m2) at 2.
    eapply thread_step; auto.
    econstructor; eauto.
    simpl; eauto.
  - auto.
  - rewrite gssThreadRes; auto.
  - eapply CoreLanguageDry.corestep_compatible, H; auto.
  - apply ev_step_ax1 in H.
    eapply CoreLanguageDry.corestep_invariant.
    3: apply H.
    all: auto.
    apply restrPermMap_irr; auto.
  - apply gssThreadCode.
  - rewrite updThread_twice, gssThreadRes; auto.
  Unshelve.
  apply cntUpdate; auto.
  auto.
Qed.

Opaque updThread updThreadC containsThread getThreadC getThreadR lockRes.

Lemma computeMap_ext: forall pmap pmap' dmap, (forall b ofs, pmap !! b ofs = pmap' !! b ofs) ->
  forall b ofs, (computeMap pmap dmap) !! b ofs = (computeMap pmap' dmap) !! b ofs.
Proof.
  intros.
  destruct (dmap ! b) eqn: Hb; [|rewrite !computeMap_3; auto].
  destruct (o ofs) eqn: Hofs; [erewrite !computeMap_1 by eauto | erewrite !computeMap_2 by eauto]; auto.
Qed.

Lemma type_of_fundef_fun: forall f, exists targs tres cc,
  Clight.type_of_fundef f = Tfunction targs tres cc.
Proof.
  destruct f; simpl; eauto.
  unfold Clight.type_of_function; eauto.
Qed.

Definition MachStateDry := @MachState dryResources (Clight_newSem ge)
       (@OrdinalPool.OrdinalThreadPool dryResources (Clight_newSem ge)).
(*
SearchHead (MachState -> _).
Print Val.inject.
Definition flat_inject (v: memval)
*)


Definition threadpool_of (st: MachStateDry) :=    match st with (_, _, tp) => tp end.

Definition dryThreadPool := @ThreadPool.t dryResources (Clight_newSem ge)
                                  (@OrdinalPool.OrdinalThreadPool dryResources (Clight_newSem ge)).

Definition ctl_ok nextb (c: @ctl veric.Clight_core.state) : Prop :=
 match c with
 | Krun q => corestate_ok nextb q 
 | Kblocked q => corestate_ok nextb q
 | Kresume q v => corestate_ok nextb q /\ val_ok nextb v
 | Kinit v1 v2 => val_ok nextb v1 /\ val_ok nextb v2
 end.

Lemma alloc_ctl_ok: 
 forall (nextb nextb': positive)
   (LESS:  (nextb <= nextb')%positive)
   c, 
   ctl_ok nextb c -> ctl_ok nextb' c.
Proof.
destruct c; simpl; intros;
try solve [eapply alloc_corestate_ok; eauto].
destruct H; split.
eapply alloc_corestate_ok; eauto.
eapply alloc_val_ok; eauto.
destruct H; split;
eapply alloc_val_ok; eauto.
Qed.

Definition mem_ok (tp: dryThreadPool) m := 
   Smallstep.globals_not_fresh (Clight.genv_genv ge) m /\
   mem_wd2 m /\
  (forall i (CT: containsThread tp i),
      ctl_ok (Mem.nextblock m) (getThreadC CT)).




Lemma mem_ok_wd: forall tp m, mem_ok tp m -> Mem.mem_wd m.
Proof.
  intros ? ? [? [? _]].
  constructor; unfold Mem.flat_inj; intros.
  - destruct (plt _ _); inv H1; auto.
    rewrite Z.add_0_r; auto.
  - destruct (plt _ _); inv H1; auto.
    apply Z.divide_0_r.
  - destruct (plt _ _); inv H1; auto.
    rewrite Z.add_0_r; auto.
Qed.

Lemma mem_ok_restr: forall tp m p Hlt, mem_ok tp m -> mem_ok tp (@restrPermMap p m Hlt).
Proof.
  intros.
  destruct H as [? Hwd]; split.
  - unfold Smallstep.globals_not_fresh.
    rewrite restrPermMap_nextblock; auto.
  - unfold mem_wd2 in *; rewrite restrPermMap_nextblock, restrPermMap_mem_contents; auto.
Qed.

Lemma ctl_ok_updThread:
  forall nextb (ms: dryThreadPool) tid c r
  (H: containsThread ms tid),
  ctl_ok nextb c ->
  (forall i (CT: containsThread ms i), ctl_ok nextb (getThreadC CT)) ->
  (forall i (CT: containsThread (updThread H c r) i), 
       ctl_ok nextb (getThreadC CT)).
Proof.
intros.
specialize (H1 i).
destruct (eq_dec tid i).
subst i.
specialize (H1 H).
pose proof (@gssThreadCode _ _ _ _ ms H _ _ CT). rewrite H2; auto.
destruct (containsThread_dec_ i ms).
specialize (H1 c0).
pose proof (@gsoThreadCode _ _ _ _ _ _ n _ c0 _ _ CT).
rewrite H2; auto.
hnf.
contradiction n0.
Qed.

Lemma ctl_ok_updLockSet:
  forall nextb (ms: dryThreadPool) tid x r
  (H: containsThread ms tid),
  (forall i (CT: containsThread ms i), ctl_ok nextb (getThreadC CT)) ->
  (forall i (CT: containsThread (updLockSet ms x r) i), 
       ctl_ok nextb (getThreadC CT)).
Proof.
intros.
pose proof (cntUpdateL' _ _ CT). specialize (H0 i H1).
replace (getThreadC CT) with (getThreadC H1); auto.
symmetry; apply gLockSetCode.
Qed.


Lemma ctl_ok_remLockSet:
  forall nextb (ms: dryThreadPool) tid x
  (H: containsThread ms tid),
  (forall i (CT: containsThread ms i), ctl_ok nextb (getThreadC CT)) ->
  (forall i (CT: containsThread (remLockSet ms x) i), 
       ctl_ok nextb (getThreadC CT)).
Proof.
intros.
pose proof (cntRemoveL' _ CT). specialize (H0 i H1).
replace (getThreadC CT) with (getThreadC H1); auto.
symmetry; apply gRemLockSetCode.
Qed.

Lemma ctl_ok_updThreadC:
  forall nextb (ms: dryThreadPool) tid c
  (H: containsThread ms tid),
  ctl_ok nextb c ->
  (forall i (CT: containsThread ms i), ctl_ok nextb (getThreadC CT)) ->
  (forall i (CT: containsThread (updThreadC H c) i), 
       ctl_ok nextb (getThreadC CT)).
Proof.
intros.
specialize (H1 i).
destruct (eq_dec tid i).
subst i.
specialize (H1 H).
pose proof (@gssThreadCC _ _ _ _ ms H _ CT). rewrite H2; auto.
destruct (containsThread_dec_ i ms).
specialize (H1 c0).
pose proof (@gsoThreadCC _ _ _ _ _ _ n _ c0 _ CT).
rewrite <- H2; auto.
hnf.
contradiction n0.
Qed.

Lemma ctl_ok_addThread:
  forall nextb (ms: dryThreadPool) tid v1 v2 r
  (H: containsThread ms tid),
  val_ok nextb v1 ->
  val_ok nextb v2 ->
  (forall i (CT: containsThread ms i), ctl_ok nextb (getThreadC CT)) ->
  (forall i (CT: containsThread (addThread ms v1 v2 r) i), 
       ctl_ok nextb (getThreadC CT)).
Proof.
intros.
specialize (H2 i).
pose proof (cntAdd' _ _ _ CT).
destruct H3.
destruct H3.
specialize (H2 H3).
replace (getThreadC CT) with (getThreadC H3); auto.
symmetry; apply gsoAddCode. subst i.
pose proof (@gssAddCode _ _ _ ms v1 v2 r (latestThread ms) (eq_refl _) CT).
rewrite H3. split; auto.
Qed.

Lemma mem_ok_threadStep: 
    forall
       (ms : dryThreadPool) (m : mem) (tid : nat) 
       (m' : mem) (ev : list mem_event)
      (Hmem : mem_ok ms m)
      (Htid : containsThread ms tid)
      (Hcmpt : mem_compatible ms m)
      (c c': veric.Clight_core.state)
      (Hcode : getThreadC Htid = Krun c)
      (Hcorestep : cl_evstep ge c (restrPermMap (proj1 (Hcmpt tid Htid))) ev c' m'),
     mem_ok (updThread Htid (Krun c') (getCurPerm m', snd (getThreadR Htid))) m'.
Proof.
 intros.
 assert (Smallstep.globals_not_fresh (Clight.genv_genv ge) m /\
             mem_wd2 m' /\ 
             corestate_ok (Mem.nextblock m') c' /\
             (Mem.nextblock m <= Mem.nextblock m')%positive /\
             (forall (i : nat) (CT : containsThread ms i),
                ctl_ok (Mem.nextblock m) (getThreadC CT))).
 2:{
    destruct H as [? [? [? [? ?]]]].
    split;[ | split]; auto.
    clear - H2 H. red in H|-*. eapply Pos.le_trans; eauto.
    assert (forall (i : nat) (CT : containsThread ms i),
     ctl_ok (Mem.nextblock m') (getThreadC CT)).
    intros. eapply alloc_ctl_ok; eauto.
    revert H4.
    eapply ctl_ok_updThread. auto.
 }
 destruct Hmem as [? [? ?]].
  assert (mem_wd2 m' /\ 
     corestate_ok (Mem.nextblock m') c' /\ 
     (Mem.nextblock m <= Mem.nextblock m')%positive); [ |intuition].
  specialize (H1 _ Htid).
  rewrite Hcode in H1. clear Hcode. simpl in H1.  
  remember (proj1 (Hcmpt tid Htid)) as P. clear HeqP.
  remember (fst (getThreadR Htid)) as u. clear Hequ.
  clear - Hcorestep H H0 H1.
  remember (restrPermMap P) as m0.
  assert (Smallstep.globals_not_fresh (Clight.genv_genv ge) m0 /\
             mem_wd2 m0 /\
               corestate_ok (Mem.nextblock m0) c).
  subst m0. clear -H H0 H1. split;[|split]; auto.
  replace (Mem.nextblock m) with (Mem.nextblock m0)
         by (subst m0; reflexivity).
  clear - H2 Hcorestep. rename m0 into m.
  revert H2.
  apply CLN_evstep_ax1 in Hcorestep.
  simpl in Hcorestep.
  eapply cl_step_ok; eauto.
Qed.

Lemma mem_ok_step: forall st m st' m' (Hmem: mem_ok (threadpool_of st) m),
  MachStep(Sem := Clight_newSem ge)
      (ThreadPool:= OrdinalPool.OrdinalThreadPool)
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig) 
      st m st' m' -> 
    mem_ok (threadpool_of st') m'.
Proof.
intros.
hnf in H. destruct st as [[sch tr] tp]. destruct st' as [[sch' tr'] tp'].
  simpl in H.
  induction H; auto; simpl threadpool_of in *.
  - (* start_thread *)
     inv Htstep.
    hnf in Hperm; subst.
    destruct Hinitial as (? & ? & H0ab); subst.
    destruct Hmem as [H1 [H2 H2']]; split; [|split].
    + unfold Smallstep.globals_not_fresh.
      etransitivity; eauto. simpl. apply Pos.le_refl. 
    + intros.
      hnf; intros.
       eapply memval_inject_incr, flat_inj_incr, Pos.le_refl; auto.
    + intros. simpl. simpl in CT.
        clear - Hcode H H2'.
        revert i CT.
        assert (H2x: forall (i : nat) (CT : containsThread ms i),
             ctl_ok (Mem.nextblock m) (getThreadC CT)). {
             intros. eapply alloc_ctl_ok. 2: eapply H2'; eauto.
             apply Pos.le_refl.
         } clear H2'.
        generalize H2x; apply ctl_ok_updThread.
        specialize (H2x tid ctn). rewrite Hcode in H2x. 
        set  (nextb := Mem.nextblock m) in *; clearbody nextb.
        clear - H H2x.
        destruct H2x; hnf; auto.
        unfold Clight_core.cl_initial_core in H.
        destruct vf; try contradiction.
        destruct (Ptrofs.eq_dec i Ptrofs.zero);  try contradiction.
        destruct (Genv.find_funct_ptr (Clight.genv_genv ge) b); try contradiction.
        destruct (Clight.type_of_fundef f); try contradiction.
        destruct H as [? [? [? ?]]]; subst.
        split. constructor; auto. hnf; auto.
  - (* resume_thread *)
    destruct Hmem as [Hmem1 [Hmem2 Hmem3]].
    split; [|split]; auto.
    inv Htstep.
    inv Hafter_external.
    clear - Hcode H0 Hmem3.
    generalize Hmem3; apply ctl_ok_updThreadC.
    specialize (Hmem3 _ ctn). rewrite Hcode in Hmem3.
    destruct Hmem3.   
    simpl.
    destruct c; inv H0. destruct f; inv H3.
    simpl in H|-*. destruct H; split; auto.
  - (* threadStep *)
   inv Htstep. simpl in *. hnf in c,c'.
    eapply mem_ok_threadStep; eauto.
  - (* suspend_thread *)
    destruct Hmem as [Hmem1 [Hmem2 Hmem3]].
    split; [|split]; auto.
    inv Htstep.
    clear - Hcode Hmem3.
    generalize Hmem3; apply ctl_ok_updThreadC.
    specialize (Hmem3 _ ctn). rewrite Hcode in Hmem3.
    apply Hmem3.
  - (* isCoarse *)
     inv Htstep; auto.
    + destruct Hmem as [? [Hwd H2']]; split; [|split].
      * unfold Smallstep.globals_not_fresh.
        erewrite Mem.nextblock_store, restrPermMap_nextblock; eauto.
      * intros; hnf; intros.
        erewrite Mem.nextblock_store, restrPermMap_nextblock, Mem.store_mem_contents by eauto.
        destruct (eq_dec b0 b); [subst; rewrite PMap.gss | rewrite PMap.gso; auto].
        replace ofs0 with (ofs0 + 0) at 2 by apply Z.add_0_r.
        replace (Ptrofs.intval ofs) with (Ptrofs.intval ofs + 0) at 3 by apply Z.add_0_r.
        apply Mem.setN_inj with (access := fun _ => True); intros; rewrite ?Z.add_0_r; auto.
        apply encode_val_inject; constructor.
      * apply Mem.nextblock_store in Hstore. simpl in Hstore. rewrite Hstore in *.
         eapply ctl_ok_updLockSet with (tid:=tid).
         apply cntUpdate; auto.
         generalize H2'; apply ctl_ok_updThread.
         specialize (H2' _ Htid). rewrite Hcode in H2'. clear - H2'.
         split; auto. hnf. auto.
    + destruct Hmem as [? [Hwd H2']]; split; [|split].
      * unfold Smallstep.globals_not_fresh.
        erewrite Mem.nextblock_store, restrPermMap_nextblock; eauto.
      * intros; hnf; intros.
        erewrite Mem.nextblock_store, restrPermMap_nextblock, Mem.store_mem_contents by eauto.
        destruct (eq_dec b0 b); [subst; rewrite PMap.gss | rewrite PMap.gso; auto].
        replace ofs0 with (ofs0 + 0) at 2 by apply Z.add_0_r.
        replace (Ptrofs.intval ofs) with (Ptrofs.intval ofs + 0) at 3 by apply Z.add_0_r.
        apply Mem.setN_inj with (access := fun _ => True); intros; rewrite ?Z.add_0_r; auto.
        apply encode_val_inject; constructor.
      * apply Mem.nextblock_store in Hstore. simpl in Hstore. rewrite Hstore in *.
         eapply ctl_ok_updLockSet with (tid:=tid).
         apply cntUpdate; auto.
         generalize H2'; apply ctl_ok_updThread.
         specialize (H2' _ Htid). rewrite Hcode in H2'. clear - H2'.
         split; auto. hnf. auto.
    + (* CREATE *)
       destruct Hmem as [? [Hwd H2']]; split; [|split]; auto.
       assert (block_ok (Mem.nextblock m') b /\ val_ok (Mem.nextblock m') arg). {
             specialize (H2' _ Htid). rewrite Hcode in H2'.
        simpl in H2'. clear - H2' Hat_external. inv Hat_external.
         destruct c; inv H0. destruct f; inv H1.
         destruct (AST.ef_inline e) eqn:Hinline; inv H0.
         simpl in H2'. destruct H2' as [? _].
          inv H. inv H3. split; auto.
       }
      apply ctl_ok_addThread with (tid:=tid).
      apply cntUpdate. auto.
      destruct H0;  auto.
      destruct H0;  auto.
         generalize H2'; apply ctl_ok_updThread.
         specialize (H2' _ Htid). rewrite Hcode in H2'. clear - H2'.
      split; auto. simpl. auto.
    + (* MKLOCK *)
       destruct Hmem as [? [Hwd H2']]; split; [|split].
      * unfold Smallstep.globals_not_fresh.
        erewrite Mem.nextblock_store, restrPermMap_nextblock; eauto.
      * intros; hnf; intros.
        erewrite Mem.nextblock_store, restrPermMap_nextblock, Mem.store_mem_contents by eauto.
        destruct (eq_dec b0 b); [subst; rewrite PMap.gss | rewrite PMap.gso; auto].
        replace ofs0 with (ofs0 + 0) at 2 by apply Z.add_0_r.
        replace (Ptrofs.intval ofs) with (Ptrofs.intval ofs + 0) at 2 by apply Z.add_0_r.
        apply Mem.setN_inj with (access := fun _ => True); intros; rewrite ?Z.add_0_r; auto.
        apply encode_val_inject; constructor.
      * apply Mem.nextblock_store in Hstore. simpl in Hstore. rewrite Hstore in *.
         eapply ctl_ok_updLockSet with (tid:=tid).
         apply cntUpdate; auto.
         generalize H2'; apply ctl_ok_updThread.
         specialize (H2' _ Htid). rewrite Hcode in H2'. clear - H2'.
         split; auto. hnf. auto.
    + (* FREE_LOCK *)
       destruct Hmem as [? [Hwd H2']]; split; [|split]; auto.
         eapply ctl_ok_remLockSet with (tid:=tid).
         apply cntUpdate; auto.
         generalize H2'; apply ctl_ok_updThread.
         specialize (H2' _ Htid). rewrite Hcode in H2'. clear - H2'.
         split; auto. hnf. auto.
Qed.

(* spawn handler *)
Notation tvoidptr := (Tpointer Tvoid noattr).
Notation tvoidfun := (Tfunction (Tcons tvoidptr Tnil) tvoidptr AST.cc_default).

Definition f_wrapper : Clight.function :=
  {| Clight.fn_return := Tvoid; Clight.fn_callconv := AST.cc_default;
     Clight.fn_params := [(1%positive, tvoidfun); (2%positive, tvoidptr)];
     Clight.fn_vars := []; Clight.fn_temps := [];
     Clight.fn_body := Clight.Scall None (Clight.Etempvar 1%positive tvoidfun) [Clight.Etempvar 2%positive tvoidptr] |}.

(*Todo Explain the following definition *)
Class spawn_wrapper := { lookup_wrapper: exists b_wrapper, Genv.find_funct_ptr (Clight.genv_genv ge) b_wrapper = Some (Ctypes.Internal f_wrapper)}.
Context {SW : spawn_wrapper}.

(*
Lemma match_cont_prefix: forall k k1 k2, match_cont (Clight_new.strip_skip k1) (strip_skip' k2) ->
  match_cont (Clight_new.strip_skip (Clight_new.Kseq k :: k1))
             (strip_skip' (CC.Kseq k k2)).
Proof.
  induction k; auto; intros; constructor; auto.
Qed.

Lemma match_body: forall body f te,
  match_cont
    (Clight_new.strip_skip
     [Clight_new.Kseq body; Clight_new.Kseq (Clight.Sreturn None);
      Clight_new.Kcall None f Clight.empty_env te;
     Clight_new.Kseq (Clight.Sloop Clight.Sskip Clight.Sskip)])
    (strip_skip'
     (CC.Kseq body
        (Clight.Kcall None f_wrapper Clight.empty_env te (Clight.Kseq (Clight.Sloop Clight.Sskip Clight.Sskip) Clight.Kstop)))).
Proof.
  intros; apply match_cont_prefix; simpl.
  constructor; simpl; auto.
  constructor.
  constructor.
Qed.

Lemma match_ext: forall ef v2 t0 tyres te,
  match_states
  (Clight_new.ExtCall ef [v2] None Clight.empty_env te 
         [Clight_new.Kseq (Clight.Sloop Clight.Sskip Clight.Sskip) ])
  (CC'.CC_core_Callstate (Ctypes.External ef (Ctypes.Tcons t0 Ctypes.Tnil) tyres AST.cc_default) [v2]
     (Clight.Kcall None f_wrapper Clight.empty_env te 
          (Clight.Kseq (Clight.Sloop Clight.Sskip Clight.Sskip) Clight.Kstop))).
Proof.
  intros; constructor; simpl; auto.
  constructor. constructor.
Qed.
*)

Lemma mem_compatible_updThreadC: forall {Sem ThreadPool} (tp : @t _ Sem ThreadPool)
  m i c (cnti : containsThread tp i),
  mem_compatible tp m -> mem_compatible (updThreadC cnti c) m.
Proof.
  inversion 1; constructor; intros.
  - unshelve erewrite gThreadCR; eauto.
    eapply cntUpdateC'; eauto.
  - rewrite gsoThreadCLPool in H0; eauto.
  - rewrite gsoThreadCLPool in H0; eauto.
Qed.

Set Bullet Behavior "Strict Subproofs".

Lemma cat_inj2:
  forall {T} (a b b': list T), seq.cat a b = seq.cat a b' -> b=b'.
Proof.
induction a; simpl; intros; auto. inv H; auto.
Qed.

Lemma ev_step_sim:
 forall (c: Clight.state) m ev (c': Clight_core.state) m',
 ev_step (@semSem (Clight_newSem ge)) (fst (veric.Clight_core.CC_state_to_CC_core c)) m ev c' m' ->
 ev_step (@semSem (ClightSem ge)) c m ev
    (veric.Clight_core.CC_core_to_CC_state c' m') m'.
Proof.
intros. simpl in H.
inv H; destruct c; try discriminate; simpl in *;
match goal with
| H: Clight_core.State _ _ _ _ _ = Clight_core.State _ _ _ _ _ |- _ =>
     symmetry in H; inv H
| H: Clight_core.Callstate _ _ _  = Clight_core.Callstate _ _ _ |- _ =>
     symmetry in H; inv H
| H: Clight_core.Returnstate _ _  = Clight_core.Returnstate _ _ |- _ =>
     symmetry in H; inv H
end;
try solve [econstructor; eauto];
econstructor; eauto.
- (* builtin *)
  unfold AST.ef_inline in *.
  
  admit. (* ask andrew: maybe change inline_external_call_mem_events? *) 
- econstructor; eauto.
- admit. (* external function *)
Admitted.

Lemma Clight_new_Clight_safety_gen:
  forall n sch tr tp m tp' (Hmem: mem_ok tp m),
  csafe
    (Sem := Clight_newSem ge)
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    (sch, tr, tp) m n ->
  match_st tp tp' ->
  csafe
    (Sem := ClightSem ge)
    (ThreadPool:= OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
    (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
    (sch, tr, tp') m n.
Proof.
  induction n; intros; [constructor|].
  inv H; simpl in *; [constructor; auto | ..];
    pose proof (mem_ok_step (sch,tr,tp) _ _ _ Hmem Hstep) as Hmem';
    [inv Hstep; simpl in *; try (apply schedSkip_id in HschedS; subst); try discriminate |
     inv Hstep; simpl in *; try match goal with H : sch = schedSkip sch |- _ =>
       symmetry in H; apply schedSkip_id in H; subst end; try discriminate].
  - inv Htstep.
    inversion H0.
    pose proof (mtch_gtc _ ctn (mtch_cnt _ ctn)) as Hc; rewrite Hcode in Hc; inv Hc.
    destruct Hinitial as (Hinit & Harg & H0ab); subst.
    unfold Clight_core.cl_initial_core in Hinit.
    destruct vf; try contradiction.
    destruct (Ptrofs.eq_dec _ _); try contradiction.
    destruct (Genv.find_funct_ptr _ b) eqn: Hb; try contradiction.
    destruct (Clight.type_of_fundef f) eqn: Hty; try contradiction.
    destruct Hinit as (? & ? & ? & ?); subst.
    eapply CoreSafe with (tp'0 := updThread (mtch_cnt _ ctn)
            (Krun (Clight.Callstate f [arg] (Clight.Kstop t0) m'))
            (HybridMachineSig.add_block Hcmpt ctn m')).
    2:{ eapply IHn; eauto. apply MTCH_updThread; eauto.
         constructor. reflexivity.
    }
    clear IHn. simpl.
    hnf; simpl.      rewrite <- H5.
    change sch with (yield sch) at 2.
    set (m'0 := restrPermMap (proj1 (Hcmpt tid ctn))).
    (*fst (Mem.alloc (restrPermMap (proj1 (Hcmpt tid ctn))) 0 0)). *)
    pattern m' at 1 2 3; replace m' with (diluteMem m'0). 
    eapply start_step; eauto.
    econstructor; eauto.
    eapply MTCH_install_perm, Hperm.
    2: eapply MTCH_invariant; eauto.
    2: f_equal; instantiate (1:=H0);
         unfold HybridMachineSig.add_block; simpl; unfold add_block;
         f_equal; auto.
      { split.
        hnf in Hperm; subst.
        (* destruct lookup_wrapper. *)
        assert (mem_ok tp (restrPermMap (proj1 (compat_th tp m Hcmpt ctn))))
               by (apply mem_ok_restr; auto).
       simpl. 
       assert (exists f', f =  Internal f').
       { admit. (* change 'f' to 'internal f' in [Clight_core.cl_initial_core] *) }
       destruct H6 as [f' ?]; subst f.
       econstructor; eauto.
        - rewrite Hty; f_equal. (* We haven't changed the return type, it's still an int. *) admit.
        - admit. (* add to initial_core *)
        - eapply mem_ok_wd; destruct H1; eauto.
        - admit. (* add to initial_core *)
        - admit. (* add to initial_core *)
        - clear - H2. inv H2; constructor; auto.
      }
      
  - inv Htstep.
    inversion H0.
    pose proof (mtch_gtc _ ctn (mtch_cnt _ ctn)) as Hc; rewrite Hcode in Hc; inv Hc.
    simpl in *.
    destruct c'0; inv Hat_external; inv H1.
    destruct fd; try discriminate.
    destruct (AST.ef_inline e) eqn:Hinline; inv H2.
    eapply CoreSafe.
    { hnf; simpl.
      rewrite <- H5.
      change sch with (yield sch) at 2.
      eapply resume_step; eauto; econstructor; eauto; simpl; eauto.
      - eapply MTCH_install_perm, Hperm.
      - match_case; reflexivity.
      - eapply MTCH_invariant; eauto. }
    eapply IHn; eauto.
    apply MTCH_updThreadC; auto. constructor. simpl.
    inv Hafter_external; auto.
  - inv Htstep.
    inversion H0.
    pose proof (mtch_gtc _ Htid (mtch_cnt _ Htid)) as Hc; rewrite Hcode in Hc; inv Hc.
    apply cat_inj2 in H6. subst tr0.
    eapply CoreSafe.
    2:{ eapply IHn; eauto.
         apply MTCH_updThread; eauto; constructor.
          instantiate (1:= veric.Clight_core.CC_core_to_CC_state c' m'0).
          rewrite veric.Clight_core.CC_core_CC_state_1.
          reflexivity.
    } 
    hnf; simpl.
    instantiate (1 := mtch_cnt _ Htid).
    change sch with (yield sch) at 2.
    replace m'0 with (diluteMem m'0). 
    apply thread_step with (Htid0 := mtch_cnt _ Htid) (Hcmpt0 := (MTCH_compat tp tp' m H0 Hcmpt)); auto.
    econstructor. reflexivity.
    eapply MTCH_invariant; eauto. 
    symmetry; eassumption.
    2: f_equal; f_equal; apply mtch_gtr2.

 replace (restrPermMap
     (fst
        (ssrfun.pair_of_and
           ((MTCH_compat tp tp' m H0 Hcmpt) tid (mtch_cnt tid Htid)))))
  with (restrPermMap (fst (ssrfun.pair_of_and (Hcmpt tid Htid)))).
2:{
 simpl. apply restrPermMap_ext.
 intros. extensionality ofs. apply mtch_gtr1.
 }
 eapply ev_step_sim; eauto.
 admit.  (* diluteMem *)
  - inv Htstep.
    inversion H0.
    pose proof (mtch_gtc _ ctn (mtch_cnt _ ctn)) as Hc; rewrite Hcode in Hc; inv Hc.
    simpl in *.
    inv Hat_external; inv H2.
    destruct c'; inv H3.
    destruct fd; try discriminate.
    destruct (AST.ef_inline e) eqn:Hinline; inv H2.
    eapply AngelSafe.
    { hnf; simpl.
      rewrite app_nil_r.
      eapply suspend_step; eauto; econstructor; eauto; simpl; eauto.
      - eapply MTCH_install_perm, Hperm.
      - match_case; reflexivity.
      - eapply MTCH_invariant; eauto. }
    { rewrite app_nil_r; rewrite <- H5 in Hsafe.
      intro; eapply IHn; auto.
(*      2:{ eapply (csafe_reduce(ThreadPool := OrdinalPool.OrdinalThreadPool)); eauto. } *)
      { auto. }
      apply MTCH_updThreadC; auto.
      constructor; constructor; auto. }

  - inv Htstep; inversion H0; pose proof (mtch_gtc _ Htid (mtch_cnt _ Htid)) as Hc;
      rewrite Hcode in Hc; inv Hc; try destruct c; inv Hat_external; destruct c'; inv H2.
    + do 2 match_case in H3; inv H3.
      eapply AngelSafe.
      
      { eapply sync_step with (Hcmpt0 := MTCH_compat _ _ _ H0 Hcmpt); eauto.
        eapply step_acquire; simpl; eauto; simpl; eauto.
        * eapply MTCH_invariant; eauto.
        * erewrite restrPermMap_irr; eauto.
        * erewrite restrPermMap_irr; eauto.
        * subst newThreadPerm; eauto.
          destruct Hlt_new as [Hlt_new1 Hlt_new2].
          Lemma computeMap_eq:
            forall x x' y y',
            (forall b ofs, x !! b ofs = x' !! b ofs) -> 
            (forall b, PTree.get b y = PTree.get b y') -> 
            forall b ofs,
            (computeMap x y) # b ofs = (computeMap x' y') # b ofs.
          Proof.
          Admitted.

          split;intros  ??.
          -- erewrite computeMap_eq; try eapply Hlt_new1.
             move mtch_gtr1 at bottom.
             symmetry; eapply mtch_gtr1.
             reflexivity.
          -- simpl in *.
             erewrite <- mtch_gtr2; eauto.
        * erewrite restrPermMap_irr; eauto.
          erewrite mtch_gtr2; eauto.
        * rewrite <- mtch_locks; eauto.
        * clear - Hangel1 mtch_gtr1.
          repeat intro.
          erewrite <- mtch_gtr1, <- computeMap_ext by eauto; apply Hangel1.
        * erewrite <- mtch_gtr2; apply Hangel2. }
      { rewrite <- H6 in Hsafe.
        intro; eapply IHn; auto.
        auto.
        apply MTCH_updLockSet, MTCH_updThread; auto.
        - constructor; constructor; auto.
        - apply computeMap_ext; auto.
        - subst newThreadPerm; intros; simpl.
          erewrite mtch_gtr2; eauto. }
    + eapply AngelSafe.
      { eapply sync_step with (Hcmpt0 := MTCH_compat _ _ _ H0 Hcmpt); eauto.
        eapply step_release; simpl; eauto; simpl; eauto.
        * eapply MTCH_invariant; eauto.
        * erewrite restrPermMap_irr; eauto.
        * erewrite restrPermMap_irr; eauto.
        * erewrite restrPermMap_irr; eauto.
          erewrite mtch_gtr2; eauto.
        * rewrite <- mtch_locks; eauto.
        * clear - Hangel1 mtch_gtr1.
          repeat intro.
          specialize (Hangel1 b ofs); simpl in *.
          erewrite <- mtch_gtr1, <- computeMap_ext; eauto.
        * erewrite <- mtch_gtr2; apply Hangel2. }
      { rewrite <- H6 in Hsafe.
        intro; eapply IHn; auto.
        { auto. }
        apply MTCH_updLockSet, MTCH_updThread; auto.
        - constructor; constructor; auto.
        - apply computeMap_ext; auto.
        - subst newThreadPerm; intros; simpl.
          erewrite mtch_gtr2; eauto. }
    + eapply AngelSafe.
      { eapply sync_step with (Hcmpt0 := MTCH_compat _ _ _ H0 Hcmpt); eauto.
        eapply step_create with (virtue3 := virtue1)(virtue4 := virtue2); simpl; eauto; simpl; eauto.
        * eapply MTCH_invariant; eauto.
        * subst newThreadPerm threadPerm'; intros ??; simpl in *.
          specialize (Hangel1 b0 ofs0).
          erewrite <- mtch_gtr1, <- (computeMap_ext _ _ (fst virtue1)) by eauto; apply Hangel1.
        * erewrite <- mtch_gtr2; apply Hangel2. }
      { rewrite <- H6 in Hsafe.
        intro; eapply IHn; auto.
        { auto. }
        apply MTCH_addThread; auto.
        apply MTCH_updThread; auto.
        - constructor; constructor; auto.
        - apply computeMap_ext; auto.
        - subst threadPerm'; intros; simpl.
          erewrite mtch_gtr2; eauto. }
    + eapply AngelSafe.
      { eapply sync_step with (Hcmpt0 := MTCH_compat _ _ _ H0 Hcmpt); eauto.
        eapply step_mklock with (pmap_tid'0 := (_, _)); simpl; eauto; simpl; eauto.
        * eapply MTCH_invariant; eauto.
        * erewrite <- restrPermMap_ext; eauto.
          intro; extensionality ofs0; auto.
        * erewrite <- restrPermMap_ext; eauto.
          intro; extensionality ofs0; auto.
        * rewrite <- mtch_locks; auto. }
      { rewrite <- H6 in Hsafe.
        intro; eapply IHn; auto.
        { auto. }
        apply MTCH_updLockSet, MTCH_updThread; auto.
        * constructor; constructor; auto.
        * intros; simpl.
          setoid_rewrite <- Hdata_perm.
          rewrite !addressFiniteMap.setPermBlock_lookup.
          destruct (adr_range_dec _ _ _); auto.
        * simpl.
          setoid_rewrite <- Hlock_perm.
          erewrite <- mtch_gtr2; eauto. }
    + eapply AngelSafe.
      { eapply sync_step with (Hcmpt0 := MTCH_compat _ _ _ H0 Hcmpt); eauto.
        eapply step_freelock with (pmap_tid'0 := (_, _)); simpl; eauto; simpl; eauto.
        * eapply MTCH_invariant; eauto.
        * rewrite <- mtch_locks; auto.
        * erewrite restrPermMap_irr; eauto. }
      { rewrite <- H6 in Hsafe.
        intro; eapply IHn; auto.
        { auto. }
        apply MTCH_remLockSet, MTCH_updThread; auto.
        * constructor; constructor; auto.
        * intros; simpl.
          setoid_rewrite <- Hdata_perm.
          destruct (adr_range_dec (b, Ptrofs.intval ofs) LKSIZE (b0, ofs0)).
          -- destruct a; subst.
             rewrite !setPermBlock_var_same by (unfold LKSIZE_nat; rewrite Z2Nat.id; lkomega); auto.
          -- destruct (eq_dec b b0); [|rewrite !setPermBlock_var_other_2; auto].
             subst; assert (~(Ptrofs.intval ofs <= ofs0 < Ptrofs.intval ofs + LKSIZE)).
             { intro; contradiction n0; split; auto. }
             rewrite !setPermBlock_var_other_1; auto; unfold LKSIZE_nat; rewrite Z2Nat.id; lkomega.
        * simpl.
          setoid_rewrite <- Hlock_perm.
          erewrite <- mtch_gtr2; eauto. }
    + eapply AngelSafe.
      { eapply sync_step with (Hcmpt0 := MTCH_compat _ _ _ H0 Hcmpt); eauto.
        eapply step_acqfail; simpl; eauto; simpl; eauto.
        * eapply MTCH_invariant; eauto.
        * erewrite restrPermMap_irr; eauto.
        * erewrite restrPermMap_irr; eauto. }
      { rewrite <- H6 in Hsafe; auto.
        intro; eapply IHn; auto.
        auto.
       }
(*  - inv Hhalted; contradiction.*)
  - subst; eapply AngelSafe.
    { simpl; rewrite <- H5.
      eapply schedfail; eauto; simpl.
      - inv H0.
        intro; contradiction Htid; apply mtch_cnt'; auto.
      - eapply MTCH_invariant; eauto.
      - eapply MTCH_compat; eauto. }
    { intro; eapply IHn; auto.
      { auto. }
    }
  Unshelve.
  all: auto.
  (*2: apply cntUpdate; auto.
  + unfold add_block.
    hnf in Hperm; subst.
    unshelve eapply @CoreLanguageDry.decay_compatible with (m := m); auto.
    * eapply MTCH_compat; eauto.
    * eapply MTCH_invariant; eauto.
    * split.
      { rewrite restrPermMap_valid; intros. 
(*        eapply Mem.valid_block_alloc_inv in H2; eauto. 
        rewrite restrPermMap_valid in H2; destruct H2; [|contradiction]. *)
        subst; right; intro. contradiction. }
      rewrite restrPermMap_valid; intro.
      right; intro. 
        erewrite restrPermMap_ext; eauto.
        intro; extensionality ofs2; auto.
  + eapply mem_compatible_updThreadC, MTCH_compat; eauto.*)
  + erewrite <- mtch_gtr2; eauto.
  + erewrite <- mtch_gtr2; eauto.
Admitted.


Definition init_threadpool := 
   @initial_machine (Clight_newSem ge)
     (@OrdinalPool.OrdinalThreadPool dryResources (Clight_newSem ge))
     (getCurPerm init_mem) (initial_corestate CPROOF).

Transparent getThreadC.

Lemma init_mem_ok: mem_ok init_threadpool init_mem.
Proof.
(*  unfold mem_ok, init_mem, semax_to_juicy_machine.init_mem, init_mem_not_none, CSL_init_mem_not_none,
    semax_initial.init_m, ge, prog.
*)
  split; [|split].
  - unfold init_mem, semax_to_juicy_machine.init_mem, init_mem_not_none, 
         semax_initial.init_m, ge, prog; simpl.
     destruct CPROOF; simpl.    
     destruct (Genv.init_mem CSL_prog) eqn: Hinit; try contradiction; simpl.
    unfold Smallstep.globals_not_fresh; simpl.
    erewrite Genv.init_mem_genv_next;  eauto.
    apply Pos.le_refl.
  - unfold init_mem, semax_to_juicy_machine.init_mem, init_mem_not_none, 
         semax_initial.init_m, ge, prog; simpl.
     destruct CPROOF; simpl.
     destruct (Genv.init_mem CSL_prog) eqn: Hinit; try contradiction; simpl.
     unfold Genv.init_mem in Hinit.
    eapply mem_wd2_alloc_globals; eauto.
    + unfold mem_wd'; simpl; intros.
      rewrite PMap.gi, ZMap.gi; constructor.
    + constructor.
      * unfold isGlobalBlock; intro.
        rewrite orb_true_iff.
        unfold genv2blocksBool; simpl.
        intros [|].
        -- destruct (Genv.invert_symbol _ _) eqn: Hsym; [|discriminate].
           apply Genv.invert_find_symbol in Hsym.
           eapply Genv.find_symbol_not_fresh; eauto.
        -- destruct (Genv.find_var_info _ _) eqn: Hsym; [|discriminate].
           eapply Genv.find_var_info_not_fresh; eauto.
      * intros.
        eapply Genv.find_funct_ptr_not_fresh; eauto.
  - simpl.
    unfold initial_corestate; simpl.
    destruct spr as (q & ? & [? Hinit] & s); simpl.
    destruct (s O) as (jm & Hjm & _).
    specialize (Hinit _ Hjm) as (? & ? & Hinit & _).
    unfold veric.Clight_core.cl_initial_core in Hinit; simpl in Hinit.
    destruct (Genv.find_funct_ptr _ _) eqn: Hfind; [|exfalso; auto].
    match_case in Hinit.
    destruct Hinit as (?&?&?&?). match_case in H2; subst.
    simpl. intros. split; auto.
Qed.

Lemma Clight_new_Clight_safety:
  (forall sch n,
    csafe
      (Sem := Clight_newSem ge)
      (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=Clight_newSem ge))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (sch, nil,
       DryHybridMachine.initial_machine
         (Sem := Clight_newSem ge)
         (permissions.getCurPerm init_mem)
        (initial_corestate CPROOF)) init_mem n) ->
  forall sch n,
    csafe
      (Sem := ClightSem ge)
      (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (sch, nil, (DryHybridMachine.initial_machine
         (Sem := ClightSem ge)
         (permissions.getCurPerm init_mem)
         initial_Clight_state)) init_mem n.
Proof.
  intros.
  eapply Clight_new_Clight_safety_gen; [apply init_mem_ok | apply H |].
  constructor; auto; intros; simpl.
  constructor.
  unfold initial_corestate, initial_Clight_state in *.
  destruct f_main as [? Hf]; destruct spr as (b & q & [? Hinit] & s); simpl in *.
  destruct (s O) as (jm & Hjm & _).
  simpl in Hinit. 
  specialize (Hinit _ Hjm) as (? & ? & Hinit & ?); subst; simpl in *.
  destruct (Genv.find_funct_ptr _ b); try contradiction.
  destruct (Clight.type_of_fundef f) eqn: Hty; try contradiction.
  destruct Hinit as (? & ? & ? & ?); subst.
  inv Hf. inv H2.
  admit. (* discrepancies in the initial states.*)
Admitted.


(*New safety theorem, with the correct initial state: 
  TODO: swap the names when we think it's ready.
 *)

(* This is the right initial state, should be a [Callstate]*)
Definition initial_Clight_state' : Clight.state.
Admitted.
Definition main_pointer:= Vptr (projT1 (spr CPROOF)) Ptrofs.zero.

(* Question: this proof assumes no arguments to main. 
   can we cahnge that? 
*)
Lemma initial_Clight_state_is_initial:
  Clight.entry_point ge init_mem initial_Clight_state' main_pointer nil.
Admitted.

  Local Ltac solve_schedule:=
      match goal with
      | [H: ?sch = schedSkip ?sch |- _ ] =>
        symmetry in H; apply schedSkip_id in H; subst
      | [H: schedSkip ?sch = ?sch |- _ ] =>
        apply schedSkip_id in H; subst
      end; simpl in *; congruence.
  
Lemma Clight_new_Clight_safety':
  (forall sch n,
    csafe
      (Sem := Clight_newSem ge)
      (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=Clight_newSem ge))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (sch, nil,
       DryHybridMachine.initial_machine
         (Sem := Clight_newSem ge)
         (permissions.getCurPerm init_mem)
        (initial_corestate CPROOF)) init_mem n) ->
  forall sch n,
    csafe
      (Sem := ClightSem ge)
      (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (sch, nil, (DryHybridMachine.initial_machine
         (Sem := ClightSem ge)
         (permissions.getCurPerm init_mem)
         initial_Clight_state')) init_mem n.
Proof.
  intros * Hsafe_new sch n.
  unshelve (exploit Clight_new_Clight_safety; eauto).
  exact sch. apply S; exact n.
  clear. revert sch.
  induction n; try solve[constructor].
  intros sch Hsafe.
  inv Hsafe; swap 2 3.
  - (*Halted*) constructor; auto.
  - (*Angelic steps, that change the schedule*)
    (* all of these cases should be impossible.*)
    simpl in *.
    inv Hstep; simpl in *; subst; try solve_schedule.
    + inv Htstep; simpl in *. inv Hcode.
      unfold Clight.at_external in *.
      unfold initial_Clight_state in *; simpl in *.
      do 3 match_case in Hat_external.
      unfold initial_Clight_state in Heqs. simpl in Heqs.
      inv Heqs. unfold f_main in H0; simpl in H0.
      repeat match_case in H0; simpl in H0.
      inv H0.
      unfold initial_Clight_state in Hat_external; inv Hat_external.
    + inv Htstep; simpl in *; inversion Hcode.
    + eapply AngelSafe; simpl; eauto.
      eapply schedfail; simpl; eauto.
      * admit. (*initial state satisfies invarian*)
      * admit. (*initial state is mem compatible*)
  - (* regular step. *)
    simpl in *.
    unfold MachStep in *; simpl in *.
    inv Hstep; simpl in *; subst; try solve_schedule.
    + inv Htstep. inv Hcode.
    + inv Htstep. inv Hcode.
    + inv Htstep. simpl in Hcorestep.
      simpl in Hcorestep.
      inv Hcode.
      remember (restrPermMap (proj1 (Hcmpt tid Htid))) as init_mem'.
      (* We need this rewrite to get the right semantics*)
      eapply (@ev_step_ax1 _ (CLC_evsem ge)) in Hcorestep.
      admit. (* Hopefully, the step in Hcorestep takes 
                us directly to [initial_Clight_state']
                i.e., initial_Clight_state' = c'.
                then, with some auxiliary proofs for memory,
                result follows from the induction hypothesis IHn.
              *)
Admitted.



End Clight_safety_equivalence.
