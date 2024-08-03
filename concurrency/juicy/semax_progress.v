Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.msl.seplog.
Require Import VST.msl.age_to.
Require Import VST.veric.aging_lemmas.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax_prog.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.shares.
Require Import VST.veric.age_to_resource_at.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.field_at.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.concurrency.juicy.semax_conc.
Require Import VST.concurrency.juicy.juicy_machine.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.juicy.JuicyMachineModule.
Require Import VST.concurrency.juicy.sync_preds_defs.
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.juicy.join_lemmas.
(*Require Import VST.concurrency.cl_step_lemmas.
Require Import VST.concurrency.resource_decay_lemmas.
Require Import VST.concurrency.resource_decay_join.*)
Require Import VST.concurrency.juicy.semax_invariant.
Require Import VST.concurrency.juicy.semax_simlemmas.
Require Import VST.concurrency.juicy.rmap_locking.
Require Import VST.concurrency.common.lksize.

Set Bullet Behavior "Strict Subproofs".

Import Mem.

Lemma load_at_phi_restrict ge i (tp : jstate ge) (cnti : containsThread tp i) m
      (compat : mem_compatible tp m) b ofs v sh R phi0 o :
  join_sub phi0 (getThreadR cnti) ->
  (LKspec LKSIZE R sh (b, ofs)) phi0 ->
  (* typically given by lock_coherence: *)
  AMap.find (elt:=option rmap) (b, ofs) (lset tp) = Some o ->
  load Mptr (restrPermMap (mem_compatible_locks_ltwritable compat)) b ofs = Some v ->
  load Mptr (@juicyRestrict_locks _ m (mem_compat_thread_max_cohere compat cnti)) b ofs = Some v.
Proof.
  intros (phi1, j) lk found.
  unfold juicyRestrict_locks in *.
  Transparent Mem.load.
  unfold Mem.load. simpl.
  match goal with
    |- (if _ ?m ?c _ _ ?r then _ else _) =_ ->
      (if _ ?m' _ _ _ _ then _ else _) = _ =>
    cut (valid_access m c b ofs r =
         valid_access m' c b ofs r) end.
  { intros E. if_tac [va|nva]; if_tac [va'|nva']; auto; exfalso; congruence. }
  unfold valid_access in *.
  f_equal.
  unfold range_perm in *.
  extensionality ofs'.
  extensionality r.
  unfold perm in *.
  pose proof restrPermMap_Cur as RR.
  unfold permission_at in *.
  rewrite RR.
  rewrite RR.
  unfold lockSet in *.

  assert (notnone : (snd (mem_access m)) ! b <> None). {
    destruct compat as (Phi & [_ _ W _ _]).
    specialize (W b ofs). unfold lockGuts in *. cleanup.
    unfold block in *.
    rewrite found in W.
    autospec W. specialize (W ofs).
    spec W. now split; simpl; auto; lkomega.
    unfold PMap.get in W. destruct ((snd (mem_access m)) ! b). congruence.
    pose proof Max_isCanonical m as can. hnf in can. apply equal_f with (x := ofs) in can.
    unfold getMaxPerm in *.
    simpl in *.
    rewrite can in W.
    inv W.
  }

  match goal with |- ?P = ?Q => cut (P /\ Q) end.
  { intros (?, ?). apply prop_ext; split; auto. }
  split.
  - setoid_rewrite A2PMap_found; eauto; try (unfold LKSIZE; lkomega).
    constructor.
  - unfold juice2Perm_locks in *.
    unfold mapmap in *.
    unfold getCurPerm in *.
    unfold PMap.get.
    simpl.
    rewrite PTree.gmap.
    unfold option_map.
    rewrite PTree.gmap1.
    unfold option_map.
    simpl.
    destruct ((snd (mem_access m)) ! b) eqn:E; [|tauto]. clear notnone.
    unfold perm_of_res_lock in *.
    specialize (lk (b, ofs')). simpl in lk.
    if_tac [r'|nr] in lk; [|now destruct nr; split; auto; unfold LKSIZE; lkomega].
    apply resource_at_join with (loc := (b, ofs')) in j.
    + destruct lk as (p & E0). rewrite E0 in j. inv j.
      * unfold block in *.
        rewr (OrdinalPool.getThreadR cnti @ (b, ofs')).
        simpl.
        unfold perm_of_sh.
        pose proof (readable_glb rsh3).
        repeat if_tac; try constructor; tauto.
      * unfold block in *.
        rewr (OrdinalPool.getThreadR cnti @ (b, ofs')).
        simpl.
        unfold perm_of_sh.
        pose proof (readable_glb rsh3).
        repeat if_tac; try constructor; tauto.
Qed.

Lemma valid_access_restrPermMap ge m i tp Phi b ofs ophi
  (compat : mem_compatible_with tp m Phi)
  (lock_coh : lock_coherence'(ge := ge) tp Phi m compat)
  (cnti : containsThread tp i)
  (Efind : AMap.find (elt:=option rmap) (b, Ptrofs.unsigned ofs) (lset tp) = Some ophi)
  (align : (size_chunk Mptr | snd (b, Ptrofs.unsigned ofs)))
  (Hlt' : permMapLt
           (setPermBlock (Some Writable) b (Ptrofs.intval ofs) (juice2Perm_locks (getThreadR cnti) m) LKSIZE_nat)
           (getMaxPerm m)) :
  valid_access (restrPermMap Hlt') Mptr b (Ptrofs.intval ofs) Writable.
Proof.
  split; [|exact align].
  intros ofs' r.
  unfold perm in *.
  pose proof restrPermMap_Cur as RR.
  unfold permission_at in *.
  rewrite RR.
  pose proof compat.(loc_writable) as LW.
  specialize (LW b (Ptrofs.unsigned ofs)). setoid_rewrite Efind in LW. autospec LW. specialize (LW ofs').
  rewrite setPermBlock_lookup.
  repeat (if_tac; [constructor |]).
  exfalso.
  simpl in r.
  assert (A : forall z, (b, z) <> (b, ofs') -> z <> ofs') by congruence.
  repeat match goal with H: (_,_)<>(_,_) |- _ => apply A in H end.
  contradiction H.
  unfold LKSIZE_nat; rewrite Z2Nat.id by lkomega.
  split; auto; lkomega.
Qed.

Lemma permMapLt_local_locks ge m i (tp : jstate ge) Phi b ofs ophi
      (compat : mem_compatible_with tp m Phi)
      (cnti : containsThread tp i)
      (Efind : AMap.find (elt:=option rmap) (b, Ptrofs.unsigned ofs) (lset tp) = Some ophi) :
  permMapLt
    (setPermBlock (Some Writable) b (Ptrofs.intval ofs)
                  (juice2Perm_locks (getThreadR cnti) m) LKSIZE_nat)
    (getMaxPerm m).
Proof.
  intros b' ofs'.
  assert (RR: (getMaxPerm m) !! b' ofs' = (mem_access m) !! b' ofs' Max)
    by (unfold getMaxPerm in *; rewrite PMap.gmap; reflexivity).

  pose proof compat.(loc_writable) as LW.
  specialize (LW b (Ptrofs.unsigned ofs)). setoid_rewrite Efind in LW. autospec LW. specialize (LW ofs').
  rewrite RR.
  rewrite setPermBlock_lookup; if_tac.
  { unfold LKSIZE_nat in H; rewrite Z2Nat.id in H by lkomega.
    destruct H; subst; auto. }
  rewrite <-RR.
  apply juice2Perm_locks_cohere, mem_compat_thread_max_cohere.
  eexists; eauto.
Qed.

(*
Lemma isLK_rewrite r :
  (forall (sh : Share.t) (rsh: readable_share sh) (z : Z) (P : preds), r <> YES sh rsh (LK z) P)
  <->
  ~ isLK r.
Proof.
  destruct r as [t0 | t0 p [] p0 | k p]; simpl; unfold isLK in *; split.
  all: try intros H ?; intros; breakhyps.
  intros E; injection E; intros; subst.
  apply H; eauto.
Qed.
*)

Section Progress.
  Variables
    (CS : compspecs)
    (ext_link : string -> ident)
    (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2).

  Definition Jspec' := (@OK_spec (Concurrent_Espec unit CS ext_link)).

  Open Scope string_scope.

  Theorem progress ge Gamma n state :
    ~ blocked_at_external state CREATE ->
    state_invariant Jspec' Gamma (S n) state ->
    exists state',
      state_step(ge := ge) state state'.
  Proof.
    intros not_spawn I.
    inversion I as [m tr sch tp Phi En envcoh (*mwellformed*) compat extcompat sparse lock_coh safety wellformed unique E]. rewrite <-E in *.
    destruct sch as [ | i sch ].

    (* empty schedule: we loop in the same state *)
    {
      exists state. subst. constructor.
    }

    destruct (ssrnat.leq (S i) tp.(num_threads).(pos.n)) eqn:Ei.

    (* the schedule selected one thread *)
    assert (cnti : ThreadPool.containsThread tp i) by apply Ei.
    remember (ThreadPool.getThreadC cnti) as ci eqn:Eci; symmetry in Eci.

    destruct ci as
        [ (* Krun *) ci
        | (* Kblocked *) ci
        | (* Kresume *) ci v
        | (* Kinit *) v1 v2 ].

    (* thread[i] is running *)
    {
      pose (jmi := jm_ cnti compat).
      (* pose (phii := m_phi jmi). *)
      (* pose (mi := m_dry jmi). *)

      destruct (j_at_external (cl_core_sem ge) ci (jm_ cnti compat)) eqn: Hext.

      (* thread[i] is running and about to call an external: Krun (at_ex c) -> Kblocked c *)
      {
        eexists.
        (* taking the step *)
        constructor.
        eapply JuicyMachine.suspend_step.
        + reflexivity.
        + reflexivity.
        + unshelve econstructor; try reflexivity; try eassumption.
          eexists; eauto.
      } (* end of Krun (at_ex c) -> Kblocked c *)

      destruct (cl_halted ci) eqn: Hhalt.

      (* thread[i] is halted *)
      { eexists; constructor.
        eapply halted_step with (i := Int.zero). (* Why doesn't cl_halted check the value? *)
        + reflexivity.
        + econstructor; eauto; simpl.
          rewrite Hhalt; discriminate.
        + reflexivity. }

      (* thread[i] is running and some internal step *)
      {
        (* get the next step of this particular thread (with safety for all oracles) *)
        assert (next: exists ci' jmi',
                   corestep (juicy_core_sem (cl_core_sem ge)) ci jmi ci' jmi'
                   (*/\ forall ora, jm_bupd ora (jsafeN Jspec' ge ora ci') jmi'*)).
        { specialize (safety i cnti).
          pose proof (safety tt) as safei.
          rewrite Eci in *.
          inversion safei as [ | ? ? ? c' m' step | | ]; subst; try congruence.
          { rewrite level_jm_ in H; setoid_rewrite H in En; discriminate. }
          exists c', m'. apply step.
        }

        destruct next as (ci' & jmi' & stepi (*& safei'*)).
        pose (tp' := age_tp_to (level jmi') tp).
        pose (tp'' := @updThread _ _ _ i tp' (cnt_age' cnti) (Krun ci') (m_phi jmi')).
        pose (cm' := (m_dry jmi', (tr, i :: sch, tp''))).
        exists cm'.
        apply state_step_c; [].
        match goal with |-@machine_step ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l ?m ?n =>
          replace _ with (@machine_step a b c d e f g h i j k (seq.cat l nil) m n) by (rewrite seq.cats0; reflexivity) end.
        apply @JuicyMachine.thread_step with (DilMem := HybridCoarseMachine.DilMem)
        (tid := i)
          (ev := nil)
          (Htid := cnti)
          (Hcmpt := mem_compatible_forget compat); [|]. reflexivity.
        eapply step_juicy; [ | | | | | ].
        + reflexivity.
        + now constructor.
        + exact Eci.
        + destruct stepi as [stepi decay].
          split.
          * simpl.
            subst.
            apply stepi.
          * simpl.
            exact_eq decay.
            reflexivity.
        + reflexivity.
        + reflexivity.
      } (* end of internal step *)
    } (* end of Krun *)

    (* thread[i] is in Kblocked *)
    {
      (* goes to Kresume ci' according to the rules of syncStep  *)

      pose proof (wellformed i cnti) as W.
      rewrite Eci in W.
      destruct ci as [ | f ? k | ]; try contradiction; simpl in W.
      destruct f as [| ef ?? cc]; try contradiction.
      destruct (ef_inline ef) eqn: Hinline; [contradiction | clear W].

      (* paragraph below: ef has to be an EF_external with one of those 5 names *)
      assert (exists name sg, ef = EF_external name sg /\
                (Some (ext_link "acquire", LOCK_SIG) = (ef_id_sig ext_link (EF_external name sg)) \/
                Some (ext_link "release", UNLOCK_SIG) = (ef_id_sig ext_link (EF_external name sg)) \/
                Some (ext_link "makelock", ef_sig MKLOCK) = (ef_id_sig ext_link (EF_external name sg)) \/
                Some (ext_link "freelock", ef_sig FREE_LOCK) = (ef_id_sig ext_link (EF_external name sg)) \/
                Some (ext_link "spawn", CREATE_SIG) = (ef_id_sig ext_link (EF_external name sg)))) as (name & sg & -> & which_primitive).
      {
        pose proof (safety i cnti tt) as safe_i.
        rewrite Eci in safe_i.
        fixsafe safe_i.
        inversion safe_i; subst.
        * rewrite level_jm_ in H; setoid_rewrite H in En; discriminate.
        * inv H. inv H1.
          rewrite Hinline in *; discriminate.
        * simpl in H.
          rewrite Hinline in H; inv H.
          match goal with x : ext_spec_type _ _  |- _ => clear -x; simpl in x end.
          unfold ef_id_sig in x.
          repeat match goal with
                   _ : context [ oi_eq_dec ?x ?y ] |- _ =>
                   destruct (oi_eq_dec x y); try (destruct e; inv e0; eexists; eexists; split; [reflexivity | rewrite H0; simpl; auto])
                 end.
          contradiction.
        * contradiction.
      }

      (* Before going any further, one needs to provide the first
        rmap of the oracle.  Unfortunately, for that, we need to know
        whether we're in an "acquire" external call or not. In
        addition, in the case of an "acquire" we need to know the
        arguments of the function (address+mpred) so that we can
        provide the right rmap from the lock set.
        |
        Two solutions: either we use a dummy oracle to know those things (but
        ... we need the oracle before that (FIX the spec OR [A]), or we write
        it as a P\/~P and then we derive a contradiction (not sure we can do
        that). *)

      destruct which_primitive as
          [ H_acquire | [ H_release | [ H_makelock | [ H_freelock | H_spawn ] ] ] ].

      { (* the case of acquire *)

        (* using the safety to prepare the precondition *)
        pose proof (safety i cnti tt) as safei.
        rewrite Eci in safei.
        fixsafe safei.
        inversion safei
          as [ | ????? bad | nz c m0 e args0 x at_ex Pre SafePost | ???? bad ]; last contradiction.
        { rewrite level_jm_ in H; setoid_rewrite H in En; discriminate. }
        { inv bad. inv H3. rewrite Hinline in *; discriminate. }
        subst.
        simpl in at_ex. injection at_ex as <- <-.
        hnf in x.
        revert x Pre SafePost.

        Local Notation "{| 'JE_spec ... |}" := {| JE_spec := _; JE_pre_hered := _; JE_post_hered := _; JE_exit_hered := _ |}.

        (* dependent destruction *)
        funspec_destruct "acquire".

        intros (phix, (ts, ((vx, shx), Rx))) (Hargsty, Pre).
        simpl (projT2 _) in *; simpl (fst _) in *; simpl (snd _) in *.
        simpl in Pre.
        destruct Pre as (phi0 & phi1 & Join & Precond & HnecR).
        simpl (and _).
        intros Post.

        (* relate lset to val *)
        destruct Precond as [PREA [PREB [_ PREC]]].
        hnf in PREB.
        unfold SeparationLogic.argsassert2assert, canon.SEPx in PREC.
        simpl in PREC.
        rewrite seplog.sepcon_emp in PREC.
        pose proof PREC as islock.
        apply lock_inv_at in islock.

        assert (SUB : join_sub phi0 Phi). {
          apply join_sub_trans with  (ThreadPool.getThreadR cnti).
          - econstructor; eauto.
          - apply compatible_threadRes_sub; eauto.
            destruct compat; eauto.
        }
        destruct islock as [b [ofs [-> [R islock]]]].
        pose proof (resource_at_join_sub _ _ (b, Ptrofs.unsigned ofs) SUB) as SUB'.
        pose proof islock_pred_join_sub SUB' islock as isl.

        (* PLAN
           - DONE: integrate the oracle in the semax_conc definitions
           - DONE: sort out this dependent type problem
           - DONE: exploit jsafeN_ to figure out which possible cases
           - DONE: push the analysis through Krun/Kblocked/Kresume
           - DONE: figure a wait out of the ext_link problem (the LOCK
             should be a parameter of the whole thing)
           - DONE: change the lock_coherence invariants to talk about
             Mem.load instead of directly reading the values, since
             this will be abstracted
           - DONE: acquire-fail: still problems (see below)
           - DONE: acquire-success: the invariant guarantees that the
             rmap in the lockset satisfies the invariant.  We can give
             this rmap as a first step to the oracle.  We again have
             to recover the fact that all oracles after this step will
             be fine as well.
           - TODO: spawning: it introduces a new Kinit, change
             invariant accordingly
           - DONE release: this time, the jsafeN_ will explain how to
             split the current rmap.
         *)

        (* next step depends on status of lock: *)
        pose proof (lock_coh (b, Ptrofs.unsigned ofs)) as lock_coh'.
        destruct (AMap.find (elt:=option rmap) (b, Ptrofs.unsigned ofs) (lset tp))
          as [[unlockedphi|]|] eqn:Efind.
        (* inversion lock_coh' as [wetv dryv notlock H H1 H2 | R0 wetv isl' Elockset Ewet Edry | R0 phi wetv isl' SAT_R_Phi Elockset Ewet Edry]. *)

        - (* acquire succeeds *)
          destruct isl as [sh [psh [z Ewetv]]].
          destruct lock_coh' as [LOAD ((* sh' &  *)align & bound & R' & lk & sat)].
          rewrite Ewetv in *.

          unfold lock_inv in PREC.
          destruct PREC as (b0 & ofs0 & EQ & LKSPEC).
          injection EQ as <- <-.

          specialize (lk (b, Ptrofs.unsigned ofs)).
          spec lk. hnf. pose proof LKSIZE_pos; split; auto; lia.
          destruct sat as [sat | sat]; [ | lia ].

          assert (Ename : name = "acquire"). {
            simpl in *.
            injection H_acquire as Ee.
            apply ext_link_inj in Ee; auto.
          }

          assert (Ez : z = LKSIZE). {
            simpl in lk.
            destruct lk as (psh' & rsh & EPhi).
            rewrite EPhi in Ewetv.
            injection Ewetv as _ <-.
            reflexivity.
          }

          assert (Eargs : l = Vptr b ofs :: nil) by auto.

          assert (Esg : sg = LOCK_SIG) by (unfold ef_id_sig in *; congruence).

          assert (Ecall: EF_external name sg = LOCK) by congruence.

          assert (Eae : at_external (@semSem (ClightSemanticsForMachines.ClightSem ge)) (Callstate (Ctypes.External (EF_external name sg) t0 t1 cc) l k) m =
                        Some (LOCK, Vptr b ofs :: nil)). {
            simpl.
            repeat f_equal; congruence.
          }

          assert (Hlt': permMapLt
                          (setPermBlock
                             (Some Writable) b (Ptrofs.intval ofs)
                             (juice2Perm_locks (getThreadR cnti) m) LKSIZE_nat) (getMaxPerm m)).
          {
            clear -Efind compat.
            eapply permMapLt_local_locks; eauto.
          }

          (* changing value of lock in dry mem *)
          assert (Hm' : exists m', Mem.store Mptr (restrPermMap Hlt') b (Ptrofs.intval ofs) (Vint Int.zero) = Some m'). {
            Transparent Mem.store.
            unfold Mem.store in *.
            destruct (Mem.valid_access_dec _ Mptr b (Ptrofs.intval ofs) Writable) as [N|N].
            now eauto.
            exfalso.
            apply N.
            clear -Efind lock_coh align.
            eapply valid_access_restrPermMap; eauto.
          }
          destruct Hm' as (m', Hm').

          (* joinability condition provided by invariant : phi' will
          be the thread's new rmap *)
          destruct (compatible_threadRes_lockRes_join (mem_compatible_forget compat) cnti _ Efind)
            as (phi', Jphi').

          (* necessary to know that we have indeed a lock *)
          assert (ex: exists sh0 psh0, forall j, 0 <= j < LKSIZE -> phi0 @ (b, Ptrofs.intval ofs+j) = YES sh0 psh0 (LK LKSIZE j) (pack_res_inv (approx (level phi0) Rx))). {
            clear -LKSPEC. simpl in LKSPEC.
            assert (rshx: readable_share shx). {
                 specialize (LKSPEC (b, Ptrofs.unsigned ofs)). rewrite if_true in LKSPEC.
                  destruct LKSPEC. auto. split; auto. pose proof LKSIZE_pos; lia.
            }
           exists shx, rshx. intros.
            specialize (LKSPEC (b, Ptrofs.intval ofs+j)).
            simpl in LKSPEC. rewrite if_true in LKSPEC. destruct LKSPEC as [rshx' ?].
            rewrite H0. f_equal. proof_irr. reflexivity. f_equal. unfold Ptrofs.unsigned. lia.
            split; auto. unfold Ptrofs.unsigned; lia.
          }
          destruct ex as (sh0 & psh0 & ex).
          pose proof (resource_at_join _ _ _ (b, Ptrofs.intval ofs) Join) as Join'.
          eexists (m', (seq.cat tr _, sch, _)).
          + (* taking the step *)
            apply state_step_c.
            apply JuicyMachine.sync_step
            with (ev := (Events.acquire (b, Ptrofs.intval ofs) None))
                   (tid := i)
                   (Htid := cnti)
                   (Hcmpt := mem_compatible_forget compat)
            ;
              [ reflexivity | reflexivity | ].
            eapply step_acquire
            with (R := approx (level phi0) Rx)
            (* with (sh := shx) *)
            .
            all: try match goal with |- _ = age_tp_to _ _ => reflexivity end.
            all: try match goal with |- _ = updLockSet _ _ _ => reflexivity end.
            all: try match goal with |- _ = updThread _ _ _ => reflexivity end.
            * now auto.
            * eassumption.
            * simpl.
              inv H_acquire; auto.
            * reflexivity.
            * instantiate (1:=shx). hnf; intros.
              specialize (ex i0 H).
              assert (Join0 := resource_at_join _ _ _ (b, Ptrofs.intval ofs + i0) Join).
              destruct (join_YES_l Join0 ex) as (sh3 & sh3' & E3).
              exists sh3, sh3'. split; auto. subst.
              clear - Join0 ex E3 LKSPEC H.
              rewrite ex in Join0. rewrite E3 in Join0.
              specialize (LKSPEC (b, Ptrofs.intval ofs + i0)).
              rewrite jam_true in LKSPEC by (split; auto; unfold Ptrofs.unsigned; lia).
              destruct LKSPEC as [? LKSPEC]. simpl in LKSPEC. rewrite LKSPEC in ex; inv ex.
              inv Join0; exists sh2; auto.
            * reflexivity.
            * eapply load_at_phi_restrict with (phi0 := phi0) (cnti := cnti) in LOAD.
              all: [ > assumption | exists phi1; eassumption | eassumption | eassumption ].
            * reflexivity.
            * reflexivity.
            * apply Hm'.
            * apply Efind.
            * apply Jphi'.

        - (* Some None: lock is locked, so [acquire] fails. *)
          destruct lock_coh' as [LOAD ((* sh' & *) align & bound & R' & lk)].
          destruct isl as [sh [psh [z Ewetv]]].
          rewrite Ewetv in *.

          (* rewrite Eat in Ewetv. *)
          specialize (lk (b, Ptrofs.unsigned ofs)).
          spec lk. pose proof LKSIZE_pos; split; auto; lia.

          unfold lock_inv in PREC.
          destruct PREC as (b0 & ofs0 & EQ & LKSPEC).
          injection EQ as <- <-.
          exists (m, (seq.cat tr (Events.external i (Events.failacq (b, Ptrofs.intval ofs)) :: nil), sch, tp))(* ; split *).
          + apply state_step_c.
            apply JuicyMachine.sync_step with
            (Htid := cnti)
              (Hcmpt := mem_compatible_forget compat);
              [ reflexivity (* schedPeek *)
              | reflexivity (* schedSkip *)
              | ].
            (* factoring proofs out before the inversion/eapply *)
            pose proof LKSPEC as LKSPEC'.
            specialize (LKSPEC (b, Ptrofs.unsigned ofs)).
            simpl in LKSPEC.
            if_tac [r|nr] in LKSPEC; [|destruct nr; split; auto; pose proof LKSIZE_pos; lia].
            destruct LKSPEC as (p & E).
            pose proof (resource_at_join _ _ _ (b, Ptrofs.unsigned ofs) Join) as J.
            rewrite E in J.

            assert (Ename : name = "acquire"). {
              simpl in *.
              injection H_acquire as Ee.
              apply ext_link_inj in Ee; auto.
            }

            assert (Ez : z = LKSIZE). {
              simpl in lk.
              destruct lk as (psh' & rsh & EPhi).
              rewrite EPhi in Ewetv.
              injection Ewetv as _ <-.
              reflexivity.
            }

            assert (Esg : sg = LOCK_SIG) by (unfold ef_id_sig in *; congruence).

            assert (Eargs : l = Vptr b ofs :: nil) by auto.

            assert (Ecall: EF_external name sg = LOCK) by congruence.

            assert (Eae : at_external (@semSem (ClightSemanticsForMachines.ClightSem ge)) (Callstate (Ctypes.External (EF_external name sg) t0 t1 cc) l k) m =
                    Some (LOCK, Vptr b ofs :: nil)). {
              simpl.
              repeat f_equal; congruence.
            }

            unfold load_at in LOAD.
            eapply load_at_phi_restrict with (phi0 := phi0) (cnti := cnti) in LOAD.
            all: [ > | exists phi1; eassumption | eassumption | eassumption ].

            inversion J; subst.

            * eapply step_acqfail with (Hcompat := mem_compatible_forget compat)
                                       (R := approx (level phi0) Rx).
              all: try solve [ constructor | eassumption | reflexivity ].
                (* [ > idtac ]. *)
              simpl.
              unfold Ptrofs.unsigned in *.
              intros. instantiate (1:=shx). hnf. intros.
              apply (resource_at_join _ _ _ (b, Ptrofs.intval ofs+i0)) in Join.
              specialize (LKSPEC' (b, Ptrofs.intval ofs+i0)).
              rewrite jam_true in LKSPEC' by (split; auto; lia).
              destruct LKSPEC' as [rsh8 LKSPEC']. simpl in LKSPEC'. rewrite LKSPEC' in Join.
              inv Join; replace (Ptrofs.intval ofs + i0 - Ptrofs.intval ofs) with i0 in * by lia.
              exists sh4, rsh2; split; auto. eexists; eassumption.
              exists sh4, rsh4; split; auto. eexists; eassumption.              
            * eapply step_acqfail with (Hcompat := mem_compatible_forget compat)
                                       (R := approx (level phi0) Rx).
              all: try solve [ constructor | eassumption | reflexivity ].
              simpl.
              unfold Ptrofs.unsigned in *.
              instantiate (1:=shx). hnf. intros.
              apply (resource_at_join _ _ _ (b, Ptrofs.intval ofs+i0)) in Join.
              specialize (LKSPEC' (b, Ptrofs.intval ofs+i0)).
              rewrite jam_true in LKSPEC' by (split; auto; lia).
              destruct LKSPEC' as [rsh8 LKSPEC']. simpl in LKSPEC'. rewrite LKSPEC' in Join.
              inv Join; replace (Ptrofs.intval ofs + i0 - Ptrofs.intval ofs) with i0 in * by lia.
              exists sh4, rsh4; split; auto. eexists; eassumption.
              exists sh4, rsh5; split; auto. eexists; eassumption.    

        - (* None: that cannot be: there is no lock at that address *)
          exfalso.
          destruct isl as [x [? [? EPhi]]].
          rewrite EPhi in lock_coh'.
          apply lock_coh'. hnf. eauto.

      }

      { (* the case of release *)

        (* using the safety to prepare the precondition *)
        pose proof (safety i cnti tt) as safei.
        rewrite Eci in safei.
        fixsafe safei.
        inversion safei
          as [ | ????? bad | z c m0 e args0 x at_ex Pre SafePost | ???? bad ]; last contradiction.
        { rewrite level_jm_ in H; setoid_rewrite H in En; discriminate. }
        { inv bad. inv H3. rewrite Hinline in *; discriminate. }
        subst.
        simpl in at_ex. injection at_ex as <- <-.
        hnf in x.
        revert x Pre SafePost.

        (* dependent destruction *)
        funspec_destruct "acquire".
        funspec_destruct "release".

        intros (phix, (ts, ((vx, shx), Rx))) (Hargsty, Pre).
        simpl (projT2 _) in *; simpl (fst _) in *; simpl (snd _) in *; clear ts.
        simpl in Pre.
        destruct Pre as (phi0 & phi1 & Join & Precond & HnecR).
        simpl (and _).
        intros Post.

        (* relate lset to val *)
        destruct Precond as ((Hreadable & _) & PreB1 & _ & PreC).
        unfold SeparationLogic.argsassert2assert, canon.SEPx in PreC.
        unfold base.fold_right_sepcon in *.
        rewrite seplog.sepcon_emp in PreC.
        rewrite seplog.corable_andp_sepcon1 in PreC by apply conclib.corable_weak_exclusive.
        rewrite seplog.sepcon_comm in PreC.
        rewrite seplog.sepcon_emp in PreC.
        destruct PreC as (Hexclusive, PreC).
        destruct PreC as (phi_lockinv & phi_sat & jphi & Hlockinv & SAT).
        pose proof Hlockinv as islock.
        apply lock_inv_at in islock.

        assert (SUB : join_sub phi_lockinv Phi). {
          apply join_sub_trans with phi0. econstructor; eauto.
          apply join_sub_trans with (getThreadR cnti). econstructor; eauto.
          apply compatible_threadRes_sub; eauto. apply compat.
        }
        destruct islock as [b [ofs [-> [R islock]]]].
        pose proof (resource_at_join_sub _ _ (b, Ptrofs.unsigned ofs) SUB) as SUB'.
        pose proof islock_pred_join_sub SUB' islock as isl.

        (* next step depends on status of lock: *)
        pose proof (lock_coh (b, Ptrofs.unsigned ofs)) as lock_coh'.
        destruct (AMap.find (elt:=option rmap) (b, Ptrofs.unsigned ofs) (lset tp))
          as [[unlockedphi|]|] eqn:Efind.

        - (* Some Some: lock is unlocked, this should be impossible *)
          destruct lock_coh' as [LOAD (align & bound & R' & lk & sat)].
          destruct sat as [sat | ?]; [ | congruence ].
          destruct isl as [sh [psh [z Ewetv]]].
          rewrite Ewetv in *.
          exfalso.
          clear Post.

          (* sketch: *)
          (* - [unlockedphi] satisfies R *)
          (* - [phi_sat] satisfies R *)
          (* - [unlockedphi] and [phi_sat] join *)
          (* - but R is exclusive so that's impossible *)

          pose proof predat6 lk as E1.
          pose proof predat1 Ewetv as E2.
          pose proof predat4 Hlockinv as E3.
          apply (predat_join_sub SUB) in E3.
          assert (level phi_lockinv = level Phi) by apply join_sub_level, SUB.
          assert (level unlockedphi = level Phi).
          { eapply join_sub_level, compatible_lockRes_sub_all; simpl;
              eauto; apply compat. }
          rewr (level phi_lockinv) in E3.
          assert (join_sub phi_sat Phi). {
            apply join_sub_trans with phi0. hnf; eauto.
            apply join_sub_trans with (getThreadR cnti). hnf; eauto.
            apply compatible_threadRes_sub. apply compat.
          }
          assert (level phi_sat = level Phi) by (apply join_sub_level; auto).

          assert (joins (age_by 1 phi_sat) (age_by 1 unlockedphi)) as [phi' J%join_comm].
          { apply age_by_joins.
            eapply @join_sub_joins_trans with (c := phi0); auto. apply Perm_rmap.
            * exists phi_lockinv. apply join_comm. auto.
            * eapply @join_sub_joins_trans with (c := getThreadR cnti); auto. apply Perm_rmap.
              -- exists phi1. auto.
              -- eapply compatible_threadRes_lockRes_join. apply (mem_compatible_forget compat).
                 apply Efind. }
          specialize (Hexclusive phi').
          spec Hexclusive.
          { apply join_level in J as [].
            apply join_level in jphi as [].
            rewrite level_age_by in *; lia. }
          specialize (Hexclusive _ _ (necR_refl _) (ext_refl _)); apply Hexclusive.
          eexists; eexists; split; eauto; split.

          + (* sat 1 *)
            revert sat.
            apply approx_eq_app_pred with (level Phi).
            * rewrite level_age_by. rewr (level unlockedphi). lia.
            * eapply predat_inj; eauto.

          + (* sat 2 *)
            revert SAT. apply age_by_ind.
            apply pred_hereditary.

        - (* Some None: lock is locked, so [release] should succeed. *)
          destruct lock_coh' as [LOAD ((* sh' &  *)align & bound & R' & lk)].
          destruct isl as [sh [psh [z Ewetv]]].
          rewrite Ewetv in *.

          (* rewrite Eat in Ewetv. *)
          specialize (lk (b, Ptrofs.unsigned ofs)).
          spec lk.
          { hnf. split; auto; lkomega. }
          destruct lk as (sh' & rsh & EPhi).

          assert (Ename : name = "release"). {
            simpl in *.
            injection H_release as Ee.
            apply ext_link_inj in Ee; auto.
          }

          assert (Ez : z = LKSIZE). {
            rewrite EPhi in Ewetv.
            injection Ewetv as _ <-.
            reflexivity.
          }

          assert (Esg : sg = LOCK_SIG) by (unfold ef_id_sig in *; congruence).

          assert (Eargs : l = Vptr b ofs :: nil) by auto.

          assert (Ecall: EF_external name sg = UNLOCK) by congruence.

          assert (Eae : at_external (@semSem (ClightSemanticsForMachines.ClightSem ge)) (Callstate (Ctypes.External (EF_external name sg) t0 t1 cc) l k) m =
                        Some (UNLOCK, Vptr b ofs :: nil)). {
            simpl.
            auto.
          }
          subst z.
          assert (E1: exists sh, lock_at_least sh (approx (level phi_lockinv) Rx) (getThreadR cnti) b (Ptrofs.intval ofs)).
          { exists shx. hnf; intros.
            clear - Join jphi Hlockinv H.
            assert (join_sub phi_lockinv  (getThreadR cnti)).
            eapply join_sub_trans. eexists; apply jphi. eexists; eassumption.
            apply (resource_at_join_sub _ _ (b, Ptrofs.intval ofs + i0)) in H0.
            forget (getThreadR cnti @ (b, Ptrofs.intval ofs + i0)) as r.
            unfold lock_inv in  Hlockinv. destruct Hlockinv as [b' [ofs' [? ?]]].
            inversion H1; subst b' ofs'. simpl in H2.
            specialize (H2 (b, Ptrofs.intval ofs + i0)). clear H1.
            rewrite if_true in H2 by (split; auto; unfold Ptrofs.unsigned; lia).
            destruct H2 as [rsh H2]. rewrite H2 in H0. destruct H0 as [sh ?].
            simpl in *.
            replace (Ptrofs.intval ofs + i0 - Ptrofs.unsigned ofs) with i0 in * by (unfold Ptrofs.unsigned; lia).
            inv H0.
            exists sh3, rsh3. split. exists sh2; auto. reflexivity.
            exists sh3, rsh3. split. exists sh2; auto. reflexivity.
          }
          destruct E1 as (sh1 & E1).

          assert (Hlt': permMapLt
                          (setPermBlock
                             (Some Writable) b (Ptrofs.intval ofs)
                             (juice2Perm_locks (getThreadR cnti) m) LKSIZE_nat) (getMaxPerm m)).
          {
            clear -Efind compat.
            clear -Efind compat.
            eapply permMapLt_local_locks; eauto.
          }

          (* changing value of lock in dry mem *)
          assert (Hm' : exists m', Mem.store Mptr (restrPermMap Hlt') b (Ptrofs.intval ofs) (Vptrofs Ptrofs.one) = Some m'). {
            Transparent Mem.store.
            unfold Mem.store in *.
            destruct (Mem.valid_access_dec _ Mptr b (Ptrofs.intval ofs) Writable) as [N|N].
            now eauto.
            exfalso.
            apply N.
            clear -Efind lock_coh align.
            eapply valid_access_restrPermMap; eauto.
          }
          destruct Hm' as (m', Hm').

          (* remove [phi_sat] from [getThreadR cnti] to get the new [phi'] *)
          assert (Hphi' : exists phi',
                     join phi_lockinv phi1 phi' /\
                     join phi' phi_sat (getThreadR cnti)). {
            repeat match goal with H : join _ _ _ |- _ => revert H end; clear; intros.
            apply join_comm in jphi.
            destruct (sepalg.join_assoc jphi Join) as (phi' & j1 & j2).
            eauto.
          }
          destruct Hphi' as (phi' & Ephi' & Join_with_sat).

          assert (Sat : R (age_by 1 phi_sat)). {
            clear Post Hm' safei Eci Heq_name Heq_name0 LOAD Eae.
            apply predat4 in Hlockinv.
            apply predat5 in islock.
            pose proof predat_inj islock Hlockinv.
            subst R.
            split.
            - rewrite level_age_by.
              replace (level phi_sat) with (level Phi) by join_level_tac.
              replace (level phi_lockinv) with (level Phi) by join_level_tac.
              lia.
            - hered.
              apply age_by_1. replace (level phi_sat) with (level Phi). lia. join_level_tac.
              apply pred_hered.
          }

          eexists (m', (seq.cat tr _, sch, _)).
          eapply state_step_c.
          eapply JuicyMachine.sync_step with (Htid := cnti); auto.
          destruct Hlockinv as (b00 & ofs00 & E & WOB); injection E as <- <-.
          eapply load_at_phi_restrict with (phi0 := phi_lockinv) (cnti := cnti) in LOAD; try eassumption.
          eapply step_release with (d_phi := phi_sat); try eassumption; try reflexivity.
          + clear - jphi SAT SUB En.
              split; auto. rewrite level_age_by. apply join_level in jphi as [H ->].
              apply join_sub_level in SUB. lia.
              simpl. unfold age1'. destruct (age1 phi_sat) eqn:?; auto.
              eapply pred_nec_hereditary; try eassumption. constructor 1. auto.
          + eauto.
          + apply join_sub_trans with phi0. eexists; eauto.
            eexists. eapply join_comm. eauto.
        - (* None: that cannot be: there is no lock at that address *)
          exfalso.
          destruct isl as [x [? [? EPhi]]].
          rewrite EPhi in lock_coh'.
          apply lock_coh'. repeat eexists.
      }

      { (* the case of makelock *)

        (* using the safety to prepare the precondition *)
        pose proof (safety i cnti tt) as safei.
        rewrite Eci in safei.
        fixsafe safei.
        inversion safei
          as [ | ????? bad | z c m0 e args0 x at_ex Pre SafePost | ???? bad ]; last contradiction.
        { rewrite level_jm_ in H; setoid_rewrite H in En; discriminate. }
        { inv bad. inv H3. rewrite Hinline in *; discriminate. }
        subst.
        simpl in at_ex. injection at_ex as <- <-.
        hnf in x.
        revert x Pre SafePost.

        (* dependent destruction *)
        funspec_destruct "acquire".
        funspec_destruct "release".
        funspec_destruct "makelock".

        intros (phix, (ts, ((vx, shx), Rx))) (Hargsty, Pre).
        simpl (projT2 _) in *; simpl (fst _) in *; simpl (snd _) in *; clear ts.
        simpl in Pre.
        destruct Pre as (phi0 & phi1 & Join & Precond & HnecR).
        simpl (and _).
        intros Post.

        assert (Ename : name = "makelock"). {
          simpl in *.
          injection H_makelock as Ee.
          apply ext_link_inj in Ee; auto.
        }

        assert (Esg : sg = UNLOCK_SIG) by (unfold ef_id_sig, ef_sig in *; congruence).

        destruct Precond as [[Hwritable _] [B1 [_ AT]]].
        assert (Hreadable : readable_share shx) by (apply writable0_readable; auto).

        (* [data_at_] from the precondition *)
        unfold SeparationLogic.argsassert2assert, canon.SEPx in *.
        simpl in AT.
        rewrite seplog.sepcon_emp in AT.

        (* value of [vx] *)
        assert (Eargs : l = vx :: nil) by auto.

        assert (Ecall: EF_external name sg = MKLOCK) by congruence.

        assert (Eae : at_external (@semSem (ClightSemanticsForMachines.ClightSem ge)) (Callstate (Ctypes.External (EF_external name sg) t0 t1 cc) l k) m =
                      Some (MKLOCK, vx :: nil)). {
          simpl.
          repeat f_equal; congruence.
        }

        assert (exists b ofs, vx = Vptr b ofs) as (b & ofs & ->).
        { destruct AT as [[] _]. destruct vx; try contradiction; eauto. }

        assert (Hm' : exists m', Mem.store Mptr (m_dry (personal_mem (thread_mem_compatible (mem_compatible_forget compat) cnti))) b (Ptrofs.intval ofs) (Vptrofs Ptrofs.zero) = Some m'). {
          clear -AT Join Hwritable.
          unfold tlock in AT.
          destruct AT as (AT1, [_ B]).
          simpl in B. unfold mapsto_memory_block.at_offset in B.
          rewrite seplog.sepcon_emp in B.
          (* if array size > 4:
          destruct B as (phi00 & phi01 & jphi0 & B & _).
          *)
          unfold SeparationLogic.mapsto in *.
          simpl in B.
          rewrite !Ptrofs.add_zero in B.
          destruct (readable_share_dec shx) as [n|n]; [|now destruct n; apply writable0_readable; auto].
          rewrite !(log_normalize.prop_false_andp False), !FF_orp in B by auto.
          rewrite log_normalize.exp_andp2, log_normalize.exp_sepcon1 in B.
          destruct B as [v2' B].
          apply mapsto_can_store with (v := v2') (sh := shx); try assumption.
          auto.
          simpl (m_phi _).
          destruct B as [phi0a [phi0b [? [[] ?]]]].
          destruct (join_assoc H Join) as [f [? ?]].
          exists phi0a, f; repeat split; auto.
        }
        destruct Hm' as (m', Hm').

        clear Post.

        unfold tlock in *.
        match type of AT with context[Tarray _ ?n] => assert (Hpos : (0 < n)%Z) by lia end.
        pose proof data_at_rmap_makelock CS as RL.
        specialize (RL shx b ofs Rx phi0 _ Hpos (writable_writable0 Hwritable) AT).
        destruct RL as (phi0' & RL0 & lkat).

        match type of lkat with context[LK_at _ ?n] => assert (Hpos' : (0 < n)%Z) by (rewrite size_chunk_Mptr in *; destruct Archi.ptr64; lia) end.
        pose proof rmap_makelock_join _ _ _ _ _ _ _ Hpos' RL0 Join as RL.
        destruct RL as (phi' & RLphi & j').
        assert (ji : join_sub (getThreadR cnti) Phi) by (apply compatible_threadRes_sub, compat).
        destruct ji as (psi & jpsi). cleanup.
        pose proof rmap_makelock_join _ _ _ _ _ _ _ Hpos' RLphi jpsi as RLPhi.
        destruct RLPhi as (Phi' & RLPhi & J').

        eexists (m', (seq.cat tr _, sch, _)).
        constructor.

        eapply JuicyMachine.sync_step with (Htid := cnti); auto.

        eapply step_mklock; try eassumption; auto.
        + constructor.
        + apply Hm'.
        + eassumption.
      }

      { (* the case of freelock *)

        (* using the safety to prepare the precondition *)
        pose proof (safety i cnti tt) as safei.
        rewrite Eci in safei.
        fixsafe safei.
        inversion safei
          as [ | ????? bad | z c m0 e args0 x at_ex Pre SafePost | ???? bad ]; last contradiction.
        { rewrite level_jm_ in H; setoid_rewrite H in En; discriminate. }
        { inv bad. inv H3. rewrite Hinline in *; discriminate. }
        subst.
        simpl in at_ex. injection at_ex as <- <-.
        hnf in x.
        revert x Pre SafePost.

        (* dependent destruction *)
        funspec_destruct "acquire".
        funspec_destruct "release".
        funspec_destruct "makelock".
        funspec_destruct "freelock".

        intros (phix, (ts, ((vx, shx), Rx))) (Hargsty, Pre).
        simpl (projT2 _) in *; simpl (fst _) in *; simpl (snd _) in *; clear ts.
        simpl in Pre.
        destruct Pre as (phi0 & phi1 & Join & Precond & HnecR).
        simpl (and _).
        intros Post.

        assert (Ename : name = "freelock"). {
          simpl in *.
          injection H_freelock as Ee.
          apply ext_link_inj in Ee; auto.
        }

        assert (Esg : sg = UNLOCK_SIG) by (unfold ef_id_sig, ef_sig in *; congruence).

        destruct Precond as ([Hwritable _] & B1 & _ & PreC).
        unfold SeparationLogic.argsassert2assert, canon.SEPx in PreC.
        unfold base.fold_right_sepcon in *.
        rewrite seplog.sepcon_emp in PreC.
        rewrite seplog.corable_andp_sepcon1 in PreC by (apply conclib.corable_weak_exclusive).
        rewrite seplog.sepcon_comm in PreC.
        rewrite seplog.sepcon_emp in PreC.
        destruct PreC as (Hexclusive, AT).
        (* pose proof AT as islock. *)
        (* apply lock_inv_at in islock. *)
        assert (Hreadable : readable_share shx) by (apply writable0_readable; auto).

        (* [data_at_] from the precondition *)
        unfold canon.SEPx in *.

        (* value of [vx] *)
        simpl in B1.
        rewrite lockinv_isptr in AT.

        destruct AT as (phi0lockinv & phi0sat & jphi0 & (IsPtr & Hlockinv) & Hsat).
        destruct vx as [ | | | | | b ofs ]; try inversion IsPtr; [ clear IsPtr ].

        assert (Eargs : l = Vptr b ofs :: nil) by auto.

        assert (Ecall: EF_external name sg = FREE_LOCK) by congruence.

        assert (Eae : at_external (@semSem (ClightSemanticsForMachines.ClightSem ge)) (Callstate (Ctypes.External (EF_external name sg) t0 t1 cc) l k) m =
                      Some (FREE_LOCK, Vptr b ofs :: nil)). {
          simpl.
          repeat f_equal; congruence.
        }

        clear Post.

        assert (lock_not_none : lockRes tp (b, Ptrofs.intval ofs) <> None). {
          specialize (lock_coh (b, Ptrofs.intval ofs)). cleanup.
          destruct (AMap.find _ _) as [|] eqn:Ephi_sat. congruence.
          unfold lock_inv in *.
          destruct Hlockinv as (b_ & ofs_ & E_ & HH).
          specialize (HH (b, Ptrofs.intval ofs)).
          simpl in HH.
          change Ptrofs.intval with Ptrofs.unsigned in *.
          injection E_ as <- <- .
          if_tac [r|nr] in HH; [|range_tac].
          destruct HH as (p & HH).
          assert (j : join_sub phi0lockinv Phi). {
            apply join_sub_trans with phi0. eexists; eauto.
            apply join_sub_trans with (@getThreadR _ _ _ i tp cnti). eexists; eauto.
            apply compatible_threadRes_sub, compat.
          }
          destruct j as (psi' & j).
          apply resource_at_join with (loc := (b, Ptrofs.unsigned ofs)) in j.
          rewrite HH in j.
          destruct lock_coh. clear - j. rewrite Z.sub_diag in j.
          inv j; hnf; repeat eexists; eauto.
        }

        assert ((align_chunk Mptr | Ptrofs.unsigned ofs) /\ (Ptrofs.unsigned ofs + LKSIZE < Ptrofs.modulus)%Z) as [].
        { 
          specialize (lock_coh (b, Ptrofs.intval ofs)). cleanup.
          remember (AMap.find (elt:=option rmap) _ _) as o in lock_coh.
          rewrite <-Heqo in lock_not_none.
          destruct o as [[phi_sat|]|]; [ | | ]; try solve [destruct lock_coh as (? & ? & ? & ?); auto].
          tauto.
        }
        pose proof Hlockinv as COPY.
        apply (lock_inv_rmap_freelock CS) with (m := m) in COPY; auto; try apply lock_coh.

        destruct COPY as (phi0lockinv' & Hrmap00 & Hlkat).

        pose proof rmap_freelock_join _ _ _ _ _ _ _ _ LKSIZE_pos Hrmap00 jphi0 as Hrmap0.
        destruct Hrmap0 as (phi0' & Hrmap0 & jphi0').
        pose proof rmap_freelock_join _ _ _ _ _ _ _ _ LKSIZE_pos Hrmap0 Join as Hrmap.
        pose proof Hrmap as Hrmap_.
        destruct Hrmap_ as (phi' & RLphi & j').
        assert (ji : join_sub (getThreadR cnti) Phi) by (apply compatible_threadRes_sub, compat).
        destruct ji as (psi & jpsi). cleanup.
        pose proof rmap_freelock_join _ _ _ _ _ _ _ _ LKSIZE_pos RLphi jpsi as Hrmap'.
        destruct Hrmap' as (Phi' & Hrmap' & J').

        assert (locked : lockRes tp (b, Ptrofs.intval ofs) = Some None). {
          specialize (lock_coh (b, Ptrofs.intval ofs)). cleanup.
          destruct (AMap.find _ _) as [[phi_sat|]|] eqn:Ephi_sat; [ exfalso | reflexivity | exfalso ].
          - (* exclusive *)
            destruct lock_coh as (_&_&_&R&lk&[sat|?]); [|lia].

            assert (J0 : join_sub phi0 Phi). {
              apply join_sub_trans with (@getThreadR _ _ _ i tp cnti). eexists; eauto.
              apply compatible_threadRes_sub, compat.
            }
            assert (Ja0 : join_sub phi0sat Phi).  {
              apply join_sub_trans with phi0; eauto. eexists; eauto.
            }
            assert (Ja : join_sub phi_sat Phi). {
              eapply compatible_lockRes_sub_all; simpl; eauto.
              apply compat.
            }
            assert (J01 : join_sub phi0lockinv Phi). {
              apply join_sub_trans with phi0. eexists; eauto.
              apply join_sub_trans with (@getThreadR _ _ _ i tp cnti). eexists; eauto.
              apply compatible_threadRes_sub, compat.
            }
            assert (R01 : level phi0lockinv = level Phi) by join_level_tac.
            assert (Ra : level phi_sat = level Phi) by join_level_tac.
            assert (Ra0 : level phi0sat = level Phi) by join_level_tac.
            pose proof predat6 lk as E1.
            pose proof predat4 Hlockinv as E3.
            apply (predat_join_sub J01) in E3.

            assert (joins (age_by 1 phi_sat) (age_by 1 phi0sat)) as [phis J].
            { apply age_by_joins.
              apply joins_comm.
              eapply @join_sub_joins_trans with (c := phi0); auto. apply Perm_rmap.
              * eexists. apply join_comm. eauto.
              * eapply @join_sub_joins_trans with (c := OrdinalPool.getThreadR cnti); auto. apply Perm_rmap.
                -- exists phi1. auto.
                -- eapply compatible_threadRes_lockRes_join. apply (mem_compatible_forget compat).
                   apply Ephi_sat. }
            specialize (Hexclusive phis).
            spec Hexclusive.
            { apply join_level in J as [].
              destruct J0 as [? J0]; apply join_level in J0 as [].
              destruct Ja as [? Ja]; apply join_level in Ja as [].
              rewrite level_age_by in *; lia. }
            specialize (Hexclusive _ _ (necR_refl _) (ext_refl _)); apply Hexclusive.
            eexists; eexists; split; eauto; split.

            + (* sat 1 *)
              revert sat.
              apply approx_eq_app_pred with (level Phi).
              * rewrite level_age_by. rewr (level phi_sat). lia.
              * eapply predat_inj; eauto.
                 apply predat6 in lk; eauto.
                 exact_eq E3. f_equal. f_equal. auto.

            + (* sat 2 *)
              revert Hsat. apply age_by_ind.
              apply pred_hereditary.

          - (* not a lock: impossible *)
            simpl in Hlockinv.
            unfold lock_inv in *.
            destruct Hlockinv as (b_ & ofs_ & E_ & HH).
            specialize (HH (b, Ptrofs.intval ofs)).
            simpl in HH.
            change Ptrofs.intval with Ptrofs.unsigned in *.
            injection E_ as <- <- .
            if_tac [r|nr] in HH; [|range_tac].
            destruct HH as (p & HH).
            assert (j : join_sub phi0lockinv Phi). {
              apply join_sub_trans with phi0. eexists; eauto.
              apply join_sub_trans with (@getThreadR _ _ _ i tp cnti). eexists; eauto.
              apply compatible_threadRes_sub, compat.
            }
            destruct j as (psi' & j).
            apply resource_at_join with (loc := (b, Ptrofs.unsigned ofs)) in j.
            rewrite HH in j.
            apply lock_coh. rewrite Z.sub_diag in j.
            inv j; hnf; eauto.
        }

        eexists (m, (seq.cat tr _, sch, _)).
        constructor.

        eapply JuicyMachine.sync_step with (Htid := cnti); auto.
        eapply step_freelock.

        all: try match goal with |- invariant _ => now constructor end.
        all: try match goal with |- _ = age_tp_to _ _ => reflexivity end.
        all: try match goal with |- _ = updThread _ _ _ => reflexivity end.
        all: try match goal with |- personal_mem _ = _ => reflexivity end.
        - eassumption.
        - eassumption.
        - reflexivity.
        - assumption.
        - eassumption.
        Unshelve.
        eexists; eauto.
      }
      { (* the case of spawn *)

        (* using the safety to prepare the precondition *)
        pose proof (safety i cnti tt) as safei.
        rewrite Eci in safei.
        fixsafe safei.
        inversion safei
          as [ | ????? bad | z c m0 e args0 x at_ex Pre SafePost | ???? bad ]; last contradiction.
        { rewrite level_jm_ in H; setoid_rewrite H in En; discriminate. }
        { inv bad. inv H3. rewrite Hinline in *; discriminate. }
        subst.
        simpl in at_ex. injection at_ex as <- <-.
        hnf in x.
        revert x Pre SafePost.

        (* dependent spawn *)
        funspec_destruct "acquire".
        funspec_destruct "release".
        funspec_destruct "makelock".
        funspec_destruct "freelock".
        funspec_destruct "spawn".

        (* disregarding the case of makelock by hypothesis *)
        exfalso; apply not_spawn.
        repeat eexists; eauto.
        simpl.
        simpl in H_spawn.
        f_equal.
        f_equal.
        injection H_spawn. intros <- E.
        apply ext_link_inj in E.
        subst name.
        reflexivity.
      }
    }
    (* end of Kblocked *)

    (* thread[i] is in Kresume *)
    {
      (* goes to Krun ci' with after_ex ci = ci'  *)
      specialize (wellformed i cnti).
      rewrite Eci in wellformed.
      destruct wellformed as [H ?]; subst.
      destruct ci as [ | f | ] eqn: Hci; try contradiction; simpl in H.
      destruct f; try contradiction.
      destruct (ef_inline e) eqn: Hinline; try contradiction.
      eexists; constructor.
      apply @JuicyMachine.resume_step with (tid := i) (Htid := cnti).
      { reflexivity. }
      eapply JuicyMachine.ResumeThread with (Hcmpt := mem_compatible_forget compat)(c := ci);
        simpl in *; try rewrite Clight_evsem.CLC_msem in *; simpl.
      -- reflexivity.
      -- rewrite Hci; simpl.
         rewrite Hinline; reflexivity.
      -- rewrite Hci; simpl; reflexivity.
      -- setoid_rewrite Eci; rewrite Hci; reflexivity.
      -- constructor.
      -- reflexivity.
    }
    (* end of Kresume *)

    (* thread[i] is in Kinit *)
    {
      specialize (safety i cnti tt). rewrite Eci in safety.
      destruct safety as (q_new & Einit & safety).
      eexists(* ; split *).
      - constructor.
        apply JuicyMachine.start_step with (tid := i) (Htid := cnti).
        + reflexivity.
        + eapply JuicyMachine.StartThread with (c_new := q_new)(Hcmpt := mem_compatible_forget compat).
          * apply Eci.
          * reflexivity.
          * instantiate (1 := install_perm (mem_compatible_forget compat) cnti). (* weird that cl_initial_core lets threads start with arbitrary memory *)
            auto.
          * constructor.
          * reflexivity.
    }
    (* end of Kinit *)

    (* bad schedule *)
    {
      eexists.
      (* split. *)
      (* -  *)constructor.
        apply JuicyMachine.schedfail with i.
        + reflexivity.
        + simpl.
          unfold OrdinalPool.containsThread.
          now setoid_rewrite Ei; auto.
        + constructor.
        + eexists; eauto.
        + reflexivity.
    }

Qed. (* Theorem progress *)

End Progress.
