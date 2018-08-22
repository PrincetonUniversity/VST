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
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clightnew_coop.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.initial_world.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mem_lessdef.
Require Import VST.veric.age_to_resource_at.
Require Import VST.floyd.coqlib3.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.concurrency.common.permjoin.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.concurrency.juicy.semax_conc.
Require Import VST.concurrency.juicy.juicy_machine.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.semantics.
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
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.juicy.semax_progress.
Require Import VST.concurrency.juicy.semax_preservation.

Local Arguments getThreadR {_} {_} {_} _ _ _.
Local Arguments getThreadC {_} {_} {_} _ _ _.
Local Arguments personal_mem : clear implicits.
Local Arguments updThread {_} {_} {_} _ _ _ _ _.
Local Arguments updThreadR {_} {_} {_} _ _ _ _.
Local Arguments updThreadC {_} {_} {_} _ _ _ _.
Local Arguments juicyRestrict : clear implicits.

Set Bullet Behavior "Strict Subproofs".

Open Scope string_scope.

(* to make the proof faster, we avoid unfolding of those definitions *)
Definition Jspec'_juicy_mem_equiv_def CS ext_link :=
  ext_spec_stable juicy_mem_equiv (JE_spec _ ( @OK_spec (Concurrent_Espec unit CS ext_link))).

Definition Jspec'_hered_def CS ext_link :=
   ext_spec_stable age (JE_spec _ ( @OK_spec (Concurrent_Espec unit CS ext_link))).

Lemma safety_induction_release ge Gamma n state
  (CS : compspecs)
  (ext_link : string -> ident)
  (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2)
  (Jspec' := @OK_spec (Concurrent_Espec unit CS ext_link))
  (Jspec'_juicy_mem_equiv : Jspec'_juicy_mem_equiv_def CS ext_link)
  (Jspec'_hered : Jspec'_hered_def CS ext_link)
  (personal_mem_equiv_spec :
     forall (m m' : Mem.mem') (phi : rmap) (pr : mem_cohere' m phi) (pr' : mem_cohere' m' phi),
       Mem.nextblock m = Mem.nextblock m' ->
       (forall loc : address, max_access_at m loc = max_access_at m' loc) ->
       (forall loc : AV.address, isVAL (phi @ loc) -> contents_at m loc = contents_at m' loc) ->
       mem_equiv (m_dry (personal_mem m phi pr)) (m_dry (personal_mem m' phi pr'))) :
  blocked_at_external state UNLOCK ->
  state_invariant Jspec' Gamma (S n) state ->
  exists state',
    state_step(ge := ge) state state' /\
    (state_invariant Jspec' Gamma n state' \/
     state_invariant Jspec' Gamma (S n) state').
Proof.
  intros isrelease.
  intros I.
  inversion I as [m tr sch_ tp Phi En envcoh compat extcompat sparse lock_coh safety wellformed unique E]. rewrite <-E in *.
  unfold blocked_at_external in *.
  destruct isrelease as (i & cnti & sch & ci & args & -> & Eci & atex).
  pose proof (safety i cnti tt) as safei.

  rewrite Eci in safei.

  fixsafe safei.
  inversion safei
    as [ | ?????? bad | n0 z c m0 e args0 x at_ex Pre SafePost | ????? bad ];
    [ now erewrite cl_corestep_not_at_external in atex; [ discriminate | eapply bad ]
    | subst | now inversion bad ].
  subst.
  simpl in at_ex. assert (args0 = args) by congruence; subst args0.
  assert (e = UNLOCK) by congruence; subst e.
  hnf in x.
  revert x Pre SafePost.

  assert (~ blocked_at_external (m, (tr, i :: sch, tp)) CREATE) as Hnot_create.
  { unfold blocked_at_external; intros (? & cnti' & ? & ? & ? & Heq & Hc & HC); inv Heq.
    assert (cnti' = cnti) by apply proof_irr; subst.
    rewrite Hc in Eci; inv Eci.
    rewrite HC in atex; inv atex. }

  assert (H_release : Some (ext_link "release", ef_sig UNLOCK) = ef_id_sig ext_link UNLOCK). reflexivity.

  (* dependent destruction *)
  funspec_destruct "acquire".
  funspec_destruct "release".

  intros (phix, (ts, ((vx, shx), Rx))) (Hargsty, Pre).
  simpl (projT2 _) in *; simpl (fst _) in *; simpl (snd _) in *; clear ts.
  destruct Pre as (phi0 & phi1 & j & Pre & HnecR).
  rewrite m_phi_jm_ in j.
  simpl (and _).
  intros Post.
  unfold release_pre in Pre.
  destruct Pre as ((Hreadable & PreA2) & ([PreB1 _] & PreB2) & PreC).
  change (Logic.True) in PreA2. clear PreA2.
  change (Logic.True) in PreB2. clear PreB2.
  unfold canon.SEPx in PreC.
  unfold base.fold_right_sepcon in *.
  rewrite seplog.sepcon_emp in PreC.
  rewrite seplog.corable_andp_sepcon1 in PreC; swap 1 2.
  { apply corable_weak_exclusive. }
  rewrite seplog.sepcon_comm in PreC.
  rewrite seplog.sepcon_emp in PreC.
  destruct PreC as (Hexclusive, PreC).
  destruct PreC as (phi0' & phi0d & jphi0 & Hlockinv & Hsat).
  rewrite lockinv_isptr in Hlockinv.
  destruct Hlockinv as (IsPtr, Hlockinv).
  destruct vx as [ | | | | | b ofs ]; try inversion IsPtr; [ clear IsPtr ].

  (* use progress to get the parts that don't depend on choice of phi *)
  destruct (progress _ _ ext_link_inj _ _ _ _ Hnot_create I) as [? Hstep0].
  inv Hstep0.
  inv H4; try inversion HschedN; subst tid;
      try contradiction; jmstep_inv; getThread_inv; try congruence;
      inv H; simpl in Hat_external;
      rewrite atex in Hat_external; inv Hat_external.
  clear dependent d_phi; clear dependent phi'.

  inv PreB1.
  assert (Htid = cnti) by apply proof_irr; subst.

  assert (pack_res_inv R = pack_res_inv (approx (level phi0') Rx)) as HR.
  { destruct Hlockinv as (bl & ofsl & Heq & Hlockinv & _); inv Heq.
    specialize (Hlockinv (bl, Ptrofs.unsigned ofsl)); simpl in Hlockinv.
    rewrite if_true in Hlockinv by (split; auto; lkomega).
    destruct Hlockinv as [? Hlock].
    destruct (HJcanwrite 0) as [?sh [?rsh [? ?]]]; [lkomega|].
    rewrite Z.add_0_r in H0. unfold Ptrofs.unsigned in *.
    assert (join_sub phi0' (getThreadR i tp cnti)).
    apply join_sub_trans with phi0; eexists; eauto.
    apply (resource_at_join_sub _ _ (bl, Ptrofs.intval ofsl)) in H1. 
    change (ClightSemanticsForMachines.Clight_newSem ge) with (@JSem ge) in *.
    rewrite H0,Hlock in H1.
    clear - H1; destruct H1 as [? H1].
    change  (SomeP rmaps.Mpred
             (fun _ : list Type => approx (@level rmap ag_rmap phi0') Rx))
         with (pack_res_inv (approx (@level rmap ag_rmap phi0') Rx))
     in H1. 
     forget (pack_res_inv (approx (@level rmap ag_rmap phi0') Rx)) as Rz.
    inv H1; auto.
  }
  unfold lock_at_least in HJcanwrite.
  rewrite HR in HJcanwrite.
  destruct (join_assoc (join_comm jphi0) j) as [phi' [? Hrem_lock_res]].
  assert (level (getThreadR i tp cnti) = S n) as Hn.
  { pose proof (getThread_level _ _ cnti _ (juice_join compat)).
    setoid_rewrite En in H0; auto. }
  evar (tpx: jstate ge).
  eexists (m', (seq.cat tr _, sch, tpx)); split.

  { (* "progress" part of the proof *)
    constructor.

    eapply JuicyMachine.sync_step with (Htid := cnti); auto.
    eapply step_release with (d_phi := phi0d); eauto.
    -
      hnf. rewrite level_age_by.
      destruct (join_level _ _ _ jphi0) as [-> <-].
      assert (0 < level phi0d)%nat.
      { destruct (join_level _ _ _ Hrem_lock_res) as [->].
        setoid_rewrite Hn; omega. }
      split; [omega|].
      eapply pred_hereditary; eauto.
      apply age_by_1; omega.
    - subst tpx; reflexivity.
  }
  subst tpx.

  (* we move on to the preservation part *)
  rename phi0d into d_phi. rename b0 into b. rename ofs0 into ofs. rename En into lev.

  assert (compat'' :
            mem_compatible_with
              (updLockSet (updThread i tp cnti (Kresume c Vundef) phi') (b, Ptrofs.intval ofs) (Some d_phi))
              m' Phi). {
    constructor.
    - (* joining to global map: the acquired rmap move from
            lockset to threads's maps *)
      destruct compat as [J].
      clear -J lev His_locked Hrem_lock_res.
      rewrite join_all_joinlist in *.
      rewrite maps_updlock2.
      rewrite maps_remLockSet_updThread.
      rewrite maps_updthread.
      erewrite <-maps_getlock2 in J; eauto.
      simpl map.
      assert (pr:containsThread (remLockSet tp (b, Ptrofs.intval ofs)) i) by auto.
      rewrite (maps_getthread i _ pr) in J.
      rewrite gRemLockSetRes with (cnti0 := cnti) in J. clear pr.
      revert Hrem_lock_res J.
      generalize (getThreadR _ _ cnti) d_phi phi'.
      generalize (all_but i (maps (remLockSet tp (b, Ptrofs.intval ofs)))).
      cleanup.
      clear -lev.
      intros l c a b j h.
      eapply joinlist_merge; eassumption.

    - (* mem_cohere' *)
      pose proof juice_join compat as J.
      pose proof all_cohere compat as MC.
      clear safety lock_coh.
      eapply (mem_cohere'_store _ _ tp _ _ _ (Int.one) _ _ cnti Hcmpt).
      (* eapply mem_cohere'_store with *)
      (* (tp := tp) *)
      (*   (Hcmpt := Hcmpt) *)
      (*   (cnti := cnti) *)
      (*   (j := Int.one). *)
      + cleanup.
        setoid_rewrite His_locked. simpl. congruence.
      + eauto.
      + auto.
      + exists phi0'; split.
        * eapply join_sub_trans; [eexists; eauto|].
          eapply join_sub_trans; [eexists; eauto|].
          apply compatible_threadRes_sub; auto.
        * destruct Hlockinv as (? & ? & Heq & ?); inv Heq; eauto.

    - (* lockSet_Writable *)
      eapply lockSet_Writable_updLockSet_updThread; eauto.

    - (* juicyLocks_in_lockSet *)
      pose proof jloc_in_set compat as jl.
      intros loc (*sh1 sh1' pp z*) E.
      cleanup.
      (* apply juicyLocks_in_lockSet_age with (n := n) in jl. *)
      specialize (jl loc E).
      simpl.
      rewrite AMap_find_add.
      if_tac. reflexivity.
      apply jl.

    - (* lockSet_in_juicyLocks *)
      pose proof lset_in_juice compat as lj.
      intros loc; specialize (lj loc).
      simpl.
      rewrite AMap_find_add.
      if_tac; swap 1 2.
      + cleanup.
        intros is; specialize (lj is). auto.
      + intros _. subst loc.
        assert_specialize lj. {
          cleanup.
          setoid_rewrite His_locked.
          reflexivity.
        }
        auto.
  }

  pose proof mem_compatible_with_age _ compat'' (n := n) as compat'.

  replace (level (getThreadR i tp cnti) - 1)%nat with n by omega.
  assert (level (getThreadR i tp cnti) - 1 = n)%nat as El by omega.
  replace (level (getThreadR i tp cnti) - 1)%nat with n; left; apply state_invariant_c with (mcompat := compat').
  + (* level *)
    apply level_age_to. cleanup. omega.

  + (* env_coherence *)
    apply env_coherence_age_to. auto.

  + (* external coherence *)
    rewrite age_to_ghost_of.
    destruct extcompat as [? J]; eapply ghost_fmap_join in J; eexists; eauto.

  + (* lock sparsity *)
    simpl.
    cleanup.
    eapply sparsity_same_support with (lset tp); auto.
    apply lset_same_support_sym.
    eapply lset_same_support_trans.
    * apply lset_same_support_map.
    * apply lset_same_support_sym.
      apply same_support_change_lock.
      cleanup.
      setoid_rewrite His_locked. congruence.

  + (* lock coherence *)
    intros loc.
    simpl (AMap.find _ _).
    rewrite AMap_find_map_option_map.
    rewrite AMap_find_add.
    specialize (lock_coh loc).
    if_tac.

    * (* current lock is acquired: load is indeed 0 *)
      { subst loc.
        split; swap 1 2.
        - (* the rmap is unchanged (but we have to prove the SAT information) *)
          cut ((4 | snd (b, Ptrofs.intval ofs)) /\
               (snd (b, Ptrofs.intval ofs) + LKSIZE < Ptrofs.modulus)%Z /\
               exists (* sh0 *) R0,
                  (lkat R0 (* sh0 *) (b, Ptrofs.intval ofs)) Phi /\
                  (app_pred R0 (age_by 1 (age_to (level (getThreadR i tp cnti) - 1) d_phi))
                   \/ level (age_to n Phi) = 0%nat)
              ).
          { intros (align & bound & (* sh0 &  *)R0 & AP & sat).
            repeat (split; auto).
            exists (* sh0, *) R0; split.
            - revert AP. apply age_to_ind, lkat_hered.
            - cleanup. rewrite El in *. auto. }
          cleanup.
          unfold JSem in *; rewrite His_locked in lock_coh.
          destruct lock_coh as (Load & align & bound & (* sh0 &  *)R0 & lk).
          repeat (split; auto).
          exists (* sh0,  *)R0; split.
          + eauto.
          + left.
            rewrite El.
            apply predat6 in lk.
            specialize (HJcanwrite 0). spec HJcanwrite; [lkomega|].
            destruct HJcanwrite as [?[?[? HJcanwrite]]].
            apply predat1 in HJcanwrite.
            apply @predat_join_sub with (phi2 := Phi) in HJcanwrite.
            rewrite Z.add_0_r in HJcanwrite.
            2:apply compatible_threadRes_sub, compat.
            pose proof predat_inj HJcanwrite lk as ER.
            replace (level (getThreadR i tp cnti)) with (level Phi) in ER.
            2:symmetry; apply join_sub_level, compatible_threadRes_sub, compat.
            cleanup.
            refine (@approx_eq_app_pred (approx (level phi0') Rx) R0 (age_by 1 (age_to n d_phi)) _ _ ER _).
            * rewrite level_age_by.
              rewrite level_age_to. omega.
              replace (level d_phi) with (level Phi). omega.
              symmetry. apply join_sub_level.
              apply join_sub_trans with (getThreadR i tp cnti).
              -- exists phi'. apply join_comm. auto.
              -- apply compatible_threadRes_sub. apply compat.
            * destruct (join_level _ _ _ jphi0).
              destruct (join_level _ _ _ Hrem_lock_res).
              hnf. rewrite level_age_by, level_age_to by omega.
              split; [omega|].
              unfold age_to.
              rewrite age_by_age_by.
              revert Hsat; apply age_by_ind.
              destruct Rx; auto.

        - (* in dry : it is 1 *)
          unfold load_at.
          clear (* lock_coh *) Hload.

          Transparent Mem.load.
          unfold Mem.load. simpl fst; simpl snd.
          clear H. if_tac [H|H].
          + rewrite restrPermMap_mem_contents.
            apply Mem.load_store_same in Hstore.
            unfold Mem.load in Hstore.
            if_tac in Hstore; [ | discriminate ].
            apply Hstore.
          + exfalso.
            apply H; clear H.
            apply islock_valid_access.
            * apply Mem.load_store_same in Hstore.
              unfold Mem.load in Hstore.
              if_tac [[H H']|H] in Hstore; [ | discriminate ].
              apply H'.
            * rewrite LockRes_age_content1.
              rewrite gssLockRes. simpl. congruence.
            * congruence.
      }

    * (* not the current lock *)
      destruct (AMap.find (elt:=option rmap) loc (lset tp)) as [o|] eqn:Eo; swap 1 2.
      {
        simpl.
        clear -lock_coh.
        rewrite isLK_age_to(* , isCT_age_to *). auto.
      }
      set (u := load_at _ _).
      set (v := load_at _ _) in lock_coh.
      assert (L : forall val, v = Some val -> u = Some val); unfold u, v in *.
      (* ; clear u v. *)
      {
        intros val.
        unfold load_at in *.
        clear lock_coh.
        destruct loc as (b', ofs'). simpl fst in *; simpl snd in *.
        pose proof sparse (b, Ptrofs.intval ofs) (b', ofs') as SPA.
        assert_specialize SPA by (cleanup; unfold JSem in *; congruence).
        assert_specialize SPA by (cleanup; congruence).
        simpl in SPA.
        destruct SPA as [SPA|SPA]; [ tauto | ].
        unfold Mem.load in *.
        if_tac [V|V]; [ | congruence].
        if_tac [V'|V'].
        - do 2 rewrite restrPermMap_mem_contents.
          intros G; exact_eq G.
          f_equal.
          f_equal.
          f_equal.
          simpl.

          pose proof store_outside' _ _ _ _ _ _ Hstore as OUT.
          destruct OUT as (OUT, _).
          cut (forall z,
                  (0 <= z < 4)%Z ->
                  ZMap.get (ofs' + z)%Z (Mem.mem_contents m) !! b' =
                  ZMap.get (ofs' + z)%Z (Mem.mem_contents m') !! b').
          {
            intros G.
            repeat rewrite <- Z.add_assoc.
            f_equal.
            - specialize (G 0%Z ltac:(omega)).
              exact_eq G. repeat f_equal; auto with zarith.
            - f_equal; [apply G; omega | ].
              f_equal; [apply G; omega | ].
              f_equal; apply G; omega.
          }
          intros z Iz.
          specialize (OUT b' (ofs' + z)%Z).

          destruct OUT as [[-> OUT]|OUT]; [ | clear SPA].
          + exfalso.
            destruct SPA as [? | [_ SPA]]; [ tauto | ].
            eapply far_range in SPA. apply SPA; clear SPA.
            instantiate (1 := z). now lkomega.
            lkomega.
          + unfold contents_at in *.
            simpl in OUT.
            apply OUT.

        - exfalso.
          apply V'; clear V'.
          unfold Mem.valid_access in *.
          split. 2:apply V. destruct V as [V _].
          unfold Mem.range_perm in *.
          intros ofs0 int0; specialize (V ofs0 int0).
          unfold Mem.perm in *.
          pose proof restrPermMap_Cur as RR.
          unfold permission_at in *.
          rewrite RR in *.
          rewrite lockSet_age_to.
          setoid_rewrite <-lockSet_updLockSet.
          match goal with |- _ ?a _ => cut (a = Some Writable) end.
          { intros ->. constructor. }

          destruct SPA as [bOUT | [<- ofsOUT]].
          + rewrite OrdinalPool.gsoLockSet_2; auto.
            apply OrdinalPool.lockSet_spec_2 with ofs'.
            * hnf; simpl. eauto. clear -int0; simpl in *.
              unfold LKSIZE_nat; rewrite Z2Nat.id; lkomega.
            * cleanup. rewrite Eo. reflexivity.
          + rewrite OrdinalPool.gsoLockSet_1; auto.
            * apply OrdinalPool.lockSet_spec_2 with ofs'.
              -- hnf; simpl. eauto.  clear -int0; simpl in *.
                 unfold LKSIZE_nat; rewrite Z2Nat.id; lkomega.
              -- cleanup. rewrite Eo. reflexivity.
            * unfold far in *.
              simpl in *.
              zify.
              unfold LKSIZE_nat; rewrite Z2Nat.id; lkomega.
      }
      destruct o; destruct lock_coh as (Load (* & sh' *) & align & bound & R' & lks); split.
      -- now intuition.
      -- repeat (split; auto).
         exists (* sh',  *)R'.
         destruct lks as (lk, sat); split.
         ++ revert lk. apply age_to_ind, lkat_hered.
         ++ destruct sat as [sat|sat].
            ** left; revert sat.
               unfold age_to in *.
               rewrite age_by_age_by.
               apply age_by_age_by_pred.
               omega.
            ** congruence.
      -- now intuition.
      -- repeat (split; auto).
         exists (* sh', *) R'.
         revert lks.
         apply age_to_ind, lkat_hered.

  + (* safety *)
    rename j into Hj. intros j lj ora.
    specialize (safety j lj ora).
    unshelve erewrite <-gtc_age. auto.
    unshelve erewrite gLockSetCode; auto.
    destruct (eq_dec i j).
    * {
        (* use the "well formed" property to derive that this is
              an external call, and derive safety from this.  But the
              level has to be decreased, here. *)
        subst j.
        rewrite gssThreadCode.
        replace lj with cnti in safety by apply proof_irr.
        rewrite Eci in safety.
        specialize (wellformed i cnti).
        rewrite Eci in wellformed.
        intros c' Ec' jm' Ejm'.
        - (* at_external : we can now use safety *)
          destruct Post with
          (ret := @None val)
            (m' := jm')
            (z' := ora) (n' := n) as (c'' & Ec'' & Safe').

          + auto.

          + simpl.
            apply Logic.I.

          + auto.

          + (* proving Hrel *)
            assert (n = level jm'). {
              rewrite <-level_m_phi.
              rewrite Ejm'.
              REWR.
              REWR.
              REWR.
              rewrite level_age_to; auto.
              replace (level phi') with (level Phi). omega.
              transitivity (level (getThreadR i tp cnti)); join_level_tac.
            }
            assert (level phi' = S n). {
              cleanup. replace (level phi') with (S n). omega. join_level_tac.
            }

            split; [ | split].
            * auto.
            * rewr (level jm'). rewrite level_jm_. cleanup. omega.
            * simpl. rewrite Ejm'. do 3 REWR.
              eapply pures_same_eq_l.
              2:apply pures_eq_age_to; omega.
              apply pures_same_trans with phi1.
              -- apply pures_same_sym. apply join_sub_pures_same. exists phi0'. apply join_comm. assumption.
              -- apply join_sub_pures_same. exists phi0. apply join_comm. assumption.

          + (* we must satisfy the post condition *)
            rewrite Ejm'.
            (* rewrite m_phi_jm_. *)
            exists (age_to n phi0'), (age_to n phi1).
            split.
            * REWR.
              apply age_to_join.
              REWR.
              REWR.
            * split. 2: now eapply necR_trans; [ eassumption | apply age_to_necR ].
              split. now constructor.
              split. now constructor.
              unfold canon.SEPx.
              simpl. rewrite seplog.sepcon_emp.
              apply age_to_pred; auto.
          + exact_eq Safe'.
            unfold jsafeN.
            f_equal.
            congruence.
      }
    * repeat REWR.
      destruct (getThreadC j tp lj) eqn:Ej.
      -- edestruct (unique_Krun_neq(ge := ge) i j); eauto.
      -- apply jsafe_phi_age_to; auto. apply jsafe_phi_downward. assumption.
      -- intros c' Ec'; specialize (safety c' Ec'). apply jsafe_phi_bupd_age_to; auto. apply jsafe_phi_bupd_downward. assumption.
      -- destruct safety as (? & q_new & Einit & safety).
         split; [erewrite Mem.nextblock_store by eauto; auto|].
         exists q_new; split; auto.
         apply jsafe_phi_age_to; auto. apply jsafe_phi_downward, safety.

  + (* well_formedness *)
    rename j into Hj. intros j lj.
    specialize (wellformed j lj).
    unshelve erewrite <-gtc_age. auto.
    unshelve erewrite gLockSetCode; auto.
    destruct (eq_dec i j).
    * subst j.
      rewrite gssThreadCode.
      replace lj with cnti in wellformed by apply proof_irr.
      unfold JSem in *; rewrite Hthread in wellformed.
      auto.
    * unshelve erewrite gsoThreadCode; auto.

  + (* uniqueness *)
    apply no_Krun_unique_Krun.
    rewrite no_Krun_age_tp_to.
    apply no_Krun_updLockSet.
    apply no_Krun_stable. congruence.
    eapply unique_Krun_no_Krun. eassumption.
    instantiate (1 := cnti). unfold JSem; rewrite Hthread.
    congruence.
Qed.
