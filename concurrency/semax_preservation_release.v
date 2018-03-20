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
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mem_lessdef.
Require Import VST.veric.age_to_resource_at.
Require Import VST.floyd.coqlib3.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.concurrency.coqlib5.
Require Import VST.concurrency.permjoin.
Require Import VST.concurrency.semax_conc_pred.
Require Import VST.concurrency.semax_conc.
Require Import VST.concurrency.juicy_machine.
Require Import VST.concurrency.concurrent_machine.
Require Import VST.concurrency.semantics.
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.addressFiniteMap.
Require Import VST.concurrency.permissions.
Require Import VST.concurrency.JuicyMachineModule.
Require Import VST.concurrency.sync_preds_defs.
Require Import VST.concurrency.sync_preds.
Require Import VST.concurrency.join_lemmas.
Require Import VST.concurrency.cl_step_lemmas.
Require Import VST.concurrency.resource_decay_lemmas.
Require Import VST.concurrency.resource_decay_join.
Require Import VST.concurrency.semax_invariant.
Require Import VST.concurrency.semax_simlemmas.
Require Import VST.concurrency.sync_preds.
Require Import VST.concurrency.lksize.

Local Arguments getThreadR : clear implicits.
Local Arguments getThreadC : clear implicits.
Local Arguments personal_mem : clear implicits.
Local Arguments updThread : clear implicits.
Local Arguments updThreadR : clear implicits.
Local Arguments updThreadC : clear implicits.
Local Arguments juicyRestrict : clear implicits.

Set Bullet Behavior "Strict Subproofs".

Open Scope string_scope.

Definition at_external_SEM_eq := ClightSemantincsForMachines.ClightSEM.at_external_SEM_eq.

(* to make the proof faster, we avoid unfolding of those definitions *)
Definition Jspec'_juicy_mem_equiv_def CS ext_link :=
  ext_spec_stable juicy_mem_equiv (JE_spec _ ( @OK_spec (Concurrent_Espec unit CS ext_link))).

Definition Jspec'_hered_def CS ext_link :=
   ext_spec_stable age (JE_spec _ ( @OK_spec (Concurrent_Espec unit CS ext_link))).

Lemma preservation_release
  (lockSet_Writable_updLockSet_updThread
     : forall (m m' : Memory.mem) (i : tid) (tp : thread_pool),
       forall (cnti : containsThread tp i) (b : block) (ofs : int) (ophi : option rmap)
         (ophi' : LocksAndResources.lock_info) (c' : ctl) (phi' : LocksAndResources.res)
         (z : int) (Hcmpt : mem_compatible tp m)
         (Hcmpt : mem_compatible tp m)
         (His_unlocked : AMap.find (elt:=option rmap) (b, Int.intval ofs) (lset tp) = Some ophi)
         (Hlt' : permMapLt
              (setPermBlock (Some Writable) b (Int.intval ofs) (juice2Perm_locks (getThreadR i tp cnti) m)
                 LKSIZE_nat) (getMaxPerm m))
         (Hstore : Mem.store Mint32 (restrPermMap Hlt') b (Int.intval ofs) (Vint z) = Some m'),
       lockSet_Writable (lset (updLockSet (updThread i tp cnti c' phi') (b, Int.intval ofs) ophi')) m')
  (mem_cohere'_store : forall m tp m' b ofs j i Phi (cnti : containsThread tp i)
    (Hcmpt : mem_compatible tp m)
    (lock : lockRes tp (b, Int.intval ofs) <> None)
    (Hlt' : permMapLt
           (setPermBlock (Some Writable) b (Int.intval ofs) (juice2Perm_locks (getThreadR i tp cnti) m)
              LKSIZE_nat) (getMaxPerm m))
    (Hstore : Mem.store Mint32 (restrPermMap Hlt') b (Int.intval ofs) (Vint j) = Some m'),
    mem_compatible_with tp m Phi ->
    mem_cohere' m' Phi)
  (personal_mem_equiv_spec
     : forall (m m' : Mem.mem') (phi : rmap) (pr : mem_cohere' m phi) (pr' : mem_cohere' m' phi),
       Mem.nextblock m = Mem.nextblock m' ->
       (forall loc : address, max_access_at m loc = max_access_at m' loc) ->
       (forall loc : AV.address, isVAL (phi @ loc) -> contents_at m loc = contents_at m' loc) ->
       mem_equiv (m_dry (personal_mem m phi pr)) (m_dry (personal_mem m' phi pr')))
  (CS : compspecs)
  (ext_link : string -> ident)
  (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2)
  (Jspec' := @OK_spec (Concurrent_Espec unit CS ext_link))
  (Jspec'_juicy_mem_equiv : Jspec'_juicy_mem_equiv_def CS ext_link)
  (Jspec'_hered : Jspec'_hered_def CS ext_link)
  (Gamma : funspecs)
  (n : nat)
  (ge : SEM.G)
  (m m' : Memory.mem)
  (i : tid)
  (sch : list tid)
  (tp : thread_pool)
  (INV : state_invariant Jspec' Gamma (S n) (m, ge, (i :: sch, tp)))
  (Phi : rmap)
  (compat : mem_compatible_with tp m Phi)
  (lev : level Phi = S n)
  (envcoh : env_coherence Jspec' ge Gamma Phi)
  (sparse : lock_sparsity (lset tp))
  (lock_coh : lock_coherence' tp Phi m compat)
  (safety : threads_safety Jspec' m ge tp Phi compat (S n))
  (wellformed : threads_wellformed ge m tp)
  (unique : unique_Krun tp (i :: sch))
  (cnti : containsThread tp i)
  (ci : code)
  (Eci : getThreadC i tp cnti = Kblocked ci)
  (Hcmpt : mem_compatible tp m)
  (El : Logic.True -> level (getThreadR i tp cnti) - 1 = n)
  (compat_aged : mem_compatible_with (age_tp_to n tp) m (age_to n Phi))
  (c : code)
  (b : block)
  (ofs : int)
  (d_phi : rmap)
  (R : pred rmap)
  (phi' : rmap)
  (sh : Share.t)
  (rsh : shares.readable_share sh)
  (Hthread : getThreadC i tp cnti = Kblocked c)
  (Hat_external : at_external SEM.Sem ge c m = Some (UNLOCK(* , ef_sig UNLOCK *), Vptr b ofs :: nil))
  (His_locked : lockRes tp (b, Int.intval ofs) = SNone)
  (Hsat_lock_inv : R (age_by 1 d_phi))
  (Hload : Mem.load Mint32 (juicyRestrict_locks (mem_compat_thread_max_cohere Hcmpt cnti))
                    b (Int.intval ofs) = Some (Vint Int.zero))
  (Hlt' : permMapLt
           (setPermBlock (Some Writable) b (Int.intval ofs) (juice2Perm_locks (getThreadR i tp cnti) m)
              LKSIZE_nat) (getMaxPerm m))
  (Hstore : Mem.store Mint32 (restrPermMap Hlt') b (Int.intval ofs) (Vint Int.one) = Some m')
  (* (Hstore : Mem.store Mint32 (juicyRestrict_locks (mem_compat_thread_max_cohere Hcmpt cnti)) *)
  (*                     b (Int.intval ofs) (Vint Int.one) = Some m') *)
  (HJcanwrite : getThreadR i tp cnti @ (b, Int.intval ofs) = YES sh rsh (LK LKSIZE) (pack_res_inv R))
  (Hrem_lock_res : join d_phi phi' (getThreadR i tp cnti))
  (jmstep : @JuicyMachine.machine_step ge (i :: sch) nil tp m sch nil
             (age_tp_to n
                (updLockSet (updThread i tp cnti (Kresume c Vundef) phi') (b, Int.intval ofs) (Some d_phi))) m')
  (Htstep : syncStep true ge cnti Hcmpt
             (age_tp_to n
                (updLockSet (updThread i tp cnti (Kresume c Vundef) phi') (b, Int.intval ofs) (Some d_phi))) m'
             (Events.release (b, Int.intval ofs) None)) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m', ge, (sch, age_tp_to n
           (updLockSet (updThread i tp cnti (Kresume c Vundef) phi') (b, Int.intval ofs) (Some d_phi)))).

Proof.
  autospec El.
  cleanup.

  assert (compat'' :
            mem_compatible_with
              (updLockSet (updThread i tp cnti (Kresume c Vundef) phi') (b, Int.intval ofs) (Some d_phi))
              m' Phi). {
    cleanup.
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
      assert (pr:containsThread (remLockSet tp (b, Int.intval ofs)) i) by auto.
      rewrite (maps_getthread i _ pr) in J.
      rewrite gRemLockSetRes with (cnti0 := cnti) in J. clear pr.
      revert Hrem_lock_res J.
      generalize (@getThreadR _ _ cnti) d_phi phi'.
      generalize (all_but i (maps (remLockSet tp (b, Int.intval ofs)))).
      cleanup.
      clear -lev.
      intros l c a b j h.
      eapply joinlist_merge; eassumption.

    - (* mem_cohere' *)
      pose proof juice_join compat as J.
      pose proof all_cohere compat as MC.
      clear safety lock_coh jmstep.
      eapply (mem_cohere'_store _ tp _ _ _ (Int.one) _ _ cnti Hcmpt).
      (* eapply mem_cohere'_store with *)
      (* (tp := tp) *)
      (*   (Hcmpt := Hcmpt) *)
      (*   (cnti := cnti) *)
      (*   (j := Int.one). *)
      + cleanup.
        rewrite His_locked. simpl. congruence.
      + eauto.
      + auto.

    - (* lockSet_Writable *)
      eapply lockSet_Writable_updLockSet_updThread; eauto.

    - (* juicyLocks_in_lockSet *)
      pose proof jloc_in_set compat as jl.
      intros loc sh1 sh1' pp z E.
      cleanup.
      (* apply juicyLocks_in_lockSet_age with (n := n) in jl. *)
      specialize (jl loc sh1 sh1' pp z E).
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
        intros is; specialize (lj is).
        destruct lj as (sh' & psh' & P & E).
        rewrite E. simpl. eauto.
      + intros _. subst loc.
        assert_specialize lj. {
          cleanup.
          rewrite His_locked.
          reflexivity.
        }
        destruct lj as (sh' & psh' & P & E).
        rewrite E. simpl. eauto.
  }

  pose proof mem_compatible_with_age compat'' (n := n) as compat'.

  apply state_invariant_c with (mcompat := compat').
  + (* level *)
    apply level_age_to. cleanup. omega.

  + (* env_coherence *)
    apply env_coherence_age_to. auto.

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
      rewrite His_locked. congruence.

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
          cut ((4 | snd (b, Int.intval ofs)) /\
               (snd (b, Int.intval ofs) + LKSIZE <= Int.modulus)%Z /\
               exists (* sh0 *) R0,
                  (lkat R0 (* sh0 *) (b, Int.intval ofs)) Phi /\
                  (app_pred R0 (age_by 1 (age_to (level (getThreadR i tp cnti) - 1) d_phi))
                   \/ level (age_to n Phi) = 0)
              ).
          { intros (align & bound & (* sh0 &  *)R0 & AP & sat).
            repeat (split; auto).
            exists (* sh0, *) R0; split.
            - revert AP. apply age_to_ind, lkat_hered.
            - cleanup. rewrite El in *. auto. }
          cleanup.
          rewrite His_locked in lock_coh.
          destruct lock_coh as (Load & align & bound & (* sh0 &  *)R0 & lk).
          repeat (split; auto).
          exists (* sh0,  *)R0; split.
          + eauto.
          + left.
            rewrite El.
            apply predat6 in lk.
            apply predat1 in HJcanwrite.
            apply @predat_join_sub with (phi2 := Phi) in HJcanwrite.
            2:apply compatible_threadRes_sub, compat.
            pose proof predat_inj HJcanwrite lk as ER.
            replace (level (getThreadR i tp cnti)) with (level Phi) in ER.
            2:symmetry; apply join_sub_level, compatible_threadRes_sub, compat.
            cleanup.
            refine (@approx_eq_app_pred R R0 (age_by 1 (age_to n d_phi)) _ _ ER _).
            * rewrite level_age_by.
              rewrite level_age_to. omega.
              replace (level d_phi) with (level Phi). omega.
              symmetry. apply join_sub_level.
              apply join_sub_trans with (getThreadR i tp cnti).
              -- exists phi'. apply join_comm. auto.
              -- apply compatible_threadRes_sub. apply compat.
            * revert Hsat_lock_inv.
              unfold age_to.
              rewrite age_by_age_by.
              rewrite plus_comm.
              rewrite <-age_by_age_by.
              apply age_by_ind.
              destruct R; auto.

        - (* in dry : it is 1 *)
          unfold load_at.
          clear (* lock_coh *) Htstep Hload.

          Transparent Mem.load.
          unfold Mem.load. simpl fst; simpl snd.
          if_tac [H|H].
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
              rewrite JTP.gssLockRes. simpl. congruence.
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
        pose proof sparse (b, Int.intval ofs) (b', ofs') as SPA.
        assert_specialize SPA by (cleanup; congruence).
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
          rewrite <-lockSet_updLockSet.
          match goal with |- _ ?a _ => cut (a = Some Writable) end.
          { intros ->. constructor. }

          destruct SPA as [bOUT | [<- ofsOUT]].
          + rewrite gsoLockSet_2; auto.
            apply lockSet_spec_2 with ofs'.
            * hnf; simpl. eauto. clear -int0; simpl in *; omega.
            * cleanup. rewrite Eo. reflexivity.
          + rewrite gsoLockSet_1; auto.
            * apply lockSet_spec_2 with ofs'.
              -- hnf; simpl. eauto.  clear -int0; simpl in *; omega.
              -- cleanup. rewrite Eo. reflexivity.
            * unfold far in *.
              simpl in *.
              zify.
              lkomega.
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
    intros j lj ora.
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
        rewrite Hthread in safety.
        specialize (wellformed i cnti).
        rewrite Hthread in wellformed.
        intros c' Ec'.
        eapply jsafe_phi_jsafeN with (compat0 := compat) in safety.

        inversion safety as [ | ?????? step | ??????? ae Pre Post Safe | ????? Ha]; swap 2 3.
        - (* not corestep *)
          exfalso.
          clear -Hat_external step.
          apply corestep_not_at_external in step.
          rewrite jstep.JuicyFSem.t_obligation_3 in step.
          set (u := at_external _ _ _ _) in Hat_external.
          set (v := at_external _ _ _ _) in step.
          assert (u = v).
          { unfold u, v. rewrite at_external_SEM_eq. reflexivity. }
          congruence.

        - (* not halted *)
          exfalso.
          clear -Hat_external Ha.
          assert (Ae : at_external SEM.Sem ge c m <> None). congruence.
          eapply at_external_not_halted in Ae.
          unfold juicy_core_sem in *.
          unfold cl_core_sem in *.
          simpl in *.
          unfold SEM.Sem in *.
          rewrite SEM.CLN_msem in *.
          simpl in *.
          congruence.

        - (* at_external : we can now use safety *)
          subst z c0 m0.
          intros jm' Ejm'.
          destruct Post with
          (ret := @None val)
            (m' := jm')
            (z' := ora) (n' := n) as (c'' & Ec'' & Safe').

          + assert (e = UNLOCK).
            { rewrite <-Ejuicy_sem in *.
              unfold juicy_sem in *.
              simpl in ae.
              clear - ae Hat_external. rewrite at_external_SEM_eq in Hat_external.
              unfold j_at_external in ae. rewrite at_external_SEM_eq in ae.
              congruence. }
            assert (args = Vptr b ofs :: nil).
            { rewrite <-Ejuicy_sem in *.
              unfold juicy_sem in *.
              simpl in ae.
              clear - ae Hat_external. rewrite at_external_SEM_eq in Hat_external.
              unfold j_at_external in ae. rewrite at_external_SEM_eq in ae.
              congruence. }
            subst e args; simpl.
            auto.

          + assert (e = UNLOCK).
            { rewrite <-Ejuicy_sem in *.
              unfold juicy_sem in *.
              simpl in ae.
              clear - ae Hat_external. rewrite at_external_SEM_eq in Hat_external.
              unfold j_at_external in ae. rewrite at_external_SEM_eq in ae.
              congruence. }
            subst e.
            apply Logic.I.

          + auto.

          + (* proving Hrel *)
            hnf.
            assert (n = level jm'). {
              rewrite <-level_m_phi.
              rewrite Ejm'.
              REWR.
              REWR.
              REWR.
              rewrite level_age_to; auto.
              replace (level phi') with (level Phi). omega.
              transitivity (level (getThreadR i tp cnti)); join_level_tac.
              rewrite getThread_level with (Phi := Phi). auto. apply compat.
            }
            assert (level phi' = S n). {
              cleanup. replace (level phi') with (S n). omega. join_level_tac.
              transitivity (level (getThreadR i tp cnti)); join_level_tac.
              rewrite getThread_level with (Phi := Phi). auto. apply compat.
            }

            split; [ | split].
            * auto.
            * rewr (level jm'). rewrite level_jm_. cleanup. omega.
            * simpl. rewrite Ejm'. do 3 REWR.
              eapply pures_same_eq_l.
              2:apply pures_eq_age_to; omega.
              apply join_sub_pures_same.
              eexists. eapply join_comm. eassumption.

          + (* we must satisfy the post condition *)
            assert (e = UNLOCK).
            { rewrite <-Ejuicy_sem in *.
              unfold juicy_sem in *.
              simpl in ae.
              clear - ae Hat_external. rewrite at_external_SEM_eq in Hat_external.
              unfold j_at_external in ae. rewrite at_external_SEM_eq in ae.
              congruence. }
            subst e.
            revert x Pre Post.
            funspec_destruct "acquire".
            { exfalso. unfold ef_id_sig in *. injection Heq_name as E.
              apply ext_link_inj in E. congruence. }
            funspec_destruct "release"; swap 1 2.
            { exfalso. unfold ef_id_sig in *.
              unfold funsig2signature in *. simpl in *; congruence. }
            intros x Pre Post.
            destruct Pre as (Hargsty & phi0 & phi1 & j & Pre).
            rewrite m_phi_jm_ in j.
            destruct x as (phix, (ts, ((vx, shx), Rx)));
              simpl (fst _) in *; simpl (snd _) in *; simpl (projT2 _) in *;
                clear ts.
            unfold release_pre in Pre.
            destruct Pre as [((Hreadable & PreA2) & (PreB1 & PreB2) & PreC) necr].
            change (Logic.True) in PreA2. clear PreA2.
            change (Logic.True) in PreB2. clear PreB2.
            unfold canon.SEPx in PreC.
            unfold base.fold_right_sepcon in *.
            rewrite seplog.sepcon_emp in PreC.
            rewrite seplog.corable_andp_sepcon1 in PreC; swap 1 2.
            { apply seplog.corable_andp.
              apply corable_weak_precise.
              apply corable_weak_positive. }
            rewrite seplog.sepcon_comm in PreC.
            rewrite seplog.sepcon_emp in PreC.
            destruct PreC as ((Hprecise & Hpositive), PreC).
            destruct PreC as (phi0' & phi0d & jphi0 & Hlockinv & Hsat).

            assert (args = Vptr b ofs :: nil). {
              revert Hat_external ae; clear.
              unfold SEM.Sem in *.
              rewrite SEM.CLN_msem. simpl.
                   intros. unfold cl_at_external in *.
              congruence.
            }
            subst args.
            assert (vx = Vptr b ofs). {
              hnf in PreB1. subst vx. clear.
              unfold expr.eval_id in *.
              unfold expr.force_val in *.
              unfold make_ext_args in *.
              unfold te_of in *.
              unfold filter_genv in *.
              unfold Genv.find_symbol in *.
              unfold expr.env_set in *.
              rewrite Map.gss.
              auto.
            }
            subst vx.

            assert (join_sub (getThreadR i tp cnti) Phi) by apply compatible_threadRes_sub, compat.

            assert (Edphi : age_to n phi0d = age_to n d_phi). {
              apply predat4 in Hlockinv.

              assert (join_sub phi0' (getThreadR i tp cnti)). {
                apply join_sub_trans with phi0.
                - eexists; eapply join_comm; eauto.
                - eexists; eapply join_comm; eauto.
              }
              apply @predat_join_sub with (phi2 := Phi) in Hlockinv; swap 1 2. {
                apply join_sub_trans with (getThreadR i tp cnti); auto.
              }
              replace (level phi0') with (level Phi) in Hlockinv by join_level_tac.
              rename R into RRRRRRRRRRR.
              rename Rx into RRRRRRRRRRRx.
              apply predat1 in HJcanwrite.
              replace (level (getThreadR i tp cnti)) with (level Phi) in HJcanwrite by join_level_tac.
              apply @predat_join_sub with (phi2 := Phi) in HJcanwrite; [ | now auto].                    unfold Int.unsigned in *.
              pose proof predat_inj Hlockinv HJcanwrite as ER.
              (* apply precise_approx with (n := S n) in Precise. *)
              apply Hprecise with (age_to n (getThreadR i tp cnti)).
              - split.
                + rewrite level_age_to. replace (level phi0) with (S n). omega.
                  replace (level phi0) with (level Phi) by join_level_tac. omega.
                  replace (level phi0d) with (level Phi) by join_level_tac. omega.
                + revert Hsat.
                  apply pred_hered.
                  apply age_to_1.
                  exact_eq lev. f_equal. join_level_tac.
              - split.
                + rewrite level_age_to. replace (level phi0) with (S n). omega.
                  replace (level phi0) with (level Phi) by join_level_tac. omega.
                  replace (level d_phi) with (level Phi) by join_level_tac.
                  rewrite lev; auto with *.
                + cut (app_pred (approx (level Phi) RRRRRRRRRRRx) (age_to n d_phi)).
                  * intros []. auto.
                  * rewrite ER. split.
                    -- rewrite level_age_to. rewrite lev; auto with *.
                       replace (level d_phi) with (level Phi) by join_level_tac.
                       rewrite lev; auto with *.
                    -- exact_eq Hsat_lock_inv. change (age1' d_phi) with (age_by 1 d_phi). f_equal. unfold age_to; f_equal.
                       replace (level d_phi) with (level Phi) by join_level_tac.
                       omega.
              - apply age_to_join_sub.
                apply join_sub_trans with phi0.
                + exists phi0'. apply join_comm; auto.
                + exists phi1. apply join_comm; auto.
              - apply age_to_join_sub.
                exists phi'. auto.
            }
            pose proof (age_to_join n _ _ _ j) as j'.
            pose proof (age_to_join n _ _ _ jphi0) as jphi0'.
            rewrite Edphi in jphi0'.
            destruct (join_assoc (join_comm jphi0') j') as (phi'_ & small & big).
            assert (phi'_ = age_to n phi'). {
              apply age_to_join with (k := n) in Hrem_lock_res.
              pose proof join_canc (join_comm Hrem_lock_res) (join_comm big).
              auto.
            }
            subst phi'_.

            (* destruct (join_assoc (join_comm j) Hrem_lock_res) as (phi0' & jphi0' & jframe). *)
            exists (age_to n phi0'), (age_to n phi1).

            rewrite Ejm'.
            REWR. REWR. REWR.
            split.
            * auto.
            * split. 2:eapply necR_trans; [ | apply  age_to_necR ]; auto.
              split. now auto.
              split. now auto.
              unfold canon.SEPx in *.
              clear Post. simpl in *.
              rewrite seplog.sepcon_emp in *.
              revert Hlockinv.
              apply pred_hered.
              apply age_to_1.
              exact_eq lev. f_equal. join_level_tac.

          + exact_eq Safe'.
            unfold jsafeN in *.
            unfold juicy_safety.safeN in *.
            f_equal.
            cut (Some c'' = Some c'). injection 1; auto.
            rewrite <-Ec'', <-Ec'.
            unfold cl_core_sem; simpl.
            auto.
      }

    * repeat REWR.
      destruct (getThreadC j tp lj) eqn:Ej.
      -- edestruct (unique_Krun_neq i j); eauto.
      -- apply jsafe_phi_age_to; auto. apply jsafe_phi_downward. assumption.
      -- intros c' Ec'; spec safety c' Ec'. apply jsafe_phi_age_to; auto. apply jsafe_phi_downward. assumption.
      -- destruct safety as (q_new & Einit & safety). exists q_new; split; auto.
         apply jsafe_phi_age_to; auto. apply jsafe_phi_downward, safety.

  + (* well_formedness *)
    intros j lj.
    specialize (wellformed j lj).
    unshelve erewrite <-gtc_age. auto.
    unshelve erewrite gLockSetCode; auto.
    destruct (eq_dec i j).
    * subst j.
      rewrite gssThreadCode.
      replace lj with cnti in wellformed by apply proof_irr.
      rewrite Hthread in wellformed.
      auto.
    * unshelve erewrite gsoThreadCode; auto.

  + (* uniqueness *)
    apply no_Krun_unique_Krun.
    rewrite no_Krun_age_tp_to.
    apply no_Krun_updLockSet.
    apply no_Krun_stable. congruence.
    eapply unique_Krun_no_Krun. eassumption.
    instantiate (1 := cnti). rewrite Hthread.
    congruence.
Qed.
