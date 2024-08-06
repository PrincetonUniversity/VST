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
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax_prog.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop.
Require Import VST.veric.semax.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mem_lessdef.
Require Import VST.floyd.coqlib3.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.concurrency.common.permjoin.
Require Import VST.concurrency.juicy.semax_conc.
Require Import VST.concurrency.juicy.juicy_machine.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.juicy.JuicyMachineModule.
Require Import VST.concurrency.juicy.sync_preds_defs.
Require Import VST.concurrency.juicy.join_lemmas.
Require Import VST.concurrency.juicy.semax_invariant.
Require Import VST.concurrency.juicy.semax_simlemmas.
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.common.lksize.
Import Events.

Local Arguments getThreadR {_} {_} {_} _ _ _.
Local Arguments getThreadC {_} {_} {_} _ _ _.
Local Arguments personal_mem : clear implicits.
Local Arguments updThread {_} {_} {_} _ _ _ _ _.
Local Arguments updThreadR {_} {_} {_} _ _ _ _.
Local Arguments updThreadC {_} {_} {_} _ _ _ _.
Local Arguments juicyRestrict : clear implicits.

Set Bullet Behavior "Strict Subproofs".

Open Scope string_scope.

Lemma listoption_inv_In : forall {A} (x : A) l, In (Some x) l -> In x (listoption_inv l).
Proof.
  induction l; auto; simpl.
  intros [|]; subst; simpl; auto.
  destruct a; simpl; auto.
Qed.

Lemma lockRes_thread : forall ge (tp : jstate ge) l r, lockRes tp l = Some (Some r) ->
  In r (listoption_inv (map snd (AMap.elements (elt:=lock_info) (lockGuts tp)))).
Proof.
  destruct tp; simpl.
  unfold OrdinalPool.lockRes; simpl.
  intros ?? H%AMap.find_2%AMap.elements_1.
  apply SetoidList.InA_alt in H as ((?,?) & [] & ?); simpl in *; subst.
  apply listoption_inv_In, in_map_iff.
  eexists; split; eauto; auto.
Qed.

(* to make the proof faster, we avoid unfolding of those definitions *)
Definition Jspec'_juicy_mem_equiv_def CS ext_link :=
  ext_spec_stable juicy_mem_equiv (JE_spec _ ( @OK_spec (Concurrent_Espec unit CS ext_link))).

Definition Jspec'_hered_def CS ext_link :=
   ext_spec_stable age (JE_spec _ ( @OK_spec (Concurrent_Espec unit CS ext_link))).

Lemma preservation_acquire
  (lockSet_Writable_updLockSet_updThread
     : forall ge (m m' : Memory.mem) (i : nat) (tp : jstate ge),
       forall (cnti : containsThread tp i) (b : block) (ofs : ptrofs) (ophi : option rmap)
         (ophi' : lock_info) (c' : ctl) (phi' : res)
         z (Hcmpt : mem_compatible tp m)
         (Hcmpt : mem_compatible tp m)
         (His_unlocked : AMap.find (elt:=option rmap) (b, Ptrofs.intval ofs) (lset tp) = Some ophi)
         (Hlt' : permMapLt
              (setPermBlock (Some Writable) b (Ptrofs.intval ofs) (juice2Perm_locks (getThreadR i tp cnti) m)
                 LKSIZE_nat) (getMaxPerm m))
         (Hstore : Mem.store Mptr (restrPermMap Hlt') b (Ptrofs.intval ofs) (Vptrofs z) = Some m'),
       lockSet_Writable (lset (updLockSet (updThread i tp cnti c' phi') (b, Ptrofs.intval ofs) ophi')) m')
  (mem_cohere'_store : forall ge m (tp : jstate ge) m' b ofs j i Phi (cnti : containsThread tp i)
    (Hcmpt : mem_compatible tp m)
    (lock : lockRes tp (b, Ptrofs.intval ofs) <> None)
    (Hlt' : permMapLt
           (setPermBlock (Some Writable) b (Ptrofs.intval ofs) (juice2Perm_locks (getThreadR i tp cnti) m)
              LKSIZE_nat) (getMaxPerm m))
    (Hstore : Mem.store Mptr (restrPermMap Hlt') b (Ptrofs.intval ofs) (Vptrofs j) = Some m'),
    mem_compatible_with tp m Phi ->
    (exists phi, join_sub phi Phi /\ exists sh R, LKspec LKSIZE sh R (b, Ptrofs.intval ofs) phi) ->
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
  (ge : genv)
  (m m' : Memory.mem)
  (tr : event_trace)
  (i : nat)
  (sch : list nat)
  (tp : jstate ge)
  (INV : state_invariant Jspec' Gamma (S n) (m, (tr, i :: sch, tp)))
  (Phi : rmap)
  (compat : mem_compatible_with tp m Phi)
  (lev : level Phi = S n)
  (envcoh : env_coherence Jspec' ge Gamma Phi)
  (extcompat : joins (ghost_of Phi) (Some (ext_ref tt, NoneP) :: nil))
  (sparse : lock_sparsity (lset tp))
  (lock_coh : lock_coherence' tp Phi m compat)
  (safety : threads_safety Jspec' m tp Phi compat)
  (wellformed : threads_wellformed tp)
  (unique : unique_Krun tp (i :: sch))
  (Ei cnti : containsThread tp i)
  (ci : semC)
  (Eci : getThreadC i tp cnti = Kblocked ci)
  (Hcmpt : mem_compatible tp m)
  (El : (level (getThreadR i tp cnti) - 1 = n)%nat)
  (compat_aged : mem_compatible_with (age_tp_to n tp) m (age_to n Phi))
  (c : semC)
  (b : block)
  (ofs : ptrofs)
  (d_phi : rmap)
  (phi' : rmap)
  (sh : Share.t)
  (psh : shares.readable_share sh)
  (R : pred rmap)
  (Hthread : getThreadC i tp cnti = Kblocked c)
  (Hat_external : at_external (Clight_evsem.CLC_evsem ge) c m = Some (LOCK, Vptr b ofs :: nil))
  (His_unlocked : lockRes tp (b, Ptrofs.intval ofs) = Some (Some d_phi))
  (Hload : Mem.load Mptr (juicyRestrict_locks (mem_compat_thread_max_cohere Hcmpt cnti))
                    b (Ptrofs.intval ofs) =
          Some (Vptrofs Ptrofs.one))
  (Hlt' : permMapLt
           (setPermBlock (Some Writable) b (Ptrofs.intval ofs) (juice2Perm_locks (getThreadR i tp cnti) m)
              LKSIZE_nat) (getMaxPerm m))
  (Hstore : Mem.store Mptr (restrPermMap Hlt') b (Ptrofs.intval ofs) (Vptrofs Ptrofs.zero) = Some m')
(*  (HJcanwrite : lock_at_least sh R (getThreadR i tp cnti) b (Ptrofs.intval ofs)) *)
(* forall j, 0 <= j < LKSIZE -> getThreadR i tp cnti @ (b, Ptrofs.intval ofs+j) = YES sh psh (LK LKSIZE j) (pack_res_inv R)) *)
  (Hadd_lock_res : join (getThreadR i tp cnti) d_phi phi')
  (jmstep : @JuicyMachine.machine_step _ (ClightSemanticsForMachines.ClightSem ge) _ HybridCoarseMachine.DilMem JuicyMachineShell HybridMachineSig.HybridCoarseMachine.scheduler (i :: sch) tr tp m sch (seq.cat tr (external i (acquire (b, Ptrofs.intval ofs) None) :: nil))
             (age_tp_to n
                (updLockSet (updThread i tp cnti (Kresume c Vundef) phi') (b, Ptrofs.intval ofs) None)) m')
  (Htstep : @syncStep (ClightSemanticsForMachines.ClightSem ge) true _ _ _ cnti Hcmpt
             (age_tp_to n
                (updLockSet (updThread i tp cnti (Kresume c Vundef) phi') (b, Ptrofs.intval ofs) None)) m'
             (Events.acquire (b, Ptrofs.intval ofs) None)) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m', (seq.cat tr (external i (acquire (b, Ptrofs.intval ofs) None) :: nil), sch, age_tp_to n
           (updLockSet (updThread i tp cnti (Kresume c Vundef) phi') (b, Ptrofs.intval ofs) None) : jstate ge)).

Proof.
  (* we prove [mem_compatible_with] BEFORE aging, as it it slightly
    easier, proving [mem_compatible_with] after aging is a simple
    application of the lemma [mem_compatible_with_age] *)
  pose (tp__ := updLockSet (updThread i tp cnti (Kresume c Vundef) phi') (b, Ptrofs.intval ofs) None).
  assert (compat'' : mem_compatible_with tp__ m' Phi). {
    subst tp__.
    constructor.
    - (* joining to global map: the acquired rmap move from
            lockset to threads's maps *)
      pose proof juice_join compat as J.
      clear -J lev His_unlocked Hadd_lock_res.
      rewrite join_all_joinlist in *.
      rewrite maps_updlock1.
      erewrite maps_getlock3 in J; eauto.
      rewrite maps_remLockSet_updThread.
      rewrite maps_updthread.
      simpl map.
      assert (pr:containsThread (remLockSet tp (b, Ptrofs.intval ofs)) i) by auto.
      rewrite (maps_getthread i _ pr) in J.
      rewrite gRemLockSetRes with (cnti := cnti) in J. clear pr.
      revert Hadd_lock_res J.
      generalize (getThreadR _ _ cnti) d_phi phi'.
      generalize (all_but i (maps (remLockSet tp (b, Ptrofs.intval ofs)))).
      clear -lev.
      intros l a b c j h.
      rewrite Permutation.perm_swap in h.
      eapply joinlist_merge; eassumption.

    - (* mem_cohere' *)
      pose proof juice_join compat as J.
      pose proof all_cohere compat as MC.
      eapply (mem_cohere'_store _ _ tp _ _ _ (Ptrofs.zero) _ _ cnti Hcmpt).
      + cleanup.
        rewrite His_unlocked. simpl. congruence.
      + (* there is this hcmpt which is redundant, we can prove they're equal or think more to factorize it *)
        apply Hstore.
      + auto.
      + specialize (safety _ cnti tt).
        rewrite Hthread in safety.
        unshelve eapply jsafe_phi_jsafeN in safety; try apply compat.
        inversion safety as [ | ????? step | ?????? ae Pre Post Safe | ???? Ha].
        * rewrite level_jm_ in H; setoid_rewrite H in lev; discriminate.
        * (* not corestep *)
          exfalso.
          clear -Hat_external step.
          apply (corestep_not_at_external (juicy_core_sem _)) in step.
          rewrite jstep.JuicyFSem.t_obligation_2 in step.
          set (u := at_external _ _ _) in Hat_external.
          set (v := at_external _ _ _) in step.
          assert (u = v).
          { unfold u, v. rewrite ClightSemanticsForMachines.at_external_SEM_eq. reflexivity. }
          congruence.
        * assert (e = LOCK).
          { simpl in ae.
            clear - ae Hat_external. rewrite ClightSemanticsForMachines.at_external_SEM_eq in Hat_external.
            unfold j_at_external in ae. unfold cl_at_external in ae.
            congruence. }
          subst e.
          revert x Pre Post.
          funspec_destruct "acquire".
          intros (? & ? & [] & ? & ?) (Hargsty, Pre) Post.
          destruct Pre as (phi0 & phi1 & j & Pre & H88).
          simpl in Pre.
          destruct Pre as [_ [Hv [_ Hlk]]].
          unfold canon.SEPx, SeparationLogic.argsassert2assert in Hlk; simpl in Hlk.
          rewrite seplog.sepcon_emp in Hlk.
          assert (args = Vptr b ofs :: nil). {
            revert Hat_external ae; clear.
            rewrite Clight_evsem.CLC_msem. simpl.
            intros. unfold cl_at_external in *.
            congruence.
          }
          subst args.
          assert (v = Vptr b ofs). {
            inv Hv; auto.
          }
          subst v.
          destruct Hlk as (? & ? & Heq & ?); inv Heq.
          exists phi0; split; eauto.
          eapply join_sub_trans; [eexists; eauto|].
          apply compatible_threadRes_sub; auto.
          { exfalso. unfold ef_id_sig, ef_sig in *.
            unfold funsig2signature in Heq_name; simpl in Heq_name.
            contradiction Heq_name; auto. }
        * (* not halted *)
          destruct c; try discriminate. contradiction.

    - (* lockSet_Writable *)
      eapply lockSet_Writable_updLockSet_updThread; eauto.

    - (* juicyLocks_in_lockSet *)
      pose proof jloc_in_set compat as jl.
      hnf. intros loc ?. 
      specialize (jl loc H). clear H.
      simpl.
      rewrite AMap_find_add.
      if_tac. reflexivity.
      apply jl.

    - (* lockSet_in_juicyLocks *)
      pose proof lset_in_juice compat as lj.
      intros loc; specialize (lj loc).
      simpl.
      rewrite AMap_find_add.
      if_tac.
      + intros _. subst loc.
        assert_specialize lj. {
          cleanup.
          rewrite His_unlocked.
          reflexivity.
        }
        destruct lj as (sh' & E). exists sh'; auto.
      + cleanup.
        intros is; specialize (lj is).
        destruct lj as (sh' & E). exists sh'. auto.
  }

  pose proof mem_compatible_with_age _ compat'' (n := n) as compat'.
  unfold tp__ in *; clear tp__.

  apply state_invariant_c with (mcompat := compat').
  + (* level *)
    apply level_age_to. cleanup. lia.

  + (* env_coherence *)
    apply env_coherence_age_to. auto.
(*  + inv INV. clear -mwellformed Hstore.
    eapply mem_wellformed_store; [.. | apply Hstore |]; auto.
    apply mem_wellformed_restr; auto. *)
  + unfold ext_compat; rewrite age_to_ghost_of.
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
      rewrite His_unlocked. congruence.

  + (* lock coherence *)
    intros loc.
    simpl (AMap.find _ _).
    rewrite AMap_find_map_option_map.
    rewrite AMap_find_add.
    specialize (lock_coh loc).
    if_tac.

    * (* current lock is acquired: load is indeed 0 *)
      { subst loc.
        split.
        - (* in dry : it is 0 *)
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
              rewrite gssLockRes. simpl. congruence.
            * congruence.

        - (* the rmap is unchanged (but we lose the SAT information) *)
          cut ((size_chunk Mptr | Ptrofs.intval ofs) /\  (Ptrofs.intval ofs + LKSIZE < Ptrofs.modulus)%Z /\
               exists R0, (lkat R0 (b, Ptrofs.intval ofs)) Phi).
          { intros (align & bound & R0 & AP). repeat (split; auto).
            exists R0. revert AP. apply age_to_ind, lkat_hered. }
          cleanup.
          rewrite His_unlocked in lock_coh.
          destruct lock_coh as (H & (* ? & *) ? & align & bound & lk & _).
          eauto.
      }

    * (* not the current lock *)
      destruct (AMap.find (elt:=option rmap) loc (lset tp)) as [o|] eqn:Eo; [|rewrite isLK_age_to; auto].
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
        assert_specialize SPA by (cleanup; congruence).
        assert_specialize SPA by (cleanup; congruence).
        simpl in SPA.
        destruct SPA as [SPA|SPA]; [ tauto | ].
        unfold Mem.load in *.
        if_tac [V|V]; [ | congruence].
        if_tac [V'|V'].
        - rewrite !restrPermMap_mem_contents.
          intros G; exact_eq G.
          f_equal.
          f_equal.
          f_equal.

          pose proof store_outside' _ _ _ _ _ _ Hstore as OUT.
          destruct OUT as (OUT, _).
          cut (forall z,
                  (0 <= z < size_chunk Mptr)%Z ->
                  ZMap.get (ofs' + z)%Z (Mem.mem_contents m) !! b' =
                  ZMap.get (ofs' + z)%Z (Mem.mem_contents m') !! b').
          {
            intros G; simpl.
            repeat rewrite <- Z.add_assoc.
            f_equal.
            - specialize (G 0%Z ltac:(simpl; lia)).
              exact_eq G. repeat f_equal; auto with zarith.
            - repeat (f_equal; [apply G; simpl; lia | ]); f_equal; apply G; simpl; lia.
          }
          intros z Iz.
          specialize (OUT b' (ofs' + z)%Z).

          destruct OUT as [[-> OUT]|OUT]; [ | clear SPA].
          + exfalso.
            destruct SPA as [? | [_ SPA]]; [ tauto | ].
            eapply far_range in SPA. apply SPA; clear SPA.
            * instantiate (1 := z).
              unfold size_chunk in *.
              unfold LKSIZE in *.
              destruct Mptr; simpl in *; lia.
            * unfold LKSIZE in *.
              destruct Mptr; simpl in *; lia.
          + unfold contents_at in *.
            simpl in OUT.
            apply OUT.

        - exfalso.
          apply V'; clear V'.
          unfold Mem.valid_access in *.
          split; [|apply V]. destruct V as [V _].
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
            * hnf; simpl. eauto. lkomega.
            * cleanup. rewrite Eo. reflexivity.
          + rewrite OrdinalPool.gsoLockSet_1; auto.
            * apply OrdinalPool.lockSet_spec_2 with ofs'.
              -- hnf; simpl. eauto. lkomega.
              -- cleanup. rewrite Eo. reflexivity.
            * unfold far in *.
              simpl in *.
              clear - int0 ofsOUT H.
              pose proof LKSIZE_pos.
              zify.
              unfold LKSIZE in *; simpl in *; lia.
      }
      destruct o; destruct lock_coh as (Load & align & bound & R' & lks); split.
      -- now intuition.
      -- repeat (split; auto).
         exists R'.
         destruct lks as (lk, sat); split.
         ++ revert lk.
            apply age_to_ind, lkat_hered.
         ++ destruct sat as [sat|sat].
            ** left; revert sat.
               unfold age_to in *.
               rewrite age_by_age_by.
               apply age_by_age_by_pred.
               lia.
            ** congruence.
      -- now intuition.
      -- repeat (split; auto).
         exists R'.
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

        eapply jsafe_phi_jsafeN with (compat := compat) in safety.
        inversion safety as [ | ????? step | ?????? ae Pre Post Safe | ???? Ha]; last (destruct c; try discriminate; contradiction).
        - rewrite level_jm_ in H; setoid_rewrite H in lev; discriminate.
        - (* not corestep *)
          exfalso.
          clear -Hat_external step.
          apply (corestep_not_at_external (juicy_core_sem _)) in step.
          rewrite jstep.JuicyFSem.t_obligation_2 in step.
          set (u := at_external _ _ _) in Hat_external.
          set (v := at_external _ _ _) in step.
          assert (u = v).
          { unfold u, v. rewrite ClightSemanticsForMachines.at_external_SEM_eq. reflexivity.
         }
          congruence.

        - (* at_external : we can now use safety *)
          subst z c0 m0.
          intros jm' Ejm'.
          destruct Post with
          (ret := @None val)
            (m' := jm')
            (z' := ora) as (c'' & Ec'' & Safe').

          + assert (e = LOCK).
            { simpl in ae.
              clear - ae Hat_external. rewrite ClightSemanticsForMachines.at_external_SEM_eq in Hat_external.
              unfold j_at_external in ae. unfold cl_at_external in ae.
              congruence. }
            assert (args = Vptr b ofs :: nil).
            { simpl in ae.
              clear - ae Hat_external. rewrite ClightSemanticsForMachines.at_external_SEM_eq in Hat_external.
              unfold j_at_external in ae. unfold cl_at_external in ae.
              congruence. }
            subst e args; simpl; auto.

          + assert (e = LOCK).
            { simpl in ae.
              clear - ae Hat_external. rewrite ClightSemanticsForMachines.at_external_SEM_eq in Hat_external.
              unfold j_at_external in ae. unfold cl_at_external in ae.
              congruence. }
            subst e.
            apply Logic.I.

          + (* proving Hrel *)
            hnf.
            assert (n = level jm'). {
              rewrite <-level_m_phi.
              rewrite Ejm'.
              REWR.
              REWR.
              REWR.
              rewrite level_age_to; auto.
              replace (level phi') with (level Phi). lia.
              transitivity (level (getThreadR i tp cnti)); join_level_tac.
              setoid_rewrite getThread_level with (Phi := Phi). auto. apply compat.
            }
            assert (level phi' = S n). {
              transitivity (level (getThreadR i tp cnti)); join_level_tac.
              setoid_rewrite getThread_level with (Phi := Phi). auto. apply compat.
            }

            split.
            * rewr (level jm'). rewrite level_jm_. cleanup. lia.
            * simpl. rewrite Ejm'. REWR. REWR. REWR.
              eapply pures_same_eq_l, pures_eq_age_to; [|lia].
              apply pures_same_sym.
              apply join_sub_pures_same. exists d_phi. assumption.

          + (* we must satisfy the post condition *)
            assert (e = LOCK).
            { simpl in ae.
              clear - ae Hat_external. rewrite ClightSemanticsForMachines.at_external_SEM_eq in Hat_external.
              unfold j_at_external in ae. unfold cl_at_external in ae. 
              congruence. }
            subst e.
            revert x Pre Post.
            funspec_destruct "acquire".
            intros x (Hargsty, Pre) Post.
            simpl.
            destruct Pre as (phi0 & phi1 & j & Pre).
            destruct (join_assoc (join_comm j) Hadd_lock_res) as (phi0' & jphi0' & jframe).
            exists (age_to n phi0'), (age_to n phi1).
            rewrite Ejm'.
            split.
            * REWR.
              apply age_to_join.
              apply join_comm in jframe.
              exact_eq jframe. f_equal.
              REWR.
              REWR.
            * destruct x as (phix, (ts, ((vx, shx), Rx)));
                simpl (fst _) in *; simpl (snd _) in *; simpl (projT2 _) in *.
              clear ts.
              cbv iota beta in Pre.
              destruct Pre as (([A _] & B & _ & D) & E & F).
Opaque age_tp_to. Opaque LKSIZE_nat.
              split; [|eapply necR_trans; [ | apply  age_to_necR ]; auto].
              split. now auto.
              split. now auto.
              unfold canon.SEPx in *.
              clear Post. simpl in *.
              rewrite seplog.sepcon_emp in *.
              exists (age_to n phi0), (age_to n d_phi); split3.
              -- apply age_to_join; auto.
              -- revert D. apply age_to_ind. apply pred_hered.
              -- specialize (lock_coh (b, Ptrofs.intval ofs)).
                 cleanup.
                 rewrite His_unlocked in lock_coh.
                 destruct lock_coh as [_ (align & bound & R' & lkat & sat)].
                 destruct sat as [sat | ?]; [|congruence].
                 pose proof predat6 lkat as ER'.
                 assert (args = vx :: nil) by auto.
                 subst args.
                 rewrite Hat_external in ae; inversion ae; subst vx.
                 pose proof predat4 D as ERx.
                 assert (join_sub phi0 Phi).
                 { join_sub_tac.
                   apply join_sub_trans with (OrdinalPool.getThreadR cnti). exists phi1. auto.
                   apply compatible_threadRes_sub, compat.
                 }
                 apply (@predat_join_sub _ Phi) in ERx; auto.
                 unfold Ptrofs.unsigned in *.
                 pose proof predat_inj ER' ERx as ER.
                 assert (age_by 1 d_phi = age_to n d_phi) as Heq; [|setoid_rewrite Heq in sat].
                 {
                   unfold age_to in *. f_equal.
                   replace (level d_phi) with (level Phi). lia.
                   pose proof @compatible_lockRes_sub_all _ _ _ _ His_unlocked Phi ltac:(apply compat).
                   join_level_tac.
                 }
                 replace (level phi0) with (level Phi) in * by join_level_tac.
                 rewrite lev in *.
                 revert sat.
                 apply approx_eq_app_pred with (S n); auto.
                 rewrite level_age_to. auto.
                 replace (level d_phi) with (level Phi) in * by join_level_tac.
                 lia.
            * exfalso. unfold ef_id_sig, ef_sig in *.
              unfold funsig2signature in Heq_name; simpl in Heq_name.
              contradiction Heq_name; auto.

          + exact_eq Safe'.
            unfold jsafeN in *.
            f_equal; f_equal.
            cut (Some c'' = Some c'). injection 1; auto.
            rewrite <-Ec'', <-Ec'.
            unfold cl_core_sem; simpl.
            auto.
      }

    * repeat REWR.
      destruct (getThreadC j tp lj) eqn:Ej.
      -- edestruct (unique_Krun_neq(ge := ge) i j); eauto.
      -- apply jsafe_phi_age_to; auto.
      -- intros c' Ec'; specialize (safety c' Ec'). apply jsafe_phi_fupd_age_to; auto.
      -- destruct safety as (q_new & Einit & safety).
         exists q_new; split; auto.
         apply jsafe_phi_fupd_age_to; auto.

  + (* well_formedness *)
    intros j lj.
    specialize (wellformed j lj).
    unshelve erewrite <-gtc_age. auto.
    unshelve erewrite gLockSetCode; auto.
    destruct (eq_dec i j).
    * subst j.
      REWR.
      replace lj with cnti in wellformed by apply proof_irr.
      rewrite Hthread in wellformed.
      auto.
    * REWR.

  + (* uniqueness *)
    apply no_Krun_unique_Krun.
    rewrite no_Krun_age_tp_to.
    apply no_Krun_updLockSet.
    apply no_Krun_stable. congruence.
    eapply unique_Krun_no_Krun. eassumption.
    instantiate (1 := cnti). rewrite Hthread.
    congruence.
Qed. (* preservation_acquire *)
