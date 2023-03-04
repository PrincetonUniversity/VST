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
Require Import VST.veric.juicy_safety.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mem_lessdef.
Require Import VST.veric.shares.
Require Import VST.veric.age_to_resource_at.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.field_at.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.concurrency.common.permjoin.
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
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.juicy.rmap_locking.
Require Import VST.concurrency.juicy.semax_conc_pred.
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

(* to make the proof faster, we avoid unfolding of those definitions *)
Definition Jspec'_juicy_mem_equiv_def CS ext_link :=
  ext_spec_stable juicy_mem_equiv (JE_spec _ ( @OK_spec (Concurrent_Espec unit CS ext_link))).

Definition Jspec'_hered_def CS ext_link :=
   ext_spec_stable age (JE_spec _ ( @OK_spec (Concurrent_Espec unit CS ext_link))).

Opaque containsThread.

(* Weaker statement than preservation for freelock, enough to prove safety *)
Lemma safety_induction_freelock ge Gamma n state
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
  blocked_at_external state FREE_LOCK ->
  state_invariant Jspec' Gamma (S n) state ->
  exists state',
    state_step(ge := ge) state state' /\
    (state_invariant Jspec' Gamma n state' \/
     state_invariant Jspec' Gamma (S n) state').
Proof.
  assert (Hpos : (0 < LKSIZE)%Z) by reflexivity.
  intros isfreelock.
  intros I.
  inversion I as [m tr sch_ tp Phi En envcoh (*mwellformed*) compat extcompat sparse lock_coh safety wellformed unique E]. rewrite <-E in *.
  unfold blocked_at_external in *.
  destruct isfreelock as (i & cnti & sch & ci & args & -> & Eci & atex).
  pose proof (safety i cnti tt) as safei.

  rewrite Eci in safei.
  fixsafe safei.
  destruct ci as [| ?? cont |]; try discriminate.
  inversion safei
    as [ | ????? bad | z c m0 e args0 x at_ex Pre SafePost | ????? bad ]; last contradiction.
  { rewrite level_jm_ in H; setoid_rewrite H in En; discriminate. }
  apply (corestep_not_at_external (juicy_core_sem _)) in bad. exfalso; subst; clear - bad atex.
   simpl in bad. unfold cl_at_external in *; simpl in *. rewrite atex in bad; inv bad.
  subst.
  simpl in at_ex.
  unfold cl_at_external in atex, at_ex.
  assert (args0 = args) by congruence; subst args0.
  assert (e = FREE_LOCK) by congruence; subst e.
  hnf in x.
  revert x Pre SafePost.

  assert (H_freelock : Some (ext_link "freelock", ef_sig FREE_LOCK) = ef_id_sig ext_link FREE_LOCK). reflexivity.

  (* dependent destruction *)
  funspec_destruct "acquire".
  funspec_destruct "release".
  funspec_destruct "makelock".
  funspec_destruct "freelock".

  intros (phix, (ts, ((vx, shx), Rx))) (Hargsty, Pre).
  simpl (projT2 _) in *; simpl (fst _) in *; simpl (snd _) in *; clear ts.
  simpl in Pre.
  destruct Pre as (phi0 & phi1 & Join & Precond & HnecR & Hjoins).
  simpl (and _).
  intros Post.

  destruct Precond as [[Hwritable _] [B1 [_ AT]]].
  assert (Hreadable : readable_share shx) by (apply writable_readable; auto).

  (* [data_at_] from the precondition *)
  unfold SeparationLogic.argsassert2assert, canon.SEPx in *.
  simpl in AT.
  rewrite seplog.sepcon_emp in AT.

  (* value of [vx] *)
  simpl in B1.
  unfold lift, liftx in B1. simpl in B1.
  unfold lift, liftx in B1. simpl in B1.
  rewrite lockinv_isptr in AT.
  rewrite log_normalize.sepcon_andp_prop' in AT.
  rewrite seplog.corable_andp_sepcon1 in AT by (apply conclib.corable_weak_exclusive).
  destruct AT as (Hexclusive, AT).
  rewrite seplog.sepcon_comm in AT.
  rewrite seplog.sepcon_emp in AT.
  destruct AT as (IsPtr, AT).
  destruct vx as [ | | | | | b ofs ]; try inversion IsPtr; [ clear IsPtr ].

  assert (Eargs : args = Vptr b ofs :: nil) by auto.

  destruct AT as (phi0lockinv & phi0sat & jphi0 & Hlockinv & Hsat).

  assert (locked : lockRes tp (b, Ptrofs.intval ofs) = Some None). {
    specialize (lock_coh (b, Ptrofs.intval ofs)). cleanup.
    destruct (AMap.find _ _) as [[phi_sat|]|] eqn:Ephi_sat; [ exfalso | reflexivity | exfalso ].
    - destruct lock_coh as (_&_&_&R&lk&[sat|?]); [|lia].

      assert (J0 : join_sub phi0 Phi). {
        apply join_sub_trans with (getThreadR i tp cnti). eexists; eauto.
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
        apply join_sub_trans with (getThreadR i tp cnti). eexists; eauto.
        apply compatible_threadRes_sub, compat.
      }
      assert (R01 : level phi0lockinv = level Phi) by join_level_tac.
      assert (Ra : level phi_sat = level Phi) by join_level_tac.
      assert (Ra0 : level phi0sat = level Phi) by join_level_tac.
      pose proof predat6 lk as E1.
      pose proof predat4 Hlockinv as E3.
      apply (predat_join_sub J01) in E3.

      assert (joins (age_by 1 phi_sat) (age_by 1 phi0sat)) as [phi' J].
      { apply age_by_joins.
        apply joins_sym.
        eapply @join_sub_joins_trans with (c := phi0); auto. apply Perm_rmap.
        * exists phi0lockinv. apply join_comm. auto.
        * eapply @join_sub_joins_trans with (c := getThreadR i tp cnti); auto. apply Perm_rmap.
          -- exists phi1. auto.
          -- eapply compatible_threadRes_lockRes_join. apply (mem_compatible_forget compat).
             apply Ephi_sat. }
      specialize (Hexclusive phi').
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
        -- rewrite level_age_by. rewr (level phi_sat). lia.
        -- eapply predat_inj; eauto.
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
        apply join_sub_trans with (getThreadR i tp cnti). eexists; eauto.
        apply compatible_threadRes_sub, compat.
      }
      destruct j as (psi & j).
      apply resource_at_join with (loc := (b, Ptrofs.unsigned ofs)) in j.
      rewrite HH in j.
      apply lock_coh. rewrite Z.sub_diag in j.
      inv j; hnf; eauto.
  }

  pose proof lock_coh as lock_coh_.
  specialize (lock_coh (b, Ptrofs.intval ofs)). cleanup. rewrite locked in lock_coh.

  unfold tlock in *.
  apply (lock_inv_rmap_freelock CS) with (m := m) in Hlockinv; auto; try apply lock_coh.
  destruct Hlockinv as (phi0lockinv' & Hrmap00 & Hlkat).

  pose proof rmap_freelock_join _ _ _ _ _ _ _ _ Hpos Hrmap00 jphi0 as Hrmap0.
  destruct Hrmap0 as (phi0' & Hrmap0 & jphi0').
  pose proof rmap_freelock_join _ _ _ _ _ _ _ _ Hpos Hrmap0 Join as Hrmap.
  pose proof Hrmap as Hrmap_.
  destruct Hrmap_ as (phi' & RLphi & j').
  assert (ji : join_sub (getThreadR _ _ cnti) Phi) by join_sub_tac.
  destruct ji as (psi & jpsi). cleanup.
  pose proof rmap_freelock_join _ _ _ _ _ _ _ _ Hpos RLphi jpsi as Hrmap'.
  destruct Hrmap' as (Phi' & Hrmap' & J').

  subst args.

  eexists (m, (seq.cat tr (external i (freelock (b, Ptrofs.intval ofs)) :: nil), sch, _)); split.

  { (* "progress" part of the proof *)
    constructor.

    eapply JuicyMachine.sync_step
    with (Htid := cnti); auto.

    eapply step_freelock
    with (Hcompat := mem_compatible_forget compat)
                   (R := Rx) (phi' := phi').
    all: try reflexivity.
    all: try eassumption.
  }

  (* we move on to the preservation part *)

  simpl (m_phi _).
  assert (Ephi : level (getThreadR _ _ cnti) = S n). {
    rewrite getThread_level with (Phi := Phi). auto. apply compat.
  }
  assert (El : (level (getThreadR _ _ cnti) - 1 = n)%nat) by lia.
  cleanup.
  rewrite El.

  assert (LPhi' : level Phi' = level Phi) by (destruct Hrmap'; auto).

  assert (APhi' : age Phi' (age_to n Phi')) by (apply age_to_1; congruence).

  assert (Phi'rev : forall sh psh k pp' loc,
             ~adr_range (b, Ptrofs.unsigned ofs) LKSIZE loc ->
             age_to n Phi' @ loc = YES sh psh k pp' ->
             exists pp,
               Phi @ loc = YES sh psh k pp /\
               pp' = preds_fmap (approx n) (approx n) pp).
  {
    destruct Hrmap.
    intros sh psh k pp' loc nr E''.
    destruct Hrmap' as (_ & E & _).
    rewrite E; eauto.
    rewrite (age_resource_at APhi' (loc := loc)) in E''.
    destruct (Phi' @ loc); simpl in E''; try congruence.
    injection E''; intros <- <- <- ; eexists; split. apply YES_ext. reflexivity.
    rewrite level_age_to by lia. reflexivity.
  }

  assert (mcompat' : mem_compatible_with' (age_tp_to n (remLockSet (updThread i tp cnti (Kresume (Callstate f l cont) Vundef) phi') (b, Ptrofs.intval ofs))) m (age_to n Phi')).
  {
    constructor.
    + (* join_all *)
      (* rewrite <-Hpersonal_juice. autospec El. cleanup. rewrite El. *)
      apply join_all_age_to. cleanup. lia.
      pose proof juice_join compat as j.
      rewrite join_all_joinlist.
      rewrite join_all_joinlist in j.
      rewrite maps_remLockSet_updThread.
      rewrite maps_updthread.
      rewrite <-(maps_getlock2 _ (b, Ptrofs.unsigned ofs)) in j by eassumption.
      assert (cnti' : containsThread (remLockSet tp (b, Ptrofs.unsigned ofs)) i) by auto.
      rewrite maps_getthread with (i := i) (cnti := cnti') in j.
      change Ptrofs.intval with Ptrofs.unsigned.
      clear Post B1.
      eapply (joinlist_merge phi0' phi1). apply j'.
      apply join_comm in jphi0'.
      eapply (joinlist_merge _ phi0lockinv' phi0'). apply jphi0'.
      REWR in j.
      rewrite <-joinlist_merge in j by apply Join.
      rewrite <-joinlist_merge in j by apply jphi0.
      rewrite joinlist_swap.
      destruct j as (xi_ & jxi_ & jx1).
      pose proof rmap_freelock_join _ _ _ _ _ _ _ _ Hpos Hrmap00 jx1 as Hrmap1.
      destruct Hrmap1 as (Phi'_ & Hrmap'_ & J).
      assert (Phi'_ = Phi') by (eapply rmap_freelock_unique; eauto). subst Phi'_.
      exists xi_. auto.

    + (* mem_cohere' *)
      split.
      * intros rsh sh v loc pp E''.
        destruct (adr_range_dec (b, Ptrofs.unsigned ofs) LKSIZE loc) as [r|nr].
        -- destruct Hrmap' as (_ & _ & inside & _). specialize (inside loc). autospec inside.
           rewrite age_to_resource_at in E''.
           destruct inside as (sh' & rsh' & E' & wsh' & E).
           rewrite E' in E''. simpl in E''.
           injection E'' as <- <- <-.
           split; auto.
        -- destruct (Phi'rev _ _ _ _ _ nr E'') as (pp' & E & ->).
           cut (contents_at m loc = v /\ pp' = NoneP).
           { intros []; split; subst pp'; auto. }
           eapply (cont_coh (all_cohere compat)); eauto.

      * (* max_access_cohere' *)
        pose proof max_coh ( all_cohere compat) as M.
        intros loc; specialize (M loc).
        rewrite perm_of_res'_age_to.
        clear Post.
        exact_eq M. f_equal.
        destruct Hrmap' as (_ & Same & Changed & _).
        specialize (Same loc). specialize (Changed loc).
        destruct (adr_range_dec (b, Ptrofs.unsigned ofs) LKSIZE loc) as [r|nr].
        -- autospec Changed.
           destruct Changed as (sh'' & rsh'' & ? & ? & ?).
           rewrite H,H1.
           reflexivity.
        -- autospec Same. rewrite <-Same.
           reflexivity.

      * (* alloc_cohere *)
        pose proof all_coh ((all_cohere compat)) as A.
        unfold alloc_cohere in *.
        intros loc out.
        destruct Hrmap' as (_ & outside & inside & _).
        specialize (outside loc).
        spec outside.
        { destruct loc as (b', ofs').
          intros [<- _].
          specialize (A (b, Ptrofs.intval ofs) out).
          specialize (inside (b, Ptrofs.unsigned ofs)).
          spec inside. split; auto. lkomega.
          unfold Ptrofs.unsigned in *.
          breakhyps. }
        specialize (A loc out).
        rewrite age_to_resource_at, <-outside, A.
        reflexivity.

    + (* lockSet_Writable *)
      apply lockSet_Writable_age.
      intros b' ofs'.
      unfold lockGuts in *.
      simpl.
      rewrite AMap_find_remove.
      if_tac [e|ne].
      { simpl. unfold is_true in *. discriminate. }
      intros H ofs0 H0.
      eapply loc_writable; eauto.

    + (* juicyLocks_in_lockSet *)
      intros loc (*sh psh P z*)  E''.
      simpl.
      rewrite isSome_find_map.
      simpl.
      rewrite AMap_find_remove. if_tac [<- | ne].
      * exfalso.
        destruct Hrmap' as (_ & outside & inside & _).
        specialize (inside (b, Ptrofs.intval ofs)). spec inside. now split; auto; unfold Ptrofs.unsigned; lia.
        breakhyps.
        unfold Ptrofs.unsigned in *. rewrite Z.sub_diag in H7.
        destruct (E'' 0) as [? [? [? E3]]]. pose proof LKSIZE_pos; lia.
        rewrite age_to_resource_at in E3. simpl in E3. rewrite Z.add_0_r in E3.
        rewrite H5 in E3.
        discriminate.
      *
       apply (jloc_in_set compat loc).
       intros.
        destruct Hrmap' as (_ & outside & inside & _).
        rewrite outside.
        destruct (E'' _ H) as [? [? [? E3]]].
       destruct (rmap_unage_YES _ _ _ _ _ _ _ APhi' E3) as (pp, E'). eauto.
        intros r.
        specialize (inside _ r).
        destruct inside as (sh' & rsh' & E1' & wsh' & E1).
        destruct r as [? r]; subst. 
        clear - APhi' E1' r E'' H.
        specialize (E'' i0 H).
        destruct E'' as [? [? [? ?]]].
       destruct (rmap_unage_YES _ _ _ _ _ _ _ APhi' H0) as (pp, E'). 
        congruence.
 
    + (* lockSet_in_juicyLocks *)
      cleanup.
      pose proof lset_in_juice compat as J.
      intros loc. specialize (J loc).
      simpl.
      rewrite isSome_find_map.
      simpl.
      rewrite AMap_find_remove.
      if_tac.
      * discriminate.
      * intro IS; specialize (J IS).
        destruct Hrmap' as (_ & outside & inside & _).
        destruct J as [sh' J]. exists sh'.
        intros.
        destruct (adr_range_dec (b, Ptrofs.unsigned ofs) LKSIZE (fst loc, snd loc + i0)).
        -- specialize (inside _ a).
             exfalso. destruct inside as [sh [psh [? [? inside]]]].
             specialize (J _ H0). destruct J as [? [? [? [? J]]]]. rewrite inside in J. inv J.
             destruct loc,a; subst. simpl in H5,H6.
             apply H; simpl; f_equal. unfold Ptrofs.unsigned in *; lia.
        -- intros. specialize (J _ H0). destruct J as [sh2 [psh2 [P2 [? J]]]].
             exists sh2, psh2. eexists; split; auto. 
             rewrite outside in J.
             rewrite age_to_resource_at. rewrite J. reflexivity. auto.
  }

  left.
  unshelve eapply state_invariant_c with (PHI := age_to n Phi') (mcompat := mcompat').
  - (* level *)
    apply level_age_to. lia.

  - (* env_coherence *)
    apply env_coherence_age_to.
    apply env_coherence_pures_eq with Phi; auto. lia.
    apply pures_same_pures_eq. auto.
    eapply rmap_freelock_pures_same; eauto.
  - unfold ext_compat; rewrite age_to_ghost_of.
    destruct Hrmap' as (? & ? & ? & <-).
    destruct extcompat as [? J]; eapply ghost_fmap_join in J; eexists; eauto.

  - (* lock sparsity *)
    apply lock_sparsity_age_to.
    clear -sparse.
    intros loc1 loc2. cleanup. simpl. rewrite !AMap_find_remove.
    specialize (sparse loc1 loc2).
    if_tac; if_tac; eauto.

  - (* lock coherence *)
    unfold lock_coherence'.
    simpl.
    intros loc.
    rewrite AMap_find_map_option_map.
    rewrite AMap_find_remove.
    if_tac; simpl.
    + destruct Hrmap' as (_ & _ & inside & _).
      specialize (inside loc). subst loc. rewrite isLK_age_to.
      spec inside. split; auto; unfold Ptrofs.unsigned in *; lia.
      unfold Ptrofs.unsigned in *.
      destruct inside as (sh & rsh & ? & wsh & ?). intros HH.
      unfold isLK in *. breakhyps.
    + specialize (lock_coh_ loc).
      destruct (AMap.find loc _) as [[uphi|]|] eqn:Eo; simpl.

      * (* Lock found, locked *)
        specialize (sparse loc (b, Ptrofs.intval ofs)). rewrite locked in sparse. rewrite Eo in sparse.
        spec sparse. congruence.
        spec sparse. congruence.
        destruct sparse as [ | sparse]. congruence. simpl in sparse.
        assert (SparseX: forall x, adr_range loc LKSIZE x -> ~adr_range (b, Ptrofs.unsigned ofs) LKSIZE x).
        {
          clear -H sparse. intros x r.
          destruct x as (b', ofs'). simpl.
          intros [<- r'].
          destruct loc as (b', ofs0). simpl in r. destruct r as (->, r0).
          simpl in sparse.
          destruct sparse as [? | [_ sparse]]. tauto. simpl in *.
          unfold Ptrofs.unsigned in *.
          assert (ofs0 <> Ptrofs.intval ofs) by congruence. clear H.
          unfold far in *.
          unfold Ptrofs.unsigned in *.
          zify.
          lkomega.
        }
        destruct lock_coh_ as (LOAD & align & bound & R & lk & [sat | ?]); [|lia].
        split; [ | split; [ | split ]]; auto.
        -- (* use sparsity to prove the load_at is the same *)
           clear -LOAD SparseX locked sparse.
           unfold load_at in *.
           destruct loc as (b0, ofs0); simpl in LOAD |- *.
           Transparent Mem.load.
           unfold Mem.load in *.
           if_tac [v1|nv1] in LOAD; [|discriminate].
           if_tac [v2|nv2].
           ++ rewrite restrPermMap_mem_contents in *. auto.
           ++ destruct nv2. clear LOAD.
              split; [|apply v1]. destruct v1 as [v1 _].
              intros ofs1 r1. specialize (v1 ofs1 r1).
              unfold Mem.perm in *.
              pose proof restrPermMap_Cur as RR.
              unfold permission_at in *.
              rewrite RR in v1.
              rewrite RR.
              simpl.
              unfold lockSet in *.
              simpl.
              cleanup.
              setoid_rewrite A2PMap_option_map.
              pose proof SparseX as SparseX'.
              specialize (SparseX (b0, ofs0)). spec SparseX. split; auto; lkomega.
              unfold Mem.valid_access in *.
              unfold Mem.range_perm in *.
              erewrite AMap_Equal_PMap_eq in v1 by (apply AMap_remove_add; eauto).
              rewrite A2PMap_add_outside in v1.
              if_tac [r|nr] in v1; [|assumption].
              exfalso.
              specialize (SparseX' (b0, ofs1)). spec SparseX'. split; auto; unfold LKSIZE; lkomega.
              destruct r; subst b0. simpl in sparse.
              destruct sparse. contradiction H; auto. destruct H as [_ sparse].
              red in sparse.
              clear - SparseX SparseX' H0 r1 sparse. simpl in *.
              change Ptrofs.intval with Ptrofs.unsigned in *.
              assert (~ (Ptrofs.unsigned ofs <= ofs0 < Ptrofs.unsigned ofs + LKSIZE)%Z) 
                      by (contradict SparseX; auto).
              assert (~ (Ptrofs.unsigned ofs <= ofs1 < Ptrofs.unsigned ofs + LKSIZE)%Z)
                      by (contradict SparseX'; auto).
              clear - r1 H0 H H1 sparse.
              lia.
        -- exists R; split.
           ++ (* sparsity again, if easier or just the rmap_freelock *)
              intros x r.
              specialize (lk x r).
              destruct Hrmap' as (_ & outside & inside).
              specialize (outside x).
              spec outside. clear - sparse r.
              destruct loc; destruct x; destruct r. subst b1.
              intros [? ?]. subst b0. simpl in *. 
              destruct sparse. contradiction H; auto. destruct H as [_ sparse].
              change Ptrofs.intval with Ptrofs.unsigned in *.
              red in sparse.
              destruct (Zabs_dec (z - Ptrofs.unsigned ofs)); lia.
              rewrite age_to_resource_at.
              rewrite <-outside. clear outside.
              unfold sync_preds_defs.pack_res_inv in *.
              rewrite level_age_to.
              ** breakhyps.
                 all: rewr (Phi @ x); simpl; eauto.
                 all: rewrite approx_approx'; eauto; lia.
              ** lia.
           ++ left. unfold age_to.
              replace (level uphi) with (level Phi).
              rewrite En. replace (S n - n)%nat with 1%nat by lia.
              apply pred_age1', sat.
              { symmetry. eapply join_all_level_lset. apply compat. eassumption. }

      * (* Lock found, unlocked *)
        specialize (sparse loc (b, Ptrofs.intval ofs)). rewrite locked in sparse. rewrite Eo in sparse.
        spec sparse. congruence.
        spec sparse. congruence.
        destruct sparse as [ | sparse]. congruence.
        assert (SparseX: forall x, adr_range loc LKSIZE x -> ~adr_range (b, Ptrofs.unsigned ofs) LKSIZE x).
        {
          clear -H sparse. intros x r.
          destruct x as (b', ofs'). simpl.
          intros [<- r'].
          destruct loc as (b', ofs0). simpl in r. destruct r as (->, r0).
          simpl in sparse.
          destruct sparse as [? | [_ sparse]]. tauto. simpl in *.
          unfold Ptrofs.unsigned in *.
          assert (ofs0 <> Ptrofs.intval ofs) by congruence. clear H.
          unfold far in *.
          zify.
          lkomega.
        }
        destruct lock_coh_ as (LOAD & align & bound & R & lk).
        split; [ | split; [ | split ]]; auto.
        -- (* use sparsity to prove the load_at is the same *)
           clear -LOAD SparseX locked sparse.
           unfold load_at in *.
           destruct loc as (b0, ofs0); simpl in LOAD |- *.
           unfold Mem.load in *.
           if_tac [v1|nv1] in LOAD; [|discriminate].
           if_tac [v2|nv2].
           ++ rewrite restrPermMap_mem_contents in *. auto.
           ++ destruct nv2. clear LOAD.
              split; [|apply v1]. destruct v1 as [v1 _].
              intros ofs1 r1. specialize (v1 ofs1 r1).
              unfold Mem.perm in *.
              pose proof restrPermMap_Cur as RR.
              unfold permission_at in *.
              rewrite RR in v1.
              rewrite RR.
              simpl.
              unfold lockSet in *.
              simpl.
              cleanup.
              setoid_rewrite A2PMap_option_map.
              pose proof SparseX as SparseX'.
              specialize (SparseX (b0, ofs0)). spec SparseX. split; auto; lkomega.
              unfold Mem.valid_access in *.
              unfold Mem.range_perm in *.
              (* say that "lset = ADD (REMOVE lset)" and use result about ADD? *)
              erewrite AMap_Equal_PMap_eq in v1 by (apply AMap_remove_add; eauto).
              rewrite A2PMap_add_outside in v1.
              if_tac [r|nr] in v1; [|assumption].
              exfalso.
              specialize (SparseX' (b0, ofs1)). spec SparseX'. split; auto; unfold LKSIZE; lkomega.
              simpl in sparse.
              destruct r; subst b0.
              clear - SparseX SparseX' H0 r1 sparse. simpl in *.
              destruct sparse. contradiction H; auto. destruct H as [_ sparse].
              change Ptrofs.intval with Ptrofs.unsigned in *.
              assert (~ (Ptrofs.unsigned ofs <= ofs0 < Ptrofs.unsigned ofs + LKSIZE)%Z) 
                      by (contradict SparseX; auto).
              assert (~ (Ptrofs.unsigned ofs <= ofs1 < Ptrofs.unsigned ofs + LKSIZE)%Z)
                      by (contradict SparseX'; auto).
              clear - r1 H0 H H1 sparse. lia.
        -- exists R.
           (* sparsity again, if easier or just the rmap_freelock *)
           intros x r.
           specialize (lk x r).
           destruct Hrmap' as (_ & outside & inside).
           specialize (outside x).
              spec outside. clear - sparse r.
              destruct loc; destruct x; destruct r. subst b1.
              intros [? ?]. subst b0. simpl in *. 
              destruct sparse. contradiction H; auto. destruct H as [_ sparse].
              change Ptrofs.intval with Ptrofs.unsigned in *.
              red in sparse.
              destruct (Zabs_dec (z - Ptrofs.unsigned ofs)); lia.
           rewrite age_to_resource_at.
           rewrite <-outside. clear outside.
           unfold sync_preds_defs.pack_res_inv in *.
           rewrite level_age_to.
           ++ breakhyps.
              all: rewr (Phi @ x); simpl; eauto.
              all: rewrite approx_approx'; eauto; lia.
           ++ lia.

      * (* Lock not found, unlocked *)
        rewrite age_to_resource_at.
        destruct Hrmap' as (_ & inside & outside & _). clear Post B1 Phi'rev.
        intros LK. specialize (inside loc). specialize (outside loc). spec inside.
        { intros r. specialize (outside r). destruct LK as (sh & sh' & z & pp & E).
          breakhyps. rewr (Phi' @ loc) in E. breakhyps. }
        apply lock_coh_. rewrite inside. destruct LK as (sh & sh' & z & pp & E).
        destruct (Phi' @ loc) as [t0 | t0 p [] p0 | k p]; breakhyps.
        hnf. inv E; eauto.

  - (* safety *)
    {
    intros j lj ora.
    specialize (safety j lj ora).
    unshelve erewrite <-gtc_age. auto.
    unshelve erewrite gRemLockSetCode; auto.
    destruct (eq_dec i j).
    * {
        (* use the "well formed" property to derive that this is
              an external call, and derive safety from this.  But the
              level has to be decreased, here. *)
        subst j.
        rewrite gssThreadCode.
        replace lj with cnti in safety by apply proof_irr.
        simpl in safety; rewrite Eci in safety.
        specialize (wellformed i cnti).
        simpl in wellformed; rewrite Eci in wellformed.
        intros c' Ec'.
        - (* at_external : we can now use safety *)
          intros jm' Ejm'.
          destruct Post with
          (ret := @None val)
            (m' := jm')
            (z' := ora) as (c'' & Ec'' & Safe').

          + auto.

          + simpl.
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
            }
            assert (level phi' = S n). {
              cleanup. replace (level phi') with (S n). lia. join_level_tac.
            }

            split.
            * rewr (level jm'). rewrite level_jm_. cleanup. lia.
            * simpl. rewrite Ejm'. REWR. REWR. REWR.
              eapply pures_same_eq_l; [|apply pures_eq_age_to; lia].
              apply pures_same_trans with phi1.
              -- apply pures_same_sym. apply join_sub_pures_same. exists phi0'. apply join_comm. assumption.
              -- apply join_sub_pures_same. exists phi0. apply join_comm. assumption.

          + (* we must satisfy the post condition *)
            rewrite Ejm'.
            exists (age_to n phi0'), (age_to n phi1).
            split.
            * REWR.
              apply age_to_join.
              REWR.
              REWR.
            * split; [|now eapply necR_trans; [ eassumption | apply age_to_necR ]].
              split. now constructor.
              split. now constructor.
              simpl. rewrite seplog.sepcon_emp.
              unfold semax_conc_pred.lock_inv in *.
              exists (age_to n phi0lockinv'), (age_to n phi0sat).
              split. now apply age_to_join; auto.
              split. 
              apply age_to_pred.
              assumption.
              apply age_to_pred. assumption.
          + simpl in Ec'.
            destruct f; inv Ec'; inv Ec''.
            apply Safe'.
      }

    * repeat REWR.
      destruct (getThreadC j tp lj) eqn:Ej.
      -- edestruct (unique_Krun_neq(ge := ge) i j); eauto.
      -- apply jsafe_phi_age_to; auto.
      -- intros c' Ec'; specialize (safety c' Ec'). apply jsafe_phi_fupd_age_to; auto.
      -- destruct safety as (q_new & Einit & safety).
         exists q_new; split; auto.
         apply jsafe_phi_fupd_age_to; auto.
    }

  - (* threads_wellformed *)
    intros j lj.
    specialize (wellformed j lj).
    unshelve erewrite <-gtc_age. auto.
    unshelve erewrite gRemLockSetCode; auto.
    destruct (eq_dec i j).
    + subst j.
      rewrite gssThreadCode; simpl.
      rewrite atex; split; auto; discriminate.
    + unshelve erewrite gsoThreadCode; auto.

  - (* unique_Krun *)
    apply no_Krun_unique_Krun.
    rewrite no_Krun_age_tp_to.
    apply no_Krun_remLockSet.
    apply no_Krun_stable. congruence.
    eapply unique_Krun_no_Krun. eassumption.
    instantiate (1 := cnti). simpl.
    congruence.
Qed.
