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
Require Import VST.veric.shares.
Require Import VST.veric.age_to_resource_at.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.field_at.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.concurrency.common.permjoin.
Require Import VST.concurrency.juicy.semax_conc.
Require Import VST.concurrency.common.addressFiniteMap.
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

(* Weaker statement than preservation for makelock, enough to prove safety *)
Lemma safety_induction_makelock ge Gamma n state
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
  blocked_at_external state MKLOCK ->
  state_invariant Jspec' Gamma (S n) state ->
  exists state',
    state_step(ge := ge) state state' /\
    (state_invariant Jspec' Gamma n state' \/
     state_invariant Jspec' Gamma (S n) state').
Proof.
  assert (Hpos : (0 < LKSIZE)%Z) by reflexivity.
  intros ismakelock.
  intros I.
  inversion I as [m tr sch_ tp Phi En envcoh compat extcompat sparse lock_coh safety wellformed unique E]. rewrite <-E in *.
  unfold blocked_at_external in *.
  destruct ismakelock as (i & cnti & sch & ci & args & -> & Eci & atex).
  pose proof (safety i cnti tt) as safei.

  rewrite Eci in safei.

  fixsafe safei.
  inversion safei
    as [ | ?????? bad | n0 z c m0 e args0 x at_ex Pre SafePost | ????? bad ].
  apply (corestep_not_at_external (juicy_core_sem _)) in bad. elimtype False; subst; clear - bad atex.
   simpl in bad. unfold cl_at_external in *; simpl in *. rewrite atex in bad; inv bad.
  2: inversion bad.
  subst.
  simpl in at_ex.
  unfold cl_at_external in atex, at_ex.
  assert (args0 = args) by congruence; subst args0.
  assert (e = MKLOCK) by congruence; subst e.
  hnf in x.
  revert x Pre SafePost.

  assert (H_makelock : Some (ext_link "makelock", ef_sig MKLOCK) = ef_id_sig ext_link MKLOCK). reflexivity.

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

  destruct Precond as [[Hwritable _] [[[B1 _] _] AT]].
  assert (Hreadable : readable_share shx) by (apply writable_readable; auto).

  (* [data_at_] from the precondition *)
  unfold canon.SEPx in *.
  simpl in AT.
  rewrite seplog.sepcon_emp in AT.

  (* value of [vx] *)
  simpl in B1.
  unfold lift, liftx in B1. simpl in B1.
  unfold lift, liftx in B1. simpl in B1.
  rewrite data_at__isptr in AT.
  destruct AT as (IsPtr, AT).
  destruct vx as [ | | | | | b ofs ]; try inversion IsPtr; [ clear IsPtr ].

  assert (Eargs : args = Vptr b ofs :: nil)
    by (eapply shape_of_args; eauto).

  assert (Hm' : exists m', Mem.store Mint32 (m_dry (personal_mem _ _ (thread_mem_compatible (mem_compatible_forget compat) cnti))) b (Ptrofs.intval ofs) (Vint Int.zero) = Some m'). {
    clear -AT Join Hwritable.
    unfold tlock in AT.
    destruct AT as (AT1, AT2).
    destruct AT2 as [A B]. clear A. (* it is 4 = 4 *)
    simpl in B. unfold mapsto_memory_block.at_offset in B.
    simpl in B. unfold nested_field_lemmas.nested_field_offset in B.
    simpl in B. unfold nested_field_lemmas.nested_field_type in B.
    simpl in B. unfold reptype_lemmas.default_val in B.
    simpl in B. unfold sublist.Znth in B.
    simpl in B. repeat rewrite Int.add_assoc in B.
    unfold data_at_rec_lemmas.data_at_rec in *.
    simpl in B.
    repeat rewrite add_repr in B.
    rewrite seplog.sepcon_emp in B. simpl in B.
    (* if array size > 4:
          destruct B as (phi00 & phi01 & jphi0 & B & _).
     *)
    unfold SeparationLogic.mapsto in *.
    simpl in B.
    destruct (readable_share_dec shx) as [n|n]. 2: now destruct n; apply writable_readable; auto.
    autorewrite with norm in B.
    rewrite !FF_orp in B.
    autorewrite with norm in B.
    destruct B as [v1' B]. 
    autorewrite with norm in B.
    destruct B as [v2' B]. 
    rewrite !TT_andp in B.
    apply mapsto_can_store with (v := v2') (sh := shx); try assumption.
    simpl (m_phi _).
    destruct B as [phi0a [phi0b [? [? ?]]]].
    destruct (join_assoc H Join) as [f [? ?]].
    exists phi0a, f; split; auto.
  }
  destruct Hm' as (m', Hstore).

  unfold tlock in *.
  match type of AT with context[Tarray _ ?n] => assert (Hpos' : (0 < n)%Z) by omega end.
  pose proof data_at_rmap_makelock CS as RL.
  specialize (RL shx b ofs Rx phi0 _ Hpos' Hwritable AT).
  destruct RL as (phi0' & RL0 & Hlkat).

  match type of Hlkat with context[LK_at _ ?n] => assert (Hpos'' : (0 < n)%Z) by (rewrite size_chunk_Mptr in *; destruct Archi.ptr64; omega) end.
  pose proof rmap_makelock_join _ _ _ _ _ _ _ Hpos'' RL0 Join as Hrmap.
  pose proof Hrmap as Hrmap_.
  destruct Hrmap_ as (phi' & RLphi & j').
  pose proof juice_join compat as j.
  rewrite join_all_joinlist in j.
  rewrite maps_getthread with (cnti0 := cnti) in j.
  destruct j as (psi & jpsi1 & jpsi).
  pose proof rmap_makelock_join _ _ _ _ _ _ _ Hpos'' RLphi jpsi as Hrmap'.
  destruct Hrmap' as (Phi' & Hrmap' & J').

  subst args.
  evar (tpx: jstate ge).
  eexists (m', (seq.cat tr (external i (mklock (b, Ptrofs.intval ofs)) :: nil), sch, tpx)); split.

  { (* "progress" part of the proof *)
    constructor.

    eapply JuicyMachine.sync_step
    with (Htid := cnti) (Hcmpt := mem_compatible_forget compat); auto.

    eapply step_mklock
    with (c := ci) (Hcompatible := mem_compatible_forget compat)
                   (R := Rx) (phi'0 := phi');
    try eassumption; try reflexivity.
    subst tpx; reflexivity.
  }
  subst tpx.

  (* we move on to the preservation part *)

  unfold personal_mem, m_phi.
  assert (Ephi : level (getThreadR _ _ cnti) = S n). {
    rewrite getThread_level with (Phi0 := Phi). auto. apply compat.
  }
  replace (level (getThreadR _ _ cnti) - 1)%nat with n by omega.

  (*
  assert (j : join_sub (getThreadR i tp cnti) Phi) by apply compatible_threadRes_sub, compat.
  destruct j as (psi & jphi).
  pose proof rmap_makelock_join _ _ _ _ _ _ _ Hpos Hrmap jphi as RL.
  *)

  assert (LPhi' : level Phi' = level Phi) by (destruct Hrmap'; auto).

  assert (notfound : lockRes tp (b, Ptrofs.intval ofs) = None). {
    specialize (lock_coh (b, Ptrofs.intval ofs)). cleanup.
    destruct (AMap.find _ _) as [o|] eqn:Eo. 2:reflexivity. exfalso.
    assert (C : exists (R : pred rmap), (lkat R (b, Ptrofs.intval ofs)) Phi)
      by (destruct o; breakhyps; eauto). clear lock_coh.
    destruct C as (R' & At).
    destruct Hrmap' as (_ & _ & inside & _).
    specialize (inside (b, Ptrofs.intval ofs)).
    spec inside. split; auto; unfold Ptrofs.unsigned in *; lkomega.
    destruct inside as (val' & sh'' & rsh'' & E & _).
    specialize (At (b, Ptrofs.intval ofs)). simpl in At.
    spec At. now split; auto; lkomega.
    destruct At as [sh [rsh  At]].
    progress breakhyps.
  }
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
    injection E''; intros <- <- <-.
    apply YES_inj in E''. exists p; simpl.
    split. apply YES_ext; reflexivity.
    rewrite level_age_to. 2:omega. reflexivity.
  }


  assert (mcompat' : mem_compatible_with' (age_tp_to n (updLockSet (updThread i tp cnti (Kresume ci Vundef) phi') (b, Ptrofs.intval ofs) None)) m' (age_to n Phi')). {
    constructor.
    + (* join_all *)
      (* rewrite <-Hpersonal_juice. autospec El. cleanup. rewrite El. *)
      apply join_all_age_to. cleanup. omega.
      rewrite join_all_joinlist.
      rewrite maps_updlock1.
      rewrite maps_remLockSet_updThread.
      rewrite maps_updthread.
      rewrite maps_getlock1. 2:assumption.
      exists psi; auto.

    + (* mem_cohere' *)
      split.
      * intros rsh sh v loc pp E''.
        destruct (adr_range_dec (b, Ptrofs.unsigned ofs) LKSIZE loc) as [r|nr].
        -- exfalso.
           destruct Hrmap' as (_ & _ & inside & _). specialize (inside loc).
           specialize (inside r).
           rewrite age_to_resource_at in E''.
           destruct inside as (? & ? & ? & ? & ? & E').
           rewrite E' in E''. simpl in E''; congruence.
        -- destruct (Phi'rev _ _ _ _ _ nr E'') as (pp' & E & ->).
           cut (contents_at m loc = v /\ pp' = NoneP).
           { intros []; split; subst pp'; auto.
             destruct loc as (b1, ofs1).
             destruct (store_outside' _ _ _ _ _ _ Hstore) as (outside & _ & _).
             specialize (outside b1 ofs1).
             destruct outside as [(->, r) | same].
             - exfalso. apply nr. split; auto.
                change Ptrofs.unsigned with Ptrofs.intval; lkomega.
             - rewrite <-same.
               unfold personal_mem.
               change (m_dry (mkJuicyMem ?m _ _ _ _ _)) with m.
               rewrite <-juicyRestrictContents. auto.
           }
           eapply (cont_coh (all_cohere compat)); eauto.

      * (* max_access_cohere' *)
        pose proof max_coh (all_cohere compat) as M.
        intros loc; specialize (M loc).
        rewrite perm_of_res'_age_to.
        clear Post.
        replace (max_access_at m' loc) with (max_access_at m loc); swap 1 2. {
          evar (m1 : mem).
          transitivity (max_access_at m1 loc); swap 1 2; subst m1.
          - unfold max_access_at in *.
            apply equal_f.
            apply equal_f.
            eapply store_access; eauto.
          - apply juicyRestrictMax.
        }
        exact_eq M. f_equal.
        destruct Hrmap' as (_ & Same & Changed & _).
        specialize (Same loc). specialize (Changed loc).
        destruct (adr_range_dec (b, Ptrofs.unsigned ofs) (4 * 2) loc) as [r|nr].
        -- autospec Changed.
           destruct Changed as (val & sh & rsh & ? & ? & ?).
           rewrite H; rewrite H1; reflexivity.
        -- autospec Same. rewrite <-Same.
           reflexivity.

      * (* alloc_cohere *)
        pose proof all_coh ((all_cohere compat)) as A.
        unfold alloc_cohere in *.
        destruct (store_outside' _ _ _ _ _ _ Hstore) as (_ & _ & <-).
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
      rewrite AMap_find_add.
      intros H ofs0 H0.
      rewrite (Mem.store_access _ _ _ _ _ _ Hstore).
      revert H ofs0 H0.
      intros H ofs0 H0.
      unfold personal_mem.
      change (m_dry (mkJuicyMem ?m _ _ _ _ _)) with m.
      pose proof juicyRestrictMax as RR.
      specialize RR _ _ _ (b', ofs0).
      unfold max_access_at in *.
      unfold access_at in *.
      simpl fst in RR. simpl snd in RR.
      rewrite <-RR. clear RR.
      revert H ofs0 H0.
      if_tac [e | ne].
      * injection e as <- <-.
        intros _ ofs0 r.
        pose proof all_cohere compat as C. destruct C as [_ C _].
        destruct Hrmap' as (_ & _ & inside & _).
        specialize (inside (b, ofs0)).
        specialize (C (b, ofs0)).
        spec inside. hnf. split. auto.
        clear - r. hnf in r. simpl in r. apply r.
        destruct inside as (val & sh & rsh & E & ? & ?).
        rewrite E in C.
        unfold max_access_at in *.
        eapply po_trans. eassumption.
        unfold perm_of_res' in *.
        unfold perm_of_sh in *.
        repeat if_tac; try constructor; tauto.
      * eapply loc_writable; eauto.

    + (* juicyLocks_in_lockSet *)
      intros loc E''. (*sh psh P z*)
      simpl in *.
      rewrite isSome_find_map.
      simpl.
      rewrite AMap_find_add. if_tac [<- | ne]. reflexivity.
      pose proof (jloc_in_set compat loc). 
      apply H.
      intros ? H0; specialize (E'' _ H0).
      destruct E'' as [sh [psh [P E'']]].
      destruct (rmap_unage_YES _ _ _ _ _ _ _ APhi' E'') as (pp, E').
      destruct Hrmap' as (_ & outside & inside & _).
      rewrite <- outside in E'. rewrite E'. eauto.
      change (size_chunk Mptr * 2) with LKSIZE in *.
      clear - Hpos I compat sparse lock_coh AT HnecR RL0 Hlkat RLphi j' jpsi1 jpsi J' notfound APhi' ne H0 E'.
      specialize (Hlkat (fst loc, snd loc + i0)).
      intro. rewrite if_true in Hlkat by apply H. destruct Hlkat as [?rsh Hlkat]. simpl in Hlkat.
      assert (join_sub phi0' Phi') by (eapply join_sub_trans; eexists; eassumption).
      apply (resource_at_join_sub _ _ (fst loc, snd loc + i0)) in H1.
      rewrite Hlkat, E' in H1. inv H1.
      destruct loc as [b0 ofs0]. simpl in *. destruct H. subst b0. assert (Ptrofs.intval ofs <> ofs0) by congruence.
      unfold Ptrofs.unsigned in *.
      inv H2. omega. omega.
    + (* lockSet_in_juicyLocks *)
      cleanup.
      pose proof lset_in_juice compat as J.
      intros loc. specialize (J loc).
      simpl.
      rewrite isSome_find_map.
      simpl.
      rewrite AMap_find_add.
      if_tac.
      * intros []. subst loc. change Ptrofs.intval with Ptrofs.unsigned in *.
         exists Share.Rsh. intros. simpl.
        destruct Hrmap' as (_ & _ & inside & _). specialize (inside (b, Ptrofs.unsigned ofs + i0)). spec inside.
        change (size_chunk Mptr * 2) with LKSIZE in *.
        { split; auto; omega. }
        simpl in inside|-*.
        destruct inside as [v [sh [rsh [? [? ?]]]]].
        exists sh, rsh.
        assert (exists P, age_to n Phi' @ (b, Ptrofs.unsigned ofs + i0) = YES sh rsh (LK LKSIZE i0) P).
        2:{ destruct H3 as [P ?]; exists P; split; auto. }
        rewrite age_to_resource_at.
        breakhyps.
        rewr (Phi' @ (b, Ptrofs.unsigned ofs + i0)). simpl.
        eexists. change (size_chunk Mptr * 2) with LKSIZE in *.
        replace (Ptrofs.unsigned ofs + i0 - Ptrofs.unsigned ofs) with i0 by omega. reflexivity.
      * intros tr0. specialize (J tr0). destruct J as [sh ?].
        destruct Hrmap' as (_ & outside & inside & _).
        exists sh. intros.
        specialize (outside (fst loc, snd loc + i0)).
        spec outside.
        { intros r. destruct loc as [b0 ofs0]; simpl in *; change (size_chunk Mptr * 2) with LKSIZE in *.
           destruct r; subst b0. specialize (inside (b,ofs0+i0)). spec inside; auto.
            destruct inside as [v [sh' [rsh' [? _]]]].
           specialize (H0 i0). destruct H0 as [sh8 [psh8 [P' [? ?]]]]. pose proof LKSIZE_pos; omega.
           congruence.
       }
       destruct (H0 _ H1) as [sh' [psh' [P [? ?]]]]. rewrite outside in H3.
       exists sh', psh'; eexists; split; try eassumption.
       rewrite age_to_resource_at. rewrite H3. reflexivity.
  }
  assert (sparse' :
            lock_sparsity
              (lset (age_tp_to n (updLockSet
                                    (updThread i tp cnti (Kresume ci Vundef) phi')
                                    (b, Ptrofs.intval ofs) None)))).
  {
    simpl.
    cleanup.
    unfold lock_sparsity in *.
    cut (forall loc, AMap.find loc (lset tp) <> None ->
                loc = (b, Ptrofs.intval ofs) \/ fst loc <> b \/ fst loc = b /\ far (snd loc) (Ptrofs.intval ofs)). {
      clear -sparse.
      intros H loc1 loc2.
      do 2 rewrite AMap_find_map_option_map. cleanup.
      do 2 rewrite AMap_find_add.
      if_tac [<- | ne1]; if_tac [<- | ne2]; simpl.
      - auto.
      - intros _ found2.
        specialize (H loc2). spec H. destruct (AMap.find loc2 _); auto; congruence.
        breakhyps. right. right. split; auto. unfold far in *; auto. zify. omega.
      - intros found1 _.
        specialize (H loc1). spec H. destruct (AMap.find loc1 _); auto; congruence.
        auto.
      - intros found1 found2.
        specialize (sparse loc1 loc2).
        spec sparse. destruct (AMap.find loc1 _); auto; congruence.
        spec sparse. destruct (AMap.find loc2 _); auto; congruence.
        auto.
    }
    intros loc found. right.
    specialize (lock_coh loc). destruct (AMap.find loc _) as [o|] eqn:Eo. clear found. 2:congruence.
    assert (coh : exists (R : pred rmap), (lkat R loc) Phi)
      by (destruct o; breakhyps; eauto). clear lock_coh.
    destruct coh as (R' & AT').
    pose proof AT' as AT''.
    specialize (AT' loc).
    destruct Hrmap' as (_ & outside & inside & _).
    spec AT'. destruct loc; split; auto; lkomega.
    specialize (outside loc). assert_specialize outside as nr. {
      intros r. specialize (inside loc r).
      breakhyps.
    }
    unfold far.
    destruct loc as (b', ofs'). simpl. simpl in nr.
    unfold Ptrofs.unsigned in *.
    destruct (eq_dec b b') as [<- | ?]; [ | now auto ].
    right; split; auto.
    specialize (AT'' (b, Ptrofs.intval ofs)).
    specialize (inside (b, Ptrofs.intval ofs)). spec inside. now split; auto; lkomega.
    destruct (adr_range_dec (b, ofs') LKSIZE (b, Ptrofs.intval ofs)) as [r|nr'].
    + autospec AT''. breakhyps.
    + clear -nr nr'. simpl in nr'. unfold LKSIZE in *.
      do 2 match goal with H : ~(b = b /\ ?P) |- _ => assert (~P) by tauto; clear H end.
      zify. omega.
  }
  left.
  unshelve erewrite updLock_updThread_comm in mcompat', sparse' |- *; try (apply cntUpdateL; auto).
  unshelve erewrite age_to_updThread in mcompat', sparse' |- *; try (apply cnt_age', cntUpdateL; auto).
  apply state_invariant_c with (PHI := age_to n Phi') (mcompat := mcompat').
  - (* level *)
    apply level_age_to. omega.

  - (* env_coherence *)
    apply env_coherence_age_to.
    apply env_coherence_pures_eq with Phi; auto. omega.
    apply pures_same_pures_eq. auto.
    eapply rmap_makelock_pures_same; eauto.

  - rewrite age_to_ghost_of.
    destruct Hrmap' as (? & ? & ? & <-).
    destruct extcompat as [? J]; eapply ghost_fmap_join in J; eexists; eauto.

  - (* lock sparsity *)
    apply sparse'.

  - (* lock coherence *)
    unfold lock_coherence'.
    (* Have we not proved that before? Not exactly: lock_coherence
    talks about the dry memory, which is defined as the restrPermMap
    of something that uses mem_compatible, which in turn uses the lock
    coherence above *)
    simpl.
    intros loc.
    rewrite AMap_find_map_option_map.
    rewrite AMap_find_add.
    if_tac.
    + split.
      * (* load_at *)
        unfold load_at. subst loc.
        clear -Hstore AT.
        apply Mem.load_store_same in Hstore.
        Transparent Mem.load.
        unfold Mem.load in *. simpl fst in *; simpl snd in *.
        if_tac [va|nva];swap 1 2.
        {
          destruct nva. simpl.
          apply islock_valid_access. destruct AT as [(_ & _ & _ & AT & _) _]. inv AT; try discriminate. lapply (H3 0%Z); [|omega]. rewrite Z.mul_0_r, Z.add_0_r. intro X; inv X. inv H; auto.
          2:congruence.
          cleanup.
          setoid_rewrite AMap_find_map_option_map.
          rewrite AMap_find_add. if_tac. 2:tauto.
          simpl; congruence.
        }
        rewrite restrPermMap_mem_contents.
        if_tac in Hstore. 2:discriminate.
        auto.

      * (* LK_at *)
        subst loc. simpl.
        split. destruct AT as [(_ & _ & _ & AT & _) _]. inv AT; try discriminate. lapply (H3 0%Z); [|omega]. rewrite Z.mul_0_r, Z.add_0_r. intro X; inv X. inv H; auto.
        split.
        destruct AT as [(_ & _ & H5 & _) _]; simpl in H5.
        unfold LKSIZE; rewrite size_chunk_Mptr; unfold Ptrofs.unsigned in *; omega.
        exists Rx.
        intros loc r.
        destruct Hrmap' as (_ & _ & inside & _). specialize (inside loc).
        spec inside. clear - r. apply r.
        rewrite age_to_resource_at.
        breakhyps.
        rewr (Phi' @ loc).
        unfold Ptrofs.unsigned in *.
        change (size_chunk Mptr * 2) with LKSIZE in *.
           unfold sync_preds_defs.pack_res_inv in *.
           simpl.
           eexists x0, x1.
           f_equal. f_equal. extensionality Ts.
           eauto.
           rewrite level_age_to. 2:omega.
           apply approx_approx'. omega.

    + specialize (lock_coh loc).
      destruct (AMap.find loc _) as [o|] eqn:Eo.
      * destruct loc as (b', ofs'). simpl fst; simpl snd.
        assert (VAEQ :
                  Mem.valid_access
                    (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget compat)))
                    Mint32 b' ofs' Readable =
                  Mem.valid_access
                    (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget mcompat')))
                    Mint32 b' ofs' Readable).
        {
          unfold Mem.valid_access in *. f_equal.
          unfold Mem.range_perm in *.
          extensionality ofs0 r0.
          unfold Mem.perm in *.
          pose proof restrPermMap_Cur as RR.
          unfold permission_at in *.
          f_equal.
          rewrite RR.
          rewrite RR.
          unfold lockSet.
          simpl.
          cleanup.
          setoid_rewrite A2PMap_option_map.
          symmetry.
          (* use lock sparsity again *)
          rewrite A2PMap_add_outside.
          if_tac. 2:reflexivity.
          change (Some Writable = (lockSet tp) !! b' ofs0).
          symmetry. apply lockSet_spec_2 with ofs'.
          unfold LKSIZE_nat; rewrite Z2Nat.id by (pose proof LKSIZE_pos; omega).
          clear - r0; hnf; simpl in *; lkomega.
          cleanup. rewrite Eo. reflexivity.
        }

        destruct o; unfold option_map; destruct lock_coh as (load & coh); split; swap 2 3.
        -- rewrite <-load.
           unfold load_at.
           unfold Mem.load. simpl fst; simpl snd.
           symmetry.
           if_tac [va|nva]; if_tac [va'|nva'].
           ++ do 2 rewrite restrPermMap_mem_contents.
              simpl.
              cut (forall z, (ofs' <= z < ofs' + 4)%Z ->
                        ZMap.get z (Mem.mem_contents m) !! b' =
                        ZMap.get z (Mem.mem_contents m') !! b').
              { intros C. f_equal. f_equal.
                f_equal. apply C. omega.
                f_equal. apply C. omega.
                f_equal. apply C. omega.
                f_equal. apply C. omega. }
              intros z rz.
              pose proof store_outside' _ _ _ _ _ _ Hstore as Hm'.
              destruct Hm' as (Hm', _).
              specialize (Hm' b' z).
              unfold contents_at in *.
              simpl in Hm'.
              destruct Hm' as [r1 | a]. 2:exact a.
              destruct r1 as [<- r1]. exfalso.
              specialize (sparse' (b, ofs') (b, Ptrofs.intval ofs)).
              simpl in sparse'. cleanup.
              do 2 rewrite AMap_find_map_option_map in sparse'.
              do 2 rewrite AMap_find_add in sparse'.
              if_tac [e | _] in sparse'.  tauto.
              if_tac [_ | ne] in sparse'. 2:tauto.
              spec sparse'. rewrite Eo. simpl. congruence.
              spec sparse'. simpl. congruence.
              destruct sparse' as [e | [ne | [_ Far]]]. congruence. tauto.
              clear -rz H Far r1.
              unfold far in Far.
              zify.
              lkomega.

           ++ rewrite VAEQ in va. tauto.
           ++ rewrite VAEQ in nva. tauto.
           ++ reflexivity.

        -- rewrite <-load.
           unfold load_at.
           unfold Mem.load. simpl fst; simpl snd.
           symmetry.
           if_tac [va|nva]; if_tac [va'|nva'].
           ++ do 2 rewrite restrPermMap_mem_contents.
              simpl.
              cut (forall z, (ofs' <= z < ofs' + 4)%Z ->
                        ZMap.get z (Mem.mem_contents m) !! b' =
                        ZMap.get z (Mem.mem_contents m') !! b').
              { intros C. f_equal. f_equal.
                f_equal. apply C. omega.
                f_equal. apply C. omega.
                f_equal. apply C. omega.
                f_equal. apply C. omega. }
              intros z rz.
              pose proof store_outside' _ _ _ _ _ _ Hstore as Hm'.
              destruct Hm' as (Hm', _).
              specialize (Hm' b' z).
              unfold contents_at in *.
              simpl in Hm'.
              destruct Hm' as [r1 | a]. 2:exact a.
              destruct r1 as [<- r1]. exfalso.
              specialize (sparse' (b, ofs') (b, Ptrofs.intval ofs)).
              simpl in sparse'. cleanup.
              do 2 rewrite AMap_find_map_option_map in sparse'.
              do 2 rewrite AMap_find_add in sparse'.
              if_tac [e | _] in sparse'.  tauto.
              if_tac [_ | ne] in sparse'. 2:tauto.
              spec sparse'. rewrite Eo. simpl. congruence.
              spec sparse'. simpl. congruence.
              destruct sparse' as [e | [ne | [_ Far]]]. congruence. tauto.
              clear -rz H Far r1.
              unfold far in Far.
              zify.
              lkomega.
           ++ rewrite VAEQ in va. tauto.
           ++ rewrite VAEQ in nva. tauto.
           ++ reflexivity.

        -- (* lkat *)
           destruct coh as (align & bound & R & lk & sat).
           split; auto.
           split; auto.
           exists R. split.
           ++ apply age_to_ind. now apply lkat_hered.
              destruct Hrmap' as (LPhi & outside & inside & _).
              intros x rx. specialize (lk x rx).
              specialize (outside x).
              specialize (inside x).
              spec outside.
              { intros r2. specialize (inside r2). breakhyps. }
              rewrite <-outside.
              rewrite LPhi'.
              eauto.
           ++ destruct sat as [sat | ?]. 2:omega. left.
              unfold age_to. replace (level r) with (level Phi); swap 1 2.
              { symmetry. apply join_sub_level. eapply compatible_lockRes_sub; simpl; eauto. apply compat. }
              rewr (level Phi). replace (S n - n)%nat with 1%nat by omega.
              apply age_by_ind. destruct R as [x h]. apply h. apply sat.

        -- (* lkat *)
           destruct coh as (align & bound & R & lk). repeat (split; auto). exists R.
           apply age_to_ind. now apply lkat_hered.
           destruct Hrmap' as (LPhi & outside & inside & _).
           intros x r. specialize (lk x r).
           specialize (outside x).
           specialize (inside x).
           spec outside.
           { intros r2. specialize (inside r2). breakhyps. }
           rewrite <-outside.
           rewrite LPhi'.
           eauto.

      * unfold option_map.
        destruct (adr_range_dec (b, Ptrofs.unsigned ofs) LKSIZE loc) as [r|nr].
        -- destruct Hrmap' as (_ & _ & inside & _).
           specialize (inside loc r).
           rewrite isLK_age_to.
           destruct inside as [? [? [? [? [? inside]]]]].
           rewrite inside. intro. hnf in H2. destruct H2 as [? [? [? [? H2]]]]; inv H2.
           clear - H r H6. destruct loc; destruct r; simpl in *; subst. contradiction H.  f_equal.
           unfold Ptrofs.unsigned in *; omega.
        -- destruct Hrmap' as (_ & outside & _).
           rewrite age_to_resource_at.
           specialize (outside loc nr).
           rewrite <-outside.
           clear -lock_coh.
           contradict lock_coh. destruct lock_coh as [? [? [? [? ?]]]].
           destruct (Phi @ loc); inv H. do 4 eexists; eauto.

  - (* safety *)
    {
    intros j cntj ?; destruct (eq_dec i j).
    + subst j; rewrite gssThreadCode, gssThreadRes; intros ? Hc' ? Hjm.
      destruct Post with
          (ret := @None val)
            (m' := jm)
            (z' := tt) (n' := n) as (c'' & Ec'' & Safe'); auto.
      { apply Logic.I. }
      { unfold Hrel.
        assert (level phi' = S n) as Hl' by (destruct (join_level _ _ _ J'); omega).
        rewrite level_jm_, m_phi_jm_, level_juice_level_phi, Hjm, level_age_to by (setoid_rewrite Hl'; auto).
        split; auto; split; [setoid_rewrite En; auto|].
        eapply pures_same_eq_l.
        2:apply pures_eq_age_to; omega.
        eapply pures_same_sym, rmap_makelock_pures_same; eauto. }
      { (* we must satisfy the post condition *)
        exists (age_to n phi0'), (age_to n phi1).
        rewrite Hjm.
        split.
        * apply age_to_join; auto.
        * split. 2: now eapply necR_trans; [ eassumption | apply age_to_necR ].
          split. now constructor.
          split. now constructor.
          simpl. rewrite seplog.sepcon_emp.
          unfold semax_conc_pred.lock_inv in *.
          exists b, ofs; split. auto.
          destruct RL0 as (Lphi0 & outside & inside & Hg).
          split.
          intros loc. simpl.
          pose proof data_at_unfold _ _ _ _ _ 2 Hwritable AT as Hbefore.
          specialize (Hbefore loc).
          if_tac [r|nr].
          - exists ((writable_readable_share Hwritable)).
            specialize (inside loc r).            
            destruct inside as (val & sh & rsh & E & wsh & E').
            if_tac in Hbefore. 2:tauto.
            rewrite age_to_resource_at.
            destruct Hbefore as (v, Hb). rewrite Hb in E.
            injection E as -> <-.
            rewrite E'. simpl.
            unfold pfullshare.
            rewrite approx_approx'. 2: join_level_tac; omega.
            rewrite level_age_to.  2: join_level_tac; omega.
            apply YES_ext.
            reflexivity.
          - if_tac in Hbefore. tauto.
            specialize (outside loc).
            specialize (outside nr).
            rewrite age_to_resource_at, <-outside.
            apply empty_NO in Hbefore.
            destruct Hbefore as [-> | (? & ? & ->)]; simpl.
            + apply NO_identity.
            + apply PURE_identity.
          - simpl; rewrite age_to_ghost_of, <- Hg.
            apply data_at_noghost in AT.
            rewrite (identity_core AT), ghost_core; simpl.
            rewrite <- (ghost_core (ghost_of phi0)); apply core_identity. }
      rewrite Hc' in Ec''; inv Ec''; destruct ora; auto.
    + unshelve erewrite gsoThreadCode, gsoThreadRes, <- gtc_age, gLockSetCode, <- getThreadR_age,
        gLockSetRes; auto.
      specialize (safety j cntj ora).
      destruct (getThreadC j tp cntj) eqn: Hget.
      * edestruct (unique_Krun_neq(ge := ge) i j); eauto.
      * apply jsafe_phi_age_to; auto. apply jsafe_phi_downward. assumption.
      * intros ? Hc'; apply jsafe_phi_bupd_age_to; auto. apply jsafe_phi_bupd_downward. auto.
      * destruct safety as (? & q_new & Einit & safety).
        split; [erewrite Mem.nextblock_store by eauto; auto|].
        exists q_new; split; auto.
        apply jsafe_phi_age_to; auto. apply jsafe_phi_downward, safety. }

  - (* threads_wellformed *)
    intros j lj.
    specialize (wellformed j lj).
    destruct (eq_dec i j).
    + subst j.
      rewrite gssThreadCode.
      replace lj with cnti in wellformed by apply proof_irr.
      rewr (getThreadC i tp cnti) in wellformed.
      auto.
    + unshelve erewrite gsoThreadCode; auto.

  - (* unique_Krun *)
    apply no_Krun_unique_Krun.
    apply no_Krun_stable. congruence.
    rewrite no_Krun_age_tp_to.
    apply no_Krun_updLockSet.
    eapply unique_Krun_no_Krun. eassumption.
    instantiate (1 := cnti). rewr (getThreadC i tp cnti).
    congruence.
Qed.
