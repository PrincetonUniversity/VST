Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import msl.Coqlib2.
Require Import msl.eq_dec.
Require Import msl.seplog.
Require Import veric.initial_world.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.semax_prog.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import veric.semax.
Require Import veric.semax_ext.
Require Import veric.juicy_extspec.
Require Import veric.juicy_safety.
Require Import veric.initial_world.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.semax_ext.
Require Import veric.res_predicates.
Require Import veric.mem_lessdef.
Require Import veric.shares.
Require Import floyd.coqlib3.
Require Import floyd.field_at.
Require Import sepcomp.semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.event_semantics.
Require Import sepcomp.semantics_lemmas.
Require Import concurrency.coqlib5.
Require Import concurrency.permjoin.
Require Import concurrency.semax_conc.
Require Import concurrency.juicy_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.
Require Import concurrency.addressFiniteMap.
Require Import concurrency.permissions.
Require Import concurrency.JuicyMachineModule.
Require Import concurrency.age_to.
Require Import concurrency.sync_preds_defs.
Require Import concurrency.sync_preds.
Require Import concurrency.join_lemmas.
Require Import concurrency.aging_lemmas.
Require Import concurrency.cl_step_lemmas.
Require Import concurrency.resource_decay_lemmas.
Require Import concurrency.resource_decay_join.
Require Import concurrency.semax_invariant.
Require Import concurrency.semax_simlemmas.
Require Import concurrency.sync_preds.
Require Import concurrency.lksize.
Require Import concurrency.rmap_locking.
Require Import concurrency.semax_conc_pred.

Local Arguments getThreadR : clear implicits.
Local Arguments getThreadC : clear implicits.
Local Arguments personal_mem : clear implicits.
Local Arguments updThread : clear implicits.
Local Arguments updThreadR : clear implicits.
Local Arguments updThreadC : clear implicits.
Local Arguments juicyRestrict : clear implicits.

Set Bullet Behavior "Strict Subproofs".

Open Scope string_scope.

(* to make the proof faster, we avoid unfolding of those definitions *)
Definition Jspec'_juicy_mem_equiv_def CS ext_link :=
  ext_spec_stable juicy_mem_equiv (JE_spec _ ( @OK_spec (Concurrent_Espec unit CS ext_link))).

Definition Jspec'_hered_def CS ext_link :=
   ext_spec_stable age (JE_spec _ ( @OK_spec (Concurrent_Espec unit CS ext_link))).

(* Weaker statement than preservation for freelock, enough to prove safety *)
Lemma safety_induction_freelock Gamma n state
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
    state_step state state' /\
    (state_invariant Jspec' Gamma n state' \/
     state_invariant Jspec' Gamma (S n) state').
Proof.
  assert (Hpos : (0 < LKSIZE)%Z) by reflexivity.
  intros isfreelock.
  intros I.
  inversion I as [m ge sch_ tp Phi En gam compat sparse lock_coh safety wellformed unique E]. rewrite <-E in *.
  unfold blocked_at_external in *.
  destruct isfreelock as (i & cnti & sch & ci & args & -> & Eci & atex).
  pose proof (safety i cnti tt) as safei.
  
  rewrite Eci in safei.
  unfold jsafeN, juicy_safety.safeN in safei.
  
  inversion safei
    as [ | ?????? bad | n0 z c m0 e args0 x at_ex Pre SafePost | ????? bad ];
    [ now erewrite cl_corestep_not_at_external in atex; [ discriminate | eapply bad ]
    | subst | now inversion bad ].
  subst.
  simpl in at_ex. assert (args0 = args) by congruence; subst args0.
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
  destruct Pre as (phi0 & phi1 & Join & Precond & HnecR).
  simpl (and _).
  intros Post.
  
  destruct Precond as [[Hwritable [Hpositive [Hprecise _]]] [[B1 _] AT]].
  assert (Hreadable : readable_share shx) by (apply writable_readable; auto).
  
  (* [data_at_] from the precondition *)
  unfold canon.SEPx in *.
  simpl in AT.
  rewrite seplog.sepcon_emp in AT.
  
  (* value of [vx] *)
  simpl in B1.
  unfold lift, liftx in B1. simpl in B1.
  unfold lift, liftx in B1. simpl in B1.
  rewrite lockinv_isptr in AT.
  rewrite log_normalize.sepcon_andp_prop' in AT.
  destruct AT as (IsPtr, AT).
  destruct vx as [ | | | | | b ofs ]; try inversion IsPtr; [ clear IsPtr ].
  
  assert (Eargs : args = Vptr b ofs :: nil)
    by (eapply shape_of_args; eauto).
  
  destruct AT as (phi0lockinv & phi0sat & jphi0 & Hlockinv & Hsat).
  
  assert (locked : lockRes tp (b, Int.intval ofs) = Some None). {
    (* TODO : use preciseness and positivity here *)
    spec lock_coh (b, Int.intval ofs). cleanup.
    destruct (AMap.find _ _) as [[phi_sat|]|] eqn:Ephi_sat; [ exfalso | reflexivity | exfalso ].
    - (* positive and precise *)
      destruct lock_coh as (_&_&_&R&lk&[sat|?]). 2:omega.
      
      assert (J0 : join_sub phi0 Phi). {
        apply join_sub_trans with (getThreadR i tp cnti). eexists; eauto.
        join_sub_tac.
      }
      assert (Ja0 : join_sub phi0sat Phi).  {
        apply join_sub_trans with phi0; eauto. eexists; eauto.
      }
      assert (Ja : join_sub phi_sat Phi). {
        eapply compatible_lockRes_sub; eauto.
        apply compat.
      }
      assert (J01 : join_sub phi0lockinv Phi). {
        apply join_sub_trans with phi0. eexists; eauto.
        apply join_sub_trans with (getThreadR i tp cnti). eexists; eauto.
        join_sub_tac.
      }
      assert (R01 : level phi0lockinv = level Phi) by join_level_tac.
      assert (Ra : level phi_sat = level Phi) by join_level_tac.
      assert (Ra0 : level phi0sat = level Phi) by join_level_tac.
      pose proof predat6 lk as E1.
      pose proof predat4 Hlockinv as E3.
      apply (predat_join_sub J01) in E3.
      
      pose proof positive_precise_joins_false
           (approx (level Phi) (Interp Rx)) (age_by 1 phi_sat) (age_by 1 phi0sat) as PP.
      apply PP.
      + (* positive *)
        apply positive_approx with (n := level Phi) in Hpositive.
        assumption.
        
      + (* precise *)
        unfold approx.
        apply precise_approx with (n := level Phi) in Hprecise.
        assumption.
      
      + (* sat 1 *)
        split.
        * rewrite level_age_by. rewrite Ra. omega.
        * revert sat.
          apply approx_eq_app_pred with (level Phi).
          -- rewrite level_age_by. rewr (level phi_sat). omega.
          -- eapply predat_inj; eauto.
             apply predat6 in lk; eauto.
             exact_eq E3. f_equal. f_equal. auto.
             
      + (* sat 2 *)
        split.
        -- rewrite level_age_by. cut (level phi0sat = level Phi). omega. join_level_tac.
        -- (* cut (app_pred (Interp Rx) (age_by 1 phi0sat)).
           ++ apply approx_eq_app_pred with (S n).
              ** rewrite level_age_by. rewrite Ra0. omega.
              ** pose proof (predat_inj E1 E3) as G.
                 exact_eq G; do 2 f_equal; auto.
                 omega.
           ++ *)
           revert Hsat. apply age_by_ind.
           destruct (Interp Rx).
           auto.
              
      + (* joins *)
        apply age_by_joins.
        apply joins_sym.
        eapply @join_sub_joins_trans with (c := phi0); auto. apply Perm_rmap.
        * exists phi0lockinv. apply join_comm. auto.
        * eapply @join_sub_joins_trans with (c := getThreadR i tp cnti); auto. apply Perm_rmap.
          -- exists phi1. auto.
          -- eapply compatible_threadRes_lockRes_join. apply (mem_compatible_forget compat).
             apply Ephi_sat.
    
    - (* not a lock: impossible *)
      simpl in Hlockinv.
      unfold lock_inv in *.
      destruct Hlockinv as (b_ & ofs_ & E_ & HH).
      spec HH (b, Int.intval ofs).
      simpl in HH.
      change Int.intval with Int.unsigned in *.
      injection E_ as <- <- .
      if_tac [r|nr] in HH. 2:range_tac.
      if_tac [e|ne] in HH. 2:tauto.
      destruct HH as (p & HH).
      assert (j : join_sub phi0lockinv Phi). {
        apply join_sub_trans with phi0. eexists; eauto.
        apply join_sub_trans with (getThreadR i tp cnti). eexists; eauto.
        join_sub_tac.
      }
      destruct j as (psi & j).
      apply resource_at_join with (loc := (b, Int.unsigned ofs)) in j.
      rewrite HH in j.
      apply lock_coh.
      inv j; hnf; eauto.
  }
  
  spec lock_coh (b, Int.intval ofs). cleanup. rewrite locked in lock_coh.
  
  unfold tlock in *.
  apply (lock_inv_rmap_freelock CS) with (m := m) in Hlockinv; auto; try apply lock_coh.
  destruct Hlockinv as (phi0lockinv' & Hrmap00 & Hlkat).
  
  assert (Hpos'' : (0 < 4)%Z) by omega.
  pose proof rmap_freelock_join _ _ _ _ _ _ _ _ Hpos'' Hrmap00 jphi0 as Hrmap0.
  destruct Hrmap0 as (phi0' & Hrmap0 & jphi0').
  pose proof rmap_freelock_join _ _ _ _ _ _ _ _ Hpos'' Hrmap0 Join as Hrmap.
  pose proof Hrmap as Hrmap_.
  destruct Hrmap_ as (phi' & RLphi & j').
  assert (ji : join_sub (getThreadR _ _ cnti) Phi) by join_sub_tac.
  destruct ji as (psi & jpsi). cleanup.
  pose proof rmap_freelock_join _ _ _ _ _ _ _ _ Hpos'' RLphi jpsi as Hrmap'.
  destruct Hrmap' as (Phi' & Hrmap' & J').
  
  subst args.
  
  eexists (m, ge, (sch, _)); split.
  
  { (* "progress" part of the proof *)
    constructor.
    
    eapply JuicyMachine.sync_step
    with (Htid := cnti); auto.
    
    eapply step_freelock
    with (c := ci) (Hcompat := mem_compatible_forget compat)
                   (R := Interp Rx) (phi'0 := phi').
    all: try reflexivity.
    all: try eassumption.
    unfold SEM.Sem in *. rewrite SEM.CLN_msem. eassumption.
    apply (mem_compatible_forget compat).
  }
  
  (* we move on to the preservation part *)
  
  simpl (m_phi _).
  assert (Ephi : level (getThreadR _ _ cnti) = S n). {
    rewrite getThread_level with (Phi := Phi). auto. apply compat.
  }
  assert (El : level (getThreadR _ _ cnti) - 1 = n) by omega.
  cleanup.
  rewrite El.
  
  assert (LPhi' : level Phi' = level Phi) by (destruct Hrmap'; auto).
  
  assert (APhi' : age Phi' (age_to n Phi')) by (apply age_to_1; congruence).
  
  assert (Phi'rev : forall sh psh k pp' loc,
             ~adr_range (b, Int.unsigned ofs) LKSIZE loc ->
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
    injection E''; intros <- <- <- <- ; eexists; split. reflexivity.
    rewrite level_age_to. 2:omega. reflexivity.
  }
  
  assert (mcompat' : mem_compatible_with' (age_tp_to n (remLockSet (updThread i tp cnti (Kresume ci Vundef) phi') (b, Int.intval ofs))) m (age_to n Phi')).
  {
    constructor.
    + (* join_all *)
      (* rewrite <-Hpersonal_juice. autospec El. cleanup. rewrite El. *)
      apply join_all_age_to. cleanup. omega.
      pose proof juice_join compat as j.
      rewrite join_all_joinlist.
      rewrite join_all_joinlist in j.
      rewrite maps_remLockSet_updThread.
      rewrite maps_updthread.
      rewrite <-(maps_getlock2 _ (b, Int.unsigned ofs)) in j. 2:eassumption.
      assert (cnti' : containsThread (remLockSet tp (b, Int.unsigned ofs)) i) by auto.
      rewrite maps_getthread with (i := i) (cnti := cnti') in j.
      change Int.intval with Int.unsigned.
      clear Post B1.
      eapply (joinlist_merge phi0' phi1). apply j'.
      apply join_comm in jphi0'.
      eapply (joinlist_merge _ phi0lockinv' phi0'). apply jphi0'.
      REWR in j.
      rewrite <-joinlist_merge in j. 2: apply Join.
      rewrite <-joinlist_merge in j. 2: apply jphi0.
      rewrite joinlist_swap.
      destruct j as (xi_ & jxi_ & jx1).
      pose proof rmap_freelock_join _ _ _ _ _ _ _ _ Hpos'' Hrmap00 jx1 as Hrmap1.
      destruct Hrmap1 as (Phi'_ & Hrmap'_ & J).
      assert (Phi'_ = Phi') by (eapply rmap_freelock_unique; eauto). subst Phi'_.
      exists xi_. auto.
    
    + (* mem_cohere' *)
      split.
      * intros rsh sh v loc pp E''.
        destruct (adr_range_dec (b, Int.unsigned ofs) LKSIZE loc) as [r|nr].
        -- destruct Hrmap' as (_ & _ & inside). spec inside loc. autospec inside.
           rewrite age_to_resource_at in E''.
           destruct inside as (? & E' & E).
           rewrite E' in E''. simpl in E''.
           injection E'' as <- <- <- <-.
           split; auto.
        -- destruct (Phi'rev _ _ _ _ _ nr E'') as (pp' & E & ->).
           cut (contents_at m loc = v /\ pp' = NoneP).
           { intros []; split; subst pp'; auto. }
           eapply (cont_coh (all_cohere compat)); eauto.
      
      * (* max_access_cohere' *)
        pose proof max_coh ( all_cohere compat) as M.
        intros loc; spec M loc.
        rewrite perm_of_res'_age_to.
        clear Post.
        exact_eq M. f_equal.
        destruct Hrmap' as (_ & Same & Changed).
        spec Same loc. spec Changed loc.
        destruct (adr_range_dec (b, Int.unsigned ofs) (4 * 1) loc) as [r|nr].
        -- autospec Changed.
           destruct Changed as (val & -> & ->).
           if_tac; reflexivity.
        -- autospec Same. rewrite <-Same.
           reflexivity.
      
      * (* alloc_cohere *)
        pose proof all_coh ((all_cohere compat)) as A.
        unfold alloc_cohere in *.
        intros loc out.
        destruct Hrmap' as (_ & outside & inside).
        spec outside loc.
        spec outside.
        { destruct loc as (b', ofs').
          intros [<- _].
          spec A (b, Int.intval ofs) out.
          spec inside (b, Int.unsigned ofs).
          spec inside. split; auto. lkomega.
          unfold Int.unsigned in *.
          if_tac in inside;
          breakhyps. }
        spec A loc out.
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
      intros loc sh psh P z E''.
      unfold lockGuts in *.
      rewrite lset_age_tp_to.
      rewrite isSome_find_map.
      simpl.
      rewrite AMap_find_remove. if_tac [<- | ne].
      * exfalso.
        destruct Hrmap' as (_ & outside & inside).
        spec inside (b, Int.intval ofs). spec inside. now split; auto; unfold Int.unsigned; omega.
        if_tac in inside; breakhyps.
        rewrite age_to_resource_at in E''.
        rewr (Phi' @ (b, Int.intval ofs)) in E''.
        discriminate.
      * destruct (rmap_unage_YES _ _ _ _ _ _ _ APhi' E'') as (pp, E').
        cut (Phi @ loc = YES sh psh (LK z) pp).
        { intros; eapply (jloc_in_set compat); eauto. }
        rewrite <-E'.
        destruct Hrmap' as (_ & outside & inside).
        apply outside.
        intros r.
        spec inside loc r.
        destruct inside as (val & E1' & E1).
        rewrite E1' in E'.
        congruence.
    
    + (* lockSet_in_juicyLocks *)
      cleanup.
      pose proof lset_in_juice compat as J.
      intros loc. spec J loc.
      simpl.
      rewrite isSome_find_map.
      simpl.
      rewrite AMap_find_remove.
      if_tac.
      * discriminate.
      * intro IS; spec J IS.
        destruct Hrmap' as (_ & outside & inside). spec inside loc. spec outside loc.
        destruct (adr_range_dec (b, Int.unsigned ofs) 4 loc).
        -- autospec inside. exfalso.
           if_tac in inside; breakhyps.
        -- autospec outside. rewrite outside in J.
           rewrite age_to_resource_at. breakhyps.
           rewr (Phi' @ loc). simpl; eauto.
  }
  
  left.
  unshelve eapply state_invariant_c with (PHI := age_to n Phi') (mcompat := mcompat').
  - (* level *)
    apply level_age_to. omega.
  
  - (* matchfunspec *)
    apply matchfunspec_age_to.
    eapply matchfunspec_common_join with (Phi := Phi); eauto.
  
  - (* lock sparsity *)
    apply lock_sparsity_age_to.
    clear -sparse.
    intros loc1 loc2. cleanup. simpl. do 2 rewrite AMap_find_remove.
    spec sparse loc1 loc2.
    if_tac; if_tac; eauto.
  
  - (* lock coherence *)
    unfold lock_coherence'.
    simpl.
    intros loc.
    rewrite AMap_find_map_option_map.
    rewrite AMap_find_remove.
    if_tac; simpl.
    + destruct Hrmap' as (_ & _ & inside). 
      spec inside loc. subst loc. rewrite isLK_age_to.
      spec inside. split; auto; unfold Int.unsigned in *; omega.
      unfold Int.unsigned in *.
      destruct inside as (sh & -> & ?). intros HH.
      unfold isLK in *. breakhyps.
    + admit (* continuing lock coh ... *).
  
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
        rewrite Eci in safety.
        specialize (wellformed i cnti).
        rewrite Eci in wellformed.
        intros c' Ec'.
        - (* at_external : we can now use safety *)
          destruct Post with
          (ret := @None val)
            (m' := jm_ lj mcompat')
            (z' := ora) (n' := n) as (c'' & Ec'' & Safe').
          
          + auto.
            
          + simpl.
            apply Logic.I.
            
          + auto.
          
          + (* proving Hrel *)
            hnf.
            split; [ | split].
            * rewrite level_jm_.
              rewrite level_age_to; auto. cleanup. omega.
            * do 2 rewrite level_jm_.
              rewrite level_age_to; auto. cleanup. omega.
              cleanup. omega.
            * eapply pures_same_eq_l.
              apply pures_same_sym, pures_same_jm_.
              eapply pures_same_eq_r.
              2:apply pures_same_sym, pures_same_jm_.
              rewrite level_m_phi.
              rewrite level_jm_.
              auto.
              apply pures_same_eq_l with Phi'. 2: apply pures_age_eq; omega.
              apply pures_same_trans with psi.
              -- apply pures_same_sym. apply join_sub_pures_same. eexists; eauto.
              -- apply join_sub_pures_same. eexists; eauto.
          
          + (* we must satisfy the post condition *)
            rewrite m_phi_jm_.
            exists (age_to n phi0'), (age_to n phi1).
            split.
            * REWR.
              apply age_to_join.
              REWR.
              REWR.
            * split. 2: now eapply necR_trans; [ eassumption | apply age_to_necR ].
              split. now constructor.
              split. now constructor.
              simpl. rewrite seplog.sepcon_emp.
              unfold semax_conc_pred.lock_inv in *.
              admit (* depend on rmap_freelock *).
          
          + admit.
      }
    
    * admit.
    }
    
  - (* threads_wellformed *)
    intros j lj.
    specialize (wellformed j lj).
    unshelve erewrite <-gtc_age. auto.
    unshelve erewrite gRemLockSetCode; auto.
    destruct (eq_dec i j).
    + subst j.
      rewrite gssThreadCode.
      replace lj with cnti in wellformed by apply proof_irr.
      rewr (getThreadC i tp cnti) in wellformed.
      auto.
    + unshelve erewrite gsoThreadCode; auto.
      
  - (* unique_Krun *)
    apply no_Krun_unique_Krun.
    rewrite no_Krun_age_tp_to.
    Lemma no_Krun_updLockSet tp loc:
      no_Krun tp -> no_Krun (remLockSet tp loc).
    Admitted.
    apply no_Krun_updLockSet.
    apply no_Krun_stable. congruence.
    eapply unique_Krun_no_Krun. eassumption.
    instantiate (1 := cnti). rewr (getThreadC i tp cnti).
    congruence.
Admitted.
