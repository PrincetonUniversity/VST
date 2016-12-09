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
Require Import msl.age_to.
Require Import veric.aging_lemmas.
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
Require Import veric.age_to_resource_at.
Require Import veric.seplog.
Require Import floyd.coqlib3.
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
Require Import concurrency.sync_preds_defs.
Require Import concurrency.sync_preds.
Require Import concurrency.join_lemmas.
Require Import concurrency.cl_step_lemmas.
Require Import concurrency.resource_decay_lemmas.
Require Import concurrency.resource_decay_join.
Require Import concurrency.semax_invariant.
Require Import concurrency.semax_simlemmas.
Require Import concurrency.sync_preds.
Require Import concurrency.lksize.

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

Lemma shape_of_args2 (F V : Type) (args : list val) v (ge : Genv.t F V) :
  Val.has_type_list args (sig_args (ef_sig CREATE)) ->
  v <> Vundef ->
  v =
  expr.eval_id _args (make_ext_args (filter_genv (symb2genv (Genv.genv_symb ge))) (_f :: _args :: nil) args) ->
  exists arg1, args = arg1 :: v :: nil.
Proof.
  intros Hargsty Nu.
  assert (L: length args = 2%nat) by (destruct args as [|? [|? [|]]]; simpl in *; tauto).
  unfold expr.eval_id.
  unfold expr.force_val.
  intros Preb.
  match goal with H : context [Map.get ?a ?b] |- _ => destruct (Map.get a b) eqn:E end.
  subst v. 2: tauto.
  pose  (gx := (filter_genv (symb2genv (Genv.genv_symb ge)))). fold gx in E.
  destruct args as [ | arg [ | ar [ | ar2 args ] ]].
  + now inversion E.
  + now inversion E.
  + simpl in E. inversion E. eauto.
  + inversion E. f_equal.
    inversion L.
Qed.

Lemma shape_of_args3 (F V : Type) (args : list val) v (ge : Genv.t F V) :
  Val.has_type_list args (sig_args (ef_sig CREATE)) ->
  v <> Vundef ->
  v =
  expr.eval_id _f (make_ext_args (filter_genv (symb2genv (Genv.genv_symb ge))) (_f :: _args :: nil) args) ->
  exists arg2, args = v :: arg2 :: nil.
Proof.
  intros Hargsty Nu.
  assert (L: length args = 2%nat) by (destruct args as [|? [|? [|]]]; simpl in *; tauto).
  unfold expr.eval_id.
  unfold expr.force_val.
  intros Preb.
  match goal with H : context [Map.get ?a ?b] |- _ => destruct (Map.get a b) eqn:E end.
  subst v. 2: tauto.
  pose  (gx := (filter_genv (symb2genv (Genv.genv_symb ge)))). fold gx in E.
  destruct args as [ | arg [ | ar [ | ar2 args ] ]].
  + now inversion E.
  + now inversion E.
  + simpl in E. inversion E. eauto.
  + inversion E. f_equal.
    inversion L.
Qed.

Lemma lock_coherence_age_to n m tp Phi :
  lock_coherence (lset tp) Phi m ->
  lock_coherence (AMap.map (option_map (age_to n)) (lset tp)) (age_to n Phi) m.
Proof.
  unfold lock_coherence.
  intros C loc; spec C loc.
  rewrite AMap_find_map_option_map.
  destruct (AMap.find _ _) as [[phi|]|].
  - destruct C as (A&B&C&R&D&E).
    repeat split; auto.
    exists R; split. apply age_to_ind; auto. apply lkat_hered.
    destruct E as [E|E]; [left|right].
    * revert E.
      unfold age_to in *.
      rewrite age_by_age_by.
      apply age_by_age_by_pred.
      omega.
    * cut (level (age_to n Phi) <= 0). omega.
      rewrite <-E. apply level_age_to_le.
  - destruct C as (A&B&C&R&D).
    repeat split; auto.
    exists R. apply age_to_ind; auto. apply lkat_hered.
  - rewrite isLK_age_to. auto.
Qed.

Lemma func_at_func_at'' fs loc phi :
  seplog.func_at fs loc phi =
  match fs with mk_funspec fsig cc A P Q _ _ => func_at'' fsig cc A P Q loc phi end.
Proof.
  destruct fs; auto.
Qed.

Lemma cond_approx_eq_app n A P1 P2 phi :
  cond_approx_eq n A P1 P2 ->
  level phi < n ->
  forall ts y z,
    app_pred (P1 ts (fmap (rmaps.dependent_type_functor_rec ts A) (approx n) (approx n) y) z) phi ->
    app_pred (P2 ts (fmap (rmaps.dependent_type_functor_rec ts A) (approx n) (approx n) y) z) phi.
Proof.
  intros E lev ts y z.
  apply approx_eq_app_pred with n; auto.
  spec E ts.
  apply equal_f_dep with (x := y) in E.
  apply equal_f_dep with (x := z) in E.
  apply E.
Qed.

Lemma prop_app_pred {A} `{_ : ageable A} (P : Prop) (phi : A) : P -> app_pred (!! P) phi.
Proof.
  intro p. apply p.
Qed.

Lemma safety_induction_spawn Gamma n state
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
  blocked_at_external state CREATE ->
  state_invariant Jspec' Gamma (S n) state ->
  exists state',
    state_step state state' /\
    (state_invariant Jspec' Gamma n state' \/
     state_invariant Jspec' Gamma (S n) state').
Proof.
  intros isspawn I.
  inversion I as [m ge sch_ tp Phi En envcoh compat sparse lock_coh safety wellformed unique E]. rewrite <-E in *.
  unfold blocked_at_external in *.
  destruct isspawn as (i & cnti & sch & ci & args & -> & Eci & atex).
  pose proof (safety i cnti tt) as safei.
  
  rewrite Eci in safei.
  unfold jsafeN, juicy_safety.safeN in safei.
  
  fixsafe safei.
  inversion safei
    as [ | ?????? bad | n0 z c m0 e args0 x at_ex Pre SafePost | ????? bad ];
    [ now erewrite cl_corestep_not_at_external in atex; [ discriminate | eapply bad ]
    | subst | now inversion bad ].
  subst.
  simpl in at_ex. assert (args0 = args) by congruence; subst args0.
  assert (e = CREATE) by congruence; subst e.
  hnf in x.
  revert x Pre SafePost.
  
  assert (H_spawn : Some (ext_link "spawn", ef_sig CREATE) = ef_id_sig ext_link CREATE). reflexivity.
  
  (* dependent destruction *)
  funspec_destruct "acquire".
  funspec_destruct "release".
  funspec_destruct "makelock".
  funspec_destruct "freelock".
  funspec_destruct "spawn".
  
  intros (phix, (ts, (((xf, xarg), globals), (f_with_ty & f_with_x & f_with_Pre)))) (Hargsty, Pre).
  intros Post.
  simpl in Pre.
  destruct Pre as (phi0 & phi1 & jphi & A).
  destruct A as ((PreA & (PreB1 & PreB2 & PreB3) & phi00 & phi01 & jphi0 & (_y & Func) & fPRE) & necr).
  simpl in fPRE.
  rewrite seplog.sepcon_emp in fPRE.
  simpl in PreA. destruct PreA as [PreA _].
  simpl in PreB1.
  unfold liftx in PreB1. simpl in PreB1. unfold lift in PreB1.
  unfold liftx in PreB2. simpl in PreB2. unfold lift in PreB2.
  
  assert (li : level (getThreadR i tp cnti) = S n).
  { rewrite <-En. apply join_sub_level, compatible_threadRes_sub, compat. }
  assert (l1 : level phi1 = S n).
  { rewrite <-li. apply join_sub_level. eexists; eauto. }
  assert (l0 : level phi0 = S n).
  { rewrite <-li. apply join_sub_level. eexists; eauto. }
  assert (l00 : level phi00 = S n).
  { rewrite <-l0. apply join_sub_level. eexists; eauto. }
  assert (l01 : level phi01 = S n).
  { rewrite <-l0. apply join_sub_level. eexists; eauto. }
  
  Import SeparationLogicSoundness.SoundSeparationLogic.CSL.
  destruct Func as (Func, emp00).
  assert (phi01 = phi0). {
    clear -emp00 jphi0.
    eapply join_unit1_e; eauto.
    apply emp00.
  }
  pose proof func_ptr_isptr _ _ _ Func as isp.
  unfold expr.isptr in *.
  destruct xf as [ | | | | | f_b f_ofs]; try contradiction.
  
  apply shape_of_args2 in PreB1; auto. 2: clear -PreA; destruct xarg; congruence || inversion PreA.
  apply shape_of_args3 in PreB2; auto. 2: clear; congruence.
  destruct PreB1 as (arg1, Eargs).
  destruct PreB2 as (arg2, Eargs').
  rewrite Eargs in Eargs'. injection Eargs' as -> <-. subst args.
  simpl in Hargsty.
  
  destruct ((fun x => x) envcoh) as (gam, SP).
  destruct SP as (prog & CS_ & V & semaxprog & Ege & FA).
  
  unfold SeparationLogic.NDmk_funspec in Func.
  match type of Func with
    context [mk_funspec ?fsig_ ?cc_ ?A_ ?P_ ?Q_ ?NEP_ ?NEQ_] =>
    set (fsig := fsig_); set (cc := cc_); set (A := A_);
      set (P := P_); set (Q := Q_);
      set (NEP := NEP_); set (NEQ := NEQ_)
  end.
  
  assert (gam0 : matchfunspecs ge Gamma phi00). {
    revert gam. apply pures_same_matchfunspecs.
    join_level_tac.
    apply pures_same_sym, join_sub_pures_same.
    apply join_sub_trans with phi0. exists phi01. auto.
    apply join_sub_trans with (getThreadR i tp cnti). exists phi1. auto.
    join_sub_tac.
  }
  
  spec gam0 f_b ((_y, Tpointer Tvoid noattr) :: nil, Tvoid) cc_default .
  rewrite func_ptr_def in Func.
  
  destruct Func as (b' & E' & FAT). injection E' as <- ->.
  
  unfold SeparationLogic.NDmk_funspec in *.
  
  specialize (gam0 _ _ _ FAT).
  destruct gam0 as (id_fun & P' & Q' & NEP' & NEQ' & Eb & Eid & Heq_P & Heq_Q).
  unfold filter_genv in *.
  
  pose proof semax_prog_entry_point (Concurrent_Espec unit CS ext_link) V Gamma prog f_b
       id_fun _y xarg A P' Q' NEP' NEQ' semaxprog as HEP.
  
  subst ge.
  rewrite <-make_tycontext_s_find_id in HEP.
  spec HEP. auto.
  
  spec HEP. {
    unfold A. 
    rewrite <-Eid.
    apply make_tycontext_s_find_id.
  }
  
  spec HEP. {
    (* here Q' is related to Q through Heq_Q, and Q is "emp". *)
    (* obviously emp does not imply false, so we'll have to change that in semax_conc *)
    
    (* adding a {emp}exit{FF} does not help, because the frame rule
    also applies on exit.  But exit is a more desirable solution
    rather than just returning from the function anyway. Maybe we can
    make do with {emp}, but we leave that for later *)
    intros ts0 a rho phi ff. hnf.
    apply cond_approx_eq_sym in Heq_Q.
    pose proof @cond_approx_eq_app _ (rmaps.ConstType (val * f_with_ty)) _ _ (age_to n phi) Heq_Q as HQ.
    spec HQ. eapply le_lt_trans with n. 2:omega.
    { apply level_age_to_le'. }
    spec HQ ts0 a rho.
    spec HQ. now apply age_to_pred, ff.
    simpl in HQ.
    unfold canon.PROPx in *.
    unfold canon.SEPx in *.
    unfold base.fold_right_sepcon in *.
    destruct a.
    rewrite seplog.sepcon_emp in HQ.
    destruct HQ as (_ & _ & []).
  }
  
  spec HEP. auto.
  
  destruct HEP as (q_new & Initcore & Safety).
  
  change (initial_core (juicy_core_sem cl_core_sem)) with cl_initial_core in Initcore.
  
  apply join_comm in jphi0.
  destruct (join_assoc jphi0 jphi) as (phi1' & jphi1' & jphi').
  assert (phi1 = phi1'). {
    clear -emp00 jphi1'.
    eapply join_unit1_e; eauto.
    apply emp00.
  }
  subst phi1'.
  
  eexists.
  split.
  {
    apply state_step_c.
    
    unshelve eapply JuicyMachine.sync_step
    with (tid := i)
           (Htid := cnti)
           (ev := Events.spawn (f_b, Int.intval Int.zero) None None).
    { eexists; eauto. }
    { reflexivity. }
    { reflexivity. }
    
    eapply step_create with
    (c_new := q_new)
      (Hcompatible := mem_compatible_forget compat)
      (phi' := phi1)
      (d_phi := phi01); try reflexivity.
    { eassumption. }
    { unfold SEM.Sem in *.
      rewrite SEM.CLN_msem.
      apply atex. }
    { replace (initial_core SEM.Sem) with cl_initial_core
        by (unfold SEM.Sem; rewrite SEM.CLN_msem; reflexivity).
      unfold code in *.
      rewrite <-Initcore.
      reflexivity. }
    { simpl. auto. }
  }
  (* "progress" part finished. *)
  
  left. (* we have to consume a step, at least because of the safety
  of the spawner, but also for the safety of the spawned thread,
  because the precondition is stored in the current rmap *)
  
  assert (compat' :
            mem_compatible_with
              (addThread (updThread i tp cnti (Kresume ci Vundef) phi1)
                         (Vptr f_b Int.zero) xarg phi01) m Phi).
  {
    split; try apply compat.
    subst phi01.
    clear -jphi compat. destruct compat as [jj _ _ _ _].
    rewrite join_all_joinlist in *.
    rewrite maps_addthread.
    rewrite maps_updthread.
    rewrite (maps_getthread _ _ cnti) in jj.
    rewrite joinlist_merge; eauto.
  }
  
  apply (@mem_compatible_with_age n) in compat'.
  replace (level _) with (S n) by (simpl; join_level_tac).
  replace (S n - 1) with n by omega.
  
  apply state_invariant_c with (mcompat := compat').
  
  - (* level *)
    apply level_age_to. cleanup. omega.
  
  - (* env_coherence *)
    apply env_coherence_age_to; auto.
  
  - (* lock sparsity *)
    apply lock_sparsity_age_to.
    auto.
  
  - (* lock coherence *)
    unfold lock_coherence' in *.
    clear -lock_coh. simpl.
    apply lock_coherence_age_to.
    exact_eq lock_coh. f_equal.
    match goal with |- restrPermMap ?p = restrPermMap ?p' => generalize p; generalize p' end.
    unfold lockSet. simpl. cleanup. rewrite A2PMap_option_map.
    intros; f_equal. apply proof_irr.
  
  - (* thread_safety :
       - new thread #n+1 (spawned),
       - thread #i (after spawning),
       - other threads *)
    intros j lj ora.
    destruct (eq_dec j tp.(num_threads).(pos.n)); [ | destruct (eq_dec i j)].
    
    + (* safety of new thread *)
      subst j.
      REWR.
      rewrite gssAddCode. 2:reflexivity.
      exists q_new. split; auto.
      intros jm. REWR. rewrite gssAddRes. 2:reflexivity.
      spec Safety jm ts.
      intros Ejm.
      replace (level jm) with n in Safety; swap 1 2.
      { rewrite <-level_m_phi, Ejm. symmetry. apply level_age_to.
        cut (level phi01 = level Phi). cleanup. intros ->. omega.
        apply join_sub_level.
        subst phi01. apply join_sub_trans with (getThreadR _ _ cnti). exists phi1. auto.
        apply compatible_threadRes_sub. apply compat. }
      
      eapply Safety.
      * rewrite Ejm.
        eapply cond_approx_eq_app with (A := rmaps.ConstType (val * f_with_ty)) (y := (xarg, f_with_x)).
        
        (* cond_approx_eq *)
        eauto.
        
        (* level *)
        rewrite level_age_to. omega. cleanup. omega.
        
        (* PROP / LOCAL / SEP *)
        simpl.
        apply age_to_pred.
        split.
        
        (* nothing in PROP *)
        now constructor.
        
        split.
        unfold SeparationLogic.local, expr.lift1.
        
        split.
        
        (* LOCAL 1 : value of xarg *)
        simpl.
        unfold liftx, lift. simpl.
        unfold expr.eval_id in *.
        unfold expr.force_val in *.
        unfold te_of in *.
        unfold construct_rho in *.
        unfold make_tenv in *.
        unfold Map.get in *.
        rewrite PTree.gss.
        reflexivity.
        
        (* LOCAL 2 : locald_denote of global variables *)
        clear -PreB3.
        induction globals. constructor.
        split; [ | now apply IHglobals; destruct PreB3; auto ].
        destruct PreB3 as [WOB _]. clear IHglobals.
        simpl in *.
        unfold canon.gvar_denote in *. simpl in *.
        unfold make_venv, Map.get, empty_env. rewrite PTree.gempty.
        unfold Genv.find_symbol in *.
        rewrite symb2genv_ax in *.
        assumption.
        
        (* SEP: only precondition of spawned condition *)
        unfold canon.SEPx in *.
        simpl.
        rewrite seplog.sepcon_emp.
        assumption.
        
      * (* funnassert *)
        rewrite Ejm.
        apply funassert_pures_eq with Phi.
        { rewrite level_age_to. omega. cleanup. omega. }
        { apply pures_same_eq_l with phi01. 2: now apply pures_eq_age_to; omega.
          apply join_sub_pures_same. subst.
          apply join_sub_trans with (getThreadR i tp cnti). exists phi1; auto.
          apply compatible_threadRes_sub, compat. }
        apply FA.
    
    + (* safety of spawning thread *)
      subst j.
      REWR. unshelve erewrite (@gsoAddCode i); auto. REWR. REWR.
      unshelve erewrite (@gsoAddRes _ _ _ _ i); auto. REWR.
      intros c' afterex jm Ejm.
      specialize (Post None jm ora n Hargsty ltac:(auto) (le_refl _)).
      
      spec Post. (* Hrel *)
      { split. rewrite <-level_m_phi, Ejm. symmetry. apply level_age_to. cleanup; omega.
        rewrite <-!level_m_phi. rewrite m_phi_jm_, Ejm. split.
        rewrite level_age_to. cleanup; omega. cleanup; omega.
        apply pures_same_eq_l with phi1. apply join_sub_pures_same. exists phi0. auto.
        apply pures_eq_age_to. omega. }
      
      spec Post. (* Postcondition *)
      { exists (age_to n phi00), (age_to n phi1); split3.
        - rewrite Ejm. apply age_to_join. auto.
        - split; auto. split; auto.
          unfold canon.SEPx in *. simpl.
          rewrite seplog.sepcon_emp.
          apply age_to_pred. auto.
        - simpl.
          apply necR_trans with phi1; auto.
          apply age_to_necR.
      }
      
      destruct Post as (c'_ & afterex_ & safe').
      assert (c'_ = c').
      { cut (Some c'_ = Some c'). congruence. rewrite <-afterex, <-afterex_. reflexivity. }
      subst c'_.
      apply safe'.
    
    + assert (cntj : containsThread tp j).
      { apply cnt_age, cntAdd' in lj.
        destruct lj as [[lj ?] | lj ]. apply lj. simpl in lj. tauto. }
      specialize (safety j cntj ora).
      REWR. REWR. REWR. REWR.
      destruct (getThreadC j tp cntj) eqn:Ej.
      -- edestruct (unique_Krun_neq i j); eauto.
      -- apply jsafe_phi_age_to; auto. apply jsafe_phi_downward.
         unshelve erewrite gsoAddRes; auto. REWR.
      -- intros c' Ec'; spec safety c' Ec'.
         apply jsafe_phi_age_to; auto. apply jsafe_phi_downward.
         unshelve erewrite gsoAddRes; auto. REWR.
      -- destruct safety as (c_new & Einit & safety). exists c_new; split; auto.
         unshelve erewrite gsoAddRes; auto. REWR.
         apply jsafe_phi_age_to; auto. apply jsafe_phi_downward, safety.
  
  - (* wellformed *)
    intros j cntj.
    destruct (eq_dec j tp.(num_threads).(pos.n)); [ | destruct (eq_dec i j)].
    + subst j. REWR. rewrite gssAddCode. 2:reflexivity. constructor.
    + subst j. REWR. REWR. REWR. rewrite atex. split; auto; congruence.
    + assert (cntj' : containsThread tp j).
      { apply cnt_age, cntAdd' in cntj. destruct cntj as [[lj ?] | lj ]. apply lj. simpl in lj. tauto. }
      REWR. REWR. REWR. apply wellformed.
  
  - (* unique_Krun *)
    apply no_Krun_unique_Krun.
    (* rewrite no_Krun_age_tp_to. *)
    intros j cntj q.
    destruct (eq_dec j tp.(num_threads).(pos.n)); [ | destruct (eq_dec i j)].
    + subst j. REWR. rewrite gssAddCode. 2:reflexivity. clear; congruence.
    + subst j. REWR. REWR. REWR. clear; congruence.
    + assert (cntj' : containsThread tp j).
      { apply cnt_age, cntAdd' in cntj. destruct cntj as [[lj ?] | lj ]. apply lj. simpl in lj. tauto. }
      REWR. REWR. REWR.
      eapply unique_Krun_no_Krun. eassumption.
      instantiate (1 := cnti). rewr (getThreadC i tp cnti).
      congruence.
Qed. (* safety_induction_spawn *)
