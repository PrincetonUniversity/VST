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
Require Import VST.concurrency.common.Clightcore_coop.
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
Require Import VST.veric.seplog.
Require Import VST.floyd.coqlib3.
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
Require Import VST.concurrency.juicy.Clight_mem_ok.
Require Import VST.concurrency.juicy.semax_invariant.
Require Import VST.concurrency.juicy.semax_simlemmas.
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.common.lksize.
Import Events.
Import sepcomp.semantics mem_lemmas extspec.

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

Lemma lock_coherence_age_to ge n m (tp : jstate ge) Phi :
  lock_coherence (lset tp) Phi m ->
  lock_coherence (AMap.map (option_map (age_to n)) (lset tp)) (age_to n Phi) m.
Proof.
  unfold lock_coherence.
  intros C loc; specialize (C loc).
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
    * cut (level (age_to n Phi) <= 0)%nat. omega.
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

Lemma args_cond_approx_eq_app n A P1 P2 phi :
  args_cond_approx_eq n A P1 P2 ->
  (level phi < n)%nat ->
  forall ts y z,
    app_pred (P1 ts (fmap (rmaps.dependent_type_functor_rec ts A) (approx n) (approx n) y) z) phi ->
    app_pred (P2 ts (fmap (rmaps.dependent_type_functor_rec ts A) (approx n) (approx n) y) z) phi.
Proof.
  intros E lev ts y z.
  apply approx_eq_app_pred with n; auto.
  specialize (E ts).
  apply equal_f_dep with (x := y) in E.
  apply equal_f_dep with (x := z) in E.
  apply E.
Qed.

Lemma prop_app_pred {A} `{_ : ageable A} (P : Prop) (phi : A) : P -> app_pred (!! P) phi.
Proof.
  intro p. apply p.
Qed.

Definition Espec_permits_framing (Espec: OracleKind) :=
  forall ge (n: nat) (ora: @OK_ty Espec) (q: CC_core) (phi phi': rmap),
   join_sub phi phi' ->
   @jsafe_phi (@OK_ty Espec) (@OK_spec Espec) ge n ora q phi ->
   @jsafe_phi (@OK_ty Espec) (@OK_spec Espec) ge n ora q phi'.

Lemma Concurrent_Espec_permits_framing:
   forall t cs ext_link, Espec_permits_framing (Concurrent_Espec t cs ext_link).
(* This is true and provable.  Here's how:
   to the Record juicy_ext_spec defined in VST.veric.juicy_extspec,
   add some more properties specifying that (exists t', ext_spec_type e = (rmap * t'))
   and about the fact that each of the external functions has
   pre/postcondition pair that satisfies the frame rule.
   Then prove that in Concurrent_Espec (or any Espec built using add_funspecs_rec),
    each of the external functions does satisfy this spec.  Voila!  
*)
Admitted.

Import SeparationLogic Clight_initial_world Clightdefs. 

Lemma safety_induction_spawn ge Gamma n state
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
    state_step(ge := ge) state state' /\
    (state_invariant Jspec' Gamma n state' \/
     state_invariant Jspec' Gamma (S n) state').
Proof.
  subst Jspec'.
  clear personal_mem_equiv_spec.
  intros isspawn I.
  inversion I as [m tr sch_ tp Phi En envcoh mwellformed compat extcompat sparse lock_coh safety wellformed unique E]. 
  subst state.
  destruct isspawn as (i & cnti & sch & ci & args & -> & Eci & atex).
  pose proof (safety i cnti tt) as safei; rewrite Eci in safei.
  destruct ci; try destruct f; simpl in atex; try discriminate.
  destruct (ef_inline e); inv atex.
 match type of Eci with _ = Kblocked ?CI => set (ci := CI) in * end.

  fixsafe safei.
  inversion safei
    as [ | ?????? bad | n0 z c' m0 e args0 x at_ex Pre SafePost | ????? bad ];
  [apply (corestep_not_at_external (juicy_core_sem _)) in bad; inv bad | | inv bad ];
  subst.
  symmetry in at_ex; inv at_ex.

  revert x Pre SafePost.
  assert (H_spawn : Some (ext_link "spawn", ef_sig CREATE) = ef_id_sig ext_link CREATE) by reflexivity.
  (* dependent destruction *)
  funspec_destruct "acquire"; clear Heq_name.
  funspec_destruct "release"; clear Heq_name.
  funspec_destruct "makelock"; clear Heq_name.
  funspec_destruct "freelock"; clear Heq_name.
  funspec_destruct "spawn"; clear Heq_name.
  clear ext_link_inj.
  clear H_spawn.

  intros (phix, (ts, ((((f,b), globals), f_with_x) , f_with_Pre)))  (Hargsty, Pre) Post.
  simpl (and _) in Post.
  unfold fst, snd, projT1, projT2 in Pre.
  destruct Pre as (phi0 & phi1 & jphi & A). simpl in A.
  destruct A as [[[PreA _] [PreB1 [[PreB3 _] [phi00 [phi01 [jphi0 [[_y [Func Hphi00]] fPRE]]]]]]] necr].
  rewrite seplog.sepcon_emp in fPRE.
  change (args = f::b::nil) in PreB1.
  subst args.
  pose proof func_ptr_isptr _ _ _ Func as isp.
  destruct f as [ | | | | | f_b f_ofs]; try contradiction isp.
  clear isp.
  assert (phi01 = phi0). {
    eapply join_unit1_e; eauto.
    assumption.
  }
  subst.

  assert (li : level (getThreadR i tp cnti) = S n).
  { rewrite <-En. apply join_sub_level, compatible_threadRes_sub, compat. }
  assert (l1 : level phi1 = S n).
  { rewrite <-li. apply join_sub_level. eexists; eauto. }
  assert (l0 : level phi0 = S n).
  { rewrite <-li. apply join_sub_level. eexists; eauto. }
  assert (l00 : level phi00 = S n).
  { rewrite <-l0. apply join_sub_level. eexists; eauto. }

  destruct ((fun x => x) envcoh) as (gam, SP).
  destruct SP as (prog & CS_ & ora & V & semaxprog & Ege & FA).
  assert (gam0 : matchfunspecs ge Gamma phi00). {
    revert gam. apply pures_same_matchfunspecs.
    join_level_tac.
    apply pures_same_sym, join_sub_pures_same.
    apply join_sub_trans with phi0. eexists; eassumption.
    apply join_sub_trans with (getThreadR i tp cnti). exists phi1. auto.
    join_sub_tac.
  }
  clear gam.
  set (ts0 := nth 0 ts unit) in *.
  unfold SeparationLogic.NDmk_funspec in Func.
  match type of Func with
    context [mk_funspec ?fsig_ _ ?A_ ?P_ ?Q_ ?NEP_ ?NEQ_] =>
    set (fsig := fsig_) in *; set (A := A_) in *; set (P := P_) in *; set (Q := Q_) in *
  end.
  match type of Func with app_pred (func_ptr ?FS _) _ => set (spawn_spec := FS) in * end.
  subst ge.
  change (?A) with (@client_lemmas.abbreviate _ A) in Post.
 assert (HP: app_pred (P ts
                        (fmap  (rmaps.dependent_type_functor_rec ts
                                       (rmaps.ConstType (val * ts0)))
                           (approx (level phi00)) (approx (level phi00))
                           (b, f_with_x))
                        (filter_genv (globalenv prog), b::nil))
                   (age_to n phi0)). {
        (* PROP / PARAMS / GLOBAL  / SEP *)
        simpl.
        apply age_to_pred.
        split; [ | split3].

        -- (* nothing in PROP *) apply Logic.I. 
        -- (* PARAMS *)
            reflexivity.
        -- (* GLOBAL locald_denote of global variables *)
        split3. hnf.
        clear - PreB3.
        hnf in PreB3. rewrite PreB3; clear PreB3.
        unfold Map.get, make_args. unfold env_set. 
        unfold ge_of.
        unfold filter_genv.
        extensionality i. unfold Genv.find_symbol. simpl. auto.
       

        -- (* SEP: only precondition of spawned condition *)
        unfold canon.SEPx in *.
        simpl.
        rewrite seplog.sepcon_emp.
        destruct fPRE; assumption.
  }
  clearbody P.
  clearbody Q.
  clear PreB3.
  destruct fPRE as [Hvalid _].
  destruct Func as (b' & E' & [fs' [Fsub FAT]]). injection E' as <- ->.  
  specialize (gam0 f_b fs' _ (necR_refl _) FAT).
  assert (Hperm: Mem.perm m f_b 0 Max Nonempty). {
     clear - jphi jphi0 FAT compat.
     pose proof (@compatible_threadRes_sub _ _ _ cnti Phi (juice_join compat)).
     assert (join_sub phi00 Phi).
     eapply join_sub_trans; try eassumption. clear H.
     apply join_sub_trans with phi0; eexists; eauto.
     pose proof (max_coh (all_cohere compat) (f_b,0)).
     clear - H0 H1 FAT.
     destruct fs'. hnf in FAT.
     pose proof (resource_at_join_sub _ _ (f_b,0) H0).
     rewrite FAT in H; clear FAT H0.
     destruct H.
     inv H.
     match type of H5 with PURE ?K ?PP = _ => forget K as k; forget PP as pp end.
     symmetry in H5.
     clear - H1 H5. 
     rewrite H5 in H1. clear H5. simpl in H1.
     hnf in H1. hnf.  unfold max_access_at, access_at in H1. simpl in *. auto.
  }
  clear FAT.
  destruct gam0 as [id_fun [fs'' [[? Eid] ?]]].
  assert (app_pred (seplog.funspec_sub_si fs'' spawn_spec) phi00).
  eapply funspec_sub_si_trans. split; eauto.
  clear H0 Fsub fs'; rename H1 into Fsub.
  rename fs'' into fs'.
  destruct fs' as [t2 c2 A' P' Q' NEP' NEQ'].
  unfold filter_genv in *.
  assert (PAE: postcondition_allows_exit
    (Concurrent_Espec unit CS ext_link) tint)
     by (hnf; intros; hnf; auto).
  pose (args := b::nil).
  pose proof semax_prog_entry_point (Concurrent_Espec unit CS ext_link) V Gamma prog f_b
       id_fun (fst fsig) args A' P' Q' NEP' NEQ' 0 ora semaxprog as HEP.
  clear PAE.
  rewrite <-make_tycontext_s_find_id in HEP.
  spec HEP. auto.
  assert (Hx: t2 = fsig /\ c2 = cc_default) by (destruct Fsub; assumption).
  destruct Hx; subst t2 c2.

  spec HEP. {
   simpl fst. fold fsig.
    rewrite <-Eid.
    apply make_tycontext_s_find_id.
  }

  specialize (HEP (conj PreA Logic.I)).
  spec HEP. {
   subst fsig args; simpl. repeat constructor; auto.
   clear - PreA. destruct b; try contradiction;
   try constructor; reflexivity.
  }
  destruct HEP as (q_new & Initcore & Safety). {
    clear Post.
    subst fsig; simpl. hnf. unfold Conventions1.size_arguments. simpl.
    destruct Archi.ptr64; reflexivity.
  }

  apply join_comm in jphi0.
  destruct (join_assoc jphi0 jphi) as (phi1' & jphi1' & jphi').
  assert (phi1 = phi1'). {
    eapply join_unit1_e; eauto.
    eassumption.
  }
  subst phi1'.

  assert (val_inject (Mem.flat_inj (Mem.nextblock m)) b b) as Hinj.
  { destruct b; try constructor; simpl in Hvalid.
    destruct (compatible_threadRes_cohere cnti (mem_compatible_forget compat)).
    destruct (plt b (Mem.nextblock m)).
    econstructor; [|symmetry; apply Ptrofs.add_zero].
    unfold Mem.flat_inj; rewrite if_true; auto.
    { specialize (all_coh0 (b, Ptrofs.unsigned i0)); spec all_coh0; auto.
      rewrite m_phi_jm_ in jphi.
      apply (resource_at_join _ _ _ (b, Ptrofs.unsigned i0)) in jphi.
      rewrite all_coh0 in jphi.
      rewrite Z.add_0_r in Hvalid; destruct (phi0 @ _) eqn: Hb; inv jphi.
      apply join_to_bot_l in RJ; subst.
      contradiction Hvalid; apply bot_identity. } }
  
  eexists.
  split.
  {
    apply state_step_c.

    unshelve eapply JuicyMachine.sync_step
    with (tid := i)
           (Htid := cnti)
           (ev := Events.spawn (f_b, Ptrofs.intval Ptrofs.zero) None None).
    { eexists; eauto. }
    { reflexivity. }
    { reflexivity. }
    eapply step_create with
      (Hcompatible := mem_compatible_forget compat)
      (phi' := phi1)
      (d_phi := phi0); try reflexivity; try eassumption; simpl; auto.
      clear - PreA. destruct b; try contradiction; congruence.
  }
  (* "progress" part finished. *)

  left. (* we have to consume a step, at least because of the safety
  of the spawner, but also for the safety of the spawned thread,
  because the precondition is stored in the current rmap *)

  assert (compat' :
            mem_compatible_with
              (addThread (updThread i tp cnti (Kresume ci Vundef) phi1)
                         (Vptr f_b Ptrofs.zero) b phi0) m Phi).
  {
    split; try apply compat.
    clear -jphi compat. destruct compat as [jj jj']. simpl in jphi.
    rewrite join_all_joinlist in *.
    rewrite maps_addthread.
    rewrite maps_updthread.
    rewrite (maps_getthread _ _ cnti) in jj.
    rewrite joinlist_merge; eauto.
  }

  apply (@mem_compatible_with_age _ n) in compat'.
  replace (level _) with (S n) by (simpl; join_level_tac).
  replace (S n - 1)%nat with n by omega.

  apply state_invariant_c with (mcompat := compat').
  (* level *)
    apply level_age_to. cleanup. omega.

  - (* env_coherence *)
    apply env_coherence_age_to; auto.
  - auto.
  - rewrite age_to_ghost_of.
    destruct extcompat as [? J]; eapply ghost_fmap_join in J; eexists; eauto.

  - (* lock sparsity *)
    apply lock_sparsity_age_to.
    auto.

  - (* lock coherence *)
    unfold lock_coherence' in *.
    clear -lock_coh. simpl.
    apply lock_coherence_age_to.
    exact_eq lock_coh. f_equal.
    match goal with |- restrPermMap ?p = restrPermMap ?p' => generalize p; generalize p' end.
    simpl. cleanup. simpl. rewrite A2PMap_option_map.
    intros; f_equal. apply proof_irr.

  - (* thread_safety :
       - new thread #n+1 (spawned),
       - thread #i (after spawning),
       - other threads *)
    rename ora into ora0.
    intros j lj ora.
    assert (ora0=ora) by (destruct ora0,ora; auto).
    subst ora0.
    destruct (eq_dec j tp.(num_threads).(pos.n)); [ | destruct (eq_dec i j)].
    + (* safety of new thread *)
      subst j.
      REWR.
      rewrite gssAddCode. 2:reflexivity.
      split; auto.
      exists q_new.
      split.
{
      destruct (Initcore (jm_ cnti compat)) as [? [? [? ?]]]; auto.
      subst args; repeat constructor; auto.
      clear Initcore Post lj ora Safety Eid NEP' NEQ' Fsub P' Q' semaxprog.
       subst fsig A.
      clear jphi' jphi1' q_new H id_fun CS_ V FA.
      clear l1 l0 l00 necr li PreA.
      clear spawn_spec Hargsty Hphi00 _y unique wellformed En.
      clear safei safety lock_coh.
      simpl Mem.nextblock.
      destruct mwellformed. split; auto.
      clear - H.
      change (Mem.nextblock m)
       with (Mem.nextblock (m_dry (@jm_ (globalenv prog) tp m Phi i cnti compat))).
      apply  maxedmem_neutral.
      assert (mem_equiv.mem_equiv (maxedmem (m_dry (@jm_ (globalenv prog) tp m Phi i cnti compat)))
                  (maxedmem m))
       by apply mem_equiv_restr_max.
  red. simpl Mem.nextblock. rewrite H0. auto.
  clear Safety jphi' jphi1' Initcore Post.
  simpl. red; simpl. 
  clear - I. inv I. destruct mwellformed. apply H0.
  clear -mwellformed; destruct mwellformed as [? _].
  hnf. 
simpl.
  change (Mem.inject_neutral (Mem.nextblock m)
  (juicyRestrict (OrdinalPool.getThreadR cnti) m
     (acc_coh (thread_mem_compatible (mem_compatible_forget compat) cnti)))).
  apply maxedmem_neutral'; auto.
 }


         destruct Fsub as [_ Fsub].
         rewrite subtypes.later_unfash in Fsub.
         do 3 red in Fsub. rewrite l00 in Fsub.
         specialize (Fsub n).
         spec Fsub. { apply laterR_nat; omega. }
         specialize (Fsub ts   (fmap (rmaps.dependent_type_functor_rec ts (rmaps.ConstType (val * ts0)))
                                                  (approx (level phi00)) (approx (level phi00))   (b, f_with_x))
                               (Genv.find_symbol (globalenv prog), b :: nil)).
        cbv beta in Fsub.
        specialize (Fsub (age_to n phi0)).
        spec Fsub.  {rewrite level_age_to.  clear; omega. omega. }
        specialize (Fsub _ (necR_refl _)).
        spec Fsub.
        split. simpl.
        split.
        hnf; intros. simpl in H0. rewrite PTree.gempty in H0; inv H0.
        repeat constructor; auto. intro. apply PreA.
        assumption.
        destruct Fsub as [ts1 [ftor1 [F [HP']]]].
        REWR. rewrite gssAddRes by reflexivity.
      destruct HP' as [phi_frame [phi_thread [?HP [?HP ?HP]]]].
      apply Concurrent_Espec_permits_framing with phi_thread.
      eexists; eauto.
      intros jm Ejm.
      specialize (Safety jm ts1 ftor1).
      replace n with (level jm).
     2:{ rewrite <- level_m_phi. rewrite Ejm. destruct (join_level _ _ _ HP0). rewrite H2; apply level_age_to. omega. }
      apply Safety.
      * apply juicy_postcondition_allows_exit_i0. hnf; intros. hnf. auto.
      * (* funnassert *)
        rewrite Ejm.
        apply fungassert_pures_eq with Phi.
        { destruct (join_level _ _ _ HP0) as [_ HP3]; rewrite HP3, level_age_to.
            omega. cleanup. omega. }
        { apply pures_eq_trans with (age_to n phi0).
           destruct (join_level _ _ _ HP0) as [_ ?]; omega.
          apply pures_same_eq_l with phi0.
           2: now apply pures_eq_age_to; omega.
          apply join_sub_pures_same. subst.
          apply join_sub_trans with (getThreadR i tp cnti). exists phi1; auto.
          apply compatible_threadRes_sub, compat.
          apply pures_same_pures_eq.
           destruct (join_level _ _ _ HP0) as [_ ?]; auto.
          apply pures_same_sym.
          apply join_sub_pures_same. eexists; eauto.
          }
        apply FA.
      * 
         rewrite Ejm. clear compat' lj Hinj Safety Initcore.
         assumption.
      * do 3 red.
         rewrite Ejm.
         apply @join_sub_joins_trans with (ghost_of (age_to n phi0)); auto with typeclass_instances.
         exists (ghost_of phi_frame). apply ghost_of_join; auto.
         rewrite age_to_ghost_of.
         destruct ora.
         eapply join_sub_joins_trans, ext_join_approx, extcompat.
         destruct (compatible_threadRes_sub cnti (juice_join compat)).
         eapply join_sub_trans.
         -- eexists; apply ghost_fmap_join, ghost_of_join; eauto.
         -- eexists; apply ghost_fmap_join, ghost_of_join; eauto.

    + (* safety of spawning thread *)
      subst j.
      REWR. unshelve erewrite (@gsoAddCode _ _ _ _ _ _ _ i); auto. REWR. REWR.
      unshelve erewrite (@gsoAddRes _ _ _ _ _ _ _ i); auto. REWR.
      intros c' afterex jm Ejm.
      specialize (Post None jm ora n Hargsty Logic.I (le_refl _)).

      spec Post. (* Hrel *)
      { split. rewrite <-level_m_phi, Ejm. symmetry. apply level_age_to. cleanup; omega.
        rewrite <-!level_m_phi. rewrite m_phi_jm_, Ejm. split.
        rewrite level_age_to. cleanup; omega. cleanup; omega.
        apply pures_same_eq_l with phi1. apply join_sub_pures_same. exists phi0. auto.
        apply pures_eq_age_to. omega. }

      spec Post. (* Postcondition *)
      { exists (age_to n phi00), (age_to n phi1); split; [ | split3].
        - rewrite Ejm. apply age_to_join. auto.
        - split; auto. split; auto. split.
          apply prop_app_pred; auto.
          unfold canon.SEPx in *. simpl.
          apply age_to_pred. auto.
        - simpl.
          apply necR_trans with phi1; [ |apply age_to_necR].
          destruct necr; auto.
        - destruct necr as [? JOINS].
           rewrite Ejm, age_to_ghost_of.
           destruct ora.
           eapply join_sub_joins_trans; [|apply ext_join_approx, JOINS].
           eexists; apply ghost_fmap_join, ghost_of_join; eauto.
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
      -- destruct (cl_halted s) eqn:Halted.
           destruct s; inv Halted. destruct v0; inv H1.  destruct c1; inv H2.
           eapply jsafeN_halted; eauto. simpl. reflexivity.
           apply Logic.I.  
           edestruct (unique_Krun_neq(ge := globalenv prog) i j); try split; eauto.
      -- apply jsafe_phi_age_to; auto. apply jsafe_phi_downward.
         unshelve erewrite gsoAddRes; auto. REWR.
      -- intros c' Ec'; specialize (safety c' Ec').
         apply jsafe_phi_bupd_age_to; auto. apply jsafe_phi_bupd_downward.
         unshelve erewrite gsoAddRes; auto. REWR.
      -- destruct safety as (? & c_new & Einit & safety).
         split; auto.
         exists c_new; split; auto.
         unshelve erewrite gsoAddRes; auto. REWR.
         apply jsafe_phi_age_to; auto. apply jsafe_phi_downward, safety.

  - (* wellformed *)
    intros j cntj.
    destruct (eq_dec j tp.(num_threads).(pos.n)); [ | destruct (eq_dec i j)].
    + subst j. REWR. rewrite gssAddCode. 2:reflexivity.
        clear - Hinj wellformed Eci.
        specialize (wellformed _ cnti). rewrite Eci in  wellformed.
        subst ci.   destruct wellformed. 
        clear - H. simpl in H. destruct H. inv H. inv H4.
        split; auto.
    + subst j. REWR. REWR. REWR.
       clear - Eci wellformed. 
        specialize (wellformed _ cnti). rewrite Eci in wellformed.
        simpl in *. intuition.
    + assert (cntj' : containsThread tp j).
      { apply cnt_age, cntAdd' in cntj. destruct cntj as [[lj ?] | lj ]. apply lj. simpl in lj. tauto. }
      REWR. REWR. REWR.

  - (* unique_Krun *)
    apply no_Krun_unique_Krun.
    (* rewrite no_Krun_age_tp_to. *)
    intros j cntj q.
    destruct (eq_dec j tp.(num_threads).(pos.n)); [ | destruct (eq_dec i j)].
    + subst j. REWR. rewrite gssAddCode. 2:reflexivity. intros [Hx _]; inv Hx.
    + subst j. REWR. REWR. REWR.  intros [Hx _]; inv Hx.
    + assert (cntj' : containsThread tp j).
      { apply cnt_age, cntAdd' in cntj. destruct cntj as [[lj ?] | lj ]. apply lj. simpl in lj. tauto. }
      REWR. REWR. REWR.
      eapply unique_Krun_no_Krun. eassumption.
      instantiate (1 := cnti). rewr (getThreadC i tp cnti).
      intros ? [Hx _]; inv Hx.
Qed. (* safety_induction_spawn *)
