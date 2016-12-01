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
Require Import concurrency.semantics.
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

Lemma preservation_acquire
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
  (Gamma : PTree.t funspec)
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
  (gam : matchfunspec (filter_genv ge) Gamma Phi)
  (sparse : lock_sparsity (lset tp))
  (lock_coh : lock_coherence' tp Phi m compat)
  (safety : threads_safety Jspec' m ge tp Phi compat (S n))
  (wellformed : threads_wellformed tp)
  (unique : unique_Krun tp (i :: sch))
  (Ei cnti : ssrnat.leq (S i) (pos.n (num_threads tp)) = true)
  (ci : code)
  (Eci : getThreadC i tp cnti = Kblocked ci)
  (Hcmpt : mem_compatible tp m)
  (El : level (getThreadR i tp cnti) - 1 = n)
  (compat_aged : mem_compatible_with (age_tp_to n tp) m (age_to n Phi))
  (c : code)
  (b : block)
  (ofs : int)
  (d_phi : rmap)
  (psh : pshare)
  (phi' : rmap)
  (sh : Share.t)
  (R : pred rmap)
  (Hthread : getThreadC i tp cnti = Kblocked c)
  (Hat_external : at_external SEM.Sem c = Some (LOCK, (* ef_sig LOCK, *) Vptr b ofs :: nil))
  (His_unlocked : lockRes tp (b, Int.intval ofs) = SSome d_phi)
  (Hload : Mem.load Mint32 (juicyRestrict_locks (mem_compat_thread_max_cohere Hcmpt cnti))
                    b (Int.intval ofs) =
          Some (Vint Int.one))
  (Hlt' : permMapLt
           (setPermBlock (Some Writable) b (Int.intval ofs) (juice2Perm_locks (getThreadR i tp cnti) m)
              LKSIZE_nat) (getMaxPerm m))
  (Hstore : Mem.store Mint32 (restrPermMap Hlt') b (Int.intval ofs) (Vint Int.zero) = Some m')
  (* (Hstore : Mem.store Mint32 (juicyRestrict_locks (mem_compat_thread_max_cohere Hcmpt cnti)) *)
  (*                     b (Int.intval ofs) (Vint Int.zero) = Some m') *)
  (HJcanwrite : getThreadR i tp cnti @ (b, Int.intval ofs) = YES sh psh (LK LKSIZE) (pack_res_inv R))
  (Hadd_lock_res : join (getThreadR i tp cnti) d_phi phi')
  (jmstep : @JuicyMachine.machine_step ge (i :: sch) nil tp m sch nil
             (age_tp_to n
                (updLockSet (updThread i tp cnti (Kresume c Vundef) phi') (b, Int.intval ofs) None)) m')
  (Htstep : syncStep true ge cnti Hcmpt
             (age_tp_to n
                (updLockSet (updThread i tp cnti (Kresume c Vundef) phi') (b, Int.intval ofs) None)) m'
             (Events.acquire (b, Int.intval ofs) None)) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m', ge, (sch, age_tp_to n
           (updLockSet (updThread i tp cnti (Kresume c Vundef) phi') (b, Int.intval ofs) None) : thread_pool)).
  
Proof.
  (* we prove [mem_compatible_with] BEFORE aging, as it it slightly
    easier, proving [mem_compatible_with] after aging is a simple
    application of the lemma [mem_compatible_with_age] *)
  pose (tp__ := updLockSet (updThread i tp cnti (Kresume c Vundef) phi') (b, Int.intval ofs) None).
  assert (compat'' : mem_compatible_with tp__ m' Phi). {
    subst tp__.
    cleanup.
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
      assert (pr:containsThread (remLockSet tp (b, Int.intval ofs)) i) by auto.
      rewrite (maps_getthread i _ pr) in J.
      rewrite gRemLockSetRes with (cnti0 := cnti) in J. clear pr.
      revert Hadd_lock_res J.
      generalize (@getThreadR _ _ cnti) d_phi phi'.
      generalize (all_but i (maps (remLockSet tp (b, Int.intval ofs)))).
      cleanup.
      clear -lev.
      intros l a b c j h.
      rewrite Permutation.perm_swap in h.
      eapply joinlist_merge; eassumption.
      
    - (* mem_cohere' *)
      pose proof juice_join compat as J.
      pose proof all_cohere compat as MC.
      clear safety lock_coh jmstep.
      eapply (mem_cohere'_store _ tp _ _ _ (Int.zero) _ _ cnti Hcmpt).
      + cleanup.
        rewrite His_unlocked. simpl. congruence.
      + (* there is this hcmpt which is redundant, we can prove they're equal or think more to factorize it *)
        apply Hstore.
      + auto.
    
    - (* lockSet_Writable *)
      eapply lockSet_Writable_updLockSet_updThread; eauto.
      
    - (* juicyLocks_in_lockSet *)
      pose proof jloc_in_set compat as jl.
      intros loc sh1 sh1' pp z E.
      cleanup.
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
          rewrite His_unlocked.
          reflexivity.
        }
        destruct lj as (sh' & psh' & P & E).
        rewrite E. simpl. eauto.
  }
  
  pose proof mem_compatible_with_age compat'' (n := n) as compat'.
  unfold tp__ in *; clear tp__.
  
  apply state_invariant_c with (mcompat := compat').
  + (* level *)
    apply level_age_to. cleanup. omega.
    
  + (* matchfunspec *)
    revert gam. clear.
    apply matchfunspec_age_to.
    
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
        split; swap 1 2.
        - (* the rmap is unchanged (but we lose the SAT information) *)
          cut ((4 | Int.intval ofs) /\  (Int.intval ofs + 4 <= Int.modulus)%Z /\
               exists R0, (lkat R0 (b, Int.intval ofs)) Phi).
          { intros (align & bound & R0 & AP). repeat (split; auto).
            exists R0. revert AP. apply age_to_ind, lkat_hered. }
          cleanup.
          rewrite His_unlocked in lock_coh.
          destruct lock_coh as (H & (* ? & *) ? & align & bound & lk & _).
          eauto.
          
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
            * instantiate (1 := z).
              unfold size_chunk in *.
              unfold LKSIZE in *.
              omega.
            * unfold LKSIZE in *.
              omega.
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
            eapply lockSet_spec_2.
            * hnf; simpl. eauto.
            (* if LKSIZE>4
                instantiate (1 := ofs').
                lkomega. *)
            * cleanup. rewrite Eo. reflexivity.
          + rewrite gsoLockSet_1; auto.
            * eapply lockSet_spec_2.
              -- hnf; simpl. eauto. (* if LKSIZE>4 instantiate (1 := ofs'). lkomega. *)
              -- cleanup. rewrite Eo. reflexivity.
            * unfold far in *.
              simpl in *.
              zify.
              lkomega.
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
               omega.
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
        
        eapply jsafe_phi_jsafeN with (compat0 := compat) in safety.
        inversion safety as [ | ?????? step | ??????? ae Pre Post Safe | ????? Ha]; swap 2 3.
        - (* not corestep *)
          exfalso.
          clear -Hat_external step.
          apply corestep_not_at_external in step.
          rewrite jstep.JuicyFSem.t_obligation_3 in step.
          set (u := at_external _) in Hat_external.
          set (v := at_external _) in step.
          assert (u = v).
          { unfold u, v. f_equal.
            unfold SEM.Sem in *.
            rewrite SEM.CLN_msem.
            reflexivity. }
          congruence.
          
        - (* not halted *)
          exfalso.
          clear -Hat_external Ha.
          assert (Ae : at_external SEM.Sem c <> None). congruence.
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
          
          + assert (e = LOCK).
            { rewrite <-Ejuicy_sem in *.
              unfold juicy_sem in *.
              simpl in ae.
              congruence. }
            assert (args = Vptr b ofs :: nil).
            { rewrite <-Ejuicy_sem in *.
              unfold juicy_sem in *.
              simpl in ae.
              congruence. }
            subst e args; simpl.
            auto.
            
          + assert (e = LOCK).
            { rewrite <-Ejuicy_sem in *.
              unfold juicy_sem in *.
              simpl in ae.
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
              transitivity (level (getThreadR i tp cnti)); join_level_tac.
              rewrite getThread_level with (Phi := Phi). auto. apply compat.
            }
            
            split; [ | split].
            * auto.
            * rewr (level jm'). rewrite level_jm_. cleanup. omega.
            * simpl. rewrite Ejm'. do 3 REWR.
              eapply pures_same_eq_l.
              2:apply pures_age_eq; omega.
              apply pures_same_sym.
              apply join_sub_pures_same. exists d_phi. assumption.
          
          + (* we must satisfy the post condition *)
            assert (e = LOCK).
            { rewrite <-Ejuicy_sem in *.
              unfold juicy_sem in *.
              simpl in ae.
              congruence. }
            subst e.
            revert x Pre Post.
            funspec_destruct "acquire"; swap 1 2.
            { exfalso. unfold ef_id_sig, ef_sig in *.
              unfold funsig2signature in Heq_name; simpl in Heq_name. congruence. }
            intros x (Hargsty, Pre) Post.
            destruct Pre as (phi0 & phi1 & j & Pre).
            destruct (join_assoc (join_comm j) Hadd_lock_res) as (phi0' & jphi0' & jframe).
            exists (age_to n phi0'), (age_to n phi1).
            rewrite m_phi_jm_ in *.
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
              Unset Printing Implicit.
              destruct Pre as [[[A B] [C D]] E].
              simpl in *.
              split. 2:eapply necR_trans; [ | apply  age_to_necR ]; auto.
              split. now auto.
              split. now auto.
              unfold canon.SEPx in *.
              clear Post. simpl in *.
              rewrite seplog.sepcon_emp in *.
              rewrite seplog.sepcon_emp in D.
              exists (age_to n phi0), (age_to n d_phi); split3.
              -- apply age_to_join; auto.
              -- revert D. apply age_to_ind. apply pred_hered.
              -- specialize (lock_coh (b, Int.intval ofs)).
                 cleanup.
                 rewrite His_unlocked in lock_coh.
                 destruct lock_coh as [_ (align & bound & R' & lkat & sat)].
                 destruct sat as [sat | ?]. 2:congruence.
                 pose proof predat6 lkat as ER'.
                 assert (args = Vptr b ofs :: nil). {
                   revert Hat_external ae; clear.
                   unfold SEM.Sem in *.
                   rewrite SEM.CLN_msem. simpl.
                   congruence.
                 }
                 subst args.
                 assert (vx = Vptr b ofs). {
                   destruct C as [-> _].
                   clear.
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
                 pose proof predat4 D as ERx.
                 assert (join_sub phi0 Phi).
                 { join_sub_tac.
                   apply join_sub_trans with (getThreadR _ _ cnti). exists phi1. auto.
                   apply compatible_threadRes_sub, compat.
                 }
                 apply (@predat_join_sub _ Phi) in ERx; auto.
                 unfold Int.unsigned in *.
                 pose proof predat_inj ER' ERx as ER.
                 replace (age_by 1 d_phi) with (age_to n d_phi) in sat; swap 1 2.
                 {
                   unfold age_to in *. f_equal.
                   replace (level d_phi) with (level Phi); swap 1 2.
                   {
                     pose proof @compatible_lockRes_sub _ _ _ His_unlocked Phi ltac:(apply compat).
                     join_level_tac.
                   }
                   omega.
                 }
                 replace (level phi0) with (level Phi) in * by join_level_tac.
                 rewrite lev in *.
                 revert sat.
                 apply approx_eq_app_pred with (S n); auto.
                 rewrite level_age_to. auto.
                 replace (level d_phi) with (level Phi) in * by join_level_tac.
                 omega.
                 
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
      -- intros c' Ec'; spec safety c' Ec'. apply jsafe_phi_age_to; auto.
         apply jsafe_phi_downward. assumption.
      -- auto.
  
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
