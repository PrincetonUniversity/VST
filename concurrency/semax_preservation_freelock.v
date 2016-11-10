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
  (mem_cohere'_store : forall m tp m' b ofs i Phi
    (Hcmpt : mem_compatible tp m),
    lockRes tp (b, Int.intval ofs) <> None ->
    Mem.store
      Mint32 (restrPermMap (mem_compatible_locks_ltwritable Hcmpt))
      b (Int.intval ofs) (Vint i) = Some m' ->
    mem_compatible_with tp m Phi (* redundant with Hcmpt, but easier *) ->
    mem_cohere' m' Phi)
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
  
  destruct Precond as [[Hwritable _] [[B1 _] AT]].
  assert (Hreadable : readable_share shx) by (apply writable_readable; auto).
  
  (* [data_at_] from the precondition *)
  unfold canon.SEPx in *.
  simpl in AT.
  rewrite seplog.sepcon_emp in AT.
  
  (* value of [vx] *)
  simpl in B1.
  unfold lift, liftx in B1. simpl in B1.
  unfold lift, liftx in B1. simpl in B1.
  Lemma lockinv_isptr sh v R : lock_inv sh v R = (!! expr.isptr v && lock_inv sh v R)%logic.
  Admitted.
  rewrite lockinv_isptr in AT.
  rewrite log_normalize.sepcon_andp_prop' in AT.
  destruct AT as (IsPtr, AT).
  destruct vx as [ | | | | | b ofs ]; try inversion IsPtr; [ clear IsPtr ].
  
  assert (Eargs : args = Vptr b ofs :: nil)
    by (eapply shape_of_args; eauto).
  
  destruct AT as (phi0lockinv & phi0sat & jphi0 & Hlockinv & Hsat).
  
  unfold tlock in *.
  apply (lock_inv_rmap_freelock CS) in Hlockinv; auto. 2:admit. 2:admit (* to be added in invariant *).
  destruct Hlockinv as (phi0lockinv' & Hrmap00 & Hlkat).
  
  assert (Hpos'' : (0 < 4)%Z) by omega.
  pose proof rmap_freelock_join _ _ _ _ _ _ _ Hpos'' Hrmap00 jphi0 as Hrmap0.
  destruct Hrmap0 as (phi0' & Hrmap0 & jphi0').
  pose proof rmap_freelock_join _ _ _ _ _ _ _ Hpos'' Hrmap0 Join as Hrmap.
  pose proof Hrmap as Hrmap_.
  destruct Hrmap_ as (phi' & RLphi & j').
  assert (ji : join_sub (getThreadR _ _ cnti) Phi) by join_sub_tac.
  destruct ji as (psi & jpsi). cleanup.
  pose proof rmap_freelock_join _ _ _ _ _ _ _ Hpos'' RLphi jpsi as Hrmap'.
  destruct Hrmap' as (Phi' & Hrmap' & J').
  
  subst args.
  
  assert (locked : lockRes tp (b, Int.intval ofs) = Some None). {
    (* TODO : use preciseness and positivity here *)
    spec lock_coh (b, Int.intval ofs). cleanup.
    destruct (AMap.find _ _) as [o|] eqn:Eo. (* 2:reflexivity. exfalso.
    assert (C : exists (R : pred rmap), (lkat R (b, Int.intval ofs)) Phi).
    destruct o; breakhyps; eauto. clear lock_coh.
    destruct C as ((* sh &  *)R' & At).
    destruct Hrmap' as (_ & _ & inside).
    spec inside (b, Int.intval ofs).
    spec inside. split; auto; unfold Int.unsigned in *; lkomega.
    destruct inside as (sh'' & E & _).
    spec At (b, Int.intval ofs). simpl in At.
    spec At. now split; auto; lkomega.
    if_tac in At. 2:tauto.
    breakhyps. breakhyps. breakhyps.
    *) admit.
    admit.
  }
  
  eexists (m, ge, (sch, _)); split.
  
  { (* "progress" part of the proof *)
    constructor.
    
    eapply JuicyMachine.sync_step
    with (Htid := cnti); auto.
    
    eapply step_freelock
    with (c := ci) (Hcompat := mem_compatible_forget compat)
                   (R := Interp Rx) (phi' := phi').
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
  
  assert (mcompat' : mem_compatible_with' (age_tp_to n (remLockSet (updThread i tp cnti (Kresume ci Vundef) phi') (b, Int.intval ofs))) m (age_to n Phi')). {
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
      Lemma joinlist_swap {A} {JA : Join A} {PA : Perm_alg A} (a b x : A) l :
        @joinlist A JA (a :: b :: l) x = @joinlist A JA (b :: a :: l) x.
      Proof.
        apply prop_ext; split; apply joinlist_permutation; constructor.
      Qed.
      rewrite <-joinlist_merge in j. 2: apply Join.
      rewrite <-joinlist_merge in j. 2: apply jphi0.
      rewrite joinlist_swap.
      destruct j as (xi_ & jxi_ & jx1).
      pose proof rmap_freelock_join _ _ _ _ _ _ _ Hpos'' Hrmap00 jx1 as Hrmap1.
      destruct Hrmap1 as (Phi'_ & Hrmap'_ & J).
      assert (Phi'_ = Phi') by (eapply rmap_freelock_unique; eauto). subst Phi'_.
      exists xi_. auto.
Admitted.

Lemma preservation_freelock
  (lockSet_Writable_updLockSet_updThread
     : forall (m m' : Memory.mem) (i : tid) (tp : thread_pool) (Phi : LocksAndResources.res),
       mem_compatible_with tp m Phi ->
       forall (cnti : containsThread tp i) (b : block) (ofs : int) (ophi : option rmap)
         (ophi' : LocksAndResources.lock_info) (c' : ctl) (phi' : LocksAndResources.res) 
         (z : int) (pr : mem_compatible tp m),
       AMap.find (elt:=option rmap) (b, Int.intval ofs) (lset tp) = Some ophi ->
       Mem.store Mint32 (restrPermMap (mem_compatible_locks_ltwritable pr)) b (Int.intval ofs) (Vint z) = Some m' ->
       lockSet_Writable (lset (updLockSet (updThread i tp cnti c' phi') (b, Int.intval ofs) ophi')) m') 
  (mem_cohere'_store : forall m tp m' b ofs i Phi
    (Hcmpt : mem_compatible tp m),
    lockRes tp (b, Int.intval ofs) <> None ->
    Mem.store
      Mint32 (restrPermMap (mem_compatible_locks_ltwritable Hcmpt))
      b (Int.intval ofs) (Vint i) = Some m' ->
    mem_compatible_with tp m Phi (* redundant with Hcmpt, but easier *) ->
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
  (m' : Memory.mem)
  (i : tid)
  (sch : list tid)
  (tp : thread_pool)
  (Phi : rmap)
  (lev : level Phi = S n)
  (gam : matchfunspec (filter_genv ge) Gamma Phi)
  (sparse : lock_sparsity (lset tp))
  (wellformed : threads_wellformed tp)
  (unique : unique_Krun tp (i :: sch))
  (Ei cnti : ssrnat.leq (S i) (pos.n (num_threads tp)) = true)
  (ci : code)
  (Eci : getThreadC i tp cnti = Kblocked ci)
  (Htid : ssrnat.leq (S i) (pos.n (num_threads tp)) = true)
  (El : Logic.True -> level (getThreadR i tp Htid) - 1 = n)
  (c : code)
  (b : block)
  (ofs : int)
  (R : pred rmap)
  (phi' : rmap)
  (sh : Share.t)
  (Hinv : invariant tp)
  (Hthread : getThreadC i tp Htid = Kblocked c)
  (Hat_external : at_external SEM.Sem c = Some (FREE_LOCK, Vptr b ofs :: nil))
  (Hcompatible : mem_compatible tp m')
  (Haccess : (address_mapsto Mint32 (Vint Int.zero) sh Share.top (b, Int.intval ofs)) phi')
  (Hlock' : exists val : memval, phi' @ (b, Int.intval ofs) = YES sh pfullshare (VAL val) NoneP)
  (INV : state_invariant Jspec' Gamma (S n) (m', ge, (i :: sch, tp)))
  (compat : mem_compatible_with tp m' Phi)
  (lock_coh : lock_coherence' tp Phi m' compat)
  (safety : threads_safety Jspec' m' ge tp Phi compat (S n))
  (Hcmpt : mem_compatible tp m')
  (compat_aged : mem_compatible_with (age_tp_to n tp) m' (age_to n Phi))
  (Hlock : getThreadR i tp Htid @ (b, Int.intval ofs) = YES sh pfullshare (LK LKSIZE) (pack_res_inv R))
  (Hct : forall ofs' : Z,
        (Int.intval ofs < ofs' < Int.intval ofs + LKSIZE)%Z ->
        exists (val : memval),
          getThreadR i tp Htid @ (b, ofs') = YES sh pfullshare (CT (ofs' - Int.intval ofs)%Z) NoneP /\
          phi' @ (b, ofs') = YES sh pfullshare (VAL val) NoneP)
  (Hj_forward : forall loc : block * Z,
               b <> fst loc \/ ~ (Int.intval ofs <= snd loc < Int.intval ofs + LKSIZE)%Z ->
               getThreadR i tp Htid @ loc = phi' @ loc)
  (tp_ := age_tp_to (level (getThreadR i tp Htid) - 1)
           (remLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs)) : thread_pool)
  (compat_ := mem_compatible_with tp_ m' (age_to n Phi) : Prop)
  (jmstep : @JuicyMachine.machine_step ge (i :: sch) nil tp m' sch nil
             (age_tp_to n
                (remLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs))) m')
  (Htstep : syncStep ge Htid Hcmpt
             (age_tp_to n
                (remLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs))) m'
             (Events.freelock (b, Int.intval ofs))) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m', ge, (sch, (age_tp_to n
                (remLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs))))).

Proof.
Abort.
