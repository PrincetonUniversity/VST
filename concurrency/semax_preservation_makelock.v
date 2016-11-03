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

Lemma join_pures_same phi1 phi2 phi3 :
  join phi1 phi2 phi3 ->
  pures_same phi1 phi2 /\ pures_same phi2 phi3 /\ pures_same phi1 phi3.
Proof.
  intros j; split; [ | split].
  - apply joins_pures_same. exists phi3; auto.
  - apply join_sub_pures_same. exists phi1; auto.
  - apply join_sub_pures_same. exists phi2; auto.
Qed.

Lemma pures_same_trans phi1 phi2 phi3 :
  pures_same phi1 phi2 ->
  pures_same phi2 phi3 ->
  pures_same phi1 phi3.
Proof.
  intros A B.
  intros x k p.
  spec A x k p.
  spec B x k p.
  tauto.
Qed.

Lemma pures_same_necR phi1 phi2 phi1' :
  level phi1 = level phi2 ->
  pures_same phi1 phi2 ->
  necR phi1 phi1' ->
  exists phi2',
    level phi1' = level phi2' /\
    pures_same phi1' phi2' /\
    necR phi2 phi2'.
Proof.
  intros EL E n; revert phi2 EL E. induction n.
  - (* age *)
    rename y into x'. rename H into A.
    intros y L E.
    assert (Hy' : exists y', age y y'). {
      apply age1_levelS in A. destruct A as (n, A).
      apply levelS_age1 with n. congruence.
    }
    destruct Hy' as (y', Ay).
    assert (level x' = level y') by (apply age_level in A; apply age_level in Ay; congruence).
    exists y'. split;[|split]. assumption. 2: constructor; assumption.
    intros l k pp.
    pose proof @age_resource_at _ _ l A as Hx.
    pose proof @age_resource_at _ _ l Ay as Hy.
    rewrite Hx, Hy.
    spec E l.
    destruct (x @ l), (y @ l); split; intro; simpl in *; breakhyps.
    + spec E k0 p. destruct E as [_ E]. autospec E. discriminate.
    + spec E k1 p1. destruct E as [_ E]. autospec E. discriminate.
    + spec E k0 p. destruct E as [E _]. autospec E. discriminate.
    + spec E k0 p. destruct E as [E _]. autospec E. discriminate.
    + spec E k0 p. destruct E as [E _]. autospec E. injection E as -> ->. rewr (PURE k pp). congruence. 
    + spec E k0 p. destruct E as [E _]. autospec E. injection E as -> ->. rewr (PURE k pp). congruence.
  - (* reflexivity case *)
    intuition eauto.
  - (* transitivity case *)
    intros x' Lx Ex.
    spec IHn1 x' Lx Ex. destruct IHn1 as (y' & Ly & Ey & ny).
    spec IHn2 y' Ly Ey. destruct IHn2 as (z' & Lz & Ez & nz).
    exists z'. split; auto. split; auto. apply necR_trans with y'; auto.
Qed.

Lemma pures_same_matchfunspec e Gamma phi1 phi2 :
  level phi1 = level phi2 ->
  pures_same phi1 phi2 ->
  matchfunspec e Gamma phi1 ->
  matchfunspec e Gamma phi2.
Proof.
  intros EL E M b fs.
  specialize (M b fs). destruct fs.
  intros phi2' necr2.
  apply pures_same_sym in E.
  symmetry in EL.
  destruct (pures_same_necR _ _ _ EL E necr2) as (phi1' & EL' & E' & necr1).
  spec M phi1' necr1.
  intros F; apply M; clear M.
  destruct F as (pp & At). exists pp.
  unfold app_pred in *. simpl in *.
  spec E' (b, 0%Z). rewrite At in E'.
  spec E' (FUN f c) (preds_fmap (approx (level phi2')) (approx (level phi2')) pp).
  destruct E' as [E' _]. autospec E'. rewrite E'. do 3 f_equal; auto.
Qed.

Lemma matchfunspec_common_join e Gamma phi phi' psi Phi Phi' :
  join phi psi Phi ->
  join phi' psi Phi' ->
  matchfunspec e Gamma Phi ->
  matchfunspec e Gamma Phi'.
Proof.
  intros j j'.
  apply pures_same_matchfunspec. now join_level_tac.
  apply join_pures_same in j.
  apply join_pures_same in j'.
  apply pures_same_trans with psi; try tauto.
  apply pures_same_sym; tauto.
Qed.

Lemma perm_of_res'_resource_fmap r f g : perm_of_res' (resource_fmap f g r) = perm_of_res' r.
Proof.
  destruct r; reflexivity.
Qed.

Lemma perm_of_res'_age_to n phi loc : perm_of_res' (age_to n phi @ loc) = perm_of_res' (phi @ loc).
Proof.
  rewrite age_to_resource_at.
  apply perm_of_res'_resource_fmap.
Qed.

Lemma approx_approx n x : approx n (approx n x) = approx n x.
Proof.
  pose proof approx_oo_approx n as E.
  apply equal_f with (x0 := x) in E.
  apply E.
Qed.

Lemma approx'_approx n n' x : n' <= n -> approx n (approx n' x) = approx n' x.
Proof.
  intros l.
  pose proof approx'_oo_approx _ _ l as E.
  apply equal_f with (x0 := x) in E.
  apply E.
Qed.

Lemma approx_approx' n n' x : n' <= n -> approx n' (approx n x) = approx n' x.
Proof.
  intros l.
  pose proof approx_oo_approx' _ _ l as E.
  apply equal_f with (x0 := x) in E.
  apply E.
Qed.

(* TODO factor this above progress *)
Lemma shape_of_args
  : forall (F V : Type) (args : list val) (b : block) (ofs : int) (ge : Genv.t F V),
    Val.has_type_list args (AST.Tint :: nil) ->
    Vptr b ofs =
    expr.eval_id _lock (make_ext_args (filter_genv (symb2genv (Genv.genv_symb ge))) (_lock :: nil) args) ->
    args = Vptr b ofs :: nil.
Admitted.

(* Weaker statement than preservation for makelock, enough to prove *)
Lemma safety_induction_makelock Gamma n state
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
  blocked_at_external state MKLOCK ->
  state_invariant Jspec' Gamma (S n) state ->
  exists state',
    state_step state state' /\
    (state_invariant Jspec' Gamma n state' \/
     state_invariant Jspec' Gamma (S n) state').
Proof.
  assert (Hpos : (0 < LKSIZE)%Z) by reflexivity.
  intros ismakelock.
  intros I.
  inversion I as [m ge sch_ tp Phi En gam compat sparse lock_coh safety wellformed unique E]. rewrite <-E in *.
  unfold blocked_at_external in *.
  destruct ismakelock as (i & cnti & sch & ci & args & -> & Eci & atex).
  pose proof (safety i cnti tt) as safei.
  
  rewrite Eci in safei.
  unfold jsafeN, juicy_safety.safeN in safei.
  
  inversion safei
    as [ | ?????? bad | n0 z c m0 e args0 x at_ex Pre SafePost | ????? bad ];
    [ now erewrite cl_corestep_not_at_external in atex; [ discriminate | eapply bad ]
    | subst | now inversion bad ].
  subst.
  simpl in at_ex. assert (args0 = args) by congruence; subst args0.
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
  rewrite data_at__isptr in AT.
  destruct AT as (IsPtr, AT).
  destruct vx as [ | | | | | b ofs ]; try inversion IsPtr; [ clear IsPtr ].
  
  assert (Eargs : args = Vptr b ofs :: nil)
    by (eapply shape_of_args; eauto).
  
  assert (Hm' : exists m', Mem.store Mint32 (m_dry (personal_mem _ _ (thread_mem_compatible (mem_compatible_forget compat) cnti))) b (Int.intval ofs) (Vint Int.zero) = Some m'). {
    clear -AT Join Hwritable.
    unfold tlock in AT.
    destruct AT as (AT1, AT2).
    destruct AT2 as [A B]. clear A. (* it is 4 = 4 *)
    simpl in B. unfold mapsto_memory_block.at_offset in B.
    simpl in B. unfold nested_field_lemmas.nested_field_offset in B.
    simpl in B. unfold nested_field_lemmas.nested_field_type in B.
    simpl in B. unfold reptype_lemmas.default_val in B.
    simpl in B. unfold Znth in B.
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
    destruct B as [B|B]. now destruct B as [[]].
    destruct B as [_ (v2', Hmaps)].
    rewrite reptype_lemmas.int_add_repr_0_r in *.
    apply mapsto_can_store with (v := v2') (rsh := (Share.unrel Share.Lsh shx)).
    simpl (m_phi _).
    (* if array size > 4:
          rewrite <-TT_sepcon_TT.
          rewrite <-sepcon_assoc. 
     *)
    exists phi0, phi1; split; auto. split; auto.
    (* if array size > 4:
          exists phi00, phi01; split; auto. split; auto.
     *)
    exact_eq Hmaps.
    f_equal.
    f_equal.
    apply writable_share_right. assumption.
  }
  destruct Hm' as (m', Hstore).
  
  unfold tlock in *.
  match type of AT with context[Tarray _ ?n] => assert (Hpos' : (0 < n)%Z) by omega end.
  pose proof data_at_rmap_makelock CS as RL.
  specialize (RL shx b ofs (Interp Rx) phi0 _ Hpos' Hwritable AT).
  destruct RL as (phi0' & RL0 & Hlkat).
  
  match type of Hlkat with context[LK_at _ ?n] => assert (Hpos'' : (0 < n)%Z) by omega end.
  pose proof rmap_makelock_join _ _ _ _ _ _ _ Hpos'' RL0 Join as Hrmap.
  pose proof Hrmap as Hrmap_.
  destruct Hrmap_ as (phi' & RLphi & j').
  assert (ji : join_sub (getThreadR _ _ cnti) Phi) by join_sub_tac.
  destruct ji as (psi & jpsi). cleanup.
  pose proof rmap_makelock_join _ _ _ _ _ _ _ Hpos'' RLphi jpsi as Hrmap'.
  destruct Hrmap' as (Phi' & Hrmap' & J').
  
  subst args.
  
  eexists (m', ge, (sch, _)); split.
  
  { (* "progress" part of the proof *)
    constructor.
    
    eapply JuicyMachine.sync_step
    with (Htid := cnti); auto.
    
    eapply step_mklock
    with (c := ci) (Hcompatible := mem_compatible_forget compat)
                   (R := Interp Rx) (phi' := phi').
    all: try reflexivity.
    all: try eassumption.
    unfold SEM.Sem in *. rewrite SEM.CLN_msem. assumption.
  }
  
  (* we move on to the preservation part *)
  
  simpl (m_phi _).
  assert (Ephi : level (getThreadR _ _ cnti) = S n). {
    rewrite getThread_level with (Phi := Phi). auto. apply compat.
  }
  assert (El : level (getThreadR _ _ cnti) - 1 = n) by omega.
  cleanup.
  rewrite El.
  
  (*
  assert (j : join_sub (getThreadR i tp cnti) Phi) by apply compatible_threadRes_sub, compat.
  destruct j as (psi & jphi).
  pose proof rmap_makelock_join _ _ _ _ _ _ _ Hpos Hrmap jphi as RL.
  *)
  
  assert (LPhi' : level Phi' = level Phi) by (destruct Hrmap'; auto).
  
  assert (notfound : lockRes tp (b, Int.intval ofs) = None). {
    spec lock_coh (b, Int.intval ofs). cleanup.
    destruct (AMap.find _ _) as [o|] eqn:Eo. 2:reflexivity. exfalso.
    assert (C : exists (R : pred rmap), (lkat R (b, Int.intval ofs)) Phi).
    destruct o; breakhyps; eauto. clear lock_coh.
    destruct C as ((* sh &  *)R' & At).
    destruct Hrmap' as (_ & _ & inside).
    spec inside (b, Int.intval ofs).
    spec inside. split; auto; unfold Int.unsigned in *; lkomega.
    destruct inside as (val' & sh'' & E & _).
    spec At (b, Int.intval ofs). simpl in At.
    spec At. now split; auto; lkomega.
    if_tac in At. 2:tauto.
    breakhyps.
  }
  
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
  
  assert (mcompat' : mem_compatible_with' (age_tp_to n (updLockSet (updThread i tp cnti (Kresume ci Vundef) phi') (b, Int.intval ofs) None)) m' (age_to n Phi')). {
    constructor.
    + (* join_all *)
      (* rewrite <-Hpersonal_juice. autospec El. cleanup. rewrite El. *)
      apply join_all_age_to. cleanup. omega.
      pose proof juice_join compat as j.
      rewrite join_all_joinlist.
      rewrite join_all_joinlist in j.
      rewrite maps_updlock1.
      rewrite maps_remLockSet_updThread.
      rewrite maps_updthread.
      rewrite maps_getlock1. 2:assumption.
      rewrite maps_getthread with (cnti := cnti) in j.
      destruct j as (psi_ & jpsi_ & jphi_).
      exists psi; split. 2:assumption.
      cut (psi = psi_). now intros <-; auto.
      eapply join_canc. eapply join_comm. apply jpsi. eapply join_comm. eauto.
    
    + (* mem_cohere' *)
      split.
      * intros rsh sh v loc pp E''.
        destruct (adr_range_dec (b, Int.unsigned ofs) LKSIZE loc) as [r|nr].
        -- exfalso.
           destruct Hrmap' as (_ & _ & inside). spec inside loc. autospec inside.
           rewrite age_to_resource_at in E''.
           destruct inside as (? & ? & _ & E').
           rewrite E' in E''. if_tac in E''; simpl in E''; congruence.
        -- destruct (Phi'rev _ _ _ _ _ nr E'') as (pp' & E & ->).
           cut (contents_at m loc = v /\ pp' = NoneP).
           { intros []; split; subst pp'; auto.
             destruct loc as (b1, ofs1).
             destruct (store_outside' _ _ _ _ _ _ Hstore) as (outside & _ & _).
             spec outside b1 ofs1.
             destruct outside as [(->, r) | same].
             - exfalso. apply nr. split; auto.
             - rewrite <-same.
               unfold personal_mem.
               change (m_dry (mkJuicyMem ?m _ _ _ _ _)) with m.
               rewrite <-juicyRestrictContents. auto.
           }
           eapply (cont_coh (all_cohere compat)); eauto.
      
      * (* max_access_cohere' *)
        pose proof        max_coh ( all_cohere compat) as M.
        intros loc; spec M loc.
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
        destruct Hrmap' as (_ & Same & Changed).
        spec Same loc. spec Changed loc.
        destruct (adr_range_dec (b, Int.unsigned ofs) (4 * 1) loc) as [r|nr].
        -- autospec Changed.
           destruct Changed as (val & sh & -> & ->).
           if_tac; reflexivity.
        -- autospec Same. rewrite <-Same.
           reflexivity.
      
      * (* alloc_cohere *)
        pose proof all_coh ((all_cohere compat)) as A.
        unfold alloc_cohere in *.
        destruct (store_outside' _ _ _ _ _ _ Hstore) as (_ & _ & <-).
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
        destruct Hrmap' as (_ & _ & inside).
        specialize (inside (b, ofs0)).
        spec C (b, ofs0).
        spec inside. hnf. split; auto.
        destruct inside as (val & sh & E & _).
        rewrite E in C.
        unfold max_access_at in *.
        eapply po_trans. eassumption.
        unfold perm_of_res' in *.
        unfold perm_of_sh in *.
        Ltac share_tac :=
          change (pshare_sh pfullshare) with Share.top in *;
          pose proof Share.nontrivial;
          try tauto.
        repeat if_tac; try constructor; share_tac.
      * eapply loc_writable; eauto.
    
    + (* juicyLocks_in_lockSet *)
      intros loc sh psh P z E''.
      unfold lockGuts in *.
      rewrite lset_age_tp_to.
      rewrite isSome_find_map.
      simpl.
      rewrite AMap_find_add. if_tac [<- | ne]. reflexivity.
      destruct (rmap_unage_YES _ _ _ _ _ _ _ APhi' E'') as (pp, E').
      cut (Phi @ loc = YES sh psh (LK z) pp).
      { intros; eapply (jloc_in_set compat); eauto. }
      rewrite <-E'.
      destruct Hrmap' as (_ & outside & inside).
      apply outside.
      intros r.
      spec inside loc r.
      destruct inside as (val & sh' & _ & E1).
      rewrite E1 in E'.
      if_tac in E'.
      * unfold Int.unsigned in *. congruence.
      * congruence.
    
    + (* lockSet_in_juicyLocks *)
      cleanup.
      pose proof lset_in_juice compat as J.
      intros loc. spec J loc.
      simpl.
      rewrite isSome_find_map.
      simpl.
      unfold lset.
      rewrite AMap_find_add.
      if_tac.
      * intros []. subst loc. change Int.intval with Int.unsigned in *.
        destruct Hrmap' as (_ & _ & inside). spec inside (b, Int.unsigned ofs). spec inside.
        { split; auto; omega. }
        if_tac in inside. 2:tauto.
        rewrite age_to_resource_at.
        breakhyps.
        rewr (Phi' @ (b, Int.unsigned ofs)). simpl. eauto.
      * intros tr. spec J tr. auto.
        destruct Hrmap' as (_ & outside & inside).
        spec outside loc.
        spec outside.
        { intros r. spec inside loc r. breakhyps. }
        rewrite age_to_resource_at, <-outside. clear outside.
        breakhyps.
        rewr (Phi @ loc). simpl; eauto.
  }
  
  left.
  unshelve eapply state_invariant_c with (PHI := age_to n Phi') (mcompat := mcompat').
  - (* level *)
    apply level_age_to. omega.
  
  - (* matchfunspec *)
    apply matchfunspec_age_to.
    eapply matchfunspec_common_join with (Phi := Phi); eauto.
  
  - (* lock sparsity *)
    simpl.
    cleanup.
    unfold lock_sparsity in *.
    cut (forall loc, AMap.find loc (lset tp) <> None ->
                loc = (b, Int.intval ofs) \/ fst loc <> b \/ fst loc = b /\ far (snd loc) (Int.intval ofs)). {
      clear -sparse.
      intros H loc1 loc2.
      do 2 rewrite AMap_find_map_option_map. cleanup.
      do 2 rewrite AMap_find_add.
      if_tac [<- | ne1]; if_tac [<- | ne2]; simpl.
      - auto.
      - intros _ found2.
        spec H loc2. spec H. destruct (AMap.find loc2 _); auto; congruence.
        breakhyps. right. right. split; auto. unfold far in *; auto. zify. omega.
      - intros found1 _.
        spec H loc1. spec H. destruct (AMap.find loc1 _); auto; congruence.
        auto.
      - intros found1 found2.
        spec sparse loc1 loc2.
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
    spec AT' loc.
    destruct Hrmap' as (_ & outside & inside).
    spec AT'. destruct loc; split; auto; lkomega.
    if_tac in AT'. 2:tauto.
    spec outside loc. assert_specialize outside as nr. {
      intros r. spec inside loc r.
      breakhyps.
    }
    unfold far.
    destruct loc as (b', ofs'). simpl. simpl in nr.
    unfold Int.unsigned in *. unfold LKSIZE.
    destruct (eq_dec b b') as [<- | ?]; [ | now auto ].
    right; split; auto.
    spec AT'' (b, Int.intval ofs).
    spec inside (b, Int.intval ofs). spec inside. now split; auto; lkomega.
    destruct (adr_range_dec (b, ofs') LKSIZE (b, Int.intval ofs)) as [r|nr'].
    + autospec AT''. if_tac in AT''; breakhyps.
    + clear -nr nr'. simpl in nr'. unfold LKSIZE in *.
      do 2 match goal with H : ~(b = b /\ ?P) |- _ => assert (~P) by tauto; clear H end.
      zify. omega.
  
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
        admit (* should be fine *).
      * (* LK_at *)
        subst loc.
        exists (Interp Rx).
        intros loc r.
        destruct Hrmap' as (_ & _ & inside). spec inside loc r.
        rewrite age_to_resource_at.
        breakhyps.
        rewr (Phi' @ loc).
        if_tac.
        -- unfold Int.unsigned in *.
           if_tac. 2:tauto.
           unfold LKSIZE in *.
           unfold sync_preds_defs.pack_res_inv in *.
           simpl.
           eexists _, _. f_equal. f_equal. extensionality Ts.
           eauto.
           rewrite level_age_to. 2:omega.
           apply approx_approx'. omega.
        -- unfold Int.unsigned in *. if_tac. tauto.
           simpl. eauto.
    
    + spec lock_coh loc.
      destruct (AMap.find loc _) as [o|] eqn:Eo.
      * destruct o; unfold option_map; destruct lock_coh as (load & coh); split; swap 2 3.
        -- admit. (* load *)
        -- admit. (* load *)
        -- admit. (* lkat *)
        -- admit. (* lkat *)
      * unfold option_map.
        destruct (adr_range_dec (b, Int.unsigned ofs) LKSIZE loc) as [r|nr].
        -- destruct Hrmap' as (_ & _ & inside).
           spec inside loc r. rewrite isLK_age_to.
           if_tac in inside; intros []; intros ? ?; breakhyps.
        -- destruct Hrmap' as (_ & outside & _).
           rewrite age_to_resource_at.
           spec outside loc nr. rewrite <-outside.
           clear -lock_coh.
           unfold isLK, isCT in *.
           destruct (Phi @ loc) as [t0 | t0 p [] p0 | k p]; (* split; *) simpl in *; intro; breakhyps.
           apply lock_coh; eauto.
  
  - (* safety *)
    {
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
              admit (* use join to solve this *).
              (* apply pures_age_eq. omega. *)
              
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
              exists b, ofs; split. auto.
              intros loc. simpl.
              destruct RL0 as (Lphi0 & outside & inside).
              pose proof data_at_unfold _ _ _ _ _ 1 Hwritable AT as Hbefore.
              spec Hbefore loc.
              if_tac [r|nr]; [ if_tac [e|ne] | ].
              -- rewrite writable_share_right; auto.
                 exists top_share_nonunit.
                 spec inside loc r.
                 if_tac in inside. 2:unfold Int.unsigned in *; congruence.
                 destruct inside as (val & sh & E & E').
                 if_tac in Hbefore. 2:tauto.
                 rewrite age_to_resource_at.
                 destruct Hbefore as (v, Hb). rewrite Hb in E.
                 injection E as -> <-.
                 rewrite E'. simpl.
                 unfold pfullshare.
                 rewrite approx_approx'. 2: join_level_tac; omega.
                 rewrite level_age_to.  2: join_level_tac; omega.
                 reflexivity.
              -- rewrite writable_share_right; auto.
                 exists top_share_nonunit.
                 spec inside loc r.
                 if_tac in inside. unfold Int.unsigned in *; congruence.
                 destruct inside as (val & sh & E & E').
                 if_tac in Hbefore. 2:tauto.
                 rewrite age_to_resource_at.
                 destruct Hbefore as (v, Hb). rewrite Hb in E.
                 injection E as -> <-.
                 rewrite E'. simpl.
                 unfold pfullshare, NoneP.
                 reflexivity.
              -- if_tac in Hbefore. tauto.
                 spec outside loc nr.
                 rewrite age_to_resource_at, <-outside.
                 apply empty_NO in Hbefore.
                 destruct Hbefore as [-> | (? & ? & ->)]; simpl.
                 ++ apply NO_identity.
                 ++ apply PURE_identity.
          
          + exact_eq Safe'.
            unfold jsafeN, safeN.
            f_equal.
            congruence.
      }
    
    * (* safety of other thread: copy-paste the one from
      acquire/release see if we can have a lemma instead *)
      REWR.
      cut (forall c (cntj : containsThread tp j),
              jsafeN Jspec' ge (S n) ora c (jm_ cntj compat) ->
              jsafeN Jspec' ge n ora c (jm_ lj mcompat')).
      {
        intros HH.
        destruct (@getThreadC j tp lj) eqn:E.
        - unshelve eapply HH; auto.
        - unshelve eapply HH; auto.
        - intros c' Ec'. eapply HH; auto.
        - constructor.
      }
      intros c0 cntj Safe.
      apply jsafeN_downward in Safe.
      apply jsafeN_age_to with (l := n) in Safe; auto.
      revert Safe.
      apply jsafeN_mem_equiv. 2: now apply Jspec'_juicy_mem_equiv.
      split.
      -- rewrite m_dry_age_to.
         unfold jm_ in *.
         set (@mem_compatible_forget _ _ _ _) as cmpt; clearbody cmpt.
         set (@mem_compatible_forget _ _ _ _) as cmpt'; clearbody cmpt'.
         match goal with
           |- context [thread_mem_compatible ?a ?b] =>
           generalize (thread_mem_compatible a b); intros pr
         end.
         match goal with
           |- context [thread_mem_compatible ?a ?b] =>
           generalize (thread_mem_compatible a b); intros pr'
         end.
         
         eapply mem_equiv_trans.
         ++ unshelve eapply personal_mem_equiv_spec with (m' := m').
            ** REWR in pr'.
               REWR in pr'.
               REWR in pr'.
               admit. (* differ here from acquire/release *)
               (*
               eapply mem_cohere_sub with Phi.
               eapply mem_cohere'_store. 2:apply Hstore. cleanup; congruence. auto.
               apply compatible_threadRes_sub. apply compat.
               *)
            ** pose proof store_outside' _ _ _ _ _ _ Hstore as STO.
               simpl in STO. apply STO.
            ** pose proof store_outside' _ _ _ _ _ _ Hstore as STO.
               destruct STO as (_ & ACC & _).
               intros loc.
               apply equal_f with (x := loc) in ACC.
               apply equal_f with (x := Max) in ACC.
               admit. (*
               rewrite restrPermMap_Max' in ACC.
               apply ACC. *)
            ** intros loc yes.
               pose proof store_outside' _ _ _ _ _ _ Hstore as STO.
               destruct STO as (CON & _ & _).
               specialize (CON (fst loc) (snd loc)).
               destruct CON as [CON|CON].
               --- exfalso.
                   destruct loc as (b', ofs'); simpl in CON.
                   destruct CON as (<- & int).
                   clear safety    Hstore  lj cmpt' pr'.
                   specialize (lock_coh (b, Int.intval ofs)).
                   cleanup.
                   rewrite notfound in lock_coh.
                   (*
                   destruct lock_coh as (_ & (* sh' & *) R' & lk).
                   apply isVAL_join_sub with (r2 := Phi @ (b, ofs')) in yes.
                   2: now apply resource_at_join_sub; join_sub_tac.
                   specialize (lk (b, ofs')).
                   simpl in lk.
                   spec lk. now split; auto; lkomega.
                   unfold isVAL in *.
                   if_tac in lk.
                   +++ breakhyps.
                       destruct (Phi @ (b, ofs')) as [t0 | t0 p [] p0 | k p]; try tauto.
                       congruence.
                   +++ breakhyps.
                       destruct (Phi @ (b, ofs')) as [t0 | t0 p [] p0 | k p]; try tauto.
                       congruence.
                    *)
                   admit.
               --- admit. (* rewrite restrPermMap_contents in CON.
                   apply CON. *)
         ++ apply mem_equiv_refl'.
            apply m_dry_personal_mem_eq.
            intros loc.
            REWR.
            REWR.
            REWR.                  
            REWR.
      -- REWR.
         rewrite m_phi_jm_.
         rewrite m_phi_jm_.
         REWR.
         REWR.
         REWR.
    }
  
  - (* threads_wellformed *)
    intros j lj.
    specialize (wellformed j lj).
    unshelve erewrite <-gtc_age. auto.
    unshelve erewrite gLockSetCode; auto.
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
    apply no_Krun_updLockSet.
    apply no_Krun_stable. congruence.
    eapply unique_Krun_no_Krun. eassumption.
    instantiate (1 := cnti). rewr (getThreadC i tp cnti).
    congruence.
  Unshelve. exists Phi. apply compat.
Admitted.

(*
Lemma preservation_makelock
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
  (m m' : Memory.mem)
  (i : tid)
  (sch : list tid)
  (tp tp' : thread_pool)
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
  (ev : Events.sync_event)
  (Hcmpt : mem_compatible tp m)
  (Htid : ssrnat.leq (S i) (pos.n (num_threads tp)) = true)
  (HschedN : SCH.schedPeek (i :: sch) = Some i)
  (Htstep : syncStep ge Htid Hcmpt tp' m' ev)
  (jmstep : @JuicyMachine.machine_step ge (i :: sch) nil tp m sch nil tp' m')
  (tp_ := tp' : thread_pool)
  (m_ := m' : Memory.mem)
  (El : Logic.True -> level (getThreadR i tp Htid) - 1 = n)
  (compat_aged : mem_compatible_with (age_tp_to n tp) m (age_to n Phi))
  (tp'0 tp'' : thread_pool)
  (jm : juicy_mem)
  (c : code)
  (b : block)
  (ofs : int)
  (R : pred rmap)
  (phi' : rmap)
  (m'0 : Memory.mem)
  (Hcompatible : mem_compatible tp m)
  (Hinv : invariant tp)
  (Hthread : getThreadC i tp Htid = Kblocked c)
  (Hat_external : at_external SEM.Sem c = Some (MKLOCK, Vptr b ofs :: nil))
  (* (Hright_juice : m = m_dry jm) *)
  (Hpersonal_perm : personal_mem m (getThreadR i tp Htid) (thread_mem_compatible Hcompatible Htid) = jm)
  (Hpersonal_juice : getThreadR i tp Htid = m_phi jm)
  (Hstore : Mem.store Mint32 (m_dry jm) b (Int.intval ofs) (Vint Int.zero) = Some m')
  (Hrmap : rmap_makelock (getThreadR i tp cnti) phi' (b, Int.unsigned ofs) R LKSIZE)
  (Htp' : tp'0 = updThread i tp Htid (Kresume c Vundef) phi')
  (Htp'' : tp' = age_tp_to (level (m_phi jm) - 1) (updLockSet tp'0 (b, Int.intval ofs) None))
  (H : tp'' = tp')
  (H0 : m'0 = m')
  (H1 : Events.mklock (b, Int.intval ofs) = ev) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m_, ge, (sch, tp_)).

Proof.
  clear lockSet_Writable_updLockSet_updThread.
  clear mem_cohere'_store.
  clear personal_mem_equiv_spec.
  assert (Hpos : (0 < LKSIZE)%Z) by reflexivity.
  assert (j : join_sub (getThreadR i tp cnti) Phi) by apply compatible_threadRes_sub, compat.
  destruct j as (psi & jphi).
  pose proof rmap_makelock_join _ _ _ _ _ _ _ Hpos Hrmap jphi as RL.
  destruct RL as (Phi' & Hrmap' & jphi').
  
  assert (cnti = Htid) by apply proof_irr; subst Htid.
  
  assert (LPhi' : level Phi' = level Phi) by (destruct Hrmap'; auto).
  
  assert (notfound : lockRes tp (b, Int.intval ofs) = None). {
    spec lock_coh (b, Int.intval ofs). cleanup.
    destruct (AMap.find _ _) as [o|] eqn:Eo. 2:reflexivity. exfalso.
    assert (C : exists (R : pred rmap), (lkat R (b, Int.intval ofs)) Phi).
    destruct o; breakhyps; eauto. clear lock_coh.
    destruct C as ((* sh &  *)R' & At).
    destruct Hrmap' as (_ & _ & inside).
    spec inside (b, Int.intval ofs).
    spec inside. split; auto; unfold Int.unsigned in *; lkomega.
    destruct inside as (val' & sh'' & E & _).
    spec At (b, Int.intval ofs). simpl in At.
    spec At. now split; auto; lkomega.
    if_tac in At. 2:tauto.
    breakhyps.
  }
  
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
  
  assert (mcompat' : mem_compatible_with' tp_ m_ (age_to n Phi')). {
    subst m_ tp_ m'0 tp'' tp'0 tp'.
    constructor.
    + (* join_all *)
      rewrite <-Hpersonal_juice. autospec El. cleanup. rewrite El.
      apply join_all_age_to. cleanup. omega.
      pose proof juice_join compat as j.
      rewrite join_all_joinlist.
      rewrite join_all_joinlist in j.
      rewrite maps_updlock1.
      rewrite maps_remLockSet_updThread.
      rewrite maps_updthread.
      rewrite maps_getlock1. 2:assumption.
      rewrite maps_getthread with (cnti := cnti) in j.
      destruct j as (psi_ & jpsi_ & jphi_).
      exists psi; split. 2:assumption.
      cut (psi = psi_). now intros <-; auto.
      eapply join_canc. eapply join_comm. apply jphi. eapply join_comm. eauto.
    
    + (* mem_cohere' *)
      split.
      * intros rsh sh v loc pp E''.
        destruct (adr_range_dec (b, Int.unsigned ofs) LKSIZE loc) as [r|nr].
        -- exfalso.
           destruct Hrmap' as (_ & _ & inside). spec inside loc. autospec inside.
           rewrite age_to_resource_at in E''.
           destruct inside as (? & ? & _ & E').
           rewrite E' in E''. if_tac in E''; simpl in E''; congruence.
        -- destruct (Phi'rev _ _ _ _ _ nr E'') as (pp' & E & ->).
           cut (contents_at m loc = v /\ pp' = NoneP).
           { intros []; split; subst pp'; auto.
             destruct loc as (b1, ofs1).
             destruct (store_outside' _ _ _ _ _ _ Hstore) as (outside & _ & _).
             spec outside b1 ofs1.
             destruct outside as [(->, r) | same].
             - exfalso. apply nr. split; auto.
             - rewrite <-same.
               subst jm. unfold personal_mem.
               change (m_dry (mkJuicyMem ?m _ _ _ _ _)) with m.
               rewrite <-juicyRestrictContents. auto.
           }
           eapply (cont_coh (all_cohere compat)); eauto.
      
      * (* max_access_cohere' *)
        intros loc.
        admit (* wait for change in access_cohere' from nick and santiago *).
      
      * (* alloc_cohere *)
        pose proof all_coh ((all_cohere compat)) as A.
        unfold alloc_cohere in *.
        destruct (store_outside' _ _ _ _ _ _ Hstore) as (_ & _ & <-).
        subst jm; simpl.
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
      rewrite AMap_find_add.
      intros H ofs0 H0.
      rewrite (Mem.store_access _ _ _ _ _ _ Hstore).
      revert H ofs0 H0.
      intros H ofs0 H0.
      subst jm.
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
        destruct Hrmap' as (_ & _ & inside).
        specialize (inside (b, ofs0)).
        spec C (b, ofs0).
        spec inside. hnf. split; auto.
        destruct inside as (val & sh & E & _).
        rewrite E in C.
        unfold max_access_at in *.
        eapply po_trans. eassumption.
        unfold perm_of_res' in *.
        unfold perm_of_sh in *.
        Ltac share_tac :=
          change (pshare_sh pfullshare) with Share.top in *;
          pose proof Share.nontrivial;
          try tauto.
        repeat if_tac; try constructor; share_tac.
      * eapply loc_writable; eauto.
    
    + (* juicyLocks_in_lockSet *)
      intros loc sh psh P z E''.
      unfold lockGuts in *.
      rewrite lset_age_tp_to.
      rewrite isSome_find_map.
      simpl.
      rewrite AMap_find_add. if_tac [<- | ne]. reflexivity.
      destruct (rmap_unage_YES _ _ _ _ _ _ _ APhi' E'') as (pp, E').
      cut (Phi @ loc = YES sh psh (LK z) pp).
      { intros; eapply (jloc_in_set compat); eauto. }
      rewrite <-E'.
      destruct Hrmap' as (_ & outside & inside).
      apply outside.
      intros r.
      spec inside loc r.
      destruct inside as (val & sh' & _ & E1).
      rewrite E1 in E'.
      if_tac in E'.
      * unfold Int.unsigned in *. congruence.
      * congruence.
    
    + (* lockSet_in_juicyLocks *)
      (* mindless *)
      admit.
  }
  
  subst m_ tp_ m'0 tp'' tp'0 tp'.
  unshelve eapply state_invariant_c with (PHI := age_to n Phi') (mcompat := mcompat').
  - (* level *)
    apply level_age_to. omega.
  
  - (* matchfunspec *)
    apply matchfunspec_age_to.
    eapply matchfunspec_common_join with (Phi := Phi); eauto.
  
  - (* lock sparsity *)
    simpl.
    cleanup.
    unfold lock_sparsity in *.
    cut (forall loc, AMap.find loc (lset tp) <> None ->
                loc = (b, Int.intval ofs) \/ fst loc <> b \/ fst loc = b /\ far (snd loc) (Int.intval ofs)). {
      clear -sparse.
      intros H loc1 loc2.
      do 2 rewrite AMap_find_map_option_map. cleanup.
      do 2 rewrite AMap_find_add.
      if_tac [<- | ne1]; if_tac [<- | ne2]; simpl.
      - auto.
      - intros _ found2.
        spec H loc2. spec H. destruct (AMap.find loc2 _); auto; congruence.
        breakhyps. right. right. split; auto. unfold far in *; auto. zify. omega.
      - intros found1 _.
        spec H loc1. spec H. destruct (AMap.find loc1 _); auto; congruence.
        auto.
      - intros found1 found2.
        spec sparse loc1 loc2.
        spec sparse. destruct (AMap.find loc1 _); auto; congruence.
        spec sparse. destruct (AMap.find loc2 _); auto; congruence.
        auto.
    }
    clear sparse jmstep Htstep.
    intros loc found. right.
    specialize (lock_coh loc). destruct (AMap.find loc _) as [o|] eqn:Eo. clear found. 2:congruence.
    assert (coh : exists (R : pred rmap), (lkat R loc) Phi)
      by (destruct o; breakhyps; eauto). clear lock_coh.
    destruct coh as (R' & AT).
    specialize (AT loc).
    destruct Hrmap.
    admit (* mindless *).
  
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
        admit (* should be fine *).
      * (* LK_at *)
        unfold sync_preds_defs.LK_at in *.
        unfold sync_preds_defs.LKspec_ext in *.
        (* we do NOT have LK_at. we have only "at least" something, but again not a rectangle. *)
        admit.
    + spec lock_coh loc.
      destruct (AMap.find loc _) as [o|] eqn:Eo.
      * destruct o; unfold option_map; destruct lock_coh as (load & coh); split; swap 2 3.
        -- admit. (* load *)
        -- admit. (* load *)
        -- admit. (* lkat *)
        -- admit. (* lkat *)
      * unfold option_map.
        destruct (adr_range_dec (b, Int.unsigned ofs) LKSIZE loc) as [r|nr].
        -- destruct Hrmap' as (_ & _ & inside).
           spec inside loc r. rewrite isLK_age_to.
           if_tac in inside; intros []; intros ? ?; breakhyps.
        -- destruct Hrmap' as (_ & outside & _).
           rewrite age_to_resource_at.
           spec outside loc nr. rewrite <-outside.
           clear -lock_coh.
           unfold isLK, isCT in *.
           destruct (Phi @ loc) as [t0 | t0 p [] p0 | k p]; (* split; *) simpl in *; intro; breakhyps.
           apply lock_coh; eauto.
  
  - (* safety *)
    {
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
          destruct Post with
          (ret := @None val)
            (m' := jm_ lj mcompat')
            (z' := ora) (n' := n) as (c'' & Ec'' & Safe').
          
          + assert (e = MKLOCK).
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
            
          + assert (e = MKLOCK).
            { rewrite <-Ejuicy_sem in *.
              unfold juicy_sem in *.
              simpl in ae.
              congruence. }
            subst e.
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
              admit (* use join to solve this *).
              (* apply pures_age_eq. omega. *)
              
          + (* we must satisfy the post condition *)
            assert (e = MKLOCK).
            { rewrite <-Ejuicy_sem in *.
              unfold juicy_sem in *.
              simpl in ae.
              congruence. }
            subst e.
            revert x Pre Post.
            funspec_destruct "acquire".
            { exfalso. unfold ef_id_sig in *. injection Heq_name as E.
              apply ext_link_inj in E. congruence. }
            funspec_destruct "release".
            { exfalso. unfold ef_id_sig in *. injection Heq_name0 as E.
              apply ext_link_inj in E. congruence. }
            funspec_destruct "makelock"; swap 1 2.
            { exfalso. unfold ef_id_sig, ef_sig in *.
              unfold funsig2signature in *; simpl in *. congruence. }
            intros x (Hargsty, Pre) Post.
            destruct Pre as (phi0 & phi1 & j & Pre).
            
            destruct x as (phix, (ts, ((vx, shx), Rx))); simpl in Pre.
            destruct Pre as [[[Hwritable [(*True*)]] [[B1 B2] AT]] necr].
            unfold canon.SEPx in *.
            unfold fold_right in *.
            simpl in B1.
            rewrite seplog.sepcon_emp in AT.
            assert (args = Vptr b ofs :: nil). {
              revert Hat_external ae; clear.
              unfold SEM.Sem in *.
              rewrite SEM.CLN_msem. simpl.
              congruence.
            }
            assert (vx = Vptr b ofs). {
              rewrite B1. subst args. clear.
              simpl.
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
            subst args vx.
            pose proof data_at_rmap_makelock CS as RL.
            unfold tlock in *.
            simpl in B1.
            unfold liftx in B1. simpl in B1. unfold lift in B1. simpl in B1.
            unfold expr.eval_id in B1. simpl in B1.
            
            match type of AT with context[Tarray _ ?n] => assert (Hpos' : (0 < n)%Z) by omega end.
            specialize (RL shx b ofs (Interp Rx) phi0 _ Hpos' Hwritable AT).
            destruct RL as (phi0' & RL0 & lkat).
            
            match type of lkat with context[LK_at _ ?n] => assert (Hpos'' : (0 < n)%Z) by omega end.
            pose proof rmap_makelock_join _ _ _ _ _ _ _ Hpos'' RL0 j as RL.
            destruct RL as (phi'_ & RLphi & j').
            rewrite m_phi_jm_ in RLphi.
            assert (phi'_ = phi'). {
              eapply rmap_makelock_unique; eauto.
              (* ok, except for one thing: it might be a different R
              chosen by the machine *)
              admit.
            }
            subst phi'_.
            Admitted. (*
            assert (ji : join_sub (getThreadR _ _ cnti) Phi) by join_sub_tac.
            destruct ji as (psi & jpsi). cleanup.
            
            exists (age_to n phi0'), (age_to n phi1).
            rewrite m_phi_jm_ in *.
            split.
            * REWR.
              cleanup.
              rewr (m_phi jm).
              rewrite El; auto.
              apply age_to_join.
              REWR.
              REWR.
        
              unfold rmap_makelock in *.
              auto.
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
                 destruct lock_coh as [_ (sh' & R' & lkat & sat)].
                 destruct sat as [sat | ?]. 2:congruence.
                 pose proof predat2 lkat as ER'.
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
      
    * unshelve erewrite gsoThreadCode; auto.
      unfold semax_invariant.Machine.containsThread in *.
      cut (forall c (cntj : containsThread tp j),
              jsafeN Jspec' ge (S n) ora c (jm_ cntj compat) ->
              jsafeN Jspec' ge n ora c (jm_ lj compat')).
      {
        intros HH.
        destruct (@getThreadC j tp lj) eqn:E.
        - unshelve eapply HH; auto.
        - unshelve eapply HH; auto.
        - intros c' Ec'. eapply HH; auto.
        - constructor.
      }
      intros c0 cntj Safe.
      apply jsafeN_downward in Safe.
      apply jsafeN_age_to with (l := n) in Safe; auto.
      revert Safe.
      apply jsafeN_mem_equiv. 2: now apply Jspec'_juicy_mem_equiv.
      split.
      -- rewrite m_dry_age_to.
         unfold jm_ in *.
         set (@mem_compatible_forget _ _ _ _) as cmpt; clearbody cmpt.
         set (@mem_compatible_forget _ _ _ _) as cmpt'; clearbody cmpt'.
         match goal with
           |- context [thread_mem_compatible ?a ?b] =>
           generalize (thread_mem_compatible a b); intros pr
         end.
         match goal with
           |- context [thread_mem_compatible ?a ?b] =>
           generalize (thread_mem_compatible a b); intros pr'
         end.
         
         eapply mem_equiv_trans.
         ++ unshelve eapply personal_mem_equiv_spec with (m' := m').
            ** REWR in pr'.
               REWR in pr'.
               REWR in pr'.
               eapply mem_cohere_sub with Phi.
               eapply mem_cohere'_store. 2:apply Hstore. cleanup; congruence. auto.
               apply compatible_threadRes_sub. apply compat.
            ** pose proof store_outside' _ _ _ _ _ _ Hstore as STO.
               simpl in STO. apply STO.
            ** pose proof store_outside' _ _ _ _ _ _ Hstore as STO.
               destruct STO as (_ & ACC & _).
               intros loc.
               apply equal_f with (x := loc) in ACC.
               apply equal_f with (x := Max) in ACC.
               rewrite restrPermMap_Max' in ACC.
               apply ACC.
            ** intros loc yes.
               pose proof store_outside' _ _ _ _ _ _ Hstore as STO.
               destruct STO as (CON & _ & _).
               specialize (CON (fst loc) (snd loc)).
               destruct CON as [CON|CON].
               --- exfalso.
                   destruct loc as (b', ofs'); simpl in CON.
                   destruct CON as (<- & int).
                   clear safety Htstep jmstep Hload Hstore compat' lj cmpt' pr'.
                   specialize (lock_coh (b, Int.intval ofs)).
                   cleanup.
                   rewrite His_unlocked in lock_coh.
                   destruct lock_coh as (_ & sh' & R' & lk & sat).
                   apply isVAL_join_sub with (r2 := Phi @ (b, ofs')) in yes.
                   2: now apply resource_at_join_sub; join_sub_tac.
                   specialize (lk (b, ofs')).
                   simpl in lk.
                   if_tac in lk. 2: range_tac.
                   unfold isVAL in *.
                   if_tac in lk.
                   +++ breakhyps.
                       destruct (Phi @ (b, ofs')) as [t0 | t0 p [] p0 | k p]; try tauto.
                       congruence.
                   +++ breakhyps.
                       destruct (Phi @ (b, ofs')) as [t0 | t0 p [] p0 | k p]; try tauto.
                       congruence.
               --- rewrite restrPermMap_contents in CON.
                   apply CON.
         ++ apply mem_equiv_refl'.
            apply m_dry_personal_mem_eq.
            intros loc.
            REWR.
            REWR.
            REWR.                  
            REWR.
      -- REWR.
         rewrite m_phi_jm_.
         rewrite m_phi_jm_.
         REWR.
         REWR.
         REWR.
  - (* thread safety *)
    
    admit.
  
  - (* well_formedness *)
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
         
  - (* uniqueness *)
    apply no_Krun_unique_Krun.
    rewrite no_Krun_age_tp_to.
    apply no_Krun_updLockSet.
    apply no_Krun_stable. congruence.
    eapply unique_Krun_no_Krun. eassumption.
    instantiate (1 := cnti).
    rewrite Hthread.
    congruence.
Admitted.

    (* now much easier with rmap_makelock.
    (* we must define the new Phi *)
    
    Definition rmap_makelock phi phi' sh loc R :=
      (forall x, ~ adr_range loc LKSIZE x -> phi @ x = phi' @ x) /\
      (forall x, adr_range loc LKSIZE x -> exists val, phi @ x = YES sh pfullshare (VAL val) NoneP) /\
      (LKspec_ext R fullshare fullshare loc phi').
    Definition rmap_freelock phi phi' sh loc R :=
      (forall x, ~ adr_range loc LKSIZE x -> phi @ x = phi' @ x) /\
      (LKspec_ext R fullshare fullshare loc phi) /\
      (forall x, adr_range loc LKSIZE x -> exists val, phi' @ x = YES sh pfullshare (VAL val) NoneP).
    
    assert (HPhi' : exists Phi', rmap_makelock Phi Phi' sh (b, Int.intval ofs) R). {
(*      pose (f' :=
              fun loc =>
                if adr_range_dec (b, Int.intval ofs) LKSIZE loc then
                  if eq_dec (Int.intval ofs) (snd loc) then
                    LK  *)
      admit.
    }
    destruct HPhi' as (Phi' & HPhi').
    
    subst m_ tp' tp'0 m'0.
    pose (tp2 := (updLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs) None)).
    fold tp2 in H.
    assert (compat' : mem_compatible_with tp2 m' Phi'). {
      unfold tp2.
      (*
      below, without the modification of the Phi'
      rewrite <-Hpersonal_juice.
      rewrite El.
      constructor.
      - (* joining to global map: the acquired rmap move from
            lockset to threads's maps *)
        pose proof juice_join compat as J.
        apply join_all_age_to. cleanup. omega.
        rewrite join_all_joinlist in J |- *.
        rewrite maps_updlock1.
        rewrite maps_remLockSet_updThread.
        rewrite maps_updthread.
        erewrite (maps_getthread i _ Htid) in J; eauto.
        clear -J Hct0 Hct Hj_forward Hpersonal_juice lock_coh levphi' Hlock.
        rewrite maps_getlock1; swap 1 2. {
          specialize (lock_coh (b, Int.intval ofs)).
          cleanup.
          destruct (AMap.find _ _) as [o|]; auto. exfalso.
          specialize (Hct (Int.intval ofs)).
          assert_specialize Hct. split. omega. unfold LKSIZE; simpl. omega.
          destruct Hct as (val & sh'' & E).
          assert (j : join_sub (getThreadR i tp Htid) Phi) by apply compatible_threadRes_sub, compat.
          destruct j as (?, j).
          apply resource_at_join with (loc := (b, Int.intval ofs)) in j.
          rewrite Hpersonal_juice in j.
          rewrite E in j.
          destruct o.
          - destruct lock_coh as (_ & sh' & R' & lk & _).
            apply predat2 in lk.
            unfold predat in *.
            inv j; breakhyps.
          - destruct lock_coh as (_ & sh' & R' & lk).
            apply predat2 in lk.
            unfold predat in *.
            inv j; breakhyps.
        }
        destruct J as (psi & j1 & j2).
        exists psi; split; auto.
        apply resource_at_join2.
        + rewrite levphi'. rewrite <-Hpersonal_juice. join_level_tac.
        + join_level_tac.
        + intros (b', ofs').
          rewrite Hpersonal_juice in j2.
          apply resource_at_join with (loc := (b', ofs')) in j2.
          specialize (Hj_forward (b', ofs')). simpl in Hj_forward.
          destruct (adr_range_dec (b, Int.intval ofs) 4 (b', ofs')) as [a|a]; swap 1 2.
          * assert_specialize Hj_forward. 2:congruence.
            unfold adr_range in *.
            unfold LKSIZE in *.
            simpl. cut ( b <> b' \/ ~ (Int.intval ofs <= ofs' < Int.intval ofs + 4)%Z). admit. (* wtf machine *)
            tauto.
          * unfold adr_range in *.
            destruct a as [<- a].
            specialize (Hct ofs'). autospec Hct.
            destruct Hct as (val & sh' & E).
            rewrite E in j2.
            destruct (eq_dec ofs' (Int.intval ofs)) as [e|e].
            -- subst ofs'.
               rewrite Hlock.
               inv j2.
               ++ (* NOT THE SAME PHI *)
                 admit.
       *) *)
*)
*)
