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
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mem_lessdef.
Require Import VST.veric.age_to_resource_at.
Require Import VST.veric.seplog.
Require Import VST.floyd.coqlib3.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.concurrency.juicy.semax_conc.
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.juicy.juicy_machine.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.ClightSemanticsForMachines.
Require Import VST.concurrency.juicy.JuicyMachineModule.
Require Import VST.concurrency.juicy.sync_preds_defs.
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.juicy.join_lemmas.
Require Import VST.concurrency.common.lksize.
(*Require Import VST.concurrency.cl_step_lemmas.*)
Require Import VST.concurrency.juicy.resource_decay_lemmas.
Require Import VST.concurrency.juicy.resource_decay_join.
Require Import VST.concurrency.juicy.semax_invariant.

Set Bullet Behavior "Strict Subproofs".

Lemma flat_inj_incr : forall b b', (b <= b')%positive ->
  inject_incr (Mem.flat_inj b) (Mem.flat_inj b').
Proof.
  unfold Mem.flat_inj; repeat intro.
  if_tac in H0; inv H0.
  if_tac; auto.
  eapply Plt_Ple_trans in H1; eauto; contradiction.
Qed.

(** Lemmas common to both parts of the progress/preservation simulation results *)

Lemma lock_coherence_align lset Phi m b ofs :
  lock_coherence lset Phi m ->
  AMap.find (elt:=option rmap) (b, ofs) lset <> None ->
  (align_chunk Mint32 | ofs).
Proof.
  intros lock_coh find.
  specialize (lock_coh (b, ofs)).
  destruct (AMap.find (elt:=option rmap) (b, ofs) lset) as [[o|]|].
  + destruct lock_coh as [L _]; revert L; clear.
    unfold load_at; simpl.
    Transparent Mem.load.
    unfold Mem.load.
    if_tac. destruct H; auto. discriminate.
  + destruct lock_coh as [L _]; revert L; clear.
    unfold load_at; simpl.
    unfold Mem.load.
    if_tac. destruct H; auto. discriminate.
  + tauto.
Qed.

Lemma lset_valid_access ge m m_any (tp : jstate ge) Phi b ofs
  (compat : mem_compatible_with tp m Phi) :
  lock_coherence (lset tp) Phi m_any ->
  AMap.find (elt:=option rmap) (b, ofs) (lset tp) <> None ->
  Mem.valid_access (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget compat))) Mptr b ofs Writable.
Proof.
  intros C F.
  split.
  - intros ofs' r. eapply lset_range_perm; eauto.
    unfold LKSIZE; omega. (* Andrew says: looks fishy *) (* Is this still fishy? -WM *)
  - eapply lock_coherence_align; eauto.
Qed.

Lemma mem_compatible_with_age ge {n} {tp : jstate ge} {m phi} :
  mem_compatible_with tp m phi ->
  mem_compatible_with (age_tp_to n tp) m (age_to n phi).
Proof.
  intros [J AC LW LJ JL]; constructor.
  - rewrite join_all_joinlist in *.
    rewrite maps_age_to.
    apply joinlist_age_to, J.
  - apply mem_cohere_age_to; easy.
  - apply lockSet_Writable_age; easy.
  - apply juicyLocks_in_lockSet_age. easy.
  - apply lockSet_in_juicyLocks_age. easy.
Qed.

Lemma after_alloc_0 : forall b phi H, after_alloc 0 0 b phi H = phi.
Proof.
  intros; apply rmap_ext; unfold after_alloc.
  - rewrite level_make_rmap; auto.
  - intro; rewrite resource_at_make_rmap.
    unfold after_alloc'.
    if_tac; auto.
    destruct l, H0; omega.
  - rewrite ghost_of_make_rmap; auto.
Qed.

Lemma PURE_SomeP_inj1 k A1 A2 pp1 pp2 : PURE k (SomeP A1 pp1) = PURE k (SomeP A2 pp2) -> A1 = A2.
Proof.
  intros.
  congruence.
Qed.

Lemma PURE_SomeP_inj2 k A pp1 pp2 : PURE k (SomeP A pp1) = PURE k (SomeP A pp2) -> pp1 = pp2.
Proof.
  intros.
  apply SomeP_inj2.
  congruence.
Qed.

(* Most general lemma about preservation of matchfunspecs *)
Lemma pures_eq_matchfunspecs e Gamma Phi Phi' :
  (level Phi' <= level Phi)%nat ->
  pures_eq Phi Phi' ->
  matchfunspecs e Gamma Phi ->
  matchfunspecs e Gamma Phi'.
Proof.
  intros lev (PS, SP) MFS b fsig cc A P Q E.
  simpl in E.
  specialize (PS (b, Z0)). specialize (SP (b, Z0)). rewrite E in PS, SP.
  specialize (MFS b fsig cc A).
  simpl (func_at'' _ _ _ _ _ _ _) in MFS.
  destruct SP as (pp, EPhi).
  destruct pp as (A', pp').
  pose proof resource_at_approx Phi (b, Z0) as RA. symmetry in RA. rewrite EPhi in RA.
  rewrite EPhi in PS.
  simpl in PS.
  assert (A' = SpecTT A) by (injection PS; auto). subst A'.
  apply PURE_SomeP_inj2 in PS.
  simpl in RA. injection RA as RA. apply inj_pair2 in RA.

  edestruct MFS with (P := fun i a e' => pp' i
    (fmap (rmaps.dependent_type_functor_rec i A) (compcert_rmaps.R.approx (level Phi))
          (compcert_rmaps.R.approx (level Phi)) a) true e')
                       (Q := fun i a e' => pp' i
    (fmap (rmaps.dependent_type_functor_rec i A) (compcert_rmaps.R.approx (level Phi))
          (compcert_rmaps.R.approx (level Phi)) a) false e')
    as (id & P' & Q' & P'_ne & Q'_ne & Ee & EG & EP' & EQ').
  { rewrite EPhi.
    f_equal. f_equal. rewrite RA. extensionality i a b' e'.
    apply equal_f_dep with (x := i) in PS.
    apply equal_f_dep with (x := (fmap (rmaps.dependent_type_functor_rec i A) (approx (level Phi)) (approx (level Phi)) a)) in PS.
    apply equal_f_dep with (x := b') in PS.
    apply equal_f_dep with (x := e') in PS.
    destruct b'.
    all:simpl.
    all:change compcert_rmaps.R.approx with approx in *.
    all:repeat rewrite (compose_rewr (fmap _ _ _) (fmap _ _ _)).
    all:repeat rewrite fmap_comp.
    all:rewrite (compose_rewr (approx _) (approx _)).
    all:repeat rewrite approx_oo_approx.
    all:rewrite (compose_rewr (fmap _ _ _) (fmap _ _ _)).
    all:rewrite fmap_comp.
    all:rewrite approx_oo_approx.
    all:change compcert_rmaps.R.approx with approx in *.
    all:reflexivity. }

  exists id, P', Q', P'_ne, Q'_ne. split; auto. split; auto.
  split.
  all: eapply cond_approx_eq_trans; [ | eapply cond_approx_eq_weakening; eauto ].
  all: intros ts.
  all: extensionality a e'; simpl.
  all: apply equal_f_dep with (x := ts) in PS.
  all: apply equal_f_dep with (x := a) in PS.

  1: apply equal_f_dep with (x := true) in PS.
  2: apply equal_f_dep with (x := false) in PS.

  all: apply equal_f_dep with (x := e') in PS.
  all: simpl in PS.
  all: change compcert_rmaps.R.approx with approx in *.
  all: rewrite (compose_rewr (fmap _ _ _) (fmap _ _ _)), fmap_comp.
  all: rewrite approx'_oo_approx; auto.
  all: rewrite approx_oo_approx'; auto.
  all: change compcert_rmaps.R.approx with approx in *.
  all: rewrite PS.
  all: rewrite level_age_to; auto.
Qed.

Lemma pures_eq_age_to phi n :
  (level phi >= n)%nat ->
  pures_eq phi (age_to n phi).
Proof.
  split; intros loc; rewrite age_to_resource_at.
  - destruct (phi @ loc); auto; simpl; do 3 f_equal; rewrite level_age_to; auto.
  - destruct (phi @ loc); simpl; eauto.
Qed.

Lemma matchfunspecs_age_to e Gamma n Phi :
  (n <= level Phi)%nat ->
  matchfunspecs e Gamma Phi ->
  matchfunspecs e Gamma (age_to n Phi).
Proof.
  intros lev. apply pures_eq_matchfunspecs. apply level_age_to_le.
  apply pures_eq_age_to; auto.
Qed.

Lemma age_pures_eq phi phi' : age phi phi' -> pures_eq phi phi'.
Proof.
  intros A. rewrite (necR_age_to phi phi'). apply pures_eq_age_to. apply age_level in A. omega.
  constructor; auto.
Qed.

Lemma matchfunspecs_hered e Gamma :
  hereditary age (matchfunspecs e Gamma).
Proof.
  intros phi phi' A. apply pures_eq_matchfunspecs.
  apply age_level in A. omega.
  apply age_pures_eq, A.
Qed.

Lemma resource_decay_pures_eq b phi phi' :
  resource_decay b phi phi' ->
  pures_eq phi phi'.
Proof.
  intros rd; split; intros loc.
  - destruct (phi @ loc) as [ | | k p] eqn:E; auto.
    apply (resource_decay_PURE rd loc k p E).
  - destruct (phi' @ loc) as [ | | k p] eqn:E; auto.
    destruct (resource_decay_PURE_inv rd loc k p E) as (p' & -> & _).
    eauto.
Qed.

Lemma resource_decay_matchfunspecs e Gamma b Phi Phi' :
  (level Phi' <= level Phi)%nat ->
  resource_decay b Phi Phi' ->
  matchfunspecs e Gamma Phi ->
  matchfunspecs e Gamma Phi'.
Proof.
  intros l rd; apply pures_eq_matchfunspecs; auto.
  eapply resource_decay_pures_eq; eauto.
Qed.

Lemma funassert_pures_eq G rho phi1 phi2 :
  (level phi1 >= level phi2)%nat ->
  pures_eq phi1 phi2 ->
  app_pred (funassert G rho) phi1 ->
  app_pred (funassert G rho) phi2.
Proof.
  intros lev (PS, SP) (FA1, FA2); split.
  - intros id fs phi2' necr Gid.
    specialize (FA1 id fs phi1 (necR_refl phi1) Gid).
    destruct FA1 as (b & ? & FAT). exists b; split; auto.
    apply pred_nec_hereditary with phi2; auto.
    clear -lev PS FAT. destruct fs; simpl in *.
    specialize (PS (b, Z0)). rewrite FAT in PS.
    exact_eq PS. f_equal. f_equal.
    simpl. f_equal. extensionality i a b' a1.
    rewrite (compose_rewr (fmap _ _ _) (fmap _ _ _)), fmap_comp.
    rewrite !(compose_rewr (approx _) (approx _)).
    rewrite approx_oo_approx'; auto.
    rewrite approx'_oo_approx; auto.
  - intros b fs phi2' necr. destruct fs eqn:Efs. intros [pp pat].
    specialize (FA2 b fs phi1 (necR_refl phi1)). subst fs.
    spec FA2; [ | auto]. simpl. clear -pat necr SP.
    simpl in pat. specialize (SP (b, Z0)).
    destruct (necR_PURE' _ _ _ _ _ necr pat) as (pp', E).
    rewrite E in SP. destruct SP as (pp'', SP). exists pp''.
    rewrite <-resource_at_approx, SP. reflexivity.
Qed.

Lemma env_coherence_hered Z Jspec ge G :
  hereditary age (@env_coherence Z Jspec ge G).
Proof.
  intros phi phi' A C.
  sync C; eauto. eapply matchfunspecs_hered; eauto.
  sync C; eauto.
  sync C; eauto.
  sync C; eauto.
  sync C; eauto.
  sync C; eauto.
  revert C. apply pred_hered, A.
Qed.

Lemma env_coherence_age_to Z Jspec ge G phi n :
  @env_coherence Z Jspec ge G phi ->
  @env_coherence Z Jspec ge G (age_to n phi).
Proof.
  apply age_to_ind, env_coherence_hered.
Qed.

Lemma env_coherence_pures_eq Z Jspec ge G phi phi' :
  (level phi >= level phi')%nat ->
  pures_eq phi phi' ->
  @env_coherence Z Jspec ge G phi ->
  @env_coherence Z Jspec ge G phi'.
Proof.
  intros L E C.
  pose proof pures_eq_matchfunspecs.
  sync C; eauto.
  sync C; eauto.
  sync C; eauto.
  sync C; eauto.
  sync C; eauto.
  sync C; eauto.
  apply funassert_pures_eq with phi; auto.
Qed.

Lemma env_coherence_resource_decay Z Jspec ge G b phi phi' :
  (level phi >= level phi')%nat ->
  resource_decay b phi phi' ->
  @env_coherence Z Jspec ge G phi ->
  @env_coherence Z Jspec ge G phi'.
Proof.
  intros l r. apply env_coherence_pures_eq; auto.
  eapply resource_decay_pures_eq; eauto.
Qed.

Lemma restrPermMap_mem_contents p' m (Hlt: permMapLt p' (getMaxPerm m)):
  Mem.mem_contents (restrPermMap Hlt) = Mem.mem_contents m.
Proof.
  reflexivity.
Qed.

Lemma islock_valid_access ge (tp : jstate ge) m b ofs p
      (compat : mem_compatible tp m) :
  (align_chunk Mptr | ofs) ->
  lockRes tp (b, ofs) <> None ->
  p <> Freeable ->
  Mem.valid_access
    (restrPermMap
       (mem_compatible_locks_ltwritable compat))
    Mptr b ofs p.
Proof.
  intros div islock NE.
  eapply Mem.valid_access_implies with (p1 := Writable).
  2:destruct p; constructor || tauto.
  pose proof lset_range_perm.
  do 7 autospec H.
  split; auto.
  intros loc range.
  apply H;
  unfold LKSIZE in *;
  omega.
Qed.

Lemma LockRes_age_content1 ge (js : jstate ge) n a :
  lockRes (age_tp_to n js) a = option_map (option_map (age_to n)) (lockRes js a).
Proof.
  cleanup.
  rewrite lset_age_tp_to, AMap_find_map_option_map.
  reflexivity.
Qed.

Lemma join_sub_to_joining {A} {J : Join A}
      {_ : Perm_alg A} {_ : Sep_alg A} {_ : Canc_alg A} {_ : Disj_alg A}
  (a b e : A) :
    join_sub e a ->
    join_sub e b ->
    joins a b ->
    identity e.
Proof.
  intros la lb ab.
  eapply join_sub_joins_identity with b; auto.
  apply (@join_sub_joins_trans _ _ _ _ _ a); auto.
Qed.

Lemma join_sub_join {A} {J : Join A}
      {PA : Perm_alg A} {SA : Sep_alg A} {_ : Canc_alg A} {DA : Disj_alg A} {CA : Cross_alg A}
      (a b c x : A) :
  join a b c ->
  join_sub a x ->
  join_sub b x ->
  join_sub c x.
Proof.
  intros j (d, ja) (e, jb).
  destruct (@cross_split _ _ _ _ _ _ _ _ ja jb)
    as ((((ab, ae), bd), de) & ha & hd & hb & he).
  exists de.
  assert (Iab : identity ab)
    by (apply join_sub_to_joining with a b; eexists; eauto).
  pose proof join_unit1_e ae a Iab ha. subst ae. clear ha.
  pose proof join_unit1_e bd b Iab hb. subst bd. clear hb.
  apply join_comm in ja.
  apply join_comm in hd.
  destruct (join_assoc hd ja) as (c' & abc' & dec'x).
  apply join_comm in abc'.
  assert (c = c'). eapply join_eq. apply j. apply abc'. subst c'.
  apply join_comm; auto.
Qed.

Lemma Ejuicy_sem : forall ge, (@juicy_sem (Clight_newSem ge)) = juicy_core_sem (cl_core_sem ge).
Proof.
  unfold juicy_sem; simpl.
  reflexivity.
Qed.

Lemma level_jm_ ge m tp Phi (compat : mem_compatible_with tp m Phi)
      i (cnti : containsThread tp i) :
  level (jm_(ge := ge) cnti compat) = level Phi.
Proof.
  rewrite level_juice_level_phi.
  apply join_sub_level.
  unfold jm_ in *.
  unfold personal_mem in *.
  simpl.
  apply compatible_threadRes_sub, compat.
Qed.

Definition pures_same phi1 phi2 := forall loc k pp, phi1 @ loc = PURE k pp <-> phi2 @ loc = PURE k pp.

Lemma pures_same_sym phi1 phi2 : pures_same phi1 phi2 -> pures_same phi2 phi1.
Proof.
  unfold pures_same in *.
  intros H loc k pp; rewrite (H loc k pp); intuition.
Qed.

Lemma joins_pures_same phi1 phi2 : joins phi1 phi2 -> pures_same phi1 phi2.
Proof.
  intros (phi3, J) loc k pp; apply resource_at_join with (loc := loc) in J.
  split; intros E; rewrite E in J; inv J; auto.
Qed.

Lemma join_sub_pures_same phi1 phi2 : join_sub phi1 phi2 -> pures_same phi1 phi2.
Proof.
  intros (phi3, J) loc k pp; apply resource_at_join with (loc := loc) in J.
  split; intros E; rewrite E in J; inv J; auto.
Qed.

Lemma pures_same_eq_l phi1 phi1' phi2 :
  pures_same phi1 phi1' ->
  pures_eq phi1 phi2 ->
  pures_eq phi1' phi2.
Proof.
  intros E [M N]; split; intros loc; autospec M; autospec N; autospec E.
  - destruct (phi1 @ loc), (phi2 @ loc), (phi1' @ loc); auto.
    all: try solve [pose proof (proj2 (E _ _) eq_refl); congruence].
  - destruct (phi1 @ loc), (phi2 @ loc), (phi1' @ loc); auto.
    all: breakhyps.
    all: try solve [pose proof (proj1 (E _ _) eq_refl); congruence].
    injection H as <- <-.
    exists p1. f_equal.
    try solve [pose proof (proj2 (E _ _) eq_refl); congruence].
Qed.

Lemma pures_same_eq_r phi1 phi2 phi2' :
  level phi2 = level phi2' ->
  pures_same phi2 phi2' ->
  pures_eq phi1 phi2 ->
  pures_eq phi1 phi2'.
Proof.
  intros L E [M N]; split; intros loc; autospec M; autospec N; autospec E.
  - destruct (phi1 @ loc), (phi2 @ loc), (phi2' @ loc); auto; try congruence.
    all: try solve [pose proof (proj1 (E _ _) eq_refl); congruence].
  - destruct (phi1 @ loc), (phi2 @ loc), (phi2' @ loc); auto.
    all: breakhyps.
    all: try solve [pose proof (proj2 (E _ _) eq_refl); congruence].
    injection H as <- <-.
    exists p. f_equal.
    try solve [pose proof (proj2 (E _ _) eq_refl); congruence].
Qed.

Lemma pures_same_pures_eq phi1 phi2 :
  level phi1 = level phi2 ->
  pures_same phi1 phi2 ->
  pures_eq phi1 phi2.
Proof.
  intros L E.
  apply pures_same_eq_r with phi1; auto.
  apply pures_eq_refl.
Qed.

Lemma pures_same_jm_ ge m tp Phi (compat : mem_compatible_with tp m Phi)
      i (cnti : containsThread tp i) :
  pures_same (m_phi (jm_(ge := ge) cnti compat)) Phi.
Proof.
  apply join_sub_pures_same, compatible_threadRes_sub, compat.
Qed.

Lemma level_m_phi jm : level (m_phi jm) = level jm.
Proof.
  symmetry; apply level_juice_level_phi.
Qed.

Lemma jsafeN_downward {Z} {Jspec : juicy_ext_spec Z} {ge n z c jm} :
  jsafeN Jspec ge (S n) z c jm ->
  jsafeN Jspec ge n z c jm.
Proof.
  apply jsafe_downward1.
Qed.

Lemma jsafe_phi_downward {Z} {Jspec : juicy_ext_spec Z} {ge n z c phi} :
  jsafe_phi Jspec ge (S n) z c phi ->
  jsafe_phi Jspec ge n z c phi.
Proof.
  intros S jm <-.
  apply jsafe_downward1.
  apply S, eq_refl.
Qed.

Lemma jsafe_phi_bupd_downward {Z} {Jspec : juicy_ext_spec Z} {ge n z c phi} :
  jsafe_phi_bupd Jspec ge (S n) z c phi ->
  jsafe_phi_bupd Jspec ge n z c phi.
Proof.
  intros S jm <- ? HC J.
  specialize (S _ eq_refl _ HC J) as (? & ? & ? & ?%jsafe_downward1); eauto.
Qed.

Lemma jsafe_phi_age Z Jspec ge ora q n phi phiaged :
  ext_spec_stable age (JE_spec _ Jspec) ->
  age phi phiaged ->
  le n (level phiaged) ->
  @jsafe_phi Z Jspec ge n ora q phi ->
  @jsafe_phi Z Jspec ge n ora q phiaged.
Proof.
  intros stable A l S jm' E.
  destruct (oracle_unage jm' phi) as (jm & Aj & <-). congruence.
  eapply jsafeN_age; eauto.
  exact_eq l; f_equal.
  rewrite level_juice_level_phi.
  congruence.
Qed.

Lemma jsafe_phi_age_to Z Jspec ge ora q n l phi :
  ext_spec_stable age (JE_spec _ Jspec) ->
  le n l ->
  @jsafe_phi Z Jspec ge n ora q phi ->
  @jsafe_phi Z Jspec ge n ora q (age_to l phi).
Proof.
  intros Stable nl.
  apply age_to_ind_refined.
  intros x y H L.
  apply jsafe_phi_age; auto.
  omega.
Qed.

Lemma jsafe_phi_bupd_age Z Jspec ge ora q n phi phiaged :
  ext_spec_stable age (JE_spec _ Jspec) ->
  age phi phiaged ->
  le n (level phiaged) ->
  @jsafe_phi_bupd Z Jspec ge n ora q phi ->
  @jsafe_phi_bupd Z Jspec ge n ora q phiaged.
Proof.
  intros stable A l S jm' E.
  destruct (oracle_unage jm' phi) as (jm & Aj & <-). congruence.
  intros ? HC J.
  rewrite (age1_ghost_of _ _ (age_jm_phi Aj)) in J.
  destruct (own.ghost_joins_approx _ _ _ J) as (J' & Hc').
  erewrite <- age_level in J' by (eapply age_jm_phi; eauto).
  rewrite ghost_of_approx in J'.
  specialize (S _ eq_refl (own.make_join (ghost_of (m_phi jm)) C0)) as (jm1 & ? & Hupd & ?); auto.
  { eapply make_join_ext; eauto. }
  destruct (jm_update_age _ _ _ Hupd Aj) as (jm1' & Hupd' & Aj').
  exists jm1'; split.
  - rewrite (age1_ghost_of _ _ (age_jm_phi Aj')), <- level_juice_level_phi.
    destruct Hupd' as (_ & -> & _).
    apply Hc'.
    erewrite <- age_level by (eapply age_jm_phi; eauto); auto.
  - split; auto; eapply jsafeN_age; eauto.
    destruct Hupd' as (_ & -> & _).
    exact_eq l; f_equal.
    rewrite level_juice_level_phi.
    congruence.
Qed.

Lemma jsafe_phi_bupd_age_to Z Jspec ge ora q n l phi :
  ext_spec_stable age (JE_spec _ Jspec) ->
  le n l ->
  @jsafe_phi_bupd Z Jspec ge n ora q phi ->
  @jsafe_phi_bupd Z Jspec ge n ora q (age_to l phi).
Proof.
  intros Stable nl.
  apply age_to_ind_refined.
  intros x y H L.
  apply jsafe_phi_bupd_age; auto.
  omega.
Qed.

Lemma m_phi_jm_ ge m (tp : jstate ge) phi i cnti compat :
  m_phi (@jm_ ge tp m phi i cnti compat) = @getThreadR _ _ _ i tp cnti.
Proof.
  reflexivity.
Qed.

Definition isVAL (r : resource) :=
  match r with
  | YES _ _ (VAL _) _ => Logic.True
  | _ => False
  end.

Lemma isVAL_join_sub r1 r2 : join_sub r1 r2 -> isVAL r1 -> isVAL r2.
Proof.
  intros (r & j); inv j; simpl; tauto.
Qed.

Lemma restrPermMap_Max' m p Hlt loc :
  access_at (@restrPermMap p m Hlt) loc Max = access_at m loc Max.
Proof.
  pose proof restrPermMap_max Hlt as R.
  apply equal_f with (x := loc) in R.
  apply R.
Qed.

Lemma restrPermMap_Cur' m p Hlt loc :
  access_at (@restrPermMap p m Hlt) loc Cur = p !! (fst loc) (snd loc).
Proof.
  apply (restrPermMap_Cur Hlt (fst loc) (snd loc)).
Qed.

Lemma juicyRestrict_ext  m phi phi' pr pr' :
  (forall loc, perm_of_res (phi @ loc) = perm_of_res (phi' @ loc)) ->
  @juicyRestrict phi m (acc_coh pr) = @juicyRestrict phi' m (acc_coh pr').
Proof.
  intros E.
  unfold juicyRestrict, juice2Perm.
  apply restrPermMap_ext; intros b.
  extensionality ofs.
  unfold mapmap in *.
  unfold "!!".
  simpl.
  do 2 rewrite PTree.gmap.
  unfold option_map in *.
  destruct (PTree.map1 _) as [|].
  - destruct (PTree.Leaf ! _) as [|]; auto.
  - destruct ((PTree.Node _ _ _) ! _) as [|]; auto.
Qed.

Lemma m_dry_personal_mem_eq m phi phi' pr pr' :
  (forall loc, perm_of_res (phi @ loc) = perm_of_res (phi' @ loc)) ->
  m_dry (@personal_mem m phi pr) =
  m_dry (@personal_mem m phi' pr').
Proof.
  intros E; simpl.
  apply juicyRestrict_ext; auto.
Qed.

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
  specialize (A x k p).
  specialize (B x k p).
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
    specialize (E l).
    destruct (x @ l), (y @ l); split; intro; simpl in *; breakhyps.
    + specialize (E k0 p). destruct E as [_ E]. autospec E. discriminate.
    + specialize (E k1 p0). destruct E as [_ E]. autospec E. discriminate.
    + specialize (E k0 p). destruct E as [E _]. autospec E. discriminate.
    + specialize (E k0 p). destruct E as [E _]. autospec E. discriminate.
    + specialize (E k0 p). destruct E as [E _]. autospec E. injection E as -> ->. rewr (PURE k pp). congruence.
    + specialize (E k0 p). destruct E as [E _]. autospec E. injection E as -> ->. rewr (PURE k pp). congruence.
  - (* reflexivity case *)
    intuition eauto.
  - (* transitivity case *)
    intros x' Lx Ex.
    specialize (IHn1 x' Lx Ex). destruct IHn1 as (y' & Ly & Ey & ny).
    specialize (IHn2 y' Ly Ey). destruct IHn2 as (z' & Lz & Ez & nz).
    exists z'. split; auto. split; auto. apply necR_trans with y'; auto.
Qed.

Lemma pures_same_matchfunspecs e Gamma phi1 phi2 :
  level phi1 = level phi2 ->
  pures_same phi1 phi2 ->
  matchfunspecs e Gamma phi1 ->
  matchfunspecs e Gamma phi2.
Proof.
  intros EL E. apply pures_eq_matchfunspecs. rewrite EL; auto.
  eapply pures_same_eq_r; eauto. apply pures_eq_refl.
Qed.

Lemma matchfunspecs_common_join e Gamma phi phi' psi Phi Phi' :
  join phi psi Phi ->
  join phi' psi Phi' ->
  matchfunspecs e Gamma Phi ->
  matchfunspecs e Gamma Phi'.
Proof.
  intros j j'.
  apply pures_same_matchfunspecs. now join_level_tac.
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

Lemma approx'_approx n n' x : (n' <= n)%nat -> approx n (approx n' x) = approx n' x.
Proof.
  intros l.
  pose proof approx'_oo_approx _ _ l as E.
  apply equal_f with (x0 := x) in E.
  apply E.
Qed.

Lemma approx_approx' n n' x : (n' <= n)%nat -> approx n' (approx n x) = approx n' x.
Proof.
  intros l.
  pose proof approx_oo_approx' _ _ l as E.
  apply equal_f with (x0 := x) in E.
  apply E.
Qed.

Lemma shape_of_args F V args b ofs ge :
  Val.has_type_list args (AST.Tint :: nil) ->
  Vptr b ofs = expr.eval_id _lock (make_ext_args (filter_genv (symb2genv (@genv_symb_injective F V ge))) (_lock :: nil) args) ->
  args = Vptr b ofs :: nil.
Proof.
  intros Hargsty.
  assert (L: length args = 1%nat) by (destruct args as [|? [|]]; simpl in *; tauto).
  unfold expr.eval_id.
  unfold val_lemmas.force_val.
  intros Preb.
  match goal with H : context [Map.get ?a ?b] |- _ => destruct (Map.get a b) eqn:E end.
  subst v. 2: discriminate.
  pose  (gx := (filter_genv (symb2genv (genv_symb_injective ge)))). fold gx in E.
  destruct args as [ | arg [ | ar args ]].
  + now inversion E.
  + simpl in E. inversion E. reflexivity.
  + inversion E. f_equal.
    inversion L.
Qed.

Lemma join_all_res : forall ge i (tp : jstate ge) (cnti : containsThread tp i) c Phi,
  join_all (updThread cnti (Krun c) (getThreadR cnti)) Phi <->
  join_all tp Phi.
Proof.
  intros.
  rewrite !join_all_joinlist, maps_updthread, <- maps_updthread; simpl.
  rewrite updThread_same; reflexivity.
Qed.

Definition thread_safety {Z} (Jspec : juicy_ext_spec Z) m ge (tp : jstate ge) PHI (mcompat : mem_compatible_with tp m PHI) n
  i (cnti : containsThread tp i) := forall (ora : Z),
    match getThreadC cnti with
    | Krun c => semax.jsafeN Jspec ge n ora c (jm_ cnti mcompat)
    | Kblocked c =>
      (* The dry memory will change, so when we prove safety after an
      external we must only inspect the rmap m_phi part of the juicy
      memory.  This means more proof for each of the synchronisation
      primitives. *)
      jsafe_phi Jspec ge n ora c (getThreadR cnti)
    | Kresume c v =>
      forall c',
        (* [v] is not used here. The problem is probably coming from
           the definition of JuicyMachine.resume_thread'. *)
        cl_after_external None c = Some c' ->
        (* same quantification as in Kblocked *)
        jsafe_phi_bupd Jspec ge n ora c' (getThreadR cnti)
    | Kinit v1 v2 =>
      val_inject (Mem.flat_inj (Mem.nextblock m)) v2 v2 /\
      exists q_new,
      cl_initial_core ge v1 (v2 :: nil) q_new /\
      jsafe_phi Jspec ge n ora q_new (getThreadR cnti)
    end.

Lemma mem_cohere'_res : forall m phi phi', mem_cohere' m phi ->
  resource_at phi' = resource_at phi -> mem_cohere' m phi'.
Proof.
  inversion 1; constructor; repeat intro; rewrite H0 in *; eauto.
Qed.

Lemma state_inv_upd1 : forall {Z} (Jspec : juicy_ext_spec Z) Gamma (n : nat)
  (m : mem) (ge : genv) (tr : event_trace) (sch : schedule) (tp : ThreadPool.t) (PHI : rmap)
      (lev : level PHI = n)
      (envcoh : env_coherence Jspec ge Gamma PHI)
      (mcompat : mem_compatible_with tp m PHI)
      (extcompat : joins (ghost_of PHI) (Some (ext_ref tt, NoneP) :: nil))
      (lock_sparse : lock_sparsity (lset tp))
      (lock_coh : lock_coherence' tp PHI m mcompat)
      (safety : exists i (cnti : containsThread tp i), let phi := getThreadR cnti in
       (exists k, getThreadC cnti = Krun k /\
       forall c, join_sub (Some (ext_ref tt, NoneP) :: nil) c ->
          joins (ghost_of phi) (ghost_fmap (approx (level phi)) (approx (level phi)) c) ->
        exists b, joins b (ghost_fmap (approx (level phi)) (approx (level phi)) c) /\
        exists phi' (Hr : resource_at phi' = resource_at phi), level phi' = level phi /\ ghost_of phi' = b /\
        forall ora, jsafeN Jspec ge n ora k
          (personal_mem (mem_cohere'_res _ _ _ (compatible_threadRes_cohere cnti (mem_compatible_forget mcompat)) Hr))) /\
       forall j (cntj : containsThread tp j), j <> i -> thread_safety Jspec m ge tp PHI mcompat n j cntj)
      (wellformed : threads_wellformed tp)
      (uniqkrun :  unique_Krun tp sch),
  state_bupd (state_invariant Jspec Gamma n) (m, (tr, sch, tp)).
Proof.
  intros; apply state_inv_upd with (mcompat0 := mcompat); auto; intros.
  destruct safety as (i & cnti & [(k & Hk & Hsafe) Hrest]).
  assert (join_all tp PHI) as Hj by (apply mcompat).
  rewrite join_all_joinlist in Hj.
  eapply joinlist_permutation in Hj; [|apply maps_getthread with (cnti0 := cnti)].
  destruct Hj as (? & ? & Hphi).
  pose proof (ghost_of_join _ _ _ Hphi) as Hghost.
  destruct H0; destruct (join_assoc Hghost H0) as (c & HC & Hc).
  eapply ghost_fmap_join in Hc; rewrite ghost_of_approx in Hc.
  destruct (Hsafe c) as (? & [? Hj'] & phi' & Hr' & Hl' & ? & Hsafe'); eauto; subst.
  { apply join_comm in HC.
    eapply join_sub_trans; [|eexists; apply HC].
    destruct H; apply ghost_fmap_join with (f := approx (level PHI))(g := approx (level PHI)) in H.
    eexists; eauto. }
  apply ghost_fmap_join with (f := approx (level (getThreadR cnti)))
    (g := approx (level (getThreadR cnti))) in HC.
  destruct (join_assoc (join_comm HC) (join_comm Hj')) as (g' & Hg' & HC').
  destruct (join_level _ _ _ Hphi) as [Hl].
  destruct (make_rmap (resource_at PHI) g' (level PHI)) as (PHI' & HL' & HR' & ?); subst.
  { extensionality; apply resource_at_approx. }
  { eapply ghost_same_level_gen.
    rewrite <- (ghost_of_approx phi') in Hg'.
    exact_eq Hg'; f_equal; f_equal; f_equal; rewrite ?Hl'; auto. }
  assert (tp_update tp PHI (updThreadR cnti phi') PHI') as Hupd.
  { repeat split; auto.
    - rewrite join_all_joinlist.
      eapply joinlist_permutation; [symmetry; apply maps_updthreadR|].
      eexists; split; eauto.
      apply resource_at_join2.
      + rewrite Hl', HL'; auto.
      + rewrite HL'; auto.
      + rewrite Hr', HR'; intro; apply resource_at_join; auto.
      + apply join_comm; exact_eq Hg'; f_equal.
        rewrite <- ghost_of_approx at 2; f_equal; rewrite Hl; auto.
    - assert (forall t, containsThread (updThreadR cnti phi') t <-> containsThread tp t) as Hiff.
      { split; [apply cntUpdateR' | apply cntUpdateR]. }
      exists Hiff; split; auto; intros.
      split; [unshelve setoid_rewrite gThreadRC; auto|].
      destruct (eq_dec i t0).
      + subst.
        rewrite gssThreadRR.
        replace cnt with cnti by apply proof_irr; auto.
      + erewrite gsoThreadRR by eauto; split; reflexivity. }
  exists _, _, Hupd; split.
  - replace (level (getThreadR cnti)) with (level PHI) in HC' by omega.
    rewrite ghost_fmap_fmap, approx_oo_approx in HC'; eauto.
  - intros j cntj ora.
    unshelve erewrite gThreadRC; auto.
    destruct (eq_dec j i).
    + subst.
      replace cntj with cnti by apply proof_irr.
      rewrite Hk.
      specialize (Hsafe' ora); exact_eq Hsafe'.
      unfold jm_; f_equal.
      apply personal_mem_ext; simpl.
      rewrite eqtype_refl; auto.
    + assert (getThreadR cntj = @getThreadR _ _ _ _ tp cntj) as Heq.
      { simpl.
        rewrite eqtype_neq; auto. }
      rewrite Heq.
      specialize (Hrest _ cntj n ora).
      destruct (@getThreadC _ _ _ j tp cntj); auto.
      exact_eq Hrest; f_equal.
      apply juicy_mem_ext; [|rewrite !m_phi_jm_; auto].
      unfold jm_, personal_mem, m_dry, juicyRestrict.
      apply restrPermMap_irr'.
      rewrite Heq; auto.
Qed.

(*
assert (cnti = Htid) by apply proof_irr; subst Htid).
assert (ctn = cnti) by apply proof_irr; subst cnt).
destruct (cntAdd' _ _ _ cnti) as [(cnti', ne) | Ei].
*)

Ltac join_sub_tac :=
  try
    match goal with
      c : mem_compatible_with ?tp ?m ?Phi |- _ =>
      match goal with
      | cnt1 : containsThread tp _,
        cnt2 : containsThread tp _,
        cnt3 : containsThread tp _,
        cnt4 : containsThread tp _ |- _ =>
        assert (join_sub (getThreadR cnt1) Phi) by (apply compatible_threadRes_sub, c);
        assert (join_sub (getThreadR cnt2) Phi) by (apply compatible_threadRes_sub, c);
        assert (join_sub (getThreadR cnt3) Phi) by (apply compatible_threadRes_sub, c);
        assert (join_sub (getThreadR cnt4) Phi) by (apply compatible_threadRes_sub, c)
      | cnt1 : containsThread tp _,
        cnt2 : containsThread tp _,
        cnt3 : containsThread tp _ |- _ =>
        assert (join_sub (getThreadR cnt1) Phi) by (apply compatible_threadRes_sub, c);
        assert (join_sub (getThreadR cnt2) Phi) by (apply compatible_threadRes_sub, c);
        assert (join_sub (getThreadR cnt3) Phi) by (apply compatible_threadRes_sub, c)
      | cnt1 : containsThread tp _,
        cnt2 : containsThread tp _ |- _ =>
        assert (join_sub (getThreadR cnt1) Phi) by (apply compatible_threadRes_sub, c);
        assert (join_sub (getThreadR cnt2) Phi) by (apply compatible_threadRes_sub, c)
      | cnt1 : containsThread tp _ |- _ =>
        assert (join_sub (getThreadR cnt1) Phi) by (apply compatible_threadRes_sub, c)
      end
    end;
  try
    match goal with
    | F : AMap.find (elt:=option rmap) ?loc (lset ?tp) = Some (Some ?phi),
          c : mem_compatible_with ?tp _ ?Phi |- _
      => assert (join_sub phi Phi) by eapply (@compatible_lockRes_sub tp loc phi F), c
    end;
  eauto using join_sub_trans.

Tactic Notation "REWR" :=
  first
    [ unshelve erewrite <-gtc_age |
      unshelve erewrite gLockSetCode |
      unshelve erewrite gRemLockSetCode |
      rewrite gssThreadCode |
      rewrite gssThreadCC |
      unshelve erewrite gsoThreadCode |
      unshelve erewrite <-gsoThreadCC |
      unshelve erewrite gsoAddCode |
      rewrite gssAddCode |
      unshelve erewrite <-getThreadR_age |
      unshelve erewrite gssThreadRes |
      unshelve erewrite gsoThreadRes |
      unshelve erewrite gThreadCR |
      unshelve erewrite gssAddRes |
      unshelve erewrite gsoAddRes |
      unshelve erewrite gLockSetRes |
      unshelve erewrite perm_of_age |
      unshelve erewrite gRemLockSetRes |
      unshelve erewrite m_phi_age_to
    ]; auto.

Tactic Notation "REWR" "in" hyp(H) :=
  first
    [ unshelve erewrite <-gtc_age in H |
      unshelve erewrite gLockSetCode in H |
      unshelve erewrite gRemLockSetCode in H |
      rewrite gssThreadCode in H |
      rewrite gssThreadCC in H |
      unshelve erewrite gsoThreadCode in H |
      unshelve erewrite <-gsoThreadCC in H |
      unshelve erewrite gsoAddCode in H |
      rewrite gssAddCode in H |
      unshelve erewrite <-getThreadR_age in H |
      unshelve erewrite gssThreadRes in H |
      unshelve erewrite gsoThreadRes in H |
      unshelve erewrite gThreadCR in H |
      unshelve erewrite gssAddRes in H |
      unshelve erewrite gsoAddRes in H |
      unshelve erewrite gLockSetRes in H |
      unshelve erewrite perm_of_age in H |
      unshelve erewrite gRemLockSetRes in H |
      unshelve erewrite m_phi_age_to in H
    ]; auto.

Tactic Notation "REWR" "in" "*" :=
  first
    [ unshelve erewrite <-gtc_age in * |
      unshelve erewrite gLockSetCode in * |
      unshelve erewrite gRemLockSetCode in * |
      rewrite gssThreadCode in * |
      rewrite gssThreadCC in * |
      unshelve erewrite gsoThreadCode in * |
      unshelve erewrite <-gsoThreadCC in * |
      unshelve erewrite gsoAddCode in * |
      rewrite gssAddCode in * |
      unshelve erewrite <-getThreadR_age in * |
      unshelve erewrite gssThreadRes in * |
      unshelve erewrite gsoThreadRes in * |
      unshelve erewrite gThreadCR in * |
      unshelve erewrite gssAddRes in * |
      unshelve erewrite gsoAddRes in * |
      unshelve erewrite gLockSetRes in * |
      unshelve erewrite perm_of_age in * |
      unshelve erewrite gRemLockSetRes in * |
      unshelve erewrite m_phi_age_to in *
    ]; auto.

Lemma FF_orp:
 forall A (ND: NatDed A) (P: A), seplog.orp seplog.FF P = P.
Proof.
intros.
unfold seplog.FF.
apply seplog.pred_ext.
apply seplog.orp_left; auto.
apply prop_left; intro; contradiction.
apply seplog.orp_right2; auto.
Qed.

Lemma TT_andp:
 forall A (ND: NatDed A) (P: A), seplog.andp seplog.TT P = P.
Proof.
intros.
unfold seplog.TT.
apply seplog.pred_ext.
apply seplog.andp_left2; auto.
apply seplog.andp_right; auto.
apply prop_right; auto.
Qed.
