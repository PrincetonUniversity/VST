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
Require Import veric.semax_ext_oracle.
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

Local Arguments getThreadR : clear implicits.
Local Arguments getThreadC : clear implicits.
Local Arguments personal_mem : clear implicits.
Local Arguments updThread : clear implicits.
Local Arguments updThreadR : clear implicits.
Local Arguments updThreadC : clear implicits.
Local Arguments juicyRestrict : clear implicits.

Set Bullet Behavior "Strict Subproofs".

Tactic Notation "REWR" :=
  first
    [ unshelve erewrite <-getThreadR_age |
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
    [ unshelve erewrite <-getThreadR_age in H |
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
    [ unshelve erewrite <-getThreadR_age in * |
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

Lemma rmap_bound_join {b phi1 phi2 phi3} :
  join phi1 phi2 phi3 ->
  rmap_bound b phi3 ->
  rmap_bound b phi2.
Proof.
  intros j B l p; specialize (B l p).
  apply resource_at_join with (loc := l) in j.
  rewrite B in j.
  inv j; eauto.
  erewrite join_to_bot_l; eauto.
Qed.

Lemma mem_compatible_with_age {n tp m phi} :
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

Lemma resource_decay_lockSet_in_juicyLocks b phi phi' lset :
  resource_decay b phi phi' ->
  lockSet_block_bound lset b ->
  lockSet_in_juicyLocks lset phi ->
  lockSet_in_juicyLocks lset phi'.
Proof.
  intros RD LB IN loc IT.
  destruct (IN _ IT) as (rsh & sh & pp & E).
  (* assert (SL : same_locks phi phi') by (eapply resource_decay_same_locks; eauto). *)
  assert (SL : same_locks_sized phi phi') by (eapply resource_decay_same_locks_sized; eauto).
  destruct (SL loc LKSIZE) as [(rsh' & sh' & pp' &  E') _].
  { rewrite E. exists rsh, sh, pp. reflexivity. }
  destruct RD as [L RD].
  destruct (RD loc) as [NN [R|[R|[[P [v R]]|R]]]].
  + rewrite E in R. simpl in R; rewrite <- R.
    eauto.
  + rewrite E in R. destruct R as (sh'' & v & v' & R & H). discriminate.
  + specialize (LB loc).
    cut (fst loc < b)%positive. now intro; exfalso; eauto.
    apply LB. destruct (AMap.find (elt:=option rmap) loc lset).
    * apply I.
    * inversion IT.
  + destruct R as (v & v' & R & N').
    rewrite E'.
    exists rsh', sh', pp'.
    eauto.
Qed.

Lemma resource_decay_joinlist b phi1 phi1' l Phi :
  rmap_bound b Phi ->
  resource_decay b phi1 phi1' ->
  joinlist (phi1 :: l) Phi ->
  exists Phi',
    joinlist (phi1' :: (map (age_to (level phi1')) l)) Phi' /\
    resource_decay b Phi Phi'.
Proof.
  intros B rd (x & h & j).
  assert (Bx : rmap_bound b x). { apply (rmap_bound_join j) in B. intuition. }
  destruct (resource_decay_join _ _ _ _ _ Bx rd j) as (Phi' & j' & rd').
  exists Phi'; split; auto.
  exists (age_to (level phi1') x); split; auto.
  apply joinlist_age_to, h.
Qed.

Lemma resource_decay_join_all {tp m Phi} c' {phi' i} {cnti : ThreadPool.containsThread tp i}:
  rmap_bound (Mem.nextblock m) Phi ->
  resource_decay (Mem.nextblock m) (getThreadR i tp cnti) phi' /\
  level (getThreadR i tp cnti) = S (level phi') ->
  join_all tp Phi ->
  exists Phi',
    join_all (@updThread i (age_tp_to (level phi') tp) (cnt_age' cnti) c' phi') Phi' /\
    resource_decay (Mem.nextblock m) Phi Phi' /\
    level Phi = S (level Phi').
Proof.
  do 2 rewrite join_all_joinlist.
  intros B (rd, lev) j.
  rewrite (maps_getthread _ _ cnti) in j.
  destruct (resource_decay_joinlist _ _ _ _ _ B rd j) as (Phi' & j' & rd').
  exists Phi'; split; [ | split]; auto.
  - rewrite maps_updthread.
    exact_eq j'. f_equal. f_equal. rewrite <-all_but_map, maps_age_to.
    auto.
  - exact_eq lev; f_equal.
    + apply rmap_join_sub_eq_level. eapply joinlist_join_sub; eauto. left; auto.
    + f_equal. apply rmap_join_sub_eq_level. eapply joinlist_join_sub; eauto. left; auto.
Qed.

Lemma resource_fmap_YES_inv f g r sh rsh k pp :
  resource_fmap f g r = YES sh rsh k pp ->
  exists pp', r = YES sh rsh k pp' /\ pp = preds_fmap f g pp'.
Proof.
  destruct r as [t0 | t0 p k0 p0 | k0 p]; simpl; try congruence.
  injection 1 as <- <- <- <-. eauto.
Qed.

Lemma resource_fmap_PURE_inv f g r k pp :
  resource_fmap f g r = PURE k pp ->
  exists pp', r = PURE k pp' /\ pp = preds_fmap f g pp'.
Proof.
  destruct r as [t0 | t0 p k0 p0 | k0 p]; simpl; try congruence.
  injection 1 as <- <-. eauto.
Qed.

Lemma resource_fmap_NO_inv f g r rsh :
  resource_fmap f g r = NO rsh ->
  r = NO rsh.
Proof.
  destruct r as [t0 | t0 p k0 p0 | k0 p]; simpl; try congruence.
Qed.

Lemma isSome_option_map {A B} (f : A -> B) o : ssrbool.isSome (option_map f o) = ssrbool.isSome o.
Proof.
  destruct o; reflexivity.
Qed.

Lemma cl_step_mem_step ge c m c' m' : cl_step ge c m c' m' -> mem_step m m'.
Admitted.

Lemma mem_step_contents_at_None m m' loc :
  Mem.valid_block m (fst loc) ->
  mem_step m m' ->
  access_at m loc Cur = None ->
  contents_at m' loc = contents_at m loc.
Proof.
  intros V Ms Ac.
  destruct loc as (b, ofs).
  pose proof mem_step_obeys_cur_write m b ofs m' V as H.
  specialize H _ Ms.
  unfold contents_at in *.
  simpl; symmetry.
  apply H; clear H.
  unfold access_at in *.
  unfold Mem.perm in *.
  simpl in *.
  rewrite Ac.
  intros O; inversion O.
Qed.

Lemma mem_step_contents_at_Nonempty m m' loc :
  Mem.valid_block m (fst loc) ->
  mem_step m m' ->
  access_at m loc Cur = Some Nonempty ->
  contents_at m' loc = contents_at m loc.
Proof.
  intros V Ms Ac.
  destruct loc as (b, ofs).
  pose proof mem_step_obeys_cur_write m b ofs m' V as H.
  specialize H _ Ms.
  unfold contents_at in *.
  simpl; symmetry.
  apply H; clear H.
  unfold access_at in *.
  unfold Mem.perm in *.
  simpl in *.
  rewrite Ac.
  intros O; inversion O.
Qed.

Import Mem.

Lemma perm_of_res_resource_fmap f g r :
  perm_of_res (resource_fmap f g r) = perm_of_res r.
Proof.
  destruct r as [t0 | t0 p [] p0 | k p]; simpl; auto.
Qed.

Lemma resource_fmap_join f g r1 r2 r3 :
  join r1 r2 r3 ->
  join (resource_fmap f g r1) (resource_fmap f g r2) (resource_fmap f g r3).
Proof.
  destruct r1 as [t1 | t1 p1 k1 pp1 | k1 pp1];
    destruct r2 as [t2 | t2 p2 k2 pp2 | k2 pp2];
    destruct r3 as [t3 | t3 p3 k3 pp3 | k3 pp3]; simpl; auto;
      intros j; inv j; constructor; auto.
Qed.

Lemma juicy_mem_perm_of_res_Max jm loc :
  perm_order'' (max_access_at (m_dry jm) loc) (perm_of_res (m_phi jm @ loc)).
Proof.
  rewrite <- (juicy_mem_access jm loc).
  apply access_cur_max.
Qed.

Lemma decay_rewrite m m' :
  decay m m' <->
  forall loc, 
    (~valid_block m (fst loc) ->
     valid_block m' (fst loc) ->
     (forall k, access_at m' loc k = Some Freeable) \/
     (forall k, access_at m' loc k = None))
    /\ (valid_block m (fst loc) ->
       (forall k, (access_at m loc k = Some Freeable /\ access_at m' loc k = None)) \/
       (forall k, access_at m loc k = access_at m' loc k)).
Proof.
  unfold decay.
  match goal with
    |- (forall x : ?A, forall y : ?B, ?P) <-> _ =>
    eapply iff_trans with (forall loc : A * B, let x := fst loc in let y := snd loc in P)
  end.
  {
    split.
    intros H []; apply H.
    intros H b ofs; apply (H (b, ofs)).
  }
  split; auto.
Qed.

Lemma valid_block0 m b : ~valid_block m b <-> (b >= nextblock m)%positive.
Proof.
  unfold valid_block in *.
  unfold Plt in *.
  split; zify; omega.
Qed.

Lemma valid_block1 m b : valid_block m b <-> (b < nextblock m)%positive.
Proof.
  unfold valid_block in *.
  unfold Plt in *.
  split; zify; omega.
Qed.

Lemma not_Pge_Plt a b : ~ Pge a b -> Plt a b.
Proof.
  unfold Plt. zify. omega.
Qed.

Lemma mem_cohere'_redundant m phi :
  contents_cohere m phi ->
  access_cohere' m phi ->
  alloc_cohere m phi ->
  mem_cohere' m phi.
Proof.
  intros A B D; constructor; auto.
  (* proving now max_access_cohere *)
  intros loc. autospec B.
  destruct (phi @ loc) as [t0 | t0 p [] p0 | k p]; auto.
  { unfold perm_of_res in *.
    unfold perm_of_sh in *.
    if_tac. now destruct Share.nontrivial; auto.
    if_tac. now auto.
    tauto. }
  all:destruct (plt (fst loc) (nextblock m)) as [|n]; [ assumption | exfalso ].
  all:unfold max_access_at in *.
  all:unfold access_at in *.
  all:rewrite (nextblock_noaccess m _ (snd loc) Max n) in B.
  all:inversion B.
Qed.

Lemma mem_cohere_age_to_inv n m phi :
  mem_cohere' m (age_to n phi) ->
  mem_cohere' m phi.
Proof.
  intros [A B C D]; split.
  - unfold contents_cohere in *.
    intros rsh sh v loc pp H.
    specialize (A rsh sh v loc).
    rewrite age_to_resource_at, H in A.
    simpl in A.
    specialize (A _ eq_refl).
    destruct A as [A1 A2].
    split. apply A1.
    Lemma preds_fmap_NoneP pp n g : preds_fmap (approx n) g pp = NoneP -> pp = NoneP.
    Proof.
      destruct pp. simpl.
      unfold NoneP in *.
      injection 1 as -> F.
      f_equal.
      extensionality x.
      apply inj_pair2 in F.
      pose proof (@equal_f _ _ _ _ F x) as E.
      simpl in E.
    Abort.
Abort.

Lemma mem_cohere_step c c' jm jm' Phi (X : rmap) ge :
  mem_cohere' (m_dry jm) Phi ->
  sepalg.join (m_phi jm) X Phi ->
  corestep (juicy_core_sem cl_core_sem) ge c jm c' jm' ->
  exists Phi',
    sepalg.join (m_phi jm') (age_to (level (m_phi jm')) X) Phi' /\
    mem_cohere' (m_dry jm') Phi'.
Proof.
  intros MC J C.
  destruct C as [step [RD L]].
  assert (Bx : rmap_bound (Mem.nextblock (m_dry jm)) X) by apply (rmap_bound_join J), MC.
  destruct (resource_decay_join _ _ _ _ _  Bx RD (* L *) J) as [Phi' [J' RD']].
  exists Phi'. split. apply J'.
  pose proof cl_step_mem_step _ _ _ _ _ step as ms.
  pose proof cl_step_decay _ _ _ _ _ step as dec.
  
  destruct MC as [A B C D].
  unfold contents_cohere in *.
  apply mem_cohere'_redundant.
  
  - (* Proving contents_cohere *)
    intros sh rsh v loc pp AT.
    specialize A _ _ _ loc.
    apply (resource_at_join _ _ _ loc) in J.
    apply (resource_at_join _ _ _ loc) in J'.
    destruct RD as (lev, RD); specialize (RD loc).
    
    rewrite age_to_resource_at in *.
    pose proof juicy_mem_contents jm as Co.
    pose proof juicy_mem_contents jm' as Co'.
    pose proof juicy_mem_access jm as Ac.
    pose proof juicy_mem_access jm' as Ac'.
    unfold contents_cohere in *.
    specialize Co _ _ _ loc.
    specialize Co' _ _ _ loc.
    specialize (Ac loc).
    specialize (Ac' loc).
    specialize (Bx loc).
    remember (Phi @ loc) as R.
    remember (Phi' @ loc) as R'.
    remember (m_phi jm @ loc) as j.
    remember (m_phi jm' @ loc) as j'.
    remember (X @ loc) as x.
    remember (resource_fmap (approx (level (m_phi jm'))) (approx (level (m_phi jm'))) x) as x'.
    clear Heqx Heqj Heqj' HeqR' HeqR.
    subst R'.
    inv J'.
    
    + (* everything in jm' *)
      specialize (Co' _ _ _ _ eq_refl).
      auto.
    
    + (* everything in X : it means nothing has been changed at this place in jm' *)
      symmetry in H0.
      apply resource_fmap_YES_inv in H0.
      destruct H0 as (pp' & -> & ->).
      
      inv J.
      * (* case where nothing came from jm, which means indeed
        contents was not changed *)
        specialize (A _ _ _ _ eq_refl).
        destruct A as [A ->].
        rewrite preds_fmap_NoneP; split; auto.
        simpl in Ac.
        assert (Mem.valid_block (m_dry jm) (fst loc)). {
          apply not_Pge_Plt.
          intros Hl; specialize (Bx Hl).
          discriminate.
        }
        if_tac in Ac.
        -- rewrite mem_step_contents_at_None with (m := m_dry jm); auto.
        -- rewrite mem_step_contents_at_Nonempty with (m := m_dry jm); auto.
      
      * (* case where something was in jm, which is impossible because
        everything is in X *)
        exfalso.
        destruct RD as [NN [RD|[RD|[[P [v' RD]]|RD]]]].
        all: breakhyps.
        injection H as -> -> -> ->.
        apply join_pfullshare in H5.
        destruct H5.
    
    + (* from both X and jm' *)
      symmetry in H1.
      apply resource_fmap_YES_inv in H1.
      destruct H1 as (pp' & -> & ->).
      simpl in *.
      inv J; eauto.
  
  - (* Proving access_cohere' *)
    intros loc.
    specialize (B loc).
    destruct RD as (lev, RD).
    specialize (RD loc).
    destruct RD as [NN [RD|[RD|[[P [v' RD]]|RD]]]].
    + (* The "preserving" case of resource_decay: in this case, same
      wet resources in jm and jm', hence same resources in Phi and
      Phi' *)
      apply resource_at_join with (loc := loc) in J'.
      rewrite <-RD in J'.
      rewrite age_to_resource_at in J'.
      
      apply resource_at_join with (loc := loc) in J.
      pose proof resource_fmap_join (approx (level (m_phi jm'))) (approx (level (m_phi jm'))) _ _ _ J as J_.
      pose proof join_eq J' J_ as E'.
      
      rewrite decay_rewrite in dec.
      specialize (dec loc).
      unfold rmap_bound in *.
      
      destruct dec as (dec1, dec2).
      destruct (valid_block_dec (m_dry jm) (fst loc)); swap 1 2.
      * rewrite <-valid_block0 in NN. autospec NN. rewrite NN in *.
        do 2 autospec Bx.
        rewrite Bx in *.
        inv J.
        rewr (Phi @ loc) in E'. simpl in E'. rewrite E'.
        apply join_bot_bot_eq in RJ. subst. simpl. if_tac. 2:tauto.
        destruct (max_access_at (m_dry jm') loc); constructor.
      * clear dec1. autospec dec2.
        destruct dec2 as [Freed | Same].
        -- exfalso (* old Cur is Freeable, new Cur is None, which
           contradict the case from resource_decay *).
           clear NN step lev L Bx A v.
           clear -Freed RD.
           specialize (Freed Cur).
           do 2 rewrite juicy_mem_access in Freed.
           rewrite <-RD in Freed.
           rewrite perm_of_res_resource_fmap in Freed.
           destruct Freed; congruence.
        -- unfold max_access_at in * (* same Cur and Max *).
           rewrite <-(Same Max), E'.
           rewrite perm_of_res_resource_fmap; auto.
    
    + (* "Write" case *)
      destruct RD as (rsh & v & v' & E & E').
      rewrite decay_rewrite in dec.
      specialize (dec loc).
      unfold rmap_bound in *.
      destruct dec as (dec1, dec2).
      destruct (valid_block_dec (m_dry jm) (fst loc)); swap 1 2.
      * rewrite <-valid_block0 in NN. autospec NN. rewrite NN in *.
        discriminate.
      * clear dec1. autospec dec2. clear v0 Bx.
        destruct dec2 as [Freed | Same].
        -- specialize (Freed Cur).
           do 2 rewrite juicy_mem_access in Freed.
           rewrite E' in Freed. destruct Freed. simpl in *.
           unfold perm_of_sh in *. repeat if_tac in H0; try discriminate.
           unfold fullshare in *.
           tauto.
        -- unfold max_access_at in * (* same Cur and Max *).
           rewrite <-(Same Max).
           replace (perm_of_res (Phi' @ loc)) with (perm_of_res (Phi @ loc)). auto.
           apply resource_at_join with (loc := loc) in J'.
           apply resource_at_join with (loc := loc) in J.
           rewrite E' in J'.
           apply (resource_fmap_join (approx (level (m_phi jm'))) (approx (level (m_phi jm')))) in J.
           rewrite E in J.
           rewrite age_to_resource_at in J'.
           remember (resource_fmap (approx (level (m_phi jm'))) (approx (level (m_phi jm'))) (X @ loc)) as r.
           inv J; inv J'.
           ++ symmetry in H.
              apply resource_fmap_YES_inv in H.
              destruct H as (pp' & -> & Epp).
              simpl; f_equal.
              assert (rsh0 = rsh2) by congruence. subst.
              eapply join_eq; eauto.
           ++ destruct (X @ loc); congruence.
           ++ destruct (X @ loc); congruence.
           ++ assert (rsh0 = rsh2) by congruence. subst.
              assert (sh0 = sh2) by congruence. subst.
              symmetry in H5.
              apply resource_fmap_YES_inv in H5.
              destruct H5 as (pp' & -> & Epp).
              simpl; f_equal.
              ** eapply join_eq; eauto.
              ** eapply join_eq; eauto.
    
    + (* "Alloc" case *)
      autospec NN.
      eapply perm_order''_trans. now apply access_cur_max.
      rewrite juicy_mem_access.
      rewrite RD.
      simpl.
      rewrite perm_of_freeable.
      destruct (perm_of_res (Phi' @ loc)) as [[]|]; constructor.
    
    + (* "Free" case *)
      cut (perm_of_res (Phi' @ loc) = None).
      { intros ->. destruct (max_access_at (m_dry jm') loc) as [[]|]; constructor. }
      destruct RD as (v & pp & E & E').
      apply resource_at_join with (loc := loc) in J'.
      apply resource_at_join with (loc := loc) in J.
      rewrite E in J. rewrite E' in J'.
      inv J.
      * apply join_top_l in RJ. subst.
        rewrite age_to_resource_at in J'.
        rewr (X @ loc) in J'. simpl in J'.
        inv J'.
        apply join_bot_bot_eq in RJ; subst.
        simpl. if_tac. auto. tauto.
      * apply join_pfullshare in H0. tauto.
  
  - (* Proving alloc_cohere *)
    intros loc g.
    pose proof juicy_mem_alloc_cohere jm' loc g as Ac'.
    specialize (Bx loc).
    assert_specialize Bx. {
      apply Pos.le_ge. apply Pos.ge_le in g. eapply Pos.le_trans. 2:eauto.
      apply forward_nextblock.
      apply mem_step_forward, ms.
    }
    apply resource_at_join with (loc := loc) in J'.
    rewr (m_phi jm' @ loc) in J'.
    rewrite age_to_resource_at in J'.
    rewr (X @ loc) in J'.
    simpl in J'.
    inv J'.
    rewrite (join_bot_bot_eq rsh3); auto.
Qed.

Lemma matchfunspec_age_to e Gamma n Phi :
  matchfunspec e Gamma Phi ->
  matchfunspec e Gamma (age_to n Phi).
Proof.
  unfold matchfunspec in *.
  apply age_to_pred.
Qed.

Lemma resource_decay_matchfunspec {b phi phi' g Gamma} :
  resource_decay b phi phi' ->
  matchfunspec g Gamma phi ->
  matchfunspec g Gamma phi'.
Proof.
  intros RD M.
  unfold matchfunspec in *.
  intros b0 fs psi' necr' FUN.
  specialize (M b0 fs phi ltac:(constructor 2)).
  apply (hereditary_necR necr').
  { clear.
    intros phi phi' A (id & hg & hgam); exists id; split; auto. }
  apply (anti_hereditary_necR necr') in FUN; swap 1 2.
  { intros x y a. apply anti_hereditary_func_at', a. }
  apply (resource_decay_func_at'_inv RD) in FUN.
  autospec M.
  destruct M as (id & Hg & HGamma).
  exists id; split; auto.
Qed.

Lemma LockRes_age_content1 js n a :
  lockRes (age_tp_to n js) a = option_map (option_map (age_to n)) (lockRes js a).
Proof.
  cleanup.
  rewrite lset_age_tp_to, AMap_find_map_option_map.
  reflexivity.
Qed.

Lemma m_phi_jm_ m tp phi i cnti compat :
  m_phi (@jm_ tp m phi i cnti compat) = getThreadR i tp cnti.
Proof.
  reflexivity.
Qed.

(** About lock_coherence *)

Lemma resource_decay_lock_coherence {b phi phi' lset m} :
  resource_decay b phi phi' ->
  lockSet_block_bound lset b ->
  (forall l p, AMap.find l lset = Some (Some p) -> level p = level phi) ->
  lock_coherence lset phi m ->
  lock_coherence (AMap.map (Coqlib.option_map (age_to (level phi'))) lset) phi' m.
Proof.
  intros rd BOUND SAMELEV LC loc; pose proof rd as rd'; destruct rd' as [L RD].
  specialize (LC loc).
  specialize (RD loc).
  rewrite AMap_find_map_option_map.
  destruct (AMap.find loc lset)
    as [[unlockedphi | ] | ] eqn:Efind;
    simpl option_map; cbv iota beta; swap 1 3.
  - rewrite <-isLKCT_rewrite.
    rewrite <-isLKCT_rewrite in LC.
    intros sh sh' z pp.
    destruct RD as [NN [R|[R|[[P [v R]]|R]]]].
    + split; intros E; rewrite E in *;
        destruct (phi @ loc); try destruct k; simpl in R; try discriminate;
          [ refine (proj1 (LC _ _ _ _) _); eauto
          | refine (proj2 (LC _ _ _ _) _); eauto ].
    + destruct R as (sh'' & v & v' & E & E'). split; congruence.
    + split; congruence.
    + destruct R as (sh'' & v & v' & R). split; congruence.
  
  - assert (fst loc < b)%positive.
    { apply BOUND.
      rewrite Efind.
      constructor. }
    destruct LC as (dry & sh & R & lk); split; auto.
    eapply resource_decay_LK_at in lk; eauto.
  
  - assert (fst loc < b)%positive.
    { apply BOUND.
      rewrite Efind.
      constructor. }
    destruct LC as (dry & sh & R & lk & sat); split; auto.
    exists sh, (approx (level phi') R); split.
    + eapply resource_decay_LK_at' in lk; eauto.
    + match goal with |- ?a \/ ?b => cut (~b -> a) end.
      { destruct (level phi'); auto. } intros Nz.
      split.
      * rewrite level_age_by.
        rewrite level_age_to.
        -- omega.
        -- apply SAMELEV in Efind.
           eauto with *.
      * destruct sat as [sat | ?]; [ | omega ].
        unfold age_to.
        rewrite age_by_age_by.
        rewrite plus_comm.
        rewrite <-age_by_age_by.
        apply age_by_ind.
        { destruct R as [p h]. apply h. }
        apply sat.
Qed.

Lemma lock_coherence_age_to lset Phi m n :
  lock_coherence lset Phi m ->
  lock_coherence (AMap.map (option_map (age_to n)) lset) Phi m.
Proof.
  intros C loc; specialize (C loc).
  rewrite AMap_find_map_option_map.
  destruct (AMap.find (elt:=option rmap) loc lset) as [[o|]|];
    simpl option_map;
    cbv iota beta.
  all:try solve [intuition].
  destruct C as [B C]; split; auto. clear B.
  destruct C as (sh & R & lk & sat).
  exists sh, R; split. eauto.
  destruct sat as [sat|?]; auto. left.
  unfold age_to.
  rewrite age_by_age_by, plus_comm, <-age_by_age_by.
  revert sat.
  apply age_by_ind.
  apply (proj2_sig R).
Qed.

Lemma load_restrPermMap m tp Phi b ofs m_any
  (compat : mem_compatible_with tp m Phi) :
  lock_coherence (lset tp) Phi m_any ->
  AMap.find (elt:=option rmap) (b, ofs) (lset tp) <> None ->
  Mem.load
    Mint32
    (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget compat)))
    b ofs =
  Some (decode_val Mint32 (Mem.getN (size_chunk_nat Mint32) ofs (Mem.mem_contents m) !! b)).
Proof.
  intros lc e.
  Transparent Mem.load.
  unfold Mem.load in *.
  if_tac; auto.
  exfalso.
  apply H.
  eapply Mem.valid_access_implies.
  eapply lset_valid_access; eauto.
  constructor.
Qed.

Lemma lock_coh_bound tp m Phi
      (compat : mem_compatible_with tp m Phi)
      (coh : lock_coherence' tp Phi m compat) :
  lockSet_block_bound (lset tp) (Mem.nextblock m).
Proof.
  intros loc find.
  specialize (coh loc).
  destruct (AMap.find (elt:=option rmap) loc (lset tp)) as [o|]; [ | inversion find ].
  match goal with |- (?a < ?b)%positive => assert (D : (a >= b \/ a < b)%positive) by (zify; omega) end.
  destruct D as [D|D]; auto. exfalso.
  assert (AT : exists (sh : Share.t) (R : pred rmap), (LK_at R sh loc) Phi). {
    destruct o.
    - destruct coh as [LOAD (sh' & R' & lk & sat)]; eauto.
    - destruct coh as [LOAD (sh' & R' & lk)]; eauto.
  }
  clear coh.
  destruct AT as (sh & R & AT).
  destruct compat.
  destruct all_cohere0.
  specialize (all_coh0 loc D).
  specialize (AT loc).
  destruct loc as (b, ofs).
  simpl in AT.
  if_tac in AT. 2:range_tac.
  if_tac in AT. 2:tauto.
  rewrite all_coh0 in AT.
  destruct AT.
  congruence.
Qed.

Lemma same_except_cur_jm_ tp m phi i cnti compat :
  same_except_cur m (m_dry (@jm_ tp m phi i cnti compat)).
Proof.
  repeat split.
  extensionality loc.
  apply juicyRestrictMax.
Qed.

Lemma level_jm_ m tp Phi (compat : mem_compatible_with tp m Phi)
      i (cnti : containsThread tp i) :
  level (jm_ cnti compat) = level Phi.
Proof.
  rewrite level_juice_level_phi.
  apply join_sub_level.
  unfold jm_ in *.
  unfold personal_mem in *.
  simpl.
  apply compatible_threadRes_sub, compat.
Qed.

Lemma resource_decay_join_identity b phi phi' e e' :
  resource_decay b phi phi' ->
  sepalg.joins phi e ->
  sepalg.joins phi' e' ->
  identity e ->
  identity e' ->
  e' = age_to (level phi') e.
Proof.
  intros rd j j' i i'.
  apply rmap_ext.
  - apply rmap_join_eq_level in j.
    apply rmap_join_eq_level in j'.
    destruct rd as (lev, rd).
    rewrite level_age_to; eauto with *.
  - intros l.
    rewrite age_to_resource_at.
    apply resource_at_identity with (loc := l) in i.
    apply resource_at_identity with (loc := l) in i'.
    apply empty_NO in i.
    apply empty_NO in i'.
    destruct j as (a & j).
    destruct j' as (a' & j').
    apply resource_at_join with (loc := l) in j.
    apply resource_at_join with (loc := l) in j'.
    unfold compcert_rmaps.R.AV.address in *.
    destruct i as [E | (k & pp & E)], i' as [E' | (k' & pp' & E')]; rewrite E, E' in *.
    + reflexivity.
    + inv j'.
      pose proof resource_decay_PURE_inv rd as I.
      repeat autospec I.
      breakhyps.
      rewr (phi @ l) in j.
      inv j.
    + inv j.
      pose proof resource_decay_PURE rd as I.
      repeat autospec I.
      rewr (phi' @ l) in j'.
      inv j'.
    + inv j.
      pose proof resource_decay_PURE rd as I.
      specialize (I l k pp ltac:(auto)).
      rewr (phi' @ l) in j'.
      inv j'.
      reflexivity.
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

Lemma pures_age_eq phi n :
  ge (level phi) n ->
  pures_eq phi (age_to n phi).
Proof.
  split; intros loc; rewrite age_to_resource_at.
  - destruct (phi @ loc); auto; simpl; do 3 f_equal; rewrite level_age_to; auto.
  - destruct (phi @ loc); simpl; eauto.
Qed.

Lemma pures_same_jm_ m tp Phi (compat : mem_compatible_with tp m Phi)
      i (cnti : containsThread tp i) :
  pures_same (m_phi (jm_ cnti compat)) Phi.
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
  apply safe_downward1.
Qed.

Lemma mem_cohere'_store m tp m' b ofs i Phi :
  forall Hcmpt : mem_compatible tp m,
    lockRes tp (b, Int.intval ofs) <> None ->
    Mem.store
      Mint32 (restrPermMap (mem_compatible_locks_ltwritable Hcmpt))
      b (Int.intval ofs) (Vint i) = Some m' ->
    mem_compatible_with tp m Phi (* redundant with Hcmpt, but easier *) ->
    mem_cohere' m' Phi.
Proof.
  intros Hcmpt lock Hstore compat.
  pose proof store_outside' _ _ _ _ _ _ Hstore as SO.
  destruct compat as [J MC LW JL LJ].
  destruct MC as [Co Ac Ma N].
  split.
  - intros sh sh' v (b', ofs') pp E.
    specialize (Co sh sh' v (b', ofs') pp E).
    destruct Co as [<- ->]. split; auto.
    destruct SO as (Co1 & A1 & N1).
    specialize (Co1 b' ofs').
    destruct Co1 as [In|Out].
    + exfalso (* because there is no lock at (b', ofs') *).
      specialize (LJ (b, Int.intval ofs)).
      cleanup.
      destruct (AMap.find (elt:=option rmap) (b, Int.intval ofs) (lset tp)).
      2:tauto.
      autospec LJ.
      destruct LJ as (sh1 & sh1' & pp & EPhi).
      destruct In as (<-, In).
      destruct (eq_dec ofs' (Int.intval ofs)).
      * subst ofs'.
        congruence.
      * pose (ii := (ofs' - Int.intval ofs)%Z).
        assert (Hii : (0 < ii < LKSIZE)%Z).
        { unfold ii; split. omega.
          unfold LKSIZE, LKCHUNK, align_chunk, size_chunk in *.
          omega. }
        pose proof rmap_valid_e1 Phi b (Int.intval ofs) _ _ Hii sh1' as H.
        assert_specialize H.
        { rewrite EPhi. reflexivity. }
        replace (Int.intval ofs + ii)%Z with ofs' in H by (unfold ii; omega).
        rewrite E in H. simpl in H. congruence.
        
    + rewrite <-Out.
      rewrite restrPermMap_contents.
      auto.
      
  - intros loc.
    replace (max_access_at m' loc)
    with (max_access_at
            (restrPermMap (mem_compatible_locks_ltwritable Hcmpt)) loc)
    ; swap 1 2.
    { unfold max_access_at in *.
      destruct SO as (_ & -> & _). reflexivity. }
    clear SO.
    rewrite restrPermMap_max.
    apply Ac.
    
  - cut (max_access_cohere (restrPermMap (mem_compatible_locks_ltwritable Hcmpt)) Phi).
    { unfold max_access_cohere in *.
      unfold max_access_at in *.
      destruct SO as (_ & <- & <-). auto. }
    intros loc; specialize (Ma loc).
    rewrite restrPermMap_max. auto.

  - unfold alloc_cohere in *.
    destruct SO as (_ & _ & <-). auto.
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

Lemma access_at_fold m b ofs k :
  (mem_access m) !! b ofs k = access_at m (b, ofs) k.
Proof.
  reflexivity.
Qed.
  
Lemma personal_mem_equiv_spec m m' phi pr pr' :
  nextblock m = nextblock m' ->
  (forall loc, max_access_at m loc = max_access_at m' loc) ->
  (forall loc, isVAL (phi @ loc) -> contents_at m loc = contents_at m' loc) ->
  mem_equiv
    (m_dry (@personal_mem m phi pr))
    (m_dry (@personal_mem m' phi pr')).
Proof.
  intros En Emax Econt.
  
  assert (same_perm :
            forall b ofs k p,
              perm (juicyRestrict _ _ (acc_coh pr)) b ofs k p <->
              perm (juicyRestrict _ _ (acc_coh pr')) b ofs k p).
  {
    intros.
    unfold juicyRestrict in *.
    unfold perm in *.
    unfold perm_order' in *.
    match goal with |-context[PMap.get ?a ?b ?c ?d] => set (x := PMap.get a b c d) end.
    match goal with |-context[PMap.get ?a ?b ?c ?d] => set (y := PMap.get a b c d) end.
    cut (x = y); [ intros ->; intuition | unfold x, y; clear x y].
    do 2 rewrite access_at_fold.
    destruct k.
    - do 2 rewrite restrPermMap_Max'.
      apply Emax.
    - do 2 rewrite restrPermMap_Cur'.
      simpl.
      rewrite <-juic2Perm_correct. 2: apply pr.
      rewrite <-juic2Perm_correct. 2: apply pr'.
      reflexivity.
  }
  
  unfold personal_mem in *; simpl.
  split3.
  - Transparent loadbytes.
    unfold loadbytes in *.
    extensionality b ofs n.
    destruct (range_perm_dec _ _ _) as [R1|R1];
      destruct (range_perm_dec _ _ _) as [R2|R2].
    + simpl.
      destruct n as [ | n | ]; auto.
      assert (Z.pos n = Z.of_nat (nat_of_Z (Z.pos n))) as R.
      { rewrite Coqlib.nat_of_Z_eq; auto. zify. omega. }
      rewrite R in R1, R2. remember (nat_of_Z (Z.pos n)) as k.
      clear Heqk R n.
      revert ofs R1 R2; induction k; intros ofs R1 R2; auto.
      simpl.
      do 2 f_equal.
      * clear IHk.
        specialize (Econt (b, ofs)).
        apply Econt.
        specialize (R1 ofs ltac:(zify;omega)).
        pose proof @juicyRestrictCurEq phi m ltac:(apply pr) (b, ofs) as R.
        unfold access_at in R.
        simpl fst in R; simpl snd in R.
        unfold perm in R1.
        rewrite R in R1.
        destruct (phi @ (b, ofs)) as [t0 | t0 p [] p0 | k0 p]; auto; try inversion R1 || constructor.
        simpl in R1. if_tac in R1; inversion R1.
      * match goal with |- ?x = ?y => cut (Some x = Some y); [injection 1; auto | ] end.
        apply IHk.
        -- intros ofs' int; apply (R1 ofs' ltac:(zify; omega)).
        -- intros ofs' int; apply (R2 ofs' ltac:(zify; omega)).
    + exfalso.
      apply R2; clear R2.
      intros ofs' int; specialize (R1 ofs' int).
      rewrite same_perm in R1; auto.
    + exfalso.
      apply R1; clear R1.
      intros ofs' int; specialize (R2 ofs' int).
      rewrite <-same_perm in R2; auto.
    + reflexivity.
  - extensionality b ofs k.
    extensionality p.
    apply prop_ext; auto.
  - auto.
Qed.

Lemma juicyRestrict_ext  m phi phi' pr pr' :
  (forall loc, perm_of_res (phi @ loc) = perm_of_res (phi' @ loc)) ->
  juicyRestrict phi m (acc_coh pr) = juicyRestrict phi' m (acc_coh pr').
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

Lemma juicyRestrict_age_to m phi n pr pr' :
  @juicyRestrict (@age_to n rmap ag_rmap phi) m (@acc_coh m (@age_to n rmap ag_rmap phi) pr) =
  @juicyRestrict phi m (@acc_coh m phi pr').
Proof.
  apply mem_ext; auto.
  apply juicyRestrictCur_ext.
  intros loc.
  apply perm_of_age.
Qed.

Lemma personal_mem_age_to m phi n pr pr' :
  @personal_mem m (age_to n phi) pr =
  age_to n (@personal_mem m phi pr').
Proof.
  apply juicy_mem_ext; simpl.
  - rewrite m_dry_age_to. simpl.
    unshelve erewrite juicyRestrict_age_to. auto.
    auto.
  - rewrite m_phi_age_to. reflexivity.
Qed.

Lemma personal_mem_rewrite m phi phi' pr pr' :
  phi = phi' ->
  @personal_mem m phi pr = @personal_mem m phi' pr'.
Proof.
  intros ->; f_equal. apply proof_irr.
Qed.

Lemma jm_updThreadC i tp ctn c' m Phi cnti pr pr' :
  @jm_ (@updThreadC i tp ctn c') m Phi i cnti pr =
  @jm_ tp m Phi i cnti pr'.
Proof.
  apply juicy_mem_ext.
  - apply juicyRestrict_ext.
    REWR.
    intro; repeat f_equal. apply proof_irr.
  - do 2 rewrite m_phi_jm_.
    REWR.
    repeat f_equal. apply proof_irr.
Qed.

Lemma islock_valid_access tp m b ofs p
      (compat : mem_compatible tp m) :
  (4 | ofs) ->
  lockRes tp (b, ofs) <> None ->
  p <> Freeable ->
  Mem.valid_access
    (restrPermMap
       (mem_compatible_locks_ltwritable compat))
    Mint32 b ofs p.
Proof.
  intros div islock NE.
  eapply Mem.valid_access_implies with (p1 := Writable).
  2:destruct p; constructor || tauto.
  pose proof lset_range_perm.
  do 6 autospec H.
  split; auto.
Qed.

Lemma lockSet_Writable_updLockSet_updThread m m' i tp Phi 
      (compat : mem_compatible_with tp m Phi)
      cnti b ofs ophi ophi' c' phi' z
      (pr : mem_compatible tp m)
      (His_unlocked : AMap.find (elt:=option rmap) (b, Int.intval ofs) (lset tp) = Some ophi)
      (Hstore : store Mint32 (restrPermMap (mem_compatible_locks_ltwritable pr)) b 
                      (Int.intval ofs) (Vint z) = Some m') :
  lockSet_Writable (lset (updLockSet (updThread i tp cnti c' phi') (b, Int.intval ofs) ophi')) m'.
Proof.
  pose proof (loc_writable compat) as lw.
  intros b' ofs' is; specialize (lw b' ofs').
  destruct (eq_dec (b, Int.intval ofs) (b', ofs')).
  + injection e as <- <- .
    intros ofs0 int0.
    rewrite (Mem.store_access _ _ _ _ _ _ Hstore).
    pose proof restrPermMap_Max as RR.
    unfold permission_at in RR.
    rewrite RR; clear RR.
    clear is.
    assert_specialize lw. {
      clear lw.
      cleanup.
      rewrite His_unlocked.
      reflexivity.
    }
    specialize (lw ofs0).
    autospec lw.
    exact_eq lw; f_equal.
    unfold getMaxPerm in *.
    rewrite PMap.gmap.
    reflexivity.
  + assert_specialize lw. {
      simpl in is.
      rewrite AMap_find_add in is.
      if_tac in is. tauto.
      exact_eq is.
      unfold ssrbool.isSome in *.
      cleanup.
      destruct (AMap.find (elt:=option rmap) (b', ofs') (lset tp));
        reflexivity.
    }
    intros ofs0 inter.
    specialize (lw ofs0 inter).
    exact_eq lw. f_equal.
    set (m_ := restrPermMap _) in Hstore.
    change (max_access_at m (b', ofs0) = max_access_at m' (b', ofs0)).
    transitivity (max_access_at m_ (b', ofs0)).
    * unfold m_.
      rewrite restrPermMap_max.
      reflexivity.
    * pose proof store_outside' _ _ _ _ _ _ Hstore as SO.
      unfold access_at in *.
      destruct SO as (_ & SO & _).
      apply equal_f with (x := (b', ofs0)) in SO.
      apply equal_f with (x := Max) in SO.
      apply SO.
Qed.

Lemma lockSet_Writable_updThread_updLockSet m m' i tp Phi 
      (compat : mem_compatible_with tp m Phi)
      b ofs ophi ophi' c' phi' z cnti
      (pr : mem_compatible tp m)
      (His_unlocked : AMap.find (elt:=option rmap) (b, Int.intval ofs) (lset tp) = Some ophi)
      (Hstore : store Mint32 (restrPermMap (mem_compatible_locks_ltwritable pr)) b 
                      (Int.intval ofs) (Vint z) = Some m') :
  lockSet_Writable (lset (updThread i (updLockSet tp (b, Int.intval ofs) ophi') cnti c' phi')) m'.
  pose proof (loc_writable compat) as lw.
  intros b' ofs' is; specialize (lw b' ofs').
  destruct (eq_dec (b, Int.intval ofs) (b', ofs')).
  + injection e as <- <- .
    intros ofs0 int0.
    rewrite (Mem.store_access _ _ _ _ _ _ Hstore).
    pose proof restrPermMap_Max as RR.
    unfold permission_at in RR.
    rewrite RR; clear RR.
    clear is.
    assert_specialize lw. {
      clear lw.
      cleanup.
      rewrite His_unlocked.
      reflexivity.
    }
    specialize (lw ofs0).
    autospec lw.
    exact_eq lw; f_equal.
    unfold getMaxPerm in *.
    rewrite PMap.gmap.
    reflexivity.
  + assert_specialize lw. {
      simpl in is.
      rewrite AMap_find_add in is.
      if_tac in is. tauto.
      auto.
    }
    intros ofs0 inter.
    specialize (lw ofs0 inter).
    exact_eq lw. f_equal.
    set (m_ := restrPermMap _) in Hstore.
    change (max_access_at m (b', ofs0) = max_access_at m' (b', ofs0)).
    transitivity (max_access_at m_ (b', ofs0)).
    * unfold m_.
      rewrite restrPermMap_max.
      reflexivity.
    * pose proof store_outside' _ _ _ _ _ _ Hstore as SO.
      unfold access_at in *.
      destruct SO as (_ & SO & _).
      apply equal_f with (x := (b', ofs0)) in SO.
      apply equal_f with (x := Max) in SO.
      apply SO.
Qed.

Section Preservation.
  Variables
    (CS : compspecs)
    (ext_link : string -> ident)
    (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2).

  Definition Jspec' := (@OK_spec (Concurrent_Espec unit CS ext_link)).
  
  Open Scope string_scope.
  
  Lemma Jspec'_juicy_mem_equiv : ext_spec_stable juicy_mem_equiv (JE_spec _ Jspec').
  Proof.
    split; [ | easy ].
    intros e x b tl vl z m1 m2 E.
    
    unfold Jspec' in *.
    destruct e as [name sg | | | | | | | | | | | ].
    all: try (exfalso; simpl in x; do 5 (if_tac in x; [ discriminate | ]); apply x).
    
    (* dependent destruction *)
    revert x.
    
    (** * the case of acquire *)
    funspec_destruct "acquire".
    rewrite (proj2 E).
    exact (fun x y => y).
    
    (** * the case of release *)
    funspec_destruct "release".
    rewrite (proj2 E).
    exact (fun x y => y).
    
    (** * the case of makelock *)
    funspec_destruct "makelock".
    rewrite (proj2 E).
    exact (fun x y => y).
    
    (** * the case of freelock *)
    funspec_destruct "freelock".
    rewrite (proj2 E).
    exact (fun x y => y).
    
    (** * the case of spawn *)
    funspec_destruct "spawn".
    rewrite (proj2 E).
    exact (fun x y => y).
    
    (** * no more cases *)
    simpl; tauto.
  Qed.
  
  Lemma Jspec'_hered : ext_spec_stable age (JE_spec _ Jspec').
  Proof.
    split; [ | easy ].
    intros e x b tl vl z m1 m2 A.
    
    unfold Jspec' in *.
    destruct e as [name sg | | | | | | | | | | | ].
    all: try (exfalso; simpl in x; do 5 (if_tac in x; [ discriminate | ]); apply x).
    
    apply age_jm_phi in A.
    
    (* dependent destruction *)
    revert x.
    1:funspec_destruct "acquire".
    2:funspec_destruct "release".
    3:funspec_destruct "makelock".
    4:funspec_destruct "freelock".
    5:funspec_destruct "spawn".
    
    all:intros.
    all:breakhyps.
    all:agejoinhyp.
    all:breakhyps.
    all:agehyps.
    all:agehyps.
    all:eauto.
  Qed.
  
  (* Preservation lemma for core steps *)  
  Lemma invariant_thread_step
        {Z} (Jspec : juicy_ext_spec Z) Gamma
        n m ge i sch tp Phi ci ci' jmi'
        (Stable : ext_spec_stable age Jspec)
        (Stable' : ext_spec_stable juicy_mem_equiv Jspec)
        (gam : matchfunspec (filter_genv ge) Gamma Phi)
        (compat : mem_compatible_with tp m Phi)
        (En : level Phi = S n)
        (lock_bound : lockSet_block_bound (ThreadPool.lset tp) (Mem.nextblock m))
        (sparse : lock_sparsity (lset tp))
        (lock_coh : lock_coherence' tp Phi m compat)
        (safety : threads_safety Jspec m ge tp Phi compat (S n))
        (wellformed : threads_wellformed tp)
        (unique : unique_Krun tp (i :: sch))
        (cnti : containsThread tp i)
        (stepi : corestep (juicy_core_sem cl_core_sem) ge ci (jm_ cnti compat) ci' jmi')
        (safei' : forall ora : Z, jsafeN Jspec ge n ora ci' jmi')
        (Eci : getThreadC i tp cnti = Krun ci)
        (tp' := age_tp_to (level jmi') tp)
        (tp'' := @updThread i tp' (cnt_age' cnti) (Krun ci') (m_phi jmi') : ThreadPool.t)
        (cm' := (m_dry jmi', ge, (i :: sch, tp''))) :
    state_invariant Jspec Gamma n cm'.
  Proof.
    (** * Two steps : [x] -> [x'] -> [x'']
          1. we age [x] to get [x'], the level decreasing
          2. we update the thread to  get [x'']
     *)
    destruct compat as [J AC LW LJ JL] eqn:Ecompat. 
    rewrite <-Ecompat in *.
    pose proof J as J_; move J_ before J.
    rewrite join_all_joinlist in J_.
    pose proof J_ as J__.
    rewrite maps_getthread with (cnti := cnti) in J__.
    destruct J__ as (ext & Hext & Jext).
    assert (Eni : level (jm_ cnti compat) = S n). {
      rewrite <-En, level_juice_level_phi.
      eapply rmap_join_sub_eq_level.
      exists ext; auto.
    }
    
    (** * Getting new global rmap (Phi'') with smaller level [n] *)
    assert (B : rmap_bound (Mem.nextblock m) Phi) by apply compat.
    destruct (resource_decay_join_all (Krun ci') B (proj2 stepi) J)
      as [Phi'' [J'' [RD L]]].
    rewrite join_all_joinlist in J''.
    assert (Eni'' : level (m_phi jmi') = n). {
      clear -stepi Eni.
      rewrite <-level_juice_level_phi.
      cut (S (level jmi') = S n); [ congruence | ].
      destruct stepi as [_ [_ <-]].
      apply Eni.
    }
    unfold LocksAndResources.res in *.
    pose proof eq_refl tp' as Etp'.
    unfold tp' at 2 in Etp'.
    move Etp' before tp'.
    rewrite level_juice_level_phi, Eni'' in Etp'.
    assert (En'' : level Phi'' = n). {
      rewrite <-Eni''.
      symmetry; apply rmap_join_sub_eq_level.
      rewrite maps_updthread in J''.
      destruct J'' as (r & _ & j).
      exists r; auto.
    }
    
    (** * First, age the whole machine *)
    pose proof J_ as J'.
    unshelve eapply @joinlist_age_to with (n := n) in J'.
    (* auto with *. (* TODO please report -- but hard to reproduce *) *)
    all: hnf.
    all: [> refine ag_rmap |  | refine Age_rmap | refine Perm_rmap ].
    
    (** * Then relate this machine with the new one through the remaining maps *)
    rewrite (maps_getthread i tp cnti) in J'.
    rewrite maps_updthread in J''.
    pose proof J' as J'_. destruct J'_ as (ext' & Hext' & Jext').
    rewrite maps_age_to, all_but_map in J''.
    pose proof J'' as J''_. destruct J''_ as (ext'' & Hext'' & Jext'').
    rewrite Eni'' in *.
    assert (Eext'' : ext'' = age_to n ext). {
      destruct (coqlib3.nil_or_non_nil (map (age_to n) (all_but i (maps tp)))) as [N|N]; swap 1 2.
      - (* Uniqueness of [ext] : when the rest is not empty *)
        eapply @joinlist_age_to with (n := n) in Hext.
        all: [> | now apply Age_rmap | now apply Perm_rmap ].
        unshelve eapply (joinlist_inj _ _ _ _ Hext'' Hext).
        apply N.
      - (* when the list is empty, we know that ext (and hence [age_to
        .. ext]) and ext' are identity, and they join with something
        that have the same PURE *)
        rewrite N in Hext''. simpl in Hext''.
        rewrite <-Eni''.
        eapply resource_decay_join_identity.
        + apply (proj2 stepi).
        + exists Phi. apply Jext.
        + exists Phi''. apply Jext''.
        + change (joinlist nil ext). exact_eq Hext. f_equal.
          revert N.
          destruct (maps tp) as [|? [|]]; destruct i; simpl; congruence || auto.
        + change (joinlist nil ext''). apply Hext''.
    }
    subst ext''.
    
    assert (compat_ : mem_compatible_with tp (m_dry (jm_ cnti compat)) Phi).
    { apply mem_compatible_with_same_except_cur with (m := m); auto.
      apply same_except_cur_jm_. }
    
    assert (compat' : mem_compatible_with tp' (m_dry (jm_ cnti compat)) (age_to n Phi)).
    { unfold tp'.
      rewrite level_juice_level_phi, Eni''.
      apply mem_compatible_with_age. auto. }
    
    assert (compat'' : mem_compatible_with tp'' (m_dry jmi') Phi'').
    {
      unfold tp''.
      constructor.
      
      - (* join_all (proved in lemma) *)
        rewrite join_all_joinlist.
        rewrite maps_updthread.
        unfold tp'. rewrite maps_age_to, all_but_map.
        exact_eq J''; repeat f_equal.
        auto.
      
      - (* cohere *)
        pose proof compat_ as c. destruct c as [_ MC _ _ _].
        destruct (mem_cohere_step
             ci ci' (jm_ cnti compat) jmi'
             Phi ext ge MC Jext stepi) as (Phi''_ & J''_ & MC''_).
        exact_eq MC''_.
        f_equal.
        rewrite Eni'' in J''_.
        eapply join_eq; eauto.
      
      - (* lockSet_Writable *)
        simpl.
        clear -LW stepi lock_coh lock_bound compat_.
        destruct stepi as [step _]. fold (jm_ cnti compat) in step.
        intros b ofs IN.
        unfold tp' in IN.
        rewrite lset_age_tp_to in IN.
        rewrite isSome_find_map in IN.
        specialize (LW b ofs IN).
        intros ofs0 interval.
        
        (* the juicy memory doesn't help much because we care about Max
        here. There are several cases were no permission change, the
        only cases where they do are:
        (1) call_internal (alloc_variables m -> m1)
        (2) return (free_list m -> m')
        in the end, (1) cannot hurt because there is already
        something, but maybe things have returned?
         *)
        
        set (mi := m_dry (jm_ cnti compat)).
        fold mi in step.
        (* state that the Cur [Nonempty] using the juice and the
             fact that this is a lock *)
        assert (CurN : (Mem.mem_access mi) !! b ofs0 Cur = Some Nonempty
                       \/ (Mem.mem_access mi) !! b ofs0 Cur = None).
        {
          pose proof juicyRestrictCurEq as H.
          unfold access_at in H.
          replace b with (fst (b, ofs0)) by reflexivity.
          replace ofs0 with (snd (b, ofs0)) by reflexivity.
          unfold mi.
          destruct compat_ as [_ MC _ _ _].
          destruct MC as [_ AC _ _].
          unfold jm_, personal_mem; simpl m_dry.
          rewrite (H _ _  _ (b, ofs0)).
          cut (Mem.perm_order'' (Some Nonempty) (perm_of_res (getThreadR _ _ cnti @ (b, ofs0)))). {
            destruct (perm_of_res (getThreadR _ _ cnti @ (b,ofs0))) as [[]|]; simpl.
            all:intros po; inversion po; subst; eauto.
          }
          clear -compat IN interval lock_coh lock_bound.
          apply po_trans with (perm_of_res (Phi @ (b, ofs0))).
          - destruct compat.
            specialize (lock_coh (b, ofs)).
            assert (lk : exists (sh : Share.t) (R : pred rmap), (LK_at R sh (b, ofs)) Phi). {
              destruct (AMap.find (elt:=option rmap) (b, ofs) (ThreadPool.lset tp)) as [[lockphi|]|].
              - destruct lock_coh as [_ [sh [R [lk _]]]].
                now eexists _, _; apply lk.
              - destruct lock_coh as [_ [sh [R lk]]].
                now eexists _, _; apply lk.
              - discriminate.
            }
            destruct lk as (sh & R & lk).
            specialize (lk (b, ofs0)). simpl in lk.
            assert (adr_range (b, ofs) lock_size (b, ofs0))
              by apply interval_adr_range, interval.
            if_tac in lk; [ | tauto ].
            if_tac in lk.
            + injection H1 as <-.
              destruct lk as [p ->].
              simpl.
              constructor.
            + destruct lk as [p ->].
              simpl.
              constructor.
          - cut (join_sub (getThreadR _ _ cnti @ (b, ofs0)) (Phi @ (b, ofs0))).
            + apply po_join_sub.
            + apply resource_at_join_sub.
              eapply compatible_threadRes_sub.
              apply compat.
        }
        
        apply cl_step_decay in step.
        pose proof step b ofs0 as D.
        assert (Emi: (Mem.mem_access mi) !! b ofs0 Max = (Mem.mem_access m) !! b ofs0 Max).
        {
          pose proof juicyRestrictMax (acc_coh (thread_mem_compatible (mem_compatible_forget compat) cnti)) (b, ofs0).
          unfold max_access_at, access_at in *.
          simpl fst in H; simpl snd in H.
          rewrite H.
          reflexivity.
        }
        
        destruct (Maps.PMap.get b (Mem.mem_access m) ofs0 Max)
          as [ [ | | | ] | ] eqn:Emax;
          try solve [inversion LW].
        + (* Max = Freeable *)
          
          (* concluding using [decay] *)
          revert step CurN.
          clearbody mi.
          generalize (m_dry jmi'); intros mi'.
          clear -Emi. intros D [NE|NE].
          * replace ((Mem.mem_access mi') !! b ofs0 Max) with (Some Freeable). now constructor.
            symmetry.
            destruct (D b ofs0) as [A B].
            destruct (valid_block_dec mi b) as [v|n].
            -- autospec B.
               destruct B as [B|B].
               ++ destruct (B Cur). congruence.
               ++ specialize (B Max). congruence.
            -- pose proof Mem.nextblock_noaccess mi b ofs0 Max n.
               congruence.
          * replace ((Mem.mem_access mi') !! b ofs0 Max) with (Some Freeable). now constructor.
            symmetry.
            destruct (D b ofs0) as [A B].
            destruct (valid_block_dec mi b) as [v|n].
            -- autospec B.
               destruct B as [B|B].
               ++ destruct (B Cur); congruence.
               ++ specialize (B Max). congruence.
            -- pose proof Mem.nextblock_noaccess mi b ofs0 Max n.
               congruence.
        
        + (* Max = writable : must be writable after, because unchanged using "decay" *)
          assert (Same: (Mem.mem_access m) !! b ofs0 Max = (Mem.mem_access mi) !! b ofs0 Max) by congruence.
          revert step Emi Same.
          generalize (m_dry jmi').
          generalize (juicyRestrict _ _ (acc_coh (thread_mem_compatible (mem_compatible_forget compat) cnti))).
          clear.
          intros m0 m1 D Emi Same.
          match goal with |- _ ?a ?b => cut (a = b) end.
          { intros ->; apply po_refl. }
          specialize (D b ofs0).
          destruct D as [A B].
          destruct (valid_block_dec mi b) as [v|n].
          * autospec B.
            destruct B as [B|B].
            -- destruct (B Max); congruence.
            -- specialize (B Max). congruence.
          * pose proof Mem.nextblock_noaccess m b ofs0 Max n.
            congruence.
        
        + (* Max = Readable : impossible because Max >= Writable  *)
          autospec LW.
          autospec LW.
          rewrite Emax in LW.
          inversion LW.
        
        + (* Max = Nonempty : impossible because Max >= Writable  *)
          autospec LW.
          autospec LW.
          rewrite Emax in LW.
          inversion LW.
        
        + (* Max = none : impossible because Max >= Writable  *)
          autospec LW.
          autospec LW.
          rewrite Emax in LW.
          inversion LW.
      
      - (* juicyLocks_in_lockSet *)
        eapply same_locks_juicyLocks_in_lockSet.
        + eapply resource_decay_same_locks.
          apply RD.
        + simpl.
          clear -LJ.
          intros loc sh psh P z H.
          unfold tp'.
          rewrite lset_age_tp_to.
          rewrite isSome_find_map.
          eapply LJ; eauto.
        
      - (* lockSet_in_juicyLocks *)
        eapply resource_decay_lockSet_in_juicyLocks.
        + eassumption.
        + simpl.
          apply lockSet_Writable_lockSet_block_bound.
          clear -LW.
          intros b ofs.
          unfold tp'; rewrite lset_age_tp_to.
          rewrite isSome_find_map.
          apply LW.
        
        + clear -JL.
          unfold tp'.
          intros addr; simpl.
          unfold tp'; rewrite lset_age_tp_to.
          rewrite isSome_find_map.
          apply JL.
    }
    (* end of proving mem_compatible_with *)
    
    (* Now that mem_compatible_with is established, we move on to the
       invariant. Two important parts:

       1) lock coherence is maintained, because the thread step could
          not affect locks in either kinds of memories
       
       2) safety is maintained: for thread #i (who just took a step),
          safety of the new state follows from safety of the old
          state. For thread #j != #i, we need to prove that the new
          memory is [juicy_mem_equiv] to the old one, in the sense
          that wherever [Cur] was readable the values have not
          changed.
    *)
    
    apply state_invariant_c with (PHI := Phi'') (mcompat := compat''); auto.
    - (* matchfunspecs *)
      eapply resource_decay_matchfunspec; eauto.
    
    - (* lock coherence: own rmap has changed, but we prove it did not affect locks *)
      unfold tp''; simpl.
      unfold tp'; simpl.
      apply lock_sparsity_age_to. auto.
    
    - (* lock coherence: own rmap has changed, but we prove it did not affect locks *)
      unfold lock_coherence', tp''; simpl lset.

      (* replacing level (m_phi jmi') with level Phi' ... *)
      assert (level (m_phi jmi') = level Phi'') by congruence.
      cut (lock_coherence
            (AMap.map (option_map (age_to (level Phi''))) (lset tp)) Phi''
            (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget compat'')))).
      { intros A; exact_eq A.
        f_equal. unfold tp'; rewrite lset_age_tp_to.
        f_equal. f_equal. f_equal. rewrite level_juice_level_phi; auto. }
      (* done replacing *)
      
      (* operations on the lset: nothing happened *)
      apply (resource_decay_lock_coherence RD).
      { auto. }
      { intros. eapply join_all_level_lset; eauto. }
      
      clear -lock_coh lock_bound stepi.
      
      (* what's important: lock values couldn't change during a corestep *)
      assert
        (SA' :
           forall loc,
             AMap.find (elt:=option rmap) loc (lset tp) <> None ->
             load_at (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget compat))) loc =
             load_at (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget compat''))) loc).
      {
        destruct stepi as [step RD].
        unfold cl_core_sem in *.
        simpl in step.
        pose proof cl_step_decay _ _ _ _ _ step as D.
        intros (b, ofs) islock.
        pose proof juicyRestrictMax (acc_coh (thread_mem_compatible (mem_compatible_forget compat) cnti)) (b, ofs).
        pose proof juicyRestrictContents (acc_coh (thread_mem_compatible (mem_compatible_forget compat) cnti)) (b, ofs).
        unfold load_at in *; simpl.
        set (W  := mem_compatible_locks_ltwritable (mem_compatible_forget compat )).
        set (W' := mem_compatible_locks_ltwritable (mem_compatible_forget compat'')).
        pose proof restrPermMap_Cur W as RW.
        pose proof restrPermMap_Cur W' as RW'.
        pose proof restrPermMap_contents W as CW.
        pose proof restrPermMap_contents W' as CW'.
        Transparent Mem.load.
        unfold Mem.load in *.
        destruct (Mem.valid_access_dec (restrPermMap W) Mint32 b ofs Readable) as [r|n]; swap 1 2.
        
        { (* can't be not readable *)
          destruct n.
          apply Mem.valid_access_implies with Writable.
          - eapply lset_valid_access; eauto.
          - constructor.
        }
        
        destruct (Mem.valid_access_dec (restrPermMap W') Mint32 b ofs Readable) as [r'|n']; swap 1 2.
        { (* can't be not readable *)
          destruct n'.
          split.
          - apply Mem.range_perm_implies with Writable.
            + eapply lset_range_perm; eauto.
              unfold tp''; simpl.
              unfold tp'; rewrite lset_age_tp_to.
              rewrite AMap_find_map_option_map.
              destruct (AMap.find (elt:=option rmap) (b, ofs) (lset tp)).
              * discriminate.
              * tauto.
            + constructor.
          - (* basic alignment *)
            eapply lock_coherence_align; eauto.
        }
        
        f_equal.
        f_equal.
        apply Mem.getN_exten.
        intros ofs0 interval.
        eapply equal_f with (b, ofs0) in CW.
        eapply equal_f with (b, ofs0) in CW'.
        unfold contents_at in CW, CW'.
        simpl fst in CW, CW'.
        simpl snd in CW, CW'.
        rewrite CW, CW'.
        pose proof cl_step_unchanged_on _ _ _ _ _ b ofs0 step as REW.
        rewrite <- REW.
        - reflexivity.
        - unfold Mem.valid_block in *.
          simpl.
          apply (lock_bound (b, ofs)).
          destruct (AMap.find (elt:=option rmap) (b, ofs) (lset tp)). reflexivity. tauto.
        - pose proof juicyRestrictCurEq (acc_coh (thread_mem_compatible (mem_compatible_forget compat) cnti)) (b, ofs0) as h.
          unfold access_at in *.
          simpl fst in h; simpl snd in h.
          unfold Mem.perm in *.
          rewrite h.
          cut (Mem.perm_order'' (Some Nonempty) (perm_of_res (getThreadR _ _ cnti @ (b, ofs0)))).
          { destruct (perm_of_res (getThreadR _ _ cnti @ (b, ofs0))); intros A B.
            all: inversion A; subst; inversion B; subst. }
          apply po_trans with (perm_of_res (Phi @ (b, ofs0))); swap 1 2.
          + eapply po_join_sub.
            apply resource_at_join_sub.
            eapply compatible_threadRes_sub.
            apply compat.
          + clear -lock_coh islock interval.
            (* todo make lemma out of this *)
            specialize (lock_coh (b, ofs)).
            assert (lk : exists sh R, (LK_at R sh (b, ofs)) Phi). {
              destruct (AMap.find (elt:=option rmap) (b, ofs) (lset tp)) as [[|]|].
              - destruct lock_coh as [_ (? & ? & ? & ?)]; eauto.
              - destruct lock_coh as [_ (? & ? & ?)]; eauto.
              - tauto.
            }
            destruct lk as (R & sh & lk).
            specialize (lk (b, ofs0)).
            simpl in lk.
            assert (adr_range (b, ofs) lock_size (b, ofs0))
              by apply interval_adr_range, interval.
            if_tac in lk; [|tauto].
            if_tac in lk.
            * destruct lk as [pp ->]. simpl. constructor.
            * destruct lk as [pp ->]. simpl. constructor.
      }
      (* end of proof of: lock values couldn't change during a corestep *)
      
      unfold lock_coherence' in *.
      intros loc; specialize (lock_coh loc). specialize (SA' loc).
      destruct (AMap.find (elt:=option rmap) loc (lset tp)) as [[lockphi|]|].
      + destruct lock_coh as [COH ?]; split; [ | easy ].
        rewrite <-COH; rewrite SA'; auto.
        congruence.
      + destruct lock_coh as [COH ?]; split; [ | easy ].
        rewrite <-COH; rewrite SA'; auto.
        congruence.
      + easy.
    
    - (* safety *)
      intros j cntj ora.
      destruct (eq_dec i j) as [e|n0].
      + subst j.
        replace (getThreadC _ _ cntj) with (Krun ci').
        * specialize (safei' ora).
          exact_eq safei'.
          f_equal.
          unfold jm_ in *.
          {
            apply juicy_mem_ext.
            - unfold personal_mem in *.
              simpl.
              match goal with |- _ = _ ?c => set (coh := c) end.
              apply mem_ext.
              
              + reflexivity.
              
              + rewrite juicyRestrictCur_unchanged.
                * reflexivity.
                * intros.
                  unfold "oo".
                  rewrite eqtype_refl.
                  unfold tp'; simpl.
                  unfold access_at in *.
                  destruct jmi'; simpl.
                  eauto.
              
              + reflexivity.
            
            - simpl.
              unfold "oo".
              rewrite eqtype_refl.
              auto.
          }
          
        * (* assert (REW: tp'' = (age_tp_to (level (m_phi jmi')) tp')) by reflexivity. *)
          (* clearbody tp''. *)
          subst tp''.
          rewrite gssThreadCode. auto.
      
      + unfold tp'' at 1.
        unfold tp' at 1.
        unshelve erewrite gsoThreadCode; auto.
        
        clear Ecompat Hext' Hext'' J'' Jext Jext' Hext RD J' LW LJ JL.
        
        (** * Bring other thread #j's memory up to current #i's level *)
        assert (cntj' : containsThread tp j). {
          unfold tp'', tp' in cntj.
          apply cntUpdate' in cntj.
          rewrite <-cnt_age in cntj.
          apply cntj.
        }
        pose (jmj' := age_to (level (m_phi jmi')) (@jm_ tp m Phi j cntj' compat)).
        
        (** * #j's memory is equivalent to the one it will be started in *)
        assert (E : juicy_mem_equiv  jmj' (jm_ cntj compat'')). {
          split.
          - unfold jmj'.
            rewrite m_dry_age_to.
            unfold jm_.
            unfold tp'' in compat''.
            pose proof
                 jstep_preserves_mem_equiv_on_other_threads
                 m ge i j tp ci ci' jmi' n0
                 cnti cntj'
                 (thread_mem_compatible (mem_compatible_forget compat) cnti)
                 stepi
                 (thread_mem_compatible (mem_compatible_forget compat) cntj')
                 (thread_mem_compatible (mem_compatible_forget compat'') (cnt_age' cntj'))
              as H.
            exact_eq H.
            repeat f_equal.
            
            unfold tp'' in *.
            apply personal_mem_rewrite.
            unfold tp' in *.
            f_equal.
            apply proof_irr.
          
          - unfold jmj'.
            unfold jm_ in *.
            rewrite m_phi_age_to.
            change (age_to (level (m_phi jmi')) (getThreadR _ _ cntj')
                    = getThreadR _ _ cntj).
            unfold tp'', tp'.
            unshelve erewrite gsoThreadRes; auto.
            unshelve erewrite getThreadR_age. auto.
            reflexivity.
        }
        
        unshelve erewrite <-gtc_age; auto.
        pose proof safety _ cntj' ora as safej.
        
        (* factoring all Krun / Kblocked / Kresume / Kinit cases in this one assert *)
        assert (forall c, jsafeN Jspec ge (S n) ora c (jm_ cntj' compat) ->
                     jsafeN Jspec ge n ora c (jm_ cntj compat'')) as othersafe.
        {
          intros c s.
          apply jsafeN_downward in s.
          apply jsafeN_age_to with (l := n) in s; auto.
          refine (jsafeN_mem_equiv _ _ s); auto.
          exact_eq E; f_equal.
          unfold jmj'; f_equal. auto.
        }
  
        destruct (@getThreadC j tp cntj') as [c | c | c v | v v0]; solve [auto].
    
    - (* wellformedness *)
      intros j cntj.
      unfold tp'', tp'.
      destruct (eq_dec i j) as [ <- | ij].
      + unshelve erewrite gssThreadCode; auto.
      + unshelve erewrite gsoThreadCode; auto.
        specialize (wellformed j). clear -wellformed.
        assert_specialize wellformed by (destruct tp; auto).
        unshelve erewrite <-gtc_age; auto.
    
    - (* uniqueness *)
      intros notalone j cntj q Ecj.
      hnf in unique.
      assert_specialize unique by (destruct tp; apply notalone).
      specialize (unique j).
      destruct (eq_dec i j) as [ <- | ij].
      + apply unique with (cnti := cnti) (q := ci); eauto.
      + assert_specialize unique by (destruct tp; auto).
        apply unique with (q := q); eauto.
        exact_eq Ecj. f_equal.
        unfold tp'',  tp'.
        unshelve erewrite gsoThreadCode; auto.
        unshelve erewrite <-gtc_age; auto.
  Qed.
  
  Lemma restrPermMap_mem_contents p' m (Hlt: permMapLt p' (getMaxPerm m)): 
    Mem.mem_contents (restrPermMap Hlt) = Mem.mem_contents m.
  Proof.
    reflexivity.
  Qed.
  
  Ltac jmstep_inv :=
    match goal with
    | H : JuicyMachine.start_thread _ _ _ |- _ => inversion H
    | H : JuicyMachine.resume_thread _ _  |- _ => inversion H
    | H : threadStep _ _ _ _ _ _          |- _ => inversion H
    | H : JuicyMachine.suspend_thread _ _ |- _ => inversion H
    | H : syncStep _ _ _ _ _ _            |- _ => inversion H
    | H : threadHalted _                  |- _ => inversion H
    | H : JuicyMachine.schedfail _        |- _ => inversion H
    end; try subst.
  
  Ltac getThread_inv :=
    match goal with
    | [ H : @getThreadC ?i _ _ = _ ,
            H2 : @getThreadC ?i _ _ = _ |- _ ] =>
      pose proof (getThreadC_fun _ _ _ _ _ _ H H2)
    | [ H : @getThreadR ?i _ _ = _ ,
            H2 : @getThreadR ?i _ _ = _ |- _ ] =>
      pose proof (getThreadR_fun _ _ _ _ _ _ H H2)
    end.
  
  Lemma Ejuicy_sem : juicy_sem = juicy_core_sem cl_core_sem.
  Proof.
    unfold juicy_sem; simpl.
    f_equal.
    unfold SEM.Sem, SEM.CLN_evsem.
    rewrite SEM.CLN_msem.
    reflexivity.
  Qed.
  
  Lemma preservation_acquire
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
  (Htid : ssrnat.leq (S i) (pos.n (num_threads tp)) = true)
  (HschedN : SCH.schedPeek (i :: sch) = Some i)
  (m_ := m' : Memory.mem)
  (El : Logic.True -> level (getThreadR i tp Htid) - 1 = n)
  (compat_aged : mem_compatible_with (age_tp_to n tp) m (age_to n Phi))
  (c : code)
  (b : block)
  (ofs : int)
  (d_phi : rmap)
  (psh : pshare)
  (phi' : LocksAndResources.res)
  (Hcompatible : mem_compatible tp m)
  (sh : Share.t)
  (R : pred rmap)
  (Hinv : invariant tp)
  (Hthread : getThreadC i tp Htid = Kblocked c)
  (Hat_external : at_external SEM.Sem c = Some (LOCK, ef_sig LOCK, Vptr b ofs :: nil))
  (His_unlocked : lockRes tp (b, Int.intval ofs) = SSome d_phi)
  (Hload : load Mint32 (restrPermMap (mem_compatible_locks_ltwritable Hcompatible)) b (Int.intval ofs) =
          Some (Vint Int.one))
  (Hstore : store Mint32 (restrPermMap (mem_compatible_locks_ltwritable Hcompatible)) b 
             (Int.intval ofs) (Vint Int.zero) = Some m')
  (HJcanwrite : getThreadR i tp Htid @ (b, Int.intval ofs) = YES sh psh (LK LKSIZE) (pack_res_inv R))
  (Hadd_lock_res : join (getThreadR i tp Htid) d_phi phi')
  (jmstep : @JuicyMachine.machine_step ge (i :: sch) nil tp m sch nil
             (age_tp_to (level (getThreadR i tp Htid) - 1)
                (updLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs) None)) m')
  (tp_ := age_tp_to (level (getThreadR i tp Htid) - 1)
           (updLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs) None) : thread_pool)
  (compat_ := mem_compatible_with tp_ m_ (age_to n Phi) : Prop)
  (Htstep : syncStep ge Htid Hcmpt
             (age_tp_to (level (getThreadR i tp Htid) - 1)
                (updLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs) None)) m'
             (Events.acquire (b, Int.intval ofs) None)) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m_, ge, (sch, tp_)).
  
  Proof.
    autospec El.
    (* we prove [mem_compatible_with] BEFORE aging, as it it slightly
    easier, proving [mem_compatible_with] after aging is a simple
    application of the lemma [mem_compatible_with_age] *)
    pose (tp__ := updLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs) None).
    assert (compat'' : mem_compatible_with tp__ m_ Phi). {
      subst compat_ tp__ m_.
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
        rewrite gRemLockSetRes with (cnti := Htid) in J. clear pr.
        revert Hadd_lock_res J.
        generalize (@getThreadR _ _ Htid) d_phi phi'.
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
        eapply mem_cohere'_store with
        (tp := tp)
          (Hcmpt := mem_compatible_forget compat)
          (i := Int.zero).
        + cleanup.
          rewrite His_unlocked. simpl. congruence.
        + exact_eq Hstore.
          f_equal.
          f_equal.
          apply restrPermMap_ext.
          unfold lockSet in *.
          intros b0.
          reflexivity.
        + auto.
          
      - (* lockSet_Writable *)
        clear -compat Hstore His_unlocked.
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
    
    assert (compat' : compat_). {
      unfold compat_, tp_.
      rewrite El.
      apply mem_compatible_with_age.
      auto.
    }
    
    apply state_invariant_c with (mcompat := compat').
    + (* level *)
      apply level_age_to. omega.
      
    + (* matchfunspec *)
      revert gam. clear.
      apply matchfunspec_age_to.
      
    + (* lock sparsity *)
      unfold tp_ in *.
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
            cut (exists sh0 R0, (LK_at R0 sh0 (b, Int.intval ofs)) Phi).
            { intros (sh0 & R0 & AP). exists sh0, R0. apply age_to_pred, AP. }
            cleanup.
            rewrite His_unlocked in lock_coh.
            destruct lock_coh as (H & ? & ? & lk & _).
            eauto.
            
          - (* in dry : it is 0 *)
            unfold m_ in *; clear m_.
            unfold compat_ in *; clear compat_.
            unfold load_at.
            clear (* lock_coh *) Htstep Hload.
            
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
              * unfold tp_.
                rewrite LockRes_age_content1.
                rewrite JTP.gssLockRes. simpl. congruence.
              * congruence.
        }
        
      * (* not the current lock *)
        rewrite El.
        destruct (AMap.find (elt:=option rmap) loc (lset tp)) as [o|] eqn:Eo; swap 1 2.
        {
          simpl.
          clear -lock_coh.
          rewrite isLK_age_to, isCT_age_to. auto.
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
                    ZMap.get (ofs' + z)%Z (Mem.mem_contents m_) !! b').
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
              apply OUT. omega.
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
            unfold tp_.
            rewrite lockSet_age_to.
            rewrite <-lockSet_updLockSet.
            match goal with |- _ ?a _ => cut (a = Some Writable) end.
            { intros ->. constructor. }
            
            destruct SPA as [bOUT | [<- ofsOUT]].
            + rewrite gsoLockSet_2; auto.
              eapply lockSet_spec_2.
              * hnf; simpl. eauto.
              * cleanup. rewrite Eo. reflexivity.
            + rewrite gsoLockSet_1; auto.
              * eapply lockSet_spec_2.
                -- hnf; simpl. eauto.
                -- cleanup. rewrite Eo. reflexivity.
              * unfold far in *.
                simpl in *.
                zify.
                omega.
        }
        destruct o; destruct lock_coh as (Load & sh' & R' & lks); split.
        -- now intuition.
        -- exists sh', R'.
           destruct lks as (lk, sat); split.
           ++ revert lk.
              apply age_to_pred.
           ++ destruct sat as [sat|sat].
              ** left; revert sat.
                 unfold age_to in *.
                 rewrite age_by_age_by.
                 apply age_by_age_by_pred.
                 omega.
              ** congruence.
        -- now intuition.
        -- exists sh', R'.
           revert lks.
           apply age_to_pred.
           
    + (* safety *)
      intros j lj ora.
      specialize (safety j lj ora).
      unfold tp_.
      unshelve erewrite <-gtc_age. auto.
      unshelve erewrite gLockSetCode; auto.
      destruct (eq_dec i j).
      * {
          (* use the "well formed" property to derive that this is
              an external call, and derive safety from this.  But the
              level has to be decreased, here. *)
          subst j.
          rewrite gssThreadCode.
          replace lj with Htid in safety by apply proof_irr.
          rewrite Hthread in safety.
          specialize (wellformed i Htid).
          rewrite Hthread in wellformed.
          intros c' Ec'.
          inversion safety as [ | ?????? step | ???????? ae Pre Post Safe | ????? Ha]; swap 2 3.
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
            (ret := Some (Vint Int.zero))
              (m' := jm_ lj compat')
              (z' := ora) (n' := n) as (c'' & Ec'' & Safe').
            
            + auto.
              
            + (* proving Hrel *)
              hnf.
              split; [ | split].
              * rewrite level_jm_.
                rewrite level_age_to; auto. omega.
              * do 2 rewrite level_jm_.
                rewrite level_age_to; auto. cleanup. omega.
                omega.
              * eapply pures_same_eq_l.
                apply pures_same_sym, pures_same_jm_.
                eapply pures_same_eq_r.
                2:apply pures_same_sym, pures_same_jm_.
                rewrite level_m_phi.
                rewrite level_jm_.
                auto.
                apply pures_age_eq. omega.
                
            + (* we must satisfy the post condition *)
              assert (e = LOCK).
              { rewrite <-Ejuicy_sem in *.
                unfold juicy_sem in *.
                simpl in ae.
                congruence. }
              subst e.
              revert x Pre Post.
              funspec_destruct "acquire"; swap 1 2.
              { exfalso. unfold ef_id in *. congruence. }
              intros x Pre Post.
              destruct Pre as (phi0 & phi1 & j & Pre).
              destruct (join_assoc (join_comm j) Hadd_lock_res) as (phi0' & jphi0' & jframe).
              exists (age_to n phi0'), (age_to n phi1).
              rewrite m_phi_jm_ in *.
              split.
              * unfold tp_ in *.
                REWR.
                cleanup.
                rewrite getThread_level with (Phi := Phi). 2:apply compat.
                cleanup.
                rewrite lev.
                simpl minus. rewrite <-minus_n_O.
                apply age_to_join.
                apply join_comm in jframe.
                exact_eq jframe. f_equal.
                REWR.
                REWR.
              * destruct x as (phix, ((vx, shx), Rx)); simpl (fst _) in *; simpl (snd _) in *.
                simpl.
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
                     apply join_sub_trans with (getThreadR _ _ Htid). exists phi1. auto.
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
        apply jsafeN_age_to with (l := n) in Safe; auto. 2:now apply Jspec'_hered.
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
              ** unfold m_ in *.
                 unfold tp_ in *.
                 REWR in pr'.
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
                     clear safety Htstep jmstep Hload Hstore tp_ compat_ compat' lj cmpt' pr'.
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
              unfold m_.
              apply m_dry_personal_mem_eq.
              intros loc.
              unfold tp_.
              REWR.
              REWR.
              REWR.                  
              REWR.
        -- REWR.
           rewrite m_phi_jm_.
           rewrite m_phi_jm_.
           unfold tp_.
           REWR.
           REWR.
           REWR.
           f_equal.
           replace (level (getThreadR i tp Htid)) with (level Phi). omega.
           symmetry; apply join_sub_level, compatible_threadRes_sub, compat.
           
    + (* well_formedness *)
      intros j lj.
      unfold tp_.
      specialize (wellformed j lj).
      unshelve erewrite <-gtc_age. auto.
      unshelve erewrite gLockSetCode; auto.
      destruct (eq_dec i j).
      * subst j.
        rewrite gssThreadCode.
        replace lj with Htid in wellformed by apply proof_irr.
        rewrite Hthread in wellformed.
        auto.
      * unshelve erewrite gsoThreadCode; auto.
        
    + (* uniqueness *)
      apply no_Krun_unique_Krun.
      unfold tp_.
      rewrite no_Krun_age_tp_to.
      apply no_Krun_updLockSet.
      apply no_Krun_stable. congruence.
      eapply unique_Krun_no_Krun. eassumption.
      instantiate (1 := Htid). rewrite Hthread.
      congruence.
  Qed.
  
  Lemma preservation_release
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
  (Htid : ssrnat.leq (S i) (pos.n (num_threads tp)) = true)
  (HschedN : SCH.schedPeek (i :: sch) = Some i)
  (m_ := m' : Memory.mem)
  (El : Logic.True -> level (getThreadR i tp Htid) - 1 = n)
  (compat_aged : mem_compatible_with (age_tp_to n tp) m (age_to n Phi))
  (c : code)
  (b : block)
  (ofs : int)
  (psh : pshare)
  (d_phi : rmap)
  (R : pred rmap)
  (phi' : rmap)
  (Hcompatible : mem_compatible tp m)
  (sh : Share.t)
  (Hinv : invariant tp)
  (Hthread : getThreadC i tp Htid = Kblocked c)
  (Hat_external : at_external SEM.Sem c = Some (UNLOCK, ef_sig UNLOCK, Vptr b ofs :: nil))
  (His_locked : lockRes tp (b, Int.intval ofs) = SNone)
  (Hsat_lock_inv : R (age_by 1 d_phi))
  (Hload : load Mint32 (restrPermMap (mem_compatible_locks_ltwritable Hcompatible)) b (Int.intval ofs) =
          Some (Vint Int.zero))
  (Hstore : store Mint32 (restrPermMap (mem_compatible_locks_ltwritable Hcompatible)) b
             (Int.intval ofs) (Vint Int.one) = Some m')
  (HJcanwrite : getThreadR i tp Htid @ (b, Int.intval ofs) = YES sh psh (LK LKSIZE) (pack_res_inv R))
  (Hrem_lock_res : join d_phi phi' (getThreadR i tp Htid))
  (jmstep : @JuicyMachine.machine_step ge (i :: sch) nil tp m sch nil
             (age_tp_to (level (getThreadR i tp Htid) - 1)
                (updLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs) (Some d_phi))) m')
  (tp_ := age_tp_to (level (getThreadR i tp Htid) - 1)
           (updLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs) (Some d_phi))
      : thread_pool)
  (compat_ := mem_compatible_with tp_ m_ (age_to n Phi) : Prop)
  (Htstep : syncStep ge Htid Hcmpt
             (age_tp_to (level (getThreadR i tp Htid) - 1)
                (updLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs) (Some d_phi))) m'
             (Events.release (b, Int.intval ofs) None)) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m_, ge, (sch, tp_)).
  
  Proof.
    autospec El.
    cleanup.
    assert (compat' : compat_). {
      subst compat_ tp_ m_.
      cleanup.
      rewrite El.
      constructor.
      - (* joining to global map: the acquired rmap move from
            lockset to threads's maps *)
        destruct compat as [J].
        clear -J lev His_locked Hrem_lock_res.
        rewrite join_all_joinlist in *.
        rewrite maps_age_to.
        rewrite maps_updlock2. 
        rewrite maps_remLockSet_updThread.
        rewrite maps_updthread.
        erewrite <-maps_getlock2 in J; eauto.
        simpl map.
        assert (pr:containsThread (remLockSet tp (b, Int.intval ofs)) i) by auto.
        rewrite (maps_getthread i _ pr) in J.
        rewrite gRemLockSetRes with (cnti := Htid) in J. clear pr.
        revert Hrem_lock_res J.
        generalize (@getThreadR _ _ Htid) d_phi phi'.
        generalize (all_but i (maps (remLockSet tp (b, Int.intval ofs)))).
        cleanup.
        clear -lev.
        intros l c a b j h.
        pose proof @joinlist_age_to _ _ _ _ _ n _ _ h as h'.
        simpl map in h'.
        apply age_to_join_eq with (k := n) in j; auto.
        + eapply joinlist_merge; eassumption.
        + cut (level c = level Phi). omega.
          apply join_level in j. destruct j.
          eapply (joinlist_level c) in h.
          * congruence.
          * left; auto.
            
      - (* mem_cohere' *)
        destruct compat as [J MC].
        clear safety lock_coh jmstep.
        eapply mem_cohere'_store with
        (tp := age_tp_to n tp)
          (Hcmpt := mem_compatible_forget compat_aged)
          (i := Int.one).
        + cleanup.
          rewrite lset_age_tp_to.
          rewrite AMap_find_map_option_map.
          rewrite His_locked. simpl. congruence.
        + exact_eq Hstore.
          f_equal.
          f_equal.
          apply restrPermMap_ext.
          unfold lockSet in *.
          rewrite lset_age_tp_to.
          intros b0.
          rewrite (@A2PMap_option_map rmap (lset tp)).
          reflexivity.
        + auto.
          
      - (* lockSet_Writable *)
        apply lockSet_Writable_age.
        clear -compat Hstore His_locked.
        eapply lockSet_Writable_updLockSet_updThread; eauto.
        
      - (* juicyLocks_in_lockSet *)
        pose proof jloc_in_set compat as jl.
        intros loc sh1 sh1' pp z E.
        cleanup.
        apply juicyLocks_in_lockSet_age with (n := n) in jl.
        specialize (jl loc sh1 sh1' pp z E).
        simpl.
        rewrite AMap_map_add.
        rewrite AMap_find_add.
        if_tac. reflexivity.
        rewrite lset_age_tp_to in jl.
        apply jl.
        
      - (* lockSet_in_juicyLocks *)
        pose proof lset_in_juice compat as lj.
        intros loc; specialize (lj loc).
        simpl.
        rewrite AMap_map_add.
        rewrite AMap_find_add.
        rewrite AMap_find_map_option_map.
        if_tac; swap 1 2.
        + cleanup.
          rewrite isSome_option_map.
          intros is; specialize (lj is).
          destruct lj as (sh' & psh' & P & E).
          rewrite age_to_resource_at.
          rewrite E. simpl. eauto.
        + intros _. subst loc.
          assert_specialize lj. {
            cleanup.
            rewrite His_locked.
            reflexivity.
          }
          destruct lj as (sh' & psh' & P & E).
          rewrite age_to_resource_at.
          rewrite E. simpl. eauto.
    }
    
    apply state_invariant_c with (mcompat := compat').
    + (* level *)
      apply level_age_to. omega.
      
    + (* matchfunspec *)
      revert gam. clear.
      apply matchfunspec_age_to.
      
    + (* lock sparsity *)
      unfold tp_ in *.
      simpl.
      cleanup.
      eapply sparsity_same_support with (lset tp); auto.
      apply lset_same_support_sym.
      eapply lset_same_support_trans.
      * apply lset_same_support_map.
      * apply lset_same_support_sym.
        apply same_support_change_lock.
        cleanup.
        rewrite His_locked. congruence.
        
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
          - (* the rmap is unchanged (but we have to prove the SAT information) *)
            cut (exists sh0 R0,
                    (LK_at R0 sh0 (b, Int.intval ofs)) Phi /\
                    (R0 (age_by 1 (age_to (level (getThreadR i tp Htid) - 1) d_phi))
                     \/ level (age_to n Phi) = 0)
                ).
            { intros (sh0 & R0 & AP & sat). exists sh0, R0. split; auto; apply age_to_pred, AP. }
            cleanup.
            rewrite His_locked in lock_coh.
            destruct lock_coh as (Load & sh0 & R0 & lk).
            exists sh0, R0; split.
            + eauto.
            + left.
              rewrite El.
              apply predat2 in lk.
              apply predat1 in HJcanwrite.
              apply @predat_join_sub with (phi2 := Phi) in HJcanwrite.
              2:apply compatible_threadRes_sub, compat.
              pose proof predat_inj HJcanwrite lk as ER.
              replace (level (getThreadR i tp Htid)) with (level Phi) in ER.
              2:symmetry; apply join_sub_level, compatible_threadRes_sub, compat.
              cleanup.
              refine (@approx_eq_app_pred R R0 (age_by 1 (age_to n d_phi)) _ _ ER _).
              * rewrite level_age_by.
                rewrite level_age_to. omega.
                replace (level d_phi) with (level Phi). omega.
                symmetry. apply join_sub_level.
                apply join_sub_trans with (getThreadR i tp Htid).
                -- exists phi'. apply join_comm. auto.
                -- apply compatible_threadRes_sub. apply compat.
              * revert Hsat_lock_inv.
                unfold age_to.
                rewrite age_by_age_by.
                rewrite plus_comm.
                rewrite <-age_by_age_by.
                apply age_by_ind.
                destruct R; auto.
                
          - (* in dry : it is 1 *)
            unfold m_ in *; clear m_.
            unfold compat_ in *; clear compat_.
            unfold load_at.
            clear (* lock_coh *) Htstep Hload.
            
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
              * unfold tp_.
                rewrite LockRes_age_content1.
                rewrite JTP.gssLockRes. simpl. congruence.
              * congruence.
        }
        
      * (* not the current lock *)
        rewrite El.
        destruct (AMap.find (elt:=option rmap) loc (lset tp)) as [o|] eqn:Eo; swap 1 2.
        {
          simpl.
          clear -lock_coh.
          rewrite isLK_age_to, isCT_age_to. auto.
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
                    ZMap.get (ofs' + z)%Z (Mem.mem_contents m_) !! b').
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
              apply OUT. omega.
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
            unfold tp_.
            rewrite lockSet_age_to.
            rewrite <-lockSet_updLockSet.
            match goal with |- _ ?a _ => cut (a = Some Writable) end.
            { intros ->. constructor. }
            
            destruct SPA as [bOUT | [<- ofsOUT]].
            + rewrite gsoLockSet_2; auto.
              eapply lockSet_spec_2.
              * hnf; simpl. eauto.
              * cleanup. rewrite Eo. reflexivity.
            + rewrite gsoLockSet_1; auto.
              * eapply lockSet_spec_2.
                -- hnf; simpl. eauto.
                -- cleanup. rewrite Eo. reflexivity.
              * unfold far in *.
                simpl in *.
                zify.
                omega.
        }
        destruct o; destruct lock_coh as (Load & sh' & R' & lks); split.
        -- now intuition.
        -- exists sh', R'.
           destruct lks as (lk, sat); split.
           ++ revert lk.
              apply age_to_pred.
           ++ destruct sat as [sat|sat].
              ** left; revert sat.
                 unfold age_to in *.
                 rewrite age_by_age_by.
                 apply age_by_age_by_pred.
                 omega.
              ** congruence.
        -- now intuition.
        -- exists sh', R'.
           revert lks.
           apply age_to_pred.
           
    + (* safety *)
      intros j lj ora.
      specialize (safety j lj ora).
      unfold tp_.
      unshelve erewrite <-gtc_age. auto.
      unshelve erewrite gLockSetCode; auto.
      destruct (eq_dec i j).
      * {
          (* use the "well formed" property to derive that this is
              an external call, and derive safety from this.  But the
              level has to be decreased, here. *)
          subst j.
          rewrite gssThreadCode.
          replace lj with Htid in safety by apply proof_irr.
          rewrite Hthread in safety.
          specialize (wellformed i Htid).
          rewrite Hthread in wellformed.
          intros c' Ec'.
          inversion safety as [ | ?????? step | ???????? ae Pre Post Safe | ????? Ha]; swap 2 3.
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
            (ret := Some (Vint Int.zero))
              (m' := jm_ lj compat')
              (z' := ora) (n' := n) as (c'' & Ec'' & Safe').
            
            + auto.
              
            + (* proving Hrel *)
              hnf.
              split; [ | split].
              * rewrite level_jm_.
                rewrite level_age_to; auto. omega.
              * do 2 rewrite level_jm_.
                rewrite level_age_to; auto. cleanup. omega.
                omega.
              * eapply pures_same_eq_l.
                apply pures_same_sym, pures_same_jm_.
                eapply pures_same_eq_r.
                2:apply pures_same_sym, pures_same_jm_.
                rewrite level_m_phi.
                rewrite level_jm_.
                auto.
                apply pures_age_eq. omega.
                
            + (* we must satisfy the post condition *)
              assert (e = UNLOCK).
              { rewrite <-Ejuicy_sem in *.
                unfold juicy_sem in *.
                simpl in ae.
                congruence. }
              subst e.
              revert x Pre Post.
              funspec_destruct "acquire".
              { exfalso. unfold ef_id in *. injection Heq_name as E.
                apply ext_link_inj in E. congruence. }
              funspec_destruct "release"; swap 1 2.
              { exfalso. unfold ef_id in *. congruence. }
              intros x Pre Post.
              destruct Pre as (phi0 & phi1 & j & Pre).
              rewrite m_phi_jm_ in j.
              destruct x as (phix, ((vx, shx), Rx)); simpl (fst _) in *; simpl (snd _) in *.
              cbv iota beta in Pre.
              cbv iota beta.
              destruct Pre as [[[A [Precise [Positive _]]] [C D]] E].
              destruct D as (phi0' & phi0d & jphi0 & Hlockinv & Hsat).
              unfold fold_right in Hsat.
              rewrite seplog.sepcon_emp in Hsat.
              
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
              
              assert (join_sub (getThreadR i tp Htid) Phi) by apply compatible_threadRes_sub, compat.
              
              assert (Edphi : age_to n phi0d = age_to n d_phi). {
                apply predat4 in Hlockinv.
                
                assert (join_sub phi0' (getThreadR i tp Htid)). {
                  apply join_sub_trans with phi0.
                  - eexists; eapply join_comm; eauto.
                  - eexists; eapply join_comm; eauto.
                }
                apply @predat_join_sub with (phi2 := Phi) in Hlockinv; swap 1 2. {
                  apply join_sub_trans with (getThreadR i tp Htid); auto.
                }
                replace (level phi0') with (level Phi) in Hlockinv by join_level_tac.
                rename R into RRRRRRRRRRR.
                rename Rx into RRRRRRRRRRRx.
                apply predat1 in HJcanwrite.
                replace (level (getThreadR i tp Htid)) with (level Phi) in HJcanwrite by join_level_tac.
                apply @predat_join_sub with (phi2 := Phi) in HJcanwrite; [ | now auto].                    unfold Int.unsigned in *.
                pose proof predat_inj Hlockinv HJcanwrite as ER.
                apply precise_approx with (n := S n) in Precise.
                apply Precise with (age_to n (getThreadR i tp Htid)).
                - split.
                  + rewrite level_age_to. omega.
                    replace (level phi0d) with (level Phi) by join_level_tac. omega.
                  + revert Hsat.
                    apply pred_hered.
                    apply age_to_1.
                    exact_eq lev. f_equal. join_level_tac.
                - split.
                  + rewrite level_age_to. auto with *.
                    replace (level d_phi) with (level Phi) by join_level_tac.
                    rewrite lev; auto with *.
                  + cut (app_pred (approx (level Phi) (Interp RRRRRRRRRRRx)) (age_to n d_phi)).
                    * intros []. auto.
                    * rewrite ER. split.
                      -- rewrite level_age_to. rewrite lev; auto with *.
                         replace (level d_phi) with (level Phi) by join_level_tac.
                         rewrite lev; auto with *.
                      -- exact_eq Hsat_lock_inv. f_equal. unfold age_to; f_equal.
                         replace (level d_phi) with (level Phi) by join_level_tac.
                         omega.
                - apply age_to_join_sub.
                  apply join_sub_trans with phi0.
                  + exists phi0'. apply join_comm; auto.
                  + exists phi1. apply join_comm; auto.
                - apply age_to_join_sub.
                  exists phi'. auto.
              }
              pose proof (age_to_join n _ _ _ j) as j'.
              pose proof (age_to_join n _ _ _ jphi0) as jphi0'.
              rewrite Edphi in jphi0'.
              destruct (join_assoc (join_comm jphi0') j') as (phi'_ & small & big).
              assert (phi'_ = age_to n phi'). {
                apply age_to_join with (k := n) in Hrem_lock_res.
                pose proof join_canc (join_comm Hrem_lock_res) (join_comm big).
                auto.
              }
              subst phi'_.
              
              (* destruct (join_assoc (join_comm j) Hrem_lock_res) as (phi0' & jphi0' & jframe). *)
              exists (age_to n phi0'), (age_to n phi1).
              
              rewrite m_phi_jm_ in *.
              split.
              * unfold tp_ in *.
                REWR.
                cleanup.
                rewrite getThread_level with (Phi := Phi). 2:apply compat.
                cleanup.
                rewrite lev.
                simpl minus. rewrite <-minus_n_O.
                exact_eq small. f_equal.
                REWR.
                REWR.
              * split. 2:eapply necR_trans; [ | apply  age_to_necR ]; auto.
                split. now auto.
                split. now auto.
                unfold canon.SEPx in *.
                clear Post. simpl in *.
                rewrite seplog.sepcon_emp in *.
                revert Hlockinv.
                apply pred_hered.
                apply age_to_1.
                exact_eq lev. f_equal. join_level_tac.
                
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
        apply jsafeN_age_to with (l := n) in Safe; auto. 2:now apply Jspec'_hered.
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
              ** unfold m_ in *.
                 unfold tp_ in *.
                 REWR in pr'.
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
                     clear safety Htstep jmstep Hload Hstore tp_ compat_ compat' lj cmpt' pr'.
                     specialize (lock_coh (b, Int.intval ofs)).
                     cleanup.
                     rewrite His_locked in lock_coh.
                     destruct lock_coh as (_ & sh' & R' & lk).
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
              unfold m_.
              apply m_dry_personal_mem_eq.
              intros loc.
              unfold tp_.
              REWR.
              REWR.
              REWR.                  
              REWR.
        -- REWR.
           rewrite m_phi_jm_.
           rewrite m_phi_jm_.
           unfold tp_.
           REWR.
           REWR.
           REWR.
           f_equal.
           replace (level (getThreadR i tp Htid)) with (level Phi). omega.
           symmetry; apply join_sub_level, compatible_threadRes_sub, compat.
           
    + (* well_formedness *)
      intros j lj.
      unfold tp_.
      specialize (wellformed j lj).
      unshelve erewrite <-gtc_age. auto.
      unshelve erewrite gLockSetCode; auto.
      destruct (eq_dec i j).
      * subst j.
        rewrite gssThreadCode.
        replace lj with Htid in wellformed by apply proof_irr.
        rewrite Hthread in wellformed.
        auto.
      * unshelve erewrite gsoThreadCode; auto.
        
    + (* uniqueness *)
      apply no_Krun_unique_Krun.
      unfold tp_.
      rewrite no_Krun_age_tp_to.
      apply no_Krun_updLockSet.
      apply no_Krun_stable. congruence.
      eapply unique_Krun_no_Krun. eassumption.
      instantiate (1 := Htid). rewrite Hthread.
      congruence.
  Qed.
  
  Lemma preservation_spawn
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
  (HschedN : SCH.schedPeek (i :: sch) = Some i)
  (m_ := m' : Memory.mem)
  (El : Logic.True -> level (getThreadR i tp Htid) - 1 = n)
  (c c_new : code)
  (arg : val)
  (d_phi phi' : rmap)
  (b : block)
  (ofs : int)
  (P Q : pred rmap)
  (Hcompatible : mem_compatible tp m')
  (p : rmaps.listprod (JMem.AType :: nil) -> pred rmap)
  (Hinv : invariant tp)
  (Hthread : getThreadC i tp Htid = Kblocked c)
  (Hget_fun_spec : JMem.get_fun_spec p = Some (P, Q))
  (Hsat_fun_spec : P d_phi)
  (Halmost_empty : almost_empty d_phi)
  (INV : state_invariant Jspec' Gamma (S n) (m', ge, (i :: sch, tp)))
  (compat : mem_compatible_with tp m' Phi)
  (lock_coh : lock_coherence' tp Phi m' compat)
  (safety : threads_safety Jspec' m' ge tp Phi compat (S n))
  (Hcmpt : mem_compatible tp m')
  (compat_aged : mem_compatible_with (age_tp_to n tp) m' (age_to n Phi))
  (Hget_fun_spec' : JMem.get_fun_spec'
                     (personal_mem m' (getThreadR i tp Htid) (thread_mem_compatible Hcompatible Htid))
                     (b, Int.intval ofs) arg =
                   Some (existT (fun A : list Type => rmaps.listprod A -> pred rmap) (JMem.AType :: nil) p))
  (Hrem_fun_res : join d_phi phi'
                   (m_phi (personal_mem m' (getThreadR i tp Htid) (thread_mem_compatible Hcompatible Htid))))
  (Hat_external : at_external SEM.Sem c = Some (CREATE, ef_sig CREATE, Vptr b ofs :: arg :: nil))
  (Hinitial : initial_core SEM.Sem ge (Vptr b ofs) (arg :: nil) = Some c_new)
  (tp_ := addThread (updThread i tp Htid (Kresume c Vundef) phi') (Vptr b ofs) arg d_phi : thread_pool)
  (compat_ := mem_compatible_with tp_ m_ (age_to n Phi) : Prop)
  (jmstep : @JuicyMachine.machine_step ge (i :: sch) nil tp m' sch nil
             (addThread (updThread i tp Htid (Kresume c Vundef) phi') (Vptr b ofs) arg d_phi) m')
  (Htstep : syncStep ge Htid Hcmpt
             (addThread (updThread i tp Htid (Kresume c Vundef) phi') (Vptr b ofs) arg d_phi) m'
             (Events.spawn (b, Int.intval ofs))) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m_, ge, (sch, tp_)).
  
  Proof.
  Admitted.
  
  Lemma preservation_makelock
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
  (sh : Share.t)
  (Hinv : invariant tp)
  (Hthread : getThreadC i tp Htid = Kblocked c)
  (Hat_external : at_external SEM.Sem c = Some (MKLOCK, ef_sig MKLOCK, Vptr b ofs :: nil))
  (* (Hright_juice : m = m_dry jm) *)
  (Hpersonal_perm : personal_mem m (getThreadR i tp Htid) (thread_mem_compatible Hcompatible Htid) = jm)
  (Hpersonal_juice : getThreadR i tp Htid = m_phi jm)
  (Hstore : store Mint32 (m_dry jm) b (Int.intval ofs) (Vint Int.zero) = Some m')
  (Hct : forall ofs' : Z,
        (Int.intval ofs <= ofs' < Int.intval ofs + LKSIZE)%Z ->
        exists (val : memval),
          m_phi jm @ (b, ofs') = YES sh pfullshare (VAL val) (pack_res_inv R))
  (* (Hct : forall ofs' : Z, *)
  (*       (Int.intval ofs <= ofs' < Int.intval ofs + LKSIZE)%Z -> *)
  (*       exists (val : memval) (sh' : Share.t), *)
  (*         m_phi jm @ (b, ofs') = YES sh' pfullshare (VAL val) (pack_res_inv R)) *)
  (Hlock : phi' @ (b, Int.intval ofs) = YES sh pfullshare (LK LKSIZE) (pack_res_inv R))
  (Hct0 : forall ofs' : Z,
         (Int.intval ofs < ofs' < Int.intval ofs + LKSIZE)%Z ->
         phi' @ (b, ofs') = YES sh pfullshare (CT LKSIZE) (pack_res_inv R))
  (Hj_forward : forall loc : block * Z,
               b <> fst loc \/ ~ (Int.intval ofs <= snd loc < Int.intval ofs + LKSIZE)%Z ->
               m_phi jm @ loc = phi' @ loc)
  (levphi' : level phi' = level (m_phi jm))
  (Htp' : tp'0 = updThread i tp Htid (Kresume c Vundef) phi')
  (Htp'' : tp' = age_tp_to (level (m_phi jm) - 1) (updLockSet tp'0 (b, Int.intval ofs) None))
  (H : tp'' = tp')
  (H0 : m'0 = m')
  (H1 : Events.mklock (b, Int.intval ofs) = ev) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m_, ge, (sch, tp_)).
  
  Proof.
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
       *)
  Admitted.
  
  Lemma preservation_freelock
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
  (HschedN : SCH.schedPeek (i :: sch) = Some i)
  (m_ := m' : Memory.mem)
  (El : Logic.True -> level (getThreadR i tp Htid) - 1 = n)
  (c : code)
  (b : block)
  (ofs : int)
  (R : pred rmap)
  (phi' : rmap)
  (sh : Share.t)
  (Hinv : invariant tp)
  (Hthread : getThreadC i tp Htid = Kblocked c)
  (Hat_external : at_external SEM.Sem c = Some (FREE_LOCK, ef_sig FREE_LOCK, Vptr b ofs :: nil))
  (Hcompatible : mem_compatible tp m')
  (Haccess : (address_mapsto LKCHUNK (Vint Int.zero) sh Share.top (b, Int.intval ofs)) phi')
  (Hlock' : exists val : memval, phi' @ (b, Int.intval ofs) = YES sh pfullshare (VAL val) (pack_res_inv R))
  (INV : state_invariant Jspec' Gamma (S n) (m', ge, (i :: sch, tp)))
  (compat : mem_compatible_with tp m' Phi)
  (lock_coh : lock_coherence' tp Phi m' compat)
  (safety : threads_safety Jspec' m' ge tp Phi compat (S n))
  (Hcmpt : mem_compatible tp m')
  (compat_aged : mem_compatible_with (age_tp_to n tp) m' (age_to n Phi))
  (Hlock : getThreadR i tp Htid @ (b, Int.intval ofs) = YES sh pfullshare (LK LKSIZE) (pack_res_inv R))
  (Hct : forall ofs' : Z,
        (Int.intval ofs < ofs' < Int.intval ofs + LKSIZE)%Z ->
        exists (val : memval) (sh' : Share.t) (X : preds),
          getThreadR i tp Htid @ (b, ofs') = YES sh' pfullshare (CT (Int.intval ofs)) X /\
          phi' @ (b, ofs') = YES sh' pfullshare (VAL val) (pack_res_inv R))
  (Hj_forward : forall loc : block * Z,
               b <> fst loc \/ ~ (Int.intval ofs <= snd loc < Int.intval ofs + LKSIZE)%Z ->
               getThreadR i tp Htid @ loc = phi' @ loc)
  (tp_ := age_tp_to (level (getThreadR i tp Htid) - 1)
           (remLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs)) : thread_pool)
  (compat_ := mem_compatible_with tp_ m_ (age_to n Phi) : Prop)
  (jmstep : @JuicyMachine.machine_step ge (i :: sch) nil tp m' sch nil
             (age_tp_to (level (getThreadR i tp Htid) - 1)
                (remLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs))) m')
  (Htstep : syncStep ge Htid Hcmpt
             (age_tp_to (level (getThreadR i tp Htid) - 1)
                (remLockSet (updThread i tp Htid (Kresume c Vundef) phi') (b, Int.intval ofs))) m'
             (Events.freelock (b, Int.intval ofs))) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m_, ge, (sch, tp_)).
  
  Proof.
  Admitted.
  
  Lemma preservation_acqfail
  (Gamma : PTree.t funspec)
  (n : nat)
  (ge : SEM.G)
  (m' : Memory.mem)
  (i : tid)
  (sch : list tid)
  (tp' : thread_pool)
  (Phi : rmap)
  (lev : level Phi = S n)
  (gam : matchfunspec (filter_genv ge) Gamma Phi)
  (ci : code)
  (HschedN : SCH.schedPeek (i :: sch) = Some i)
  (tp_ := tp' : thread_pool)
  (m_ := m' : Memory.mem)
  (compat_ := mem_compatible_with tp_ m_ (age_to n Phi) : Prop)
  (c : code)
  (b : block)
  (ofs : int)
  (psh : pshare)
  (sh : Share.t)
  (R : pred rmap)
  (Hat_external : at_external SEM.Sem c = Some (LOCK, ef_sig LOCK, Vptr b ofs :: nil))
  (sparse : lock_sparsity (lset tp'))
  (wellformed : threads_wellformed tp')
  (unique : unique_Krun tp' (i :: sch))
  (Ei cnti : ssrnat.leq (S i) (pos.n (num_threads tp')) = true)
  (Eci : getThreadC i tp' cnti = Kblocked ci)
  (Htid : ssrnat.leq (S i) (pos.n (num_threads tp')) = true)
  (El : Logic.True -> level (getThreadR i tp' Htid) - 1 = n)
  (Hcompatible : mem_compatible tp' m')
  (Hinv : invariant tp')
  (Hthread : getThreadC i tp' Htid = Kblocked c)
  (INV : state_invariant Jspec' Gamma (S n) (m', ge, (i :: sch, tp')))
  (compat : mem_compatible_with tp' m' Phi)
  (lock_coh : lock_coherence' tp' Phi m' compat)
  (safety : threads_safety Jspec' m' ge tp' Phi compat (S n))
  (Hcmpt : mem_compatible tp' m')
  (jmstep : @JuicyMachine.machine_step ge (i :: sch) nil tp' m' sch nil tp' m')
  (compat_aged : mem_compatible_with (age_tp_to n tp') m' (age_to n Phi))
  (Htstep : syncStep ge Htid Hcmpt tp' m' (Events.failacq (b, Int.intval ofs)))
  (Hload : load Mint32 (restrPermMap (mem_compatible_locks_ltwritable Hcompatible)) b (Int.intval ofs) =
          Some (Vint Int.zero))
  (HJcanwrite : m_phi (personal_mem m' (getThreadR i tp' Htid) (thread_mem_compatible Hcompatible Htid)) @
               (b, Int.intval ofs) = YES sh psh (LK LKSIZE) (pack_res_inv R)) :
  (* ============================ *)
  state_invariant Jspec' Gamma n (m', ge, (sch, tp')).
  
  Proof.
  Admitted.
  
  Lemma preservation_Kinit
  (Gamma : PTree.t funspec)
  (n : nat)
  (ge : SEM.G)
  (m m' : Memory.mem)
  (i : tid)
  (sch : list tid)
  (sch' : JuicyMachine.Sch)
  (tp tp' : thread_pool)
  (jmstep : @JuicyMachine.machine_step ge (i :: sch) (@nil Events.machine_event) tp m sch'
             (@nil Events.machine_event) tp' m')
  (INV : @state_invariant (@OK_ty (Concurrent_Espec unit CS ext_link)) Jspec' Gamma (S n) (m, ge, (i :: sch, tp)))
  (Phi : rmap)
  (compat : mem_compatible_with tp m Phi)
  (lev : @level rmap ag_rmap Phi = S n)
  (gam : matchfunspec (filter_genv ge) Gamma Phi)
  (sparse : @lock_sparsity LocksAndResources.lock_info (lset tp))
  (lock_coh : lock_coherence' tp Phi m compat)
  (safety : @threads_safety (@OK_ty (Concurrent_Espec unit CS ext_link)) Jspec' m ge tp Phi compat (S n))
  (wellformed : threads_wellformed tp)
  (unique : unique_Krun tp (i :: sch))
  (Ei : ssrnat.leq (S i) (pos.n (num_threads tp)) = true)
  (cnti : containsThread tp i)
  (v1 v2 : val)
  (Eci : getThreadC i tp cnti = @Kinit code v1 v2) :
  (* ============================ *)
  @state_invariant (@OK_ty (Concurrent_Espec unit CS ext_link)) Jspec' Gamma n (m', ge, (sch', tp')) \/
  @state_invariant (@OK_ty (Concurrent_Espec unit CS ext_link)) Jspec' Gamma (S n) (m', ge, (sch', tp')).
  
  Proof.
  Admitted.
  
  Theorem preservation Gamma n state state' :
    state_step state state' ->
    state_invariant Jspec' Gamma (S n) state ->
    state_invariant Jspec' Gamma n state' \/
    state_invariant Jspec' Gamma (S n) state'.
  Proof.
    intros STEP.
    inversion STEP as [ | ge m m' sch sch' tp tp' jmstep E E']. now auto.
    (* apply state_invariant_S *)
    subst state state'; clear STEP.
    intros INV.
    inversion INV as [m0 ge0 sch0 tp0 Phi lev gam compat sparse lock_coh safety wellformed unique E].
    subst m0 ge0 sch0 tp0.
    
    destruct sch as [ | i sch ].
    
    (* empty schedule: we loop in the same state *)
    {
      inversion jmstep; subst; try inversion HschedN.
    }
    
    destruct (ssrnat.leq (S i) tp.(num_threads).(pos.n)) eqn:Ei; swap 1 2.
    
    (* bad schedule *)
    {
      inversion jmstep; subst; try inversion HschedN; subst tid;
        unfold containsThread, is_true in *;
        try congruence.
      simpl.
      
      assert (i :: sch <> sch) by (clear; induction sch; congruence).
      inversion jmstep; subst; simpl in *; try tauto;
        unfold containsThread, is_true in *;
        try congruence.
      right. (* not consuming step level *)
      apply state_invariant_c with (PHI := Phi) (mcompat := compat); auto.
      (* invariant about "only one Krun and it is scheduled": the
       bad schedule case is not possible *)
      intros H0 i0 cnti q H1.
      exfalso.
      specialize (unique H0 i0 cnti q H1).
      destruct unique as [sch' unique]; injection unique as <- <- .
      congruence.
    }
    
    (* the schedule selected one thread *)
    assert (cnti : containsThread tp i) by apply Ei.
    remember (getThreadC _ _ cnti) as ci eqn:Eci; symmetry in Eci.
    (* remember (getThreadR cnti) as phi_i eqn:Ephi_i; symmetry in Ephi_i. *)
    
    destruct ci as
        [ (* Krun *) ci
        | (* Kblocked *) ci
        | (* Kresume *) ci v
        | (* Kinit *) v1 v2 ].
    
    (* thread[i] is running *)
    {
      pose (jmi := jm_ cnti compat).
      
      destruct ci as [ve te k | ef sig args lid ve te k] eqn:Heqc.
      
      (* thread[i] is running and some internal step *)
      {
        (* get the next step of this particular thread (with safety for all oracles) *)
        assert (next: exists ci' jmi',
                   corestep (juicy_core_sem cl_core_sem) ge ci jmi ci' jmi'
                   /\ forall ora, jsafeN Jspec' ge n ora ci' jmi').
        {
          specialize (safety i cnti).
          pose proof (safety tt) as safei.
          rewrite Eci in *.
          inversion safei as [ | ? ? ? ? c' m'' step safe H H2 H3 H4 | | ]; subst.
          2: now match goal with H : at_external _ _ = _ |- _ => inversion H end.
          2: now match goal with H : halted _ _ = _ |- _ => inversion H end.
          exists c', m''. split; [ apply step | ].
          revert step safety safe; clear.
          generalize (jm_ cnti compat).
          generalize (State ve te k).
          unfold jsafeN.
          intros c j step safety safe ora.
          eapply safe_corestep_forward.
          - apply juicy_core_sem_preserves_corestep_fun.
            apply semax_lemmas.cl_corestep_fun'.
          - apply step.
          - apply safety.
        }
        
        destruct next as (ci' & jmi' & stepi & safei').
        pose (tp'' := @updThread i tp cnti (Krun ci') (m_phi jmi')).
        pose (tp''' := age_tp_to (level jmi') tp').
        pose (cm' := (m_dry jmi', ge, (i :: sch, tp'''))).
        
        (* now, the step that has been taken in jmstep must correspond
        to this cm' *)
        inversion jmstep; subst; try inversion HschedN; subst tid;
          unfold containsThread, is_true in *;
          try congruence.
        
        - (* not in Kinit *)
          jmstep_inv. getThread_inv. congruence.
        
        - (* not in Kresume *)
          jmstep_inv. getThread_inv. congruence.
        
        - (* here is the important part, the corestep *)
          jmstep_inv.
          assert (En : level Phi = S n) by auto. (* will be in invariant *)
          left. (* consuming one step of level *)
          eapply invariant_thread_step; eauto.
          + apply Jspec'_hered.
          + apply Jspec'_juicy_mem_equiv.
          + eapply lock_coh_bound; eauto.
          + exact_eq Hcorestep.
            rewrite Ejuicy_sem.
            unfold jm_.
            do 2 f_equal.
            apply proof_irr.
          + rewrite Ejuicy_sem in *.
            getThread_inv.
            injection H as <-.
            unfold jmi in stepi.
            exact_eq safei'.
            extensionality ora.
            cut ((ci', jmi') = (c', jm')). now intros H; injection H as -> ->; auto.
            eapply juicy_core_sem_preserves_corestep_fun; eauto.
            * apply semax_lemmas.cl_corestep_fun'.
            * exact_eq Hcorestep.
              unfold jm_.
              f_equal.
              apply personal_mem_ext.
              repeat f_equal; apply proof_irr.
        
        - (* not at external *)
          jmstep_inv. getThread_inv.
          injection H as <-.
          erewrite corestep_not_at_external in Hat_external. discriminate.
          unfold SEM.Sem in *.
          rewrite SEM.CLN_msem.
          eapply stepi.
          
        - (* not in Kblocked *)
          jmstep_inv.
          all: getThread_inv.
          all: congruence.
          
        - (* not halted *)
          jmstep_inv. getThread_inv.
          injection H as <-.
          erewrite corestep_not_halted in Hcant. discriminate.
          unfold SEM.Sem in *.
          rewrite SEM.CLN_msem.
          eapply stepi.
      }
      (* end of internal step *)
      
      (* thread[i] is running and about to call an external: Krun (at_ex c) -> Kblocked c *)
      {
        inversion jmstep; subst; try inversion HschedN; subst tid;
          unfold containsThread, is_true in *;
          try congruence.
        
        - (* not in Kinit *)
          jmstep_inv. getThread_inv. congruence.
        
        - (* not in Kresume *)
          jmstep_inv. getThread_inv. congruence.
        
        - (* not a corestep *)
          jmstep_inv. getThread_inv. injection H as <-.
          pose proof corestep_not_at_external _ _ _ _ _ _ Hcorestep.
          rewrite Ejuicy_sem in *.
          discriminate.
        
        - (* we are at an at_ex now *)
          jmstep_inv. getThread_inv.
          injection H as <-.
          rename m' into m.
          right. (* no aging *)
          
          match goal with |- _ _ (_, _, (_, ?tp)) => set (tp' := tp) end.
          assert (compat' : mem_compatible_with tp' m Phi).
          {
            clear safety wellformed unique.
            destruct compat as [JA MC LW LC LJ].
            constructor; [ | | | | ].
            - destruct JA as [tp phithreads philocks Phi jointhreads joinlocks join].
              econstructor; eauto.
            - apply MC.
            - intros b o H.
              apply (LW b o H).
            - apply LC.
            - apply LJ.
          }
          
          apply state_invariant_c with (PHI := Phi) (mcompat := compat').
          + assumption.
          
          + (* matchfunspec *)
            assumption.
          
          + (* lock sparsity *)
            auto.
          
          + (* lock coherence *)
            unfold lock_coherence' in *.
            exact_eq lock_coh.
            f_equal.
            f_equal.
            apply proof_irr.
          
          + (* safety (same, except one thing is Kblocked instead of Krun) *)
            intros i0 cnti0' ora.
            destruct (eq_dec i i0) as [ii0 | ii0].
            * subst i0.
              unfold tp'.
              rewrite gssThreadCC.
              specialize (safety i cnti ora).
              rewrite Eci in safety.
              simpl.
              simpl in safety.
              unfold jm_ in *.
              erewrite personal_mem_ext.
              -- apply safety.
              -- apply gThreadCR.
            * assert (cnti0 : containsThread tp i0) by auto.
              unfold tp'.
              rewrite <- (@gsoThreadCC _ _ tp ii0 ctn cnti0).
              specialize (safety i0 cnti0 ora).
              clear -safety.
              destruct (@getThreadC i0 tp cnti0).
              -- unfold jm_ in *.
                 erewrite personal_mem_ext.
                 ++ apply safety.
                 ++ intros; apply gThreadCR.
              -- unfold jm_ in *.
                 erewrite personal_mem_ext.
                 ++ apply safety.
                 ++ intros; apply gThreadCR.
              -- unfold jm_ in *.
                 intros c' E.
                 erewrite personal_mem_ext.
                 ++ apply safety, E.
                 ++ intros; apply gThreadCR.
              -- constructor.
          
          + (* wellformed. *)
            intros i0 cnti0'.
            destruct (eq_dec i i0) as [ii0 | ii0].
            * subst i0.
              unfold tp'.
              rewrite gssThreadCC.
              simpl.
              congruence.
            * assert (cnti0 : containsThread tp i0) by auto.
              unfold tp'.
              rewrite <- (@gsoThreadCC _ _ tp ii0 ctn cnti0).
              specialize (wellformed i0 cnti0).
              destruct (@getThreadC i0 tp cnti0).
              -- constructor.
              -- apply wellformed.
              -- apply wellformed.
              -- constructor.
          
          + (* uniqueness *)
            intros notalone i0 cnti0' q Eci0.
            pose proof (unique notalone i0 cnti0' q) as unique'.
            destruct (eq_dec i i0) as [ii0 | ii0].
            * subst i0.
              unfold tp' in Eci0.
              rewrite gssThreadCC in Eci0.
              discriminate.
            * assert (cnti0 : containsThread tp i0) by auto.
              unfold tp' in Eci0.
              clear safety wellformed.
              rewrite <- (@gsoThreadCC _ _ tp ii0 ctn cnti0) in Eci0.
              destruct (unique notalone i cnti _ Eci).
              destruct (unique notalone i0 cnti0 q Eci0).
              congruence.
        
        - (* not in Kblocked *)
          jmstep_inv.
          all: getThread_inv.
          all: congruence.
          
        - (* not halted *)
          jmstep_inv. getThread_inv.
          injection H as <-.
          erewrite at_external_not_halted in Hcant. discriminate.
          unfold SEM.Sem in *.
          rewrite SEM.CLN_msem.
          simpl.
          congruence.
      } (* end of Krun (at_ex c) -> Kblocked c *)
    } (* end of Krun *)
    
    (* thread[i] is in Kblocked *)
    { (* only one possible jmstep, in fact divided into 6 sync steps *)
      inversion jmstep; try inversion HschedN; subst tid;
        unfold containsThread, is_true in *;
        try congruence; try subst;
        try solve [jmstep_inv; getThread_inv; congruence].
      
      simpl SCH.schedSkip in *.
      left (* TO BE CHANGED *).
      (* left (* we need aging, because we're using the safety of the call *). *)
      match goal with |- _ _ _ (?M, _, (_, ?TP)) => set (tp_ := TP); set (m_ := M) end.
      pose (compat_ := mem_compatible_with tp_ m_ (age_to n Phi)).
      cleanup.
      assert (El : Logic.True -> level (getThreadR _ _ Htid) - 1 = n). {
        rewrite getThread_level with (Phi := Phi).
        - cleanup; rewrite lev; omega.
        - apply compat.
      }
      
      pose proof mem_compatible_with_age compat (n := n) as compat_aged.
      
      jmstep_inv.
      
      - (* the case of acquire *)
        eapply preservation_acquire; eauto.
      
      - (* the case of release *)
        eapply preservation_release; eauto.
      
      - (* the case of spawn *)
        eapply preservation_spawn; eauto.
      
      - (* the case of makelock *)
        eapply preservation_makelock; eauto.
      
      - (* the case of freelock *)
        eapply preservation_freelock; eauto.
      
      - (* the case of acq-fail *)
        eapply preservation_acqfail; eauto.
    }
    
    (*thread[i] is in Kresume *)
    { (* again, only one possible case *)
      right (* no aging *).
      inversion jmstep; try inversion HschedN; subst tid;
        unfold containsThread, is_true in *;
        try congruence; try subst;
        try solve [jmstep_inv; getThread_inv; congruence].
      jmstep_inv.
      rename m' into m.
      assert (compat' : mem_compatible_with (updThreadC _ _ ctn (Krun c')) m Phi).
      {
        clear safety wellformed unique.
        destruct compat as [JA MC LW LC LJ].
        constructor; [ | | | | ].
        - destruct JA as [tp phithreads philocks Phi jointhreads joinlocks join].
          econstructor; eauto.
        - apply MC.
        - intros b o H.
          apply (LW b o H).
        - apply LC.
        - apply LJ.
      }
      
      apply state_invariant_c with (PHI := Phi) (mcompat := compat').
      + (* level *)
        assumption.
      
      + (* matchfunspec *)
        assumption.
      
      + (* lock sparsity *)
        auto.
      
      + (* lock coherence *)
        unfold lock_coherence' in *.
        exact_eq lock_coh.
        f_equal.
        f_equal.
        apply proof_irr.
      
      + (* safety : the new c' is derived from "after_external", so
           that's not so good? *)
        intros i0 cnti0' ora.
        destruct (eq_dec i i0) as [ii0 | ii0].
        * subst i0.
          rewrite gssThreadCC.
          specialize (safety i cnti ora).
          rewrite Eci in safety.
          simpl.
          (* apply safe_downward1. *)
          change (jsafeN Jspec' ge (S n) ora c' (jm_ cnti0' compat')).
          getThread_inv. injection H as -> -> .
          specialize (safety c').
          unfold SEM.Sem in *.
          rewrite SEM.CLN_msem in *.
          specialize (safety ltac:(eauto)).
          exact_eq safety.
          f_equal.
          Set Printing Implicit.
          unshelve erewrite jm_updThreadC. auto.
          unfold jm_ in *.
          f_equal.
          apply personal_mem_ext.
          f_equal.
          apply proof_irr.
        * assert (cnti0 : containsThread tp i0) by auto.
          rewrite <- (@gsoThreadCC _ _ tp ii0 ctn cnti0).
          specialize (safety i0 cnti0 ora).
          clear -safety.
          destruct (@getThreadC i0 tp cnti0).
          -- unfold jm_ in *.
             erewrite personal_mem_ext.
             ++ apply safety.
             ++ intros; apply gThreadCR.
          -- unfold jm_ in *.
             erewrite personal_mem_ext.
             ++ apply safety.
             ++ intros; apply gThreadCR.
          -- unfold jm_ in *.
             erewrite personal_mem_ext.
             ++ intros c'' E; apply safety, E.
             ++ intros; apply gThreadCR.
          -- constructor.
      
      + (* wellformed. *)
        intros i0 cnti0'.
        destruct (eq_dec i i0) as [ii0 | ii0].
        * subst i0.
          rewrite gssThreadCC.
          constructor.
        * assert (cnti0 : containsThread tp i0) by auto.
          rewrite <- (@gsoThreadCC _ _ tp ii0 ctn cnti0).
          specialize (wellformed i0 cnti0).
          destruct (@getThreadC i0 tp cnti0).
          -- constructor.
          -- apply wellformed.
          -- apply wellformed.
          -- constructor.
             
      + (* uniqueness *)
        intros notalone i0 cnti0' q Eci0.
        pose proof (unique notalone i0 cnti0' q) as unique'.
        destruct (eq_dec i i0) as [ii0 | ii0].
        * subst i0.
          eauto.
        * assert (cnti0 : containsThread tp i0) by auto.
          clear safety wellformed.
          rewrite <- (@gsoThreadCC _ _ tp ii0 ctn cnti0) in Eci0.
          destruct (unique notalone i0 cnti0 q Eci0).
          congruence.
    }
    
    (* thread[i] is in Kinit *)
    {
      (* still unclear how to handle safety of Kinit states *)
      eapply preservation_Kinit; eauto.
    }
  Qed.
End Preservation.
