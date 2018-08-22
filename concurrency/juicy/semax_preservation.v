
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
Require Import VST.veric.age_to_resource_at.
Require Import VST.floyd.coqlib3.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.concurrency.common.permjoin.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.concurrency.juicy.semax_conc.
Require Import VST.concurrency.juicy.juicy_machine.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.juicy.JuicyMachineModule.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.juicy.sync_preds_defs.
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.juicy.join_lemmas.
Require Import VST.concurrency.juicy.cl_step_lemmas.
Require Import VST.concurrency.juicy.resource_decay_lemmas.
Require Import VST.concurrency.juicy.resource_decay_join.
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.juicy.semax_invariant.
Require Import VST.concurrency.juicy.semax_simlemmas.
Require Import VST.concurrency.juicy.semax_preservation_jspec.
Require Import VST.concurrency.juicy.semax_preservation_local.
Require Import VST.concurrency.juicy.semax_preservation_acquire.

Local Arguments getThreadR {_} {_} {_} _ _ _.
Local Arguments getThreadC {_} {_} {_} _ _ _.
Local Arguments personal_mem : clear implicits.
Local Arguments updThread {_} {_} {_} _ _ _ _ _.
Local Arguments updThreadR {_} {_} {_} _ _ _ _.
Local Arguments updThreadC {_} {_} {_} _ _ _ _.
Local Arguments juicyRestrict : clear implicits.

Set Bullet Behavior "Strict Subproofs".

Lemma rmap_bound_join {b phi1 phi2 phi3} :
  join phi1 phi2 phi3 ->
  rmap_bound b phi3 ->
  rmap_bound b phi2.
Proof.
  intros j B l p; specialize (B l p).
  apply resource_at_join with (loc := l) in j.
  rewrite B in j.
  inv j; eauto. apply NO_ext.
  erewrite join_to_bot_l; eauto.
Qed.

Lemma resource_fmap_YES_inv f g r sh rsh k pp :
  resource_fmap f g r = YES sh rsh k pp ->
  exists pp', r = YES sh rsh k pp' /\ pp = preds_fmap f g pp'.
Proof.
  destruct r as [t0 | t0 p k0 p0 | k0 p]; simpl; try congruence.
  injection 1 as <- <- <-. exists p0. split; auto. apply YES_ext; auto.
Qed.

Lemma resource_fmap_PURE_inv f g r k pp :
  resource_fmap f g r = PURE k pp ->
  exists pp', r = PURE k pp' /\ pp = preds_fmap f g pp'.
Proof.
  destruct r as [t0 | t0 p k0 p0 | k0 p]; simpl; try congruence.
  injection 1 as <- <-. eauto.
Qed.

Lemma resource_fmap_NO_inv f g r sh nsh :
  resource_fmap f g r = NO sh nsh ->
  r = NO sh nsh.
Proof.
  destruct r as [t0 | t0 p k0 p0 | k0 p]; simpl; try congruence.
Qed.

Lemma isSome_option_map {A B} (f : A -> B) o : ssrbool.isSome (option_map f o) = ssrbool.isSome o.
Proof.
  destruct o; reflexivity.
Qed.

Lemma cl_step_mem_step ge c m c' m' : cl_step ge c m c' m' -> mem_step m m'.
Proof.
  intros H.
  eapply (corestep_mem (CLN_memsem ge)), H.
Qed.

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

(*Lemma mem_cohere_age_to_inv n m phi :
  mem_cohere' m (age_to n phi) ->
  mem_cohere' m phi.
Proof.
  intros [A B C]; split.
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
      pose proof (@equal_f_dep _ _ _ _ F x) as E.
      simpl in E.
    Abort.
Abort.*)

           Lemma perm_of_res'_resource_fmap f g r :
             perm_of_res' (resource_fmap f g r) = perm_of_res' r.
           Proof.
             destruct r; simpl; auto.
           Qed.

Lemma mem_cohere_step c c' jm jm' Phi (X : rmap) ge :
  mem_cohere' (m_dry jm) Phi ->
  sepalg.join (m_phi jm) X Phi ->
  corestep (juicy_core_sem (cl_core_sem ge)) c jm c' jm' ->
  exists Phi',
    sepalg.join (m_phi jm') (age_to (level (m_phi jm')) X) Phi' /\
    mem_cohere' (m_dry jm') Phi'.
Proof.
  intros MC J C.
  destruct C as [step [RD [L G]]].
  assert (Bx : rmap_bound (Mem.nextblock (m_dry jm)) X) by apply (rmap_bound_join J), MC.
  destruct (resource_decay_join _ _ _ _ _  Bx RD (* L *) G J) as [Phi' [J' RD']].
  exists Phi'. split. apply J'.
  pose proof cl_step_mem_step _ _ _ _ _ step as ms.
  pose proof cl_step_decay _ _ _ _ _ step as dec.

  destruct MC as [A B C D].
  unfold contents_cohere in *.
  constructor.
  (* apply mem_cohere'_redundant. *)

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
        apply YES_inj in H1. inv H1. inv H2.
         clear - RJ0 rsh5. apply join_top_l in RJ0. subst.
         apply shares.bot_unreadable; auto.

    + (* from both X and jm' *)
      symmetry in H0.
      apply resource_fmap_YES_inv in H0.
      destruct H0 as (pp' & -> & ->).
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
           rewrite perm_of_res'_resource_fmap; auto.

    + (* "Write" case *)
      destruct RD as (sh & wsh & v & v' & E & E').
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
           replace (perm_of_res' (Phi' @ loc)) with (perm_of_res' (Phi @ loc)). now auto.
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
              assert (sh0 = sh2) by congruence. subst.
              eapply join_eq; eauto.
           ++ destruct (X @ loc); congruence.
           ++ destruct (X @ loc); congruence.
           ++ assert (sh0 = sh2) by congruence. subst.
              symmetry in H5.
              assert (sh3=sh4) by (eapply join_eq; eauto). subst.
              apply resource_fmap_YES_inv in H5.
              destruct H5 as (pp' & ? & Epp).
              destruct (Phi @ loc); inv H.
              simpl; f_equal.

    + (* "Alloc" case *)
      autospec NN.
      eapply perm_order''_trans. now apply access_cur_max.
      rewrite juicy_mem_access.
      rewrite RD.
      simpl.
      rewrite perm_of_freeable.
      destruct (perm_of_res' (Phi' @ loc)) as [[]|]; constructor.

    + (* "Free" case *)
      cut (perm_of_res' (Phi' @ loc) = None).
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
      * elimtype False; clear - RJ rsh2.  apply join_top_l in RJ. subst.
         apply shares.bot_unreadable; auto.

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
    apply NO_ext.
    rewrite (join_bot_bot_eq sh3); auto.
Qed.

(** About lock_coherence *)

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
  destruct C as ((* sh &  *)align & bound & R & lk & sat).
  repeat (split; auto).
  exists (* sh, *) R; split. eauto.
  destruct sat as [sat|?]; auto. left.
  unfold age_to.
  rewrite age_by_age_by, plus_comm, <-age_by_age_by.
  revert sat.
  apply age_by_ind.
  apply (proj2_sig R).
Qed.

Ltac jmstep_inv :=
  match goal with
  | H : JuicyMachine.start_thread _ _ _ _  |- _ => inversion H
  | H : JuicyMachine.resume_thread _ _ _   |- _ => inversion H
  | H : JuicyMachine.threadStep _ _ _ _ _           |- _ => inversion H
  | H : JuicyMachine.suspend_thread _ _ _ |- _ => inversion H
  | H : JuicyMachine.syncStep _ _ _ _ _ _           |- _ => inversion H
(*  | H : JuicyMachine.threadHalted _                   |- _ => inversion H*)
  | H : JuicyMachine.schedfail _         |- _ => inversion H
  end; try subst.

Ltac getThread_inv :=
  match goal with
  | [ H : getThreadC ?i _ _ = _ ,
          H2 : getThreadC ?i _ _ = _ |- _ ] =>
    pose proof (getThreadC_fun _ _ _ _ _ _ _ H H2)
  | [ H : getThreadR ?i _ _ = _ ,
          H2 : getThreadR ?i _ _ = _ |- _ ] =>
    pose proof (getThreadR_fun _ _ _ _ _ _ _ H H2)
  end.

Ltac substwith x y := assert (x = y) by apply proof_irr; subst x.

Lemma load_restrPermMap ge m (tp : jstate ge) Phi b ofs m_any
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

Lemma lock_coh_bound ge (tp : jstate ge) m Phi
      (compat : mem_compatible_with tp m Phi)
      (coh : lock_coherence' tp Phi m compat) :
  lockSet_block_bound (lset tp) (Mem.nextblock m).
Proof.
  intros loc find.
  specialize (coh loc).
  destruct (AMap.find (elt:=option rmap) loc (lset tp)) as [o|]; [ | inversion find ].
  match goal with |- (?a < ?b)%positive => assert (D : (a >= b \/ a < b)%positive) by (zify; omega) end.
  destruct D as [D|D]; auto. exfalso.
  assert (AT : exists (R : pred rmap), (lkat R loc) Phi). {
    destruct o.
    - destruct coh as [LOAD ((* sh' &  *)align & bound & R' & lk & sat)]; eauto.
    - destruct coh as [LOAD ((* sh' &  *)align & bound & R' & lk)]; eauto.
  }
  clear coh.
  destruct AT as (R & AT).
  destruct compat.
  destruct all_cohere0.
  specialize (all_coh0 loc D).
  specialize (AT loc).
  destruct loc as (b, ofs).
  simpl in AT.
  spec AT. split; auto. lkomega.
  rewrite all_coh0 in AT.
  breakhyps.
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
  - replace (ghost_of e') with (core (ghost_of e')).
    rewrite age_to_ghost_of; replace (ghost_of e) with (core (ghost_of e)).
    rewrite !ghost_core; auto.
    + symmetry; apply identity_core, ghost_of_identity; auto.
    + symmetry; apply identity_core, ghost_of_identity; auto.
Qed.

Lemma mem_cohere'_store ge m (tp : jstate ge) m' b ofs j i Phi (cnti : containsThread tp i):
  forall (Hcmpt : mem_compatible tp m)
    (lock : lockRes tp (b, Ptrofs.intval ofs) <> None)
    (Hlt' : permMapLt
           (setPermBlock (Some Writable) b (Ptrofs.intval ofs) (juice2Perm_locks (getThreadR i tp cnti) m)
              LKSIZE_nat) (getMaxPerm m))
    (Hstore : Mem.store Mint32 (restrPermMap Hlt') b (Ptrofs.intval ofs) (Vint j) = Some m'),
    mem_compatible_with tp m Phi (* redundant with Hcmpt, but easier *) ->
    (exists phi, join_sub phi Phi /\ exists sh R, LKspec LKSIZE sh R (b, Ptrofs.intval ofs) phi) ->
    mem_cohere' m' Phi.
Proof.
  intros Hcmpt lock Hlt' Hstore compat HLKspec.
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
      destruct HLKspec as (? & J' & ? & ? & HLKspec & ?).
      apply (resource_at_join_sub _ _ (b', ofs')) in J' as [? J'].
      rewrite E in J'.
      specialize (HLKspec (b', ofs')); simpl in HLKspec.
      rewrite if_true in HLKspec.
      destruct HLKspec as [? HLK]; rewrite HLK in J'; inv J'.
      { destruct In; pose proof LKSIZE_int; split; auto; omega. }

    + rewrite <-Out.
      unfold juicyRestrict_locks in *.
      rewrite restrPermMap_contents.
      auto.

  - intros loc.
    replace (max_access_at m' loc)
    with (max_access_at (restrPermMap Hlt') loc)
    ; swap 1 2.
    { unfold max_access_at in *.
      unfold juicyRestrict_locks in *.
      destruct SO as (_ & -> & _). reflexivity. }
    clear SO.
    unfold juicyRestrict_locks in *.
    rewrite restrPermMap_max.
    apply Ac.

  - unfold alloc_cohere in *.
    destruct SO as (_ & _ & <-). auto.
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
      rewrite <-juic2Perm_correct. 2: apply acc_coh, pr.
      rewrite <-juic2Perm_correct. 2: apply acc_coh, pr'.
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
        pose proof @juicyRestrictCurEq phi m ltac:(apply acc_coh, pr) (b, ofs) as R.
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
  - extensionality b ofs k p.
    apply prop_ext; auto.
  - auto.
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

Lemma jm_updThreadC ge i (tp : jstate ge) ctn c' m Phi cnti pr pr' :
  @jm_ _ (updThreadC i tp ctn c') m Phi i cnti pr =
  @jm_ _ tp m Phi i cnti pr'.
Proof.
  apply juicy_mem_ext.
  - apply juicyRestrict_ext.
    REWR.
    intro; repeat f_equal. apply proof_irr.
  - do 2 rewrite m_phi_jm_.
    REWR.
    repeat f_equal. apply proof_irr.
Qed.

Lemma lockSet_Writable_updLockSet_updThread ge m m' i (tp : jstate ge)
      cnti b ofs ophi ophi' c' phi' z
      (Hcmpt : mem_compatible tp m)
      (His_unlocked : AMap.find (elt:=option rmap) (b, Ptrofs.intval ofs) (lset tp) = Some ophi)
      (Hlt' : permMapLt
           (setPermBlock (Some Writable) b (Ptrofs.intval ofs) (juice2Perm_locks (getThreadR i tp cnti) m)
              LKSIZE_nat) (getMaxPerm m))
      (Hstore : Mem.store Mint32 (restrPermMap Hlt') b (Ptrofs.intval ofs) (Vint z) = Some m') :
  lockSet_Writable (lset (updLockSet (updThread i tp cnti c' phi') (b, Ptrofs.intval ofs) ophi')) m'.
Proof.
  destruct Hcmpt as (Phi, compat).
  pose proof (loc_writable compat) as lw.
  intros b' ofs' is; specialize (lw b' ofs').
  destruct (eq_dec (b, Ptrofs.intval ofs) (b', ofs')).
  + injection e as <- <- .
    intros ofs0 int0.
    rewrite (Mem.store_access _ _ _ _ _ _ Hstore).
    pose proof restrPermMap_Max as RR.
    unfold juicyRestrict_locks in *.
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
    unfold juicyRestrict_locks in *.
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

Lemma lockSet_Writable_updThread_updLockSet ge m m' i (tp : jstate ge)
      b ofs ophi ophi' c' phi' z cnti
      (Hcmpt : mem_compatible tp m)
      (His_unlocked : AMap.find (elt:=option rmap) (b, Ptrofs.intval ofs) (lset tp) = Some ophi)
      (Hlt' : permMapLt
           (setPermBlock (Some Writable) b (Ptrofs.intval ofs) (juice2Perm_locks (getThreadR i tp cnti) m)
              LKSIZE_nat) (getMaxPerm m))
      (Hstore : Mem.store Mint32 (restrPermMap Hlt') b (Ptrofs.intval ofs) (Vint z) = Some m') :
  lockSet_Writable (lset (updThread i (updLockSet tp (b, Ptrofs.intval ofs) ophi') cnti c' phi')) m'.
Proof.
  destruct Hcmpt as (Phi, compat).
  pose proof (loc_writable compat) as lw.
  intros b' ofs' is; specialize (lw b' ofs').
  destruct (eq_dec (b, Ptrofs.intval ofs) (b', ofs')).
  + injection e as <- <- .
    intros ofs0 int0.
    rewrite (Mem.store_access _ _ _ _ _ _ Hstore).
    pose proof restrPermMap_Max as RR.
    unfold permission_at in RR.
    unfold juicyRestrict_locks in *.
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
    unfold juicyRestrict_locks in *.
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

Lemma resource_decay_join_all' ge {tp : jstate ge} {m Phi} c' {phi' i} {cnti : containsThread tp i}:
  rmap_bound (Mem.nextblock m) Phi ->
  resource_decay (Mem.nextblock m) (getThreadR i tp cnti) phi' /\
  level (getThreadR i tp cnti) = level phi' /\
  ghost_of phi' = ghost_fmap (approx (level phi')) (approx (level phi')) (ghost_of (getThreadR i tp cnti)) ->
  join_all tp Phi ->
  exists Phi',
    join_all (updThread i (age_tp_to (level phi') tp) (cnt_age' cnti) c' phi') Phi' /\
    resource_decay (Mem.nextblock m) Phi Phi' /\
    ghost_of Phi' = own.ghost_approx Phi' (ghost_of Phi) /\
    level Phi = level Phi'.
Proof.
  do 2 rewrite join_all_joinlist.
  intros B (rd & lev & g) j.
  rewrite (maps_getthread _ _ cnti) in j.
  destruct (resource_decay_joinlist _ _ _ _ _ B rd g j) as (Phi' & j' & rd' & ?).
  exists Phi'; split; [ | split; [|split]]; auto.
  - rewrite maps_updthread.
    exact_eq j'. f_equal. f_equal. rewrite <-all_but_map, maps_age_to.
    auto.
  - exact_eq lev; f_equal.
    + apply rmap_join_sub_eq_level. eapply joinlist_join_sub; eauto. left; auto.
    + apply rmap_join_sub_eq_level. eapply joinlist_join_sub; eauto. left; auto.
Qed.

Lemma AMap_ext : forall {A} (m1 m2 : AMap.t A), AMap.this m1 = AMap.this m2 -> m1 = m2.
Proof.
  destruct m1, m2; simpl; intros; subst; f_equal.
  apply proof_irr.
Qed.

Lemma AMap_find_In : forall {A} m k (v : A), AMap.Raw.find k m = Some v -> In (k, v) m.
Proof.
  induction m; [discriminate | simpl; intros].
  destruct a.
  destruct (AddressOrdered.compare _ _); try discriminate.
  - inv H; auto.
  - right; apply IHm; auto.
Qed.

Lemma age_tp_to_eq: forall ge (k : nat) (tp : jstate ge) (phi : rmap),
  join_all tp phi ->
  k = level phi ->
  age_tp_to k tp = tp.
Proof.
  intros.
  assert (forall i cnti, level (getThreadR i tp cnti) = level phi) as Hl.
  { intros; apply getThread_level; auto. }
  assert (forall l r, AMap.find l (lset tp) = Some (Some r) -> level r = level phi) as Hll.
  { intros; eapply join_all_level_lset; eauto. }
  destruct tp; simpl in *; f_equal.
  - extensionality; unfold compose.
    apply age_to_eq.
    destruct x.
    rewrite Hl; auto.
  - apply AMap_ext; simpl.
    rewrite <- H0 in Hll.
    clear - Hll.
    unfold AMap.find in Hll.
    pose proof AMap.sorted lset0 as Hsorted.
    apply Sorted.Sorted_StronglySorted in Hsorted.
    forget (AMap.this lset0) as l; induction Hsorted; auto; simpl in *.
    destruct a.
    rewrite IHHsorted.
    + specialize (Hll a).
      destruct o; auto.
      simpl; repeat f_equal.
      apply age_to_eq.
      destruct (AMap.Raw.MX.elim_compare_eq(y := a) eq_refl).
      rewrite H0 in Hll; rewrite Hll; auto.
    + intros.
      apply (Hll l0).
      assert (is_true (AddressOrdered.lt' a l0)) as Hlt.
      { rewrite Forall_forall in H.
        apply (H _ (AMap_find_In _ _ _ H0)). }
      destruct (AMap.Raw.MX.elim_compare_gt Hlt) as [? ->]; auto.
    + intros ?????; hnf in *.
      eapply AMap.Raw.MX.lt_strorder; eauto.
Qed.

Section Preservation.
  Variables
    (CS : compspecs)
    (ext_link : string -> ident)
    (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2).

  Definition Jspec' := (@OK_spec (Concurrent_Espec unit CS ext_link)).

  Open Scope string_scope.

  Lemma preservation_Kinit
  (Gamma : funspecs)
  (n : nat)
  (ge : genv)
  (m m' : Memory.mem)
  (i : nat)
  (tr tr' : event_trace)
  (sch : list nat)
  sch'
  (tp tp' : jstate ge)
  (jmstep : @JuicyMachine.machine_step _ (ClightSemanticsForMachines.Clight_newSem ge) _ HybridCoarseMachine.DilMem JuicyMachineShell HybridMachineSig.HybridCoarseMachine.scheduler (i :: sch) tr tp m sch'
             tr' tp' m')
  (INV : @state_invariant (@OK_ty (Concurrent_Espec unit CS ext_link)) Jspec' _ Gamma (S n) (m, (tr, i :: sch, tp)))
  (Phi : rmap)
  (compat : mem_compatible_with tp m Phi)
  (extcompat : joins (ghost_of Phi) (Some (ext_ref tt, NoneP) :: nil))
  (lev : @level rmap ag_rmap Phi = S n)
  (envcoh : env_coherence Jspec' ge Gamma Phi)
  (sparse : @lock_sparsity lock_info (lset tp))
  (lock_coh : lock_coherence' tp Phi m compat)
  (safety : @threads_safety (@OK_ty (Concurrent_Espec unit CS ext_link)) Jspec' _ m tp Phi compat (S n))
  (wellformed : threads_wellformed tp)
  (unique : unique_Krun tp (i :: sch))
  (Ei : ssrnat.leq (S i) (pos.n (num_threads tp)) = true)
  (cnti : containsThread tp i)
  (v1 v2 : val)
  (Eci : getThreadC i tp cnti = @Kinit semC v1 v2) :
  (* ============================ *)
  @state_invariant (@OK_ty (Concurrent_Espec unit CS ext_link)) Jspec' _ Gamma n (m', (tr', sch', tp')) \/
  @state_invariant (@OK_ty (Concurrent_Espec unit CS ext_link)) Jspec' _ Gamma (S n) (m', (tr', sch', tp')).

  Proof.
    inversion jmstep; subst; try inversion HschedN; subst tid;
      simpl containsThread in *; unfold containsThread, is_true in *;
      try congruence.
 *
   inv Htstep.
   simpl in Hinitial.
   pose proof safety as safety'.
   specialize (safety i cnti tt). rewr (getThreadC i tp cnti) in safety.
   destruct safety as (Hvalid & c_new_ & E_c_new & safety).
   substwith ctn Htid.
   substwith Htid cnti.
   setoid_rewrite Eci in Hcode; inv Hcode.
   assert (c_new_ = c_new). {
     destruct Hinitial. clear - E_c_new H.
    hnf in E_c_new,H. destruct vf; try contradiction. if_tac in H; try contradiction.
     destruct (Genv.find_funct_ptr ge b); try contradiction.
     destruct (type_of_fundef f); try contradiction.
     decompose [and] E_c_new. decompose [and] H. congruence.
  } subst c_new_.
   destruct Hinitial as (Hinitial & ? & ?); subst.
      simpl JuicyMachine.add_block in *.
      unfold add_block in *.
      assert (mem_compatible_with (updThread i tp cnti (Krun c_new) (getThreadR i tp cnti))
        m' Phi) as Hcmpt'.
      {apply mem_compatible_with_same_except_cur with m.
       inv Hperm.
       pose proof (same_except_cur_jm_ _ _ _ _ _ cnti compat).
       unfold install_perm; simpl in H0.
       auto. 
       clear - compat. inv compat; constructor; auto.
       rewrite join_all_res; auto. }
      assert (B : rmap_bound (Mem.nextblock m) Phi) by apply compat.
      right.  (* ? *)
      apply state_invariant_c with (mcompat := Hcmpt'); auto.
      - intro; simpl.
        pose proof (lock_coh loc) as lock_coh'.
        destruct (AMap.find _ _) eqn: Hloc; auto.
        assert (forall v, load_at (restrPermMap
          (mem_compatible_locks_ltwritable (mem_compatible_forget compat))) loc = Some v ->
          load_at (restrPermMap
          (mem_compatible_locks_ltwritable (mem_compatible_forget Hcmpt'))) loc = Some v).
        { intro.
          unfold load_at; intro Hload.
          apply lock_coh_bound in lock_coh.
          specialize (lock_coh loc).
          setoid_rewrite Hloc in lock_coh; spec lock_coh; [simpl; auto|].
          unfold load in *.
          destruct (valid_access_dec (restrPermMap (mem_compatible_locks_ltwritable
            (mem_compatible_forget compat))) _ _ _ _); [|discriminate].
          hnf in Hperm; subst.
          rewrite if_true; auto.
        { unfold install_perm, juicyRestrict.
            destruct v0; split; auto.
            apply Mem.range_perm_implies with Writable; [|constructor].
            destruct loc as (?, ofs).
            repeat intro.
            eapply lset_range_perm with (ofs := ofs); eauto.
            destruct (AMap.find (elt:=option rmap) _ _); discriminate.
            { lkomega. } } }
        destruct o.
        + destruct lock_coh' as (? & ? & ? & ? & ? & ?); eauto 7.
        + destruct lock_coh' as (? & ? & ? & ? & ?); eauto 6.
      - intros j cntj [].
        destruct (eq_dec i j) as [<-|ne].
        + REWR.
(*          inv Hinitial. *)
          apply safety.
          rewrite m_phi_jm_.
          REWR.
        + REWR.
          specialize (safety' j cntj tt).
          destruct (getThreadC j tp cntj) eqn: Ej; try solve [erewrite gsoThreadRes; eauto].
          pose proof cntUpdate'(ThreadPool := OrdinalThreadPool) _ _ cnti cntj as cntj'.
          eapply unique_Krun_neq in Ej; try apply unique; auto; contradiction.
          { destruct safety' as [Hvalid' ?].
            split; [|erewrite gsoThreadRes; eauto].
(*            destruct (alloc m' 0 0) eqn: Halloc.
            simpl; apply nextblock_alloc in Halloc as ->.
*)
            eapply val_inject_incr, Hvalid'.
            hnf in Hperm; subst; simpl.
            apply flat_inj_incr. apply Pos.le_refl. }
      - intros j cntj.
        destruct (eq_dec i j) as [<-|ne]; REWR.
        specialize (wellformed j cntj). auto.
      - intros more j cntj q.
        destruct (eq_dec i j) as [<-|ne]; REWR.
        + simpl; eauto.
        + intros Ej. specialize (unique more j cntj q Ej). auto.
*
  inv Htstep.
      rename m' into m.
      pose proof safety as safety'.
      specialize (safety i cnti tt). rewr (getThreadC i tp cnti) in safety.
      destruct safety as (c_new_ & E_c_new & safety).
      getThread_inv; congruence.
*
  jmstep_inv. getThread_inv; congruence.
*
  inv Htstep. 
      rename m' into m.
      pose proof safety as safety'.
      specialize (safety i cnti tt). rewr (getThreadC i tp cnti) in safety.
      destruct safety as (c_new_ & E_c_new & safety).
      getThread_inv; congruence.
*
  jmstep_inv; getThread_inv; congruence.
(* *
  jmstep_inv; getThread_inv; congruence.*)
*
  contradiction Htid.
Qed. (* Lemma preservation_Kinit *)

  (* We prove preservation for most states of the machine, including
  Kblocked at acquire, but preservation does not hold for
  makelock or release, so, we make an exception and will use safety induction in
  the safety theorem.  Because it's faster to prove safety induction,
  we don't prove preservation for freelock and spawn, either, because
  we did those two last. *)
  Theorem preservation ge Gamma n state state' :
    ~ blocked_at_external state CREATE ->
    ~ blocked_at_external state MKLOCK ->
    ~ blocked_at_external state FREE_LOCK ->
    ~ blocked_at_external state UNLOCK ->
    state_step state state' ->
    state_invariant Jspec' Gamma (S n) state ->
    state_bupd(ge := ge) (state_invariant Jspec' Gamma n) state' \/
    state_bupd(ge := ge) (state_invariant Jspec' Gamma (S n)) state'.
  Proof.
    intros not_spawn not_makelock not_freelock not_release STEP.
    inversion STEP as [ | m m' tr tr' sch sch' tp tp' jmstep E E']. right. assert (exists PHI, mem_compatible_with jstate0 m PHI) as [? HPHI] by (inv H1; eauto). now apply state_bupd_intro'.
    (* apply state_invariant_S *)
    subst state state'; clear STEP.
    intros INV.
    inversion INV as [m0 tr0 sch0 tp0 Phi lev envcoh compat extcompat sparse lock_coh safety wellformed unique E].
    subst m0 sch0 tp0.

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
      right; apply state_bupd_intro'.
      simpl.

      assert (i :: sch <> sch) by (clear; induction sch; congruence).
      inversion jmstep; subst; simpl in *; try tauto;
        unfold containsThread, is_true in *;
        try congruence.
      apply state_invariant_c with (PHI := Phi) (mcompat := compat); auto.
      (* invariant about "only one Krun and it is scheduled": the
       bad schedule case is not possible *)
      intros H0 i0 cnti q H1.
      exfalso.
      specialize (unique H0 i0 cnti q H1).
      destruct unique as [sch' unique]; injection unique as <- <- .
      contradiction Htid.
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
                   corestep (juicy_core_sem (cl_core_sem ge)) ci jmi ci' jmi'
                   /\ forall ora, jm_bupd ora (jsafeN Jspec' ge n ora ci') jmi').
        {
          specialize (safety i cnti).
          pose proof (safety tt) as safei.
          unfold JSem in *. rewrite Eci in safei, safety.
          subst.
          inversion safei as [ | ? ? ? ? c' m'' step safe H H2 H3 H4 | | ]; subst.
          2: now match goal with H : j_at_external _ _ _ = _ |- _ => inversion H end.
          2: now match goal with H : halted _ _ _ |- _ => inversion H end.
          exists c', m''. split; [ apply step | ].
          revert step safety safe; clear.
          generalize (jm_ cnti compat).
          generalize (State ve te k).
          unfold jsafeN.
          intros c j step safety safe ora.
          eapply semax_lemmas.jsafe_corestep_forward.
          - apply step.
          - apply safety.
        }

        destruct next as (ci' & jmi' & stepi & safei').
        pose (tp'' := updThread i tp cnti (Krun ci') (m_phi jmi')).
        pose (tp''' := age_tp_to (level jmi') tp').
        pose (cm' := (m_dry jmi', (i :: sch, tp'''))).

        (* now, the step that has been taken in jmstep must correspond
        to this cm' *)
        inversion jmstep; subst; try inversion HschedN; subst tid; try congruence.

        - (* not in Kinit *)
         
          inv Htstep.
          simpl in Hinitial.
          getThread_inv. congruence.

        - (* not in Kresume *)
          inv Htstep. getThread_inv. congruence.

        - (* here is the important part, the corestep *)
          jmstep_inv.
          assert (En : level Phi = S n) by auto. (* will be in invariant *)
          left. (* consuming one step of level *)
          eapply invariant_thread_step; eauto.
          + apply mem_cohere_step.
          + apply personal_mem_equiv_spec.
          + apply Jspec'_hered.
          + apply Jspec'_juicy_mem_equiv.
          + eapply lock_coh_bound; eauto.
          + exact_eq Hcorestep.
            rewrite Ejuicy_sem.
            unfold jm_.
            do 2 f_equal.
            apply proof_irr.
          + rewrite Ejuicy_sem in Hcorestep.
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
          inv Htstep. getThread_inv.
          injection H as <-.
          evar (mx: Memory.mem).
          assert (H: at_external (@semSem (ClightSemanticsForMachines.Clight_newSem ge)) (State ve te k) mx = Some X). {
            simpl in *.
            subst mx; eassumption.
          }
          erewrite corestep_not_at_external in H. discriminate.
          subst mx.
          eapply stepi.

        - (* not in Kblocked *)
          jmstep_inv.
          all: getThread_inv.
          all: congruence.

(*        - (* not halted *)
          jmstep_inv. contradiction.*)
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
          pose proof corestep_not_at_external _ _ _ _ _ Hcorestep.
          rewrite Ejuicy_sem in H.
          discriminate.

        - (* we are at an at_ex now *)
          jmstep_inv. getThread_inv.
          injection H as <-.
          rename m' into m.
          right. (* no aging *)

          unfold state_bupd.
          match goal with |- tp_bupd _ ?tp => set (tp' := tp) end.
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

          eapply (state_bupd_intro' _ _ _ (_, (_, _, _))), state_invariant_c with (PHI := Phi) (mcompat := compat').
          + assumption.

          + (* env_coherence *)
            assumption.

          + (* external coherence *)
            auto.

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
              REWR. REWR.
              specialize (safety i cnti ora).
              unfold JSem in *. rewrite Eci in safety.
              eapply Jspec'_jsafe_phi in safety. 2:reflexivity.
              replace cnti with ctn in safety by apply proof_irr.
              substwith cnti0' ctn.
              apply safety.
            * assert (cnti0 : containsThread tp i0) by auto.
              unfold tp'.
              rewrite <- (@gsoThreadCC _ _ _ _ _ tp ii0 ctn cnti0).
              specialize (safety i0 cnti0 ora).
              clear -safety.
              unfold JSem in *.
              substwith cnti0' cnti0.
              destruct (getThreadC i0 tp cnti0).
              -- unfold jm_ in *.
                 erewrite personal_mem_ext.
                 ++ apply safety.
                 ++ REWR.
              -- REWR.
              -- REWR.
              -- destruct safety as (? & q_new & Einit & safety).
                 split; auto.
                 exists q_new; split; auto.

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
              rewrite <- (@gsoThreadCC _ _ _ _ _ tp ii0 ctn cnti0).
              specialize (wellformed i0 cnti0).
              unfold JSem in *.
              destruct (getThreadC i0 tp cnti0).
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
              rewrite <- (@gsoThreadCC _ _ _ _ _ tp ii0 ctn cnti0) in Eci0.
              destruct (unique notalone i cnti _ Eci).
              destruct (unique notalone i0 cnti0 q Eci0).
              congruence.

        - (* not in Kblocked *)
          jmstep_inv.
          all: getThread_inv.
          all: congruence.

(*        - (* not halted *)
          jmstep_inv. contradiction.*)
      } (* end of Krun (at_ex c) -> Kblocked c *)
    } (* end of Krun *)

    (* thread[i] is in Kblocked *)
    { (* only one possible jmstep, in fact divided into 6 sync steps *)
      inversion jmstep; try inversion HschedN; subst tid;
      try solve
          [ try congruence; try subst;
            try solve [jmstep_inv; getThread_inv; congruence ] ].
      subst.

      simpl schedSkip in *.
      clear HschedN.
      (* left (* TO BE CHANGED *). *)
      (* left (* we need aging, because we're using the safety of the call *). *)
      assert (Htid = cnti) by apply proof_irr. subst Htid.
      assert (Ephi : 0 = 0 -> level (getThreadR _ _ cnti) = S n). {
        rewrite getThread_level with (Phi0 := Phi). auto. apply compat.
      }
      assert (El : (0 = 0 -> level (getThreadR _ _ cnti) - 1 = n)%nat) by omega.

      pose proof mem_compatible_with_age _ compat (n := n) as compat_aged.

      pose proof lockSet_Writable_updLockSet_updThread.
      pose proof mem_cohere'_store.
      pose proof personal_mem_equiv_spec.
      pose proof Jspec'_juicy_mem_equiv CS ext_link.
      pose proof Jspec'_hered CS ext_link.

      jmstep_inv. all: try autospec Ephi; try autospec El; try rewrite El.
      (* pose (compat_ := mem_compatible_with tp_ m_ (age_to n Phi)). *)
      (* match goal with |- _ _ _ (?M, _, (_, ?TP)) => set (tp_ := TP); set (m_ := M) end. *)

      - (* the case of acquire *)
        left.
        assert (Hcompatible = Hcmpt) by apply proof_irr. subst Hcompatible.
        rewrite El in *.
        apply state_bupd_intro'.
        eapply preservation_acquire with (Phi := Phi); eauto.
      - (* the case of release *)
        exfalso; apply not_release.
        repeat eexists; eauto.

      - (* the case of spawn *)
        left.
        simpl (m_phi _) in *.
        (* disregarding the case of makelock by hypothesis *)
        exfalso; apply not_spawn.
        repeat eexists; eauto.

      - (* the case of makelock *)
        left.
        simpl (m_phi _) in *.
        (* disregarding the case of makelock by hypothesis *)
        exfalso; apply not_makelock.
        repeat eexists; eauto.

      - (* the case of freelock *)
        left.
        simpl (m_phi _) in *.
        (* disregarding the case of makelock by hypothesis *)
        exfalso; apply not_freelock.
        repeat eexists; eauto.

      - (* the case of acq-fail *)
        right.
        eapply state_bupd_intro', state_invariant_c with (PHI := Phi); eauto.
        apply no_Krun_unique_Krun.
        eapply unique_Krun_no_Krun; eauto.
        setoid_rewrite Eci. congruence.
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

      apply state_inv_upd1 with (PHI := Phi) (mcompat := compat').
      + (* level *)
        assumption.

      + (* env_coherence *)
        assumption.

      + (* external coherence *)
        assumption.

      + (* sparsity *)
        assumption.

      + (* lock coherence *)
        unfold lock_coherence' in *.
        exact_eq lock_coh.
        f_equal.
        f_equal.
        apply proof_irr.

      + assert (ctn = cnti) by apply proof_irr; subst cnti.
        exists i, ctn; split.
        * rewrite gssThreadCC.
          eexists; split; eauto.
          specialize (safety i ctn tt).
          unfold JSem in *. rewrite Eci in safety.
          intros ? HC J.
          unshelve erewrite gThreadCR in J; auto.
          getThread_inv. injection H as -> -> .
          setoid_rewrite ClightSemanticsForMachines.CLN_msem in Hafter_external.
          specialize (safety _ Hafter_external (jm_ ctn compat)).
          erewrite getThread_level in J by apply compat.
          substwith Htid ctn.
          rewrite m_phi_jm_ in safety; specialize (safety eq_refl) as (jm' & ? & Hupd & safety); eauto.
          { rewrite m_phi_jm_, level_jm_; eauto. }
          rewrite level_jm_ in H.
          eexists; split; [unshelve erewrite gThreadCR, getThread_level by apply compat; eauto|].
          destruct Hupd as (Hd & Hl & Hr).
          exists (m_phi jm').
          assert (resource_at (m_phi jm') =
                  resource_at (getThreadR i (updThreadC i tp ctn (Krun c')) ctn)) as Hr'.
          { unshelve erewrite gThreadCR; auto. }
          exists Hr'; split; [unshelve erewrite gThreadCR; auto|].
          split; auto; intros [].
          exact_eq safety; simpl; f_equal; f_equal.
          apply juicy_mem_ext; auto.
          rewrite Hd; simpl.
          apply juicyRestrict_ext; rewrite Hr; auto.
        * repeat intro.
          assert (cnti0 : containsThread tp j) by auto.
          assert (i <> j) as ii0 by auto.
          rewrite <- (@gsoThreadCC _ _ _ _ _ tp ii0 ctn cnti0).
          specialize (safety _ cnti0 ora).
          clear -safety.
          unfold JSem in *.
          destruct (getThreadC _ tp cnti0).
          -- unfold jm_ in *.
             erewrite personal_mem_ext.
             ++ apply safety.
             ++ apply (gThreadCR ctn).
          -- REWR.
          -- REWR.
          -- destruct safety as (? & q_new & Einit & safety).
              split; auto.
              exists q_new; split; auto. REWR.

      + (* wellformed. *)
        intros i0 cnti0'.
        destruct (eq_dec i i0) as [ii0 | ii0].
        * subst i0.
          rewrite gssThreadCC.
          constructor.
        * assert (cnti0 : containsThread tp i0) by auto.
          rewrite <- (@gsoThreadCC _ _ _ _ _ tp ii0 ctn cnti0).
          specialize (wellformed i0 cnti0).
          unfold JSem in *.
          destruct (getThreadC i0 tp cnti0).
          -- constructor.
          -- apply wellformed.
          -- apply wellformed.
          -- constructor.

      + (* uniqueness *)
        intros notalone i0 cnti0' q Eci0.
        pose proof (unique notalone i0 cnti0' q) as unique'.
        simpl; destruct (eq_dec i i0) as [ii0 | ii0].
        * subst i0.
          eauto.
        * assert (cnti0 : containsThread tp i0) by auto.
          clear safety wellformed.
          rewrite <- (@gsoThreadCC _ _ _ _ _ tp ii0 ctn cnti0) in Eci0.
          destruct (unique notalone i0 cnti0 q Eci0).
          congruence.
    }

    (* thread[i] is in Kinit *)
    {
      edestruct preservation_Kinit; eauto; [left | right]; apply state_bupd_intro'; auto.
    }
  Qed.

End Preservation.
