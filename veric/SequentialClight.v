Require Import VST.sepcomp.semantics.

Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clight_lemmas.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.veric.Clight_evsem.
Require Import VST.veric.SeparationLogic.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_mem.
Require VST.veric.NullExtension.
(*Require Import VST.veric.Clight_sim.*)
Require Import VST.veric.SeparationLogicSoundness.
Require Import VST.sepcomp.extspec.
Require Import VST.msl.msl_standard.

Import VericSound.
Import VericMinimumSeparationLogic.
Import VericMinimumSeparationLogic.CSHL_Def.
Import VericMinimumSeparationLogic.CSHL_Defs.
Import Clight.

Definition ignores_juice Z (J: external_specification juicy_mem external_function Z) : Prop :=
  (forall e t b tl vl x jm jm',
     m_dry jm = m_dry jm' ->
    ext_spec_pre J e t b tl vl x jm ->
    ext_spec_pre J e t b tl vl x jm') /\
 (forall ef t b ot v x jm jm',
     m_dry jm = m_dry jm' -> 
    ext_spec_post J ef t b ot v x jm ->
    ext_spec_post J ef t b ot v x jm') /\
 (forall v x jm jm',
     m_dry jm = m_dry jm' -> 
     ext_spec_exit J v x jm ->
     ext_spec_exit J v x jm').

Import VST.veric.compcert_rmaps.R.

Definition mem_evolve (m m': mem) : Prop :=
   (* dry version of resource_decay *)
 forall loc,
 match access_at m loc Cur, access_at m' loc Cur with
 | None, None => True
 | None, Some Freeable => True
 | Some Freeable, None => True
 | Some Writable, Some p' => p' = Writable
 | Some p, Some p' => p=p' /\ access_at m loc Max = access_at m' loc Max
 | _, _ => False
 end.

#[(*export, after Coq 8.13*)global] Instance mem_evolve_refl : RelationClasses.Reflexive mem_evolve.
Proof.
  repeat intro.
  destruct (access_at x loc Cur); auto.
  destruct p; auto.
Qed.

Lemma access_Freeable_max : forall m l, access_at m l Cur = Some Freeable -> access_at m l Max = Some Freeable.
Proof.
  intros.
  pose proof (access_cur_max m l) as Hperm; rewrite H in Hperm; simpl in Hperm.
  destruct (access_at m l Max); try contradiction.
  inv Hperm; auto.
Qed.

#[(*export, after Coq 8.13*)global] Instance mem_evolve_trans : RelationClasses.Transitive mem_evolve.
Proof.
  repeat intro.
  specialize (H loc); specialize (H0 loc).
  destruct (access_at x loc Cur) eqn: Hx; [destruct p|]; destruct (access_at y loc Cur) eqn: Hy; subst; auto; try contradiction.
  - destruct H; subst.
    destruct (access_at z loc Cur); congruence.
  - destruct (access_at z loc Cur) eqn: Hz; auto.
    destruct p; try contradiction.
    apply access_Freeable_max in Hx; apply access_Freeable_max in Hz.
    rewrite Hx, Hz; auto.
  - destruct H; subst.
    destruct (access_at z loc Cur); congruence.
  - destruct H; subst.
    destruct (access_at z loc Cur); congruence.
  - destruct p; try contradiction.
    destruct (access_at z loc Cur); auto.
    destruct H0; subst; auto.
Qed.

Definition ext_spec_mem_evolve (Z: Type) 
  (D: external_specification mem external_function Z) :=
 forall ef w b tl vl ot v z m z' m',
    ext_spec_pre D ef w b tl vl z m ->
    ext_spec_post D ef w b ot v z' m' ->
    mem_evolve m m'.

Definition juicy_dry_ext_spec (Z: Type)
   (J: external_specification juicy_mem external_function Z)
   (D: external_specification mem external_function Z)
   (dessicate: forall ef jm, ext_spec_type J ef -> ext_spec_type D ef) :=
  (forall e t t' b tl vl x jm,
    dessicate e jm t = t' ->
    (ext_spec_pre J e t b tl vl x jm ->
    ext_spec_pre D e t' b tl vl x (m_dry jm))) /\
 (forall ef t t' b ot v x jm0 jm,
    (exists tl vl x0, dessicate ef jm0 t = t' /\ ext_spec_pre J ef t b tl vl x0 jm0) ->
    (level jm <= level jm0)%nat ->
    resource_at (m_phi jm) = resource_fmap (approx (level jm)) (approx (level jm)) oo juicy_mem_lemmas.rebuild_juicy_mem_fmap jm0 (m_dry jm) ->
    ghost_of (m_phi jm) = Some (ghost_PCM.ext_ghost x, compcert_rmaps.RML.R.NoneP) :: ghost_fmap (approx (level jm)) (approx (level jm)) (tl (ghost_of (m_phi jm0))) ->
    (ext_spec_post D ef t' b ot v x (m_dry jm) ->
     ext_spec_post J ef t b ot v x jm)) /\
 (forall v x jm,
     ext_spec_exit J v x jm <->
     ext_spec_exit D v x (m_dry jm)).

Definition juicy_dry_ext_spec_make (Z: Type) 
   (J: external_specification juicy_mem external_function Z) :
   external_specification mem external_function Z.
destruct J.
apply Build_external_specification with ext_spec_type.
intros e t b tl vl x m.
apply (forall jm, m_dry jm = m -> (* external ghost matches x -> *) ext_spec_pre e t b tl vl x jm).
intros e t b ot v x m.
apply (forall jm, m_dry jm = m -> ext_spec_post e t b ot v x jm).
intros v x m.
apply (forall jm, m_dry jm = m -> ext_spec_exit v x jm).
Defined.


Definition dessicate_id Z 
   (J: external_specification juicy_mem external_function Z) :
   forall ef (jm : juicy_mem), ext_spec_type J ef -> 
       ext_spec_type (juicy_dry_ext_spec_make Z J) ef.
intros.
destruct J; simpl in *. apply X.
Defined.

Lemma jdes_make_lemma:
  forall Z J, ignores_juice Z J ->
    juicy_dry_ext_spec Z J (juicy_dry_ext_spec_make Z J)
     (dessicate_id Z J).
Proof.
intros.
destruct H as [? [? ?]], J; split; [ | split3]; simpl in *; intros; auto.
-
subst t'.
eapply H. symmetry; eassumption.  auto.
-
destruct H2 as (? & ? & ? & ? & ?).
subst t'.
eapply H0; auto.
-
eapply H1. symmetry; eassumption. auto.
Qed.

Definition mem_rmap_cohere m phi :=
  contents_cohere m phi /\
  access_cohere m phi /\
  max_access_cohere m phi /\ alloc_cohere m phi.

Lemma age_to_cohere:
 forall m phi n,
    mem_rmap_cohere m phi -> mem_rmap_cohere m (age_to.age_to n phi).
Proof.
intros.
destruct H as [? [? [? ?]]].
split; [ | split3]; hnf; intros.
-
hnf in H.
rewrite age_to_resource_at.age_to_resource_at in H3.
destruct (phi @ loc) eqn:?H; inv H3.
destruct (H _ _ _ _ _ H4); split; subst; auto.
-
rewrite age_to_resource_at.age_to_resource_at .
specialize (H0 loc).
rewrite H0.
destruct (phi @ loc); simpl; auto.
-
rewrite age_to_resource_at.age_to_resource_at .
specialize (H1 loc).
destruct (phi @ loc); simpl; auto.
-
rewrite age_to_resource_at.age_to_resource_at .
specialize (H2 loc H3).
rewrite H2.
reflexivity.
Qed.

Lemma set_ghost_cohere:
 forall m phi g H,
    mem_rmap_cohere m phi -> 
   mem_rmap_cohere m (initial_world.set_ghost phi g H).
Proof.
intros.
unfold initial_world.set_ghost.
rename H into Hg. rename H0 into H.
destruct H as [? [? [? ?]]].
split; [ | split3]; hnf; intros.
-
hnf in H.
rewrite resource_at_make_rmap in H3.
destruct (phi @ loc) eqn:?H; inv H3.
destruct (H _ _ _ _ _ H4); split; subst; auto.
-
rewrite resource_at_make_rmap.
specialize (H0 loc).
rewrite H0.
destruct (phi @ loc); simpl; auto.
-
rewrite resource_at_make_rmap.
specialize (H1 loc).
destruct (phi @ loc); simpl; auto.
-
rewrite resource_at_make_rmap.
specialize (H2 loc H3).
rewrite H2.
reflexivity.
Qed.

Lemma mem_evolve_cohere:
  forall jm m' phi',
   mem_evolve (m_dry jm) m' ->
   compcert_rmaps.RML.R.resource_at phi' =
     juicy_mem_lemmas.rebuild_juicy_mem_fmap jm m' ->
   mem_rmap_cohere m' phi'.
Proof.
intros.
destruct jm.
simpl in *.
unfold  juicy_mem_lemmas.rebuild_juicy_mem_fmap in H0.
simpl in H0.
split; [ | split3].
-
hnf; intros; specialize (H loc).
rewrite (JMaccess loc) in *.
rewrite H0 in *; clear H0; simpl in *.
destruct (phi @ loc) eqn:?H.
simpl in H. if_tac in H.
if_tac in H1.
inv H1; auto.
inv H1.
if_tac in H1.
inv H1; auto.
inv H1.
destruct k; simpl in *.
destruct (perm_of_sh sh0) as [[ | | | ] | ] eqn:?H; try contradiction ;auto.
destruct (access_at m' loc Cur) as [[ | | | ] | ]  eqn:?H; try contradiction; try discriminate; auto.
if_tac in H1; inv H1; auto.
if_tac in H1; inv H1; auto.
if_tac in H1; inv H1; auto.
if_tac in H1; inv H1; auto.
if_tac in H1; inv H1; auto.
if_tac in H1; inv H1; auto.
if_tac in H1; inv H1; auto.
inv H1; auto.
inv H1; auto.
inv H1; auto.
-
hnf; intros; specialize (H loc).
rewrite H0; clear H0.
rewrite (JMaccess loc) in *.
destruct (phi @ loc) eqn:?H.
simpl in H. if_tac in H.
destruct (access_at m' loc Cur) as [[ | | | ] | ] eqn:?H; try contradiction; try discriminate; simpl; auto.
unfold perm_of_sh. rewrite if_true by auto. rewrite if_true by auto. auto.
subst. rewrite if_true by auto; auto.
destruct (access_at m' loc Cur) as [[ | | | ] | ] eqn:?H; try contradiction; try discriminate; simpl; auto.
destruct H; discriminate.
destruct H; discriminate.
destruct H; discriminate.
rewrite if_false by auto; auto.
destruct k; simpl in *; auto.
destruct (perm_of_sh sh) as [[ | | | ] | ] eqn:?H; try contradiction ;auto.
destruct (access_at m' loc Cur) as [[ | | | ] | ]  eqn:?H; try solve [contradiction]; try discriminate; auto.
destruct H; discriminate.
destruct H; discriminate.
destruct H; discriminate.
simpl. rewrite if_true; auto.
destruct (access_at m' loc Cur) as [[ | | | ] | ]  eqn:?H; try solve [contradiction]; try discriminate; auto.
destruct (access_at m' loc Cur) as [[ | | | ] | ]  eqn:?H; try solve [contradiction]; try discriminate; auto.
destruct (access_at m' loc Cur) as [[ | | | ] | ]  eqn:?H; try solve [contradiction]; try discriminate; auto.
destruct H; discriminate.
destruct H; discriminate.
destruct H; discriminate.
elimtype False; clear - r H1.
unfold perm_of_sh in H1. if_tac in H1. if_tac in H1; inv H1.
rewrite if_true in H1 by auto. inv H1.
destruct (access_at m' loc Cur) as [[ | | | ] | ]  eqn:?H; try solve [contradiction]; try discriminate; auto.
unfold perm_of_sh in H1. if_tac in H1. if_tac in H1; inv H1.
rewrite if_true in H1 by auto. inv H1.
unfold perm_of_sh in H1. if_tac in H1. if_tac in H1; inv H1.
rewrite if_true in H1 by auto.
inv H1.
destruct (access_at m' loc Cur) as [[ | | | ] | ]  eqn:?H; try solve [contradiction]; try discriminate; auto.
destruct H; discriminate.
destruct H; discriminate.
destruct H; discriminate.
destruct (access_at m' loc Cur) as [[ | | | ] | ]  eqn:?H; try solve [contradiction]; try discriminate; auto.
destruct H; discriminate.
destruct H; discriminate.
destruct H; discriminate.
destruct (access_at m' loc Cur) as [[ | | | ] | ]  eqn:?H; try solve [contradiction]; try discriminate; auto.
simpl in H; destruct H; discriminate.
simpl in H; destruct H; discriminate.
simpl in H; destruct H; discriminate.
-
hnf; intros; specialize (H loc).
rewrite H0; clear H0.
rewrite (JMaccess loc) in *.
destruct (phi @ loc) eqn:?H.
simpl in H. if_tac in H.
destruct (access_at m' loc Cur) as [[ | | | ] | ] eqn:?H; try contradiction; try discriminate; simpl; auto.
eapply perm_order''_trans; [apply access_cur_max | ].
rewrite H2.
unfold perm_of_sh. rewrite if_true by auto. rewrite if_true by auto. constructor.
subst sh. rewrite if_true by auto.
apply po_None.
destruct (access_at m' loc Cur) as [[ | | | ] | ] eqn:?H; try contradiction; try discriminate; simpl; auto.
destruct H; discriminate.
destruct H; discriminate.
destruct H; discriminate.
rewrite if_false by auto.
eapply perm_order''_trans; [apply access_cur_max | ].
rewrite H2. constructor.
destruct k; simpl in *; auto.
destruct (perm_of_sh sh) as [[ | | | ] | ] eqn:?H; try contradiction ;auto.
eapply perm_order''_trans; [apply access_cur_max | ].
destruct (access_at m' loc Cur). destruct H; subst.
match goal with |- Mem.perm_order'' _ ?A =>
  destruct A; try constructor
end.
simpl.
rewrite if_true by auto. auto.
eapply perm_order''_trans; [apply access_cur_max | ].
destruct (access_at m' loc Cur). destruct H; subst.
rewrite if_true. simpl. rewrite H1. apply perm_refl.
clear - r H1.
unfold perm_of_sh in H1.
if_tac in H1. if_tac in H1. inv H1; constructor.
inv H1; constructor.
rewrite if_true in H1 by auto. inv H1; constructor.
contradiction.
eapply perm_order''_trans; [apply access_cur_max | ].
destruct (access_at m' loc Cur). destruct H; subst.
rewrite if_true. simpl. rewrite H1. apply perm_refl.
clear - r H1.
unfold perm_of_sh in H1.
if_tac in H1. if_tac in H1. inv H1; constructor.
inv H1; constructor.
rewrite if_true in H1 by auto. inv H1; constructor.
contradiction.
eapply perm_order''_trans; [apply access_cur_max | ].
destruct (access_at m' loc Cur). destruct H; subst.
rewrite if_true. simpl. rewrite H1. apply perm_refl.
clear - r H1.
unfold perm_of_sh in H1.
if_tac in H1. if_tac in H1. inv H1; constructor.
inv H1; constructor.
rewrite if_true in H1 by auto. inv H1; constructor.
contradiction.
eapply perm_order''_trans; [apply access_cur_max | ].
destruct (access_at m' loc Cur). destruct p0; try contradiction.
match goal with |- Mem.perm_order'' _ ?A =>
  destruct A; try constructor
end.
elimtype False.
clear - H1 r.
unfold perm_of_sh in H1.
if_tac in H1. if_tac in H1. inv H1; constructor.
inv H1; constructor.
rewrite if_true in H1 by auto. inv H1; constructor.
destruct (access_at m' loc Cur); try contradiction.
destruct H; subst p0.
specialize (JMmax_access loc).
rewrite H0 in JMmax_access.
simpl in JMmax_access.
unfold max_access_at in *.
rewrite <- H1. auto.
destruct (access_at m' loc Cur); try contradiction.
destruct H; subst p0.
specialize (JMmax_access loc).
rewrite H0 in JMmax_access.
simpl in JMmax_access.
unfold max_access_at in *.
rewrite <- H1. auto.
simpl in H.
destruct (access_at m' loc Cur); try contradiction.
destruct H; subst.
simpl.
specialize (JMmax_access loc).
rewrite H0 in JMmax_access.
simpl in JMmax_access.
unfold max_access_at in *.
rewrite <- H1. auto.
-
hnf; intros; specialize (H loc).
rewrite H0; clear H0.
specialize (JMalloc loc).
rewrite (JMaccess loc) in *.
destruct (phi @ loc) eqn:?H.
simpl in H. if_tac in H.
destruct loc as [b z]. 
rewrite nextblock_access_empty in *by auto.
subst.
simpl.
f_equal. apply proof_irr.
destruct loc as [b z]. 
rewrite nextblock_access_empty in * by auto.
contradiction.
destruct loc as [b z]. 
rewrite nextblock_access_empty in * by auto.
simpl.
destruct k; auto; try contradiction H.
simpl in H.
destruct loc as [b z]. 
rewrite nextblock_access_empty in * by auto.
contradiction.
Qed.

Lemma mem_step_evolve : forall m m', mem_step m m' -> mem_evolve m m'.
Proof.
  induction 1; intros loc.
  - rewrite <- (storebytes_access _ _ _ _ _ H); destruct (access_at m loc Cur); auto.
    destruct p; auto.
  - destruct (adr_range_dec (b', lo) (hi - lo) loc).
    + destruct (alloc_dry_updated_on _ _ _ _ _ loc H) as [->]; auto.
      pose proof (Mem.alloc_result _ _ _ _ _ H); subst.
      destruct loc, a; subst.
      rewrite nextblock_access_empty; auto; lia.
    + eapply alloc_dry_unchanged_on in n as [Heq _]; eauto.
      rewrite <- Heq.
      destruct (access_at m loc Cur); auto.
      destruct p; auto.
  - revert dependent m; induction l; simpl; intros.
    + inv H; destruct (access_at m' loc Cur); auto.
      destruct p; auto.
    + destruct a as ((b, lo), hi).
      destruct (Mem.free m b lo hi) eqn: Hfree; inv H.
      apply IHl in H1.
      destruct (adr_range_dec (b, lo) (hi - lo) loc).
      * destruct loc, a; subst.
        eapply free_access in Hfree as [Hfree H2]; [rewrite Hfree | lia].
        pose proof (access_cur_max m0 (b0, z)) as Hperm; rewrite H2 in Hperm; simpl in Hperm.
        destruct (access_at m0 (b0, z) Cur); try contradiction.
        destruct (access_at m' (b0, z) Cur) eqn: Hm'; auto.
        destruct p; try contradiction.
        apply access_Freeable_max in Hfree; apply access_Freeable_max in Hm'; rewrite Hfree, Hm'; auto.
      * destruct loc; eapply free_nadr_range_eq in n as [->]; eauto.
  - eapply mem_evolve_trans; eauto.
Qed.

(* Require Import VST.veric.resource_decay_join.

We almost certainly want event semantics here. But one more try. *)

(*Lemma resource_decay_join_rebuild b jm jm' phi2 jm3 m :
  (forall loc, (fst loc >= b)%positive -> phi2 @ loc = NO Share.bot shares.bot_unreadable) ->
  resource_decay b (m_phi jm) (m_phi jm') ->
  ghost_of (m_phi jm') = own.ghost_approx jm' (ghost_of (m_phi jm)) ->
  sepalg.join (m_phi jm) phi2 (m_phi jm3) -> mem_step (m_dry jm) (m_dry jm') -> mem_step (m_dry jm3) m -> Mem.extends (m_dry jm) (m_dry jm3) -> Mem.extends (m_dry jm') m ->
    sepalg.join (m_phi jm') (age_to.age_to (level jm') phi2) (proj1_sig (juicy_mem_lemmas.rebuild_juicy_mem_rmap jm3 m)) /\
    resource_decay b (m_phi jm3) (proj1_sig (juicy_mem_lemmas.rebuild_juicy_mem_rmap jm3 m)).
Proof.
  intros bound [lev rd] Hg J Hev Hev' Hmem Hmem'.
  assert (lev12 : level (m_phi jm) = level phi2) by (apply join_level in J as []; congruence).

  set (phi2' := age_to.age_to (level jm') phi2).
  unfold resource_decay in *.

  set (phi3' := proj1_sig (juicy_mem_lemmas.rebuild_juicy_mem_rmap jm3 m)).

  induction Hev'.
  - pose (storebytes_juicy_mem _ _ _ _ _ H).

  assert (DESCR : forall loc,
             sepalg.join (m_phi jm' @ loc) (phi2' @ loc) (phi3' @ loc) /\
               resource_decay_at b (level jm') (m_phi jm @ loc) (phi3' @ loc) (fst loc) /\
               resource_fmap (approx (level jm')) (approx (level jm')) (phi3' @ loc) = phi3' @ loc
         ).
  {
    intros loc.
    specialize (rd loc).
    apply compcert_rmaps.RML.resource_at_join with (loc := loc) in J.

    unfold phi2'; clear phi2'; rewrite age_to_resource_at.age_to_resource_at.
    unfold phi3'; clear phi3'; unfold juicy_mem_lemmas.rebuild_juicy_mem_rmap; rewrite resource_at_make_rmap.
    unfold juicy_mem_lemmas.rebuild_juicy_mem_fmap.
    destruct jm as [m1 phi1 contents1 access1 max1 alloc1], jm' as [m1' phi1' contents1' access1' max1' alloc1'],
      jm3 as [m3 phi3 contents3 access3 max3 alloc3]; simpl in *.
    specialize (access1 loc); specialize (max1 loc); specialize (alloc1 loc);
    specialize (access1' loc); specialize (max1' loc); specialize (alloc1' loc);
    specialize (access3 loc); specialize (max3 loc); specialize (alloc3 loc).
    specialize (Hev loc); specialize (Hev' loc). rewrite access3 in Hev'; rewrite access1, access1' in Hev.
    autospec bound. destruct loc as (b1, ofs).

    destruct rd as [nn [E1 | [(sh & rsh & v & v' & E1 & E1') | [(pos & v & E1') | (v & pp & E1 & E1')]]]].

    - rewrite <-E1 in Hev, access1', max1', alloc1' |- *.
      split;[|split;[split|]].
      + inversion J; simpl. rewrite <- H0 in *; rewrite <- H2 in *; simpl in *.
        if_tac; try constructor; auto.
        edestruct (Mem.perm_extends_inv m1') as [Hnot | Hnot]; eauto.
        { rewrite perm_access; eauto. }
        { rewrite perm_access in Hnot. rewrite access1' in Hnot; simpl in Hnot.
          if_tac in Hnot; inv Hnot. }
        rewrite perm_access in Hnot. if_tac in max1'; try contradiction; subst. rewrite max1' in Hnot.
if_tac in Hev'. edestruct Hperm' as [Hnot | Hnot]; eauto. { if_tac in Hnot; inv Hnot. }
        destruct (access_at m' (b1, ofs) Max) eqn: Hmax. { contradiction Hnot; constructor. }
        { 
 if_tac in Hmem; subst. apply ghosts.join_Bot in RJ as []; subst. rewrite if_true in Hperm by auto; simpl in Hperm.
        Search Mem.extends "inv".
 rewrite if_true in Hmem by admit.  Check Mem.extends'.
      + intros pos; autospec bound; autospec nn. rewrite bound in *; rewrite nn in *.
        inv J. apply NO_ext. apply bot_identity in RJ; auto.
      + left. auto.
      + apply resource_fmap_approx_idempotent.

    -  rewrite E1'.
      apply res_join'_spec in J.
      inversion J; rewr (phi1 @ loc) in E1; simpl in *.
      all:try congruence.
      + injection E1; intros; subst.
        exists (YES sh3 rsh3 (VAL v') NoneP).
        split;[|split;[split|]].
        * constructor; assumption.
        * intros pos; autospec bound; autospec nn. rewrite bound in *; rewrite nn in *.
          congruence.
        * right. left. simpl. exists sh3, rsh3, v, v'. split3; auto; try congruence.
          clear - H2 E1''. eapply join_writable01; eauto.
        * simpl. f_equal.
      + injection E1; intros; subst.
        rewr (phi1 @ loc) in J.
        apply res_join'_spec_inv in J.
        apply YES_join_full in J.
        exfalso. breakhyps. auto. 

    - autospec nn.
      autospec bound.
      rewrite nn in *.
      rewrite bound in *.
      apply res_join'_spec in J.
      inv J; simpl.
      exists (phi1' @ loc).
      rewrite E1'.
      split;[|split;[split|]].
      + constructor. eauto.
      + intros _. apply NO_ext.
        apply bot_identity in H2; auto.
      + right. right. left. eauto.
      + simpl. unfold NoneP in *. simpl. do 2 f_equal.

    - rewrite E1 in J.
      exists (NO _ bot_unreadable).
      rewrite E1'.
      inv J.
      + simpl.
        split;[|split;[split|]].
        * constructor. clear - RJ. apply join_top_l in RJ. rewrite RJ. apply join_bot.
        * intros pos; autospec bound; autospec nn. rewrite bound in *; rewrite nn in *.
          congruence.
        * right. right. right. exists v, pp. split; f_equal.
          revert RJ; clear.
          intro. apply YES_ext. eapply join_top; eauto.
        * reflexivity.
      + exfalso.
        clear - RJ rsh2. apply join_top_l in RJ. subst. contradiction bot_unreadable; auto.
  }

  destruct (make_rmap (fun loc => proj1_sig (DESCR loc)) (own.ghost_approx phi1' (ghost_of phi3)))
    with (n := level phi1') as (phi3' & lev3 & at3 & Hg3).
  {
    (* the right level of approximation *)
    unfold "oo".
    extensionality loc; simpl.
    destruct (DESCR loc) as (?&?&rd3&?); simpl; auto.
  }
  {
    rewrite !ghost_fmap_fmap, approx_oo_approx; auto.
  }

  exists phi3'.
  split;[|split; [split|]].
  - apply resource_at_join2; auto.
    + rewrite lev3.
      unfold phi2'.
      apply level_age_to.
      eauto with *.
    + intros loc.
      rewrite at3.
      destruct (DESCR loc) as (?&?&?); simpl; auto.
    + subst phi2'; rewrite Hg, age_to_ghost_of, Hg3.
      apply ghost_fmap_join, ghost_of_join; auto.
  - rewrite lev3.
    apply join_level in J.
    auto with *.
  - intros loc.
    rewrite at3.
    destruct (DESCR loc) as (?&?&rd3); simpl; auto.
    destruct rd3 as [[NN rd3] _].
    split; auto.
    destruct rd3 as [R|[R|[R|R]]].
    + left. exact_eq R; do 3 f_equal; auto.
    + right; left. destruct R as [sh [psh [v [v' [H [H0 H1]]]]]].
       exists sh, H1, v, v'.
       split. replace (level phi3') with (level phi1'); rewrite H. apply YES_ext; auto.
       rewrite H0; apply YES_ext; auto.
    + right; right; left. auto.
    + auto.
  - congruence.
Qed.*)

Lemma whole_program_sequential_safety_ext:
   forall {CS: compspecs} {Espec: OracleKind} (initial_oracle: OK_ty) 
     (EXIT: semax_prog.postcondition_allows_exit Espec tint)
     (dryspec: ext_spec OK_ty)
     (dessicate : forall (ef : external_function) jm,
               ext_spec_type OK_spec ef ->
               ext_spec_type dryspec ef)
     (JDE: juicy_dry_ext_spec _ (@JE_spec OK_ty OK_spec) dryspec dessicate)
     (DME: ext_spec_mem_evolve _ dryspec)
     prog V G m,
     @semax_prog Espec (*NullExtension.Espec*) CS prog initial_oracle V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q,
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       initial_core  (cl_core_sem (globalenv prog))
           0 m q m (Vptr b Ptrofs.zero) nil /\
       forall n,
        @dry_safeN _ _ _ OK_ty (semax.genv_symb_injective)
            (cl_core_sem (globalenv prog))
            (*(dryspec  OK_ty)*) dryspec
            (Build_genv (Genv.globalenv prog) (prog_comp_env prog)) 
             n initial_oracle q m.
Proof.
 intros.
 destruct (@semax_prog_rule Espec CS _ _ _ _ 
     0 (*additional temporary argument - TODO (Santiago): FIXME*)
     initial_oracle EXIT H H0) as [b [q [[H1 H2] H3]]].
 destruct (H3 O) as [jmx [H4x [H5x [H6x [H6'x [H7x _]]]]]].
 destruct (H2 jmx H4x) as [jmx' [H8x H8y]].
 exists b, q. (* , (m_dry jmx'). *)
 split3; auto.
 rewrite H4x in H8y. auto.
 subst. simpl.
 clear H5x H6x H6'x H7x H8y.
 forget (m_dry jmx) as m. clear jmx.
 intro n.
 specialize (H3 n).
 destruct H3 as [jm [? [? [? [Hwsat [? _]]]]]].
 unfold semax.jsafeN in H6.
 subst m.
 assert (joins (compcert_rmaps.RML.R.ghost_of (m_phi jm))
   (Some (ghost_PCM.ext_ref initial_oracle, compcert_rmaps.RML.R.NoneP) :: nil)) as J.
 { destruct (compcert_rmaps.RML.R.ghost_of (m_phi jm)); inv H5.
   eexists; constructor; constructor.
   instantiate (1 := (_, _)); constructor; simpl; constructor; auto.
   instantiate (1 := (Some _, _)); repeat constructor; simpl; auto. }
 destruct Hwsat as (z & Jz & Hdry & Hz).
 (* safety uses all the resources, including the ones we put inside
    invariants (since there's no take-from-invariant step in Clight) *)
 rewrite Hdry.
 assert (exists w, join (m_phi jm) w (m_phi z) /\
   (invariants.wsat * invariants.ghost_set invariants.g_en Ensembles.Full_set)%pred w) as Hwsat.
 { do 2 eexists; eauto; apply initial_world.wsat_rmap_wsat. }
 assert (mem_sub (m_dry jm) (m_dry z)) as Hmem.
 { rewrite Hdry; repeat (split; auto). }
 clear - JDE DME H4 J H6 Hwsat Hmem.
  rewrite <- H4.
 assert (level jm <= n)%nat by lia.
 clear H4; rename H into H4.
 forget initial_oracle as ora.
 revert ora jm z q H4 J Hwsat H6; induction n; intros.
 assert (level jm = 0%nat) by lia. rewrite H; constructor.
 inv H6.
 - rewrite H; constructor.
 - (* in the juicy semantics, we took a step with jm *)
   destruct H as (?&?&Hl&Hg).
   (* so we can take the same step with the full memory z *)
   evstep???

   rewrite Hl; eapply safeN_step.
   + red. red. fold (globalenv prog). eassumption.
   + destruct Hwsat as (w & Jw & Hw).
     (* the new full memory can be broken into the memory we got from the step,
        and the memory we left in the invariant *)
     assert (exists z', join (m_phi m') (age_to.age_to (level m') w) (m_phi z') /\ m_dry z' = m'') as (z' & J' & ?); subst.
     { destruct (CLC_memsem (globalenv prog)) eqn: Hsem.
       inv Hsem.
       apply corestep_mem, mem_step_evolve in H2.
       destruct (juicy_mem_lemmas.rebuild_juicy_mem_rmap z m'') as (? & ? & Hr' & Hg').
       eapply mem_evolve_cohere in H2; [|eauto].
       apply (age_to_cohere _ _ (level m')) in H2 as (A & B & C & D).
       exists (mkJuicyMem _ _ A B C D); split; auto; simpl.
       apply compcert_rmaps.RML.resource_at_join2; auto.
       * apply join_level in Jw as []. rewrite !level_juice_level_phi in *. rewrite age_to.level_age_to; auto; lia.
       * apply join_level in Jw as []. rewrite !level_juice_level_phi in *. rewrite !age_to.level_age_to; auto; lia.
       * intros; rewrite !age_to_resource_at.age_to_resource_at, Hr';
           unfold juicy_mem_lemmas.rebuild_juicy_mem_fmap.
         clear - H1 Jw Hw.
         destruct m', z; simpl in *.

resource_decay b phi1 phi1'
join phi1 phi2 phi3

join phi1' phi2 

         
         (* Something's missing. *) admit.
       * rewrite !age_to_resource_at.age_to_ghost_of, Hg, Hg'.
         rewrite <- level_juice_level_phi; apply compcert_rmaps.RML.ghost_fmap_join, compcert_rmaps.RML.ghost_of_join; auto. }
     assert ((invariants.wsat * invariants.ghost_set invariants.g_en Ensembles.Full_set)%pred
       (age_to.age_to (level m') w)).
     { eapply pred_nec_hereditary, Hw; apply age_to.age_to_necR. }
Search jstep.
     assert (joins (compcert_rmaps.RML.R.ghost_of (m_phi z'))
       (compcert_rmaps.RML.R.ghost_fmap
         (compcert_rmaps.RML.R.approx (level z'))
         (compcert_rmaps.RML.R.approx (level z'))
        (Some (ghost_PCM.ext_ref ora, compcert_rmaps.RML.R.NoneP) :: nil))).
     { admit. }
     edestruct H0 as (? & ? & Hz' & Hsafe); eauto.
     { apply join_sub_refl. }
     destruct Hsafe as [Hsafe | (m2 & ? & ? & ? & Hsafe)].
     { admit. }
     (* after accessing invariants, we have a new sub-memory m2, which
        completes to the same full memory *)
     replace (level m') with (level m2) by admit.
     destruct Hz' as [<- ?].
     apply IHn; eauto.
     { admit. }
     { admit. }
 -
   destruct dryspec as [ty pre post exit]. simpl in *. (* subst ty. *)
   destruct JE_spec as [ty' pre' post' exit']. simpl in *.
   change (level (m_phi jm)) with (level jm) in *.
   destruct JDE as [JDE1 [JDE2 JDE3]].
   specialize (JDE1 e x (dessicate e jm x)); simpl in JDE1.
   destruct (level jm) eqn: Hl; [constructor|].
   eapply safeN_external.
     eassumption.
     apply JDE1. Search mem_rmap_cohere. reflexivity. assumption.
     simpl. intros.
     assert (H20: exists jm', m_dry jm' = m' 
                      /\ (level jm' = n')%nat
                      /\ juicy_safety.pures_eq (m_phi jm) (m_phi jm')
                      /\ resource_at (m_phi jm') = resource_fmap (approx (level jm')) (approx (level jm')) oo juicy_mem_lemmas.rebuild_juicy_mem_fmap jm (m_dry jm')
                      /\ compcert_rmaps.RML.R.ghost_of (m_phi jm') = Some (ghost_PCM.ext_ghost z', compcert_rmaps.RML.R.NoneP) :: ghost_fmap (approx (level jm')) (approx (level jm')) (tl (ghost_of (m_phi jm)))). {
     destruct (juicy_mem_lemmas.rebuild_juicy_mem_rmap jm m') 
            as [phi [? [? ?]]].
     assert (own.ghost_approx phi (Some (ghost_PCM.ext_ghost z', NoneP) :: tl (compcert_rmaps.RML.R.ghost_of phi)) =
        Some (ghost_PCM.ext_ghost z', NoneP) :: tl (compcert_rmaps.RML.R.ghost_of phi)) as Happrox.
     { simpl; f_equal.
        rewrite <- compcert_rmaps.RML.ghost_of_approx at 2.
        destruct (compcert_rmaps.RML.R.ghost_of phi); auto. }
     set (phi1 := initial_world.set_ghost _ _ Happrox).
     assert (level phi1 = level phi /\ resource_at phi1 = resource_at phi) as [Hl1 Hr1].
     { subst phi1; unfold initial_world.set_ghost; rewrite level_make_rmap, resource_at_make_rmap; auto. }
     pose (phi' := age_to.age_to n' phi1).
     assert (mem_rmap_cohere m' phi'). {
       clear - H1 Hr1 Hl1 H8 H7 H6 H3 DME JDE1.
       apply JDE1 in H1; [ | reflexivity].
       specialize (DME e _ _ _ _ _ _ _ _ _ _ H1 H6).
     subst phi'.
     apply age_to_cohere.
     subst phi1.
     apply set_ghost_cohere.
     eapply mem_evolve_cohere; eauto.
   }
    destruct H10 as [H10 [H11 [H12 H13]]].
     pose (jm' := mkJuicyMem _ _ H10 H11 H12 H13).
     exists jm'.
     split; [ | split3].
     subst jm'; simpl; auto.
     subst jm' phi'; simpl. apply age_to.level_age_to. lia.
     hnf. split. intro loc. subst jm' phi'. simpl.
     rewrite age_to_resource_at.age_to_resource_at.
     rewrite Hr1, H8. unfold juicy_mem_lemmas.rebuild_juicy_mem_fmap.
     destruct (m_phi jm @ loc); auto. rewrite age_to.level_age_to by lia.
      reflexivity.
     intro loc. subst jm' phi'. simpl.
     rewrite age_to_resource_at.age_to_resource_at.
     rewrite Hr1, H8. unfold juicy_mem_lemmas.rebuild_juicy_mem_fmap; simpl.
     destruct (m_phi jm @ loc); auto.
     if_tac; simpl; auto. destruct k; simpl; auto. if_tac; simpl; eauto. simpl; eauto.
     subst jm' phi'. simpl m_phi.
     rewrite age_to_resource_at.age_to_ghost_of.
     subst phi1.
     split.
     extensionality; unfold compose; simpl.
     rewrite age_to_resource_at.age_to_resource_at, age_to.level_age_to by lia.
     unfold initial_world.set_ghost; rewrite resource_at_make_rmap.
     rewrite H8; auto.
     unfold initial_world.set_ghost; rewrite ghost_of_make_rmap; simpl.
     rewrite age_to.level_age_to, H9 by (rewrite level_make_rmap; lia); simpl; auto.
   }
   destruct H20 as [jm'  [H26 [H27 [H28 [H29 Hg']]]]].
   specialize (H2 ret jm' z' n' Hargsty Hretty).
   spec H2. lia.
    spec H2. hnf; split3; auto. lia.
  spec H2.
  eapply JDE2; eauto 6. lia. subst m'. apply H6.
  destruct H2 as [c' [H2a H2b]]; exists c'; split; auto.
  hnf in H2b.
  specialize (H2b (Some (ghost_PCM.ext_ref z', compcert_rmaps.RML.R.NoneP) :: nil)).
  spec H2b. apply join_sub_refl.
  spec H2b.
  { rewrite Hg'.
    eexists (Some (ghost_PCM.ext_both z', compcert_rmaps.RML.R.NoneP) :: _);
      repeat constructor.  }
  destruct H2b as [jm'' [? [? ?]]].
  destruct H7 as [? [? ?]].
  subst m'. rewrite <- H7.
  specialize (IHn  z' jm'' c').
  subst n'. rewrite <- H9.
  change (level (m_phi jm'')) with (level  jm'') in IHn.
  apply IHn. lia.
  auto.
  rewrite H9; auto.
 - eapply safeN_halted; eauto.
    apply JDE. auto.
 Unshelve. simpl. split; [apply Share.nontrivial | hnf]. exists None; constructor.
Qed.

Require Import VST.veric.juicy_safety.

Definition fun_id (ext_link: Strings.String.string -> ident) (ef: external_function) : option ident :=
  match ef with EF_external id sig => Some (ext_link id) | _ => None end.
