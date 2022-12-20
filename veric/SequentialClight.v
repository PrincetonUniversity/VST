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

#[export] Instance mem_evolve_refl : RelationClasses.Reflexive mem_evolve.
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

#[export] Instance mem_evolve_trans : RelationClasses.Transitive mem_evolve.
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
    ext_spec_pre J e t b tl vl x jm ->
    ext_spec_pre D e t' b tl vl x (m_dry jm)) /\
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

(* This will probably never be useful, since the witness from semax_ext
   always includes a frame rmap, which doesn't make sense in the witness
   of a dry spec.*)
Definition juicy_dry_ext_spec_make (Z: Type)
   (J: external_specification juicy_mem external_function Z) :
   external_specification mem external_function Z.
destruct J.
apply Build_external_specification with ext_spec_type.
intros e t b tl vl x m.
apply (forall jm, m_dry jm = m -> ext_spec_pre e t b tl vl x jm).
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
exfalso; clear - r H1.
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
exfalso.
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

Fixpoint in_alloc_trace b ofs T :=
  match T with
  | nil => false
  | Alloc b' lo hi :: rest => adr_range_dec (b', lo) (hi - lo) (b, ofs) || in_alloc_trace b ofs rest
  | _ :: rest => in_alloc_trace b ofs rest
  end.

Lemma ev_elim_perm_inv : forall l k T m m', ev_elim m T m' ->
  (in_free_list_trace (fst l) (snd l) T /\ access_at m' l k = None) \/
  ~in_free_list_trace (fst l) (snd l) T /\ ((in_alloc_trace (fst l) (snd l) T = true /\
   (fst l >= Mem.nextblock m)%positive /\ access_at m' l k = Some Freeable) \/
  (in_alloc_trace (fst l) (snd l) T = false /\
   access_at m' l k = access_at m l k)).
Proof.
  induction T; simpl; intros; subst; auto.
  destruct a.
  - destruct H as (? & ? & ?%IHT).
    rewrite (storebytes_access _ _ _ _ _ H), <- (Mem.nextblock_storebytes _ _ _ _ _ H); auto.
  - destruct H as (? & ?%IHT); auto.
  - destruct H as (? & ? & Hrest%IHT).
    destruct Hrest as [? | [? Hrest]]; auto.
    right; split; auto.
    destruct (adr_range_dec _ _ _); simpl.
    + left; split; auto.
      destruct a; subst.
      split; [apply Mem.alloc_result in H; lia|].
      destruct Hrest as [(? & ? & ?) | (? & ->)]; auto.
      destruct l; simpl in *; eapply alloc_access_same; eauto; lia.
    + destruct Hrest as [(? & Hge & ?) | (? & ?)]; [left | right]; split; auto.
      * split; auto.
        erewrite Mem.nextblock_alloc in Hge by eauto; lia.
      * destruct l; simpl in *; rewrite (alloc_access_other _ _ _ _ _ H); auto; lia.
  - destruct H as (? & ? & Hrest%IHT).
    destruct Hrest as [[] | [? Hrest]]; auto.
    destruct (in_free_list_dec (fst l) (snd l) l0).
    + left; split; auto.
      edestruct freelist_access_2'; eauto.
      destruct Hrest as [(? & ? & ?) | [_ ->]].
      * unfold Mem.valid_block, Plt in *; lia.
      * unfold access_at; auto.
    + right; split; [tauto|].
      destruct Hrest as [(? & Hge & ?) | (? & ?)]; [left | right]; split; auto.
      * split; auto.
        erewrite mem_lemmas.nextblock_freelist in Hge by eauto; lia.
      * unfold access_at at 2; rewrite <- (freelist_access_1 _ _ _ _ n _ _ H); auto.
Qed.

Lemma ev_elim_alloc : forall l k T m m', ev_elim m T m' ->
  in_alloc_trace (fst l) (snd l) T = true -> ~ in_free_list_trace (fst l) (snd l) T ->
  access_at m' l k = Some Freeable.
Proof.
  induction T; [discriminate|]; simpl; intros.
  destruct a.
  - destruct H as (? & ? & ?%IHT); auto.
  - destruct H as (? & ?%IHT); auto.
  - destruct H as (? & ? & Helim).
    unfold proj_sumbool in *.
    apply orb_true_iff in H0 as [Hin | ?]; eauto.
    if_tac in Hin; inv Hin.
    destruct H0; subst.
    eapply ev_elim_perm_inv in Helim as [[] | [_ Hcase]]; [contradiction H1; eauto|].
    destruct Hcase as [(? & ? & ?) | (? & ->)]; eauto.
    destruct l; simpl in *; eapply alloc_access_same; eauto; lia.
  - destruct H as (? & ? & ?%IHT); auto.
Qed.

Lemma ev_elim_alloc_new : forall b lo sz T m m', ev_elim m T m' ->
  In (Alloc b lo sz) T -> (b >= Mem.nextblock m)%positive.
Proof.
  induction T; simpl; [contradiction|]; intros.
  destruct H0.
  - subst.
    destruct H as (? & ? & ?).
    apply Mem.alloc_result in H; subst; lia.
  - destruct a; (destruct H as (? & ? & Helim) || destruct H as (? & Helim)); eapply IHT in Helim; eauto.
    + erewrite <- Mem.nextblock_storebytes; eauto.
    + erewrite Mem.nextblock_alloc in Helim; eauto; lia.
    + erewrite <- mem_lemmas.nextblock_freelist; eauto.
Qed.

Fixpoint in_write_trace b ofs T :=
  match T with
  | nil => false
  | Write b' z lv :: rest => adr_range_dec (b', z) (Zlength lv) (b, ofs) || in_write_trace b ofs rest
  | _ :: rest => in_write_trace b ofs rest
  end.

Lemma perm_order_total : forall p1 p2, ~perm_order p1 p2 -> perm_order p2 p1.
Proof.
  destruct p1, p2; try constructor; intros H; contradiction H; constructor.
Qed.

Lemma pmax_l : forall p1 p2 q : option permission,
  Mem.perm_order'' (pmax p1 p2) q <-> Mem.perm_order'' p1 q \/ Mem.perm_order'' p2 q.
Proof.
  intros; unfold pmax.
  destruct p1, p2; simpl in *; try solve [destruct q; tauto].
  if_tac; [|apply perm_order_total in H]; destruct q; simpl; split; auto; intros [? | ?]; auto; eapply perm_order_trans; eauto.
Qed.

Lemma in_write_trace_perm : forall b ofs T, in_write_trace b ofs T = true ->
  (exists z sz, In (Alloc b z sz) T) \/ Mem.perm_order' (cur_perm (b, ofs) T) Writable.
Proof.
  induction T; simpl; [discriminate|]; intros.
  rewrite mem_lemmas.po_oo in *.
  destruct a.
  - rewrite pmax_l; destruct (adr_range_dec _ _ _); simpl in *; [|apply IHT in H as [(? & ? & ?) | ?]; eauto].
    destruct a; subst.
    right; left; setoid_rewrite if_true; auto; [|lia]; simpl.
    destruct (zle _ _); try lia; constructor.
  - rewrite pmax_l; apply IHT in H as [(? & ? & ?) | ?]; eauto.
  - if_tac; [|apply IHT in H as [(? & ? & ?) | ?]; eauto].
    subst; eauto.
  - apply IHT in H as [(? & ? & ?) | ?]; eauto.
    right.
    induction l; auto; simpl.
    destruct a as ((?, ?), ?); simple_if_tac; auto; constructor.
Qed.

Lemma free_contents : forall m b lo hi m', Mem.free m b lo hi = Some m' ->
  contents_at m' = contents_at m.
Proof.
  intros; apply Mem.free_result in H; subst; auto.
Qed.

Lemma free_list_contents : forall l m m', Mem.free_list m l = Some m' ->
  contents_at m' = contents_at m.
Proof.
  induction l; simpl; intros.
  { inv H; auto. }
  destruct a as ((?, ?), ?).
  destruct (Mem.free _ _ _ _) eqn: Hfree; inv H.
  apply free_contents in Hfree as <-; auto.
Qed.

Lemma ev_elim_nostore : forall l T m m', ev_elim m T m' ->
  in_write_trace (fst l) (snd l) T = false ->
  (exists z sz, In (Alloc (fst l) z sz) T) \/ contents_at m' l = contents_at m l.
Proof.
  induction T; simpl; intros; subst; auto.
  destruct a.
  - destruct (adr_range_dec _ _ _); [discriminate|].
    destruct H as (? & ? & Helim).
    apply IHT in Helim as [(? & ? & ?) | ->]; eauto.
    unfold contents_at; erewrite Mem.storebytes_mem_contents by eauto.
    destruct (eq_block b (fst l)).
    + subst; rewrite Maps.PMap.gss, Mem.setN_outside; auto.
      rewrite <- Zlength_correct.
      unfold adr_range in n.
      destruct (zlt (snd l) ofs); auto.
      destruct (zlt (snd l) (ofs + Zlength bytes)); auto; lia.
    + rewrite Maps.PMap.gso; auto.
  - destruct H as (? & Helim).
    apply IHT in Helim as [(? & ? & ?) | ->]; eauto.
  - destruct H as (? & ? & Helim).
    apply IHT in Helim as [(? & ? & ?) | ->]; eauto.
    destruct (eq_block b (fst l)); subst; eauto.
    unfold contents_at; erewrite mem_lemmas.AllocContentsOther; eauto.
  - destruct H as (? & ? & Helim).
    apply IHT in Helim as [(? & ? & ?) | ->]; eauto.
    erewrite free_list_contents; eauto.
Qed.

Lemma ev_elim_contents' : forall l T m m', ev_elim m T m' -> (fst l < Mem.nextblock m)%positive ->
  ~Mem.perm m (fst l) (snd l) Cur Writable ->
  (forall m1 m1', ev_elim m1 T m1' -> contents_at m1' l = contents_at m1 l).
Proof.
  intros.
  destruct (in_write_trace (fst l) (snd l) T) eqn: Hwrite.
  - apply in_write_trace_perm in Hwrite as [(? & ? & Halloc) | ?].
    { eapply (ev_elim_alloc_new _ _ _ _ _ _ H) in Halloc; eauto; lia. }
    eapply ev_perm in H.
    unfold Mem.perm in *.
    rewrite mem_lemmas.po_oo in *; eapply mem_lemmas.po_trans in H3; eauto; contradiction.
  - eapply ev_elim_nostore in Hwrite as [(? & ? & Halloc) | ?]; eauto.
    eapply (ev_elim_alloc_new _ _ _ _ _ _ H) in Halloc; eauto.
    apply Pos.lt_nle in H0; apply Pos.ge_le in Halloc; contradiction.
Qed.

Lemma join_ev_elim_commut : forall jm1 x jm2 T jm1' m2', join (m_phi jm1) x (m_phi jm2) ->
  mem_sub (m_dry jm1) (m_dry jm2) -> ev_elim (m_dry jm1) T (m_dry jm1') -> mem_sub (m_dry jm1') m2' ->
  resource_decay (Mem.nextblock (m_dry jm1)) (m_phi jm1) (m_phi jm1') -> ev_elim (m_dry jm2) T m2' ->
  forall l, join (m_phi jm1' @ l)
    (compcert_rmaps.RML.R.resource_fmap (compcert_rmaps.RML.R.approx (level jm1')) (compcert_rmaps.RML.R.approx (level jm1')) (x @ l))
    (compcert_rmaps.RML.R.resource_fmap (compcert_rmaps.RML.R.approx (level jm1')) (compcert_rmaps.RML.R.approx (level jm1')) (juicy_mem_lemmas.rebuild_juicy_mem_fmap jm2 m2' l)).
Proof.
  intros ?????? J Hmem Helim1 Hmem' Hdecay Helim2 l.
  unfold juicy_mem_lemmas.rebuild_juicy_mem_fmap.
  apply (compcert_rmaps.RML.resource_at_join _ _ _ l) in J.
  edestruct ev_elim_perm_inv as [[? Hnone] | [? [(? & ? & Hnew) | (? & Hsame)]]]; eauto.
  - (* location was freed *)
    rewrite Hnone; simpl.
    destruct jm1'; simpl in *.
    specialize (JMaccess l).
    eapply ev_elim_free_1 in H as (Hcase & Hnone1 & ? & ?); [|apply Helim1].
    unfold access_at in JMaccess; rewrite Hnone1 in JMaccess.
    unfold perm_of_res in JMaccess.
    destruct (phi @ l); try discriminate.
    if_tac in JMaccess; inv JMaccess.
    destruct Hcase as [Hm1 | Hm1].
    + destruct l; simpl in *.
      rewrite perm_access, (juicy_mem_access jm1) in Hm1.
      assert (perm_of_res (m_phi jm1 @ (b, z)) = Some Freeable) as Hperm1
        by (destruct (perm_of_res _); inv Hm1; auto).
      apply semax_call.perm_of_res_val in Hperm1 as (? & ? & Hp); rewrite Hp in J.
      inv J.
      * apply join_Tsh in RJ as []; subst.
        constructor; auto.
      * apply join_Tsh in RJ as []; subst.
        contradiction bot_unreadable.
    + assert (fst l >= Mem.nextblock (m_dry jm2))%positive.
      { destruct Hmem as (_ & <- & _); auto. }
      rewrite (juicy_mem_alloc_cohere jm2) in * by auto.
      inv J; constructor.
      apply join_Bot in RJ as []; subst; auto.
    + destruct k; try discriminate.
      unfold perm_of_sh in JMaccess; repeat if_tac in JMaccess; try discriminate; subst.
      contradiction.
  - (* location was newly allocated and not freed *)
    rewrite Hnew; simpl.
    rewrite (juicy_mem_alloc_cohere jm2) in * by auto.
    inv J; simpl.
    apply join_Bot in RJ as []; subst.
    eapply ev_elim_alloc in Helim1; eauto.
    rewrite juicy_mem_access in Helim1.
    apply semax_call.perm_of_res_val in Helim1 as (? & ? & Hp); rewrite Hp.
    apply juicy_mem_contents in Hp as []; subst.
    unfold contents_at; destruct Hmem' as [-> _].
    constructor; auto.
  - (* location was only read and written *)
    rewrite Hsame, juicy_mem_access.
    destruct (ev_elim_perm_inv l Cur _ _ _ Helim1) as [[? ?] | [_ [(? & ? & Hnew) | (_ & Hsame1)]]].
    { contradiction H; eauto. }
    { congruence. }
    pose proof (juicy_mem_access jm1' l) as Hperm; rewrite Hsame1, juicy_mem_access in Hperm.
    destruct Hdecay as [_ Hdecay]; specialize (Hdecay l); destruct Hdecay as [_ Hdecay].
    inv J; rewrite <- H2 in Hperm, Hdecay; simpl in *.
    + rewrite if_false by (if_tac; simpl; auto; intros X; inv X).
      destruct (m_phi jm1' @ l); try discriminate; simpl in Hperm.
      destruct Hdecay as [Heq | [(? & ? & ? & ? & ? & ?) | [(? & ? & ?) | (? & ? & ? & ?)]]]; try discriminate; inv Heq.
      constructor; auto.
      { destruct Hdecay as [? | [(? & ? & ? & ? & ? & ?) | [(? & ? & Heq) | (? & ? & ? & ?)]]]; try discriminate; inv Heq.
        rewrite perm_of_freeable in Hperm; if_tac in Hperm; discriminate. }
      { destruct Hdecay as [Heq | [(? & ? & ? & ? & ? & ?) | [(? & ? & ?) | (? & ? & ? & ?)]]]; discriminate. }
    + destruct (Pos.ltb_spec (fst l) (Mem.nextblock (m_dry jm1))).
      destruct k.
      rewrite if_true by (unfold perm_of_sh; if_tac; if_tac; try contradiction; constructor).
      unfold perm_of_sh in Hperm; rewrite (if_true _ _ _ _ _ rsh1) in Hperm.
      destruct (m_phi jm1' @ l) eqn: H1'; simpl in Hperm; try (repeat if_tac in Hperm; discriminate).
      destruct k; try (repeat if_tac in Hperm; discriminate).
      apply juicy_mem_contents in H1' as []; subst.
      unfold contents_at; destruct Hmem' as (-> & _ & _).
      constructor.
      destruct Hdecay as [Heq | [(? & ? & ? & ? & Heq & Heq1) | [(? & ? & Heq) | (? & ? & ? & ?)]]]; try discriminate; inv Heq; try inv Heq1; auto.
      rewrite perm_of_freeable in Hperm; repeat if_tac in Hperm; try discriminate; subst; auto.
      { destruct Hdecay as [<- | [(? & ? & ? & ? & ? & ?) | [(? & ? & ?) | (? & ? & ? & ?)]]]; try discriminate; try lia; constructor; auto. }
      { destruct Hdecay as [<- | [(? & ? & ? & ? & ? & ?) | [(? & ? & ?) | (? & ? & ? & ?)]]]; try discriminate; try lia; constructor; auto. }
      { rewrite juicy_mem_alloc_cohere in H2 by (apply Pos.le_ge; auto). inv H2. }
    + destruct Hdecay as [Heq | [(? & ? & ? & ? & Heq & Heq1) | [(? & ? & Heq) | (? & ? & ? & ?)]]]; try discriminate.
      rewrite <- Heq.
      destruct k; try constructor; auto.
      rewrite if_true by (unfold perm_of_sh; if_tac; if_tac; try contradiction; constructor).
      rewrite (juicy_mem_access jm1'), <- Hperm in Hsame1.
      eapply (ev_elim_contents' _ _ _ _ Helim1) in Helim2 as ->; auto.
      symmetry in H4; apply juicy_mem_contents in H4 as []; subst.
      constructor; auto.
      { destruct (Pos.ltb_spec (fst l) (Mem.nextblock (m_dry jm1))); auto.
        erewrite juicy_mem_alloc_cohere in H4. inv H4.
        destruct Hmem as (_ & <- & _); apply Pos.le_ge; auto. }
      { unfold Mem.perm; unfold access_at in Hsame1.
        setoid_rewrite <- Hsame1.
        if_tac; intros X; inv X. }
      { erewrite juicy_mem_alloc_cohere in H4. inv H4.
        destruct Hmem as (_ & <- & _); auto. }
    + destruct (Pos.ltb_spec (fst l) (Mem.nextblock (m_dry jm1))).
      destruct k.
      rewrite if_true by (unfold perm_of_sh; if_tac; if_tac; try contradiction; constructor).
      unfold perm_of_sh in Hperm; rewrite (if_true _ _ _ _ _ rsh1) in Hperm.
      destruct (m_phi jm1' @ l) eqn: H1'; simpl in Hperm; try (repeat if_tac in Hperm; discriminate).
      destruct k; try (repeat if_tac in Hperm; discriminate).
      rewrite (juicy_mem_access jm1'), H1' in Hsame1.
      apply juicy_mem_contents in H1' as []; subst.
      unfold contents_at; destruct Hmem' as (-> & _ & _).
      fold (contents_at m2' l).
      eapply (ev_elim_contents' _ _ _ _ Helim1) in Helim2 as ->; auto.
      symmetry in H4; apply juicy_mem_contents in H4 as []; subst.
      constructor; auto.
      { destruct Hdecay as [Heq | [(? & ? & ? & ? & Heq & Heq1) | [(? & ? & Heq) | (? & ? & ? & ?)]]]; try discriminate; inv Heq; try inv Heq1; auto; lia. }
      { unfold Mem.perm. unfold access_at in Hsame1; setoid_rewrite <- Hsame1; simpl.
        rewrite <- Hperm; if_tac; [|intros X; inv X].
        apply join_writable0_readable in RJ; auto. }
      { destruct Hdecay as [<- | [(? & ? & ? & ? & ? & ?) | [(? & ? & ?) | (? & ? & ? & ?)]]]; try discriminate; try lia; constructor; auto. }
      { destruct Hdecay as [<- | [(? & ? & ? & ? & ? & ?) | [(? & ? & ?) | (? & ? & ? & ?)]]]; try discriminate; try lia; constructor; auto. }
      { rewrite juicy_mem_alloc_cohere in H2 by (apply Pos.le_ge; auto). inv H2. }
    + destruct Hdecay as [<- | [(? & ? & ? & ? & ? & ?) | [(? & ? & ?) | (? & ? & ? & ?)]]]; try discriminate.
      constructor; auto.
      erewrite juicy_mem_alloc_cohere in H4. inv H4.
      destruct Hmem as (_ & <- & _); auto.
Qed.

Lemma join_sub_pures_eq : forall a b, join_sub a b -> juicy_safety.pures_eq a b.
Proof.
  intros ?? [? J]; unfold juicy_safety.pures_eq, juicy_safety.pures_sub.
  split; intros l; apply (compcert_rmaps.RML.resource_at_join _ _ _ l) in J; inv J; eauto.
  rewrite H2, <- compcert_rmaps.RML.resource_at_approx, <- H2; reflexivity.
Qed.

Lemma pures_eq_sym : forall a b, level a = level b -> juicy_safety.pures_eq a b -> juicy_safety.pures_eq b a.
Proof.
  unfold juicy_safety.pures_eq, juicy_safety.pures_sub; intros.
  destruct H0 as [H1 H2]; split; intros l; specialize (H1 l); specialize (H2 l); destruct (a @ l) eqn: Ha, (b @ l) eqn: Hb; try congruence; eauto.
  - destruct H2; discriminate.
  - destruct H2; discriminate.
  - destruct H2 as [? H2]; inv H2; inv H1.
    rewrite <- Ha, <- compcert_rmaps.RML.resource_at_approx, Ha.
    rewrite compcert_rmaps.RML.preds_fmap_fmap, H, compcert_rmaps.RML.approx_oo_approx; reflexivity.
Qed.

(* frame property for juicy extspecs *)
Definition extspec_frame {Z} (JE : juicy_ext_spec Z) := forall e t b lt lv z jm w jm1, ext_spec_pre JE e t b lt lv z jm ->
        mem_sub (m_dry jm) (m_dry jm1) -> join (m_phi jm) w (m_phi jm1) -> semax.ext_compat z (m_phi jm1) ->
        exists t1, ext_spec_pre JE e t1 b lt lv z jm1 /\
        forall ot v z' jm1', ext_spec_post JE e t1 b ot v z' jm1' ->
          exists jm', ext_spec_post JE e t b ot v z' jm' /\ mem_sub (m_dry jm') (m_dry jm1') /\
            join (m_phi jm') (age_to.age_to (level jm') w) (m_phi jm1').

Lemma funspec2jspec_frame : forall {Z} (JE : juicy_ext_spec Z) extlink f,
  extspec_frame JE -> extspec_frame (semax_ext.funspec2jspec _ JE extlink f).
Proof.
  unfold semax_ext.funspec2jspec, semax_ext.funspec2extspec, extspec_frame; simpl; intros.
  destruct f as (?, []), t0; simpl in *.
  unfold semax_ext.funspec2pre, semax_ext.funspec2post in *; if_tac; [|eauto].
  destruct t as (frame, t); simpl in *.
  destruct H0 as (? & ? & ? & J & ? & ? & ?).
  destruct (join_assoc J H2) as (frame' & Jframe & ?).
  exists (frame', t); simpl; split; eauto 7.
  intros ???? (? & ? & J' & ? & ?).
  eapply join_comm, nec_join2 in Jframe as (? & frame1 & Jframe & Hnecw & ?); eauto.
  destruct (join_assoc (join_comm Jframe) (join_comm J')) as (? & J1 & J1').
  destruct (join_assoc J1 (join_comm J1')) as (? & J'' & Jtop%join_comm).
  edestruct juicy_mem_sub as (? & ? & ?); [eexists; eauto | subst].
  eexists; split; [do 3 eexists; [apply J''|]|]; split; auto.
  - eapply rt_trans; eauto.
  - pose proof (necR_level _ _ Hnecw).
    apply age_to.necR_age_to in Hnecw; rewrite Hnecw in Jtop.
    destruct (join_level _ _ _ Jtop) as [-> <-].
    rewrite age_to.level_age_to; auto.
Qed.

Lemma add_funspecs_frame' : forall {Espec : OracleKind} extlink fs,
  extspec_frame OK_spec -> extspec_frame (@OK_spec (add_funspecs Espec extlink fs)).
Proof.
  destruct Espec; simpl; intros.
  revert dependent OK_spec; induction fs; simpl; auto; intros.
  destruct a; apply funspec2jspec_frame; auto.
Qed.

Lemma void_spec_frame : forall {Z}, extspec_frame (@OK_spec (ok_void_spec Z)).
Proof.
  unfold ok_void_spec; simpl; repeat intro; contradiction.
Qed.

Lemma add_funspecs_frame : forall {Z} extlink fs,
  extspec_frame (@OK_spec (add_funspecs (ok_void_spec Z) extlink fs)).
Proof.
  intros; apply add_funspecs_frame', void_spec_frame.
Qed.

Lemma whole_program_sequential_safety_ext:
   forall {CS: compspecs} {Espec: OracleKind} (initial_oracle: OK_ty)
     (EXIT: semax_prog.postcondition_allows_exit Espec tint)
     (Jsub: forall ef se lv m t v m' (EFI : ef_inline ef = true) m1
       (EFC : Events.external_call ef se lv m t v m'), mem_sub m m1 ->
       exists m1' (EFC1 : Events.external_call ef se lv m1 t v m1'),
         mem_sub m' m1' /\ proj1_sig (inline_external_call_mem_events _ _ _ _ _ _ _ EFI EFC1) =
         proj1_sig (inline_external_call_mem_events _ _ _ _ _ _ _ EFI EFC))
     (Jframe: extspec_frame OK_spec)
     (dryspec: ext_spec OK_ty)
     (dessicate : forall (ef : external_function) jm,
               ext_spec_type OK_spec ef ->
               ext_spec_type dryspec ef)
     (JDE: juicy_dry_ext_spec _ (@JE_spec OK_ty OK_spec) dryspec dessicate)
     (DME: ext_spec_mem_evolve _ dryspec)
     (Esub: forall v z m m', ext_spec_exit dryspec v z m -> mem_sub m m' -> ext_spec_exit dryspec v z m')
     prog V G m,
     @semax_prog Espec CS prog initial_oracle V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q,
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       initial_core  (cl_core_sem (globalenv prog))
           0 m q m (Vptr b Ptrofs.zero) nil /\
       forall n,
        @dry_safeN _ _ _ OK_ty (semax.genv_symb_injective)
            (cl_core_sem (globalenv prog))
            dryspec
            (Build_genv (Genv.globalenv prog) (prog_comp_env prog))
             n initial_oracle q m.
Proof.
 intros.
 destruct (@semax_prog_rule Espec CS _ _ _ _
     0 (*additional temporary argument - TODO (Santiago): FIXME*)
     initial_oracle EXIT H H0) as [b [q [[H1 H2] H3]]].
 destruct (H3 O) as [jmx [H4x [H5x [H6x [H6'x [H7x _]]]]]].
 destruct (H2 jmx H4x) as [jmx' [H8x H8y]].
 exists b, q.
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
 destruct Hwsat as (z & Jz & Hdry & Hz).
 (* safety uses all the resources, including the ones we put inside
    invariants (since there's no take-from-invariant step in Clight) *)
 rewrite Hdry.
 assert (joins (compcert_rmaps.RML.R.ghost_of (m_phi z))
   (Some (ghost_PCM.ext_ref initial_oracle, compcert_rmaps.RML.R.NoneP) :: nil)) as J.
 { apply compcert_rmaps.RML.ghost_of_join in Jz.
   unfold initial_world.wsat_rmap in Jz; rewrite ghost_of_make_rmap in Jz.
   inv Jz.
   { rewrite <- H7 in H5; discriminate. }
   rewrite <- H3 in H5; inv H5; inv H10.
   eexists; constructor; constructor.
   instantiate (1 := (_, _)); split; simpl; [|hnf; eauto].
   apply semax_prog.ext_ref_join. }
 assert (exists w, join (m_phi jm) w (m_phi z) /\
   (invariants.wsat * invariants.ghost_set invariants.g_en Ensembles.Full_set)%pred w) as Hwsat.
 { do 2 eexists; eauto; apply initial_world.wsat_rmap_wsat. }
 assert (mem_sub (m_dry jm) (m_dry z)) as Hmem.
 { rewrite Hdry; repeat (split; auto). }
 clear - Jsub Jframe Esub JDE DME H4 J H6 Hwsat Hmem.
  rewrite <- H4.
 assert (level jm <= n)%nat by lia.
 clear H4; rename H into H4.
 forget initial_oracle as ora.
 revert ora jm z q H4 J Hwsat Hmem H6; induction n; intros.
 assert (level jm = 0%nat) by lia. rewrite H; constructor.
 inv H6.
 - rewrite H; constructor.
 - (* in the juicy semantics, we took a step with jm *)
   destruct H as (?&?&Hl&Hg).
   (* so we can take the same step with the full memory z *)
   destruct (CLC_evsem (globalenv prog)) eqn: Hevsem; inv Hevsem.
   destruct (CLC_memsem (globalenv prog)) eqn: Hmemsem; inv Hmemsem.
   simpl in ev_step_ax1, ev_step_ax2.
   apply ev_step_ax2 in H as [T H].
   pose proof (ev_step_elim _ _ _ _ _ H) as Helim.
   eapply cl_evstep_extends in H as (m1' & H & Hmem'); eauto.
   pose proof (ev_step_elim _ _ _ _ _ H) as Helim1; clear ev_step_elim.
   apply ev_step_ax1 in H.
   rewrite Hl; eapply safeN_step.
   + red. red. fold (globalenv prog). eassumption.
   + destruct Hwsat as (w & Jw & Hw).
     (* the new full memory can be broken into the memory we got from the step,
        and the memory we left in the invariant *)
     assert (exists z', join (m_phi m') (age_to.age_to (level m') w) (m_phi z') /\ m_dry z' = m1') as (z' & J' & ?); subst.
     { apply corestep_mem, mem_step_evolve in H.
       destruct (juicy_mem_lemmas.rebuild_juicy_mem_rmap z m1') as (? & ? & Hr' & Hg').
       eapply mem_evolve_cohere in H; [|eauto].
       apply (age_to_cohere _ _ (level m')) in H as (A & B & C & D).
       exists (mkJuicyMem _ _ A B C D); split; auto; simpl.
       apply compcert_rmaps.RML.resource_at_join2; auto.
       * apply join_level in Jw as []. rewrite !level_juice_level_phi in *. rewrite age_to.level_age_to; auto; lia.
       * apply join_level in Jw as []. rewrite !level_juice_level_phi in *. rewrite !age_to.level_age_to; auto; lia.
       * intros; rewrite !age_to_resource_at.age_to_resource_at, Hr'.
         eapply join_ev_elim_commut; eauto.
       * rewrite !age_to_resource_at.age_to_ghost_of, Hg, Hg'.
         rewrite <- level_juice_level_phi; apply compcert_rmaps.RML.ghost_fmap_join, compcert_rmaps.RML.ghost_of_join; auto. }
     assert ((invariants.wsat * invariants.ghost_set invariants.g_en Ensembles.Full_set)%pred
       (age_to.age_to (level m') w)).
     { eapply pred_nec_hereditary, Hw; apply age_to.age_to_necR. }
     assert (joins (compcert_rmaps.RML.R.ghost_of (m_phi z'))
       (compcert_rmaps.RML.R.ghost_fmap
         (compcert_rmaps.RML.R.approx (level z'))
         (compcert_rmaps.RML.R.approx (level z'))
        (Some (ghost_PCM.ext_ref ora, compcert_rmaps.RML.R.NoneP) :: nil))).
     { assert (join (ghost_of (m_phi m')) (ghost_of (age_to.age_to (level m') w))
         (ghost_of (age_to.age_to (level m') (m_phi z)))) as J1.
       { rewrite Hg, !age_to_resource_at.age_to_ghost_of.
         apply compcert_rmaps.RML.ghost_fmap_join, compcert_rmaps.RML.ghost_of_join; auto. }
       eapply join_eq in J1; [|apply compcert_rmaps.RML.ghost_of_join; eauto].
       rewrite J1. rewrite age_to_resource_at.age_to_ghost_of.
       destruct J as [? J]; eapply compcert_rmaps.RML.ghost_fmap_join in J; simpl in *; eexists; apply J. }
     edestruct H0 as (? & ? & Hz' & Hsafe); eauto.
     { apply join_sub_refl. }
     assert (level x = level m') as Hl'.
     { destruct Hz' as (? & ? & ?); apply join_level in J' as [];
         rewrite <- !level_juice_level_phi in *; lia. }
     destruct Hsafe as [Hsafe | (m2 & ? & ? & ? & ? & Hsafe)].
     { rewrite <- Hl', Hsafe; constructor. }
     (* after accessing invariants, we have a new sub-memory m2, which
        completes to the same full memory *)
     assert (level m' = level m2) as Hl2 by (apply join_level in H6 as []; rewrite <- !level_juice_level_phi in *; lia).
     rewrite Hl2.
     destruct Hz' as [<- ?].
     apply IHn; eauto. lia.
 -
   unfold extspec_frame in Jframe.
   destruct dryspec as [ty pre post exit].
   destruct JE_spec as [ty' pre' post' exit'].
   change (level (m_phi jm)) with (level jm) in *.
   destruct JDE as [JDE1 [JDE2 JDE3]].
   destruct (level jm) eqn: Hl; [constructor|].
   destruct Hwsat as (w & Jw & Hw).
   edestruct Jframe as (x' & H0' & Hpost); eauto.
   eapply safeN_external.
   { eassumption. }
   { eapply JDE1; eauto. }
   simpl. intros.
   assert (level jm = level z) as Hlz.
   { apply join_level in Jw as []; rewrite <- !level_juice_level_phi in *; lia. }
   (* We need to reconstruct the full jm, then find a sub-memory s.t.
      join sub w jm'. *)
   assert (H20: exists jm', m_dry jm' = m'
                    /\ (level jm' = n')%nat
                    /\ juicy_safety.pures_eq (m_phi z) (m_phi jm')
                    /\ resource_at (m_phi jm') = resource_fmap (approx (level jm')) (approx (level jm')) oo juicy_mem_lemmas.rebuild_juicy_mem_fmap z (m_dry jm')
                    /\ compcert_rmaps.RML.R.ghost_of (m_phi jm') = Some (ghost_PCM.ext_ghost z', compcert_rmaps.RML.R.NoneP) :: ghost_fmap (approx (level jm')) (approx (level jm')) (tl (ghost_of (m_phi z)))). {
     destruct (juicy_mem_lemmas.rebuild_juicy_mem_rmap z m')
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
     assert (mem_rmap_cohere m' phi') as H10. {
       clear - H0' Hr1 Hl1 H8 H7 H5 H2 Hmem DME JDE1.
       eapply JDE1 in H0'; eauto.
       specialize (DME e _ _ _ _ _ _ _ _ _ _ H0' H5).
       subst phi'.
       apply age_to_cohere.
       subst phi1.
       apply set_ghost_cohere.
       eapply mem_evolve_cohere; eauto.
     }
     destruct H10 as [H10 [H11 [H12 H13]]].
     pose (jm' := mkJuicyMem _ _ H10 H11 H12 H13).
     exists jm'.
     assert (n' <= level phi1)%nat by lia.
     split; [ | split3].
     * subst jm'; simpl; auto.
     * subst jm' phi'; simpl. apply age_to.level_age_to; auto.
     * unfold juicy_safety.pures_eq, juicy_safety.pures_sub. subst jm' phi'; simpl.
       split; intros; rewrite age_to_resource_at.age_to_resource_at, Hr1, H7;
         unfold juicy_mem_lemmas.rebuild_juicy_mem_fmap; destruct (m_phi z @ _); simpl; eauto;
         try solve [try (destruct k; auto); if_tac; auto].
       rewrite age_to.level_age_to; auto.
     * subst jm' phi'; simpl. split.
       { extensionality. rewrite age_to_resource_at.age_to_resource_at, Hr1, H7.
         rewrite age_to.level_age_to; auto. }
       rewrite age_to_resource_at.age_to_ghost_of, age_to.level_age_to; auto.
       subst phi1.
       unfold initial_world.set_ghost; rewrite ghost_of_make_rmap, H8; auto.
   }
   destruct H20 as [jm' [H26 [H27 [H28 [H29 Hg']]]]].
   subst m'; eapply JDE2 in H5; eauto 7; [|lia].
   apply Hpost in H5 as (jm1 & ? & ? & Jw').
   specialize (H1 ret jm1 z' Hargsty Hretty).
   assert (level jm1 = level jm') as Hl1 by (apply join_level in Jw' as []; rewrite <- !level_juice_level_phi in *; lia).
   spec H1.
   { split; [lia|].
     eapply juicy_safety.pures_eq_trans, juicy_safety.pures_eq_trans; [| apply join_sub_pures_eq; eexists; eauto | | eauto |];
       rewrite <- ?level_juice_level_phi; try lia.
     apply pures_eq_sym, join_sub_pures_eq; [|eexists; eauto].
     rewrite <- !level_juice_level_phi; auto. }
   spec H1. assumption.
   destruct H1 as [c' [H2a H2b]]; exists c'; split; auto.
   (* eliminate fupd *)
   assert (app_pred (invariants.wsat * invariants.ghost_set invariants.g_en Ensembles.Full_set)%pred
         (age_to.age_to (level jm1) w)).
   { eapply pred_nec_hereditary, Hw; apply age_to.age_to_necR. }
   edestruct H2b as (x1 & ? & Hz' & Hsafe); eauto.
   { apply join_sub_refl. }
   { rewrite Hg'; eexists; do 2 constructor; simpl.
     instantiate (1 := (_, _)); split; simpl; [apply semax_prog.ext_ref_join | repeat constructor]. }
   assert (level x1 = level jm') as Hl'.
   { destruct Hz' as (? & ? & ?); lia. }
   subst n'; destruct Hsafe as [Hsafe | (m2 & ? & ? & ? & ? & Hsafe)].
   { rewrite <- Hl', Hsafe; constructor. }
   assert (level jm' = level m2) as Hl2 by (apply join_level in H8 as []; rewrite <- !level_juice_level_phi in *; lia).
   rewrite Hl2.
   destruct Hz' as [<- ?].
   apply IHn; eauto. lia.
 - eapply safeN_halted; eauto.
   eapply Esub; eauto.
   apply JDE; auto.
Qed.

Definition fun_id (ext_link: Strings.String.string -> ident) (ef: external_function) : option ident :=
  match ef with EF_external id sig => Some (ext_link id) | _ => None end.
