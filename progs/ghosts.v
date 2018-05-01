Require Import VST.veric.compcert_rmaps.
Require Export VST.msl.ghost.
Require Import VST.msl.sepalg.
Require Import VST.msl.sepalg_generators.
Require Import VST.veric.SeparationLogic.
Require Import VST.progs.conclib.

(* Lemmas about ghost state and common instances *)
(* Where should this sit? *)

Hint Resolve Share.nontrivial.

Definition gname := own.gname.

Instance Inhabitant_preds : Inhabitant preds := NoneP.

Section ghost.

Context {RA: Ghost}.

Lemma own_op' : forall g a1 a2 pp,
  own g a1 pp * own g a2 pp = EX a3 : _, !!(join a1 a2 a3 /\ valid a3) && own g a3 pp.
Proof.
  intros.
  apply pred_ext.
  - assert_PROP (valid_2 a1 a2) as Hjoin by (apply own_valid_2).
    destruct Hjoin as (a3 & ? & ?); Exists a3; entailer!.
    erewrite <- own_op by eauto.  apply derives_refl.
  - Intros a3.
    erewrite own_op by eauto.  apply derives_refl.
Qed.

Lemma own_op_gen : forall g a1 a2 a3 pp, (valid_2 a1 a2 -> join a1 a2 a3) ->
  own g a1 pp * own g a2 pp = !!(valid_2 a1 a2) && own g a3 pp.
Proof.
  intros; apply pred_ext.
  - assert_PROP (valid_2 a1 a2) as Hv by apply own_valid_2.
    erewrite <- own_op by eauto; entailer!.
  - Intros.
    erewrite own_op by eauto; entailer!.
Qed.

Lemma own_precise : forall g a pp, precise (own g a pp).
Proof.
  intros ?????? (? & ? & Hg1) (? & ? & Hg2) J1 J2; simpl in *.
  apply rmap_ext.
  - destruct J1 as [? ?%join_level], J2 as [? ?%join_level]; omega.
  - intro; apply join_sub_same_identity with (a0 := w1 @ l)(c := w @ l); auto.
    + apply identity_unit'; auto.
    + eapply join_sub_unit_for, resource_at_join_sub; eauto.
      apply identity_unit'; auto.
    + apply resource_at_join_sub; auto.
  - rewrite Hg1, Hg2.
    destruct J1 as [? ?%join_level], J2 as [? ?%join_level].
    replace (level w1) with (level w2) by omega.
    f_equal; f_equal; f_equal; f_equal.
    apply exist_ext; auto.
Qed.

Lemma own_list_alloc : forall a0 la lp, Forall valid la -> length lp = length la ->
  emp |-- |==> (EX lg : _, !!(Zlength lg = Zlength la) && fold_right sepcon emp
    (map (fun i => own (Znth i lg) (@Znth _ a0 i la) (Znth i lp))
    (upto (Z.to_nat (Zlength la))))).
Proof.
  intros until 1; revert lp; induction H; intros.
  - eapply derives_trans, bupd_intro.
    Exists (@nil own.gname). simpl. entailer!.
  - destruct lp; inv H1.
    rewrite <- emp_sepcon at 1.
    eapply derives_trans; [apply sepcon_derives; [apply IHForall; eauto | apply own_alloc; eauto]|].
    eapply derives_trans; [apply bupd_sepcon|].
    apply bupd_mono.
    Intros lg g.
    Exists (g :: lg); rewrite !Zlength_cons, Z2Nat.inj_succ by apply Zlength_nonneg.
    rewrite (upto_app 1), map_app, sepcon_app; simpl.
    rewrite !Znth_0_cons; entailer!.
    rewrite sepcon_comm; apply sepcon_derives; [apply derives_refl|].
    erewrite map_map, map_ext_in; eauto; intros; simpl.  apply derives_refl.
    rewrite In_upto in *; rewrite !Znth_pos_cons by omega.
    rewrite Z.add_comm, Z.add_simpl_r; auto.
Qed.

Corollary own_list_alloc' : forall a pp i, 0 <= i -> valid a ->
  emp |-- |==> (EX lg : _, !!(Zlength lg = i) &&
    fold_right sepcon emp (map (fun i => own (Znth i lg) a pp) (upto (Z.to_nat i)))).
Proof.
  intros.
  eapply derives_trans;
    [apply own_list_alloc with (a0 := a)(la := repeat a (Z.to_nat i))(lp := repeat pp (Z.to_nat i))|].
  { apply Forall_repeat; auto. }
  { rewrite !repeat_length; auto. }
  apply bupd_mono; Intros lg; Exists lg.
  rewrite Zlength_repeat, Z2Nat.id in H1 |- * by auto.
  apply andp_right; [entailer!|].
  erewrite map_ext_in; eauto; intros; simpl.  apply derives_refl.
  apply In_upto in H2.
  rewrite !Znth_repeat'; auto.
Qed.

Lemma own_list_dealloc : forall {A} (l : list A) g a p,
  fold_right sepcon emp (map (fun i => own (g i) (a i) (p i)) l) |-- |==> emp.
Proof.
  induction l; simpl; intros.
  - apply bupd_intro.
  - eapply derives_trans; [apply sepcon_derives, IHl; apply own_dealloc|].
    eapply derives_trans, bupd_mono; [apply bupd_sepcon | cancel].
Qed.

End ghost.

Instance exclusive_PCM A : Ghost := { valid a := True; Join_G := Join_lower (Join_discrete A) }.
Proof. auto. Defined.

Definition excl {A} g a := @own _ _ _ _ _ _ (exclusive_PCM A) g (Some a) NoneP.

Lemma exclusive_update : forall {A} (v v' : A) p, excl p v |-- |==> excl p v'.
Proof.
  intros; apply own_update.
  intros ? (? & ? & _).
  exists (Some v'); split; simpl; auto; inv H; constructor.
  inv H1.
Qed.

Instance prod_PCM (GA GB: Ghost): Ghost := { G := @G GA * @G GB;
  valid a := valid (fst a) /\ valid (snd a); Join_G := Join_prod _ _ _ _ }.
Proof.
  intros ??? [] []; split; eapply join_valid; eauto.
Defined.

(* Can we use Santiago and Qinxiang's paper to simplify this? *)
Class PCM_order `{P : Ghost} (ord : G -> G -> Prop) := { ord_refl :> RelationClasses.Reflexive ord;
  ord_trans :> RelationClasses.Transitive ord;
  ord_lub : forall a b c, ord a c -> ord b c -> {c' | join a b c' /\ ord c' c};
  join_ord : forall a b c, join a b c -> ord a c /\ ord b c; ord_join : forall a b, ord b a -> join a b a }.

(*Class lub_ord {A} (ord : A -> A -> Prop) := { lub_ord_refl :> RelationClasses.Reflexive ord;
  lub_ord_trans :> RelationClasses.Transitive ord;
  has_lub : forall a b c, ord a c -> ord b c -> exists c', ord a c' /\ ord b c' /\
    forall d, ord a d -> ord b d -> ord c' d }.

Global Instance ord_PCM `{lub_ord} : Ghost := { Join_G a b c := ord a c /\ ord b c /\
  forall c', ord a c' -> ord b c' -> ord c c' }.
Proof.
  - 
  - intros ??? (? & ? & ?); eauto.
  - intros ????? (? & ? & Hc) (? & ? & He).
    destruct (has_lub b d e) as (c' & ? & ? & Hlub); try solve [etransitivity; eauto].
    exists c'; repeat split; auto.
    + etransitivity; eauto.
    + apply Hlub; auto; transitivity c; auto.
    + intros.
      apply He.
      * apply Hc; auto; etransitivity; eauto.
      * etransitivity; eauto.
Defined.

Global Instance ord_PCM_ord `{lub_ord} : PCM_order ord.
Proof.
  constructor.
  - apply lub_ord_refl.
  - apply lub_ord_trans.
  - intros ??? Ha Hb.
    destruct (has_lub _ _ _ Ha Hb) as (c' & ? & ? & ?).
    exists c'; simpl; eauto.
  - simpl; intros; tauto.
  - intros; simpl.
    repeat split; auto.
    reflexivity.
Defined.*)

(* Instances of ghost state *)
Section Snapshot.
(* One common kind of PCM is one in which a central authority has a reference copy, and clients pass around
   partial knowledge. *)

Context `{ORD : PCM_order}.

Lemma join_refl : forall (v : G), join v v v.
Proof.
  intros. apply ord_join; reflexivity.
Qed.

Lemma join_compat : forall v1 v2 v' v'', join v2 v' v'' -> ord v1 v2 -> exists v0, join v1 v' v0 /\ ord v0 v''.
Proof.
  intros.
  destruct (join_ord _ _ _ H).
  destruct (ord_lub v1 v' v'') as (? & ? & ?); eauto.
  etransitivity; eauto.
Qed.

Lemma join_ord_eq : forall a b, ord a b <-> exists c, join a c b.
Proof.
  split.
  - intros; exists b.
    apply ord_join in H.
    apply join_comm; auto.
  - intros (? & H); apply join_ord in H; tauto.
Qed.

(* The master-snapshot PCM in the RCU paper divides the master into shares, which is useful for having both
   an authoritative writer and an up-to-date invariant. *)

Global Instance snap_PCM : Ghost :=
  { valid _ := True; Join_G a b c := sepalg.join (fst a) (fst b) (fst c) /\
      if eq_dec (fst a) Share.bot then if eq_dec (fst b) Share.bot then join (snd a) (snd b) (snd c)
        else ord (snd a) (snd b) /\ snd c = snd b else snd c = snd a /\
          if eq_dec (fst b) Share.bot then ord (snd b) (snd a) else snd c = snd b }.
Proof.
  2: constructor.
  - exists (fun '(sh, a) => (Share.bot, core a)); repeat intro.
    + destruct t; constructor; auto; simpl.
      rewrite eq_dec_refl.
      if_tac; [apply core_unit | split; auto].
      rewrite join_ord_eq; eexists; apply core_unit.
    + destruct a, b, c; f_equal.
      inv H; simpl in *.
      destruct (eq_dec t Share.bot); [|destruct H1; subst; auto].
      subst; apply bot_identity in H0; subst.
      destruct (eq_dec t1 Share.bot); [|destruct H1; subst; auto].
      * eapply join_core; eauto.
      * rewrite join_ord_eq in H; destruct H.
        eapply join_core; eauto.
  - intros ???? [? Hjoin1] [? Hjoin2].
    assert (fst z = fst z') by (eapply join_eq; eauto).
    destruct z, z'; simpl in *; subst; f_equal.
    destruct (eq_dec (fst x) Share.bot); [|destruct Hjoin1, Hjoin2; subst; auto].
    destruct (eq_dec (fst y) Share.bot); [|destruct Hjoin1, Hjoin2; subst; auto].
    eapply join_eq; eauto.
  - intros ????? [Hsh1 Hjoin1] [Hsh2 Hjoin2].
    destruct (sepalg.join_assoc Hsh1 Hsh2) as [sh' []].
    destruct (eq_dec (fst b) Share.bot) eqn: Hb.
    + assert (fst d = fst a) as Hd.
      { eapply sepalg.join_eq; eauto.
        rewrite e0; apply join_bot_eq. }
      rewrite Hd in *.
      assert (sh' = fst c) as Hc.
      { eapply sepalg.join_eq; eauto.
        rewrite e0; apply bot_join_eq. }
      rewrite Hc in *.
      destruct (eq_dec (fst c) Share.bot) eqn: Hc1.
      * destruct (eq_dec (fst a) Share.bot) eqn: Ha.
        -- destruct (join_assoc Hjoin1 Hjoin2) as [c' []].
           exists (Share.bot, c'); split; split; rewrite ?e2, ?e0, ?e1, ?eq_dec_refl in *; auto.
        -- destruct Hjoin1 as [Hc' ?]; rewrite Hc' in *.
           destruct Hjoin2, (ord_lub (snd b) (snd c) (snd a)) as [c' []]; eauto.
           exists (Share.bot, c'); split; split; rewrite ?e0, ?e1, ?eq_dec_refl, ?Ha in *; auto.
      * exists c.
        destruct (eq_dec (fst a) Share.bot) eqn: Ha; try solve [split; split; auto].
        -- destruct Hjoin2.
           apply join_ord in Hjoin1; destruct Hjoin1.
           split; split; rewrite ?e0, ?Ha, ?Hc1, ?eq_dec_refl; auto; split; auto; etransitivity; eauto.
        -- destruct Hjoin2 as [He1 He2]; rewrite He1, He2 in *.
           destruct Hjoin1 as [Hd' ?]; rewrite Hd' in *; split; split; rewrite ?e0, ?Ha, ?Hc1, ?eq_dec_refl, ?Hd'; auto.
    + exists (sh', snd b); simpl.
      destruct (eq_dec (fst d) Share.bot).
      { rewrite e0 in Hsh1; apply join_Bot in Hsh1; destruct Hsh1; contradiction. }
      destruct (eq_dec sh' Share.bot) eqn: Hn'.
      { subst; apply join_Bot in H; destruct H; contradiction. }
      assert (snd d = snd b) as Hd by (destruct (eq_dec (fst a) Share.bot); tauto).
      destruct Hjoin2 as [He ?]; rewrite He in *; split; split; simpl; rewrite ?Hb, ?Hn', ?Hd, ?He in *; auto.
  - intros ??? []; split; [apply join_comm; auto|].
    if_tac; if_tac; auto; tauto.
  - intros ???? [? Hjoin1] [? Hjoin2].
    assert (fst a = fst b) by (eapply join_positivity; eauto).
    destruct (eq_dec (fst a) Share.bot), a, a', b, b'; simpl in *; subst; f_equal.
    + apply join_Bot in H0 as []; subst.
      apply join_Bot in H as []; subst.
      rewrite eq_dec_refl in Hjoin1, Hjoin2, Hjoin2.
      eapply join_positivity; eauto.
    + destruct Hjoin1; auto.
  - auto.
Defined.

Definition ghost_snap (a : @G P) p := own p (Share.bot, a) NoneP.

Lemma ghost_snap_join : forall v1 v2 p v, join v1 v2 v ->
  ghost_snap v1 p * ghost_snap v2 p = ghost_snap v p.
Proof.
  intros; symmetry; apply own_op.
  split; simpl; rewrite ?eq_dec_refl; auto.
Qed.

Lemma ghost_snap_conflict : forall v1 v2 p, ghost_snap v1 p * ghost_snap v2 p |-- !!(joins v1 v2).
Proof.
  intros; eapply derives_trans; [apply own_valid_2|].
  apply prop_left; intros ((?, a) & (? & Hj) & _); simpl in Hj.
  rewrite !eq_dec_refl in Hj.
  apply prop_right; exists a; auto.
Qed.

Lemma ghost_snap_join' : forall v1 v2 p,
  ghost_snap v1 p * ghost_snap v2 p = EX v : _, !!(join v1 v2 v) && ghost_snap v p.
Proof.
  intros; apply pred_ext.
  - assert_PROP (joins v1 v2) as H by apply ghost_snap_conflict.
    destruct H as [v]; Exists v; entailer!.
    erewrite ghost_snap_join; eauto.  apply derives_refl.
  - Intros v; erewrite ghost_snap_join; eauto.  apply derives_refl.
Qed.

Definition ghost_master sh (a : @G P) p := own p (sh, a) NoneP.

Lemma snap_master_join : forall v1 sh v2 p, sh <> Share.bot ->
  ghost_snap v1 p * ghost_master sh v2 p = !!(ord v1 v2) && ghost_master sh v2 p.
Proof.
  intros; setoid_rewrite own_op'.
  apply pred_ext.
  - Intros a3.
    destruct a3 as (sh', ?), H0 as [Hsh Hj]; simpl in *.
    apply bot_identity in Hsh; subst sh'.
    rewrite eq_dec_refl in Hj.
    destruct (eq_dec sh Share.bot); [contradiction|].
    destruct Hj; subst; entailer!.
    apply derives_refl.
  - Intros; Exists (sh, v2); entailer!.
    split; simpl; rewrite ?eq_dec_refl.
    + apply bot_join_eq.
    + if_tac; auto; contradiction.
    + apply derives_refl.
Qed.

Corollary snaps_master_join : forall lv sh v2 p, sh <> Share.bot ->
  fold_right sepcon emp (map (fun v => ghost_snap v p) lv) * ghost_master sh v2 p =
  !!(Forall (fun v1 => ord v1 v2) lv) && ghost_master sh v2 p.
Proof.
  induction lv; simpl; intros.
  - rewrite emp_sepcon, prop_true_andp; auto.
  - rewrite sepcon_comm, <- sepcon_assoc, (sepcon_comm (ghost_master _ _ _)), snap_master_join by auto.
    apply pred_ext.
    + Intros; rewrite sepcon_comm, IHlv by auto; entailer!.
    + Intros.
      match goal with H : Forall _ _ |- _ => inv H end.
      rewrite prop_true_andp, sepcon_comm, IHlv by auto; entailer!.
Qed.

Lemma master_update : forall v v' p, ord v v' -> ghost_master Tsh v p |-- |==> ghost_master Tsh v' p.
Proof.
  intros; apply own_update.
  intros ? (x & Hj & _); simpl in Hj.
  exists (Tsh, v'); simpl; split; auto.
  destruct Hj as [Hsh Hj]; simpl in *.
  apply join_Tsh in Hsh as []; destruct c, x; simpl in *; subst.
  split; auto; simpl.
  fold share in *; destruct (eq_dec Tsh Share.bot); [contradiction Share.nontrivial|].
  destruct Hj as [? Hc']; subst.
  rewrite eq_dec_refl in Hc' |- *; split; auto.
  etransitivity; eauto.
Qed.

Lemma master_init : forall (a : @G P), exists g', joins (Tsh, a) g'.
Proof.
  intros; exists (Share.bot, a), (Tsh, a); simpl.
  split; auto; simpl.
  apply join_refl.
Qed.

Lemma make_snap : forall (sh : share) v p, ghost_master sh v p |-- |==> ghost_snap v p * ghost_master sh v p.
Proof.
  intros; destruct (eq_dec sh Share.bot).
  - subst; setoid_rewrite ghost_snap_join; [apply bupd_intro | apply join_refl].
  - rewrite snap_master_join by auto.
    eapply derives_trans, bupd_intro; entailer!.
Qed.

Lemma ghost_snap_forget : forall v1 v2 p, ord v1 v2 -> ghost_snap v2 p |-- |==> ghost_snap v1 p.
Proof.
  intros; apply own_update.
  intros (shc, c) [(shx, x) [[? Hj] _]]; simpl in *.
  rewrite eq_dec_refl in Hj.
  assert (shx = shc) by (eapply sepalg.join_eq; eauto); subst.
  unfold share in Hj; destruct (eq_dec shc Share.bot); subst.
  - destruct (join_compat _ _ _ _ Hj H) as [x' []].
    exists (Share.bot, x'); simpl; split; auto; split; auto; simpl.
    rewrite !eq_dec_refl; auto.
  - destruct Hj; subst.
    exists (shc, c); simpl; split; auto; split; auto; simpl.
    rewrite eq_dec_refl; if_tac; [contradiction|].
    split; auto.
    etransitivity; eauto.
Qed.

Lemma ghost_snap_choose : forall v1 v2 p, ghost_snap v1 p * ghost_snap v2 p |-- |==> ghost_snap v1 p.
Proof.
  intros.
  setoid_rewrite own_op'.
  Intros v'.
  destruct v', H as [Hsh Hj]; apply bot_identity in Hsh; simpl in *; subst.
  rewrite !eq_dec_refl in Hj.
  apply ghost_snap_forget.
  rewrite join_ord_eq; eauto.
Qed.

Lemma master_share_join : forall sh1 sh2 sh v p, sepalg.join sh1 sh2 sh ->
  ghost_master sh1 v p * ghost_master sh2 v p = ghost_master sh v p.
Proof.
  intros; symmetry; apply own_op; split; auto; simpl.
  if_tac; if_tac; try split; auto; try apply ord_refl; apply join_refl.
Qed.

Lemma master_inj : forall sh1 sh2 v1 v2 p, readable_share sh1 -> readable_share sh2 ->
  ghost_master sh1 v1 p * ghost_master sh2 v2 p |-- !!(v1 = v2).
Proof.
  intros.
  eapply derives_trans; [apply own_valid_2|].
  apply prop_left; intros ((?, ?) & [[? Hj] _]); simpl in Hj.
  fold share in *.
  destruct (eq_dec sh1 Share.bot); [subst; contradiction unreadable_bot|].
  destruct (eq_dec sh2 Share.bot); [subst; contradiction unreadable_bot|].
  destruct Hj; subst; apply prop_right; auto.
Qed.

Lemma master_share_join' : forall sh1 sh2 sh v1 v2 p, readable_share sh1 -> readable_share sh2 ->
  sepalg.join sh1 sh2 sh ->
  ghost_master sh1 v1 p * ghost_master sh2 v2 p = !!(v1 = v2) && ghost_master sh v2 p.
Proof.
  intros; apply pred_ext.
  - assert_PROP (v1 = v2) by (apply master_inj; auto).
    subst; erewrite master_share_join; eauto; entailer!.
  - Intros; subst.
    erewrite master_share_join; eauto.  apply derives_refl.
Qed.

(* useful when we only want to deal with full masters *)
Definition ghost_master1 a p := ghost_master Tsh a p.

Lemma snap_master_join1 : forall v1 v2 p,
  ghost_snap v1 p * ghost_master1 v2 p = !!(ord v1 v2) && ghost_master1 v2 p.
Proof.
  intros; apply snap_master_join, Share.nontrivial.
Qed.

Lemma snap_master_update1 : forall v1 v2 p v', ord v2 v' ->
  ghost_snap v1 p * ghost_master1 v2 p |-- |==> ghost_snap v' p * ghost_master1 v' p.
Proof.
  intros; rewrite !snap_master_join1.
  Intros.
  eapply derives_trans; [apply master_update; eauto|].
  apply bupd_mono; entailer!.
  apply derives_refl.
Qed.

End Snapshot.

Section Reference.
(* One common kind of PCM is one in which a central authority has a reference copy, and clients pass around
   partial knowledge. When a client recovers all pieces, it can gain full knowledge. *)
(* This is related to the snapshot PCM, but the snapshots aren't duplicable. *)

Global Instance pos_PCM (P : Ghost) : Ghost := { G := option (share * G);
  valid a := match a with Some (sh, _) => sh <> Share.bot | _ => True end;
  Join_G a b c := match a, b, c with
  | Some (sha, a'), Some (shb, b'), Some (shc, c') =>
      sha <> Share.bot /\ shb <> Share.bot /\ sepalg.join sha shb shc /\ join a' b' c'
  | Some (sh, a), None, Some c' | None, Some (sh, a), Some c' => c' = (sh, a)
  | None, None, None => True
  | _, _, _ => False
  end }.
Proof.
  2: constructor.
  - exists (fun _ => None); auto.
    intros [[]|]; constructor.
  - intros [[]|] [[]|] [[]|] [[]|]; unfold join; simpl; auto; try contradiction; try congruence.
    intros (? & ? & ? & ?) (? & ? & ? & ?); f_equal; f_equal; eapply join_eq; eauto.
  - intros [[]|] [[]|] [[]|] [[]|] [[]|]; try contradiction; unfold join; simpl;
      intros; decompose [and] H; decompose [and] H0;
      repeat match goal with H : (_, _) = (_, _) |- _ => inv H end;
      try solve [eexists (Some _); split; auto; simpl; auto]; try solve [exists None; split; auto].
    + destruct (join_assoc H2 H6) as (sh' & ? & ?), (join_assoc H5 H9) as (a' & ? & ?).
      exists (Some (sh', a')); repeat (split; auto).
      intro; subst.
      apply join_Bot in H8 as []; auto.
    + exists (Some (s2, g2)); auto.
  - intros [[]|] [[]|] [[]|]; try contradiction; unfold join; auto.
    intros (? & ? & ? & ?); split; auto; split; auto; split; apply join_comm; auto.
  - intros [[]|] [[]|] [[]|] [[]|]; try contradiction; auto.
    intros (? & ? & ? & ?) (? & ? & ? & ?); f_equal; f_equal; eapply join_positivity; eauto.
  - intros [[]|] [[]|] [[]|]; try contradiction; auto.
    + intros []; auto.
    + unfold join; simpl; congruence.
Defined.

Definition completable {P : Ghost} (a: @G (pos_PCM P)) r := exists x, join a x (Some (Tsh, r)).

Global Instance ref_PCM (P : Ghost) : Ghost :=
{ valid a := valid (fst a) /\ match snd a with Some r => completable (fst a) r | None => True end;
  Join_G a b c := @Join_G (pos_PCM P) (fst a) (fst b) (fst c) /\
    @psepalg.Join_lower _ (psepalg.Join_discrete _) (snd a) (snd b) (snd c) }.
Proof.
  - apply sepalg_generators.Sep_prod.
    + apply @Sep_G.
    + apply psepalg.Sep_option.
  - apply sepalg_generators.Perm_prod.
    + apply @Perm_G.
    + apply psepalg.Perm_option.
  - intros ??? [? J] []; split; [eapply join_valid; eauto|].
    destruct a, b, c; simpl in *; inv J; auto.
    + destruct o1; auto.
      destruct H1.
      destruct (join_assoc H H1) as (? & ? & ?); eexists; eauto.
    + inv H2.
Defined.

Lemma ref_sub : forall {P : Ghost} (sh : share) g (a b : @G P) pp,
  @own _ _ _ _ _ _ (ref_PCM P) g (Some (sh, a), None) pp * @own _ _ _ _ _ _ (ref_PCM P) g (None, Some b) pp |--
    !!(if eq_dec sh Tsh then a = b else exists x, join a x b).
Proof.
  intros.
  eapply derives_trans; [apply own_valid_2|].
  apply prop_left; intros (c & [Hsh Hj] & ?); simpl in *.
  apply prop_right.
  destruct (fst c); [subst | contradiction].
  inv Hj.
  rewrite <- H0 in H.
  destruct H as (? & c' & Hsub).
  destruct c' as [(?, ?)|].
  - destruct Hsub as (? & ? & Hsh & ?).
    if_tac; eauto; subst.
    apply join_Tsh in Hsh; tauto.
  - inv Hsub.
    rewrite eq_dec_refl; auto.
Qed.

End Reference.

Section Discrete.

Instance discrete_PCM (A : Type) : Ghost := { valid a := True;
  Join_G := Join_equiv A }.
Proof.
  auto.
Defined.

End Discrete.

Section GVar.

Context {A : Type}.

Definition ghost_var (sh : share) (v : A) g :=
  @own _ _ _ _ _ _ (@pos_PCM (discrete_PCM A)) g (Some (sh, v)) NoneP.

Lemma ghost_var_share_join : forall sh1 sh2 sh v p, sepalg.join sh1 sh2 sh ->
  sh1 <> Share.bot -> sh2 <> Share.bot ->
  ghost_var sh1 v p * ghost_var sh2 v p = ghost_var sh v p.
Proof.
  intros; symmetry; apply own_op.
  repeat (split; auto).
Qed.

Lemma ghost_var_share_join_gen : forall sh1 sh2 v1 v2 p,
  ghost_var sh1 v1 p * ghost_var sh2 v2 p = EX sh : _,
  !!(v1 = v2 /\ sh1 <> Share.bot /\ sh2 <> Share.bot /\ sepalg.join sh1 sh2 sh) && ghost_var sh v1 p.
Proof.
  intros; setoid_rewrite own_op'.
  apply pred_ext.
  - Intros a.
    destruct a as [(sh, v')|]; inv H.
    destruct H2 as (? & ? & Hv); inv Hv.
    Exists sh; entailer!.
    apply derives_refl.
  - Intros sh; subst.
    Exists (Some (sh, v2)); apply andp_right, derives_refl.
    apply prop_right; repeat (split; auto); simpl.
    intro; subst; apply join_Bot in H2 as []; contradiction.
Qed.

Lemma ghost_var_inj : forall sh1 sh2 v1 v2 p, sh1 <> Share.bot -> sh2 <> Share.bot ->
  ghost_var sh1 v1 p * ghost_var sh2 v2 p |-- !!(v1 = v2).
Proof.
  intros; rewrite ghost_var_share_join_gen; Intros sh; entailer!.
Qed.

Lemma ghost_var_share_join' : forall sh1 sh2 sh v1 v2 p, sh1 <> Share.bot -> sh2 <> Share.bot ->
  sepalg.join sh1 sh2 sh ->
  ghost_var sh1 v1 p * ghost_var sh2 v2 p = !!(v1 = v2) && ghost_var sh v2 p.
Proof.
  intros; rewrite ghost_var_share_join_gen.
  apply pred_ext.
  - Intros sh'; entailer!.
    eapply join_eq in H1; eauto; subst; auto.
  - Intros; Exists sh; entailer!.
Qed.

Lemma ghost_var_update : forall v p v', ghost_var Tsh v p |-- |==> ghost_var Tsh v' p.
Proof.
  intros; apply own_update.
  intros [[]|] ([[]|] & J & ?); inv J.
  - destruct H1 as (? & ?%join_Tsh & ?); tauto.
  - exists (Some (Tsh, v')); split; [constructor | auto].
Qed.

Lemma ex_ghost_var_exclusive : forall sh p, exclusive_mpred (EX v : A, ghost_var sh v p).
Proof.
  intros; unfold exclusive_mpred.
  Intros v v'; setoid_rewrite own_op'.
  Intros a; destruct a as [[]|]; simpl in *; try contradiction.
  destruct H as (? & _ & ?%sepalg.join_self%identity_share_bot & _); contradiction.
Qed.

Lemma ghost_var_exclusive : forall sh v p, exclusive_mpred (ghost_var sh v p).
Proof.
  intros; eapply derives_exclusive, ex_ghost_var_exclusive.
  Exists v; apply derives_refl.
Qed.

End GVar.

Section PVar.
(* Like ghost variables, but the partial values may be out of date. *)

Global Instance nat_PCM: Ghost := { valid a := True; Join_G a b c := c = Nat.max a b }.
Proof.
  2: constructor.
  - exists (fun _ => O); auto; intros.
    apply Nat.max_0_l.
  - unfold join; congruence.
  - unfold join; eexists; split; eauto.
    rewrite Nat.max_assoc; subst; auto.
  - unfold join; intros.
    rewrite Nat.max_comm; auto.
  - unfold join; intros.
    apply Nat.le_antisymm; [subst b | subst a]; apply Nat.le_max_l.
  - auto.
Defined.

Global Instance max_order : PCM_order le.
Proof.
  constructor; auto; intros.
  - intros ???; omega.
  - eexists; unfold join; simpl; split; eauto.
    apply Nat.max_lub; auto.
  - hnf in H; subst.
    split; [apply Nat.le_max_l | apply Nat.le_max_r].
  - hnf.
    rewrite Nat.max_l; auto.
Defined.

Lemma ghost_snap_join_N : forall v1 v2 p, ghost_snap v1 p * ghost_snap v2 p = ghost_snap (Nat.max v1 v2) p.
Proof.
  intros; apply ghost_snap_join; hnf; auto.
Qed.

Lemma snap_master_join' : forall v1 v2 p,
  ghost_snap v1 p * ghost_master1 v2 p = !!(v1 <= v2)%nat && ghost_master1 v2 p.
Proof.
  intros; apply snap_master_join1.
Qed.

Lemma snap_master_update' : forall (v1 v2 : nat) p v', (v2 <= v')%nat ->
  ghost_snap v1 p * ghost_master1 v2 p |-- |==> ghost_snap v' p * ghost_master1 v' p.
Proof.
  intros; apply snap_master_update1; auto.
Qed.

End PVar.

Section Maps.

Context {A B : Type} {A_eq : EqDec A}.

Implicit Types (k : A) (v : B) (m : A -> option B).

Definition map_upd m k v k' := if eq_dec k' k then Some v else m k'.

Lemma map_upd_triv : forall m k v, m k = Some v -> map_upd m k v = m.
Proof.
  intros; extensionality; unfold map_upd.
  if_tac; subst; auto.
Qed.

Fixpoint map_upd_list m l :=
  match l with
  | [] => m
  | (k, v) :: rest => map_upd_list (map_upd m k v) rest
  end.

Definition map_add m1 m2 k := match m1 k with Some v' => Some v' | None => m2 k end.

Definition empty_map k : option B := None.

Global Instance Inhabitant_map : Inhabitant (A -> option B) := empty_map.

Definition singleton k v k1 := if eq_dec k1 k then Some v else None.

Definition map_incl m1 m2 := forall k v, m1 k = Some v -> m2 k = Some v.

Global Instance map_incl_refl : RelationClasses.Reflexive map_incl.
Proof.
  repeat intro; auto.
Qed.

Global Instance map_incl_antisym : RelationClasses.Antisymmetric _ _ map_incl.
Proof.
  intros x y Hx Hy a.
  specialize (Hx a); specialize (Hy a).
  destruct (x a); [erewrite Hx; eauto|].
  destruct (y a); auto.
Qed.

Global Instance map_incl_trans : RelationClasses.Transitive map_incl.
Proof.
  repeat intro; auto.
Qed.

Lemma map_add_incl_compat : forall m1 m2 m3, map_incl m1 m2 -> map_incl (map_add m3 m1) (map_add m3 m2).
Proof.
  unfold map_add; repeat intro.
  destruct (m3 k); auto.
Qed.

Definition compatible m1 m2 := forall k v1 v2, m1 k = Some v1 -> m2 k = Some v2 -> v1 = v2.

Global Instance compatible_comm : RelationClasses.Symmetric compatible.
Proof.
  repeat intro.
  symmetry; eauto.
Qed.

Lemma map_add_comm : forall m1 m2, compatible m1 m2 -> map_add m1 m2 = map_add m2 m1.
Proof.
  intros; extensionality x; unfold map_add.
  destruct (m1 x) eqn: Hm1, (m2 x) eqn: Hm2; eauto.
Qed.

Global Instance map_join : Join (A -> option B) :=
  fun a b c => forall k v, c k = Some v <-> a k = Some v \/ b k = Some v.

Lemma map_join_spec : forall m1 m2 m3, join m1 m2 m3 <-> compatible m1 m2 /\ m3 = map_add m1 m2.
Proof.
  unfold join, map_join; simpl; split; intros.
  - split.
    + repeat intro.
      assert (m3 k = Some v1) as Hk by (rewrite H; auto).
      replace (m3 k) with (Some v2) in Hk by (symmetry; rewrite H; auto).
      inv Hk; auto.
    + extensionality x; unfold map_add.
      destruct (m1 x) eqn: Hm1; [rewrite H; auto|].
      destruct (m2 x) eqn: Hm2; [rewrite H; auto|].
      destruct (m3 x) eqn: Hm3; auto.
      rewrite H in Hm3; destruct Hm3 as [Hm3 | Hm3]; rewrite Hm3 in *; discriminate.
  - destruct H as [Hcompat]; subst; unfold map_add.
    destruct (m1 k) eqn: Hm1; split; auto; intros [?|?]; eauto; discriminate.
Qed.

Lemma map_add_assoc : forall m1 m2 m3, map_add (map_add m1 m2) m3 = map_add m1 (map_add m2 m3).
Proof.
  intros; extensionality; unfold map_add.
  destruct (m1 x); auto.
Qed.

Lemma compatible_add_assoc : forall m1 m2 m3, compatible m1 m2 ->
  compatible (map_add m1 m2) m3 -> compatible m1 (map_add m2 m3).
Proof.
  unfold compatible, map_add; intros.
  repeat match goal with H : forall _, _ |- _ => specialize (H k) end.
  replace (m1 k) with (Some v1) in *.
  destruct (m2 k); auto.
Qed.

Lemma compatible_incl : forall m1 m2 m (Hcompat : compatible m2 m) (Hincl : map_incl m1 m2), compatible m1 m.
Proof.
  repeat intro; eauto.
Qed.

Lemma map_incl_add : forall m1 m2, map_incl m1 (map_add m1 m2).
Proof.
  repeat intro; unfold map_add.
  rewrite H; auto.
Qed.

Global Instance map_PCM : Ghost := { valid a := True;
  Join_G a b c := forall k v, c k = Some v <-> a k = Some v \/ b k = Some v }.
Proof.
  2: constructor.
  - exists (fun _ => empty_map); auto; intros.
    split; auto.
    intros [|]; auto; discriminate.
  - intros.
    assert (forall k v, z k = Some v <-> z' k = Some v) as Heq.
    { intros.
      rewrite (H k); symmetry; apply H0. }
    extensionality k; specialize (Heq k).
    destruct (z k).
    + symmetry; apply Heq; auto.
    + destruct (z' k); auto.
      apply Heq; auto.
  - intros.
    rewrite map_join_spec in *.
    destruct H, H0; subst.
    rewrite map_add_assoc.
    eexists; rewrite !map_join_spec; repeat split.
    + eapply compatible_incl; eauto.
      rewrite map_add_comm by auto; apply map_incl_add.
    + apply compatible_add_assoc; auto.
  - intros ???; rewrite !map_join_spec; intros []; subst.
    split; [apply compatible_comm | apply map_add_comm]; auto.
  - intros.
    extensionality k; specialize (H k); specialize (H0 k).
    destruct (a k), (b k); auto.
    + apply H0; auto.
    + destruct (H b0) as [_ H']; lapply H'; auto.
    + destruct (H0 b0) as [_ H']; lapply H'; auto.
  - auto.
Defined.

Lemma map_incl_compatible : forall m1 m2 m3 (Hincl1 : map_incl m1 m3) (Hincl2 : map_incl m2 m3),
  compatible m1 m2.
Proof.
  intros; intros ??? Hk1 Hk2.
  apply Hincl1 in Hk1; apply Hincl2 in Hk2.
  rewrite Hk1 in Hk2; inv Hk2; auto.
Qed.

Lemma map_add_incl : forall m1 m2 m3, map_incl m1 m3 -> map_incl m2 m3 -> map_incl (map_add m1 m2) m3.
Proof.
  unfold map_add; intros.
  intros ?? Hk.
  destruct (m1 k) eqn: Hk1; auto.
  inv Hk; auto.
Qed.

Global Instance fmap_order : PCM_order map_incl.
Proof.
  constructor.
  - apply map_incl_refl.
  - apply map_incl_trans.
  - intros ??? Ha Hb; exists (map_add a b); split; simpl.
    + rewrite map_join_spec; split; auto.
      eapply map_incl_compatible; eauto.
    + apply map_add_incl; auto.
  - split; repeat intro; specialize (H k v); rewrite H; auto.
  - split; auto; intros [|]; auto.
Defined.

Lemma map_snap_join : forall m1 m2 p,
  ghost_snap m1 p * ghost_snap m2 p = !!(compatible m1 m2) && ghost_snap (map_add m1 m2) p.
Proof.
  intros; rewrite ghost_snap_join'.
  apply pred_ext.
  - Intros m.
    rewrite map_join_spec in H; destruct H; subst; entailer!.
  - Intros; Exists (map_add m1 m2).
    rewrite map_join_spec; entailer!.
Qed.

Lemma map_upd_list_app : forall l1 l2 m, map_upd_list m (l1 ++ l2) = map_upd_list (map_upd_list m l1) l2.
Proof.
  induction l1; auto; simpl; intros.
  destruct a; auto.
Qed.

Lemma map_upd_list_out : forall l m k, m k = None -> ~In k (map fst l) -> map_upd_list m l k = None.
Proof.
  induction l; auto; simpl; intros.
  destruct a; apply IHl.
  - unfold map_upd; if_tac; auto.
    subst; simpl in *; tauto.
  - tauto.
Qed.

Lemma compatible_k : forall m1 m2 (Hcompat : compatible m1 m2) k v, m2 k = Some v -> map_add m1 m2 k = Some v.
Proof.
  unfold compatible; intros.
  unfold map_add.
  destruct (m1 k) eqn: Hk; eauto.
Qed.

Lemma map_join_incl_compat : forall m1 m2 m' m'' (Hincl : map_incl m1 m2) (Hjoin : join m2 m' m''),
  exists m, join m1 m' m /\ map_incl m m''.
Proof.
  intros; apply (@join_comm _ _ (@Perm_G map_PCM)) in Hjoin.
  rewrite map_join_spec in Hjoin; destruct Hjoin as [Hjoin]; subst.
  do 2 eexists; [|apply map_add_incl_compat; eauto].
  symmetry in Hjoin; eapply compatible_incl in Hjoin; eauto.
  rewrite map_join_spec; split; auto.
  rewrite <- map_add_comm; auto.
Qed.

Lemma map_add_empty : forall m, map_add m empty_map = m.
Proof.
  intros; extensionality; unfold map_add, empty_map.
  destruct (m x); auto.
Qed.

Lemma map_upd_incl : forall m1 m2 k v, map_incl m1 m2 ->
  m2 k = Some v -> map_incl (map_upd m1 k v) m2.
Proof.
  unfold map_upd; repeat intro.
  destruct (eq_dec k0 k); [congruence | auto].
Qed.

Lemma map_add_single : forall m k v, map_add (singleton k v) m = map_upd m k v.
Proof.
  intros; extensionality; unfold map_add, singleton, map_upd; if_tac; auto.
Qed.

Lemma incl_compatible : forall m1 m2, map_incl m1 m2 -> compatible m1 m2.
Proof.
  intros; intros ??? Hk1 Hk2.
  specialize (H _ _ Hk1); rewrite H in Hk2; inv Hk2; auto.
Qed.

Lemma map_add_redundant : forall m1 m2, map_incl m1 m2 -> map_add m1 m2 = m2.
Proof.
  intros; unfold map_add; extensionality k.
  destruct (m1 k) eqn: Hk; auto; symmetry; auto.
Qed.

Lemma empty_map_incl : forall m, map_incl empty_map m.
Proof.
  repeat intro; discriminate.
Qed.

Lemma map_upd2_incl : forall m1 m2 k v, map_incl m1 m2 -> map_incl (map_upd m1 k v) (map_upd m2 k v).
Proof.
  unfold map_upd; repeat intro.
  if_tac; auto.
Qed.

Lemma compatible_upd : forall m1 m2 k v, compatible m1 m2 -> m2 k = None ->
  compatible (map_upd m1 k v) m2.
Proof.
  unfold map_upd; repeat intro.
  destruct (eq_dec k0 k); eauto; congruence.
Qed.

Lemma map_add_upd : forall m1 m2 k v, map_upd (map_add m1 m2) k v = map_add (map_upd m1 k v) m2.
Proof.
  intros.
  rewrite <- !map_add_single.
  rewrite map_add_assoc; auto.
Qed.

End Maps.

Hint Resolve empty_map_incl.

Section GHist.

(* Ghost histories in the style of Nanevsky *)
Context {hist_el : Type}.

Notation hist_part := (nat -> option hist_el).

Definition hist_sub sh (h : hist_part) hr := sh <> Share.bot /\ if eq_dec sh Tsh then h = hr
  else map_incl h hr.

Lemma completable_alt : forall sh h hr, @completable map_PCM (Some (sh, h)) hr <-> hist_sub sh h hr.
Proof.
  unfold completable, hist_sub; intros; simpl; split.
  - intros ([(?, ?)|] & Hcase).
    + destruct Hcase as (? & ? & Hsh & Hj); split; auto.
      if_tac.
      * subst; apply join_Tsh in Hsh; tauto.
      * rewrite (@join_ord_eq _ _ fmap_order); eauto.
    + hnf in Hcase.
      inv Hcase.
      rewrite eq_dec_refl; auto.
  - if_tac.
    + intros []; subst; exists None; split; auto.
    + rewrite (@join_ord_eq _ _ fmap_order).
      intros (? & h' & ?); exists (Some (Share.comp sh, h')).
      split; auto.
      split.
      { intro Hbot; contradiction H.
        rewrite <- Share.comp_inv at 1.
        rewrite Hbot; apply comp_bot. }
      split; [apply comp_join_top | auto].
Qed.

Lemma hist_sub_upd : forall sh h hr t' e (Hsub : hist_sub sh h hr),
  hist_sub sh (map_upd h t' e) (map_upd hr t' e).
Proof.
  unfold hist_sub; intros.
  destruct Hsub; split; auto.
  if_tac; subst; auto.
  apply map_upd2_incl; auto.
Qed.

Definition ghost_hist (sh : share) (h : hist_part) g :=
  @own _ _ _ _ _ _ (@ref_PCM map_PCM) g (Some (sh, h), None) NoneP.

Lemma ghost_hist_join : forall sh1 sh2 sh h1 h2 p (Hsh : sepalg.join sh1 sh2 sh)
  (Hsh1 : sh1 <> Share.bot) (Hsh2 : sh2 <> Share.bot),
  ghost_hist sh1 h1 p * ghost_hist sh2 h2 p = !!(compatible h1 h2) && ghost_hist sh (map_add h1 h2) p.
Proof.
  intros; unfold ghost_hist.
  erewrite own_op_gen.
  apply pred_ext; Intros; apply andp_right, derives_refl; apply prop_right.
  - destruct H as (? & [] & ?); simpl in *.
    destruct (fst x) as [[]|]; [|contradiction].
    rewrite map_join_spec in H; tauto.
  - eexists (Some (sh, map_add h1 h2), None); split; [split|]; simpl.
    + rewrite map_join_spec; auto.
    + constructor.
    + split; auto.
      intro; subst.
      apply join_Bot in Hsh as []; auto.
  - intros (? & [] & ?); simpl in *.
    destruct (fst x) as [[]|]; [|contradiction].
    split; [simpl | constructor].
    rewrite map_join_spec in *; tauto.
Qed.

Definition hist_incl (h : hist_part) l := forall t e, h t = Some e -> nth_error l t = Some e.

Definition hist_list (h : hist_part) l := forall t e, h t = Some e <-> nth_error l t = Some e.

Lemma hist_list_inj : forall h l1 l2 (Hl1 : hist_list h l1) (Hl2 : hist_list h l2), l1 = l2.
Proof.
  unfold hist_list; intros; apply list_nth_error_eq.
  intro j; specialize (Hl1 j); specialize (Hl2 j).
  destruct (nth_error l1 j).
  - symmetry; rewrite <- Hl2, Hl1; auto.
  - destruct (nth_error l2 j); auto.
    specialize (Hl2 h0); rewrite Hl1 in Hl2; tauto.
Qed.

Lemma hist_list_nil_inv1 : forall l, hist_list empty_map l -> l = [].
Proof.
  unfold hist_list; intros.
  destruct l; auto.
  specialize (H O h); destruct H as [_ H]; specialize (H eq_refl); discriminate.
Qed.

Lemma hist_list_nil_inv2 : forall h, hist_list h [] -> h = empty_map.
Proof.
  unfold hist_list; intros.
  extensionality t.
  specialize (H t); destruct (h t); auto.
  destruct (H h0) as [H' _].
  specialize (H' eq_refl); rewrite nth_error_nil in H'; discriminate.
Qed.

Definition ghost_ref l g := EX hr : hist_part, !!(hist_list hr l) &&
  @own _ _ _ _ _ _ (@ref_PCM map_PCM) g (None, Some hr) NoneP.

Lemma hist_next : forall h l (Hlist : hist_list h l), h (length l) = None.
Proof.
  intros.
  specialize (Hlist (length l)).
  destruct (h (length l)); auto.
  destruct (Hlist h0) as [H' _].
  pose proof (nth_error_Some l (length l)) as (Hlt & _).
  lapply Hlt; [omega|].
  rewrite H' by auto; discriminate.
Qed.

Definition ghost_hist_ref sh (h r : hist_part) g :=
  @own _ _ _ _ _ _ (@ref_PCM map_PCM) g (Some (sh, h), Some r) NoneP.

Lemma hist_add : forall (sh : share) (h h' : hist_part) e p t' (Hfresh : h' t' = None),
  ghost_hist_ref sh h h' p |-- |==> ghost_hist_ref sh (map_upd h t' e) (map_upd h' t' e) p.
Proof.
  intros; apply own_update.
  intros (c1, c2) ((d1, d2) & [Hjoin1 Hjoin2] & [? Hcompat]); simpl in *.
  destruct d2 as [d2|]; [|inv Hjoin2].
    assert (d2 = h'); subst.
    { inv Hjoin2; auto.
      inv H3; auto. }
  destruct d1 as [(?, ?)|]; [|destruct c1 as [[]|]; contradiction].
  rewrite completable_alt in Hcompat.
  pose proof (hist_sub_upd _ _ _ t' e Hcompat).
  assert (psepalg.Join_lower (psepalg.Join_discrete hist_part) (Some (map_upd h' t' e)) c2
    (Some (map_upd h' t' e))).
  { inv Hjoin2; constructor.
    inv H4; auto. }
  destruct c1 as [(shc, hc)|].
  - destruct Hjoin1 as (? & ? & ? & Hj).
    rewrite map_join_spec in Hj.
    exists (Some (s, map_upd (map_add h hc) t' e), Some (map_upd h' t' e)).
    destruct Hj; subst.
    split; split; auto; simpl; rewrite ?completable_alt; auto.
    split; auto; split; auto; split; auto.
    rewrite map_join_spec.
    split; [apply compatible_upd | apply map_add_upd]; auto.
    destruct Hcompat.
    assert (map_incl hc h') as Hincl.
    { pose proof (map_incl_add hc h) as Hincl.
      rewrite map_add_comm in Hincl by (symmetry; auto).
      fold share in *; destruct (eq_dec s Tsh); subst; auto.
      etransitivity; eauto. }
    specialize (Hincl t').
    destruct (hc t'); auto.
    erewrite Hincl in Hfresh by eauto; discriminate.
  - inv Hjoin1.
    exists (Some (sh, map_upd h t' e), Some (map_upd h' t' e)); split; split; simpl; auto.
    rewrite completable_alt; auto.
Qed.

Lemma hist_incl_nil : forall h, hist_incl empty_map h.
Proof.
  repeat intro; discriminate.
Qed.

Lemma hist_list_nil : hist_list empty_map [].
Proof.
  split; [discriminate|].
  rewrite nth_error_nil; discriminate.
Qed.

Lemma hist_list_snoc : forall h l e, hist_list h l ->
  hist_list (map_upd h (length l) e) (l ++ [e]).
Proof.
  unfold hist_list, map_upd; split.
  - if_tac.
    + intro X; inv X.
      rewrite nth_error_app2, minus_diag; auto.
    + rewrite H.
      intro X; rewrite nth_error_app1; auto.
      rewrite <- nth_error_Some, X; discriminate.
  - if_tac.
    + subst; rewrite nth_error_app2, minus_diag; auto.
    + intro X; apply H; rewrite nth_error_app1 in X; auto.
      assert (t < length (l ++ [e]))%nat; [|rewrite app_length in *; simpl in *; omega].
      rewrite <- nth_error_Some, X; discriminate.
Qed.

Lemma hist_sub_list_incl : forall sh h h' l (Hsub : hist_sub sh h h') (Hlist : hist_list h' l),
  hist_incl h l.
Proof.
  unfold hist_list, hist_incl; intros.
  apply Hlist.
  destruct Hsub.
  destruct (eq_dec sh Tsh); subst; auto.
Qed.

Lemma hist_sub_Tsh : forall h h', hist_sub Tsh h h' <-> (h = h').
Proof.
  intros; unfold hist_sub; rewrite eq_dec_refl; repeat split; auto; tauto.
Qed.

Lemma hist_ref_join : forall sh h l p, sh <> Share.bot ->
  ghost_hist sh h p * ghost_ref l p =
  EX h' : hist_part, !!(hist_list h' l /\ hist_sub sh h h') && ghost_hist_ref sh h h' p.
Proof.
  unfold ghost_hist, ghost_ref; intros; apply pred_ext.
  - Intros hr; Exists hr.
    erewrite own_op_gen.
    + Intros; apply andp_right, derives_refl; apply prop_right.
      split; auto.
      destruct H1 as ([g] & [H1 H2] & [? Hcompat]); simpl in *.
      destruct g as [[]|]; [|contradiction].
      inv H1; inv H2.
      apply completable_alt; auto.
    + split; simpl; auto; constructor.
  - Intros h'; Exists h'; entailer!.
    erewrite <- own_op; [apply derives_refl|].
    split; simpl; auto; constructor.
Qed.

Corollary hist_ref_join_nil : forall sh p, sh <> Share.bot ->
  ghost_hist sh empty_map p * ghost_ref [] p = ghost_hist_ref sh empty_map empty_map p.
Proof.
  intros; rewrite hist_ref_join by auto.
  apply pred_ext; entailer!.
  - apply hist_list_nil_inv2 in H0; subst; auto.
  - Exists (fun _ : nat => @None hist_el); apply andp_right, derives_refl.
    apply prop_right; split; [apply hist_list_nil|].
    split; auto.
    if_tac; auto.
Qed.

Lemma hist_ref_incl : forall sh h h' p, sh <> Share.bot ->
  ghost_hist sh h p * ghost_ref h' p |-- !!hist_incl h h'.
Proof.
  intros; rewrite hist_ref_join by auto.
  Intros l; eapply prop_right, hist_sub_list_incl; eauto.
Qed.

Lemma hist_add' : forall sh h h' e p, sh <> Share.bot ->
  ghost_hist sh h p * ghost_ref h' p |-- |==>
  ghost_hist sh (map_upd h (length h') e) p * ghost_ref (h' ++ [e]) p.
Proof.
  intros; rewrite !hist_ref_join by auto.
  Intros hr.
  eapply derives_trans; [apply hist_add|].
  { apply hist_next; eauto. }
  apply bupd_mono.
  Exists (map_upd hr (length h') e); apply andp_right, derives_refl.
  apply prop_right; split; [apply hist_list_snoc | apply hist_sub_upd]; auto.
Qed.

Definition newer (l : hist_part) t := forall t', l t' <> None -> (t' < t)%nat.

Lemma newer_trans : forall l t1 t2, newer l t1 -> (t1 <= t2)%nat -> newer l t2.
Proof.
  repeat intro.
  specialize (H _ H1); omega.
Qed.

Corollary newer_upd : forall l t1 e t2, newer l t1 -> (t1 < t2)%nat ->
  newer (map_upd l t1 e) t2.
Proof.
  unfold newer, map_upd; intros.
  destruct (eq_dec t' t1); [omega|].
  eapply newer_trans; eauto; omega.
Qed.

Lemma newer_over : forall h t t', newer h t -> (t <= t')%nat -> h t' = None.
Proof.
  intros.
  specialize (H t').
  destruct (h t'); auto.
  lapply H; [omega | discriminate].
Qed.

Corollary newer_out : forall h t, newer h t -> h t = None.
Proof.
  intros; eapply newer_over; eauto.
Qed.

Lemma hist_incl_lt : forall h l, hist_incl h l -> newer h (length l).
Proof.
  unfold hist_incl; repeat intro.
  specialize (H t').
  destruct (h t'); [|contradiction].
  specialize (H _ eq_refl).
  rewrite <- nth_error_Some, H; discriminate.
Qed.

Corollary hist_list_lt : forall h l, hist_list h l -> newer h (length l).
Proof.
  intros; apply hist_incl_lt; repeat intro; apply H; auto.
Qed.

(* We want to be able to remove irrelevant operations from a history, leading to a slightly weaker
   correspondence between history and list of operations. *)
Inductive hist_list' : hist_part -> list hist_el -> Prop :=
| hist_list'_nil : hist_list' empty_map []
| hist_list'_snoc : forall h l t e (He : h t = None) (Hlast : newer h t) (Hrest : hist_list' h l),
    hist_list' (map_upd h t e) (l ++ [e]).
Hint Resolve hist_list'_nil.

Lemma hist_list'_in : forall h l (Hl : hist_list' h l) e, (exists t, h t = Some e) <-> In e l.
Proof.
  induction 1.
  - split; [intros (? & ?); discriminate | contradiction].
  - intro; subst; split.
    + unfold map_upd; intros (? & Hin); rewrite in_app in *.
      destruct (eq_dec x t); [inv Hin; simpl; auto|].
      rewrite <- IHHl; eauto.
    + rewrite in_app; intros [Hin | [Heq | ?]]; [| inv Heq | contradiction].
      * rewrite <- IHHl in Hin; destruct Hin as (? & ?).
        unfold map_upd; exists x; if_tac; auto; congruence.
      * unfold map_upd; eexists; apply eq_dec_refl.
Qed.

Lemma hist_list_weak : forall l h (Hl : hist_list h l), hist_list' h l.
Proof.
  induction l using rev_ind; intros.
  - apply hist_list_nil_inv2 in Hl; subst; auto.
  - destruct (Hl (length l) x) as (_ & H); exploit H.
    { rewrite nth_error_app2, minus_diag by omega; auto. }
    intro Hx.
    set (h0 := fun k => if eq_dec k (length l) then None else h k).
    replace h with (map_upd h0 (length l) x).
    constructor.
    + subst h0; apply eq_dec_refl.
    + pose proof (hist_list_lt _ _ Hl) as Hn.
      intro t; specialize (Hn t).
      subst h0; simpl; if_tac; [contradiction|].
      intro X; specialize (Hn X); rewrite app_length in Hn; simpl in Hn; omega.
    + apply IHl.
      intros t e; specialize (Hl t e).
      subst h0; simpl; if_tac.
      * split; [discriminate|].
        intro X; assert (t < length l)%nat by (rewrite <- nth_error_Some, X; discriminate); omega.
      * rewrite Hl; destruct (lt_dec t (length l)).
        { rewrite nth_error_app1 by auto; reflexivity. }
        split; intro X.
        -- assert (t < length (l ++ [x]))%nat by (rewrite <- nth_error_Some, X; discriminate);
             rewrite app_length in *; simpl in *; omega.
        -- assert (t < length l)%nat by (rewrite <- nth_error_Some, X; discriminate); contradiction.
    + unfold map_upd; subst h0; simpl.
      extensionality k'; if_tac; subst; auto.
Qed.

Lemma ghost_hist_init : @valid (@ref_PCM (@map_PCM nat hist_el)) (Some (Tsh, empty_map), Some empty_map).
Proof.
  split; simpl; auto.
  rewrite completable_alt; split; auto.
  rewrite eq_dec_refl; auto.
Qed.

Inductive add_events h : list hist_el -> hist_part -> Prop :=
| add_events_nil : add_events h [] h
| add_events_snoc : forall le h' t e (Hh' : add_events h le h') (Ht : newer h' t),
    add_events h (le ++ [e]) (map_upd h' t e).
Hint Resolve add_events_nil.

Lemma add_events_1 : forall h t e (Ht : newer h t), add_events h [e] (map_upd h t e).
Proof.
  intros; apply (add_events_snoc _ []); auto.
Qed.

Lemma add_events_trans : forall h le h' le' h'' (H1 : add_events h le h') (H2 : add_events h' le' h''),
  add_events h (le ++ le') h''.
Proof.
  induction 2.
  - rewrite app_nil_r; auto.
  - rewrite app_assoc; constructor; auto.
Qed.

Lemma add_events_add : forall h le h', add_events h le h' ->
  exists h2, h' = map_add h h2 /\ forall t e, h2 t = Some e -> newer h t /\ In e le.
Proof.
  induction 1.
  - eexists; rewrite map_add_empty; split; auto; discriminate.
  - destruct IHadd_events as (h2 & ? & Hh2); subst.
    assert (compatible h h2).
    { repeat intro.
      destruct (Hh2 _ _ H1) as [Hk _].
      specialize (Hk k); lapply Hk; [omega | congruence]. }
    assert (newer h t).
    { repeat intro; apply Ht.
      unfold map_add.
      destruct (h t'); auto. }
    rewrite map_add_comm, map_add_upd, map_add_comm; auto.
    eexists; split; eauto; intros.
    unfold map_upd in *.
    rewrite in_app; simpl.
    destruct (eq_dec t0 t); [inv H2; auto|].
    destruct (Hh2 _ _ H2); auto.
    { apply compatible_upd; [symmetry; auto|].
      specialize (H1 t).
      destruct (h t); auto.
      lapply H1; [omega | discriminate]. }
Qed.

Corollary add_events_dom : forall h le h' t e, add_events h le h' -> h' t = Some e ->
  h t = Some e \/ In e le.
Proof.
  intros; apply add_events_add in H as (? & ? & Hh2); subst.
  unfold map_add in H0.
  destruct (h t); [inv H0; auto|].
  destruct (Hh2 _ _ H0); auto.
Qed.

Corollary add_events_incl : forall h le h', add_events h le h' -> map_incl h h'.
Proof.
  intros; apply add_events_add in H as (? & ? & ?); subst.
  apply map_incl_add.
Qed.

Corollary add_events_newer : forall h le h' t, add_events h le h' -> newer h' t -> newer h t.
Proof.
  repeat intro.
  apply H0.
  destruct (h t') eqn: Ht'; [|contradiction].
  eapply add_events_incl in Ht' as ->; eauto.
Qed.

Lemma add_events_in : forall h le h' e, add_events h le h' -> In e le ->
  exists t, newer h t /\ h' t = Some e.
Proof.
  induction 1; [contradiction|].
  rewrite in_app; intros [? | [? | ?]]; try contradiction.
  - destruct IHadd_events as (? & ? & ?); auto.
    do 2 eexists; eauto.
    unfold map_upd; if_tac; auto; subst.
    specialize (Ht t); rewrite H2 in Ht; lapply Ht; [omega | discriminate].
  - subst; unfold map_upd; do 2 eexists; [|apply eq_dec_refl].
    eapply add_events_newer; eauto.
Qed.

End GHist.

Hint Resolve hist_incl_nil hist_list_nil hist_list'_nil add_events_nil.
Hint Resolve ghost_var_exclusive ex_ghost_var_exclusive.
Hint Resolve (*ghost_var_init*) master_init (*ghost_map_init*) ghost_hist_init : init.

Ltac ghost_alloc G :=
  match goal with |-semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    apply (semax_pre_bupd (PROPx P (LOCALx Q (SEPx ((EX g : _, G g) :: R)))));
  [go_lower; rewrite !prop_true_andp by (repeat (split; auto));
   rewrite <- emp_sepcon at 1; eapply derives_trans, bupd_frame_r;
   apply sepcon_derives, derives_refl; apply own_alloc; auto; simpl; auto|] end.

(* weak view shift for use in funspecs *)
Program Definition weak_view_shift (P Q: mpred): mpred :=
  fun w => predicates_hered.derives (approx (S (level w)) P) (own.bupd (approx (S (level w)) Q)).
Next Obligation.
  repeat intro.
  destruct H1.
  apply age_level in H.
  lapply (H0 a0); [|split; auto; omega].
  intro HQ; destruct (HQ _ H2) as (? & ? & ? & ? & ? & ? & []).
  eexists; split; eauto; eexists; split; eauto; repeat split; auto; omega.
Defined.

Lemma view_shift_nonexpansive: forall P Q n,
  approx n (weak_view_shift P Q) = approx n (weak_view_shift (approx n P) (approx n Q)).
Proof.
  apply nonexpansive2_super_non_expansive; repeat intro.
  - split; intros ??%necR_level Hshift ? HP ? J;
      destruct (Hshift _ HP _ J) as (? & ? & m' & ? & ? & ? & []); destruct HP;
      eexists; split; eauto; eexists; split; eauto; repeat split; auto;
      apply (H m'); auto; omega.
  - split; intros ??%necR_level Hshift ? []; apply Hshift; split; auto; apply (H a0); auto; omega.
Qed.

Lemma view_shift_weak: forall P Q, P |-- |==> Q -> TT |-- weak_view_shift P Q.
Proof.
  intros.
  change (predicates_hered.derives TT (weak_view_shift P Q)).
  intros w _ ? [? HP] ? J.
  destruct (H _ HP _ J) as (? & ? & ? & ? & ? & ? & ?).
  eexists; split; eauto; eexists; split; eauto; repeat split; auto; omega.
Qed.

Lemma apply_view_shift: forall P Q, (weak_view_shift P Q && emp) * P |-- |==> Q.
Proof.
  intros.
  change (predicates_hered.derives ((weak_view_shift P Q && emp) * P) (own.bupd Q)).
  intros ? (? & ? & ? & [Hshift Hemp] & HP) ? J.
  destruct (join_level _ _ _ H).
  apply Hemp in H; subst.
  lapply (Hshift a); [|split; auto; omega].
  intro X; destruct (X _ J) as (? & ? & ? & ? & ? & ? & []); eauto 7.
Qed.
