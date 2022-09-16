Require Export VST.msl.ghost.
Require Import VST.msl.shares.
Require Import VST.msl.sepalg_generators.
Require Import VST.msl.iter_sepcon.
Require Import VST.msl.ghost_seplog.
Require Import VST.veric.mpred.
Require Import VST.veric.shares.
Require Import VST.veric.own.
Require Import VST.veric.compcert_rmaps.

(* Lemmas about ghost state and common instances *)

Notation "|==> P" := (own.bupd P) (at level 99, P at level 200): pred.

Section ghost.

Local Open Scope pred.

Context {RA: Ghost}.

Lemma own_op' : forall g a1 a2 pp,
  own g a1 pp * own g a2 pp = EX a3 : _, !!(join a1 a2 a3 /\ valid a3) && own g a3 pp.
Proof.
  intros.
  apply pred_ext.
  - eapply derives_trans, prop_andp_left; [apply andp_right, derives_refl; apply ghost_valid_2|].
    intros (a3 & ? & ?); apply exp_right with a3, prop_andp_right; auto.
    erewrite <- ghost_op by eauto; apply derives_refl.
  - apply exp_left; intro; apply prop_andp_left; intros [].
    erewrite ghost_op by eauto; apply derives_refl.
Qed.

Lemma own_op_gen : forall g a1 a2 a3 pp, (valid_2 a1 a2 -> join a1 a2 a3) ->
  own g a1 pp * own g a2 pp = !!(valid_2 a1 a2) && own g a3 pp.
Proof.
  intros; apply pred_ext.
  - eapply derives_trans, prop_andp_left; [apply andp_right, derives_refl; apply ghost_valid_2|].
    intro; erewrite <- ghost_op by eauto.
    apply prop_andp_right; auto.
  - apply prop_andp_left; intro.
    erewrite ghost_op by eauto; apply derives_refl.
Qed.

End ghost.

#[export] Hint Resolve Share.nontrivial : share.

Section Reference.
(* One common kind of PCM is one in which a central authority has a reference copy, and clients pass around
   partial knowledge. When a client recovers all pieces, it can gain full knowledge. *)
(* This is related to the snapshot PCM, but the snapshots aren't duplicable. *)

Global Program Instance pos_PCM (P : Ghost) : Ghost := { G := option (share * G);
  valid a := match a with Some (sh, _) => sh <> Share.bot | _ => True end;
  Join_G a b c := match a, b, c with
  | Some (sha, a'), Some (shb, b'), Some (shc, c') =>
      sha <> Share.bot /\ shb <> Share.bot /\ sepalg.join sha shb shc /\ join a' b' c'
  | Some (sh, a), None, Some c' | None, Some (sh, a), Some c' => c' = (sh, a)
  | None, None, None => True
  | _, _, _ => False
  end }.
Next Obligation.
repeat split; intros; intro X; decompose [and] X; congruence.
Qed.
Next Obligation.
repeat split; intros; intro X; decompose [and] X; congruence.
Qed.
Next Obligation.
repeat split; intros; intro X; decompose [and] X; congruence.
Qed.
Next Obligation.
repeat split; intros; intro X; decompose [and] X; congruence.
Qed.
Next Obligation.
apply fsep_sep.
exists (fun _ => None); auto.
intros [[]|]; constructor.
Defined.
Next Obligation.
constructor.
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
  - intros [[]|] [[]|] [[]|] [[]|]; try contradiction; intros H1 H2; try solve [inv H1; reflexivity || inv H2; reflexivity].
    destruct H1 as (? & ? & ? & ?), H2 as (? & ? & ? & ?); f_equal; f_equal; eapply join_positivity; eauto.
Qed.
(*Next Obligation.
  hnf.
  destruct a as [[]|]; auto.
Qed.
Next Obligation.
  exists None; hnf; auto.
Qed.*)
Next Obligation.
destruct a as [[]|]; destruct b as [[]|]; destruct c as [[]|]; try trivial;
unfold join in *; try contradiction.
- decompose [and] H; assumption.
- congruence.
Qed.

Definition completable {P : Ghost} (a: @G (pos_PCM P)) r := exists x, join a x (Some (Share.top, r)).

Local Obligation Tactic := idtac.

Global Program Instance ref_PCM (P : Ghost) : Ghost :=
{ valid a := valid (fst a) /\ match snd a with Some r => completable (fst a) r | None => True end;
  Join_G a b c := @Join_G (pos_PCM P) (fst a) (fst b) (fst c) /\
    @psepalg.Join_lower _ (psepalg.Join_discrete _) (snd a) (snd b) (snd c) }.
Next Obligation.
  intros P; apply sepalg_generators.Sep_prod; try apply _.
  apply fsep_sep, _.
Defined.
Next Obligation.
  intros P; apply sepalg_generators.Perm_prod; typeclasses eauto.
Qed.
(*Next Obligation.
  intros; hnf.
  split; [apply (@core2_unit (pos_PCM P)) | constructor].
Qed.
Next Obligation.
  intros; reflexivity.
Qed.
Next Obligation.
  intros; exists (None, None); hnf.
  split; constructor.
Qed.*)
Next Obligation.
  intros P ??? [? J] []; split; [eapply join_valid; eauto|].
  destruct a, b, c; simpl in *; inv J; auto.
  + destruct o1; auto.
    destruct H1.
    destruct (join_assoc H H1) as (? & ? & ?); eexists; eauto.
  + inv H2.
Qed.

End Reference.

#[global] Program Instance exclusive_PCM A : Ghost :=
  { valid a := True; Join_G := Join_lower (Join_discrete A) }.
(*Next Obligation.
Proof.
  eexists; constructor.
Qed.*)

Definition excl {A} g a : mpred := own(RA := exclusive_PCM A) g (Some a) NoneP.

Lemma exclusive_update : forall {A} (v v' : A) p, excl p v |-- |==> excl p v'.
Proof.
  intros; apply ghost_update.
  intros ? (? & ? & _).
  exists (Some v'); split; simpl; auto; inv H; constructor.
  inv H1.
Qed.

Local Obligation Tactic := idtac.

#[global] Program Instance prod_PCM (GA GB: Ghost): Ghost := { G := @G GA * @G GB;
  valid a := valid (fst a) /\ valid (snd a); Join_G := Join_prod _ _ _ _ }.
Next Obligation.
  intros GA GB ??? [] []; split; eapply join_valid; eauto.
Defined.

(* Can we use Santiago and Qinxiang's paper to simplify this? *)
Class PCM_order `{P : Ghost} (ord : G -> G -> Prop) := { ord_preorder :> PreOrder ord;
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

Global Program Instance snap_PCM : Ghost :=
  { valid _ := True; Join_G a b c := sepalg.join (fst a) (fst b) (fst c) /\
      if eq_dec (fst a) Share.bot then if eq_dec (fst b) Share.bot then join (snd a) (snd b) (snd c)
        else ord (snd a) (snd b) /\ snd c = snd b else snd c = snd a /\
          if eq_dec (fst b) Share.bot then ord (snd b) (snd a) else snd c = snd b }.
Next Obligation.
  exists (fun '(sh, a) => (Share.bot, a)); repeat intro.
  + destruct t; constructor; auto; simpl.
    rewrite eq_dec_refl.
    if_tac; [apply join_refl | split; auto].
    reflexivity.
  + destruct a, c, H as [? Hj].
    assert (join_sub g g0) as [].
    { if_tac in Hj. if_tac in Hj.
      eexists; eauto.
      destruct Hj; simpl in *; subst.
      apply join_ord_eq; auto.
      destruct Hj; simpl in *; subst.
      apply join_sub_refl. }
    eexists (_, _). split; simpl.
    * apply join_bot_eq.
    * rewrite !eq_dec_refl; eauto.
  + destruct a; reflexivity.
Defined.
Next Obligation.
  constructor.
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
      rewrite Hd in Hsh1, Hsh2, Hjoin2.
      assert (sh' = fst c) as Hc.
      { eapply sepalg.join_eq; eauto.
        rewrite e0; apply bot_join_eq. }
      subst sh'.
      destruct (eq_dec (fst c) Share.bot) eqn: Hc1.
      * destruct (eq_dec (fst a) Share.bot) eqn: Ha.
        -- destruct (join_assoc Hjoin1 Hjoin2) as [c' []].
            destruct a, b, c; simpl in *; subst.
           exists (Share.bot, c'); split; split; rewrite ?eq_dec_refl; auto.
        -- destruct Hjoin1 as [Hc' ?]; rewrite Hc' in Hjoin2.
           destruct Hjoin2, (ord_lub (snd b) (snd c) (snd a)) as [c' []]; eauto.
           destruct b, c; simpl in *; subst.
           exists (Share.bot, c'); split; split; rewrite ?eq_dec_refl, ?Ha; auto.
      * exists c.
        destruct (eq_dec (fst a) Share.bot) eqn: Ha; try solve [split; split; auto].
        -- destruct Hjoin2.
           apply join_ord in Hjoin1; destruct Hjoin1.
           destruct b; simpl in *; subst.
           split; split; rewrite ?Ha, ?Hc1, ?eq_dec_refl; auto; split; auto; etransitivity; eauto.
        -- destruct Hjoin2 as [He1 He2].
           destruct Hjoin1 as [Hd' ?]; rewrite He2, Hd' in He1; split; split; rewrite ?e0, ?He2, ?He1, ?Ha, ?Hc1, ?eq_dec_refl, ?Hd'; auto.
    + exists (sh', snd b); simpl.
      destruct (eq_dec (fst d) Share.bot).
      { rewrite e0 in Hsh1; apply join_Bot in Hsh1; destruct Hsh1; contradiction. }
      destruct (eq_dec sh' Share.bot) eqn: Hn'.
      { subst; apply join_Bot in H; destruct H; contradiction. }
      assert (snd d = snd b) as Hd by (destruct (eq_dec (fst a) Share.bot); tauto).
      rewrite Hd in Hjoin1, Hjoin2; destruct Hjoin2 as [He Hjoin2]; rewrite He in Hjoin2; split; split; simpl; rewrite ?Hb, ?Hn', ?Hd, ?He; auto.
  - intros ??? []; split; [apply join_comm; auto|].
    if_tac; if_tac; auto; tauto.
  - intros ???? [? Hjoin1] [? Hjoin2].
    assert (fst a = fst b) by (eapply join_positivity; eauto).
    destruct (eq_dec (fst a) Share.bot), a, a', b, b'; simpl in *; subst; f_equal.
    + rewrite eq_dec_refl in Hjoin2.
      apply join_Bot in H0 as []; subst.
      apply join_Bot in H as []; subst.
      rewrite !eq_dec_refl in Hjoin1, Hjoin2.
      eapply join_positivity; eauto.
    + destruct Hjoin1; auto.
Defined.
Next Obligation.
  auto.
Defined.

Definition ghost_snap (a : @G P) p := own p (Share.bot, a) NoneP.

Lemma ghost_snap_join : forall v1 v2 p v, join v1 v2 v ->
  (ghost_snap v1 p * ghost_snap v2 p = ghost_snap v p)%pred.
Proof.
  intros; symmetry; apply ghost_op.
  split; simpl; rewrite ?eq_dec_refl; auto.
Qed.

Lemma prop_derives : forall (P Q : Prop), (P -> Q) -> !!P |-- !!Q.
Proof.
  repeat intro; simpl in *; auto.
Qed.

Lemma ghost_snap_conflict : forall v1 v2 p, ghost_snap v1 p * ghost_snap v2 p |-- !!(joins v1 v2).
Proof.
  intros; eapply derives_trans; [apply ghost_valid_2|].
  apply prop_derives.
  intros ((?, a) & (? & Hj) & _); simpl in Hj.
  rewrite !eq_dec_refl in Hj.
  exists a; auto.
Qed.

Lemma ghost_snap_join' : forall v1 v2 p,
  (ghost_snap v1 p * ghost_snap v2 p = EX v : _, !!(join v1 v2 v) && ghost_snap v p)%pred.
Proof.
  intros; apply pred_ext.
  - eapply derives_trans, prop_andp_left; [apply andp_right, derives_refl; apply ghost_snap_conflict|].
    intros [v]; apply exp_right with v; apply prop_andp_right; auto.
    erewrite ghost_snap_join; eauto.
  - apply exp_left; intro v; apply prop_andp_left; intro.
    erewrite ghost_snap_join; eauto.
Qed.

Definition ghost_master sh (a : @G P) p := own p (sh, a) NoneP.

Lemma snap_master_join : forall v1 sh v2 p, sh <> Share.bot ->
  (ghost_snap v1 p * ghost_master sh v2 p = !!(ord v1 v2) && ghost_master sh v2 p)%pred.
Proof.
  intros; setoid_rewrite own_op'.
  apply pred_ext.
  - apply exp_left; intro a3; apply prop_andp_left.
    destruct a3 as (sh', ?); intros ([Hsh Hj] & _); simpl in *.
    apply bot_identity in Hsh; subst sh'.
    rewrite eq_dec_refl in Hj.
    destruct (eq_dec sh Share.bot); [contradiction|].
    destruct Hj; subst; apply prop_andp_right; auto.
  - apply prop_andp_left; intro.
    apply exp_right with (sh, v2), prop_andp_right; auto.
    split; simpl; auto.
    split; simpl; rewrite ?eq_dec_refl.
    + apply bot_join_eq.
    + if_tac; auto; contradiction.
Qed.

Corollary snaps_master_join : forall lv sh v2 p, sh <> Share.bot ->
  (fold_right sepcon emp (map (fun v => ghost_snap v p) lv) * ghost_master sh v2 p =
  !!(Forall (fun v1 => ord v1 v2) lv) && ghost_master sh v2 p)%pred.
Proof.
  induction lv; simpl; intros.
  - rewrite emp_sepcon, prop_true_andp; auto.
  - rewrite sepcon_comm, <-sepcon_assoc, (sepcon_comm (ghost_master _ _ _)), snap_master_join; auto.
    apply pred_ext.
    + rewrite sepcon_andp_prop1; apply prop_andp_left; intro.
      rewrite sepcon_comm, IHlv by auto.
      apply prop_andp_left; intro; apply prop_andp_right; auto.
    + apply prop_andp_left; intros Hall.
      inv Hall.
      rewrite prop_true_andp; auto.
      rewrite sepcon_comm, IHlv by auto.
      apply prop_andp_right; auto.
Qed.

Lemma master_update : forall v v' p, ord v v' -> ghost_master Tsh v p |-- |==> ghost_master Tsh v' p.
Proof.
  intros; apply ghost_update.
  intros ? (x & Hj & _); simpl in Hj.
  exists (Tsh, v'); simpl; split; auto.
  destruct Hj as [Hsh Hj]; simpl in *.
  apply join_Tsh in Hsh as []; destruct c, x; simpl in *; subst.
  split; auto; simpl.
  fold share in *; destruct (eq_dec Tsh Share.bot); [contradiction Share.nontrivial|].
  destruct Hj as [? Hc']; subst.
  rewrite !eq_dec_refl in Hc' |- *; split; auto.
  etransitivity; eauto.
Qed.

Lemma master_init : forall (a : @G P), exists g', joins (Tsh, a) g'.
Proof.
  intros; exists (Share.bot, a), (Tsh, a); simpl.
  split; auto; simpl.
  apply join_refl.
Qed.

Hint Resolve bupd_intro : ghost.

Lemma make_snap : forall (sh : share) v p, ghost_master sh v p |-- |==> ghost_snap v p * ghost_master sh v p.
Proof.
  intros.
  destruct (eq_dec sh Share.bot).
  - subst; setoid_rewrite ghost_snap_join; [|apply join_refl]; auto with ghost.
  - rewrite snap_master_join by auto.
    rewrite prop_true_andp by reflexivity; apply bupd_intro.
Qed.

Lemma ghost_snap_forget : forall v1 v2 p, ord v1 v2 -> ghost_snap v2 p |-- |==> ghost_snap v1 p.
Proof.
  intros; apply ghost_update.
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
  apply exp_left; intro v'; apply prop_andp_left; intros [H ?].
  destruct v', H as [Hsh Hj]; apply bot_identity in Hsh; simpl in *; subst.
  rewrite !eq_dec_refl in Hj.
  apply ghost_snap_forget.
  rewrite join_ord_eq; eauto.
Qed.

Lemma master_share_join : forall sh1 sh2 sh v p, sepalg.join sh1 sh2 sh ->
  (ghost_master sh1 v p * ghost_master sh2 v p = ghost_master sh v p)%pred.
Proof.
  intros; symmetry; apply ghost_op; split; auto; simpl.
  if_tac; if_tac; try split; auto; try reflexivity; apply join_refl.
Qed.

Lemma unreadable_bot : ~readable_share Share.bot.
Proof.
  unfold readable_share, nonempty_share, sepalg.nonidentity.
  rewrite Share.glb_bot; auto.
Qed.

Lemma master_inj : forall sh1 sh2 v1 v2 p, readable_share sh1 -> readable_share sh2 ->
  ghost_master sh1 v1 p * ghost_master sh2 v2 p |-- !!(v1 = v2).
Proof.
  intros.
  eapply derives_trans; [apply ghost_valid_2|].
  apply prop_derives; intros ((?, ?) & [[? Hj] _]); simpl in Hj.
  fold share in *.
  destruct (eq_dec sh1 Share.bot); [subst; contradiction unreadable_bot|].
  destruct (eq_dec sh2 Share.bot); [subst; contradiction unreadable_bot|].
  destruct Hj; subst; auto.
Qed.

Lemma master_share_join' : forall sh1 sh2 sh v1 v2 p, readable_share sh1 -> readable_share sh2 ->
  sepalg.join sh1 sh2 sh ->
  (ghost_master sh1 v1 p * ghost_master sh2 v2 p = !!(v1 = v2) && ghost_master sh v2 p)%pred.
Proof.
  intros; apply pred_ext.
  - eapply derives_trans; [apply andp_right, derives_refl; apply master_inj; auto|].
    apply prop_andp_left; intros; subst.
    apply prop_andp_right; auto.
    erewrite master_share_join; eauto.
  - apply prop_andp_left; intro; subst.
    erewrite master_share_join; eauto.
Qed.

(* useful when we only want to deal with full masters *)
Definition ghost_master1 a p := ghost_master Tsh a p.

Lemma snap_master_join1 : forall v1 v2 p,
  (ghost_snap v1 p * ghost_master1 v2 p = !!(ord v1 v2) && ghost_master1 v2 p)%pred.
Proof.
  intros; apply snap_master_join, Share.nontrivial.
Qed.

Lemma snap_master_update1 : forall v1 v2 p v', ord v2 v' ->
  ghost_snap v1 p * ghost_master1 v2 p |-- |==> ghost_snap v' p * ghost_master1 v' p.
Proof.
  intros; rewrite !snap_master_join1.
  apply prop_andp_left; intro.
  rewrite prop_true_andp by reflexivity.
  apply master_update; auto.
Qed.

End Snapshot.

#[global] Hint Resolve bupd_intro : ghost.

Section Discrete.

#[global] Program Instance discrete_PCM (A : Type) : Ghost := { valid a := True;
  Join_G := Join_equiv A }.
Next Obligation.
  auto.
Defined.

Context {A : Type}.

Global Instance discrete_order : PCM_order(P := discrete_PCM A) eq.
Proof.
  constructor; intros.
  - typeclasses eauto.
  - exists c; subst; split; hnf; auto.
  - inv H; auto.
  - subst; hnf; auto.
Defined.

End Discrete.
