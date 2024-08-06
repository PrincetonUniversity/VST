Require Export VST.msl.ghost.
Require Export VST.veric.ghosts.
Require Import VST.veric.compcert_rmaps.
Require Import VST.concurrency.conclib.
Import List.

(* Lemmas about ghost state and common instances, part 2 *)

#[export] Hint Resolve Share.nontrivial : core.

Opaque eq_dec.

Definition gname := own.gname.

#[export] Instance Inhabitant_preds : Inhabitant preds := NoneP.

Section ghost.

Context {RA: Ghost}.

Lemma own_op' : forall g a1 a2 pp,
  own g a1 pp * own g a2 pp = EX a3 : _, !!(join a1 a2 a3 /\ valid a3) && own g a3 pp.
Proof.
  exact own_op'.
Qed.

Lemma own_op_gen : forall g a1 a2 a3 pp, (valid_2 a1 a2 -> join a1 a2 a3) ->
  own g a1 pp * own g a2 pp = !!(valid_2 a1 a2) && own g a3 pp.
Proof.
  exact own_op_gen.
Qed.

Lemma own_alloc : forall (a : G) (pp : preds), valid a -> emp |-- |==> EX g : own.gname, own g a pp.
Proof.
  exact own_alloc.
Qed.

Lemma own_dealloc : forall g (a : G) (pp : preds), own g a pp |-- emp.
Proof.
  exact own_dealloc.
Qed.

Lemma own_update : forall g a b pp, fp_update a b -> own g a pp |-- |==> own g b pp.
Proof.
  exact own_update.
Qed.

Lemma own_update_ND : forall g a B pp, fp_update_ND a B -> own g a pp |-- |==> EX b : G, !! B b && own g b pp.
Proof.
  exact own_update_ND.
Qed.

Lemma own_list_alloc : forall la lp, Forall valid la -> length lp = length la ->
  emp |-- |==> (EX lg : _, !!(Zlength lg = Zlength la) &&
    iter_sepcon (fun '(g, a, p) => own g a p) (combine (combine lg la) lp)).
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
    Exists (g :: lg); rewrite !Zlength_cons; simpl.
    rewrite sepcon_comm; entailer!.
    apply derives_refl.
Qed.

Corollary own_list_alloc' : forall a pp i, 0 <= i -> valid a ->
  emp |-- |==> (EX lg : _, !!(Zlength lg = i) && iter_sepcon (fun g => own g a pp) lg).
Proof.
  intros.
  eapply derives_trans;
    [apply own_list_alloc with (la := repeat a (Z.to_nat i))(lp := repeat pp (Z.to_nat i))|].
  { apply Forall_repeat; auto. }
  { rewrite !repeat_length; auto. }
  apply bupd_mono; Intros lg; Exists lg.
  rewrite coqlib4.Zlength_repeat, Z2Nat.id in H1 by lia.
  rewrite !combine_const1 by (rewrite ?Zlength_combine, ?coqlib4.Zlength_repeat, ?Z2Nat.id, ?Z.min_r; lia).
  entailer!.
  clear H; induction lg; simpl; entailer!.
Qed.

Lemma own_list_dealloc : forall {A} f (l : list A),
  (forall b, exists g a pp, f b |-- own g a pp) ->
  iter_sepcon f l |-- emp.
Proof.
  intros; induction l; simpl; auto.
  eapply derives_trans; [apply sepcon_derives, IHl | rewrite emp_sepcon; auto].
  destruct (H a) as (? & ? & ? & Hf).
  eapply derives_trans; [apply Hf | apply own_dealloc].
Qed.

Lemma own_list_dealloc' : forall {A} g a p (l : list A),
  iter_sepcon (fun x => own (g x) (a x) (p x)) l |-- emp.
Proof.
  intros; apply own_list_dealloc.
  do 3 eexists; apply derives_refl.
Qed.

End ghost.

Definition excl {A} g a := own(RA := exclusive_PCM A) g (Some a) NoneP.

Lemma exclusive_update : forall {A} (v v' : A) p, excl p v |-- |==> excl p v'.
Proof.
  intros; apply own_update.
  intros ? (? & ? & _).
  exists (Some v'); split; simpl; auto; inv H; constructor.
  inv H1.
Qed.

(* lift from veric.invariants *)
#[export] Instance set_PCM : Ghost := invariants.set_PCM.

Definition ghost_set g s := own(RA := set_PCM) g s NoneP.

Lemma ghost_set_join : forall g s1 s2,
  ghost_set g s1 * ghost_set g s2 = !!(Ensembles.Disjoint s1 s2) && ghost_set g (Ensembles.Union s1 s2).
Proof.
  apply invariants.ghost_set_join.
Qed.

Lemma ghost_set_subset : forall g s s' (Hdec : forall a, Ensembles.In s' a \/ ~Ensembles.In s' a),
  Ensembles.Included s' s -> ghost_set g s = ghost_set g s' * ghost_set g (Ensembles.Setminus s s').
Proof.
  apply invariants.ghost_set_subset.
Qed.

Corollary ghost_set_remove : forall g a s,
  Ensembles.In s a -> ghost_set g s = ghost_set g (Ensembles.Singleton a) * ghost_set g (Ensembles.Subtract s a).
Proof.
  apply invariants.ghost_set_remove.
Qed.

Section Snapshot.

Context `{ORD : PCM_order}.

Definition ghost_snap (a : @G P) p := own(RA := snap_PCM) p (Share.bot, a) NoneP.

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

Definition ghost_master sh (a : @G P) p := own(RA := snap_PCM) p (sh, a) NoneP.

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
  - rewrite sepcon_comm, <-sepcon_assoc, (sepcon_comm (ghost_master _ _ _)), snap_master_join; auto.
    apply pred_ext.
    + Intros; rewrite sepcon_comm, IHlv; auto; entailer!.
    + Intros.
      match goal with H : Forall _ _ |- _ => inv H end.
      rewrite prop_true_andp; auto.
      rewrite sepcon_comm, IHlv; auto; entailer!.
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
  rewrite !eq_dec_refl in Hc' |- *; split; auto.
  etransitivity; eauto.
Qed.

Lemma master_init : forall (a : @G P), exists g', joins (Tsh, a) g'.
Proof.
  intros; exists (Share.bot, a), (Tsh, a); simpl.
  split; auto; simpl.
  apply join_refl.
Qed.

#[local] Hint Resolve bupd_intro : ghost.

Lemma make_snap : forall (sh : share) v p, ghost_master sh v p |-- |==> ghost_snap v p * ghost_master sh v p.
Proof.
  intros.
  destruct (eq_dec sh Share.bot).
  - subst; setoid_rewrite ghost_snap_join; [|apply join_refl]; auto with ghost.
  - rewrite snap_master_join; auto; entailer!; auto with ghost.
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
  if_tac; if_tac; try split; auto; try reflexivity; apply join_refl.
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
  Intros; entailer!.
  apply master_update; auto.
Qed.

End Snapshot.

#[global] Hint Resolve bupd_intro : ghost.

Section Reference.

Context {P : Ghost}.

Definition ghost_reference a g := own(RA := ref_PCM P) g (None, Some a) NoneP.
Definition ghost_part sh a g := own(RA := ref_PCM P) g (Some (sh, a), None) NoneP.
Definition ghost_part_ref sh a r g :=
  own(RA := ref_PCM P) g (Some (sh, a), Some r) NoneP.

Lemma ghost_part_join : forall sh1 sh2 sh a1 a2 a g, join sh1 sh2 sh -> join a1 a2 a ->
  sh1 <> Share.bot -> sh2 <> Share.bot ->
  ghost_part sh1 a1 g * ghost_part sh2 a2 g = ghost_part sh a g.
Proof.
  intros.
  symmetry; apply own_op.
  hnf; simpl.
  split; auto; constructor.
Qed.

Lemma ghost_part_ref_join : forall g (sh : share) a b,
  ghost_part sh a g * ghost_reference b g = ghost_part_ref sh a b g.
Proof.
  intros.
  symmetry; apply own_op.
  hnf; simpl.
  split; auto; constructor.
Qed.

Lemma ref_sub_gen : forall g sh a b pp,
  own(RA := ref_PCM P) g (Some (sh, a), None) pp * own(RA := ref_PCM P) g (None, Some b) pp |--
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

Lemma ref_sub : forall g sh a b,
  ghost_part sh a g * ghost_reference b g |--
    !!(if eq_dec sh Tsh then a = b else exists x, join a x b).
Proof.
  intros; apply ref_sub_gen.
Qed.

Lemma self_completable : forall a, completable (Some (Tsh, a)) a.
Proof.
  intros; unfold completable.
  exists None; constructor.
Qed.

Lemma part_ref_valid : forall a, valid(Ghost := ref_PCM P) (Some (Tsh, a), Some a).
Proof.
  intros; hnf; simpl.
  split; auto with share.
  apply self_completable.
Qed.

Lemma ref_update_gen : forall g a r a' pp,
  own(RA := ref_PCM P) g (Some (Tsh, a), Some r) pp |-- |==>
  own(RA := ref_PCM P) g (Some (Tsh, a'), Some a') pp.
Proof.
  intros; apply own_update.
  intros (c, ?) ((x, ?) & [J1 J2] & [? Hvalid]); simpl in *.
  inv J2; [|contradiction].
  destruct c as [(?, c)|], x as [(shx, x)|]; try contradiction.
  - destruct J1 as (? & ? & J & Hx).
    apply join_Tsh in J as []; contradiction.
  - inv J1.
    exists (Some (Tsh, a'), Some a'); repeat split; simpl; auto; try constructor.
    apply self_completable.
Qed.

Lemma ref_update : forall g a r a',
  ghost_part_ref Tsh a r g |-- |==> ghost_part_ref Tsh a' a' g.
Proof.
  intros; apply ref_update_gen.
Qed.

Lemma part_ref_update : forall g sh a r a' r'
  (Ha' : forall b, join a b r -> join a' b r' /\ (a = r -> a' = r')),
  ghost_part_ref sh a r g |-- |==> ghost_part_ref sh a' r' g.
Proof.
  intros; apply own_update.
  intros (c, ?) ((x, ?) & [J1 J2] & [? Hvalid]); simpl in *.
  inv J2; [|contradiction].
  destruct c as [(?, c)|], x as [(shx, x)|]; try contradiction.
  - destruct J1 as (? & ? & ? & Hx).
    assert (join_sub x r) as [f J].
    { destruct Hvalid as [[(?, ?)|] Hvalid]; hnf in Hvalid.
      + destruct Hvalid as (? & ? & ? & ?); eexists; eauto.
      + inv Hvalid; apply join_sub_refl. }
    destruct (join_assoc Hx J) as (b & Jc & Jb%Ha').
    destruct Jb as [Jb Heq].
    destruct (join_assoc (join_comm Jc) (join_comm Jb)) as (x' & Hx' & Hr').
    exists (Some (shx, x'), Some r'); repeat (split; auto); try constructor; simpl.
    + destruct Hvalid as (d & Hvalid); hnf in Hvalid.
      destruct d as [(shd, d)|].
      * exists (Some (shd, f)); destruct Hvalid as (? & ? & ? & Hd); repeat (split; auto).
      * exists None; hnf.
        inv Hvalid; f_equal.
        eapply join_eq; [apply Ha'|]; eauto.
  - inv J1.
    exists (Some (sh, a'), Some r'); repeat split; simpl; auto; try constructor.
    unfold completable in *.
    destruct Hvalid as (d & Hvalid); hnf in Hvalid.
    exists d; destruct d as [(shd, d)|]; hnf.
    + destruct Hvalid as (? & ? & ? & Hd); repeat (split; auto).
      eapply Ha'; auto.
    + inv Hvalid. f_equal.
      symmetry; eapply Ha'; auto.
      apply join_comm, core_unit.
Qed.

Corollary ref_add : forall g sh a r b a' r'
  (Ha : join a b a') (Hr : join r b r'),
  ghost_part_ref sh a r g |-- |==> ghost_part_ref sh a' r' g.
Proof.
  intros; apply part_ref_update; intros c J.
  destruct (join_assoc (join_comm J) Hr) as (? & ? & ?).
  eapply join_eq in Ha; eauto; subst; auto.
  split; auto; intros; subst.
  eapply join_eq; eauto.
Qed.

End Reference.

#[export] Hint Resolve part_ref_valid : init.

#[export] Hint Resolve self_completable : init.

Section GVar.

Context {A : Type}.

Notation ghost_var_PCM A := (@pos_PCM (discrete_PCM A)).

Definition ghost_var (sh : share) (v : A) g :=
  own(RA := @pos_PCM (discrete_PCM A)) g (Some (sh, v)) NoneP.

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

Lemma ghost_var_update' : forall g (v1 v2 v : A), ghost_var gsh1 v1 g * ghost_var gsh2 v2 g |--
  |==> !!(v1 = v2) && (ghost_var gsh1 v g * ghost_var gsh2 v g).
Proof.
  intros; erewrite ghost_var_share_join' by eauto.
  Intros; subst; erewrite ghost_var_share_join by eauto.
  rewrite -> prop_true_andp by auto; apply ghost_var_update.
Qed.

Lemma ghost_var_exclusive : forall sh v p, sh <> Share.bot -> exclusive_mpred (ghost_var sh v p).
Proof.
  intros; unfold exclusive_mpred.
  rewrite ghost_var_share_join_gen.
  Intros sh'.
  apply join_self, identity_share_bot in H1; contradiction.
Qed.

End GVar.

#[export] Hint Resolve ghost_var_exclusive : exclusive.

Section PVar.
(* Like ghost variables, but the partial values may be out of date. *)

Global Program Instance nat_PCM: Ghost := { valid a := True; Join_G a b c := c = Nat.max a b }.
Next Obligation.
  exists (id _); auto; intros.
  - hnf. symmetry; apply Nat.max_id.
  - eexists; eauto.
Defined.
Next Obligation.
  constructor.
  - unfold join; congruence.
  - unfold join; eexists; split; eauto.
    rewrite Nat.max_assoc; subst; auto.
  - unfold join; intros.
    rewrite Nat.max_comm; auto.
  - unfold join; intros.
    apply Nat.le_antisymm; [subst b | subst a]; apply Nat.le_max_l.
Qed.

Global Instance max_order : PCM_order Peano.le.
Proof.
  constructor; auto; intros.
  - constructor; auto. intros ???; lia.
  - eexists; unfold join; simpl; split; eauto.
    apply Nat.max_lub; auto.
  - hnf in H; subst.
    split; [apply Nat.le_max_l | apply Nat.le_max_r].
  - hnf.
    rewrite Nat.max_l; auto.
Qed.

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

Section Option.

Context {P : Ghost}.

Global Program Instance option_PCM : Ghost := { G := option G; valid a := True }.

Context `{ORD : PCM_order(P := P)}.

Definition option_ord (a b : G) : Prop :=
  match a, b with
  | None, _ => True
  | Some a, Some b => ord a b
  | _, _ => False
  end.

#[export] Instance option_ord_refl : Reflexive option_ord.
Proof.
  intros ?.
  destruct x; simpl; auto.
  reflexivity.
Qed.

Global Instance option_order : PCM_order option_ord.
Proof.
  constructor.
  - constructor; [apply option_ord_refl|].
    intros ???. destruct x; simpl in *; auto.
      destruct y; [simpl in * | contradiction].
      destruct z; [|contradiction].
      etransitivity; eauto.
  - intros.
    destruct a; [destruct b|]; simpl in *.
    + destruct c; [|contradiction].
      destruct (ord_lub _ _ _ H H0) as (c' & ? & ?); exists (Some c'); split; auto.
      constructor; auto.
    + exists (Some g); split; auto; constructor.
    + exists b; split; auto; constructor.
  - inversion 1; subst; try solve [split; simpl; auto; reflexivity].
    apply join_ord in H0 as []; auto.
  - destruct b; simpl.
    + destruct a; [|contradiction].
      intros; constructor; apply ord_join; auto.
    + destruct a; constructor.
Qed.

End Option.

Section Maps.

Context {A} {A_eq : EqDec A} {B : Type}.

Implicit Types (k : A) (v : B) (m : A -> option B).

Definition map_add m1 m2 k := match m1 k with Some v' => Some v' | None => m2 k end.

Definition map_upd m k v k' := if eq_dec k' k then Some v else m k'.

Lemma map_upd_triv : forall m k v, m k = Some v -> map_upd m k v = m.
Proof.
  intros; extensionality; unfold map_upd.
  if_tac; subst; auto.
Qed.

Lemma map_upd_comm : forall m k1 v1 k2 v2, k1 <> k2 ->
  map_upd (map_upd m k1 v1) k2 v2 = map_upd (map_upd m k2 v2) k1 v1.
Proof.
  intros; unfold map_upd.
  extensionality; if_tac; if_tac; auto; subst; contradiction.
Qed.

Fixpoint map_upd_list m l :=
  match l with
  | [] => m
  | (k, v) :: rest => map_upd_list (map_upd m k v) rest
  end.

Definition empty_map k : option B := None.

Global Instance Inhabitant_map : Inhabitant (A -> option B) := empty_map.

Definition singleton k v k1 := if eq_dec k1 k then Some v else None.

Lemma map_add_empty : forall m, map_add m empty_map = m.
Proof.
  intros; extensionality; unfold map_add, empty_map.
  destruct (m x); auto.
Qed.

Lemma map_add_single : forall m k v, map_add (singleton k v) m = map_upd m k v.
Proof.
  intros; extensionality; unfold map_add, singleton, map_upd; if_tac; auto.
Qed.

Lemma map_add_assoc : forall m1 m2 m3, map_add (map_add m1 m2) m3 = map_add m1 (map_add m2 m3).
Proof.
  intros; extensionality; unfold map_add.
  destruct (m1 x); auto.
Qed.

Lemma map_add_upd : forall m1 m2 k v, map_upd (map_add m1 m2) k v = map_add (map_upd m1 k v) m2.
Proof.
  intros.
  rewrite <- !map_add_single.
  rewrite map_add_assoc; auto.
Qed.

End Maps.

Section Maps1.

Context {A} {A_eq : EqDec A} {P : Ghost}.

Implicit Types (k : A) (v : G) (m : A -> option G).

Global Instance map_join : Join (A -> option G) := fun a b c => forall k, join (a k) (b k) (c k).

Global Program Instance map_PCM : Ghost := { valid a := True; Join_G := map_join }.

Context `{ORD : PCM_order(P := P)}.

Definition map_incl m1 m2 := forall k, option_ord(ord := ord) (m1 k) (m2 k).

Global Instance map_incl_refl : Reflexive map_incl.
Proof.
  repeat intro; reflexivity.
Qed.

Global Instance map_incl_trans : Transitive map_incl.
Proof.
  repeat intro; etransitivity; eauto.
Qed.

#[export] Instance fmap_order : PCM_order map_incl.
Proof.
  constructor.
  - split; [apply map_incl_refl | apply map_incl_trans].
  - intros ??? Ha Hb. exists (fun k => proj1_sig (ord_lub _ _ _ (Ha k) (Hb k))); split;
      intros k; destruct (ord_lub(ord := option_ord) (a k) (b k) (c k) (Ha k) (Hb k)) as (? & ? & ?); auto.
  - split; repeat intro; specialize (H k); apply (join_ord(ord := option_ord)) in H as []; auto.
  - intros ??? k.
    specialize (H k); apply (ord_join(ord := option_ord)); auto.
Qed.

Lemma map_upd_single : forall m k v, m k = None -> join m (singleton k v) (map_upd m k v).
Proof.
  intros; intros k'.
  unfold singleton, map_upd; if_tac; subst; [|constructor].
  rewrite H; constructor.
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

Lemma map_upd_incl : forall m1 m2 k v, map_incl m1 m2 ->
  m2 k = Some v -> map_incl (map_upd m1 k v) m2.
Proof.
  unfold map_upd; repeat intro.
  destruct (eq_dec k0 k); [|auto].
  subst; rewrite H0; reflexivity.
Qed.

Lemma empty_map_incl : forall m, map_incl empty_map m.
Proof.
  repeat intro; constructor.
Qed.

Lemma map_upd2_incl : forall m1 m2 k v, map_incl m1 m2 -> map_incl (map_upd m1 k v) (map_upd m2 k v).
Proof.
  unfold map_upd; repeat intro.
  if_tac; auto; reflexivity.
Qed.

End Maps1.

Section MapsL.

Context {A B : Type} {A_eq : EqDec A}.

Implicit Types (k : A) (v : B) (m : A -> option B).

Global Instance discrete_order : PCM_order(P := discrete_PCM B) eq.
Proof.
  constructor.
  - constructor.
    + constructor.
    + intros ???; inversion 1; inversion 1; constructor.
  - intros.
    assert (a = c) by (inv H; auto).
    assert (b = c) by (inv H0; auto).
    subst; do 2 eexists; constructor; auto.
  - inversion 1; subst; split; constructor.
  - inversion 1; constructor; auto.
Qed.

Local Notation map_incl := (@map_incl A (discrete_PCM B) eq).

Global Instance map_incl_antisym : Antisymmetric _ eq map_incl.
Proof.
  intros x y Hx Hy.
  extensionality a.
  specialize (Hx a); specialize (Hy a).
  destruct (x a), (y a); simpl in *; auto; try contradiction.
Qed.

Lemma map_add_incl_compat : forall m1 m2 m3, map_incl m1 m2 -> map_incl (map_add m3 m1) (map_add m3 m2).
Proof.
  unfold map_add; repeat intro.
  destruct (m3 k); auto; simpl.
  constructor.
Qed.

Definition compatible m1 m2 := forall k v1 v2, m1 k = Some v1 -> m2 k = Some v2 -> v1 = v2.

Global Instance compatible_refl : Reflexive compatible.
Proof.
  repeat intro.
  congruence.
Qed.

Global Instance compatible_comm : Symmetric compatible.
Proof.
  repeat intro.
  symmetry; eauto.
Qed.

Lemma map_add_comm : forall m1 m2, compatible m1 m2 -> map_add m1 m2 = map_add m2 m1.
Proof.
  intros; extensionality x; unfold map_add.
  destruct (m1 x) eqn: Hm1, (m2 x) eqn: Hm2; eauto.
Qed.

Lemma compatible_add_assoc : forall m1 m2 m3, compatible m1 m2 ->
  compatible (map_add m1 m2) m3 -> compatible m1 (map_add m2 m3).
Proof.
  unfold compatible, map_add; intros.
  repeat match goal with H : forall _, _ |- _ => specialize (H k) end.
  replace (m1 k) with (Some v1) in *.
  destruct (m2 k); auto.
Qed.

Lemma map_incl_spec : forall m1 m2 k v, map_incl m1 m2 -> m1 k = Some v -> m2 k = Some v.
Proof.
  intros; specialize (H k).
  rewrite H0 in H; simpl in H.
  destruct (m2 k); auto; inv H; auto.
Qed.

Lemma compatible_incl : forall m1 m2 m (Hcompat : compatible m2 m) (Hincl : map_incl m1 m2), compatible m1 m.
Proof.
  repeat intro.
  eapply Hcompat; eauto.
  eapply map_incl_spec; eauto.
Qed.

Lemma map_incl_add : forall m1 m2, map_incl m1 (map_add m1 m2).
Proof.
  repeat intro; unfold map_add.
  destruct (m1 k); simpl; auto.
Qed.

Lemma map_incl_compatible : forall m1 m2 m3 (Hincl1 : map_incl m1 m3) (Hincl2 : map_incl m2 m3),
  compatible m1 m2.
Proof.
  intros; intros ??? Hk1 Hk2.
  apply (map_incl_spec _ _ _ _ Hincl1) in Hk1; apply (map_incl_spec _ _ _ _ Hincl2) in Hk2.
  rewrite Hk1 in Hk2; inv Hk2; auto.
Qed.

Lemma map_add_incl : forall m1 m2 m3, map_incl m1 m3 -> map_incl m2 m3 -> map_incl (map_add m1 m2) m3.
Proof.
  unfold map_add; intros.
  intros k.
  destruct (m1 k) eqn: Hk1; auto; simpl.
  eapply map_incl_spec in Hk1 as ->; eauto; constructor.
Qed.

Local Notation map_join := (map_join(P := discrete_PCM B)).

Lemma map_join_spec : forall m1 m2 m3, map_join m1 m2 m3 <-> compatible m1 m2 /\ m3 = map_add m1 m2.
Proof.
  unfold join, map_join; simpl; split; intros.
  - split.
    + repeat intro.
      specialize (H k); rewrite H0, H1 in H; inv H.
      inv H5; auto.
    + extensionality x; unfold map_add.
      specialize (H x); inv H; auto.
      { destruct (m1 x); auto. }
      inv H3; auto.
  - destruct H as [Hcompat]; subst; unfold map_add.
    destruct (m1 k) eqn: Hm1; simpl; try constructor.
    destruct (m2 k) eqn: Hm2; constructor.
    eapply Hcompat in Hm2; eauto; subst; constructor; auto.
Qed.

Lemma map_snap_join : forall m1 m2 p,
  ghost_snap(ORD := fmap_order(P := discrete_PCM B)) m1 p * ghost_snap(ORD := fmap_order(P := discrete_PCM B)) m2 p = !!(compatible m1 m2) && ghost_snap(ORD := fmap_order(P := discrete_PCM B)) (map_add m1 m2) p.
Proof.
  intros; rewrite ghost_snap_join'.
  apply pred_ext.
  - Intros m.
    apply map_join_spec in H as []; subst; entailer!.
  - Intros; Exists (map_add m1 m2).
    setoid_rewrite map_join_spec; entailer!.
Qed.

Lemma compatible_k : forall m1 m2 (Hcompat : compatible m1 m2) k v, m2 k = Some v -> map_add m1 m2 k = Some v.
Proof.
  unfold compatible; intros.
  unfold map_add.
  destruct (m1 k) eqn: Hk; eauto.
Qed.

Lemma map_join_incl_compat : forall m1 m2 m' m'' (Hincl : map_incl m1 m2) (Hjoin : map_join m2 m' m''),
  exists m, map_join m1 m' m /\ map_incl m m''.
Proof.
  intros; apply (@join_comm _ _ (@Perm_G map_PCM)) in Hjoin.
  apply map_join_spec in Hjoin as [Hjoin]; subst.
  do 2 eexists; [|apply map_add_incl_compat; eauto].
  symmetry in Hjoin; eapply compatible_incl in Hjoin; eauto.
  rewrite map_join_spec; split; auto.
  rewrite <- map_add_comm; auto.
Qed.

Lemma incl_compatible : forall m1 m2, map_incl m1 m2 -> compatible m1 m2.
Proof.
  intros; intros ??? Hk1 Hk2.
  eapply map_incl_spec in Hk1; eauto; congruence.
Qed.

Lemma map_add_redundant : forall m1 m2, map_incl m1 m2 -> map_add m1 m2 = m2.
Proof.
  intros; unfold map_add; extensionality k.
  destruct (m1 k) eqn: Hk; auto; symmetry; auto.
  eapply map_incl_spec; eauto.
Qed.

Lemma compatible_upd : forall m1 m2 k v, compatible m1 m2 -> m2 k = None ->
  compatible (map_upd m1 k v) m2.
Proof.
  unfold map_upd; repeat intro.
  destruct (eq_dec k0 k); eauto; congruence.
Qed.

Notation maps_add l := (fold_right map_add empty_map l).

Lemma in_maps_add : forall l (k : A) (v : B), maps_add l k = Some v -> exists m, In m l /\ m k = Some v.
Proof.
  induction l; [discriminate | simpl; intros].
  unfold map_add at 1 in H.
  destruct (a k) eqn: Ha.
  - inv H; eauto.
  - destruct (IHl _ _ H) as (? & ? & ?); eauto.
Qed.

Definition all_compatible (l : list (A -> option B)) := forall m1 m2, In m1 l -> In m2 l -> compatible m1 m2.

Lemma all_compatible_cons : forall (m : A -> option B) l, all_compatible (m :: l) -> compatible m (maps_add l) /\ all_compatible l.
Proof.
  split; repeat intro.
  - eapply in_maps_add in H1 as (m2 & ? & ?).
    eapply (H m m2); simpl; eauto.
  - eapply (H m1 m2); simpl; eauto.
Qed.

Lemma maps_add_in : forall l m (k : A) (v : B) (Hcompat : all_compatible l),
  In m l -> m k = Some v -> maps_add l k = Some v.
Proof.
  induction l; [contradiction | simpl; intros].
  destruct H.
  - subst.
    unfold map_add.
    replace (m k) with (Some v); auto.
  - apply all_compatible_cons in Hcompat as [].
    rewrite map_add_comm; auto.
    unfold map_add.
    erewrite IHl; eauto.
Qed.

Lemma fold_right_maps_add : forall l (e : A -> option B), fold_right map_add e l = map_add (maps_add l) e.
Proof.
  induction l; auto; simpl; intros.
  rewrite map_add_assoc, IHl; auto.
Qed.

Section Maps_Disjoint.
(* This map instance requires that maps be disjoint, providing e.g. uniqueness of
   timestamps for histories. *)

Definition disjoint m1 m2 := forall k v1, m1 k = Some v1 -> m2 k = None.

Global Instance disjoint_comm : Symmetric disjoint.
Proof.
  repeat intro.
  destruct (x k) eqn: Hx; auto.
  specialize (H _ _ Hx); congruence.
Qed.

Lemma disjoint_compatible : forall m1 m2, disjoint m1 m2 -> compatible m1 m2.
Proof.
  repeat intro.
  specialize (H _ _ H0); congruence.
Qed.

Instance map_disj_join : Join (A -> option B) :=
  fun a b c => forall k, match a k, b k with Some v, None | None, Some v => c k = Some v | None, None => c k = None | _, _ => False end.

Lemma map_disj_join_spec : forall m1 m2 m3, join m1 m2 m3 <-> disjoint m1 m2 /\ m3 = map_add m1 m2.
Proof.
  unfold join, map_disj_join; simpl; split; intros.
  - split.
    + repeat intro.
      specialize (H k); rewrite H0 in H.
      destruct (m2 k); auto; contradiction.
    + extensionality k; unfold map_add.
      specialize (H k).
      destruct (m1 k), (m2 k); auto; contradiction.
  - destruct H as [Hdisj]; subst; unfold map_add.
    specialize (Hdisj k).
    destruct (m1 k); [specialize (Hdisj _ eq_refl) as ->; auto|].
    destruct (m2 k); auto.
Qed.

Lemma disjoint_incl : forall m1 m2 m (Hcompat : disjoint m2 m) (Hincl : map_incl m1 m2), disjoint m1 m.
Proof.
  repeat intro; eauto.
  eapply map_incl_spec in Hincl; eauto.
Qed.

Lemma disjoint_add : forall m1 m2 m3, disjoint m1 m2 -> disjoint m1 m3 -> disjoint m1 (map_add m2 m3).
Proof.
  unfold disjoint; intros.
  unfold map_add.
  specialize (H _ _ H1); specialize (H0 _ _ H1).
  rewrite H, H0; auto.
Qed.

Global Program Instance map_disj_PCM : Ghost := { valid a := True; Join_G := map_disj_join }.
Next Obligation.
  exists (fun _ => empty_map); auto; repeat intro.
  - simpl.
    destruct (t k); auto.
  - exists empty_map; hnf.
    intros; simpl; auto.
Defined.
Next Obligation.
  constructor.
  - intros.
    extensionality k.
    specialize (H k); specialize (H0 k).
    destruct (x k), (y k); try congruence; contradiction.
  - intros.
    apply map_disj_join_spec in H as []; apply map_disj_join_spec in H0 as []; subst.
    rewrite map_add_assoc.
    eexists; rewrite !map_disj_join_spec; repeat split.
    + eapply disjoint_incl; eauto.
      rewrite map_add_comm by (apply disjoint_compatible; auto); apply map_incl_add.
    + apply disjoint_add; auto.
      eapply disjoint_incl; eauto.
      apply map_incl_add.
  - intros ???; rewrite !map_disj_join_spec; intros []; subst.
    split; [symmetry | apply map_add_comm, disjoint_compatible]; auto.
  - intros.
    extensionality k; specialize (H k); specialize (H0 k).
    destruct (a k), (b k); auto.
    + destruct (a' k); [contradiction | auto].
    + destruct (a' k); [contradiction | auto].
    + destruct (b' k); [contradiction | auto].
Qed.

Lemma disj_join_sub : forall m1 m2, map_incl m1 m2 -> exists m3, join m1 m3 m2.
Proof.
  intros; exists (fun x => match m2 x, m1 x with Some v, None => Some v | _, _ => None end).
  intro k; specialize (H k).
  destruct (m1 k); simpl in H.
  - destruct (m2 k); [|contradiction].
    inv H; auto.
  - destruct (m2 k); auto.
Qed.

Definition all_disjoint (l : list (A -> option B)) := forall i j, 0 <= i < Zlength l -> 0 <= j < Zlength l ->
  i <> j -> disjoint (Znth i l) (Znth j l).

Lemma all_disjoint_compatible : forall l, all_disjoint l -> all_compatible l.
Proof.
  unfold all_disjoint, all_compatible; intros.
  apply In_Znth in H0 as (i & ? & ?); apply In_Znth in H1 as (j & ? & ?); subst.
  destruct (eq_dec i j); [subst; reflexivity|].
  apply disjoint_compatible; auto.
Qed.

Lemma all_disjoint_nil : all_disjoint [].
Proof.
  repeat intro.
  rewrite Zlength_nil in *; lia.
Qed.

Lemma all_disjoint_cons : forall (m : A -> option B) l, all_disjoint (m :: l) <-> disjoint m (maps_add l) /\ all_disjoint l.
Proof.
  split.
  - split; repeat intro.
    + destruct (maps_add l k) eqn: Hl; auto.
      eapply in_maps_add in Hl as (m2 & ? & ?).
      apply In_Znth in H1 as (j & ? & ?); subst.
      specialize (H 0 (j + 1)).
      rewrite Znth_0_cons, Znth_pos_cons, Z.add_simpl_r, Zlength_cons in H by lia.
      erewrite H in H2; eauto; lia.
    + specialize (H (i + 1) (j + 1)).
      rewrite !Znth_pos_cons, !Z.add_simpl_r, Zlength_cons in H by lia.
      eapply H; eauto; lia.
  - intros []; repeat intro.
    rewrite Zlength_cons in H1, H2.
    destruct (eq_dec i 0), (eq_dec j 0); subst; try contradiction.
    + rewrite Znth_0_cons in H4; rewrite Znth_pos_cons by lia.
      specialize (H _ _ H4).
      destruct (Znth _ _ _) eqn: Hj; auto.
      apply maps_add_in with (l := l) in Hj; try congruence.
      * apply all_disjoint_compatible; auto.
      * apply Znth_In; lia.
    + rewrite Znth_0_cons; rewrite Znth_pos_cons in H4 by lia.
      destruct (m k) eqn: Hm; auto.
      specialize (H _ _ Hm).
      apply maps_add_in with (l := l) in H4; try congruence.
      * apply all_disjoint_compatible; auto.
      * apply Znth_In; lia.
    + rewrite Znth_pos_cons in * by lia.
      eapply (H0 (i - 1) (j - 1)); eauto; lia.
Qed.

Lemma all_disjoint_rev1 : forall l, all_disjoint l -> all_disjoint (rev l).
Proof.
  unfold all_disjoint; intros.
  rewrite Zlength_rev in *.
  rewrite !Znth_rev by auto.
  apply H; lia.
Qed.

Lemma all_disjoint_rev : forall l, all_disjoint l <-> all_disjoint (rev l).
Proof.
  split; [apply all_disjoint_rev1|].
  intros H; apply all_disjoint_rev1 in H.
  rewrite rev_involutive in H; auto.
Qed.

Lemma  maps_add_rev : forall l, all_compatible l -> maps_add (rev l) = maps_add l.
Proof.
  induction l; auto; simpl; intros.
  apply all_compatible_cons in H as [].
  rewrite map_add_comm; auto.
  rewrite fold_right_app; simpl.
  rewrite map_add_empty.
  rewrite (fold_right_maps_add _ a).
  rewrite IHl; auto.
Qed.

Lemma all_disjoint_snoc : forall m l, all_disjoint (l ++ [m]) <-> disjoint m (maps_add l) /\ all_disjoint l.
Proof.
  intros.
  replace (l ++ [m]) with (rev (m :: rev l)) by (simpl; rewrite rev_involutive; auto).
  rewrite all_disjoint_rev, rev_involutive, all_disjoint_cons, <- all_disjoint_rev.
  split; intros []; rewrite ?maps_add_rev in *; auto; apply all_disjoint_compatible; auto.
Qed.

Lemma empty_map_disjoint : forall m, disjoint empty_map m.
Proof.
  repeat intro; discriminate.
Qed.

Definition map_sub (m : A -> option B) k := fun x => if eq_dec x k then None else m x.

Lemma map_upd_sub : forall m (k : A) (v : B), m k = Some v -> map_upd (map_sub m k) k v = m.
Proof.
  intros; unfold map_upd, map_sub.
  extensionality x.
  if_tac; subst; auto.
Qed.

Lemma map_sub_upd : forall m (k : A) (v : B), m k = None -> map_sub (map_upd m k v) k = m.
Proof.
  intros; unfold map_upd, map_sub.
  extensionality x.
  if_tac; subst; auto.
Qed.

Lemma disjoint_sub : forall (m1 m2 : A -> option B) k, disjoint m1 m2 ->
  disjoint (map_sub m1 k) m2.
Proof.
  unfold map_sub, disjoint; intros.
  destruct (eq_dec _ _); [discriminate | eauto].
Qed.

End Maps_Disjoint.

End MapsL.

Notation maps_add l := (fold_right map_add empty_map l).

#[export] Hint Resolve empty_map_incl empty_map_disjoint all_disjoint_nil : core.

Section GHist.

(* Ghost histories in the style of Nanevsky *)
Context {hist_el : Type}.

Notation hist_part := (nat -> option hist_el).

Local Notation map_incl := (@map_incl _ (discrete_PCM hist_el) eq).

Definition hist_sub sh (h : hist_part) hr := sh <> Share.bot /\ if eq_dec sh Tsh then h = hr
  else map_incl h hr.

Lemma completable_alt : forall sh h hr, @completable map_disj_PCM (Some (sh, h)) hr <-> hist_sub sh h hr.
Proof.
  unfold completable, hist_sub; intros; simpl; split.
  - intros ([(?, ?)|] & Hcase).
    + destruct Hcase as (? & ? & Hsh & Hj); split; auto.
      if_tac.
      * subst; apply join_Tsh in Hsh; tauto.
      * apply map_disj_join_spec in Hj as []; subst.
        apply map_incl_add.
    + hnf in Hcase.
      inv Hcase.
      rewrite eq_dec_refl; auto with share.
  - if_tac.
    + intros []; subst; exists None; split; auto.
    + intros [? Hincl].
      apply disj_join_sub in Hincl as (h' & ?).
      exists (Some (Share.comp sh, h')).
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
  eapply @map_upd2_incl; auto.
  apply _.
Qed.

Definition ghost_hist (sh : share) (h : hist_part) g :=
  own(RA := ref_PCM map_disj_PCM) g (Some (sh, h), None) NoneP.

Lemma ghost_hist_join : forall sh1 sh2 sh h1 h2 p (Hsh : sepalg.join sh1 sh2 sh)
  (Hsh1 : sh1 <> Share.bot) (Hsh2 : sh2 <> Share.bot),
  ghost_hist sh1 h1 p * ghost_hist sh2 h2 p = !!(disjoint h1 h2) && ghost_hist sh (map_add h1 h2) p.
Proof.
  intros; unfold ghost_hist.
  erewrite own_op_gen.
  apply pred_ext; Intros; apply andp_right, derives_refl; apply prop_right.
  - destruct H as (? & [] & ?); simpl in *.
    destruct (fst x) as [[]|]; [|contradiction].
    erewrite map_disj_join_spec in H; tauto.
  - eexists (Some (sh, map_add h1 h2), None); split; [split|]; simpl.
    + rewrite map_disj_join_spec; auto.
    + constructor.
    + split; auto.
      intro; subst.
      apply join_Bot in Hsh as []; auto.
  - intros (? & [] & ?); simpl in *.
    destruct (fst x) as [[]|]; [|contradiction].
    split; [simpl | constructor].
    erewrite map_disj_join_spec in *; tauto.
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
    specialize (Hl2 h0); erewrite Hl1 in Hl2; tauto.
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
  own(RA := ref_PCM map_disj_PCM) g (None, Some hr) NoneP.

Lemma hist_next : forall h l (Hlist : hist_list h l), h (length l) = None.
Proof.
  intros.
  specialize (Hlist (length l)).
  destruct (h (length l)); auto.
  destruct (Hlist h0) as [H' _].
  pose proof (nth_error_Some l (length l)) as (Hlt & _).
  lapply Hlt; [lia|].
  rewrite H' by auto; discriminate.
Qed.

Definition ghost_hist_ref sh (h r : hist_part) g :=
  own(RA := ref_PCM map_disj_PCM) g (Some (sh, h), Some r) NoneP.

Lemma hist_add : forall (sh : share) (h h' : hist_part) e p t' (Hfresh : h' t' = None),
  ghost_hist_ref sh h h' p |-- |==> ghost_hist_ref sh (map_upd h t' e) (map_upd h' t' e) p.
Proof.
  intros.
  erewrite (add_andp (ghost_hist_ref _ _ _ _)) by apply own_valid.
  Intros.
  destruct H as [? Hcomp]; simpl in *.
  erewrite completable_alt in Hcomp; destruct Hcomp as [_ Hcomp].
  apply (ref_add(P := map_disj_PCM)) with (b := fun k => if eq_dec k t' then Some e else None).
  - repeat intro.
    unfold map_upd.
    if_tac; [|destruct (h k); auto].
    subst; destruct (h t') eqn: Hh; auto.
    if_tac in Hcomp; [congruence|].
    eapply map_incl_spec in Hh; eauto; congruence.
  - repeat intro.
    unfold map_upd.
    if_tac; [|destruct (h' k); auto].
    subst; rewrite Hfresh; auto.
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
      erewrite nth_error_app2, Nat.sub_diag; auto.
    + rewrite H.
      intro X; rewrite nth_error_app1; auto.
      rewrite <- nth_error_Some, X; discriminate.
  - if_tac.
    + subst; rewrite nth_error_app2, Nat.sub_diag; auto.
    + intro X; apply H; rewrite nth_error_app1 in X; auto.
      assert (t < length (l ++ [e]))%nat; [|rewrite app_length in *; simpl in *; lia].
      rewrite <- nth_error_Some, X; discriminate.
Qed.

Lemma hist_sub_list_incl : forall sh h h' l (Hsub : hist_sub sh h h') (Hlist : hist_list h' l),
  hist_incl h l.
Proof.
  unfold hist_list, hist_incl; intros.
  apply Hlist.
  destruct Hsub.
  destruct (eq_dec sh Tsh); subst; auto.
  eapply map_incl_spec; eauto.
Qed.

Lemma hist_sub_Tsh : forall h h', hist_sub Tsh h h' <-> (h = h').
Proof.
  intros; unfold hist_sub; rewrite eq_dec_refl; repeat split; auto with share; tauto.
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
  intros; erewrite hist_ref_join by auto.
  apply pred_ext; entailer!.
  - apply hist_list_nil_inv2 in H0; subst; auto.
  - Exists (fun _ : nat => @None hist_el); apply andp_right, derives_refl.
    apply prop_right; split; [apply hist_list_nil|].
    split; auto.
    if_tac; [auto|].
    reflexivity.
Qed.

Lemma hist_ref_incl : forall sh h h' p, sh <> Share.bot ->
  ghost_hist sh h p * ghost_ref h' p |-- !!hist_incl h h'.
Proof.
  intros; erewrite hist_ref_join by auto.
  Intros l; eapply prop_right, hist_sub_list_incl; eauto.
Qed.

Lemma hist_add' : forall sh h h' e p, sh <> Share.bot ->
  ghost_hist sh h p * ghost_ref h' p |-- |==>
  ghost_hist sh (map_upd h (length h') e) p * ghost_ref (h' ++ [e]) p.
Proof.
  intros; erewrite !hist_ref_join by auto.
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
  specialize (H _ H1); lia.
Qed.

Corollary newer_upd : forall l t1 e t2, newer l t1 -> (t1 < t2)%nat ->
  newer (map_upd l t1 e) t2.
Proof.
  unfold newer, map_upd; intros.
  destruct (eq_dec t' t1); [lia|].
  eapply newer_trans; eauto; lia.
Qed.

Lemma newer_over : forall h t t', newer h t -> (t <= t')%nat -> h t' = None.
Proof.
  intros.
  specialize (H t').
  destruct (h t'); auto.
  lapply H; [lia | discriminate].
Qed.

Corollary newer_out : forall h t, newer h t -> h t = None.
Proof.
  intros; eapply newer_over; eauto.
Qed.

Lemma add_new_inj : forall h h' t t' v v' (Ht : newer h t) (Ht' : newer h' t'),
  map_upd h t v = map_upd h' t' v' -> h = h' /\ t = t' /\ v = v'.
Proof.
  intros.
  pose proof (equal_f H t) as Hh.
  pose proof (equal_f H t') as Hh'.
  pose proof (newer_out _ _ Ht) as Hout.
  pose proof (newer_out _ _ Ht') as Hout'.
  unfold map_upd in Hh, Hh'.
  rewrite !eq_dec_refl in Hh, Hh'.
  if_tac in Hh.
  - inv Hh; clear Hh'.
    repeat split; auto.
    erewrite <- (map_sub_upd h) by (eapply newer_out; eauto).
    erewrite H, map_sub_upd; auto.
  - erewrite if_false in Hh' by auto.
    lapply (Ht t'); [|rewrite Hh'; discriminate].
    lapply (Ht' t); [|rewrite <- Hh; discriminate].
    lia.
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
| hist_list'_snoc : forall h l t e (Hlast : newer h t) (Hrest : hist_list' h l),
    hist_list' (map_upd h t e) (l ++ [e]).
Local Hint Resolve hist_list'_nil : core.

Lemma hist_list'_in : forall h l (Hl : hist_list' h l) e, (exists t, h t = Some e) <-> In e l.
Proof.
  induction 1.
  - split; [intros (? & ?); discriminate | contradiction].
  - intro; subst; split.
    + unfold map_upd; intros (? & Hin); erewrite in_app in *.
      destruct (eq_dec x t); [inv Hin; simpl; auto|].
      rewrite <- IHHl; eauto.
    + rewrite in_app; intros [Hin | [Heq | ?]]; [| inv Heq | contradiction].
      * rewrite <- IHHl in Hin; destruct Hin as (? & ?).
        apply newer_out in Hlast.
        unfold map_upd; exists x; if_tac; auto; congruence.
      * unfold map_upd; eexists; apply eq_dec_refl.
Qed.

Lemma hist_list_weak : forall l h (Hl : hist_list h l), hist_list' h l.
Proof.
  induction l using rev_ind; intros.
  - apply hist_list_nil_inv2 in Hl; subst; auto.
  - destruct (Hl (length l) x) as (_ & H); exploit H.
    { rewrite nth_error_app2, Nat.sub_diag by lia; auto. }
    intro Hx.
    set (h0 := fun k => if eq_dec k (length l) then None else h k).
    replace h with (map_upd h0 (length l) x).
    constructor.
    + pose proof (hist_list_lt _ _ Hl) as Hn.
      intro t; specialize (Hn t).
      subst h0; simpl; if_tac; [contradiction|].
      intro X; specialize (Hn X); rewrite app_length in Hn; simpl in Hn; lia.
    + apply IHl.
      intros t e; specialize (Hl t e).
      subst h0; simpl; if_tac.
      * split; [discriminate|].
        intro X; assert (t < length l)%nat by (rewrite <- nth_error_Some, X; discriminate); lia.
      * rewrite Hl; destruct (lt_dec t (length l)).
        { erewrite nth_error_app1 by auto; reflexivity. }
        split; intro X.
        -- assert (t < length (l ++ [x]))%nat by (rewrite <- nth_error_Some, X; discriminate);
             rewrite app_length in *; simpl in *; lia.
        -- assert (t < length l)%nat by (rewrite <- nth_error_Some, X; discriminate); contradiction.
    + unfold map_upd; subst h0; simpl.
      extensionality k'; if_tac; subst; auto.
Qed.

Lemma hist_list'_add : forall h1 h2 (l : list hist_el) (Hdisj : disjoint h1 h2), hist_list' (map_add h1 h2) l ->
  exists l1 l2, Permutation l (l1 ++ l2) /\ hist_list' h1 l1 /\ hist_list' h2 l2.
Proof.
  intros.
  remember (map_add h1 h2) as h.
  revert dependent h2; revert h1; induction H; intros.
  - exists [], []; split; [reflexivity|].
    assert (h1 = empty_map /\ h2 = empty_map) as [].
    { split; extensionality k; apply equal_f with (x := k) in Heqh; unfold map_add in Heqh;
        destruct (h1 k); auto; discriminate. }
    subst; split; constructor.
  - pose proof (equal_f Heqh t) as Ht.
    unfold map_upd, map_add in Ht.
    erewrite eq_dec_refl in Ht by auto.
    destruct (h1 t) eqn: Hh1.
    + inv Ht.
      destruct (IHhist_list' (map_sub h1 t) h2) as (l1 & l2 & ? & ? & ?).
      { apply disjoint_sub; auto. }
      { extensionality k.
        apply equal_f with (x := k) in Heqh.
        unfold map_upd, map_sub, map_add in *.
        if_tac; auto; subst.
        apply newer_out in Hlast.
        apply Hdisj in Hh1; congruence. }
      exists (l1 ++ [h0]), l2; repeat split; auto.
      * etransitivity; [|apply Permutation_app_comm].
        rewrite app_assoc; apply Permutation_app_tail.
        etransitivity; eauto.
        apply Permutation_app_comm.
      * erewrite <- (map_upd_sub h1 t) by eauto.
        constructor; auto.
        repeat intro.
        unfold map_sub in *.
        apply equal_f with (x := t') in Heqh.
        unfold map_upd, map_add in Heqh.
        apply Hlast.
        destruct (eq_dec _ _); [contradiction|].
        destruct (h1 t'); [congruence | contradiction].
    + destruct (IHhist_list' h1 (map_sub h2 t)) as (l1 & l2 & ? & ? & ?).
      { symmetry; apply disjoint_sub; symmetry; auto. }
      { extensionality k.
        apply equal_f with (x := k) in Heqh.
        unfold map_upd, map_sub, map_add in *.
        if_tac; auto; subst.
        apply newer_out in Hlast.
        rewrite Hh1; auto. }
      exists l1, (l2 ++ [e]); repeat split; auto.
      * rewrite app_assoc; apply Permutation_app_tail; auto.
      * erewrite <- (map_upd_sub h2 t) by eauto.
        constructor; auto.
        repeat intro.
        unfold map_sub in *.
        apply equal_f with (x := t') in Heqh.
        unfold map_upd, map_add in Heqh.
        apply Hlast.
        destruct (eq_dec _ _); [contradiction|].
        destruct (h1 t'); congruence.
Qed.

Lemma ghost_hist_init : @valid (ref_PCM (@map_disj_PCM nat hist_el)) (Some (Tsh, empty_map), Some empty_map).
Proof.
  split; simpl; auto with share.
  rewrite completable_alt; split; auto with share.
  rewrite eq_dec_refl; auto.
Qed.

Inductive add_events h : list hist_el -> hist_part -> Prop :=
| add_events_nil : add_events h [] h
| add_events_snoc : forall le h' t e (Hh' : add_events h le h') (Ht : newer h' t),
    add_events h (le ++ [e]) (map_upd h' t e).
Local Hint Resolve add_events_nil : core.

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
  - eexists; erewrite map_add_empty; split; auto; discriminate.
  - destruct IHadd_events as (h2 & ? & Hh2); subst.
    assert (compatible h h2).
    { repeat intro.
      destruct (Hh2 _ _ H1) as [Hk _].
      specialize (Hk k); lapply Hk; [lia | congruence]. }
    assert (newer h t).
    { repeat intro; apply Ht.
      unfold map_add.
      destruct (h t'); auto. }
    erewrite map_add_comm, map_add_upd, map_add_comm; auto.
    eexists; split; eauto; intros.
    unfold map_upd in *.
    rewrite in_app; simpl.
    destruct (eq_dec t0 t); [inv H2; auto|].
    destruct (Hh2 _ _ H2); auto.
    { apply compatible_upd; [symmetry; auto|].
      specialize (H1 t).
      destruct (h t); auto.
      lapply H1; [lia | discriminate]. }
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
  eapply map_incl_spec in Ht' as ->; eauto.
  eapply add_events_incl; eauto.
Qed.

Lemma add_events_in : forall h le h' e, add_events h le h' -> In e le ->
  exists t, newer h t /\ h' t = Some e.
Proof.
  induction 1; [contradiction|].
  rewrite in_app; intros [? | [? | ?]]; try contradiction.
  - destruct IHadd_events as (? & ? & ?); auto.
    do 2 eexists; eauto.
    unfold map_upd; if_tac; auto; subst.
    specialize (Ht t); rewrite H2 in Ht; lapply Ht; [lia | discriminate].
  - subst; unfold map_upd; do 2 eexists; [|apply eq_dec_refl].
    eapply add_events_newer; eauto.
Qed.

End GHist.

#[export] Hint Resolve hist_incl_nil hist_list_nil hist_list'_nil add_events_nil : core.
(*#[export] Hint Resolve ghost_var_precise ghost_var_precise'.*)
#[export] Hint Resolve (*ghost_var_init*) master_init (*ghost_map_init*) ghost_hist_init : init.

Lemma wand_nonexpansive_l: forall P Q n,
  approx n (P -* Q)%logic = approx n (approx n P  -* Q)%logic.
Proof.
  apply wand_nonexpansive_l.
Qed.

Lemma wand_nonexpansive_r: forall P Q n,
  approx n (P -* Q)%logic = approx n (P  -* approx n Q)%logic.
Proof.
  apply wand_nonexpansive_r.
Qed.

Lemma wand_nonexpansive: forall P Q n,
  approx n (P -* Q)%logic = approx n (approx n P  -* approx n Q)%logic.
Proof.
  apply wand_nonexpansive.
Qed.

Corollary view_shift_nonexpansive : forall P Q n,
  approx n (P -* |==> Q)%logic = approx n (approx n P  -* |==> approx n Q)%logic.
Proof.
  intros.
  rewrite wand_nonexpansive, approx_bupd; reflexivity.
Qed.

Ltac ghost_alloc G :=
  match goal with |-semax _ (PROPx _ (LOCALx _ (SEPx (?R1 :: _)))) _ _ =>
    rewrite <- (emp_sepcon R1) at 1; Intros; viewshift_SEP 0 (EX g : _, G g);
  [go_lowerx; eapply derives_trans; [|unseal_derives; apply fupd.bupd_fupd]; rewrite ?emp_sepcon;
   apply own_alloc; auto; simpl; auto with init share ghost|] end.

Ltac ghosts_alloc G n :=
  match goal with |-semax _ (PROPx _ (LOCALx _ (SEPx (?R1 :: _)))) _ _ =>
    rewrite <- (emp_sepcon R1) at 1; Intros; viewshift_SEP 0 (EX lg : _, !!(Zlength lg = n) && iter_sepcon G lg);
  [go_lowerx; eapply derives_trans; [|unseal_derives; apply fupd.bupd_fupd]; rewrite ?emp_sepcon;
   apply own_list_alloc'; auto; simpl; auto with init share ghost|] end.
