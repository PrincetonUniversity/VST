Require Import veric.base.
Require Import msl.msl_standard.
Require Import veric.compcert_rmaps.

Open Local Scope pred.

Definition slice_resource (rsh: share) (sh: pshare) (r: resource) :=
  match r with
   | NO _ => NO rsh
   | YES _ _ k pp => YES rsh sh k pp
   | PURE k pp => PURE k pp
 end.

Lemma slice_resource_valid:
  forall rsh sh phi, AV.valid (fun l => res_option (slice_resource (rsh l) sh (phi @ l))).
Proof.
intros.
unfold slice_resource.
intro; intros.
case_eq (phi @ (b,ofs)); intros; simpl; auto.
generalize (rmap_valid phi b ofs); unfold compose; intro.
rewrite H in H0. simpl in H0.
destruct k; simpl; auto.
+ intros; specialize (H0 _ H1).
  destruct (phi @ (b,ofs+i)); inv H0; auto.
+ destruct H0 as [n [? ?]].
  exists n; split; auto.
  destruct (phi @ (b,ofs-z)); inv H1; auto.
Qed.

Lemma slice_rmap_valid:
    forall rsh sh m, CompCert_AV.valid (res_option oo (fun l => slice_resource (rsh l) sh (m @ l))).
Proof.
intros.
intros b ofs.
unfold compose.
case_eq (m @ (b,ofs)); intros; simpl; auto.
generalize (rmap_valid m b ofs); unfold compose; simpl; rewrite H; simpl; intro.
destruct k; auto; intros.
specialize (H0 _ H1).
destruct (m @ (b,ofs+i)); inv H0; auto.
destruct H0 as [n [? ?]]. exists n; split; auto.
destruct (m @ (b,ofs-z)); inv H1; auto.
Qed.

Lemma slice_rmap_ok: forall rsh sh m,
  resource_fmap (approx (level m)) (approx (level m)) oo
    (fun l => slice_resource (rsh l) sh (m @ l)) =
       (fun l => slice_resource (rsh l) sh (m @ l)).
Proof.
intros.
extensionality l; unfold compose; simpl.
case_eq (m@l); simpl; intros; auto.
generalize (eq_sym (resource_at_approx m l)); intro.
pattern (m@l) at 2 in H0; rewrite H in H0.
simpl in H0.
rewrite H in H0.
inversion H0.
rewrite <- H2.
rewrite <- H2.
auto.
generalize (eq_sym (resource_at_approx m l)); intro.
pattern (m@l) at 2 in H0; rewrite H in H0.
simpl in H0.
rewrite H in H0.
inversion H0.
rewrite <- H2.
rewrite <- H2.
auto.
Qed.

Definition slice_rmap (rsh: address -> share) (sh: pshare) (m: rmap) : rmap :=
   proj1_sig (make_rmap _ (slice_rmap_valid rsh sh m) (level m) (slice_rmap_ok rsh sh m)).

Lemma resource_at_slice:
  forall rsh sh m l, resource_at (slice_rmap rsh sh m) l = slice_resource (rsh l) sh (resource_at m l).
Proof.
intros.
unfold slice_rmap.
case_eq (make_rmap (fun l : CompCert_AV.address => slice_resource (rsh l) sh (m @ l))
             (slice_rmap_valid rsh sh m) (level m)
             (slice_rmap_ok rsh sh m)); intros.
simpl.
generalize a; intros [? ?].
rewrite H1.
auto.
Qed.

Lemma slice_rmap_level: forall rsh sh w, level (slice_rmap rsh sh w) = level w.
Proof.
intros.
unfold slice_rmap.
case_eq (make_rmap (fun l  => slice_resource (rsh l) sh (w @ l))
        (slice_rmap_valid rsh sh w) (level w)
        (slice_rmap_ok rsh sh w)); intros.
simpl.
clear H; destruct a; auto.
Qed.

Lemma slice_rmap_join: forall rsh1 rsh2 rsh (sh1 sh2 sh: pshare) w,
    join rsh1 rsh2 rsh ->
    join (pshare_sh sh1) (pshare_sh sh2) (pshare_sh sh) ->
     join (slice_rmap rsh1 sh1 w) (slice_rmap rsh2 sh2 w) (slice_rmap rsh sh w).
Proof.
intros.
apply resource_at_join2.
transitivity (level w).
apply slice_rmap_level.
symmetry; apply slice_rmap_level.
transitivity (level w).
apply slice_rmap_level.
symmetry; apply slice_rmap_level.
intro loc.
repeat rewrite resource_at_slice.
destruct (w @ loc); simpl; constructor; auto.
Qed.

Definition split_resource r :=
  match r with YES rsh sh k pp => (YES (fst (Share.split rsh)) (fst (split_pshare sh)) k pp ,
                                                       YES (snd (Share.split rsh)) (snd (split_pshare sh)) k pp)
                     | PURE k pp => (PURE k pp, PURE k pp)
                     | NO rsh => (NO (fst (Share.split rsh)) ,NO (snd (Share.split rsh)))
  end.

Lemma split_rmap_valid1:
  forall m, CompCert_AV.valid (res_option oo (fun l => fst (split_resource (m@l)))).
Proof.
intros.
unfold compose; intros b ofs.
generalize (rmap_valid m b ofs); unfold compose; intro.
destruct (m @ (b,ofs)); simpl in *; auto; destruct k; auto.
intros. spec H i H0. destruct (m @(b,ofs+i)); inv H; auto.
destruct H as [n [? ?]].
exists n; split; auto.
destruct (m @ (b,ofs-z)); inv H0; auto.
Qed.

Lemma split_rmap_valid2:
  forall m, CompCert_AV.valid (res_option oo (fun l => snd (split_resource (m@l)))).
Proof.
intros.
unfold compose; intros b ofs.
generalize (rmap_valid m b ofs); unfold compose; intro.
destruct (m @ (b,ofs)); simpl in *; auto; destruct k; auto.
intros. spec H i H0. destruct (m @(b,ofs+i)); inv H; auto.
destruct H as [n [? ?]].
exists n; split; auto.
destruct (m @ (b,ofs-z)); inv H0; auto.
Qed.

Lemma split_rmap_ok1: forall m,
  resource_fmap (approx (level m)) (approx (level m)) oo (fun l => fst (split_resource (m @ l))) =
       (fun l => fst (split_resource (m @ l))).
Proof.
intros.
extensionality l; unfold compose; simpl.
case_eq (m@l); simpl; intros; auto.
generalize (eq_sym (resource_at_approx m l)); intro.
pattern (m@l) at 2 in H0; rewrite H in H0.
simpl in H0.
rewrite H in H0.
inversion H0.
rewrite <- H2.
rewrite <- H2.
auto.
generalize (eq_sym (resource_at_approx m l)); intro.
pattern (m@l) at 2 in H0; rewrite H in H0.
simpl in H0.
rewrite H in H0.
inversion H0.
rewrite <- H2.
rewrite <- H2.
auto.
Qed.

Lemma split_rmap_ok2: forall m,
  resource_fmap (approx (level m)) (approx (level m)) oo (fun l => snd (split_resource (m @ l))) =
       (fun l => snd (split_resource (m @ l))).
Proof.
intros.
extensionality l; unfold compose; simpl.
case_eq (m@l); simpl; intros; auto.
generalize (eq_sym (resource_at_approx m l)); intro.
pattern (m@l) at 2 in H0; rewrite H in H0.
simpl in H0.
rewrite H in H0.
inversion H0.
rewrite <- H2.
rewrite <- H2.
auto.
generalize (eq_sym (resource_at_approx m l)); intro.
pattern (m@l) at 2 in H0; rewrite H in H0.
simpl in H0.
rewrite H in H0.
inversion H0.
rewrite <- H2.
rewrite <- H2.
auto.
Qed.


Definition split_rmap (m: rmap) : rmap * rmap :=
 (proj1_sig (make_rmap _ (split_rmap_valid1 m) (level m) (split_rmap_ok1 m)),
  proj1_sig (make_rmap _ (split_rmap_valid2 m) (level m) (split_rmap_ok2 m))).

Lemma split_resource_join: forall r, join (fst (split_resource r)) (snd (split_resource r)) r.
Proof.
intro.
destruct r; simpl; constructor; auto; try (apply split_join; apply surjective_pairing).
Qed.

Lemma split_rmap_join:
  forall m, join (fst (split_rmap m)) (snd (split_rmap m)) m.
Proof.
intros.
unfold split_rmap; simpl.
case_eq (make_rmap _ (split_rmap_valid1 m) (level m) (split_rmap_ok1 m)); intros.
case_eq (make_rmap _ (split_rmap_valid2 m) (level m) (split_rmap_ok2 m)); intros.
simpl in *.
generalize a; intros  [? ?].
generalize a0; intros [? ?].
apply resource_at_join2; simpl; try congruence.
rewrite H2; rewrite H4; simpl; auto.
intro l.
apply split_resource_join; auto.
Qed.

Lemma split_rmap_at1:
  forall m l , fst (split_rmap m) @ l = fst (split_resource (m @ l)).
Proof.
unfold split_rmap; intros; simpl.
case_eq (make_rmap _ (split_rmap_valid1 m) (level m) (split_rmap_ok1 m)); intros.
simpl in *.
destruct a. rewrite e0; auto.
Qed.

Lemma split_rmap_at2:
  forall m l , snd (split_rmap m) @ l = snd (split_resource (m @ l)).
Proof.
unfold split_rmap; intros; simpl.
case_eq (make_rmap _ (split_rmap_valid2 m) (level m) (split_rmap_ok2 m)); intros.
simpl. clear H; destruct a. rewrite H0; auto.
Qed.

Definition split_shareval (shv: Share.t * val) : ((Share.t * val) * (Share.t * val)) :=
  ((fst (Share.split (fst shv)), snd shv), (snd (Share.split (fst shv)), snd shv)).

Definition general_slice_resource (sh: share) (r: resource) : resource.
  refine (match r with
          | NO _ => NO (Share.unrel Share.Lsh sh)
          | YES _ _ k pp => _
          | PURE k pp => PURE k pp
          end).
  destruct (dec_share_identity (Share.unrel Share.Rsh sh)).
  + exact (NO (Share.unrel Share.Lsh sh)).
  + apply nonidentity_nonunit in n.
    refine (YES (Share.unrel Share.Lsh sh) (mk_pshare _ n) k pp).
Defined.

Lemma general_slice_resource_valid:
  forall sh phi P (P_DEC: forall l, {P l} + {~ P l}),
  (forall l, ~ P l -> identity (phi @ l)) ->
  AV.valid (fun l => res_option (if P_DEC l then general_slice_resource sh (phi @ l) else phi @ l)).
Proof.
intros ? ? ? ? H_id.
unfold general_slice_resource.
pose proof rmap_valid phi as H_valid.
unfold compose in H_valid.
change compcert_rmaps.R.res_option with res_option in H_valid.
intro; intros.
destruct (P_DEC (b, ofs)).
+ specialize (H_valid b ofs); cbv beta in H_valid.
  destruct (phi @ (b, ofs)) eqn:?H; intros; simpl in H_valid |- *; auto.
  destruct (dec_share_identity (Share.unrel Share.Rsh sh)) as [HH | HH];
    try solve [simpl; auto].
  simpl.
  destruct k; simpl; auto.
  - intros. specialize (H_valid _ H0).
    destruct (P_DEC (b, ofs + i)) as [HHp | HHp].
    * destruct (phi @ (b, ofs + i)); inv H_valid; auto.
    * specialize (H_id _ HHp).
      destruct (phi @ (b, ofs + i)); inv H_valid.
      apply YES_not_identity in H_id; tauto.
  - destruct H_valid as [n [? ?]].
    exists n; split; auto.
    destruct (P_DEC (b, ofs - z)) as [HHm | HHm].
    * destruct (phi @ (b, ofs - z)); inv H1; auto.
    * specialize (H_id _ HHm).
      destruct (phi @ (b, ofs - z)); inv H1.
      apply YES_not_identity in H_id; tauto.
+ specialize (H_valid b ofs); cbv beta in H_valid.
  destruct (phi @ (b, ofs)) eqn:?H; intros; simpl in H_valid |- *; auto.
  simpl.
  specialize (H_id _ n).
  rewrite H in H_id.
  apply YES_not_identity in H_id; tauto.
Qed.

