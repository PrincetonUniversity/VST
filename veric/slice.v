Require Import veric.base.
Require Import msl.msl_standard.
Require Import veric.shares.
Require Import veric.compcert_rmaps.
Require Import veric.res_predicates.

Open Local Scope pred.

Lemma rshare_sh_readable:
 forall r, readable_share (rshare_sh r).
Proof.
destruct r; simpl.
destruct p;
auto.
Qed.

(*
Definition slice_resource (sh: share) (rsh: readable_share sh) (r: resource) :=
  match r with
   | NO _ _ => NO (retainer_part sh) (@retainer_part_nonreadable sh)
   | YES _ _ k pp => YES sh rsh k pp
   | PURE k pp => PURE k pp
 end.

Lemma slice_resource_valid:
  forall sh rsh phi, 
   AV.valid (fun l => res_option (slice_resource (retain l) rsh (phi @ l))).
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
  simpl. f_equal. f_equal. apply exist_ext.
  unfold retainer_part. rewrite !Share.distrib1.
  rewrite <- !(Share.glb_assoc Share.Rsh).
  rewrite !(Share.glb_commute Share.Rsh).
  rewrite !glb_Lsh_Rsh.
  rewrite !(Share.glb_commute Share.bot).
  rewrite !(Share.glb_bot). auto.
+ destruct H0 as [n [? ?]].
  exists n; split; auto.
  destruct (phi @ (b,ofs-z)); inv H1; auto.
  simpl. f_equal. f_equal. apply exist_ext.
  unfold retainer_part. rewrite !Share.distrib1.
  rewrite <- !(Share.glb_assoc Share.Rsh).
  rewrite !(Share.glb_commute Share.Rsh).
  rewrite !glb_Lsh_Rsh.
  rewrite !(Share.glb_commute Share.bot).
  rewrite !(Share.glb_bot). auto.
Qed.

Lemma slice_rmap_valid:
    forall retain rsh m, CompCert_AV.valid 
        (res_option oo (fun l => slice_resource (retain l) rsh (m @ l))).
Proof.
intros.
replace (res_option
   oo (fun l : AV.address =>
       slice_resource (retain l) rsh (m @ l)))
with (fun l => res_option (slice_resource (retain l) rsh (m @ l))).
apply slice_resource_valid.
extensionality l.
unfold compose. auto.
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

Definition slice_rmap (retain: address -> share) (rsh: rshare) (m: rmap) : rmap :=
   proj1_sig (make_rmap _ (slice_rmap_valid retain rsh m) (level m) 
                     (slice_rmap_ok retain rsh m)).

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

Lemma slice_rmap_level: forall retain rsh w, level (slice_rmap retain rsh w) = level w.
Proof.
intros.
unfold slice_rmap.
case_eq (make_rmap (fun l  => slice_resource (retain l) rsh (w @ l))
        (slice_rmap_valid retain rsh w) (level w)
        (slice_rmap_ok retain rsh w)); intros.
simpl.
clear H; destruct a; auto.
Qed.

Lemma slice_rmap_join: forall retain1 retain2 retain rsh1 rsh2 rsh w,
    join retain1 retain2 retain ->
    join (rshare_sh rsh1) (rshare_sh rsh2) (rshare_sh rsh) ->
     join (slice_rmap retain1 rsh1 w) (slice_rmap retain2 rsh2 w) 
          (slice_rmap retain rsh w).
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
specialize (H loc).
destruct (w @ loc); simpl; constructor; auto.
apply (join_comp_parts comp_Lsh_Rsh H).
destruct rsh1 as [sh1 ?].
destruct rsh2 as [sh2 ?].
destruct rsh as [sh3 ?].
unfold retainer_part.
simpl in *.
apply (comp_parts_join comp_Lsh_Rsh).
destruct p0,p1,p2.
rewrite !Share.distrib1.
rewrite H1,H3,H5.
rewrite !Share.lub_bot.
rewrite !glb_twice.
apply (join_comp_parts comp_Lsh_Rsh H).
rewrite !Share.distrib1.
  rewrite <- !(Share.glb_assoc Share.Rsh).
  rewrite !(Share.glb_commute Share.Rsh).
  rewrite !glb_Lsh_Rsh.
  rewrite !(Share.glb_commute Share.bot).
  rewrite !(Share.glb_bot).
  rewrite !(Share.lub_commute Share.bot).
  rewrite !(Share.lub_bot).
  rewrite <- !(Share.glb_commute Share.Rsh).
apply (join_comp_parts comp_Lsh_Rsh H0).
Qed.
*)

(*
Definition split_parts (sh: Share.t) : Share.t * Share.t :=
 (Share.lub (fst (Share.split (Share.glb Share.Lsh sh))) (fst (Share.split (Share.glb Share.Rsh sh))),
  Share.lub (snd (Share.split (Share.glb Share.Lsh sh))) (snd (Share.split (Share.glb Share.Rsh sh)))).
*)

Lemma split_NO_ok1:
  forall sh, ~readable_share sh -> ~ readable_share (fst (Share.split sh)).
Proof.
intros.
destruct (Share.split sh) eqn:?H.
simpl.
contradict H.
do 3 red in H|-*.
contradict H.
pose proof (split_join _ _ _ H0).
apply (join_comp_parts comp_Lsh_Rsh) in H1.
destruct H1 as [_ ?].
apply split_identity in H1; auto.
Qed.

Lemma split_NO_ok2:
  forall sh, ~readable_share sh -> ~ readable_share (snd (Share.split sh)).
Proof.
intros.
destruct (Share.split sh) eqn:?H.
simpl.
contradict H.
do 3 red in H|-*.
contradict H.
pose proof (split_join _ _ _ H0).
apply (join_comp_parts comp_Lsh_Rsh) in H1.
destruct H1 as [_ ?].
apply join_comm in H1.
apply split_identity in H1; auto.
Qed.

Lemma glb_split_lemma1:
  forall a b, Share.glb Share.Rsh a = Share.glb Share.Rsh b ->
     Share.glb Share.Rsh (fst (Share.split a)) =
     Share.glb Share.Rsh (fst (Share.split b)).
Proof.
Admitted.

Lemma glb_split_lemma2:
  forall a b, Share.glb Share.Rsh a = Share.glb Share.Rsh b ->
     Share.glb Share.Rsh (snd (Share.split a)) =
     Share.glb Share.Rsh (snd (Share.split b)).
Admitted.

Lemma fst_split_glb_orthogonal: forall sh : share,
identity (Share.glb Share.Rsh (fst (Share.split sh))) ->
identity (Share.glb Share.Rsh sh).
Proof.
Admitted.

Lemma snd_split_glb_orthogonal: forall sh : share,
identity (Share.glb Share.Rsh (snd (Share.split sh))) ->
identity (Share.glb Share.Rsh sh).
Admitted.

Lemma split_YES_ok1:
 forall sh, readable_share sh -> readable_share (fst (Share.split sh)).
Proof.
intros.
destruct (Share.split sh) eqn:?H.
simpl in *.
do 3 red in H|-*.
contradict H.
replace t with (fst (Share.split sh)) in H by (rewrite H0; reflexivity).
apply fst_split_glb_orthogonal; auto.
Qed.

Lemma split_YES_ok2:
 forall sh, readable_share sh -> readable_share (snd (Share.split sh)).
Proof.
intros.
destruct (Share.split sh) eqn:?H.
simpl in *.
do 3 red in H|-*.
contradict H.
replace t0 with (snd (Share.split sh)) in H by (rewrite H0; reflexivity).
apply snd_split_glb_orthogonal; auto.
Qed.


Definition split_resource r :=
  match r with YES sh rsh k pp => 
               (YES (fst (Share.split sh)) (split_YES_ok1 _ rsh) k pp , 
                YES (snd (Share.split sh)) (split_YES_ok2 _ rsh) k pp)
             | PURE k pp => (PURE k pp, PURE k pp)
             | NO sh nsh => (NO (fst (Share.split sh)) (split_NO_ok1 _ nsh),
                             NO (snd (Share.split sh)) (split_NO_ok2 _ nsh))
  end.

Lemma split_rmap_valid1:
  forall m, CompCert_AV.valid (res_option oo (fun l => fst (split_resource (m@l)))).
Proof.
intros.
unfold compose; intros b ofs.
generalize (rmap_valid m b ofs); unfold compose; intro.
destruct (m @ (b,ofs)); simpl in *; auto; destruct k; auto.
*
intros. spec H i H0. destruct (m @(b,ofs+i)); inv H; auto.
simpl. f_equal. f_equal. apply exist_ext.
apply glb_split_lemma1; auto.
*
destruct H as [n [? ?]].
exists n; split; auto.
destruct (m @ (b,ofs-z)); inv H0; auto.
simpl. f_equal. f_equal. apply exist_ext.
apply glb_split_lemma1; auto.
Qed.

Lemma split_rmap_valid2:
  forall m, CompCert_AV.valid (res_option oo (fun l => snd (split_resource (m@l)))).
Proof.
intros.
unfold compose; intros b ofs.
generalize (rmap_valid m b ofs); unfold compose; intro.
destruct (m @ (b,ofs)); simpl in *; auto; destruct k; auto.
*
intros. spec H i H0. destruct (m @(b,ofs+i)); inv H; auto.
simpl. f_equal. f_equal. apply exist_ext.
apply glb_split_lemma2; auto.
*
destruct H as [n [? ?]].
exists n; split; auto.
destruct (m @ (b,ofs-z)); inv H0; auto.
simpl. f_equal. f_equal. apply exist_ext.
apply glb_split_lemma2; auto.
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

Definition general_slice_resource (sh: share) (r: resource) : resource :=
  match r with
   | NO _ _ => NO (retainer_part sh) (retainer_part_nonreadable sh)
   | YES _ _ k pp =>
    match readable_share_dec sh with
    | left r1 => YES sh r1 k pp
    | right n => NO sh n
    end
   | PURE k pp => PURE k pp
  end.

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
  destruct (readable_share_dec sh) as [HH | HH];
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

Lemma make_slice_rmap: forall w (P: address -> Prop) (P_DEC: forall l, {P l} + {~ P l}) sh,
  (forall l : AV.address, ~ P l -> identity (w @ l)) ->
  {w' | level w' = level w /\ compcert_rmaps.R.resource_at w' =
       (fun l => if P_DEC l then general_slice_resource sh (w @ l) else w @ l)}.
Proof.
  intros.
  pose (f l := if P_DEC l then general_slice_resource sh (w @ l) else w @ l).
  assert (Vf: AV.valid (res_option oo f)) by (apply general_slice_resource_valid; auto).
  apply (make_rmap _ Vf (level w)).
  extensionality loc; unfold compose, f.
  destruct (P_DEC loc).
  + pose proof resource_at_approx w loc.
    destruct (w @ loc); auto.
    simpl.
    destruct (readable_share_dec sh); auto.
    inversion H0.
    simpl; f_equal; f_equal; auto.
  + apply resource_at_approx.
Qed.

Lemma jam_noat_splittable_aux:
  forall S' S Q (PARAMETRIC: spec_parametric Q)
           (sh1 sh2 sh3: share)
           (rsh1: readable_share sh1) (rsh2: readable_share sh2)
           l
           (H: join sh1 sh2 sh3)
           w (H0: allp (@jam _ _ _ _ _ _ (S' l) (S l) (Q l sh3) noat) w)
           f (Hf: resource_at f = fun loc => general_slice_resource (if S l loc then sh1 else Share.bot) (w @ loc))
           g (Hg: resource_at g = fun loc => general_slice_resource (if S l loc then sh2 else Share.bot) (w @ loc))
           (H1: join f g w),
           allp (jam (S l) (Q l sh1) noat) f.
Proof.
intros.
(*assert (rsh3: readable_share sh3) by (eapply readable_share_join ; eauto). *)
intro l'.
spec H0 l'.
unfold jam in H0 |- *.
simpl in H0|-*.
if_tac.
destruct (PARAMETRIC l l') as [pp [ok ?]]; clear PARAMETRIC.
rewrite H3 in H0 |- *; clear H3.
destruct H0 as [rsh3 [k [? ?]]].
exists rsh1, k; split; auto.
clear H0.
case_eq (w @ l'); intros.
inversion2 H0 H3. 
destruct p.
inversion2 H0 H3.
generalize (resource_at_join _ _ _ l' H1); intro.
generalize (f_equal (resource_at f) (refl_equal l')); intro.
pattern f at 1 in H4; rewrite Hf in H4.
rewrite H0 in H4.
rewrite H4.
rewrite if_true in H4|-* by auto.
simpl.
destruct (readable_share_dec sh1); [ | contradiction].
replace (level f) with (level w). 
rewrite H7.
f_equal. apply proof_irr.
apply join_level in H1; intuition.
congruence.
(* noat case *)
generalize (resource_at_join _ _ _ l' H1); intro.
apply split_identity in H3; auto.
Qed.

Lemma general_slice_resource_identity:
  forall r, identity r -> general_slice_resource Share.bot r = r.
Proof.
 intros.
 destruct r; simpl in *; auto.
 assert (sh = retainer_part Share.bot).
   unfold retainer_part. rewrite Share.glb_bot.
   apply identity_NO in H.
   destruct H. inv H. auto. destruct H as [? [? ?]]. inv H.
   subst; f_equal. apply proof_irr.
   apply YES_not_identity in H. contradiction.
Qed.

Definition splittable {A} {JA: Join A}{PA: Perm_alg A}{agA: ageable A}{AgeA: Age_alg A} (Q: Share.t -> pred A) := 
  forall (sh1 sh2 sh3: Share.t) (rsh1: readable_share sh1) (rsh2: readable_share sh2),
    join sh1 sh2 sh3 ->
    Q sh1 * Q sh2 = Q sh3.

Lemma jam_noat_splittable:
  forall (S': address -> address -> Prop) S
           (Q: address -> spec)
     (PARAMETRIC: spec_parametric Q),
    forall l, splittable (fun sh => allp (@jam _ _ _ _ _ _ (S' l) (S l) (Q l sh) noat)).
Proof.
unfold splittable; intros.
apply pred_ext; intro w; simpl.
+  intros [w1 [w2 [? [? ?]]]].
  intro l'. spec H1 l'; spec H2 l'.
  unfold jam in *.
  revert H1 H2.
  if_tac.
  - intros.
    specialize (PARAMETRIC l l').
    destruct PARAMETRIC as [pp [ok ?]].
    rewrite H4 in H2. destruct H2 as [rsh1' [k1 [G1 H1']]]. 
    rewrite H4 in H3; destruct H3 as [rsh2' [k2 [G2 H2']]]. 
    rewrite H4.
    assert (rsh3 := join_readable1 H rsh1).
    exists rsh3.
    exists k2.
    generalize (resource_at_join _ _ _ l' H0); rewrite H1'; rewrite H2'; intro Hx.
    generalize H; clear H.
    inv Hx. 
    split; auto.
    simpl.
    replace (level w1) with (level w) by (apply join_level in H0; intuition).
    pose proof (join_eq H RJ). subst sh5.
    f_equal; auto with extensionality.
  - intros.
    generalize (resource_at_join _ _ _ l' H0); intro.
    apply H2 in H4. rewrite H4 in H3; auto.
+ intros.
  pose (f loc := if S l loc then general_slice_resource sh1 (w @ loc) else w@loc).
  assert (Vf: CompCert_AV.valid (res_option oo f)). {
     apply general_slice_resource_valid.
     intros. specialize (H0 l0). rewrite if_false in H0; auto.
  }
  destruct (make_rmap _ Vf (level w)) as [phi [Gf Hf]].
  Focus 1. {
    extensionality loc; unfold compose, f.
    specialize (PARAMETRIC l loc).
    destruct PARAMETRIC as [pp [ok Jf]].
    spec H0 loc.
    destruct (S l loc).
    rewrite Jf in H0.
    destruct H0 as [p3 [k3 [G0 H0]]].
    generalize (resource_at_approx w loc); intro.
    rewrite H0 in H1.
    inversion H1; clear H1; auto.
    rewrite H0.
    simpl.
    destruct (readable_share_dec sh1); auto.
    revert H0; case_eq (w @ loc); intros; try contradiction; simpl; f_equal; auto.
    apply resource_at_approx.
  } Unfocus.
  pose (g loc := if S l loc then general_slice_resource sh2 (w @ loc) else w@loc).
  assert (Vg: CompCert_AV.valid (res_option oo g)). {
     apply general_slice_resource_valid.
     intros. specialize (H0 l0). rewrite if_false in H0; auto.
  }
  destruct (make_rmap _ Vg (level w)) as [phi' [Gg Hg]].
  Focus 1. {
    extensionality loc; unfold compose, g.
    specialize (PARAMETRIC l loc).
    destruct PARAMETRIC as [pp [ok Jg]].
    spec H0 loc.
    destruct (S l loc).
    rewrite Jg in H0.
    destruct H0 as [p3 [k3 [G0 H0]]].
    generalize (resource_at_approx w loc); intro.
    rewrite H0 in H1.
    inversion H1; clear H1; auto.
    rewrite H0.
    simpl.
    destruct (readable_share_dec sh2); auto.
    revert H0; case_eq (w @ loc); intros; try contradiction; simpl; f_equal; auto.
    apply resource_at_approx.
  } Unfocus.
  unfold f,g in *; clear f g.
  rename phi into f; rename phi' into g.
  assert (join f g w). {
   apply resource_at_join2; auto.
   intro.
   rewrite Hf; rewrite Hg.
   clear - PARAMETRIC H H0 rsh1 rsh2.
   spec H0 loc.
   if_tac in H0.
   destruct (PARAMETRIC l loc) as [pp [ok ?]]; clear PARAMETRIC.
   rewrite H2 in H0.
   destruct H0 as [? [? [? ?]]].
   rewrite H3.
   generalize (preds_fmap (approx (level w)) (approx (level w)) pp); intro.
   simpl.
   destruct (readable_share_dec sh1); [ | contradiction].
   destruct (readable_share_dec sh2); [ | contradiction].
   constructor; auto.
   apply identity_unit_equiv in H0. apply H0.
  }
  econstructor; econstructor; split; [apply H1|].
  split.
  eapply jam_noat_splittable_aux; eauto.
  simpl; auto.
  rewrite Hf. extensionality loc. if_tac. auto.
  clear - H0 H2. specialize (H0 loc). rewrite if_false in H0 by auto.
  symmetry; apply general_slice_resource_identity; auto.
  rewrite Hg. extensionality loc. if_tac. auto.
  clear - H0 H2. specialize (H0 loc). rewrite if_false in H0 by auto.
  symmetry; apply general_slice_resource_identity; auto.
  apply join_comm in H.
  eapply jam_noat_splittable_aux.
  auto. auto. apply rsh1. eauto. 4: apply (join_comm H1).
  simpl; auto.
  rewrite Hg. extensionality loc. if_tac. auto.
  clear - H0 H2. specialize (H0 loc). rewrite if_false in H0 by auto.
  symmetry; apply general_slice_resource_identity; auto.
  rewrite Hf. extensionality loc. if_tac. auto.
  clear - H0 H2. specialize (H0 loc). rewrite if_false in H0 by auto.
  symmetry; apply general_slice_resource_identity; auto.
Qed.

Lemma address_mapsto_splittable:
      forall ch v l, splittable (fun sh => address_mapsto ch v sh l).
Proof.
intros.
unfold splittable.
intros ? ? ? rsh1 rsh2 H.
apply pred_ext; intros ? ?.
*
destruct H0 as [m1 [m2 [? [? ?]]]].
unfold address_mapsto in *.
destruct H1 as [bl1 [[LEN1 DECODE1] ?]]; destruct H2 as [bl2 [[LEN2 DECODE2] ?]].
exists bl1; split; auto.
simpl; auto.
intro loc; spec H1 loc; spec H2 loc.
unfold jam in *.
apply (resource_at_join _ _ _ loc) in H0.
hnf in H1, H2|-*.
if_tac.
hnf in H1,H2.
destruct H1; destruct H2.
hnf.
exists (join_readable1 H rsh1).
unfold yesat_raw in *.
hnf in H1,H2|-*.
rewrite preds_fmap_NoneP in *.
repeat proof_irr.
rewrite H1 in H0; rewrite H2 in H0; clear H1 H2.
unfold yesat_raw.
inv H0.
pose proof (join_eq H RJ); subst sh5; clear RJ rsh5 rsh6.
f_equal.
apply proof_irr.
apply H1 in H0. do 3 red in H2|-*. rewrite <- H0; auto.
*
rename a into m.
hnf in H0|-*.
destruct H0 as [bl [[? [? Halign]] ?]].
pose (rslice (rsh : Share.t) (loc: address) := if adr_range_dec l (size_chunk ch) loc then rsh else Share.bot).
assert (G1: forall l0 : AV.address,
  ~ adr_range l (size_chunk ch) l0 -> identity (m @ l0)). {
   intros. specialize (H2 l0). rewrite  jam_false in H2 by auto.
   apply H2.
 }
destruct (make_slice_rmap m _ (adr_range_dec l (size_chunk ch)) sh1 G1)
  as [m1 [? ?]].
destruct (make_slice_rmap m _ (adr_range_dec l (size_chunk ch)) sh2 G1)
  as [m2 [? ?]].
exists m1, m2.
split3.
+
apply resource_at_join2; try congruence.
intro loc.
rewrite H4,H6. clear H4 H6. clear H3 H5. clear m1 m2.
specialize (G1 loc). clear rslice.
specialize (H2 loc). hnf in H2.
if_tac.
destruct H2 as [rsh ?].
hnf in H2. rewrite H2. clear H2.
unfold general_slice_resource.
destruct (readable_share_dec sh1); [ | contradiction].
destruct (readable_share_dec sh2); [ | contradiction].
constructor. auto.
do 3 red in H2. apply identity_unit_equiv in H2. apply H2; auto.
+
exists bl; repeat split; auto.
intro loc; spec H2 loc; unfold jam in *;  hnf in H2|-*; if_tac; auto.
exists rsh1.
hnf.
rewrite H4.
rewrite if_true by auto.
unfold general_slice_resource.
destruct H2. hnf in H2.
rewrite H2.
destruct (readable_share_dec sh1); [ | contradiction].
f_equal. apply proof_irr.
do 3 red in H2|-*.
rewrite H4. rewrite if_false by auto. auto.
+
exists bl; repeat split; auto.
intro loc; spec H2 loc; unfold jam in *;  hnf in H2|-*; if_tac; auto.
exists rsh2.
hnf.
rewrite H6.
rewrite if_true by auto.
unfold general_slice_resource.
destruct H2. hnf in H2.
rewrite H2.
destruct (readable_share_dec sh2); [ | contradiction].
f_equal. apply proof_irr.
do 3 red in H2|-*.
rewrite H6. rewrite if_false by auto. auto.
Qed.

Lemma VALspec_splittable: forall l, splittable (fun sh => VALspec sh l).
Proof.
apply jam_noat_splittable.
apply VALspec_parametric.
Qed.

Lemma LKspec_splittable size: forall R l, splittable (fun sh => LKspec size R sh l).
Proof.
intro.
apply jam_noat_splittable.
apply LKspec_parametric.
Qed.

Lemma VALspec_range_splittable: forall n l, splittable (fun sh => VALspec_range n sh l).
Proof.
intro.
apply jam_noat_splittable.
apply VALspec_parametric.
Qed.

Definition share_oblivious (P: pred rmap) :=
  forall w w',
   (forall l, match w' @ l , w @ l with
                 | NO _ _, NO _ _ => True
                 | YES _ sh1 k1 p1 , YES _ sh2 k2 p2 => k1=k2 /\ p1=p2
                 | PURE k1 p1, PURE k2 p2 => k1=k2 /\ p1=p2
                 | _ , _ => False
                 end) ->
     P w' -> P w.

Lemma intersection_splittable:
    forall (S': address -> address -> Prop) S P Q, 
         spec_parametric P -> 
         (forall l, share_oblivious (Q l)) ->
    forall l, splittable (fun sh => allp (@jam _ _ _ _ _ _ (S' l) (S l) (P l sh) noat) && Q l).
Proof.
intros.
intro; intros.
generalize (jam_noat_splittable S' S _ H); intro.
rewrite <- (H2  _ _ _  _ rsh1 rsh2 H1).
apply pred_ext; intros w ?.
destruct H3 as [w1 [w2 [? [[? ?] [? ?]]]]].
split.
exists w1; exists w2; auto.
eapply H0; eauto.
intro.
generalize (resource_at_join _ _ _ l0 H3).
case_eq (w2 @ l0); case_eq (w @ l0); intros; auto; try solve [inv H10].
case_eq (w1 @ l0); intros.
rewrite H11 in H10; inv H10. 
rewrite H11 in H10; inv H10.
specialize (H4 l0).
specialize (H6 l0).
hnf in H4,H6.
if_tac in H4; auto.
specialize (H l l0).
destruct H as [pp [ok ?]].
rewrite H in H4; rewrite H in H6.
destruct H4 as [? [? [? ?]]].
destruct H6 as [? [? [? ?]]].
inversion2 H11 H12.
inversion2 H9 H13.
do 3 red in H4. rewrite H11 in H4.
contradiction (YES_not_identity _ _ _ _ H4).
rewrite H11 in H10; inv H10.
destruct (w1 @ l0); inv H10; auto.
inv H10; auto.
destruct H3 as [[w1 [w2 [? [? ?]]]] ?].
exists w1; exists w2.
split; auto.
split; split; auto.
apply (H0 l w1 w).
intro l0; generalize (resource_at_join _ _ _ l0 H3).
case_eq (w @ l0); case_eq (w1 @ l0); intros; auto; try solve [inv H9].
case_eq (w2 @ l0); intros.
rewrite H10 in H9; inv H9. 
rewrite H10 in H9; inv H9.
specialize (H l l0).
destruct H as [pp [ok ?]].
specialize (H4 l0).
specialize (H5 l0).
hnf in H4,H5.
if_tac in H4.
rewrite H in H4,H5.
destruct H4 as [? [? [? ?]]].
destruct H5 as [? [? [? ?]]].
congruence.
do 3 red in H5. rewrite H10 in H5. 
contradiction (YES_not_identity _ _ _ _ H5).
rewrite H10 in H9; inv H9.
inv H9; auto.
inv H9; auto.
auto.
apply (H0 l w2 w ).
intro l0; generalize (resource_at_join _ _ _ l0 H3).
case_eq (w @ l0); case_eq (w2 @ l0); intros; auto; try solve [inv H9].
inv H9.
specialize (H l l0).
destruct H as [pp [ok ?]].
specialize (H4 l0).
specialize (H5 l0).
hnf in H4,H5.
if_tac in H4.
rewrite H in H4,H5.
destruct H4 as [? [? [? ?]]].
destruct H5 as [? [? [? ?]]].
congruence.
do 3 red in H4. rewrite <- H11 in H4.
contradiction (YES_not_identity _ _ _ _ H4).
inv H9; auto. inv H9; auto.
auto.
Qed.

Lemma not_readable_share_retainer_part_eq:
  forall sh, ~ readable_share sh -> retainer_part sh = sh.
   intros.
    apply not_not_share_identity in H.
    unfold retainer_part.
    rewrite (comp_parts comp_Lsh_Rsh sh) at 2.
    apply identity_share_bot in H; rewrite H.
    rewrite Share.lub_bot. auto.
Qed.

Lemma general_slice_resource_resource_share: forall r sh sh',
  resource_share r = Some sh ->
  join_sub sh' sh ->
  resource_share (general_slice_resource sh' r) = Some sh'.
Proof.
  intros.
  destruct r; inv H; unfold general_slice_resource; simpl.
  + f_equal.
    assert (~readable_share sh'). contradict n. destruct H0.
    eapply join_readable1; eauto.
    apply not_readable_share_retainer_part_eq; auto.
  + destruct (readable_share_dec sh'); simpl; auto.
Qed.

Lemma general_slice_resource_nonlock: forall r sh sh',
  resource_share r = Some sh ->
  join_sub sh' sh ->
  nonlock r ->
  nonlock (general_slice_resource sh' r).
Proof.
  intros.
  destruct r; inv H; unfold general_slice_resource; simpl; auto.
  destruct (readable_share_dec sh'); simpl; auto.
Qed.

Lemma NO_ext: forall sh1 sh2 rsh1 rsh2, sh1=sh2 -> NO sh1 rsh1 = NO sh2 rsh2.
Proof. intros. subst sh1. f_equal. apply proof_irr. Qed.

Lemma join_sub_is_general_slice_resource: forall r r' sh',
  join_sub r' r ->
  resource_share r' = Some sh' ->
  r' = general_slice_resource sh' r.
Proof.
  intros.
  destruct H as [r'' ?].
  destruct r, r'; inv H; inv H0; simpl.
  + f_equal.
    clear - n0.
    apply NO_ext. symmetry.
    rewrite not_readable_share_retainer_part_eq; auto.
  + destruct (readable_share_dec sh'); [ contradiction |].
    apply NO_ext; auto.
  + destruct (readable_share_dec sh'); [| contradiction ].
    f_equal. apply proof_irr.
  + destruct (readable_share_dec sh'); [| contradiction ].
    f_equal. apply proof_irr.
Qed.

Lemma general_slice_resource_share_join: forall sh1 sh2 sh r,
  join sh1 sh2 sh ->
  resource_share r = Some sh ->
  join (general_slice_resource sh1 r) (general_slice_resource sh2 r) r.
Proof.
  intros.
  destruct r; simpl in *.
*
  constructor. inv H0.
  assert (~readable_share sh1) by (contradict n; eapply join_readable1; eauto).
  assert (~readable_share sh2) by (contradict n; eapply join_readable2; eauto).
  rewrite !(not_readable_share_retainer_part_eq); auto.
*
  inv H0.
  destruct (readable_share_dec sh1), (readable_share_dec sh2);
  try (constructor; auto).
  contradiction (join_unreadable_shares H n n0).
*
  constructor.
Qed.

Definition resource_share_split (p q r: address -> pred rmap): Prop :=
  exists p' q' r' p_sh q_sh r_sh,
    is_resource_pred p p' /\
    is_resource_pred q q' /\
    is_resource_pred r r' /\
    join q_sh r_sh p_sh /\
    (forall res l n, p' res l n ->
      resource_share res = Some p_sh /\
      q' (general_slice_resource q_sh res) l n /\
      r' (general_slice_resource r_sh res) l n) /\
    (forall p_res q_res r_res l n,
      join q_res r_res p_res ->
      q' q_res l n ->
      r' r_res l n ->
      p' p_res l n).

(* We should use this lemma to prove all share_join lemmas, also all splittable lemmas. *)
Lemma allp_jam_share_split: forall (P: address -> Prop) (p q r: address -> pred rmap)
  (P_DEC: forall l, {P l} + {~ P l}),
  resource_share_split p q r ->
  allp (jam P_DEC p noat) = allp (jam P_DEC q noat) * allp (jam P_DEC r noat).
Proof.
  intros.
  destruct H as [p' [q' [r' [p_sh [q_sh [r_sh [? [? [? [? [? ?]]]]]]]]]]].
  apply pred_ext; intros w; simpl; intros.
  + destruct (make_slice_rmap w P P_DEC q_sh) as [w1 [? ?]].
    Focus 1. {
      intros; specialize (H5 l).
      rewrite if_false in H5 by auto.
      auto.
    } Unfocus.
    destruct (make_slice_rmap w P P_DEC r_sh) as [w2 [? ?]].
    Focus 1. {
      intros; specialize (H5 l).
      rewrite if_false in H5 by auto.
      auto.
    } Unfocus.
    exists w1, w2.
    split3.
    - apply resource_at_join2; try congruence.
      intro l.
      rewrite H7, H9; clear H7 H9.
      specialize (H5 l); destruct (P_DEC l).
      * eapply general_slice_resource_share_join; eauto.
        rewrite H in H5.
        apply H3 in H5.
        tauto.
      * apply identity_unit_equiv in H5.
        exact H5.
    - intros l.
      rewrite H0, H7, H6.
      specialize (H5 l).
      rewrite H in H5.
      if_tac.
      * apply H3 in H5.
        tauto.
      * auto.
    - intros l.
      rewrite H1, H9, H8.
      specialize (H5 l).
      rewrite H in H5.
      if_tac.
      * apply H3 in H5.
        tauto.
      * auto.
  + destruct H5 as [y [z [? [? ?]]]].
    specialize (H6 b); specialize (H7 b).
    if_tac.
    - rewrite H; rewrite H0 in H6; rewrite H1 in H7.
      destruct (join_level _ _ _ H5).
      rewrite H9 in H6; rewrite H10 in H7.
      eapply H4; eauto.
      apply resource_at_join; auto.
    - apply resource_at_join with (loc := b) in H5.
      apply H6 in H5; rewrite <- H5; auto.
Qed.

Lemma address_mapsto_share_join:
 forall (sh1 sh2 sh : share) ch v a,
   join sh1 sh2 sh ->
   readable_share sh1 -> readable_share sh2 ->
   address_mapsto ch v sh1 a * address_mapsto ch v sh2 a 
    = address_mapsto ch v sh a.
Proof.
  intros ? ? ? ? ? ? H rsh1 rsh2.
(*  rename H1 into NON_UNIT1, H2 into NON_UNIT2.
  assert (NON_UNIT: nonunit sh) by (eapply nonunit_join; eauto; auto with typeclass_instances).
*)
  symmetry.
  unfold address_mapsto.
  transitivity
   (EX  bl : list memval,
    !!(length bl = size_chunk_nat ch /\
       decode_val ch bl = v /\ (align_chunk ch | snd a)) &&
   (allp
      (jam (adr_range_dec a (size_chunk ch))
         (fun loc : address =>
          yesat NoneP (VAL (nth (nat_of_Z (snd loc - snd a)) bl Undef)) sh1
            loc) noat) *
    allp
      (jam (adr_range_dec a (size_chunk ch))
         (fun loc : address =>
          yesat NoneP (VAL (nth (nat_of_Z (snd loc - snd a)) bl Undef)) sh2
            loc) noat))).
  + pose proof log_normalize.exp_congr (pred rmap) _ (list memval).
    simpl in H0.
    apply H0; clear H0.
    intros b.
    f_equal.
    apply allp_jam_share_split.
    do 3 eexists.
    exists sh, sh1, sh2.
    split; [| split; [| split; [| split; [| split]]]].
    - apply is_resource_pred_YES_VAL'.
    - apply is_resource_pred_YES_VAL'.
    - apply is_resource_pred_YES_VAL'.
    - auto.
    - simpl; intros.
      destruct H0.
      split; [subst; auto |].
      split.
      * exists rsh1.
        subst; simpl.
        destruct (readable_share_dec sh1); [| contradiction].
        f_equal.
        auto with extensionality.
      * exists rsh2.
        subst; simpl.
        destruct (readable_share_dec sh); [| contradiction].
        destruct (readable_share_dec sh2); [| contradiction].
        f_equal.
        auto with extensionality. 
    - simpl; intros.
      destruct H1,H2. repeat proof_irr.
      exists (join_readable1 H rsh1).
      subst.
      inv H0.
      apply YES_ext.
      eapply join_eq; eauto.
  + apply pred_ext.
    - apply exp_left; intro bl.
      apply prop_andp_left; intro.
      rewrite exp_sepcon1.
      apply (exp_right bl).
      rewrite exp_sepcon2.
      apply (exp_right bl).
      rewrite sepcon_andp_prop1.
      apply andp_right; [intros w _; simpl; auto |].
      rewrite sepcon_andp_prop.
      apply andp_right; [intros w _; simpl; auto |].
      auto.
    - rewrite exp_sepcon1.
      apply exp_left; intro bl1.
      rewrite exp_sepcon2.
      apply exp_left; intro bl2.
      rewrite sepcon_andp_prop1.
      apply prop_andp_left; intro.
      rewrite sepcon_andp_prop.
      apply prop_andp_left; intro.
      apply (exp_right bl1).
      apply andp_right; [intros w _; simpl; auto |].
      intros w ?.
      destruct H2 as [w1 [w2 [? [? ?]]]].
      exists w1, w2.
      split; [| split]; auto.
      intro l; specialize (H3 l); specialize (H4 l).
      simpl in H3, H4 |- *.
      if_tac; auto.
      destruct H3, H4. exists rsh2.
      apply resource_at_join with (loc := l) in H2.
      rewrite H3, H4 in H2; inv H2.
      rewrite H11. rewrite H4. apply YES_ext. auto.
Qed.

Lemma nonlock_permission_bytes_address_mapsto_join:
 forall (sh1 sh2 sh : share) ch v a,
   join sh1 sh2 sh ->
   readable_share sh2 ->
   nonlock_permission_bytes sh1 a (Memdata.size_chunk ch)
     * address_mapsto ch v sh2 a 
    = address_mapsto ch v sh a.
Proof.
intros. rename H0 into rsh2.
unfold nonlock_permission_bytes, address_mapsto.
rewrite exp_sepcon2.
f_equal. extensionality bl.
rewrite sepcon_andp_prop.
f_equal.
apply pred_ext.
*
 intros z [x [y [? [? ?]]]] b.
 specialize (H1 b); specialize (H2 b).
 pose proof (resource_at_join _ _ _ b H0).
 hnf in H1,H2|-*.
 if_tac.
 +
  destruct H2 as [p ?].
  hnf in H2. rewrite H2 in *. clear H2.
  destruct H1 as [H1 H1'].
  hnf in H1, H1'. unfold resource_share in H1.
  assert (p8 := join_readable2 H p).
  exists p8.
  destruct (x @ b); inv H1.
  -
    inv H3.
    pose proof (join_eq H RJ); subst sh4. clear RJ.
    hnf. rewrite <- H8; clear H8.
    f_equal. apply proof_irr.
  -
   clear H1'.  inv H3. 
   hnf. rewrite <- H10. clear H10. simpl.
    pose proof (join_eq H RJ); subst sh4. clear RJ.
   f_equal. apply proof_irr.
 +
   do 3 red in H1,H2|-*. 
   apply join_unit1_e in H3; auto.
   rewrite <- H3; auto.
*
  assert (rsh := join_readable2 H rsh2).
  intros w ?.
  hnf in H0.
  destruct (make_slice_rmap w _ (adr_range_dec a (size_chunk ch)) sh1)
   as [w1 [? ?]].
  intros. specialize (H0 l). simpl in H0. rewrite if_false in H0; auto. 
  destruct (make_slice_rmap w _ (adr_range_dec a (size_chunk ch)) sh2)
   as [w2 [? ?]].
  intros. specialize (H0 l). simpl in H0. rewrite if_false in H0; auto. 
  exists w1, w2.
  split3.
 +
   eapply resource_at_join2; try omega.
   change compcert_rmaps.R.resource_at with resource_at in *.
  intro . rewrite H2,H4. clear dependent w1. clear dependent w2.
  specialize (H0 loc). hnf in H0.  
  if_tac in H0. destruct H0 as [rsh' H0]. proof_irr. rewrite H0.
  unfold general_slice_resource.
  destruct (readable_share_dec sh2); [ | contradiction]. proof_irr.
  destruct (readable_share_dec sh1).
  constructor; auto.
  constructor; auto.
  do 3 red in H0. 
  apply identity_unit_equiv in H0. apply H0.
 +
   intro loc; hnf. simpl. rewrite H2.
  clear dependent w1. clear dependent w2.
  specialize (H0 loc). hnf in H0.  
  if_tac in H0.
  -
   destruct H0. proof_irr. rewrite H0.
   unfold general_slice_resource.
   destruct (readable_share_dec sh1).
   simpl. split; auto.
   split; simpl; auto.
  -
   apply H0.
 +
   intro loc; hnf. simpl. rewrite H4.  simpl.
  clear dependent w1. clear dependent w2.
  specialize (H0 loc). hnf in H0.  
  if_tac in H0.
  -
   exists rsh2.
   destruct H0 as [p0 H0]. proof_irr. simpl in H0.
   rewrite H0. clear H0. simpl.
   destruct (readable_share_dec sh2); [ | contradiction]. proof_irr.
   reflexivity.
 - apply H0.
Qed.

Lemma VALspec_range_share_join:
 forall sh1 sh2 sh n p,
  readable_share sh1 ->
  readable_share sh2 ->
  join sh1 sh2 sh ->
  VALspec_range n sh1 p *
  VALspec_range n sh2 p =
  VALspec_range n sh p.
Proof.
  intros.
  symmetry.
  apply allp_jam_share_split.
  do 3 eexists.
  exists sh, sh1, sh2. 
  split; [| split; [| split; [| split; [| split]]]].
  + apply is_resource_pred_YES_VAL.
  + apply is_resource_pred_YES_VAL.
  + apply is_resource_pred_YES_VAL.
  + auto.
  + simpl; intros.
    destruct H2 as [x [rsh ?]].
    split; [subst; simpl; auto |].
    split; [exists x, H | exists x, H0].
    - subst. simpl.
      destruct (readable_share_dec sh1); [ | contradiction].
      f_equal. apply proof_irr.
    - subst. simpl.
      destruct (readable_share_dec sh2); [ | contradiction].
      f_equal. apply proof_irr.
  + simpl; intros.
    destruct H3 as [? [? ?]], H4 as [? [? ?]].
    exists x. exists (join_readable1 H1 H).
    subst.
    inv H2. apply YES_ext. eapply join_eq; eauto.
Qed.

Lemma nonlock_permission_bytes_share_join:
 forall sh1 sh2 sh a n,
  join sh1 sh2 sh ->
  nonlock_permission_bytes sh1 a n *
  nonlock_permission_bytes sh2 a n =
  nonlock_permission_bytes sh a n.
Proof.
  intros.
  symmetry.
  apply allp_jam_share_split.
  do 3 eexists.
  exists sh, sh1, sh2.
  split; [| split; [| split; [| split; [| split]]]].
  + apply is_resource_pred_nonlock_shareat.
  + apply is_resource_pred_nonlock_shareat.
  + apply is_resource_pred_nonlock_shareat.
  + auto.
  + simpl; intros.
    destruct H0.
    split; [auto |].
    split; split.
    - eapply general_slice_resource_resource_share; [eauto | eexists; eauto ].
    - eapply general_slice_resource_nonlock; [eauto | eexists; eauto | auto].
    - eapply general_slice_resource_resource_share; [eauto | eexists; eapply join_comm; eauto].
    - eapply general_slice_resource_nonlock; [eauto | eexists; eapply join_comm; eauto | auto].
  + simpl; intros.
    destruct H1, H2.
    split.
    - eapply (resource_share_join q_res r_res); eauto.
    - eapply (nonlock_join q_res r_res); eauto.
Qed.

Lemma nonlock_permission_bytes_VALspec_range_join:
 forall sh1 sh2 (rsh2: readable_share sh2) sh p n,
  join sh1 sh2 sh ->
  nonlock_permission_bytes sh1 p n *
  VALspec_range n sh2 p =
  VALspec_range n sh p.
Proof.
  intros.
  symmetry.
  apply allp_jam_share_split.
  do 3 eexists.
  exists sh, sh1, sh2.
  split; [| split; [| split; [| split; [| split]]]].
  + apply is_resource_pred_YES_VAL.
  + apply is_resource_pred_nonlock_shareat.
  + apply is_resource_pred_YES_VAL.
  + auto.
  + simpl; intros.
    destruct H0 as [? [? ?]]; subst; split; [| split; [split |]].
    - simpl; auto.
    - simpl.
      destruct (readable_share_dec sh1); reflexivity.
    - simpl.
      destruct (readable_share_dec sh1); simpl; auto.
    - simpl.
      exists x, rsh2.
      destruct (readable_share_dec sh2); [ | contradiction].
      apply YES_ext. auto.
  + simpl; intros.
    destruct H2 as [? [? ?]].
    subst. proof_irr.
    exists x, (join_readable2 H rsh2).
    destruct H1.
    destruct q_res; simpl in H1.
    - inversion H0; subst. inv H1.
      apply YES_ext.
      eapply join_eq; eauto.
    - inv H1. inv H0. apply YES_ext. eapply join_eq; eauto.
    - inv H1.
Qed.

Lemma is_resource_pred_YES_LK lock_size l (R: pred rmap) sh:
  is_resource_pred
    (fun l' => jam (eq_dec l) (yesat (SomeP rmaps.Mpred (fun _ => R)) (LK lock_size) sh) (CTat l sh) l')
    (fun r l0 n => (if eq_dec l l0 then exists p, r = YES sh p (LK lock_size)
        (SomeP rmaps.Mpred (fun _ => approx n R))
       else exists p, r = YES sh p (CT (snd l0 - snd l)) NoneP)).
Proof. hnf; intros. reflexivity. Qed.

Lemma LKspec_share_join lock_size:
 forall sh1 sh2 (rsh1: readable_share sh1) (rsh2: readable_share sh2) sh R p,
  join sh1 sh2 sh ->
  LKspec lock_size R sh1 p *
  LKspec lock_size R sh2 p =
  LKspec lock_size R sh p.
Proof.
  intros.
  symmetry.
  unfold LKspec.
  apply allp_jam_share_split.
  do 3 eexists.
  exists sh, sh1, sh2.
  split; [| split; [| split; [| split; [| split]]]].
  + apply is_resource_pred_YES_LK.
  + apply is_resource_pred_YES_LK.
  + apply is_resource_pred_YES_LK.
  + auto.
  + simpl; intros.
    destruct (eq_dec p l); subst; destruct H0; split; try solve [subst; simpl; auto];
    split.
    - exists rsh1. subst. simpl.
      destruct (readable_share_dec sh1); [ | contradiction].
      apply YES_ext; auto.
    - exists rsh2. subst. simpl.
      destruct (readable_share_dec sh2); [ | contradiction].
      apply YES_ext; auto.
    - exists rsh1. subst. simpl.
      destruct (readable_share_dec sh1); [ | contradiction].
      apply YES_ext; auto.
    - exists rsh2. subst. simpl.
      destruct (readable_share_dec sh2); [ | contradiction].
      apply YES_ext; auto.
  + simpl; intros.
    destruct (eq_dec p l); subst; destruct H1, H2. repeat proof_irr.
    - exists (join_readable1 H rsh1). subst. inv H0. apply YES_ext.
      eapply join_eq; eauto.
    - exists (join_readable1 H rsh1). subst. inv H0. apply YES_ext.
      eapply join_eq; eauto.
Qed.


