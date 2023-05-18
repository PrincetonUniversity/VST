Require Import VST.veric.base.
Require Import VST.veric.shares.
Require Import VST.veric.share_alg.
Require Import VST.veric.res_predicates.
Require Import VST.zlist.sublist.

Definition cleave (sh: share) :=
  (Share.lub (fst (Share.split (Share.glb Share.Lsh sh))) (fst (Share.split (Share.glb Share.Rsh sh))),
   Share.lub (snd (Share.split (Share.glb Share.Lsh sh))) (snd (Share.split (Share.glb Share.Rsh sh)))).

Lemma cleave_join:
 forall sh: share, sepalg.join (fst (cleave sh)) (snd (cleave sh)) sh.
Proof.
intros.
unfold cleave.
destruct (Share.split (Share.glb Share.Lsh sh)) as [a b] eqn:?H.
apply split_join in H.
destruct (Share.split (Share.glb Share.Rsh sh)) as [e f] eqn:?H.
apply split_join in H0.
destruct (Share.split sh) as [c g] eqn:?H.
apply split_join in H1.
simpl.
destruct H1.
subst sh.
destruct H.
destruct H0.
split.
*
rewrite !Share.distrib1.
rewrite !(Share.glb_commute (Share.lub _ _)).
rewrite !Share.distrib1.
rewrite (Share.glb_commute b a) (Share.glb_commute f e).
rewrite H H0.
rewrite (Share.lub_commute Share.bot).
rewrite !Share.lub_bot.
rewrite Share.distrib2.
rewrite !(Share.lub_commute (Share.glb _ _)).
rewrite !Share.distrib2.
rewrite (Share.lub_commute f e) H3 H2.
rewrite (Share.glb_commute (Share.lub _ _)).
rewrite (Share.glb_assoc Share.Lsh).
rewrite !(Share.glb_assoc Share.Rsh).
rewrite (Share.glb_commute _ (Share.glb Share.Lsh _)).
rewrite (Share.glb_assoc Share.Lsh).
rewrite <- (Share.glb_assoc Share.Rsh).
rewrite (Share.glb_commute Share.Rsh).
rewrite glb_Lsh_Rsh.
rewrite Share.glb_commute. apply Share.glb_bot.
*
rewrite Share.lub_assoc.
rewrite (Share.lub_commute e).
rewrite (Share.lub_assoc b).
rewrite <- Share.lub_assoc.
rewrite H2.
rewrite (Share.lub_commute f e) H3.
clear.
do 2 rewrite (Share.glb_commute _ (Share.lub _ _)).
rewrite <- Share.distrib1.
rewrite lub_Lsh_Rsh.
apply Share.glb_top.
Qed.

Lemma cleave_readable1:
 forall sh, readable_share sh -> readable_share (fst (cleave sh)).
Proof.
intros.
hnf in H|-*. contradict H.
apply identity_share_bot in H.
unfold cleave in H.
simpl in H.
rewrite Share.distrib1 in H.
apply lub_bot_e in H. destruct H as [_ ?].
destruct (Share.split (Share.glb Share.Rsh sh)) as [c d] eqn:H1.
apply (split_nontrivial' _ _ _ H1).
left.
apply split_join in H1.
simpl in *.
destruct (join_parts1 comp_Rsh_Lsh H1).
rewrite <- H0, H.
apply bot_identity.
Qed.

Lemma cleave_readable2:
 forall sh, readable_share sh -> readable_share (snd (cleave sh)).
Proof.
intros.
hnf in H|-*. contradict H.
apply identity_share_bot in H.
unfold cleave in H.
simpl in H.
rewrite Share.distrib1 in H.
apply lub_bot_e in H. destruct H as [_ ?].
destruct (Share.split (Share.glb Share.Rsh sh)) as [c d] eqn:H1.
apply (split_nontrivial' _ _ _ H1).
simpl in *.
right.
apply split_join in H1.
apply sepalg.join_comm in H1.
simpl in *.
destruct (join_parts1 comp_Rsh_Lsh H1).
rewrite <- H0, H.
apply bot_identity.
Qed.

(*Lemma rshare_sh_readable:
 forall r, readable_share (rshare_sh r).
Proof.
destruct r; simpl.
destruct p;
auto.
Qed.*)

(*Lemma cleave_nonreadable1:
  forall sh, ~readable_share sh -> ~ readable_share (fst (cleave sh)).
Proof.
intros.
contradict H.
do 3 red in H|-*.
contradict H.
unfold cleave. simpl.
apply identity_share_bot in H.
rewrite H. clear H.
destruct (Share.split Share.bot) as [a b] eqn:?H.
apply split_join in H.
simpl.
apply sepalg.split_identity in H; [ | apply bot_identity].
apply identity_share_bot in H. subst.
rewrite Share.lub_bot.
clear.
destruct (Share.split (Share.glb Share.Lsh sh)) as [a b] eqn:H.
apply split_join in H.
simpl.
replace (Share.glb Share.Rsh a) with Share.bot.
apply bot_identity.
symmetry.
destruct H.
apply (f_equal (Share.glb Share.Rsh)) in H0.
rewrite <- Share.glb_assoc in H0.
rewrite (Share.glb_commute _ Share.Lsh) in H0.
rewrite glb_Lsh_Rsh in H0.
rewrite (Share.glb_commute Share.bot) in H0.
rewrite Share.glb_bot in H0.
rewrite Share.distrib1 in H0.
apply lub_bot_e in H0. destruct H0 as [? _].
auto.
Qed.

Lemma cleave_nonreadable2:
  forall sh, ~readable_share sh -> ~ readable_share (snd (cleave sh)).
Proof.
intros.
contradict H.
do 3 red in H|-*.
contradict H.
unfold cleave. simpl.
apply identity_share_bot in H.
rewrite H. clear H.
destruct (Share.split Share.bot) as [a b] eqn:?H.
apply split_join in H.
simpl.
apply join_comm in H.
apply split_identity in H; [ | apply bot_identity].
apply identity_share_bot in H. subst.
rewrite Share.lub_bot.
clear.
destruct (Share.split (Share.glb Share.Lsh sh)) as [a b] eqn:H.
apply split_join in H.
simpl.
replace (Share.glb Share.Rsh b) with Share.bot.
apply bot_identity.
symmetry.
destruct H.
apply (f_equal (Share.glb Share.Rsh)) in H0.
rewrite <- Share.glb_assoc in H0.
rewrite (Share.glb_commute _ Share.Lsh) in H0.
rewrite glb_Lsh_Rsh in H0.
rewrite (Share.glb_commute Share.bot) in H0.
rewrite Share.glb_bot in H0.
rewrite Share.lub_commute in H0.
rewrite Share.distrib1 in H0.
apply lub_bot_e in H0. destruct H0 as [? _].
auto.
Qed.*)

(*Definition split_resource r :=
  match r with YES sh rsh k pp =>
               (YES (fst (cleave sh)) (cleave_readable1 _ rsh) k pp ,
                YES (snd (cleave sh)) (cleave_readable2 _ rsh) k pp)
             | PURE k pp => (PURE k pp, PURE k pp)
             | NO sh nsh => (NO (fst (cleave sh)) (cleave_nonreadable1 _ nsh),
                             NO (snd (cleave sh)) (cleave_nonreadable2 _ nsh))
  end.


Lemma glb_cleave_lemma1: forall sh0 sh,
  Share.glb Share.Rsh sh0 = Share.glb Share.Rsh sh ->
 Share.glb Share.Rsh (fst (cleave sh0)) =
 Share.glb Share.Rsh (fst (cleave sh)).
Proof.
intros.
unfold cleave; simpl.
destruct (Share.split (Share.glb Share.Lsh sh0)) as [a0 b0]  eqn:H0.
apply split_join in H0.
destruct (Share.split (Share.glb Share.Lsh sh)) as [a b]  eqn:H1.
apply split_join in H1.
destruct (Share.split (Share.glb Share.Rsh sh0)) as [c0 d0]  eqn:H2.
rewrite H in H2. rewrite H2.
simpl.
apply split_join in H2.
rewrite !Share.distrib1.
apply (join_parts1 comp_Lsh_Rsh) in H1.
destruct H1 as [_ ?]. rewrite H1.
apply (join_parts1 comp_Lsh_Rsh) in H0.
destruct H0 as [_ ?]. rewrite H0.
auto.
Qed.

Lemma glb_cleave_lemma2: forall sh0 sh,
  Share.glb Share.Rsh sh0 = Share.glb Share.Rsh sh ->
 Share.glb Share.Rsh (snd (cleave sh0)) =
 Share.glb Share.Rsh (snd (cleave sh)).
Proof.
intros.
unfold cleave; simpl.
destruct (Share.split (Share.glb Share.Lsh sh0)) as [a0 b0]  eqn:H0.
apply split_join in H0.
destruct (Share.split (Share.glb Share.Lsh sh)) as [a b]  eqn:H1.
apply split_join in H1.
apply join_comm in H0.
apply join_comm in H1.
destruct (Share.split (Share.glb Share.Rsh sh0)) as [c0 d0]  eqn:H2.
rewrite H in H2. rewrite H2.
simpl.
apply split_join in H2.
rewrite !Share.distrib1.
apply (join_parts1 comp_Lsh_Rsh) in H1.
destruct H1 as [_ ?]. rewrite H1.
apply (join_parts1 comp_Lsh_Rsh) in H0.
destruct H0 as [_ ?]. rewrite H0.
auto.
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

(*
Definition split_rmap (m: rmap) : rmap * rmap :=
 (proj1_sig (make_rmap _ (split_rmap_valid1 m) (level m) (split_rmap_ok1 m)),
  proj1_sig (make_rmap _ (split_rmap_valid2 m) (level m) (split_rmap_ok2 m))).
*)

Lemma split_resource_join:
  forall r, join (fst (split_resource r)) (snd (split_resource r)) r.
Proof.
intro.
destruct r; simpl; constructor; auto; try (apply cleave_join; apply surjective_pairing).
Qed.

(*Lemma split_rmap_join:
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
Qed.*)

Definition split_shareval (shv: Share.t * val) : ((Share.t * val) * (Share.t * val)) :=
  ((fst (Share.split (fst shv)), snd shv), (snd (Share.split (fst shv)), snd shv)).

Definition slice_resource (sh: share) (r: resource) : resource :=
  match r with
   | NO _ _ => NO (retainer_part sh) (retainer_part_nonreadable sh)
   | YES _ _ k pp =>
    match readable_share_dec sh with
    | left r1 => YES sh r1 k pp
    | right n => NO sh n
    end
   | PURE k pp => PURE k pp
  end.


Lemma make_slice_rmap: forall w (P: address -> Prop) (P_DEC: forall l, {P l} + {~ P l}) sh,
  (forall l : AV.address, ~ P l -> identity (w @ l)) ->
  {w' | level w' = level w /\ resource_at w' =
       (fun l => if P_DEC l then slice_resource sh (w @ l) else w @ l) /\
       ghost_of w' = ghost_of w}.
Proof.
  intros.
  pose (f l := if P_DEC l then slice_resource sh (w @ l) else w @ l).
  apply (make_rmap _ (ghost_of w) (level w)).
  extensionality loc; unfold compose, f.
  destruct (P_DEC loc).
  + pose proof resource_at_approx w loc.
    destruct (w @ loc); auto.
    simpl.
    destruct (readable_share_dec sh); auto.
    inversion H0.
    simpl; f_equal; f_equal; auto.
  + apply resource_at_approx.
  + apply ghost_of_approx.
Qed.

Lemma make_core_slice_rmap: forall w (P: address -> Prop) (P_DEC: forall l, {P l} + {~ P l}) sh,
  (forall l : AV.address, ~ P l -> identity (w @ l)) ->
  {w' | level w' = level w /\ resource_at w' =
       (fun l => if P_DEC l then slice_resource sh (w @ l) else w @ l) /\
       ghost_of w' = core (ghost_of w)}.
Proof.
  intros.
  pose (f l := if P_DEC l then slice_resource sh (w @ l) else w @ l).
  apply (make_rmap _ (core (ghost_of w)) (level w)).
  extensionality loc; unfold compose, f.
  destruct (P_DEC loc).
  + pose proof resource_at_approx w loc.
    destruct (w @ loc); auto.
    simpl.
    destruct (readable_share_dec sh); auto.
    inversion H0.
    simpl; f_equal; f_equal; auto.
  + apply resource_at_approx.
  + apply ghost_fmap_core.
Qed.

Lemma jam_noat_splittable_aux:
  forall S' S Q (PARAMETRIC: spec_parametric Q)
           (sh1 sh2 sh3: share)
           (rsh1: readable_share sh1) (rsh2: readable_share sh2)
           l
           (H: join sh1 sh2 sh3)
           w (H0: allp (@jam _ _ _ _ _ _ _ _ _ (S' l) (S l) (Q l sh3) noat) w)
           f (Hf: resource_at f = fun loc => slice_resource (if S l loc then sh1 else Share.bot) (w @ loc))
           g (Hg: resource_at g = fun loc => slice_resource (if S l loc then sh2 else Share.bot) (w @ loc))
           (H1: join f g w),
           allp (jam (S l) (Q l sh1) noat) f.
Proof.
intros.
(*assert (rsh3: readable_share sh3) by (eapply readable_share_join ; eauto). *)
intro l'.
specialize ( H0 l').
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

Lemma slice_resource_identity:
  forall r, identity r -> slice_resource Share.bot r = r.
Proof.
 intros.
 destruct r; simpl in *; auto.
 assert (sh = retainer_part Share.bot).
   unfold retainer_part. rewrite Share.glb_bot.
   apply identity_NO in H.
   destruct H as [|]. inv H. auto. destruct H as [? [? ?]]. inv H.
   subst; f_equal. apply proof_irr.
   apply YES_not_identity in H. contradiction.
Qed.

Definition splittable {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A} (Q: Share.t -> pred A) :=
  forall (sh1 sh2 sh3: Share.t) (rsh1: readable_share sh1) (rsh2: readable_share sh2),
    join sh1 sh2 sh3 ->
    Q sh1 * Q sh2 = Q sh3.

(*Lemma jam_noat_splittable:
  forall (S': address -> address -> Prop) S
           (Q: address -> spec)
     (PARAMETRIC: spec_parametric Q),
    forall l, splittable (fun sh => allp (@jam _ _ _ _ _ _ _ _ (S' l) (S l) (Q l sh) noat)).
Proof.
unfold splittable; intros.
apply pred_ext; intro w; simpl.
+  intros [w1 [w2 [? [? ?]]]].
  intro l'. specialize ( H1 l'); specialize ( H2 l').
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
  pose (f loc := if S l loc then slice_resource sh1 (w @ loc) else w@loc).
  assert (Vf: CompCert_AV.valid (res_option oo f)). {
     apply slice_resource_valid.
     intros. specialize (H0 l0). rewrite if_false in H0; auto.
  }
  destruct (make_rmap _ Vf (level w)) as [phi [Gf Hf]].
  {
    extensionality loc; unfold compose, f.
    specialize (PARAMETRIC l loc).
    destruct PARAMETRIC as [pp [ok Jf]].
    specialize ( H0 loc).
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
  }
  pose (g loc := if S l loc then slice_resource sh2 (w @ loc) else w@loc).
  assert (Vg: CompCert_AV.valid (res_option oo g)). {
     apply slice_resource_valid.
     intros. specialize (H0 l0). rewrite if_false in H0; auto.
  }
  destruct (make_rmap _ Vg (level w)) as [phi' [Gg Hg]].
  {
    extensionality loc; unfold compose, g.
    specialize (PARAMETRIC l loc).
    destruct PARAMETRIC as [pp [ok Jg]].
    specialize ( H0 loc).
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
  }
  unfold f,g in *; clear f g.
  rename phi into f; rename phi' into g.
  assert (join f g w). {
   apply resource_at_join2; auto.
   intro.
   rewrite Hf; rewrite Hg.
   clear - PARAMETRIC H H0 rsh1 rsh2.
   specialize ( H0 loc).
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
   apply identity_unit' in H0. apply H0.
  }
  econstructor; econstructor; split; [apply H1|].
  split.
  eapply jam_noat_splittable_aux; eauto.
  simpl; auto.
  rewrite Hf. extensionality loc. if_tac. auto.
  clear - H0 H2. specialize (H0 loc). rewrite if_false in H0 by auto.
  symmetry; apply slice_resource_identity; auto.
  rewrite Hg. extensionality loc. if_tac. auto.
  clear - H0 H2. specialize (H0 loc). rewrite if_false in H0 by auto.
  symmetry; apply slice_resource_identity; auto.
  apply join_comm in H.
  eapply jam_noat_splittable_aux.
  auto. auto. apply rsh1. eauto. 4: apply (join_comm H1).
  simpl; auto.
  rewrite Hg. extensionality loc. if_tac. auto.
  clear - H0 H2. specialize (H0 loc). rewrite if_false in H0 by auto.
  symmetry; apply slice_resource_identity; auto.
  rewrite Hf. extensionality loc. if_tac. auto.
  clear - H0 H2. specialize (H0 loc). rewrite if_false in H0 by auto.
  symmetry; apply slice_resource_identity; auto.
Qed.*)

(*Lemma address_mapsto_splittable:
      forall ch v l, splittable (fun sh => address_mapsto ch v sh l).
Proof.
intros.
unfold splittable.
intros ? ? ? rsh1 rsh2 H.
apply pred_ext; intros ? ?.
*
destruct H0 as [m1 [m2 [? [? ?]]]].
unfold address_mapsto in *.
destruct H1 as [bl1 [[[LEN1 DECODE1] ?] Hg1]]; destruct H2 as [bl2 [[[LEN2 DECODE2] ?] Hg2]].
exists bl1; split; [split|]; auto.
simpl; auto.
intro loc; specialize ( H1 loc); specialize ( H2 loc).
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
simpl; rewrite <- (Hg1 _ _ (ghost_of_join _ _ _ H0)); auto.
*
rename a into m.
hnf in H0|-*.
destruct H0 as [bl [[[? [? Halign]] ?] Hg]].
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
unfold slice_resource.
destruct (readable_share_dec sh1); [ | contradiction].
destruct (readable_share_dec sh2); [ | contradiction].
constructor. auto.
do 3 red in H2. apply identity_unit' in H2. apply H2; auto.
+
exists bl; repeat split; auto.
intro loc; specialize ( H2 loc); unfold jam in *;  hnf in H2|-*; if_tac; auto.
exists rsh1.
hnf.
rewrite H4.
rewrite if_true by auto.
unfold slice_resource.
destruct H2. hnf in H2.
rewrite H2.
destruct (readable_share_dec sh1); [ | contradiction].
f_equal. apply proof_irr.
do 3 red in H2|-*.
rewrite H4. rewrite if_false by auto. auto.
+
exists bl; repeat split; auto.
intro loc; specialize ( H2 loc); unfold jam in *;  hnf in H2|-*; if_tac; auto.
exists rsh2.
hnf.
rewrite H6.
rewrite if_true by auto.
unfold slice_resource.
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
Qed. *)

Definition share_oblivious (P: pred rmap) :=
  forall w w',
   (forall l, match w' @ l , w @ l with
                 | NO _ _, NO _ _ => True
                 | YES _ sh1 k1 p1 , YES _ sh2 k2 p2 => k1=k2 /\ p1=p2
                 | PURE k1 p1, PURE k2 p2 => k1=k2 /\ p1=p2
                 | _ , _ => False
                 end) ->
     P w' -> P w.

(*Lemma intersection_splittable:
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
Qed. *)

Lemma not_readable_share_retainer_part_eq:
  forall sh, ~ readable_share sh -> retainer_part sh = sh.
   intros.
    apply not_not_share_identity in H.
    unfold retainer_part.
    rewrite (comp_parts comp_Lsh_Rsh sh) at 2.
    apply identity_share_bot in H; rewrite H.
    rewrite Share.lub_bot. auto.
Qed.

Lemma slice_resource_resource_share: forall r sh sh',
  resource_share r = Some sh ->
  join_sub sh' sh ->
  resource_share (slice_resource sh' r) = Some sh'.
Proof.
  intros.
  destruct r; inv H; unfold slice_resource; simpl.
  + f_equal.
    assert (~readable_share sh'). contradict n. destruct H0.
    eapply join_readable1; eauto.
    apply not_readable_share_retainer_part_eq; auto.
  + destruct (readable_share_dec sh'); simpl; auto.
Qed.

Lemma slice_resource_nonlock: forall r sh sh',
  resource_share r = Some sh ->
  join_sub sh' sh ->
  nonlock r ->
  nonlock (slice_resource sh' r).
Proof.
  intros.
  destruct r; inv H; unfold slice_resource; simpl; auto.
  destruct (readable_share_dec sh'); simpl; auto.
Qed.

Lemma NO_ext: forall sh1 sh2 rsh1 rsh2, sh1=sh2 -> NO sh1 rsh1 = NO sh2 rsh2.
Proof. intros. subst sh1. f_equal. apply proof_irr. Qed.

Lemma join_sub_is_slice_resource: forall r r' sh',
  join_sub r' r ->
  resource_share r' = Some sh' ->
  r' = slice_resource sh' r.
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

Lemma slice_resource_share_join: forall sh1 sh2 sh r,
  join sh1 sh2 sh ->
  resource_share r = Some sh ->
  join (slice_resource sh1 r) (slice_resource sh2 r) r.
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
      q' (slice_resource q_sh res) l n /\
      r' (slice_resource r_sh res) l n) /\
    (forall p_res q_res r_res l n,
      join q_res r_res p_res ->
      q' q_res l n ->
      r' r_res l n ->
      p' p_res l n).

(* We should use this lemma to prove all share_join lemmas, also all splittable lemmas. *)
Lemma allp_jam_share_split: forall (P: address -> Prop) (p q r: address -> pred rmap)
  (P_DEC: forall l, {P l} + {~ P l}),
  resource_share_split p q r ->
  allp (jam P_DEC p noat) =
  (allp (jam P_DEC q noat)) * (allp (jam P_DEC r noat)).
Proof.
  intros.
  destruct H as [p' [q' [r' [p_sh [q_sh [r_sh [? [? [? [? [? ?]]]]]]]]]]].
  apply pred_ext; intros w; simpl; intros.
  + destruct (make_core_slice_rmap w P P_DEC q_sh) as [w1 [? ?]].
    {
      intros; specialize (H5 l).
      rewrite if_false in H5 by auto.
      auto.
    }
    destruct (make_slice_rmap w P P_DEC r_sh) as [w2 [? ?]].
    {
      intros; specialize (H5 l).
      rewrite if_false in H5 by auto.
      auto.
    }
    exists w1, w2.
    split3.
    - apply resource_at_join2; try congruence.
      intro l.
      destruct H7, H9; rewrite H7, H9; clear H7 H9.
      specialize (H5 l); destruct (P_DEC l).
      * eapply slice_resource_share_join; eauto.
        rewrite H in H5.
        apply H3 in H5.
        tauto.
      * apply identity_unit' in H5.
        exact H5.
      * destruct H7 as [? ->], H9 as [? ->].
        apply core_unit.
    - destruct H7 as [H7 _].
      intros l.
      rewrite H0, H7, H6.
      specialize (H5 l).
      rewrite H in H5.
      if_tac.
      * apply H3 in H5.
        tauto.
      * auto.
    - destruct H9 as [H9 _].
      intros l.
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
Qed.*)

Section heap.
Context `{!gen_heapGS resource Σ} `{!wsatGS Σ}.

Lemma share_join_op: forall (sh1 sh2 sh : share), sepalg.join sh1 sh2 sh ->
  Share sh1 ⋅ Share sh2 = Share sh.
Proof.
  intros; rewrite share_op_equiv; eauto.
Qed.

Lemma mapsto_share_join: forall sh1 sh2 sh l r, sepalg.join sh1 sh2 sh ->
  readable_share sh1 -> readable_share sh2 ->
  l ↦{#sh1} r ∗ l ↦{#sh2} r ⊣⊢ l ↦{#sh} r.
Proof.
  intros; rewrite -mapsto_split; try done.
  rewrite dfrac_op_own.
  erewrite share_join_op; try done; intros ->; contradiction bot_unreadable.
Qed.

Lemma address_mapsto_share_join:
 forall (sh1 sh2 sh : share) ch v a,
   sepalg.join sh1 sh2 sh ->
   readable_share sh1 -> readable_share sh2 ->
   address_mapsto ch v sh1 a ∗ address_mapsto ch v sh2 a
    ⊣⊢ address_mapsto ch v sh a.
Proof.
  intros.
  rewrite /address_mapsto.
  setoid_rewrite big_sepL_proper at 3; last by intros; symmetry; apply mapsto_share_join.
  setoid_rewrite big_sepL_sep.
  iSplit.
  - iIntros "[H1 H2]".
    iDestruct "H1" as (bl1 (? & ? & ?)) "H1".
    iDestruct "H2" as (bl (? & ? & ?)) "H2".
    iDestruct (mapsto_list_value_cohere with "[$H1 $H2]") as %->.
    { congruence. }
    iExists bl; iSplit; first auto.
    iSplitL "H1"; done.
  - iIntros "H".
    iDestruct "H" as (bl ?) "H".
    rewrite bi.sep_exist_r; iExists bl.
    rewrite bi.sep_exist_l; iExists bl.
    by iFrame "%".
Qed.

Lemma mapsto_no_mapsto_share_join: forall sh1 sh2 sh l r (nsh : ~readable_share sh1), sepalg.join sh1 sh2 sh ->
  readable_share sh2 ->
  mapsto_no l sh1 ∗ l ↦{#sh2} r ⊣⊢ l ↦{#sh} r.
Proof.
  intros; rewrite -mapsto_split_no; try done.
  rewrite dfrac_op_own.
  erewrite share_join_op; try done; intros ->; contradiction bot_unreadable.
Qed.

Lemma mapsto_mapsto_no_share_join: forall sh1 sh2 sh l r (nsh : ~readable_share sh2), sepalg.join sh1 sh2 sh ->
  readable_share sh1 ->
  l ↦{#sh1} r ∗ mapsto_no l sh2 ⊣⊢ l ↦{#sh} r.
Proof.
  intros; rewrite -(mapsto_no_mapsto_share_join _ _ sh); [| | apply sepalg.join_comm, H | ..]; try done.
  by rewrite comm.
Qed.

Lemma mapsto_no_share_join: forall sh1 sh2 sh l (nsh1 : ~readable_share sh1) (nsh2 : ~readable_share sh2), sepalg.join sh1 sh2 sh ->
  mapsto_no l sh1 ∗ mapsto_no l sh2 ⊣⊢ mapsto_no l sh.
Proof.
  intros; rewrite -mapsto_no_split //.
Qed.

Lemma nonlock_permission_bytes_address_mapsto_join:
 forall (sh1 sh2 sh : share) ch v a,
   sepalg.join sh1 sh2 sh ->
   readable_share sh2 ->
   nonlock_permission_bytes sh1 a (Memdata.size_chunk ch)
     ∗ address_mapsto ch v sh2 a
    ⊣⊢ address_mapsto ch v sh a.
Proof.
  intros.
  rewrite /nonlock_permission_bytes /address_mapsto.
  rewrite bi.sep_exist_l.
  apply bi.exist_proper; intros bl.
  rewrite !(big_sepL_seq bl).
  iSplit.
  - iIntros "[H1 [%Hbl H2]]"; iFrame "%".
    destruct Hbl as [-> _].
    rewrite /size_chunk_nat.
    iPoseProof (big_sepL_sep_2 with "H1 H2") as "H".
    iApply (big_sepL_mono with "H").
    intros; iIntros "[H1 H2]".
    destruct (readable_share_dec _).
    + iDestruct "H1" as (??) "H1".
      iDestruct (mapsto_combine with "H1 H2") as "[? ->]".
      erewrite dfrac_op_own, share_join_op; try done; intros ->; contradiction bot_unreadable.
    + iDestruct (mapsto_no_mapsto_combine with "H1 H2") as "?".
      erewrite dfrac_op_own, share_join_op; try done; intros ->; contradiction bot_unreadable.
  - iIntros "[%Hbl H]"; iFrame "%".
    destruct Hbl as [-> _].
    rewrite /size_chunk_nat.
    rewrite -big_sepL_sep.
    iApply (big_sepL_mono with "H").
    intros; iIntros "H".
    destruct (readable_share_dec _).
    + rewrite -mapsto_share_join; try done.
      iDestruct "H" as "[? $]".
      iExists _; iSplit; last done; done.
    + rewrite -mapsto_no_mapsto_share_join //.
Qed.

Lemma VALspec_range_share_join:
 forall sh1 sh2 sh n p,
  readable_share sh1 ->
  readable_share sh2 ->
  sepalg.join sh1 sh2 sh ->
  VALspec_range n sh1 p ∗
  VALspec_range n sh2 p ⊣⊢
  VALspec_range n sh p.
Proof.
  intros.
  rewrite /VALspec_range /VALspec.
  rewrite -big_sepL_sep.
  apply big_sepL_proper; intros.
  iSplit.
  - iIntros "[H1 H2]"; iDestruct "H1" as (v1) "H1"; iDestruct "H2" as (v) "H2".
    iDestruct (mapsto_value_cohere with "[$H1 $H2]") as %->.
    iExists v; rewrite -(mapsto_share_join _ _ sh); try done; iFrame.
  - iIntros "H"; iDestruct "H" as (v) "H".
    rewrite bi.sep_exist_r; iExists v.
    rewrite bi.sep_exist_l; iExists v.
    by rewrite mapsto_share_join.
Qed.

Lemma nonlock_permission_bytes_share_join:
 forall sh1 sh2 sh a n,
  sepalg.join sh1 sh2 sh ->
  nonlock_permission_bytes sh1 a n ∗
  nonlock_permission_bytes sh2 a n ⊣⊢
  nonlock_permission_bytes sh a n.
Proof.
  intros.
  rewrite /nonlock_permission_bytes -big_sepL_sep.
  apply big_sepL_proper; intros.
  pose proof (readable_share_join H).
  repeat destruct (readable_share_dec _); try solve [match goal with H : ~readable_share sh |- _ => contradiction H; auto end];
    try solve [exfalso; eapply join_unreadable_shares; eauto].
  - rewrite bi.sep_exist_r; apply bi.exist_proper; intros ?.
    rewrite bi.sep_exist_l -(mapsto_share_join _ _ sh); try done.
    iSplit; [iIntros "(% & [(% & ?) (% & ?)])" | iIntros "(% & $ & ?)"].
    + iDestruct (mapsto_value_cohere with "[$]") as %->; by iFrame.
    + iExists _; by iFrame.
  - rewrite bi.sep_exist_r; apply bi.exist_proper; intros ?.
    rewrite -bi.persistent_and_sep_assoc; apply bi.and_proper; first done.
    by apply mapsto_mapsto_no_share_join.
  - rewrite bi.sep_exist_l; apply bi.exist_proper; intros ?.
    rewrite comm -bi.persistent_and_sep_assoc; apply bi.and_proper; first done.
    rewrite comm; by apply mapsto_no_mapsto_share_join.
  - by apply mapsto_no_share_join.
Qed.

Lemma nonlock_permission_bytes_VALspec_range_join:
 forall sh1 sh2 sh p n,
  sepalg.join sh1 sh2 sh ->
  readable_share sh2 ->
  nonlock_permission_bytes sh1 p n ∗
  VALspec_range n sh2 p ⊣⊢
  VALspec_range n sh p.
Proof.
  intros.
  rewrite /nonlock_permission_bytes /VALspec_range.
  rewrite -big_sepL_sep.
  apply big_sepL_proper; intros.
  rewrite /VALspec bi.sep_exist_l; apply bi.exist_proper; intros v.
  if_tac.
  - rewrite -(mapsto_share_join _ _ sh) //.
    iSplit.
    + iIntros "[(% & % & H1) H2]".
      iDestruct (mapsto_value_cohere with "[$H1 $H2]") as %->; iFrame.
    + iIntros "[? $]".
      iExists _; iFrame.
  - rewrite mapsto_no_mapsto_share_join //.
Qed.

(*Lemma is_resource_pred_YES_LK lock_size (l: address) (R: pred rmap) sh:
  is_resource_pred
    (fun l' => yesat (SomeP rmaps.Mpred (fun _ => R)) (LK lock_size (snd l' - snd l)) sh l')
    (fun r (l': address) n => exists p, r = YES sh p (LK lock_size (snd l' - snd l))
        (SomeP rmaps.Mpred (fun _ => approx n R))).
Proof. hnf; intros. reflexivity. Qed.*)

Lemma LKspec_share_join lock_size:
 forall sh1 sh2 sh R p,
  sepalg.join sh1 sh2 sh ->
  readable_share sh1 -> readable_share sh2 ->
  LKspec lock_size R sh1 p ∗
  LKspec lock_size R sh2 p ⊣⊢
  LKspec lock_size R sh p.
Proof.
  intros.
  rewrite /LKspec -big_sepL_sep.
  apply big_sepL_proper; intros.
  rewrite assoc -(bi.sep_assoc (_ ↦{_} _)) (bi.sep_comm (inv _ _)) assoc mapsto_share_join //.
  rewrite -assoc -bi.persistent_sep_dup //.
Qed.

End heap.

(* It's often useful to split Tsh in half. *)
Definition gsh1 := fst (slice.cleave Tsh).
Definition gsh2 := snd (slice.cleave Tsh).

Lemma readable_gsh1 : readable_share gsh1.
Proof.
  apply slice.cleave_readable1; auto.
Qed.

Lemma readable_gsh2 : readable_share gsh2.
Proof.
  apply slice.cleave_readable2; auto.
Qed.

Lemma gsh1_gsh2_join : sepalg.join gsh1 gsh2 Tsh.
Proof.
  apply slice.cleave_join; unfold gsh1, gsh2; destruct (slice.cleave Tsh); auto.
Qed.

#[export] Hint Resolve readable_gsh1 readable_gsh2 gsh1_gsh2_join : core.

Lemma gsh1_not_bot : gsh1 <> Share.bot.
Proof.
  intro X; contradiction bot_unreadable; rewrite <- X; auto.
Qed.

Lemma gsh2_not_bot : gsh2 <> Share.bot.
Proof.
  intro X; contradiction bot_unreadable; rewrite <- X; auto.
Qed.
#[export] Hint Resolve gsh1_not_bot gsh2_not_bot : core.

Lemma split_readable_share sh :
  readable_share sh ->
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 sh.
Proof.
  intros.
  pose proof (slice.cleave_readable1 _ H); pose proof (slice.cleave_readable2 _ H).
  destruct (slice.cleave sh) as (sh1, sh2) eqn: Hsplit.
  exists sh1, sh2; split; [|split]; auto.
  replace sh1 with (fst (slice.cleave sh)) by (rewrite Hsplit; auto).
  replace sh2 with (snd (slice.cleave sh)) by (rewrite Hsplit; auto).
  apply slice.cleave_join; auto.
Qed.

Lemma split_Ews :
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 Ews.
Proof.
  apply split_readable_share; auto.
Qed.

(* Split a share into an arbitrary number of subshares. *)
Lemma split_shares : forall n sh, readable_share sh ->
  exists sh1 shs, Zlength shs = Z.of_nat n /\ readable_share sh1 /\ Forall readable_share shs /\
                  sepalg_list.list_join sh1 shs sh.
Proof.
  induction n; intros.
  - exists sh, nil; repeat split; auto.
    apply sepalg_list.fold_rel_nil.
  - destruct (split_readable_share _ H) as (sh1 & sh2 & H1 & ? & ?).
    destruct (IHn _ H1) as (sh1' & shs & ? & ? & ? & ?).
    exists sh1', (shs ++ sh2 :: nil).
    rewrite -> Nat2Z.inj_succ, Zlength_app, Zlength_cons, Zlength_nil; split; [lia|].
    rewrite Forall_app; repeat split; auto.
    eapply sepalg_list.list_join_app; eauto.
    rewrite <- sepalg_list.list_join_1; auto.
Qed.
