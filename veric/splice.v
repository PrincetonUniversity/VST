Require Import VST.msl.msl_standard.
Require Import VST.msl.Coqlib2.
Require Import VST.veric.shares.

Section UNPROVABLE.

Variable wishes_eq_horses : False.

Lemma unrel_glb:
 forall a b,
    Share.unrel a b = Share.unrel a (Share.glb a b).
contradiction wishes_eq_horses.
Qed.

Lemma share_rel_unrel':
  forall r sh,
    Share.rel r (Share.unrel r sh) = Share.glb r sh.
Proof.
contradiction wishes_eq_horses.
Qed.

Lemma share_sub_Lsh:
forall sh, identity (Share.unrel Share.Rsh sh) -> join_sub sh Share.Lsh.
Proof.
 intros.
 rewrite (Share.decompose_Rsh sh) in H.
 remember (decompose sh).
 symmetry in Heqp. destruct p as [sh1 sh2].
 simpl in H.
 apply identity_share_bot in H. subst.
 generalize (top_correct' sh1);intro.
 destruct H.
 exists (Share.recompose (x, Share.bot)).
 rewrite Share.Lsh_recompose.
 assert (sh = Share.recompose (sh1, Share.bot)).
  rewrite <- Heqp. rewrite Share.recompose_decompose. trivial.
 rewrite H0.
 eapply Share.decompose_join.
 rewrite Share.decompose_recompose. f_equal.
 rewrite Share.decompose_recompose. f_equal.
 rewrite Share.decompose_recompose. f_equal.
 split. trivial.
 split. apply Share.glb_bot. apply Share.lub_bot.
Qed.

Lemma join_splice2_aux:
forall a1 a2 a3 b1 b2 b3,
Share.lub (Share.rel Share.Lsh (Share.lub a1 a2)) (Share.rel Share.Rsh (Share.lub b1 b2))
= Share.lub (Share.rel Share.Lsh a3) (Share.rel Share.Rsh b3) ->
Share.lub a1 a2 = a3 /\ Share.lub b1 b2 = b3.
Proof with try tauto.
 intros. rewrite Share.lub_rel_recompose in H.
 generalize (Share.decompose_recompose (Share.lub a1 a2, Share.lub b1 b2));intro.
 rewrite H in H0.
 rewrite Share.lub_rel_recompose in H0.
 rewrite Share.decompose_recompose in H0.
 split;congruence.
Qed.

Lemma share_rel_unrel:
  forall r sh,
    join_sub sh r ->
    Share.rel r (Share.unrel r sh) = sh.
Proof.
intros.
rewrite share_rel_unrel'.
destruct H as [a [H H0]].
subst r.
rewrite Share.glb_commute.
rewrite Share.distrib1.
rewrite H.
rewrite Share.lub_bot.
apply Share.glb_idem.
Qed.

Lemma glb_rel_Lsh_Rsh:
 forall a b, Share.glb (Share.rel Share.Lsh a) (Share.rel Share.Rsh b) = Share.bot.
Proof.
intros.
assert (H := rel_leq Share.Lsh a).
assert (H0 := rel_leq Share.Rsh b).
apply leq_join_sub in H.
apply leq_join_sub in H0.
forget (Share.rel Share.Lsh a) as aL.
forget (Share.rel Share.Rsh b) as bR.
apply Share.ord_antisym; [ | apply Share.bot_correct].
rewrite <- glb_Lsh_Rsh.
forget Share.Lsh as L.
forget Share.Rsh as R.
apply glb_less_both; auto.
Qed.

Lemma glb_Rsh_rel_Lsh_sh:
 forall sh,
  Share.glb Share.Rsh (Share.rel Share.Lsh sh) = Share.bot.
Proof.
intros.
destruct (Share.split Share.top) eqn:?.
unfold Share.Rsh, Share.Lsh. rewrite Heqp; simpl.
rewrite Share.glb_commute.
destruct (rel_join t t t0 _ (split_join _ _ _ Heqp)).
clear - H Heqp.
pose proof (rel_leq t t0).
rewrite <- leq_join_sub in H0.
rewrite Share.ord_spec1 in H0.
rewrite H0 in H.
rewrite <- Share.glb_assoc in H.
rewrite <- Share.rel_preserves_glb in H.
pose proof (rel_leq t (Share.glb t t0)).
apply leq_join_sub in H1.
apply Share.ord_spec1 in H1. rewrite <- H1 in H.
clear H1.
pose proof bot_identity. rewrite <- H in H1.
apply (rel_nontrivial) in H1.
destruct H1.
apply split_nontrivial' in Heqp; auto.
apply identity_share_bot in Heqp.
apply Share.nontrivial in Heqp; contradiction.
clear H.
apply identity_share_bot in H1.
clear - H1.
pose proof (rel_leq t sh).
forget (Share.rel t sh) as b.
destruct H as [a [? ?]].
subst t.
rewrite Share.glb_commute in H1; rewrite Share.distrib1 in H1.
rewrite Share.glb_commute in H1.
pose proof (Share.lub_upper1 (Share.glb b t0) (Share.glb t0 a)).
rewrite H1 in H0.
apply Share.ord_antisym; auto.
apply Share.bot_correct.
Qed.

Lemma right_nonempty_readable:
  forall rsh sh, sepalg.nonidentity sh <->
     readable_share (Share.splice rsh sh).
Proof.
intros.
unfold readable_share, Share.splice.
unfold nonempty_share,nonidentity.
assert (identity sh <-> identity (Share.glb Share.Rsh (Share.lub (Share.rel Share.Lsh rsh) (Share.rel Share.Rsh sh))));
  [ | intuition].
split; intro.
*
apply identity_share_bot in H. subst.
rewrite Share.rel_bot1.
rewrite Share.lub_bot.
rewrite glb_Rsh_rel_Lsh_sh.
apply bot_identity.
*
rewrite Share.distrib1 in H.
rewrite glb_Rsh_rel_Lsh_sh in H.
rewrite Share.lub_commute, Share.lub_bot in H.
assert (identity (Share.glb (Share.rel Share.Rsh Share.top) (Share.rel Share.Rsh sh)))
  by (rewrite Share.rel_top1; auto).
clear H.
rewrite <- Share.rel_preserves_glb in H0.
rewrite Share.glb_commute, Share.glb_top in H0.
apply rel_nontrivial in H0.
destruct H0; auto.
unfold Share.Rsh in H.
destruct (Share.split Share.top) eqn:?; simpl in *.
apply split_nontrivial' in Heqp; auto.
apply top_share_nonidentity in Heqp.
contradiction.
Qed.

Lemma writable_share_right: forall sh, writable_share sh -> Share.unrel Share.Rsh sh = Share.top.
Proof.
 intros.
 apply Share.contains_Rsh_e.
 apply H.
Qed.

Lemma unrel_bot:
 forall sh, nonidentity sh -> Share.unrel sh Share.bot = Share.bot.
Proof.
intros.
rewrite <- (Share.rel_bot1 sh) at 1.
rewrite Share.unrel_rel; auto.
Qed.

Lemma join_splice2_aux1:
  forall a1 a2 b1 b2,
  Share.lub (Share.rel Share.Lsh (Share.glb a1 a2)) (Share.rel Share.Rsh (Share.glb b1 b2)) = Share.bot ->
  Share.glb a1 a2 = Share.bot /\ Share.glb b1 b2 = Share.bot.
Proof. intros.
  rewrite !Share.rel_preserves_glb in H.
  apply lub_bot_e in H; destruct H.
  rewrite <- Share.rel_preserves_glb in H, H0.
  pose proof (rel_nontrivial Share.Lsh (Share.glb a1 a2)).
  rewrite H in H1. specialize (H1 bot_identity). clear H.
  pose proof (rel_nontrivial Share.Rsh (Share.glb b1 b2)).
  rewrite H0 in H. specialize (H bot_identity). clear H0.
  destruct H1. contradiction (Lsh_nonidentity H0).
  destruct H. contradiction (Rsh_nonidentity H).
  apply identity_share_bot in H.
  apply identity_share_bot in H0.
  auto.
Qed.

Lemma join_splice:
  forall a1 a2 a3 b1 b2 b3,
 sepalg.join a1 a2 a3 ->
 sepalg.join b1 b2 b3 ->
 sepalg.join (Share.splice a1 b1)  (Share.splice a2 b2)  (Share.splice a3 b3).
Proof.
intros.
unfold Share.splice.
destruct H, H0.
split.
*
rewrite Share.distrib1.
do 2 rewrite (Share.glb_commute (Share.lub _ _)).
rewrite Share.distrib1.
rewrite Share.distrib1.
rewrite !(Share.glb_commute (Share.rel _ a2)).
rewrite !(Share.glb_commute (Share.rel _ b2)).
rewrite <- !Share.rel_preserves_glb.
rewrite H,H0.
rewrite !Share.rel_bot1.
rewrite (Share.lub_commute Share.bot).
rewrite !Share.lub_bot.
rewrite Share.glb_commute.
rewrite !glb_rel_Lsh_Rsh.
apply Share.lub_bot.
*
subst a3 b3.
rewrite !Share.rel_preserves_lub.
forget (Share.rel Share.Lsh a1) as La1.
forget (Share.rel Share.Rsh b1) as Rb1.
forget (Share.rel Share.Lsh a2) as La2.
forget (Share.rel Share.Rsh b2) as Rb2.
rewrite !Share.lub_assoc.
f_equal.
rewrite Share.lub_commute.
rewrite !Share.lub_assoc.
f_equal.
apply Share.lub_commute.
Qed.

Lemma splice_bot2:
 forall sh, Share.splice sh Share.bot = Share.rel Share.Lsh sh.
Proof.
intros.
unfold Share.splice.
rewrite Share.rel_bot1.
rewrite Share.lub_bot.
auto.
Qed.

Lemma splice_unrel_unrel:
  forall sh,
   Share.splice (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) = sh.
Proof.
intros.
unfold Share.splice.
rewrite !share_rel_unrel'.
rewrite share_distrib2'.
rewrite Share.lub_idem.
rewrite lub_Lsh_Rsh.
rewrite (Share.glb_commute Share.top).
rewrite Share.glb_top.
rewrite <- Share.glb_assoc.
rewrite (Share.lub_commute sh).
rewrite share_distrib1'.
rewrite (Share.glb_commute Share.Rsh).
rewrite glb_Lsh_Rsh.
rewrite (Share.lub_commute Share.bot), Share.lub_bot.
rewrite Share.glb_idem.
rewrite (Share.glb_commute sh).
rewrite <- Share.lub_assoc.
rewrite Share.glb_commute.
rewrite Share.lub_commute.
rewrite Share.glb_absorb.
auto.
Qed.

Lemma join_splice2:
  forall a1 a2 a3 b1 b2 b3 : Share.t,
  join (Share.splice a1 b1) (Share.splice a2 b2) (Share.splice a3 b3) ->
  join a1 a2 a3 /\ join b1 b2 b3.
Proof.
intros.
unfold Share.splice in H.
destruct H.
unfold join, Share.Join_ba.
assert ((Share.glb a1 a2 = Share.bot /\ Share.glb b1 b2 = Share.bot)
         /\ (Share.lub a1 a2 = a3 /\ Share.lub b1 b2 = b3)); [ | intuition].
split.
*
clear - H.
rewrite share_distrib1' in H.
rewrite (Share.lub_commute (Share.glb _ _)) in H.
rewrite Share.lub_assoc in H.
rewrite <- (Share.lub_assoc (Share.glb (Share.rel Share.Lsh _) _)) in H.
rewrite (Share.lub_commute (Share.lub _ _)) in H.
rewrite <- Share.lub_assoc in H.
rewrite <- !Share.rel_preserves_glb in H.
rewrite (Share.glb_commute (Share.rel Share.Rsh _)) in H.
rewrite !glb_rel_Lsh_Rsh in H.
rewrite (Share.lub_commute Share.bot), !Share.lub_bot in H.
rewrite Share.lub_commute in H.
apply join_splice2_aux1; auto.
*
clear - H0.
rewrite Share.lub_assoc in H0.
rewrite (Share.lub_commute (Share.rel Share.Rsh _)) in H0.
rewrite <- !Share.lub_assoc in H0.
rewrite <- Share.rel_preserves_lub in H0.
rewrite Share.lub_assoc in H0.
rewrite <- Share.rel_preserves_lub in H0.
rewrite (Share.lub_commute b2) in H0.
apply join_splice2_aux; auto.
Qed.

Lemma nonidentity_rel_Lsh: forall t, nonidentity (Share.rel Share.Lsh t) -> nonidentity t.
Proof.
  intros.
  rewrite <- splice_bot2 in H.
  intro.
  apply H; clear H.
  intros ? ? ?.
  rewrite <- (splice_unrel_unrel a), <- (splice_unrel_unrel b) in H |- *.
  forget (Share.unrel Share.Lsh a) as sh0.
  forget (Share.unrel Share.Rsh a) as sh1.
  forget (Share.unrel Share.Lsh b) as sh2.
  forget (Share.unrel Share.Rsh b) as sh3.
  apply join_splice2 in H.
  destruct H.
  apply H0 in H.
  apply bot_identity in H1.
  subst.
  auto.
Qed.

Lemma readable_share_unrel_Rsh: forall sh, readable_share sh <-> nonunit (Share.unrel Share.Rsh sh).
unfold readable_share in *.
Proof.
intros.
unfold nonempty_share.
transitivity (nonidentity (Share.unrel Share.Rsh sh)).
unfold nonidentity.
split; intro; contradict H.
apply identity_share_bot in H.
rewrite <- share_rel_unrel'.
rewrite H.
rewrite Share.rel_bot1.
apply bot_identity.
rewrite <- share_rel_unrel' in H.
apply rel_nontrivial in H.
destruct H; auto.
elimtype False.
apply identity_share_bot in H.
unfold Share.Rsh in H.
destruct (Share.split Share.top) eqn:?. simpl in H. subst.
apply split_nontrivial' in Heqp.
apply identity_share_bot in Heqp.
apply Share.nontrivial; auto.
right.
apply bot_identity.
split.
apply nonidentity_nonunit.
intro.
hnf in H|-*; intro.
apply identity_share_bot in H0.
rewrite H0 in H.
apply (H Share.top).
red.
apply bot_join_eq.
Qed.

End UNPROVABLE.

