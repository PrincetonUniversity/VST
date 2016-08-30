Require Import msl.msl_standard.
Require Import msl.Coqlib2.

Set Implicit Arguments.

Definition Tsh : share := Share.top.

Definition nonempty_share (sh: share) := 
       sepalg.nonidentity sh.
Definition readable_share (sh: share) :=
       nonempty_share (Share.glb Share.Rsh sh).
Definition writable_share (sh: share) := 
    join_sub Share.Rsh sh.

Lemma readable_share_dec:
  forall sh, {readable_share sh}+{~ readable_share sh}.
Proof.
intros.
unfold readable_share, nonempty_share.
unfold nonidentity.
destruct (dec_share_identity (Share.glb Share.Rsh sh)); [ right | left]; auto.
Defined.

Lemma writable_share_dec: forall sh, {writable_share sh} + {~ writable_share sh}.
Proof.
  unfold writable_share. intros.
  destruct (Share.EqDec_share (Share.glb Share.Rsh sh) Share.Rsh); [left|right].
*
  exists (Share.glb Share.Lsh sh).
  split.
  -
  rewrite <- Share.glb_assoc.
  rewrite (Share.glb_commute Share.Rsh).
  unfold Share.Rsh, Share.Lsh.
  destruct (Share.split Share.top) eqn:?. simpl.
  apply Share.split_disjoint in Heqp. rewrite Heqp.
  rewrite Share.glb_commute, Share.glb_bot. auto.
  -
  apply Share.distrib_spec with Share.Rsh.
  rewrite <- Share.lub_assoc. rewrite Share.lub_idem.
  rewrite Share.distrib2.
  rewrite Share.lub_commute.
  destruct (Share.split Share.top) eqn:?.
  unfold Share.Lsh, Share.Rsh at 1.
  rewrite Heqp. simpl.
  rewrite (Share.split_together _ _ _ Heqp).
  rewrite Share.glb_commute, Share.glb_top. auto.
  rewrite Share.glb_absorb. rewrite e. auto.
*
  contradict n.
  destruct n as [a [? ?]].
  subst sh.
  rewrite Share.glb_absorb. auto.
Qed.

Lemma writable_share_right: forall sh, writable_share sh -> Share.unrel Share.Rsh sh = Share.top.
Proof.
 intros.
 apply Share.contains_Rsh_e.
 apply H.
Qed.

Lemma writable_readable:
 forall sh, writable_share sh -> readable_share sh.
Proof.
unfold writable_share, readable_share.
intros.
intro.
destruct H as [a ?].
destruct H.
subst sh. 
rewrite Share.glb_absorb in H0.
clear - H0. unfold Share.Rsh in H0.
destruct (Share.split Share.top) eqn:?. simpl in H0.
apply split_nontrivial' in Heqp; auto.
apply top_share_nonidentity in Heqp. auto.
Qed.

Lemma readable_share_top:
  readable_share Share.top.
Proof.
hnf. intros.
rewrite Share.glb_top in H.
unfold Share.Rsh in H.
destruct (Share.split Share.top) eqn:?.
apply split_nontrivial' in Heqp.
apply identity_share_bot in Heqp.
apply Share.nontrivial; auto.
simpl in H; auto.
Qed.
Hint Resolve writable_readable.

Lemma unrel_bot:
 forall sh, Share.unrel sh Share.bot = Share.bot.
Proof.
Admitted. (* share hacking *)

Lemma top_pfullshare: forall psh, pshare_sh psh = Share.top -> psh = pfullshare.
Proof.
intros psh H.
apply lifted_eq; auto.
Qed.

Lemma fst_split_fullshare_not_bot: fst (Share.split fullshare) <> Share.bot.
Proof.
intro.
case_eq (Share.split fullshare); intros.
rewrite H0 in H. simpl in H. subst.
apply Share.split_nontrivial in H0; auto.
apply Share.nontrivial in H0. contradiction.
Qed.

Lemma fst_split_fullshare_not_top: fst (Share.split fullshare) <> Share.top.
Proof.
case_eq (Share.split fullshare); intros.
simpl; intro. subst.
apply nonemp_split_neq1 in H.
apply H; auto.
apply top_share_nonidentity.
Qed.

Definition read_sh: pshare := fst (split_pshare pfullshare).

Definition extern_retainer : share := Share.Lsh.

Lemma extern_retainer_neq_bot:
  extern_retainer <> Share.bot.
apply fst_split_fullshare_not_bot.
Qed.

Lemma extern_retainer_neq_top:
  extern_retainer <> Share.top.
apply fst_split_fullshare_not_top.
Qed.

Lemma writable_share_top: writable_share Tsh.
Proof.
red.
exists Share.Lsh.
apply join_comm.
unfold Share.Lsh, Share.Rsh, Tsh.
destruct (Share.split Share.top) eqn:?. simpl.
apply split_join; auto.
Qed.
Hint Resolve writable_share_top.

Lemma writable_readable_share:
 forall sh, writable_share sh -> readable_share sh.
Proof.
apply writable_readable; auto.
Qed.
Hint Resolve writable_readable_share.

Definition Ews (* extern_write_share *) := Share.splice extern_retainer Tsh.

Lemma glb_Rsh_rel_Lsh_sh:
 forall sh,
  Share.glb Share.Rsh (Share.rel Share.Lsh sh) = Share.bot.
Proof.
intros.
destruct (Share.split Share.top) eqn:?.
unfold Share.Rsh, Share.Lsh. rewrite Heqp; simpl.
rewrite Share.glb_commute.
destruct (rel_join t t t0 _ (split_join _ _ _ Heqp)).
clear - H.
pose proof (rel_leq t t0).
rewrite <- leq_join_sub in H0.
rewrite Share.ord_spec1 in H0.
rewrite H0 in H.
rewrite <- Share.glb_assoc in H.
rewrite <- Share.rel_preserves_glb in H.
Admitted.

Lemma writable_Ews: writable_share Ews.
Proof.
unfold writable_share, Ews, extern_retainer.
unfold Share.splice.
exists (Share.rel Share.Lsh Share.Lsh).
unfold Tsh.
rewrite Share.rel_top1.
split.
*
 apply glb_Rsh_rel_Lsh_sh.
*
rewrite Share.lub_commute. auto.
Qed.

Hint Resolve writable_Ews.

Definition Ers (* Extern read share *) := 
    Share.splice extern_retainer Share.Lsh.

Lemma readable_nonidentity: forall sh, readable_share sh -> sepalg.nonidentity sh.
Proof.
intros.
do 2 red in H.
red in H|-*. contradict H.
apply identity_share_bot in H. subst.
rewrite Share.glb_bot.
apply bot_identity.
Qed.

Hint Resolve readable_nonidentity.

Lemma sub_glb_bot:
  forall r a c : share,
   sepalg.join_sub a c ->
   Share.glb r c = Share.bot ->
   Share.glb r a = Share.bot.
Proof.
intros.
apply leq_join_sub in H.
apply Share.ord_spec1 in H.
rewrite H. rewrite <- Share.glb_assoc.
rewrite (Share.glb_commute r).
rewrite Share.glb_assoc. rewrite H0.
apply Share.glb_bot.
Qed.

Lemma glb_split: forall sh,
 Share.glb (fst (Share.split sh)) (snd (Share.split sh)) = Share.bot.
Proof.
intros.
destruct (Share.split sh) eqn:?H.
simpl.
apply split_join in H.
destruct H.
auto.
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

Lemma Lsh_nonidentity:   sepalg.nonidentity Share.Lsh.
Proof.
unfold Share.Lsh.
destruct (Share.split Share.top) eqn:?. simpl; intro.
apply identity_share_bot in H. subst.
pose proof (Share.split_nontrivial _ _ _ Heqp).
spec H;[auto | ].
apply Share.nontrivial in H. auto.
Qed.

Lemma join_splice:
  forall a1 a2 a3 b1 b2 b3,
 sepalg.join a1 a2 a3 ->
 sepalg.join b1 b2 b3 ->
 sepalg.join (Share.splice a1 b1)  (Share.splice a2 b2)  (Share.splice a3 b3).
Admitted. (* share hacking *)

Lemma join_unrel:
  forall sh a b c,
  sepalg.join a b c ->
  sepalg.join (Share.unrel sh a)  (Share.unrel sh b)  (Share.unrel sh c).
Admitted. (* share hacking *) 

Lemma splice_bot2:
 forall sh, Share.splice sh Share.bot = Share.rel Share.Lsh sh.
Proof.
intros.
unfold Share.splice.
rewrite Share.rel_bot1.
rewrite Share.lub_bot.
auto.
Qed.

Lemma share_rel_unrel:
  forall r sh, 
    join_sub sh r ->
    Share.rel r (Share.unrel r sh) = sh.
Admitted.

Lemma share_sub_Lsh:
 forall sh, identity (Share.unrel Share.Rsh sh) -> join_sub sh Share.Lsh.
Admitted. (* share hacking *)

Lemma splice_unrel_unrel:
  forall sh,
   Share.splice (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) = sh.
Admitted.  (* share hacking *)

Lemma join_rel_rel_strange:
    forall t1 t2 t3 (p: pshare),
      join (Share.rel Share.Lsh t1) (Share.rel Share.Lsh t2) (Share.splice t3 (pshare_sh p)) ->
      False.
  Admitted. (* share hacking *)

Lemma join_rel_rel_strange2:
    forall sh1 t2  t3 (p: pshare),
      join sh1 (Share.splice t2 (pshare_sh p)) (Share.rel Share.Lsh t3) ->
      False.
  Admitted. (* share hacking *)

Lemma join_splice2:
  forall a1 a2 a3 b1 b2 b3 : Share.t,
  join (Share.splice a1 b1) (Share.splice a2 b2) (Share.splice a3 b3) ->
  join a1 a2 a3 /\ join b1 b2 b3.
Admitted. (* share hacking *)

Lemma join_sub_readable:
  forall sh sh', sepalg.join_sub sh sh' -> readable_share sh -> readable_share sh'.
Proof.
unfold readable_share; 
intros.
hnf in H0|-*.
contradict H0.
apply identity_share_bot in H0.
eapply sub_glb_bot in H0; eauto.
rewrite H0.
apply bot_identity.
Qed.

Lemma join_unreadable_shares:
 forall sh1 sh2 sh,
  sepalg.join sh1 sh2 sh ->
  ~ readable_share sh1 ->
  ~ readable_share sh2 ->
 ~ readable_share sh.
Proof.
unfold readable_share; intros.
unfold nonempty_share in *.
unfold sepalg.nonidentity in *.
contradict H0. contradict H1. contradict H0.
destruct H.
subst sh.
apply identity_share_bot in H1.
apply identity_share_bot in H0.
rewrite Share.distrib1, H0,H1.
rewrite Share.lub_bot.
apply bot_identity.
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

Lemma readable_share_join_left:
  forall sh1 sh2 sh,
    sepalg.join sh1 sh2 sh ->
    readable_share sh1 -> readable_share sh.
Proof.
intros.
unfold readable_share in *.
Admitted. (* share hacking *)

Lemma readable_share_join:
  forall sh1 sh2 sh,
    sepalg.join sh1 sh2 sh ->
    readable_share sh1 \/ readable_share sh2 -> readable_share sh.
Proof.
  intros.
  destruct H0.
  + eapply readable_share_join_left; eauto.
  + apply join_comm in H.
    eapply readable_share_join_left; eauto.
Qed.

Lemma Lsh_bot_neq: Share.Lsh <> Share.bot.
Proof.
  pose proof Lsh_nonidentity.
  pose proof bot_identity.
  intro.
  rewrite <- H1 in H0.
  apply H; auto.
Qed.

Lemma readable_share_unrel_Rsh: forall sh, readable_share sh <-> nonunit (Share.unrel Share.Rsh sh).
unfold readable_share in *.
Admitted. (* share hacking *)

Lemma not_nonunit_bot: forall sh, ~ nonunit sh <-> sh = Share.bot.
Proof.
  intros; split; intros.
  + destruct (dec_share_identity sh).
    - apply identity_share_bot; auto.
    - exfalso; apply H.
      apply nonidentity_nonunit.
      auto.
  + subst.
    intro.
    apply nonunit_nonidentity in H.
    apply H.
    apply bot_identity.
Qed.