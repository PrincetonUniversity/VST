Require Import msl.msl_standard.
Require Import msl.Coqlib2.

Set Implicit Arguments.

Lemma unrel_glb:
 forall a b,
    Share.unrel a b = Share.unrel a (Share.glb a b).
Admitted.

Lemma join_unrel:
  forall sh a b c,
  sepalg.join a b c ->
  sepalg.join (Share.unrel sh a)  (Share.unrel sh b)  (Share.unrel sh c).
Proof.
intros.
destruct H.
subst c.
rewrite (unrel_glb sh a), (unrel_glb sh b), (unrel_glb sh (Share.lub a b)).
rewrite Share.distrib1.
Admitted. (* share hacking *) 

Lemma share_rel_unrel':
  forall r sh, 
    Share.rel r (Share.unrel r sh) = Share.glb r sh.
Proof.
Admitted.

Lemma join_splice2_aux:
  forall L R a1 a2 a3 b1 b2 b3,
  Share.glb L R = Share.bot ->
  Share.lub (Share.rel L (Share.lub a1 a2)) (Share.rel R (Share.lub b1 b2)) 
        = Share.lub (Share.rel L a3) (Share.rel R b3) ->
  Share.lub a1 a2 = a3.
Admitted.

Lemma join_top_comp:
  forall a b, join a b Share.top -> Share.comp a = b.
Admitted.

Lemma share_lemma87:
  forall a b, Share.glb a b = Share.bot -> Share.glb (Share.comp a) b = b.
Admitted.

Lemma share_distrib1':
      forall w x y z : Share.t,
       Share.glb (Share.lub w x) (Share.lub y z) =
       Share.lub (Share.lub (Share.glb w y)  (Share.glb x y))
                     (Share.lub (Share.glb w z) (Share.glb x z)).
Proof.
intros.
rewrite Share.distrib1.
rewrite <- (Share.glb_commute y), <- (Share.glb_commute z).
rewrite !Share.distrib1.
f_equal; f_equal; apply Share.glb_commute.
Qed.

Lemma share_distrib2':
   forall w x y z : Share.t,
       Share.lub (Share.glb w x) (Share.glb y z) =
       Share.glb (Share.glb (Share.lub w y) (Share.lub x y))
                      (Share.glb (Share.lub w z) (Share.lub x z)).
Proof.
intros.
rewrite Share.distrib2.
rewrite <- (Share.lub_commute y), <- (Share.lub_commute z).
rewrite !Share.distrib2.
f_equal; f_equal; apply Share.lub_commute.
Qed.

Lemma lub_bot_e:
  forall x y, Share.lub x y = Share.bot -> x = Share.bot /\ y = Share.bot.
Proof.
intros.
pose proof (Share.lub_upper1 x y).
pose proof (Share.lub_upper2 x y).
rewrite H in H0,H1.
split; apply Share.ord_antisym; auto; apply Share.bot_correct.
Qed.

Lemma glb_less_both:
  forall a L b R,
   Share.Ord a L -> Share.Ord b R ->
   Share.Ord (Share.glb a b) (Share.glb L R).
Proof.
intros.
apply leq_join_sub in H.
apply leq_join_sub in H0.
apply leq_join_sub.
destruct H as [x H]; destruct H0 as [y H0].
exists (Share.lub (Share.lub (Share.glb b x) (Share.glb a y)) (Share.glb x y)).
destruct H, H0.
subst L R.
rewrite share_distrib1'.
split.
*
rewrite Share.distrib1.
rewrite Share.distrib1.
rewrite (Share.glb_commute a b).
rewrite !(Share.glb_assoc b a).
rewrite <- (Share.glb_assoc a a).
rewrite Share.glb_idem.
rewrite (Share.glb_commute b x).
rewrite <- (Share.glb_assoc a x).
rewrite H.
rewrite (Share.glb_commute Share.bot), !Share.glb_bot.
rewrite (Share.glb_commute a y).
rewrite <- (Share.glb_assoc b y).
rewrite H0.
rewrite (Share.glb_commute Share.bot), !Share.glb_bot.
rewrite Share.lub_bot.
rewrite <- (Share.glb_assoc a x).
rewrite H.
rewrite (Share.glb_commute Share.bot), !Share.glb_bot.
rewrite Share.lub_bot; auto.
*
rewrite !Share.lub_assoc.
rewrite (Share.glb_commute x b).
auto.
Qed.

Lemma comp_bot: Share.comp Share.bot = Share.top.
Proof.
apply join_top_comp.
apply bot_join_eq.
Qed.

Lemma comp_Lsh_Rsh:
  Share.comp Share.Lsh = Share.Rsh.
Proof.
 unfold Share.Lsh, Share.Rsh.
 destruct (Share.split Share.top) eqn:?H; simpl.
 apply split_join in H.
 apply join_top_comp; auto.
Qed.

Lemma share_lemma88:
   forall sh, Share.glb sh Share.Rsh = Share.bot ->
                 join_sub sh Share.Lsh.
Proof.
 intros.
 exists (Share.glb (Share.comp sh) Share.Lsh).
 rewrite <- (Share.comp_inv Share.Lsh) at 1.
 rewrite comp_Lsh_Rsh.
 split.
*
 rewrite <- Share.glb_assoc.
 rewrite Share.comp2. rewrite Share.glb_commute. apply Share.glb_bot.
*
 rewrite <- Share.demorgan1.
 rewrite <- Share.comp_inv; symmetry; rewrite <- Share.comp_inv; symmetry.
 f_equal.
 rewrite comp_Lsh_Rsh.
 rewrite <- (Share.comp_inv sh) at 1.
 rewrite <- Share.demorgan2.
 rewrite Share.comp_inv.
 rewrite Share.distrib1.
 rewrite Share.glb_commute.
 rewrite Share.comp2.
 rewrite Share.lub_commute,  Share.lub_bot.
 forget Share.Rsh as b.
 apply share_lemma87; auto.
Qed.

Definition Tsh : share := Share.top.

Definition nonempty_share (sh: share) := 
       sepalg.nonidentity sh.
Definition readable_share (sh: share) :=
       nonempty_share (Share.glb Share.Rsh sh).
Definition writable_share (sh: share) := 
    join_sub Share.Rsh sh.


Lemma lub_Lsh_Rsh:
 Share.lub Share.Lsh Share.Rsh = Share.top.
Proof.
unfold Share.Lsh, Share.Rsh.
destruct (Share.split Share.top) eqn:H; simpl.
apply Share.split_together; auto.
Qed.

Lemma glb_Lsh_Rsh:
 Share.glb Share.Lsh Share.Rsh = Share.bot.
Proof.
unfold Share.Lsh, Share.Rsh.
destruct (Share.split Share.top) eqn:H; simpl.
apply (Share.split_disjoint _ _ _ H).
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
 forall sh, nonidentity sh -> Share.unrel sh Share.bot = Share.bot.
Proof.
intros.
rewrite <- (Share.rel_bot1 sh) at 1.
rewrite Share.unrel_rel; auto.
Qed.

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


Lemma Rsh_nonidentity:   sepalg.nonidentity Share.Rsh.
Proof.
unfold Share.Rsh.
destruct (Share.split Share.top) eqn:?. simpl; intro.
apply identity_share_bot in H. subst.
pose proof (Share.split_nontrivial _ _ _ Heqp).
spec H;[auto | ].
apply Share.nontrivial in H. auto.
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

Lemma join_splice2_aux2:
  forall a1 a2 a3 b1 b2 b3,
  Share.lub (Share.rel Share.Lsh (Share.lub a1 a2)) (Share.rel Share.Rsh (Share.lub b1 b2)) 
        = Share.lub (Share.rel Share.Lsh a3) (Share.rel Share.Rsh b3) ->
  Share.lub a1 a2 = a3 /\ Share.lub b1 b2 = b3.
Proof.
intros.
split.
apply join_splice2_aux in H; auto.
apply glb_Lsh_Rsh.
rewrite Share.lub_commute in H.
rewrite (Share.lub_commute (Share.rel _ a3)) in H.
apply join_splice2_aux in H; auto.
rewrite Share.glb_commute.
apply glb_Lsh_Rsh.
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
apply join_splice2_aux2; auto.
Qed.

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
unfold readable_share, nonempty_share, nonidentity in *.
contradict H0.
destruct H.
subst sh.
rewrite Share.distrib1 in H0.
pose proof (Share.lub_upper1 (Share.glb Share.Rsh sh1) (Share.glb Share.Rsh sh2)).
apply identity_share_bot in H0. rewrite H0 in H1.
pose proof Share.bot_correct (Share.glb Share.Rsh sh1).
pose proof (Share.ord_antisym _ _ H1 H2).
rewrite H3.
apply bot_identity.
Qed.

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