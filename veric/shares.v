Require Import msl.msl_standard.
Require Import msl.Coqlib2.

Set Implicit Arguments.

Definition Tsh : share := Share.top.

Definition nonempty_share (sh: share) := 
       sepalg.nonidentity sh.
Definition readable_share (sh: share) :=
       nonempty_share (Share.glb Share.Rsh sh).
Definition writable_share (sh: share) := 
       Share.unrel Share.Rsh sh = Share.top.

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
  intros.
  unfold writable_share.
  apply Share.EqDec_share.
Qed.

Lemma writable_share_right: forall sh, writable_share sh -> Share.unrel Share.Rsh sh = Share.top.
Proof.  auto. 
Qed.

Lemma writable_readable:
 forall sh, writable_share sh -> readable_share sh.
Proof.
unfold writable_share, readable_share.
intros.
intro.
Admitted. (* share hacking *)

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
apply Share.contains_Rsh_e. apply top_correct'.
Qed.
Hint Resolve writable_share_top.

Lemma writable_readable_share:
 forall sh, writable_share sh -> readable_share sh.
Proof.
unfold writable_share, readable_share.
intros.
intro.
Admitted. (* share hacking *)
Hint Resolve writable_readable_share.

Definition Ews (* extern_write_share *) := Share.splice extern_retainer Tsh.

Lemma writable_Ews: writable_share Ews.
Proof.
hnf; intros.
unfold Ews,  extern_retainer.
apply Share.unrel_splice_R.
Qed.
Hint Resolve writable_Ews.

Definition Ers (* Extern read share *) := 
    Share.splice extern_retainer Share.Lsh.

Lemma readable_nonidentity: forall sh, readable_share sh -> sepalg.nonidentity sh.
Proof.
Admitted. (* share hacking *)

Hint Resolve readable_nonidentity.

Lemma misc_share_lemma1:
  forall sh, 
  Share.lub (Share.rel Share.Lsh (Share.unrel Share.Lsh sh))
      (Share.rel Share.Rsh (Share.unrel Share.Rsh sh)) 
   = sh.
Admitted.

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
Admitted.  (* share hacking *)

Lemma right_nonempty_readable:
  forall rsh sh, sepalg.nonidentity sh <-> 
     readable_share (Share.splice rsh sh).
Proof.
intros.
unfold readable_share, Share.splice.
rewrite Share.distrib1.
rewrite <- (Share.rel_top1 Share.Rsh) at 2.
rewrite <- Share.rel_preserves_glb.
rewrite (Share.glb_commute Share.top).
rewrite Share.glb_top.
(* red in H. red. red. contradict H. *)
Admitted.

Lemma Lsh_nonidentity:   sepalg.nonidentity Share.Lsh.
Proof.
unfold Share.Lsh.
destruct (Share.split Share.top) eqn:?. simpl; intro.
apply identity_share_bot in H. subst.
pose proof (Share.split_nontrivial _ _ _ Heqp).
spec H;[auto | ].
apply Share.nontrivial in H. auto.
Qed.

Lemma sub_unrel_bot:
  forall r a c : share,
    sepalg.join_sub a c ->
    Share.unrel r c = Share.bot ->
    Share.unrel r a = Share.bot.
Admitted.

Lemma share_unrel_lub:
  forall a b r : Share.t,
  Share.glb a b = Share.bot ->
  Share.glb (Share.unrel r a) (Share.unrel r b) = Share.bot ->
  Share.unrel r (Share.lub a b) = Share.lub (Share.unrel r a) (Share.unrel r b).
Admitted. (* share hacking *)

Lemma share_splice_lub: 
forall (a b : Share.t) (sh : share),
Share.glb a b = Share.bot ->
Share.glb (Share.splice a sh) (Share.unrel Share.Lsh b) = Share.bot ->
Share.splice (Share.lub a b) sh =
Share.lub (Share.splice a sh) (Share.unrel Share.Lsh b).
Admitted. (* share hacking *)

Lemma share_splice_lub': 
forall (a b : Share.t) (sh : share),
Share.glb a b = Share.bot ->
Share.glb (Share.unrel Share.Lsh a) (Share.splice b sh) = Share.bot ->
Share.splice (Share.lub a b) sh =
Share.lub (Share.unrel Share.Lsh a) (Share.splice b sh).
Admitted. (* share hacking *)

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
