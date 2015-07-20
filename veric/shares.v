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
  forall rsh sh, sepalg.nonidentity sh -> 
     readable_share (Share.splice rsh sh).
Proof.
intros.
unfold readable_share, Share.splice.
rewrite Share.distrib1.
rewrite <- (Share.rel_top1 Share.Rsh) at 2.
rewrite <- Share.rel_preserves_glb.
rewrite (Share.glb_commute Share.top).
rewrite Share.glb_top.
red in H. red. red. contradict H.
Admitted.

Lemma Lsh_nonidentity:   sepalg.nonidentity Share.Lsh.
   (* copy me to veric/shares.v *)
Proof.
unfold Share.Lsh.
destruct (Share.split Share.top) eqn:?. simpl; intro.
apply identity_share_bot in H. subst.
pose proof (Share.split_nontrivial _ _ _ Heqp).
spec H;[auto | ].
apply Share.nontrivial in H. auto.
Qed.

