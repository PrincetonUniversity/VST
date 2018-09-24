Require Import VST.msl.msl_standard.
Require Import VST.msl.Coqlib2.

Set Implicit Arguments.

Lemma share_lemma87:
  forall a b, Share.glb a b = Share.bot -> Share.glb (Share.comp a) b = b.
Proof.
intros.
rewrite <- (Share.glb_top b) at 2.
rewrite (Share.glb_commute b).
rewrite <- (Share.comp1 a).
rewrite (Share.glb_commute (Share.lub _ _)).
rewrite Share.distrib1.
rewrite (Share.glb_commute b).
rewrite H.
rewrite (Share.lub_commute Share.bot), Share.lub_bot.
apply Share.glb_commute.
Qed.

Lemma join_top_comp:
  forall a b, join a b Share.top -> Share.comp a = b.
Proof.
intros.
destruct H.
pose proof (share_lemma87 H).
rewrite <- H1.
rewrite Share.glb_commute.
symmetry.
rewrite <- (Share.comp_inv b).
apply share_lemma87.
rewrite <- Share.demorgan1.
rewrite Share.lub_commute, H0.
clear.
pose proof (Share.comp1 Share.bot).
rewrite Share.lub_commute, Share.lub_bot in H.
rewrite <- H.
rewrite Share.comp_inv.
auto.
Qed.

Lemma comp_bot: Share.comp Share.bot = Share.top.
Proof.
apply join_top_comp.
apply bot_join_eq.
Qed.

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
 generalize (Share.glb_lower1 a b);intro.
 generalize (Share.glb_lower2 a b);intro.
 generalize (Share.ord_trans _ _ _ H1 H);intro.
 generalize (Share.ord_trans _ _ _ H2 H0);intro.
 eapply Share.glb_greatest;auto.
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

Lemma glb_Rsh_not_top:
   forall sh, Share.glb Share.Rsh sh <> Share.top.
Proof.
 intros.
 intro.
 unfold Share.Rsh in H.
 destruct (Share.split Share.top) eqn:?H.
  pose proof (Share.split_disjoint _ _ _ H0).
 simpl in H.
  pose proof (Share.glb_lower1 t0 sh).
  rewrite H in H2.
  apply leq_join_sub in H2.
  destruct H2. destruct H2.
  rewrite Share.lub_commute, Share.lub_top in H3.
  subst.
  clear - H0.
  apply nonemp_split_neq2 in H0; auto.
  intro. apply identity_share_bot in H.
  contradiction Share.nontrivial.
Qed.
Arguments glb_Rsh_not_top sh _ : clear implicits.

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

Definition extern_retainer := fst (Share.split Share.Lsh).

Definition Ews (* extern_write_share *) := 
  Share.lub extern_retainer Share.Rsh.

Lemma writable_Ews: writable_share Ews.
Proof.
unfold writable_share, Ews.
apply leq_join_sub.
apply Share.lub_upper2.
Qed.

Lemma writable_Rsh: writable_share Share.Rsh.
Proof.
  unfold writable_share.
  apply join_sub_refl.
Qed.

Hint Resolve writable_Ews.

Definition Ers (* Extern read share *) := 
  Share.lub extern_retainer (fst (Share.split Share.Rsh)).

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

Lemma nonidentity_extern_retainer: ~identity extern_retainer.
Proof.
unfold extern_retainer.
intro.
destruct (Share.split Share.Lsh) eqn:?H.
simpl in H.
apply split_nontrivial' in H0; auto.
apply Lsh_nonidentity.
auto.
Qed.

Lemma glb_split_x:
  forall a, Share.glb a (fst (Share.split a)) = fst (Share.split a).
Proof.
intros.
destruct (Share.split a) eqn:H; simpl in *.
destruct (split_join _ _ _ H).
subst a.
rewrite Share.glb_commute, Share.distrib1.
rewrite H0.
rewrite Share.glb_idem.
rewrite Share.lub_bot.
auto.
Qed.

Lemma readable_Ers: readable_share Ers.
Proof.
hnf; intros.
unfold Ers in H.
unfold extern_retainer in H.
rewrite Share.distrib1 in H.
apply identity_share_bot in H.
match type of H with Share.lub ?A _ = _ => forget A as a end.
rewrite glb_split_x in H.
pose proof (Share.lub_upper2 a (fst (Share.split Share.Rsh))).
rewrite H in H0.
apply leq_join_sub in H0.
destruct H0.
apply split_identity in H0; auto.
clear - H0.
destruct (Share.split Share.Rsh) eqn:?. simpl in *.
apply identity_share_bot in H0. subst.
pose proof (Share.split_nontrivial _ _ _ Heqp).
spec H;[auto | ].
assert (identity Share.Rsh) by (rewrite H; auto).
contradiction Rsh_nonidentity.
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


Lemma join_readable1:
  forall sh1 sh2 sh3,
    join sh1 sh2 sh3 ->
    readable_share sh1 -> readable_share sh3.
Proof.
intros.
eapply readable_share_join; eauto.
Qed.

Lemma join_readable2:
  forall sh1 sh2 sh3,
    join sh1 sh2 sh3 ->
    readable_share sh2 -> readable_share sh3.
Proof.
intros.
eapply readable_share_join; eauto.
Qed.

Lemma bot_unreadable: ~readable_share Share.bot.
Proof.
intro.
unfold readable_share, nonempty_share, nonidentity in H.
apply H; clear H.
rewrite Share.glb_bot. apply bot_identity.
Qed.

Definition pure_readable_share (sh: Share.t) :=
  Share.glb Share.Lsh sh = Share.bot /\ readable_share sh.

Definition rshare := sig pure_readable_share.

Definition readable_part: forall (sh: Share.t) (rsh: readable_share sh), rshare.
intros.
exists (Share.glb Share.Rsh sh).
split.
rewrite <- Share.glb_assoc. rewrite glb_Lsh_Rsh.
rewrite Share.glb_commute. apply Share.glb_bot.
unfold readable_share.
rewrite <- Share.glb_assoc.
rewrite Share.glb_idem.
apply rsh.
Defined.

Lemma readable_not_identity: forall sh P,
  readable_share sh -> identity sh -> P.
Proof.
 intros.
 unfold readable_share in H.
 unfold nonempty_share, nonidentity in H. contradiction H.
 apply identity_share_bot in H0; subst.
 rewrite Share.glb_bot. apply bot_identity.
Qed.
Arguments readable_not_identity sh P _ _ : clear implicits.

Lemma comp_parts:  
  forall L R : Share.t,
  Share.comp L = R ->
  forall sh: Share.t, sh = Share.lub (Share.glb L sh) (Share.glb R sh).
Proof.
intros.
subst R.
rewrite <- !(Share.glb_commute sh).
rewrite <- Share.distrib1.
rewrite Share.comp1.
rewrite Share.glb_top. auto.
Qed.

Lemma join_comp_parts:  
  forall L R : Share.t,
  Share.comp L = R ->
  forall a b c : Share.t,
  join a b c ->
  (join (Share.glb L a) (Share.glb L b) (Share.glb L c) /\
   join (Share.glb R a) (Share.glb R b) (Share.glb R c)).
Proof.
intros.
split; split.
*
rewrite (comp_parts H a) in H0.
rewrite (comp_parts H b) in H0.
rewrite (comp_parts H c) in H0.
destruct H0 as [H0 _].
pose proof (@glb_less_both
             (Share.glb L a) (Share.lub (Share.glb L a) (Share.glb R a))
             (Share.glb L b) (Share.lub (Share.glb L b) (Share.glb R b))).
apply Share.ord_antisym; [ | apply Share.bot_correct].
eapply Share.ord_trans; try apply H1; try apply Share.lub_upper1.
rewrite H0. apply Share.ord_refl.
*
destruct H0 as [_ H0].
subst c.
rewrite <- Share.distrib1. auto.
*
rewrite (comp_parts H a) in H0.
rewrite (comp_parts H b) in H0.
rewrite (comp_parts H c) in H0.
destruct H0 as [H0 _].
pose proof (@glb_less_both
             (Share.glb R a) (Share.lub (Share.glb L a) (Share.glb R a))
             (Share.glb R b) (Share.lub (Share.glb L b) (Share.glb R b))).
apply Share.ord_antisym; [ | apply Share.bot_correct].
eapply Share.ord_trans; try apply H1; try apply Share.lub_upper2.
rewrite H0. apply Share.ord_refl.
*
destruct H0 as [_ H0].
subst c.
rewrite <- Share.distrib1. auto.
Qed.

Lemma join_pure_readable:
  forall sh1 sh2 sh3,
    join sh1 sh2 sh3 ->
    pure_readable_share sh1 -> 
    pure_readable_share sh2 -> 
    pure_readable_share sh3.
Proof.
intros.
destruct H0,H1.
split.
destruct (join_comp_parts comp_Lsh_Rsh H).
rewrite H0,H1 in *. apply join_unit1_e in H4; auto.
eapply readable_share_join; eauto.
Qed.


Instance Join_rshare: Join rshare :=
  fun a b c => join (proj1_sig a) (proj1_sig b) (proj1_sig c).

Instance Perm_rshare: Perm_alg rshare. (* move me! *)
Proof.
  unfold rshare.
  constructor; intros.
*
  destruct z, z'. apply exist_ext.
  do 2 red in H, H0. simpl in *. eapply join_eq; eauto.
* 
  destruct a,b,c,d,e; do 2 red in H,H0. simpl in *.
  destruct (join_assoc H H0) as [a [? ?]].
  assert (pure_readable_share a).
  eapply join_pure_readable; eauto.
  exists (exist pure_readable_share _ H3).
  split; eassumption.
*
  destruct a,b,c; do 2 red in H|-*; simpl in *. apply join_comm; auto.
*
  destruct a,a',b,b'; do 2 red in H,H0; simpl in *.
  apply exist_ext.
  eapply join_positivity; eauto.
Qed.

Lemma dec_readable sh : {readable_share sh}+{~readable_share sh}.
Proof.
unfold readable_share, nonempty_share, nonidentity.
destruct (dec_share_identity (Share.glb Share.Rsh sh));[right|left].
intro. contradiction.
auto.
Defined.

Lemma dec_pure_readable sh : {pure_readable_share sh}+{~pure_readable_share sh}.
Proof.
unfold pure_readable_share.
apply sumbool_dec_and.
apply eq_dec.
unfold readable_share, nonempty_share, nonidentity.
destruct (dec_share_identity (Share.glb Share.Rsh sh));[right|left].
intro. contradiction.
auto.
Defined.

Lemma dec_share_identity': forall sh: Share.t, Decidable.decidable (identity sh).
Proof.
intros.
destruct (dec_share_identity sh); [left|right]; auto.
Qed.

Lemma not_not_share_identity: forall sh: Share.t,
  ~ ~ (identity sh) -> identity sh.
Proof.
intros.
 apply (Decidable.not_not _ (dec_share_identity' _)). auto.
Qed.

Lemma join_readable_part_eq:
  forall sh1 (rsh1: readable_share sh1)
         sh2 (nsh2: ~readable_share sh2)
         sh3 (rsh3: readable_share sh3),
        join sh1 sh2 sh3 -> 
        readable_part rsh1 = readable_part rsh3.
Proof.
 intros.
 apply exist_ext.
 apply not_not_share_identity in nsh2.
 destruct H. subst sh3.
 apply identity_share_bot in nsh2.
 rewrite Share.distrib1. rewrite nsh2. rewrite Share.lub_bot.
 auto.
Qed.

Lemma join_readable_part:
  forall sh1 (rsh1: readable_share sh1) sh2 (rsh2: readable_share sh2) sh3 (rsh3: readable_share sh3),
   join sh1 sh2 sh3 ->
  join (readable_part rsh1) (readable_part rsh2)(readable_part rsh3).
Proof.
intros.
red. red. simpl.
destruct H. subst.
split.
rewrite Share.glb_assoc. rewrite (Share.glb_commute sh1).
rewrite <- Share.glb_assoc.
rewrite <- (Share.glb_assoc Share.Rsh).
rewrite Share.glb_idem. rewrite Share.glb_assoc.
rewrite (Share.glb_commute sh2). rewrite H.
apply Share.glb_bot.
rewrite <- Share.distrib1. auto.
Qed.

Lemma share_self_join_bot:
  forall sh: Share.t, join sh sh sh -> sh = Share.bot.
Proof.
 intros.
  destruct H.
  rewrite Share.glb_idem in H. auto.
Qed.

Definition retainer_part (sh: Share.t) := Share.glb Share.Lsh sh.

Lemma retainer_part_nonreadable:
  forall sh, ~readable_share (retainer_part sh).
Proof.
 intros.
 unfold readable_share, retainer_part, nonempty_share, nonidentity.
 intro. apply H; clear H.
 rewrite <- Share.glb_assoc.
 rewrite (Share.glb_commute Share.Rsh). 
 rewrite glb_Lsh_Rsh.
 rewrite Share.glb_commute, Share.glb_bot.
 apply bot_identity.
Qed.
Arguments retainer_part_nonreadable: clear implicits.

Lemma readable_share_lub:
 forall a b: Share.t, readable_share b -> readable_share (Share.lub a b).
Proof.
intros.
do 3 red in H|-*.
contradict H.
apply identity_share_bot in H.
rewrite Share.distrib1 in H.
apply lub_bot_e in H. destruct H.
rewrite H0.
apply bot_identity.
Qed.

Lemma retainer_part_join: forall sh1 sh2 sh3, 
  join sh1 sh2 sh3 -> join (retainer_part sh1) (retainer_part sh2) (retainer_part sh3).
Proof.
intros.
 unfold retainer_part.
 destruct H; subst; simpl  in *; split.
 rewrite Share.glb_assoc. rewrite (Share.glb_commute sh1).
 rewrite <- Share.glb_assoc. rewrite <- Share.glb_assoc. rewrite Share.glb_idem.
 rewrite Share.glb_assoc. rewrite (Share.glb_commute sh2). rewrite H. 
 apply Share.glb_bot.
 rewrite <- Share.distrib1. auto.
Qed.

Lemma not_readable_Rsh_part:
 forall sh, ~ readable_share sh -> Share.glb Share.Rsh sh = Share.bot.
Proof.
intros.
apply not_not_share_identity in H.
apply identity_share_bot in H. auto.
Qed.

Lemma join_parts1:
  forall L R (HC: Share.comp L = R) sh1 sh2 sh,         
         join sh1 sh2 (Share.glb L sh) ->
         Share.glb L sh1 = sh1 /\
         Share.glb R sh1 = Share.bot.
Proof.
intros.
cut (Share.glb L sh1 = sh1).
*
intro. split; auto.
rewrite <- H0.
rewrite <- Share.glb_assoc.
rewrite (Share.glb_commute R).
subst R. rewrite Share.comp2.
rewrite Share.glb_commute.
apply Share.glb_bot.
*
assert (Share.Ord sh1 L).
apply Share.ord_trans with (Share.glb L sh).
apply leq_join_sub.
exists sh2; auto.
apply Share.glb_lower1.
clear H.
apply Share.ord_spec1 in H0.
symmetry.
rewrite Share.glb_commute.
auto.
Qed.

Lemma join_parts:
  forall L R (HC: Share.comp L = R) sh1 sh2 sh,         
         join sh1 sh2 (Share.glb L sh) ->
         Share.glb L sh1 = sh1 /\
         Share.glb R sh1 = Share.bot /\
         Share.glb L sh2 = sh2 /\
         Share.glb R sh2 = Share.bot.
Proof.
intros.
destruct (join_parts1 HC H).
destruct (join_parts1 HC (join_comm H)).
split3; auto.
Qed.

Lemma comp_Rsh_Lsh: Share.comp Share.Rsh = Share.Lsh.
Proof.
rewrite <- (Share.comp_inv Share.Lsh).
f_equal. symmetry. apply comp_Lsh_Rsh.
Qed.

Lemma glb_twice: forall a b, Share.glb a (Share.glb a b) = Share.glb a b.
Proof.
intros. rewrite <- Share.glb_assoc. rewrite Share.glb_idem; auto.
Qed.

Lemma glb_Lsh_Rsh':
  forall sh, Share.glb Share.Lsh (Share.glb Share.Rsh sh) = Share.bot.
Proof.
intros.
rewrite <- Share.glb_assoc. rewrite glb_Lsh_Rsh.
rewrite Share.glb_commute; apply Share.glb_bot.
Qed.

Lemma comp_parts_join:
 forall L R (HC: Share.comp L = R) a b c,
  join (Share.glb L a) (Share.glb L b) (Share.glb L c) ->
  join (Share.glb R a) (Share.glb R b) (Share.glb R c) ->
  join a b c.
Proof.
intros.
subst R.
split.
*
destruct H,H0.
clear H1 H2.
rewrite <- (Share.glb_top a), <- (Share.glb_commute Share.top).
rewrite <- (Share.comp1 L).
rewrite !(Share.glb_commute (Share.lub _ _)).
rewrite !Share.distrib1.
rewrite <- (Share.glb_top b), <- (Share.glb_commute Share.top).
rewrite <- (Share.comp1 L).
rewrite !(Share.glb_commute _ b).
rewrite (Share.distrib1 b).
rewrite !(Share.glb_commute a).
rewrite !(Share.glb_commute b).
pose proof (Share.glb_lower1 L a).
pose proof (Share.glb_lower1 L b).
pose proof (Share.glb_lower2 a (Share.comp L)). rewrite Share.glb_commute in H3.
pose proof (Share.glb_lower2 b (Share.comp L)). rewrite Share.glb_commute in H4.
forget (Share.glb L a) as al.
forget (Share.glb (Share.comp L) a) as ar.
forget (Share.glb L b) as bl.
forget (Share.glb (Share.comp L) b) as br.
rewrite Share.distrib1.
rewrite (Share.glb_commute _ bl).
rewrite Share.distrib1.
rewrite Share.glb_commute. rewrite H.
rewrite (Share.lub_commute Share.bot), Share.lub_bot.
rewrite (Share.glb_commute _ br).
rewrite Share.distrib1.
rewrite (Share.glb_commute br ar). rewrite H0.
rewrite Share.lub_bot.
apply Share.ord_spec1 in H1.
apply Share.ord_spec1 in H2.
apply Share.ord_spec1 in H3.
apply Share.ord_spec1 in H4.
rewrite H1,H2,H3,H4.
clear.
rewrite Share.glb_assoc. rewrite (Share.glb_commute ar). rewrite <- (Share.glb_assoc L).
rewrite (Share.comp2 L).
rewrite (Share.glb_commute Share.bot). rewrite Share.glb_bot.
rewrite Share.glb_bot.
rewrite (Share.lub_commute Share.bot). rewrite Share.lub_bot.
rewrite Share.glb_assoc. rewrite (Share.glb_commute al).
rewrite <- (Share.glb_assoc (Share.comp L)).
rewrite (Share.glb_commute (Share.comp L)).
rewrite (Share.comp2 L). rewrite (Share.glb_commute Share.bot). rewrite Share.glb_bot.
apply Share.glb_bot.
*
destruct H,H0.
clear H H0.
rewrite <- (Share.glb_top c).
rewrite <- (Share.comp1 L).
rewrite Share.distrib1.
rewrite !(Share.glb_commute c).
rewrite <- H1. rewrite <- H2.
rewrite Share.lub_assoc.
rewrite <- (Share.lub_assoc (Share.glb L b)).
rewrite (Share.lub_commute (Share.glb L b)).
rewrite Share.lub_assoc.
rewrite <- Share.lub_assoc.
f_equal.
rewrite !(Share.glb_commute _ a).
rewrite <- Share.distrib1.
rewrite (Share.comp1 L).
rewrite Share.glb_top.
auto.
rewrite !(Share.glb_commute _ b).
rewrite <- Share.distrib1.
rewrite (Share.comp1 L).
rewrite Share.glb_top.
auto.
Qed.


Lemma left_right_join:
 forall a b c,
  join (Share.glb Share.Lsh a) (Share.glb Share.Lsh b) (Share.glb Share.Lsh c) ->
  join (Share.glb Share.Rsh a) (Share.glb Share.Rsh b) (Share.glb Share.Rsh c) ->
  join a b c.
Proof.
apply comp_parts_join.
apply comp_Lsh_Rsh.
Qed.

Lemma lub_bot': forall sh, Share.lub Share.bot sh = sh.
Proof.
intros.
rewrite Share.lub_commute.
apply Share.lub_bot.
Qed.

Lemma glb_Rsh_Lsh: Share.glb Share.Rsh Share.Lsh = Share.bot.
Proof.
rewrite Share.glb_commute.
apply glb_Lsh_Rsh.
Qed.

Lemma join_writable1: forall sh1 sh2 sh,
   join sh1 sh2 sh -> writable_share sh1 -> writable_share sh.
Proof.
intros.
red in H0|-*.
eapply join_sub_trans; [apply H0 | ].
exists sh2; auto.
Qed.

Lemma join_writable_readable:
  forall {sh1 sh2 sh}, 
   join sh1 sh2 sh -> writable_share sh1 -> readable_share sh2 -> False.
Proof.
intros.
red in H0,H1.
destruct H0 as [a ?].
destruct (join_assoc (join_comm H0) H) as [f [? ?]].
destruct H2.
rewrite H2 in H1.
apply H1; auto.
Qed.

Lemma writable_share_glb_Rsh:
  forall sh, writable_share sh -> writable_share (Share.glb Share.Rsh sh).
Proof.
intros.
unfold writable_share in *.
apply leq_join_sub in H.
apply leq_join_sub.
apply Share.ord_spec1.
apply Share.ord_spec1 in H.
rewrite <- H.
rewrite Share.glb_idem; auto.
Qed.

Lemma glb_split_lemma1:
  forall a b, Share.glb Share.Rsh a = Share.glb Share.Rsh b ->
     Share.glb Share.Rsh (fst (Share.split a)) =
     Share.glb Share.Rsh (fst (Share.split b)).
Proof.
intros.
Abort.  (* Probably true, but not absolutely needed *)

Lemma glb_split_lemma2:
  forall a b, Share.glb Share.Rsh a = Share.glb Share.Rsh b ->
     Share.glb Share.Rsh (snd (Share.split a)) =
     Share.glb Share.Rsh (snd (Share.split b)).
Proof.
Abort.  (* Probably true, but not absolutely needed *)

Lemma fst_split_glb_orthogonal: forall sh : share,
identity (Share.glb Share.Rsh (fst (Share.split sh))) ->
identity (Share.glb Share.Rsh sh).
Proof.
Abort. (* not true? *)

Lemma snd_split_glb_orthogonal: forall sh : share,
identity (Share.glb Share.Rsh (snd (Share.split sh))) ->
identity (Share.glb Share.Rsh sh).
Abort.  (* not needed? *)

(** the following lemmas are useful in the concurrency proofs *)


  Lemma writable_not_join_readable:
    forall sh1 sh2,
      joins sh1 sh2 ->
      writable_share sh1 ->
      ~ readable_share sh2.
  Proof.
    intros.
    intro.
    unfold readable_share, writable_share in *.
    destruct H0. destruct H.
    destruct (join_assoc (join_comm H0) H) as [? [? _]].
    unfold nonempty_share in H1. clear - H1 H2.
    destruct H2 as [H2 _]. rewrite H2 in H1.
    apply H1. apply bot_identity.
 Qed.

  Lemma writable_not_join_writable :
    forall sh1 sh2,
      joins sh1 sh2 ->
      writable_share sh1 ->
      ~ writable_share sh2.
   Proof.
     intros. intro.
    pose proof (writable_not_join_readable H H0).
    apply H2. auto.
   Qed.

  Lemma only_bot_joins_top:
    forall sh, joins Share.top sh -> sh = Share.bot.
  Proof.
    intros. destruct H. destruct H.
    rewrite Share.glb_commute in H. rewrite Share.glb_top in H. auto.
  Qed.

(*
  Lemma glb_Rsh_not_top:
    forall sh, ~ Share.glb Share.Rsh sh = Share.top.
  Proof.
    intros. apply glb_Rsh_not_top.
  Qed.
*)
  Lemma writable_right:
    forall sh,  writable_share (Share.glb Share.Rsh sh) ->
           writable_share sh.
  Proof.
     intros.
     unfold writable_share in *.
     apply leq_join_sub in H.
     apply leq_join_sub.
     eapply Share.ord_trans; try eassumption.
     rewrite Share.glb_commute.
     apply Share.glb_lower1.
  Qed.

Lemma join_readable_unreadable:
  forall sh1 sh2 sh3,
    join sh1 sh2 sh3 ->
    ~ writable_share sh1 ->
    ~ readable_share sh2 ->
    ~ writable_share sh3.
Proof.
 intros.
 contradict H0.
 unfold writable_share in *.
 destruct H0.
 destruct (join_comp_parts comp_Lsh_Rsh H) as [_ ?].
 destruct (join_comp_parts comp_Lsh_Rsh H0) as [_ ?].
 rewrite Share.glb_idem in H3.
 apply not_readable_Rsh_part in H1.
 rewrite H1 in H2.
 apply join_unit2_e in H2; [ | apply bot_identity].
 rewrite <- H2 in H3.
 assert (join_sub Share.Rsh (Share.glb Share.Rsh sh1)).
 eexists; eauto.
 apply leq_join_sub in H4.
 eapply leq_join_sub.
 eapply Share.ord_trans; eauto.
 apply Share.glb_lower2.
Qed.

Lemma readable_glb:
   forall sh,
     readable_share sh ->
     readable_share (Share.glb Share.Rsh sh).
 Proof.
   intros.
   unfold readable_share in *. rewrite glb_twice. auto.
 Qed.

 Lemma unreadable_glb:
   forall sh,
     ~readable_share sh ->
     ~readable_share (Share.glb Share.Rsh sh).
 Proof.
   intros.
   unfold readable_share in *. rewrite glb_twice. auto.
 Qed.

  Lemma nonreadable_emptyshare: ~ readable_share emptyshare.
  Proof.
    unfold emptyshare.
    intro.
    hnf in H.
    rewrite Share.glb_bot in H.
    apply H; auto.
  Qed.
  
Lemma join_comp_Tsh:
  forall sh, sepalg.join sh (Share.comp sh) Tsh.
Proof.
intros.
split.
apply Share.comp2.
apply Share.comp1.
Qed.
