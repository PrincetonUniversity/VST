Require Import msl.Coqlib2.
Require Import msl.sepalg.
Require Import msl.shares.
Require Import msl.pshares.
Require Import veric.coqlib4.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_ops.
Require Import concurrency.permjoin_def.

Lemma join_bot_bot_eq sh :
  sepalg.join Share.bot Share.bot sh ->
  sh = Share.bot.
Proof.
  intros j.
  apply (join_eq j  (z' := Share.bot) (join_bot_eq Share.bot)).
Qed.

Lemma join_to_bot_l {sh1 sh2} :
  sepalg.join sh1 sh2 Share.bot ->
  sh1 = Share.bot.
Proof.
  intros [H H'].
  apply shares.lub_bot_e in H'.
  apply H'.
Qed.

Lemma join_to_bot_r {sh1 sh2} :
  sepalg.join sh1 sh2 Share.bot ->
  sh2 = Share.bot.
Proof.
  intros [H H'].
  apply shares.lub_bot_e in H'.
  apply H'.
Qed.

Lemma join_top_l {sh2 sh3} :
  sepalg.join Share.top sh2 sh3 ->
  sh2 = Share.bot.
Proof.
  intros [H H'].
  rewrite Share.glb_commute in H.
  rewrite Share.glb_top in H.
  auto.
Qed.
         
Lemma join_top {sh2 sh3} :
  sepalg.join Share.top sh2 sh3 ->
  sh3 = Share.top.
Proof.
  intros [H H'].
  rewrite Share.lub_commute in H'.
  rewrite Share.lub_top in H'.
  auto.
Qed.

Lemma join_pfullshare {sh2 sh3 : pshare} : ~sepalg.join pfullshare sh2 sh3.
Proof.
  intros [H H'].
  unfold pfullshare in *.
  unfold fullshare in *.
  simpl in *.
  rewrite Share.glb_commute in H.
  rewrite Share.glb_top in H.
  destruct sh2.
  simpl in *.
  subst.
  destruct (shares.not_nonunit_bot Share.bot).
  tauto.
Qed.

Lemma join_with_bot_r sh1 sh2 : join sh1 Share.bot sh2 -> sh1 = sh2.
Proof.
  intros [H H'].
  rewrite Share.lub_bot in H'.
  auto.
Qed.

Lemma join_with_bot_l sh1 sh2 : join Share.bot sh1 sh2 -> sh1 = sh2.
  intros [H H'].
  rewrite Share.lub_commute in H'.
  rewrite Share.lub_bot in H'.
  auto.
Qed.

Lemma join_top_r sh1 sh3 : join sh1 Share.top sh3 -> sh1 = Share.bot.
Proof.
  intros [H H'].
  rewrite Share.glb_top in H.
  auto.
Qed.

Lemma join_pshare_top_l (p1 p2 p3 : pshare) :
  @join pshare _ p1 p2 p3 ->
  pshare_sh p1 <> Share.top.
Proof.
  destruct p1; simpl in *.
  intros [H H'] ->.
  simpl in *.
  destruct p2 as [x n0]; simpl in *.
  rewrite Share.glb_commute in H.
  rewrite Share.glb_top in H.
  subst x.
  simpl in *.
  subst.
  destruct (shares.not_nonunit_bot Share.bot).
  tauto.
Qed.

Lemma join_pshare_top_r (p1 p2 p3 : pshare) :
  @join pshare _ p1 p2 p3 ->
  pshare_sh p2 <> Share.top.
Proof.
  intros j.
  apply join_comm in j.
  apply join_pshare_top_l in j; auto.
Qed.

Lemma join_permjoin r1 r2 r3 :
  join r1 r2 r3 ->
  permjoin (perm_of_res r1) (perm_of_res r2) (perm_of_res r3).
Proof.
  destruct r1 as [t1 | t1 p1 k1 pp1 | k1 pp1];
    destruct r2 as [t2 | t2 p2 k2 pp2 | k2 pp2];
    destruct r3 as [t3 | t3 p3 k3 pp3 | k3 pp3].
  all: intros j; inversion j; subst.
  all: simpl.
  all: repeat if_tac; try constructor.
  all: subst.
  all: try pose proof join_bot_bot_eq _ RJ.
  all: try pose proof join_with_bot_l _ _ RJ.
  all: try pose proof join_with_bot_r _ _ RJ.
  all: try pose proof join_to_bot_l RJ.
  all: try pose proof join_to_bot_r RJ.
  all: subst.
  all: try congruence.
  all: try destruct k3.
  all: try constructor.
  all: unfold perm_of_sh; repeat if_tac; subst.
  all: try pose proof @join_top_l _ _ RJ.
  all: try pose proof @join_top_r _ _ RJ.
  all: subst.
  all: try constructor.
  all: try pose proof @join_top_l _ _ RJ.
  all: try pose proof @join_top_r _ _ RJ.
  all: try congruence.
  all: try pose proof join_to_bot_l RJ.
  all: try pose proof join_to_bot_r RJ.
  all: subst.
  all: try congruence.
  all: try constructor.
  all: try solve [edestruct Share.nontrivial; eauto].
  all: exfalso.
  all: try solve [edestruct Abs.pshare_sh_bot; eauto].
  all: try solve [eapply join_pshare_top_l; eauto].
  all: try solve [eapply join_pshare_top_r; eauto].
Qed.

Lemma join_permjoin_lock
  : forall r1 r2 r3 ,
    sepalg.join r1 r2 r3 ->
    permjoin_def.permjoin
      (perm_of_res_lock r1)
      (perm_of_res_lock r2)
      (perm_of_res_lock r3).
Proof. 
  destruct r1 as [t1 | t1 p1 k1 pp1 | k1 pp1];
    destruct r2 as [t2 | t2 p2 k2 pp2 | k2 pp2];
    destruct r3 as [t3 | t3 p3 k3 pp3 | k3 pp3].
  all: intros j; inversion j; subst.
  all: simpl.
  all: repeat if_tac; try constructor.
  all: subst.
  all: try pose proof join_bot_bot_eq _ RJ.
  all: try pose proof join_with_bot_l _ _ RJ.
  all: try pose proof join_with_bot_r _ _ RJ.
  all: try pose proof join_to_bot_l RJ.
  all: try pose proof join_to_bot_r RJ.
  all: subst.
  all: try congruence.
  all: try destruct k3.
  all: try constructor.
  all: unfold perm_of_sh; repeat if_tac; subst.
  all: try pose proof @join_top_l _ _ RJ.
  all: try pose proof @join_top_r _ _ RJ.
  all: subst.
  all: try constructor.
  all: try pose proof @join_top_l _ _ RJ.
  all: try pose proof @join_top_r _ _ RJ.
  all: try congruence.
  all: try pose proof join_to_bot_l RJ.
  all: try pose proof join_to_bot_r RJ.
  all: subst.
  all: try congruence.
  all: try constructor.
  all: try solve [edestruct Share.nontrivial; eauto].
  all: exfalso.
  all: try solve [edestruct Abs.pshare_sh_bot; eauto].
  all: try solve [eapply join_pshare_top_l; eauto].
  all: try solve [eapply join_pshare_top_r; eauto].
Qed.