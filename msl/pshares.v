(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import VST.msl.base.
Require Import VST.msl.sepalg.
Require Import VST.msl.psepalg.
Require Import VST.msl.eq_dec.
Require Import VST.msl.shares.

(** The prototypical example of a psepalg is the positive shares, which
    are just the lifted basic shares. *)
Definition pshare : Type := lifted Share.Join_ba.
Instance Join_pshare: Join pshare := @Join_lift _ _.
Instance Perm_pshare : Perm_alg pshare := Perm_lift Share.pa.
Instance Canc_pshare : Canc_alg pshare := @Canc_lift _ _ Share.ca.
Instance Disj_pshare : Disj_alg pshare := @Disj_lift _ _ Share.da.
Instance Pos_pshare : Pos_alg pshare := @Pos_lift _ _.

Definition pshare_sh : pshare -> share := @lifted_obj share Share.Join_ba.
Coercion pshare_sh : pshare >-> share.

Lemma pshare_eq_dec: forall sh1 sh2: pshare, {sh1=sh2}+{sh1<>sh2}.
Proof.
  intros.
  destruct sh1; destruct sh2.
  destruct (eq_dec x x0); [left|right].
  subst x0.
  rewrite (proof_irr n n0); auto.
  intro.
  inv H.
  contradiction n1; auto.
Qed.

Instance EqDec_pshare : EqDec pshare := pshare_eq_dec.

Definition pfullshare : pshare :=
  mk_lifted fullshare top_share_nonunit.

Lemma pfullshare_pfull : full pfullshare.
Proof with auto.
  unfold pshare.
  apply lifted_full. auto with typeclass_instances.
  apply fullshare_full.
Qed.

Lemma join_sub_pfullshare: forall (p: pshare),
  @join_sub share Share.Join_ba pfullshare p ->
  p = pfullshare.
Proof.
  intros. apply join_sub_fullshare in H. apply lifted_eq. trivial.
Qed.

Lemma pjoin_sub_pfullshare: forall (p : pshare),
  join_sub pfullshare p -> False.
Proof.
  intros.
  generalize pfullshare_pfull; intro.
  rewrite pfull_pmaximal in H0.
  generalize (H0 _ H); intro.
  destruct H. subst p.
  apply join_comm in H.
  contradiction (no_units x pfullshare).
Qed.

Lemma pshare_join_full_false1 : forall (p:pshare),
   joins pfullshare p -> False.
Proof.
  intros.
  destruct H. inv H. simpl in *. unfold fullshare in H0.
  rewrite Share.glb_commute in H0. rewrite Share.glb_top in H0.
  destruct p; simpl in *. subst. contradiction (n Share.bot). auto.
Qed.

Lemma pshare_join_full_false2 : forall (p:pshare),
   joins p pfullshare -> False.
Proof.
  intros. apply joins_comm in H. apply pshare_join_full_false1 with p; auto.
Qed.

Lemma pshare_join_full_false3: forall (p1: pshare) sh3,
  join (lifted_obj p1) Share.top sh3 -> False.
Proof.
  intros.
  destruct p1. unfold lifted_obj, pfullshare, mk_lifted, proj1_sig in H.
  destruct H. rewrite Share.glb_top in H. subst. contradiction (n Share.bot); auto.
Qed.

Lemma pshare_join_full_false4: forall (p1: pshare) sh3,
  join Share.top (lifted_obj p1) sh3 -> False.
Proof.
  intros.
  eapply pshare_join_full_false3. apply join_comm in H. eauto.
Qed.

Lemma pshare_pjoin_full_false3: forall (p1: pshare) pp sh3,
   join p1 (mk_lifted Share.top pp) sh3 -> False.
Proof.
  intros. destruct sh3.
  do 2 red in H. simpl lifted_obj in *.
 apply pshare_join_full_false3 in H. trivial.
Qed.

Lemma pshare_pjoin_full_false4: forall (p1: pshare) pp sh3,
   join (mk_lifted Share.top pp) p1 sh3 -> False.
Proof.
  intros. destruct sh3.
  do 2 red in H. simpl lifted_obj in *.
  apply pshare_join_full_false4 in H. trivial.
Qed.

Ltac pfullshare_join :=
  elimtype False;
  solve [ eapply pshare_join_full_false1; eauto
    | eapply pshare_join_full_false2; eauto
    | eapply pshare_join_full_false3; eauto
    | eapply pshare_join_full_false4; eauto
    | eapply pshare_pjoin_full_false3; eauto
    | eapply pshare_pjoin_full_false4; eauto
  ].

Program Definition split_pshare (sh: pshare) : pshare * pshare :=
  (mk_lifted (fst (Share.split sh)) _, mk_lifted (snd (Share.split sh)) _).
Next Obligation.
Proof.
  intros.
  case_eq (Share.split (proj1_sig sh)); simpl.
  intros.
  generalize (split_nontrivial' _ _ _ H); intro.
  intros ? ?. apply unit_identity in H1. destruct sh; simpl in H0.
  assert (identity x0) by auto. contradiction (n x0).
  apply identity_unit_equiv in H2; auto.
Qed.
Next Obligation.
Proof.
  intros.
  case_eq (Share.split (proj1_sig sh)); simpl.
  intros.
  generalize (split_nontrivial' _ _ _ H); intro.
  intros ? ?. apply unit_identity in H1. destruct sh; simpl in H0.
  assert (identity x0) by auto. contradiction (n x0).
  apply identity_unit_equiv in H2; auto.
Qed.

Lemma psplit_split: forall psh psha pshb,
  (split_pshare psh = (psha, pshb)) =
  (Share.split (lifted_obj psh) = (lifted_obj psha, lifted_obj pshb)).
Proof.
  unfold split_pshare, lifted_obj.
  intros. apply prop_ext. split; intro.
  inversion H.
  apply injective_projections; auto.
  apply injective_projections; apply lifted_eq; simpl; rewrite H; auto.
Qed.

Lemma psplit_pjoin: forall psh psha pshb,
  split_pshare psh = (psha, pshb) ->
   join psha pshb psh.
Proof.
  intros.
  rewrite psplit_split in H.
  apply split_join in H.
  trivial.
Qed.

Lemma pshare_split_neq1: forall psh psh1 psh2, split_pshare psh = (psh1, psh2) -> psh1 <> psh.
Proof.
  intros.
  apply psplit_pjoin in H.
  intro contra. subst psh1.
  apply  join_comm in H.
  apply pjoin_unit in H. trivial.
Qed.

Lemma pshare_split_neq2: forall psh psh1 psh2, split_pshare psh = (psh1, psh2) -> psh2 <> psh.
Proof.
  intros.
  apply psplit_pjoin in H.
  intro contra. subst psh2.
  apply pjoin_unit in H. trivial.
Qed.

Definition pLhalf : pshare := fst (split_pshare pfullshare).
Definition pRhalf : pshare := snd (split_pshare pfullshare).

Lemma pleftright :  join pLhalf pRhalf pfullshare.
Proof.
  apply psplit_pjoin.
  trivial.
Qed.

Lemma pshare_nonunit: forall sh: pshare, nonunit (pshare_sh sh).
Proof. repeat intro. destruct sh; simpl in *. apply n in H. auto.
Qed.

Lemma pshare_not_identity: forall sh: pshare, ~ identity (pshare_sh sh).
Proof. intros. apply nonunit_nonidentity. apply pshare_nonunit.
Qed.
