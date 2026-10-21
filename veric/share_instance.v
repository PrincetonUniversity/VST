Set Warnings "-notation-overridden,-hiding-delimiting-key".
Require Import VST.shared.share_alg.
Set Warnings "notation-overridden,hiding-delimiting-key".
Require Import VST.msl.eq_dec.
Require Export VST.msl.shares.
Require Export VST.veric.shares.

#[export] Program Instance share_instance : ShareType share := { share_bot := Share.bot; share_top := Tsh;
  share_op a b := if eq_dec (Share.glb a b) Share.bot then Some (Share.lub a b) else None;
  share_writable := writable0_share; share_readable := readable_share }.
Next Obligation.
Proof.
  intros ??.
  rewrite Share.glb_commute Share.lub_commute //.
Qed.
Next Obligation.
Proof.
  intros *; simpl.
  do 2 (destruct (eq_dec _ _) as [?glb|]; last done).
  inversion 1; inversion 1; subst.
  rewrite Share.distrib1 in glb0; apply lub_bot_e in glb0 as [Hac ?].
  rewrite Share.glb_commute in Hac.
  destruct (eq_dec _ _); last done.
  do 2 eexists; first done.
  rewrite Share.glb_commute Share.distrib1 Share.glb_commute glb lub_bot' Share.glb_commute.
  destruct (eq_dec _ _); last done.
  rewrite (Share.lub_commute a c) Share.lub_assoc //.
Qed.
Next Obligation.
Proof.
  intros *; simpl.
  destruct (eq_dec _ _) as [glb|]; inversion 1.
  rewrite Share.distrib1.
  destruct (eq_dec (Share.glb c a) Share.bot) as [?glb|].
  - rewrite glb0 lub_bot'.
    split; repeat destruct (eq_dec _ _); auto; try congruence.
    intros [?|?]; done.
  - destruct (eq_dec _ _) as [?lub|]; last tauto.
    apply lub_bot_e in lub; tauto.
Qed.
Next Obligation.
Proof.
  intros *; simpl.
  rewrite Share.glb_commute Share.glb_bot eq_dec_refl lub_bot' //.
Qed.
Next Obligation.
Proof.
  intros *; simpl.
  do 2 (destruct (eq_dec _ _) as [?glb|]; last done).
  inversion 1; inversion 1; subst.
  eapply Share.distrib_spec; eauto; congruence.
Qed.
Next Obligation.
Proof.
  intros *; simpl.
  destruct (eq_dec _ _); inversion 1.
  apply Share.lub_top.
Qed.
Next Obligation.
Proof.
  apply readable_share_dec.
Defined.
Next Obligation.
Proof.
  intros *; simpl.
  destruct (eq_dec _ _); inversion 2.
  eapply join_writable01, H.
  rewrite /sepalg.join /Share.Join_ba; eauto.
Qed.
Next Obligation.
Proof.
  intros *; simpl.
  destruct (eq_dec _ _); inversion 2.
  rewrite Share.lub_commute; by apply readable_share_lub.
Qed.
Next Obligation.
Proof.
  apply writable0_readable.
Qed.
Next Obligation.
Proof.
  intros; simpl.
  destruct (eq_dec _ _); last done.
  eapply join_writable0_readable in H; done.
Qed.
Next Obligation.
Proof.
  apply bot_unreadable.
Qed.
Next Obligation.
Proof.
  apply writable_writable0; auto.
Qed.
Next Obligation.
Proof.
  intros *; simpl.
  destruct (eq_dec _ _); inversion 1; subst.
  intros; by apply (@join_unreadable_shares a b).
Qed.

Lemma share_op_is_join : forall a b c, share_op a b = Some c <-> sepalg.join a b c.
Proof.
  intros; rewrite /= /sepalg.join /Share.Join_ba.
  split.
  - destruct (eq_dec _ _); inversion 1; auto.
  - intros [-> ->]; rewrite eq_dec_refl //.
Qed.

Global Instance share_eq_dec : EqDecision share.
Proof. intros ??. by destruct (eq_dec x y); [left | right]. Defined.

Set Warnings "-notation-overridden,-hiding-delimiting-key".
Require Import VST.shared.dshare.
Set Warnings "notation-overridden,hiding-delimiting-key".

Global Instance dfrac_eq_dec : EqDecision dfrac.
Proof.
  rewrite /RelDecision /Decision => ??.
  decide equality; decide equality; apply share_eq_dec.
Defined.
