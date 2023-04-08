(* modified from iris.algebra.frac *)

From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import VST.msl.eq_dec.
Require Export VST.msl.shares.
Require Export VST.veric.shares.

Global Instance share_eq_dec : EqDecision share.
Proof. intros ??. by destruct (eq_dec x y); [left | right]. Defined.

Section share.
  Canonical Structure shareO := leibnizO share.

  Local Instance share_valid_instance : Valid share := λ x, x <> Share.bot.
  Local Instance share_pcore_instance : PCore share := λ _, None.
  Local Instance share_op_instance : Op share := λ a b,
    if eq_dec a Share.bot then Share.bot else if eq_dec b Share.bot then Share.bot else
    if eq_dec (Share.glb a b) Share.bot then Share.lub a b else Share.bot.

  Lemma share_op_eq : forall a b, a ⋅ b = if eq_dec a Share.bot then Share.bot else if eq_dec b Share.bot then Share.bot else
    if eq_dec (Share.glb a b) Share.bot then Share.lub a b else Share.bot.
  Proof. reflexivity. Qed.

  Lemma share_op_join : forall x y z, z <> Share.bot -> x ⋅ y = z <-> x <> Share.bot /\ y <> Share.bot /\ sepalg.join x y z.
  Proof.
    intros; rewrite share_op_eq; split.
    - repeat (destruct eq_dec; intros; subst; try contradiction).
      repeat split; auto.
    - intros (? & ? & []); subst.
      repeat (destruct eq_dec; try contradiction).
      reflexivity.
  Qed.

  Lemma share_valid2_joins : forall x y, valid (x ⋅ y) <-> x <> Share.bot /\ y <> Share.bot /\ sepalg.join x y (x ⋅ y).
  Proof.
    split.
    - intros J.
      eapply share_op_join in J as [(? & ? & ?) _]; first done.
      repeat (eexists; eauto).
    - intros (? & ? & J).
      intros X; rewrite X in J; apply join_Bot in J as []; contradiction.
  Qed.

  Lemma share_op_equiv : forall x y z, x ⋅ y = z <->
    if eq_dec z Share.bot then x = Share.bot \/ y = Share.bot \/ Share.glb x y <> Share.bot
    else x <> Share.bot /\ y <> Share.bot /\ sepalg.join x y z.
  Proof.
    intros; destruct eq_dec; last by apply share_op_join.
    subst; rewrite share_op_eq.
    repeat (destruct eq_dec; subst; try tauto).
    split; try tauto.
    intros ?%lub_bot_e; tauto.
  Qed.

  Definition share_ra_mixin : @RAMixin share (ofe_equiv shareO) _ _ _.
  Proof.
    split; try apply _; try done.
    - unfold share; intros ???; rewrite !share_op_eq; simpl.
      destruct (eq_dec x Share.bot); rewrite ?eq_dec_refl; try done.
      destruct (eq_dec y Share.bot); rewrite ?eq_dec_refl; try done.
      destruct (eq_dec z Share.bot); rewrite ?eq_dec_refl; try done.
      { repeat destruct eq_dec; done. }
      destruct (eq_dec (Share.glb y z) Share.bot), (eq_dec (Share.glb x y) Share.bot); rewrite ?eq_dec_refl; try done.
      * destruct (eq_dec (Share.lub y z)); [apply lub_bot_e in e1 as []; contradiction|].
        destruct (eq_dec (Share.lub x y)); [apply lub_bot_e in e1 as []; contradiction|].
        by rewrite (Share.glb_commute _ z) !Share.distrib1 !(Share.glb_commute z) e e0 Share.lub_bot lub_bot' Share.lub_assoc.
      * destruct (eq_dec (Share.lub y z)); [apply lub_bot_e in e0 as []; contradiction|].
        destruct (eq_dec (Share.glb x (Share.lub y z)) Share.bot); auto.
        rewrite Share.distrib1 in e0; apply lub_bot_e in e0 as []; contradiction.
      * destruct (eq_dec (Share.lub x y)); [apply lub_bot_e in e0 as []; contradiction|].
        destruct (eq_dec (Share.glb (Share.lub x y) z) Share.bot); auto.
        rewrite Share.glb_commute Share.distrib1 in e0; apply lub_bot_e in e0 as [].
        rewrite Share.glb_commute in H0; contradiction.
    - unfold share; intros ??; rewrite !share_op_eq; simpl.
      destruct (eq_dec x Share.bot), (eq_dec y Share.bot); try reflexivity.
      rewrite (Share.glb_commute y x) (Share.lub_commute y x); reflexivity.
    - intros ????; subst.
      by rewrite share_op_eq eq_dec_refl in H.
  Qed.
  Canonical Structure shareR := discreteR shareO share_ra_mixin.

  Global Instance share_cmra_discrete : CmraDiscrete shareR.
  Proof. apply discrete_cmra_discrete. Qed.
  Global Instance share_full_exclusive : Exclusive(A := shareR) Tsh.
  Proof. intros p Hnone. contradiction Hnone. rewrite share_op_eq.
    repeat destruct eq_dec; try done.
    rewrite Share.glb_commute Share.glb_top in e; contradiction.
  Qed.
  Global Instance share_cancelable (q : shareR) : Cancelable q.
  Proof. intros n p1 p2 Hv. rewrite !share_op_eq in Hv |- *.
    unfold share in *.
    repeat destruct eq_dec; try done.
    inversion 1; f_equal; eapply Share.distrib_spec; eauto; congruence.
  Qed.
  Global Instance share_id_free (q : shareR) : IdFree q.
  Proof. intros p Hq.
    intros (? & ? & J)%share_op_join; subst; try done.
    apply sepalg.join_comm, sepalg.unit_identity, identity_share_bot in J; contradiction.
  Qed.

  Lemma Tsh_valid : valid Tsh.
  Proof.
    inversion 1; contradiction Share.nontrivial.
  Qed.

  Lemma Tsh_validN n : validN(A := shareR) n Tsh.
  Proof.
    apply Tsh_valid.
  Qed.

End share.

#[global] Hint Resolve Tsh_valid Tsh_validN : core.
