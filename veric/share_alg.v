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
  Inductive share_car :=
  | Share (sh : share)
  | ShareBot.

  Canonical Structure shareO := leibnizO share_car.

  Global Instance share_car_inhabited : Inhabited share_car := populate ShareBot.
  Global Instance share_car_eq_dec : EqDecision share_car.
  Proof. solve_decision. Defined.

  Local Instance share_valid_instance : Valid share_car := λ x, match x with Share _ => True | _ => False end.
  Local Instance share_pcore_instance : PCore share_car := λ _, Some (Share Share.bot).
  Local Instance share_op_instance : Op share_car := λ a b, match a, b with
    | Share a, Share b => if eq_dec (Share.glb a b) Share.bot then Share (Share.lub a b) else ShareBot
    | _, _ => ShareBot
    end.

  Lemma share_op_eq : forall a b, a ⋅ b = match a, b with
    | Share a, Share b => if eq_dec (Share.glb a b) Share.bot then Share (Share.lub a b) else ShareBot
    | _, _ => ShareBot
    end.
  Proof. reflexivity. Qed.

  Lemma share_op_join : forall a b z, a ⋅ b = Share z <-> exists x y, a = Share x /\ b = Share y /\ sepalg.join x y z.
  Proof.
    intros; rewrite share_op_eq; split.
    - destruct a, b; try done.
      destruct eq_dec; try done.
      inversion 1; subst.
      by repeat eexists.
    - intros (? & ? & ? & ? & ? & ?); subst.
      repeat (destruct eq_dec; try contradiction).
      reflexivity.
  Qed.

  Lemma share_valid2_joins : forall a b, valid (a ⋅ b) <-> exists x y z, a = Share x /\ b = Share y /\ a ⋅ b = Share z /\ sepalg.join x y z.
  Proof.
    split.
    - destruct (a ⋅ b) eqn: J; last done.
      eapply share_op_join in J as (? & ? & ? & ? & ?); subst.
      repeat (eexists; eauto).
    - intros (? & ? & ? & ? & ? & Heq & J); subst.
      rewrite Heq //.
  Qed.

  Lemma share_op_equiv : forall x y z, x ⋅ y = z <->
    match z with Share c => exists a b, x = Share a /\ y = Share b /\ sepalg.join a b c
    | ShareBot => match x, y with
              | Share a, Share b => Share.glb a b <> Share.bot
              | _, _ => True
              end
    end.
  Proof.
    intros; destruct z; first by apply share_op_join.
    rewrite share_op_eq.
    destruct x, y; try done.
    destruct eq_dec; done.
  Qed.

  Definition share_ra_mixin : RAMixin share_car.
  Proof.
    apply ra_total_mixin; try apply _; try done.
    - intros [x|] [y|] [z|]; try done; rewrite !share_op_eq; last by destruct eq_dec.
      do 2 destruct eq_dec; try done.
      * rewrite Share.distrib1 in e0; apply lub_bot_e in e0 as (Hglb1 & Hglb2).
        rewrite Hglb1 eq_dec_refl Share.glb_commute Share.distrib1 Share.glb_commute Hglb2 Share.glb_commute e.
        rewrite Share.lub_bot eq_dec_refl Share.lub_assoc //.
      * rewrite Share.distrib1 in n.
        repeat (destruct eq_dec; try done).
        rewrite Share.glb_commute Share.distrib1 in e1.
        apply lub_bot_e in e1 as (Hglb1 & ?).
        rewrite Share.glb_commute in Hglb1; rewrite e0 Hglb1 Share.lub_bot // in n.
      * destruct eq_dec; try done.
        rewrite Share.glb_commute Share.distrib1 in e0.
        apply lub_bot_e in e0 as (? & Hglb2).
        rewrite Share.glb_commute // in Hglb2.
    - intros [x|] [y|]; try done.
      rewrite !share_op_eq.
      rewrite Share.glb_commute Share.lub_commute //.
    - intros [|]; try done.
      rewrite leibniz_equiv_iff share_op_join; eauto.
    - intros; exists (Share Share.bot).
      symmetry; rewrite leibniz_equiv_iff share_op_join; eauto.
    - intros ?? (? & ? & ? & -> & -> & ? & ?)%share_valid2_joins; hnf; eauto.
  Qed.
  Canonical Structure shareR := discreteR share_car share_ra_mixin.

  Global Instance share_cmra_total : CmraTotal shareR.
  Proof. hnf; eauto. Qed.
  Global Instance share_cmra_discrete : CmraDiscrete shareR.
  Proof. apply discrete_cmra_discrete. Qed.
  Global Instance share_cancelable (q : shareR) : Cancelable q.
  Proof.
    apply: discrete_cancelable.
    intros p1 p2 Hv Heq.
    destruct ((proj1 (share_valid2_joins _ _) Hv)) as (? & ? & ? & -> & -> & Hop & J%sepalg.join_comm).
    rewrite Heq in Hop; apply share_op_join in Hop as (? & ? & [=] & -> & ?%sepalg.join_comm); subst.
    eapply sepalg.join_canc in J; last done; by subst.
  Qed.

  Local Instance share_unit_instance : Unit share_car := Share Share.bot.

  Definition share_ucmra_mixin : UcmraMixin share_car.
  Proof.
    split; try done.
    intros [|]; last done.
    rewrite leibniz_equiv_iff share_op_join; eauto.
  Qed.
  Canonical Structure shareUR := Ucmra share_car share_ucmra_mixin.

  Lemma share_core_unit (x : shareO) : core x = ε.
  Proof. done. Qed.

End share.
