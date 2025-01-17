(* modified from iris.algebra.frac *)

From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.

(* parameterize by a type of shares with bot, top, readable and writable; axioms determined by need *)
(* It should be possible to instantiate this with both tree shares and nonnegative fractions. *)
Class ShareType share_type := { share_bot : share_type; share_top : share_type;
  share_op : share_type -> share_type -> option share_type;
  share_op_comm : Comm eq share_op;
  share_op_assoc a b c d e : share_op a b = Some d -> share_op c d = Some e ->
    exists f, share_op a c = Some f /\ share_op f b = Some e;
  share_op_fail a b c d : share_op a b = Some d -> share_op c d = None <->
    share_op c a = None \/ share_op c b = None;
  share_op_bot a : share_op share_bot a = Some a;
  share_op_cancel a b c d : share_op a b = Some d -> share_op a c = Some d -> b = c;
  share_op_top a b : share_op a share_top = Some b -> b = share_top;
  share_writable : share_type -> Prop;
  share_readable : share_type -> Prop;
  readable_dec a : {share_readable a} + {~share_readable a};
  writable_mono a b c : share_writable a -> share_op a b = Some c -> share_writable c;
  readable_mono a b c : share_readable a -> share_op a b = Some c -> share_readable c;
  writable_readable a : share_writable a -> share_readable a;
  writable_readable_conflict a b : share_writable a -> share_readable b -> share_op a b = None;
  unreadable_bot : ~share_readable share_bot;
  writable_top : share_writable share_top;
  join_unreadable a b c : share_op a b = Some c -> ~share_readable a -> ~share_readable b -> ~share_readable c }.

(*Global Instance share_eq_dec : EqDecision share.
Proof. intros ??. by destruct (eq_dec x y); [left | right]. Defined.*)

Inductive share_car `{ShareType} :=
| Share (sh : share_type)
| ShareBot.

Section share.

  Context `{ST : ShareType}.

  Lemma share_op_top' a b : share_op a share_top = Some b -> b = share_top /\ a = share_bot.
  Proof.
    intros.
    pose proof (share_op_top _ _ H) as ->.
    rewrite share_op_comm in H; eapply share_op_cancel in H as <-; last by rewrite share_op_comm; apply share_op_bot.
    done.
  Qed.

  Lemma readable_top : share_readable share_top.
  Proof. apply writable_readable, writable_top. Qed.

Set Warnings "-redundant-canonical-projection".
  Canonical Structure shareO := leibnizO share_car.
Set Warnings "redundant-canonical-projection".

  Global Instance share_car_inhabited : Inhabited share_car := populate ShareBot.
(*  Global Instance share_car_eq_dec : EqDecision share_car.
  Proof. solve_decision. Defined.*)

  Local Instance share_valid_instance : Valid share_car := λ x, match x with Share _ => True | _ => False end.
  Local Instance share_pcore_instance : PCore share_car := λ _, Some (Share share_bot).
  Local Instance share_op_instance : Op share_car := λ a b, match a, b with
    | Share a, Share b => match share_op a b with Some c => Share c | _ => ShareBot end
    | _, _ => ShareBot
    end.

  Lemma share_op_eq : forall a b, a ⋅ b = match a, b with
    | Share a, Share b => match share_op a b with Some c => Share c | _ => ShareBot end
    | _, _ => ShareBot
    end.
  Proof. reflexivity. Qed.

  Lemma share_op_join : forall a b z, a ⋅ b = Share z <-> exists x y, a = Share x /\ b = Share y /\ share_op x y = Some z.
  Proof.
    intros; rewrite share_op_eq; split.
    - destruct a, b; try done.
      destruct (share_op _ _) eqn: ?; try done.
      inversion 1; subst.
      by repeat eexists.
    - intros (? & ? & ? & ? & H); subst.
      rewrite H //.
  Qed.

  Lemma share_valid2_joins : forall a b, valid (a ⋅ b) <-> exists x y z, a = Share x /\ b = Share y /\ a ⋅ b = Share z /\ share_op x y = Some z.
  Proof.
    split.
    - destruct (a ⋅ b) eqn: J; last done.
      eapply share_op_join in J as (? & ? & ? & ? & ?); subst.
      repeat (eexists; eauto).
    - intros (? & ? & ? & ? & ? & Heq & J); subst.
      rewrite Heq //.
  Qed.

  Lemma share_op_equiv : forall x y z, x ⋅ y = z <->
    match z with Share c => exists a b, x = Share a /\ y = Share b /\ share_op a b = Some c
    | ShareBot => match x, y with
              | Share a, Share b => share_op a b = None
              | _, _ => True
              end
    end.
  Proof.
    intros; destruct z; first by apply share_op_join.
    rewrite share_op_eq.
    destruct x, y; try done.
    destruct (share_op _ _); done.
  Qed.

  Definition share_ra_mixin : RAMixin share_car.
  Proof.
    apply ra_total_mixin; try apply _; try done.
    - intros [x|] [y|] [z|]; try done; rewrite !share_op_eq; last by destruct (share_op _ _).
      destruct (share_op y z) eqn: Hyz, (share_op x _) eqn: Hx; try done.
      * eapply share_op_assoc in Hx as (? & Hxy & Hz); last done.
        rewrite share_op_comm in Hxy; rewrite Hxy Hz //.
      * destruct (share_op x y) eqn: Hxy; try done.
        eapply share_op_fail in Hx as [? | ?]; try done.
        { congruence. }
        rewrite share_op_comm.
        unshelve erewrite (proj2 (share_op_fail _ _ _ _ Hxy)); first done.
        rewrite share_op_comm; auto.
      * destruct (share_op s z) eqn: Hz; try done.
        rewrite share_op_comm in Hz; rewrite share_op_comm in Hx.
        eapply share_op_assoc in Hz as (? & ? & ?); last done; congruence.
    - intros [x|] [y|]; try done.
      rewrite !share_op_eq share_op_comm //.
    - intros [|]; try done.
      rewrite leibniz_equiv_iff share_op_join.
      repeat eexists.
      apply share_op_bot.
    - intros; exists (Share share_bot).
      symmetry; rewrite leibniz_equiv_iff share_op_join.
      repeat eexists.
      apply share_op_bot.
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
    destruct ((proj1 (share_valid2_joins _ _) Hv)) as (? & ? & ? & -> & -> & Hop & J).
    rewrite Heq in Hop; apply share_op_join in Hop as (? & ? & [=] & -> & J'); subst.
    eapply share_op_cancel in J; last done; by subst.
  Qed.

  Local Instance share_unit_instance : Unit share_car := Share share_bot.

  Definition share_ucmra_mixin : UcmraMixin share_car.
  Proof.
    split; try done.
    intros [|]; last done.
    rewrite leibniz_equiv_iff share_op_join.
    repeat eexists.
    apply share_op_bot.
  Qed.
  Canonical Structure shareUR := Ucmra share_car share_ucmra_mixin.

  Lemma share_core_unit (x : shareO) : core x = ε.
  Proof. done. Qed.

End share.
