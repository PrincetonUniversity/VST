(* modified from iris.algebra.frac *)

From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import VST.msl.eq_dec.
Require Export VST.msl.shares.
Require Import VST.veric.shares.

(* modified from iris.algebra.dfrac *)
Declare Custom Entry dfrac.
Notation "{ dq }" := (dq) (in custom dfrac at level 1, dq constr).
Notation "□" := None (in custom dfrac).
Notation "{# q }" := (Some q) (in custom dfrac at level 1, q constr).
Notation "" := (Some Tsh) (in custom dfrac).

Section share.
  Canonical Structure shareO := leibnizO (option share).

  Local Instance share_valid_instance : Valid (option share) := λ x, x <> Some (Share.bot) /\ x <> None.
  Local Instance share_pcore_instance : PCore (option share) := λ _, None.
  Local Instance share_op_instance : Op (option share) := λ x y, match x, y with
    | Some a, Some b => if eq_dec a Share.bot then None else if eq_dec b Share.bot then None else
        if eq_dec (Share.glb a b) Share.bot then Some (Share.lub a b) else None | _, _ => None end.

  Lemma share_op_eq : forall x y, x ⋅ y = match x, y with
    | Some a, Some b => if eq_dec a Share.bot then None else if eq_dec b Share.bot then None else
        if eq_dec (Share.glb a b) Share.bot then Some (Share.lub a b) else None | _, _ => None end.
  Proof. reflexivity. Qed.

  Lemma share_op_join : forall x y z, x ⋅ y = Some z <-> exists a b, x = Some a /\ y = Some b /\ a <> Share.bot /\ b <> Share.bot /\ sepalg.join a b z.
  Proof.
    intros; rewrite share_op_eq; split.
    - destruct x as [x|]; [|discriminate].
      destruct y as [y|]; [|discriminate].
      repeat (destruct eq_dec; try discriminate).
      inversion 1; subst.
      do 3 eexists; eauto; repeat (split; auto).
    - intros (a & b & ? & ? & ? & ? & []); subst.
      repeat (destruct eq_dec; try contradiction).
      reflexivity.
  Qed.

  Lemma share_valid2_joins : forall x y, valid (Some x ⋅ Some y) <-> x <> Share.bot /\ y <> Share.bot /\ sepalg.joins x y.
  Proof.
    split.
    - destruct (Some x ⋅ Some y) eqn: J; [|intros []; contradiction].
      apply share_op_join in J as (? & ? & H1 & H2 & ? & ? & J).
      inversion H1; inversion H2; repeat (eexists; eauto).
    - intros (? & ? & ? & J).
      erewrite (proj2 (share_op_join _ _ _)); [|eauto 7].
      split; auto.
      inversion 1; subst.
      apply join_Bot in J as []; contradiction.
  Qed.

  Lemma share_op_equiv : forall x y z, x ⋅ y = z <->
    match z with Some c => exists a b, x = Some a /\ y = Some b /\ a <> Share.bot /\ b <> Share.bot /\ sepalg.join a b c
    | None => x = None \/ y = None \/ x = Some Share.bot \/ y = Some Share.bot \/ exists a b, x = Some a /\ y = Some b /\ Share.glb a b <> Share.bot end.
  Proof.
    intros; destruct z.
    { apply share_op_join. }
    rewrite share_op_eq.
    destruct x; [|tauto].
    destruct y; [|tauto].
    repeat (destruct eq_dec; subst; try tauto).
    - split; try discriminate.
      intros [|[|[|[|(? & ? & ? & ? & ?)]]]]; congruence.
    - split; eauto 9.
  Qed.

  Definition share_ra_mixin : @RAMixin (option share) (ofe_equiv shareO) _ _ _.
  Proof.
    split; try apply _; try done.
    - unfold share; intros ???; rewrite !share_op_eq; simpl.
      destruct x as [x|], y as [y|], z as [z|]; try reflexivity.
      + destruct (eq_dec x Share.bot), (eq_dec y Share.bot), (eq_dec z Share.bot); try reflexivity.
        { destruct (eq_dec); reflexivity. }
        { destruct (eq_dec); [destruct (eq_dec)|]; reflexivity. }
        destruct (eq_dec (Share.glb y z) Share.bot), (eq_dec (Share.glb x y) Share.bot).
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
        * reflexivity.
      + destruct (if eq_dec _ _ then _ else _); reflexivity.
    - unfold share; intros ??; rewrite !share_op_eq; simpl.
      destruct x as [x|], y as [y|]; try reflexivity.
      destruct (eq_dec x Share.bot), (eq_dec y Share.bot); try reflexivity.
      rewrite (Share.glb_commute y x) (Share.lub_commute y x); reflexivity.
    - unfold share; intros ??; rewrite !share_op_eq; unfold valid, share_valid_instance; intros [].
      destruct x as [x|], y as [y|]; try contradiction.
      split; [inversion 1; subst | auto].
      rewrite eq_dec_refl in H0; contradiction.
  Qed.
  Canonical Structure shareR := discreteR shareO share_ra_mixin.

  Global Instance share_cmra_discrete : CmraDiscrete shareR.
  Proof. apply discrete_cmra_discrete. Qed.
  Global Instance share_full_exclusive : Exclusive(A := shareR) (Some Tsh).
  Proof. intros p [? Hnone]. contradiction Hnone. rewrite share_op_eq.
    destruct p; auto. destruct (eq_dec); auto. destruct (eq_dec); auto.
    destruct (eq_dec); auto. rewrite Share.glb_commute Share.glb_top in e; contradiction.
  Qed.
  Global Instance share_cancelable (q : shareR) : Cancelable q.
  Proof. intros n p1 p2 [Hv1 Hv2]. rewrite !share_op_eq in Hv1 Hv2 |- *.
    destruct q as [q|], p1 as [p1|], p2 as [p2|]; try contradiction.
    unfold share in *.
    destruct (eq_dec q Share.bot), (eq_dec p1 Share.bot), (eq_dec p2 Share.bot); try contradiction.
    destruct (eq_dec), (eq_dec); try contradiction.
    inversion 1; f_equal; eapply Share.distrib_spec; eauto; congruence.
  Qed.
  Global Instance share_id_free (q : shareR) : IdFree q.
  Proof. intros p []. destruct q; [|contradiction].
    intros (? & ? & Heq & ? & ? & ? & J)%share_op_join; subst.
    inversion Heq; subst.
    apply sepalg.join_comm, sepalg.unit_identity, identity_share_bot in J; contradiction.
  Qed.

  Lemma Tsh_valid : valid (Some Tsh).
  Proof.
    split; auto.
    inversion 1; contradiction Share.nontrivial.
  Qed.

  Lemma Tsh_validN n : validN(A := shareR) n (Some Tsh).
  Proof.
    apply Tsh_valid.
  Qed.

End share.

#[global] Hint Resolve Tsh_valid Tsh_validN : core.
