(* An algebra of share-annotated values, where shares may be readable or unreadable,
   but unreadable shares don't give access to the value. *)

From iris.algebra Require Export agree.
From iris.algebra Require Import local_updates proofmode_classes big_op.
From VST.msl Require Import shares.
From VST.veric Require Export base share_alg dfrac.
From iris_ora.algebra Require Export ora agree.
From iris.prelude Require Import options.

Definition readable_dfrac (dq : dfrac) :=
  match dq with DfracOwn sh => readable_share sh | DfracBoth sh => sh <> Share.bot | _ => True end.

Definition readable_dfrac_dec dq : { readable_dfrac dq } + { ¬readable_dfrac dq }.
destruct dq; try by left.
- destruct (readable_share_dec s); [left | right]; done.
- destruct (eq_dec s Share.bot); [right | left]; intros ?; done.
Defined.

Section shared.

Context (V : ofe).

Inductive shared :=
| YES (dq : dfrac) (rsh : readable_dfrac dq) (v : agree V)
| NO (sh : share) (rsh : ¬readable_share sh).

Definition dfrac_of (s : shared) := match s with
| YES dq _ _ => dq
| NO sh _ => DfracOwn sh
end.

Local Instance shared_dist : Dist shared := λ n x y,
  match x, y with
  | YES dqx _ vx, YES dqy _ vy => dqx = dqy ∧ vx ≡{n}≡ vy
  | NO shx _, NO shy _ => shx = shy
  | _, _ => False
  end.
Local Instance shared_equiv : Equiv shared := λ x y,
  match x, y with
  | YES dqx _ vx, YES dqy _ vy => dqx = dqy ∧ vx ≡ vy
  | NO shx _, NO shy _ => shx = shy
  | _, _ => False
  end.

Definition shared_ofe_mixin : OfeMixin shared.
Proof.
  split.
  - destruct x, y; intuition; try split; try pose proof (H 0) as H'; try destruct H; try destruct H'; try done.
    + intros n; specialize (H n); destruct H; done.
    + apply O.
  - intros n; split; rewrite /dist /shared_dist.
    + intros x; destruct x; done.
    + intros [|] [|]; try done.
      by intros [-> ->].
    + intros [|] [|] [|]; try done.
      * by intros [-> ->].
      * by intros ->.
  - intros ?? [|] [|]; try done.
    intros [??]; split; first done.
    eapply dist_lt; eauto.
Qed.
Canonical Structure sharedO := Ofe shared shared_ofe_mixin.

(* CMRA *)
Existing Instance share_valid_instance.

Local Instance shared_validN_instance : ValidN shared := λ n x,
  match x with
  | YES dq _ v => ✓{n} dq ∧ ✓{n} v
  | NO sh _ => ✓ sh
  end.
Local Instance shared_valid_instance : Valid shared := λ x, ∀ n, ✓{n} x.

Existing Instance share_op_instance.

Lemma op_unreadable_shares : forall sh1 sh2, ~readable_share sh1 -> ~readable_share sh2 -> ~readable_share (sh1 ⋅ sh2).
Proof.
  intros.
  intros X.
  destruct (eq_dec (sh1 ⋅ sh2) Share.bot); [rewrite e in X; contradiction bot_unreadable|].
  edestruct (share_op_join sh1 sh2) as [(? & ? & J) _]; try done.
  eapply join_unreadable_shares; eauto.
Qed.

Local Instance shared_op_instance : Op shared := λ x y,
  match x, y with
  | YES dqx _ vx, YES dqy _ vy =>
      match readable_dfrac_dec (dqx ⋅ dqy) with
      | left rsh => YES (dqx ⋅ dqy) rsh (vx ⋅ vy)
      | right _ => NO Share.bot bot_unreadable
      end
  | YES dq _ v, NO sh _ | NO sh _, YES dq _ v => if eq_dec sh Share.bot then NO Share.bot bot_unreadable else
      match readable_dfrac_dec (dq ⋅ DfracOwn sh) with
      | left rsh => YES (dq ⋅ DfracOwn sh) rsh v
      | right _ => NO Share.bot bot_unreadable
      end
  | NO shx rshx, NO shy rshy => NO (shx ⋅ shy) (op_unreadable_shares _ _ rshx rshy)
  end.

Definition dfrac_error df := match df with DfracOwn sh | DfracBoth sh => if eq_dec sh Share.bot then true else false | _ => false end.

Lemma share_op_readable : forall sh1 sh2, readable_share sh1 \/ readable_share sh2 -> ~readable_share (sh1 ⋅ sh2) -> sh1 ⋅ sh2 = Share.bot.
Proof.
  intros.
  destruct (eq_dec (sh1 ⋅ sh2) Share.bot); first done.
  edestruct (share_op_join sh1 sh2) as [(? & ? & J) _]; try done.
  contradiction H0; eapply readable_share_join; eauto.
Qed.

Lemma dfrac_op_readable : forall d1 d2, readable_dfrac d1 \/ readable_dfrac d2 -> ~readable_dfrac (d1 ⋅ d2) -> dfrac_error (d1 ⋅ d2) = true.
Proof.
  destruct d1, d2; simpl; intros; try done; if_tac; try done.
  exfalso; contradiction H1; apply share_op_readable; auto.
Qed.

Lemma bot_op_share : forall s, Share.bot ⋅ s = Share.bot.
Proof.
  intros; rewrite /op /share_op_instance.
  rewrite eq_dec_refl; done.
Qed.

Lemma share_op_bot : forall s, s ⋅ Share.bot = Share.bot.
Proof.
  intros; rewrite /op /share_op_instance.
  if_tac; [|rewrite eq_dec_refl]; done.
Qed.

Lemma op_dfrac_error : forall d1 d2, dfrac_error d2 = true -> dfrac_error (d1 ⋅ d2) = true.
Proof.
  destruct d1, d2; try done; simpl; repeat if_tac; subst; try done; simpl; contradiction H0; apply share_op_bot.
Qed.

Lemma dfrac_error_unreadable : forall d, dfrac_error d = true -> ~readable_dfrac d.
Proof.
  destruct d; try done; simpl; repeat if_tac; subst; try done; try tauto.
  intros; apply bot_unreadable.
Qed.

Lemma dfrac_of_op : forall x y, (dfrac_error (dfrac_of x ⋅ dfrac_of y) = true ∧ dfrac_of (x ⋅ y) = DfracOwn Share.bot) ∨ (dfrac_of (x ⋅ y) = dfrac_of x ⋅ dfrac_of y).
Proof.
  rewrite /op /shared_op_instance; intros; destruct x, y; simpl.
  - destruct (readable_dfrac_dec _); simpl; auto.
    apply dfrac_op_readable in n; auto.
  - if_tac; subst; auto.
    { destruct dq; rewrite /= ?share_op_bot eq_dec_refl; auto. }
    destruct (readable_dfrac_dec _); simpl; auto.
    apply dfrac_op_readable in n; auto.
  - if_tac; subst; auto.
    { destruct dq; rewrite /= ?bot_op_share eq_dec_refl; auto. }
    rewrite (comm _ (DfracOwn sh)).
    destruct (readable_dfrac_dec _); simpl; auto.
    apply dfrac_op_readable in n; auto.
  - auto.
Qed.

Definition val_of s := match s with YES _ _ v => Some v | _ => None end.

Lemma shared_op_alt : forall x y, match readable_dfrac_dec (dfrac_of x ⋅ dfrac_of y) with
  | left rsh => exists v, val_of x ⋅ val_of y = Some v /\ x ⋅ y = YES (dfrac_of x ⋅ dfrac_of y) rsh v
  | right rsh => if dfrac_error (dfrac_of x ⋅ dfrac_of y) then x ⋅ y ≡ NO Share.bot bot_unreadable
      else exists shx shy rshx rshy, x = NO shx rshx /\ y = NO shy rshy /\ x ⋅ y = NO (shx ⋅ shy) (op_unreadable_shares _ _ rshx rshy) /\ shx ⋅ shy ≠ Share.bot
  end.
Proof.
  intros [|] [|]; rewrite /op /shared_op_instance /=.
  - destruct (readable_dfrac_dec _); eauto.
    apply dfrac_op_readable in n; auto.
    rewrite n //.
  - destruct (readable_dfrac_dec _); eauto.
    + if_tac; eauto.
      exfalso; eapply dfrac_error_unreadable, r.
      subst; apply op_dfrac_error, eq_dec_refl.
    + apply dfrac_op_readable in n; auto.
      rewrite n; if_tac; done.
  - rewrite comm; destruct (readable_dfrac_dec _); eauto.
    + if_tac; eauto.
      exfalso; eapply dfrac_error_unreadable, r.
      subst; apply op_dfrac_error, eq_dec_refl.
    + apply dfrac_op_readable in n; auto.
      rewrite n; if_tac; done.
  - destruct (readable_share_dec _).
    { exfalso; eapply op_unreadable_shares, r; auto. }
    if_tac; eauto 8.
Qed.

Lemma val_of_op : forall x y, dfrac_error (dfrac_of x ⋅ dfrac_of y) = false -> val_of (x ⋅ y) = val_of x ⋅ val_of y.
Proof.
  intros.
  pose proof (shared_op_alt x y) as Hop.
  destruct (readable_dfrac_dec _).
  - by destruct Hop as (? & -> & ->).
  - rewrite H in Hop.
    by destruct Hop as (? & ? & ? & ? & -> & -> & -> & ?).
Qed.

Lemma dfrac_error_op : forall x y, dfrac_error (dfrac_of x ⋅ dfrac_of y) = dfrac_error (dfrac_of (x ⋅ y)).
Proof.
  intros.
  pose proof (shared_op_alt x y) as Hop.
  destruct (readable_dfrac_dec _).
  - by destruct Hop as (? & ? & ->).
  - destruct (dfrac_error _) eqn: Herr.
    + hnf in Hop.
      destruct (x ⋅ y); try done.
      subst; simpl.
      rewrite eq_dec_refl //.
    + by destruct Hop as (? & ? & ? & ? & -> & -> & -> & ?).
Qed.

Lemma pcore_dfrac_readable : forall dq dq', readable_dfrac dq -> pcore dq = Some dq' -> readable_dfrac dq'.
Proof.
  destruct dq; inversion 2; done.
Qed.

(* This runs into trouble with pcore_mono, since a YES can be included in an error.
Local Instance shared_pcore_instance : PCore shared := λ x,
  match x with
  | YES DfracDiscarded rsh v | YES (DfracBoth _) rsh v => Some (YES DfracDiscarded I v)
  | _ => None
  end.*)

Local Instance shared_pcore_instance : PCore shared := λ x, None.

(*Lemma shared_pcore_Some : forall x cx, pcore x = Some cx ->
  exists dq dq' rsh rsh' v, x = YES dq rsh v /\ pcore dq = Some dq' /\ cx = YES dq' rsh' v.
Proof.
  intros [|]; try done.
  rewrite /pcore /shared_pcore_instance.
  simpl.
  destruct dq; inversion 1; subst; eauto 8.
Qed.*)

Lemma dfrac_error_assoc : forall x y z, dfrac_error (dfrac_of (x ⋅ y) ⋅ dfrac_of z) = dfrac_error (dfrac_of x ⋅ dfrac_of (y ⋅ z)).
Proof.
  intros.
  destruct (dfrac_of_op x y) as [[??] | ->], (dfrac_of_op y z) as [[??] | ->].
  - rewrite (comm _ _ (dfrac_of z)) op_dfrac_error; last by rewrite -dfrac_error_op.
    rewrite op_dfrac_error //; last by rewrite -dfrac_error_op.
  - rewrite assoc !(comm _ _ (dfrac_of z)) op_dfrac_error; last by rewrite -dfrac_error_op.
    rewrite op_dfrac_error //.
  - rewrite -assoc op_dfrac_error; last done.
    rewrite op_dfrac_error //; last by rewrite -dfrac_error_op.
  - rewrite assoc //.
Qed.

Global Instance NO_discrete sh rsh : Discrete (NO sh rsh).
Proof. intros [|] ?; done. Qed.

Definition shared_cmra_mixin : CmraMixin shared.
Proof.
  split.
  - intros [|] ? [|] [|]; try done.
    + intros [-> H]; hnf.
      rewrite /op /shared_op_instance.
      destruct (readable_dfrac_dec _); rewrite ?H //.
    + intros H; hnf in H; subst; done.
    + intros [-> H]; hnf.
      rewrite /op /shared_op_instance.
      if_tac; try done.
      destruct (readable_dfrac_dec _); rewrite ?H //.
    + intros H; hnf in H; subst; done.
  - intros ? [|]; try done.
(*    intros [|]; try done.
    intros ? [-> H] Hcore.
    destruct dq0; inv Hcore; eexists; split; eauto; done.*)
  - intros n [|] [|]; try done.
    + intros [-> H] [??]; split; by rewrite -?H.
    + intros H; hnf in H; subst; done.
  - reflexivity.
  - intros ? [|]; try done.
    intros [??]; split; by apply cmra_validN_S.
  - intros ???.
    pose proof (shared_op_alt x (y ⋅ z)) as Hop1.
    pose proof (shared_op_alt (x ⋅ y) z) as Hop2.
    destruct (readable_dfrac_dec _); [|destruct (dfrac_error _) eqn: Herr].
    + destruct Hop1 as (v1 & Hval1 & ->).
      assert (dfrac_error (dfrac_of y ⋅ dfrac_of z) = false) as Hyz.
      { rewrite dfrac_error_op.
        destruct (dfrac_error (dfrac_of (y ⋅ z))) eqn: Herr; try done.
        exfalso; eapply dfrac_error_unreadable, r; apply op_dfrac_error; done. }
      destruct (dfrac_of_op y z) as [[??] | Hyz']; first congruence.
      assert (dfrac_error (dfrac_of x ⋅ dfrac_of y) = false) as Hxy.
      { rewrite Hyz' assoc in r.
        destruct (dfrac_error (dfrac_of x ⋅ dfrac_of y)) eqn: Herr; try done.
        exfalso; eapply dfrac_error_unreadable, r; rewrite (comm _ _ (dfrac_of z)); apply op_dfrac_error; done. }
      destruct (dfrac_of_op x y) as [[??] | Hxy']; first congruence.
      assert (dfrac_of x ⋅ dfrac_of (y ⋅ z) = (dfrac_of (x ⋅ y) ⋅ dfrac_of z)) as Heq.
      { rewrite Hxy' Hyz' assoc //. }
      destruct (readable_dfrac_dec _); [|exfalso; rewrite Heq // in r].
      destruct Hop2 as (v2 & Hval2 & ->).
      rewrite !val_of_op in Hval1 Hval2; try done.
      split.
      * rewrite Hxy' Hyz' assoc //.
      * assert (Some v1 ≡ Some v2) as Hv by (rewrite -Hval1 -Hval2 assoc //).
        by inv Hv.
    + rewrite Hop1.
      rewrite -dfrac_error_assoc in Herr.
      destruct (readable_dfrac_dec _).
      { exfalso; eapply dfrac_error_unreadable; eauto. }
      rewrite Herr in Hop2; rewrite Hop2 //.
    + destruct Hop1 as (? & shyz & ? & ? & -> & Hyz & Hxyz & ?).
      assert (shyz ≠ Share.bot) by (intros ->; rewrite share_op_bot // in H).
      pose proof (shared_op_alt y z) as Hop3; rewrite Hyz in Hop3.
      destruct (readable_dfrac_dec (dfrac_of y ⋅ dfrac_of z)); first by destruct Hop3 as (? & ? & ?).
      rewrite dfrac_error_op Hyz /= if_false in Hop3; last done.
      destruct Hop3 as (? & ? & ? & ? & -> & -> & [=] & ?); simpl in *; subst.
      rewrite /op /shared_op_instance; hnf.
      apply (@cmra_assoc shareR).
  - intros ??.
    pose proof (shared_op_alt x y) as Hop1.
    pose proof (shared_op_alt y x) as Hop2.
    rewrite comm in Hop2.
    destruct (readable_dfrac_dec _).
    + destruct Hop1 as (v1 & Hval1 & ->), Hop2 as (v2 & Hval2 & ->).
      split; auto.
      assert (Some v1 ≡ Some v2) as Hv by (rewrite -Hval1 -Hval2 comm //).
      by inv Hv.
    + destruct (dfrac_error _) eqn: Herr; first by rewrite Hop1 Hop2.
      destruct Hop1 as (? & ? & ? & ? & -> & -> & -> & ?), Hop2 as (? & ? & ? & ? & [=] & [=] & -> & ?); subst.
      hnf; by rewrite (@cmra_comm shareR).
  - inversion 1.
  - inversion 1.
  - inversion 2.
  - intros.
    destruct x; hnf.
    + rewrite /op /shared_op_instance in H.
      destruct y.
      * destruct (readable_dfrac_dec _); last done.
        destruct H; split; eapply cmra_validN_op_l; eauto.
      * if_tac in H; try done.
        destruct (readable_dfrac_dec _); last done.
        destruct H; split; auto; eapply cmra_validN_op_l; eauto.
    + intros; subst.
      rewrite /op /shared_op_instance in H.
      destruct y.
      * rewrite eq_dec_refl // in H.
      * hnf in H; rewrite bot_op_share // in H.
  - intros ????? Hop.
    assert (y1 ⋅ y2 ≠ NO Share.bot bot_unreadable) as Hfail.
    { intros X; rewrite X in Hop; destruct x; done. }
    rewrite /op /shared_op_instance in Hop Hfail.
    destruct y1, y2.
    + destruct (readable_dfrac_dec _); try done.
      destruct x; try done.
      destruct Hop as [Hd Hv].
      destruct H; subst.
      apply cmra_extend in Hv as (vz1 & vz2 & ? & ? & ?); last done.
      exists (YES dq rsh vz1), (YES dq0 rsh0 vz2); repeat (split; try done).
      rewrite {2}/op /shared_op_instance.
      destruct (readable_dfrac_dec _); done.
    + if_tac in Hop; try done.
      destruct (readable_dfrac_dec _); try done.
      destruct x; try done.
      destruct Hop as [-> ?].
      eexists (YES dq rsh v0), _; split; last done.
      rewrite {2}/op /shared_op_instance.
      rewrite if_false; last done.
      destruct (readable_dfrac_dec _); done.
    + if_tac in Hop; try done.
      destruct (readable_dfrac_dec _); try done.
      destruct x; try done.
      destruct Hop as [-> ?].
      eexists _, (YES dq rsh0 v0); split; last done.
      rewrite {2}/op /shared_op_instance.
      rewrite if_false; last done.
      destruct (readable_dfrac_dec _); done.
    + eexists _, _; split; last done.
      symmetry; rewrite discrete_iff //.
Qed.
Canonical Structure sharedC : cmra := Cmra shared shared_cmra_mixin.

Lemma dfrac_error_discarded : forall x, dfrac_error (DfracDiscarded ⋅ x) = dfrac_error x.
Proof.
  destruct x; done.
Qed.

Local Instance shared_orderN : OraOrderN shared := λ n x y,
  match x, y with
  | YES shx _ vx, YES shy _ vy => shx ≼ₒ{n} shy ∧ vx ≼ₒ{n} vy
  | NO shx _, NO shy _ => shx = shy
  | _, _ => False
  end.

Local Instance shared_order : OraOrder shared := λ x y,
  match x, y with
  | YES shx _ vx, YES shy _ vy => shx ≼ₒ shy ∧ vx ≼ₒ vy
  | NO shx _, NO shy _ => shx = shy
  | _, _ => False
  end.

Lemma shared_orderN_inv : forall n x y, x ≼ₒ{n} y → x ≡ y ∨
  ∃ shx shy rshx rshy vx vy, x = YES shx rshx vx ∧ y = YES shy rshy vy ∧ shx ≼ₒ{n} shy ∧ vx ≼ₒ{n} vy.
Proof.
  intros n [|] [|]; inversion 1; eauto 10.
Qed.

Lemma shared_order_inv : forall x y, x ≼ₒ y → x ≡ y ∨
  ∃ shx shy rshx rshy vx vy, x = YES shx rshx vx ∧ y = YES shy rshy vy ∧ shx ≼ₒ shy ∧ vx ≼ₒ vy.
Proof.
  intros [|] [|]; inversion 1; eauto 10.
Qed.

Lemma shared_orderN_implies : forall n x y, x ≼ₒ{n} y → dfrac_of x ≼ₒ dfrac_of y ∧ val_of x ≼ₒ{n} val_of y.
Proof.
  intros ? [|] [|]; try done; simpl.
  inversion 1; subst; split; try done.
  hnf; auto.
Qed.

Lemma readable_dfrac_order : forall dq dq', dq ≼ₒ dq' -> readable_dfrac dq -> readable_dfrac dq'.
Proof.
  intros ?? [-> | <-]; try done.
  destruct dq; try done.
  intros; hnf; intros ->.
  contradiction bot_unreadable.
Qed.

Lemma shared_orderN_op : ∀ (n : nat) (x x' y : shared), x ≼ₒ{n} x' → x ⋅ y ≼ₒ{n} x' ⋅ y.
Proof.
  intros.
  destruct (shared_orderN_implies _ _ _ H) as [Hd ?].
  pose proof (shared_op_alt x y) as Hop; destruct (readable_dfrac_dec _); [|destruct (dfrac_error (dfrac_of x ⋅ dfrac_of y)) eqn: Herr];
    pose proof (shared_op_alt x' y) as Hop'.
  - destruct Hop as (? & Hv & ->).
    destruct (readable_dfrac_dec _); last by contradiction n0; eapply readable_dfrac_order, r; apply ora_order_op.
    destruct Hop' as (? & Hv' & ->).
    split.
    + by apply ora_orderN_op.
    + rewrite -Some_orderN -Hv -Hv'; by apply ora_orderN_op.
  - destruct (x ⋅ y); inv Hop.
    destruct Hd as [Hd | Hd]; rewrite -Hd in Hop'; first by destruct (readable_dfrac_dec _); try done; rewrite Herr in Hop'; destruct (x' ⋅ y); inv Hop'.
    rewrite (comm _ _ DfracDiscarded) -assoc in Hop'.
    destruct (readable_dfrac_dec _).
    + exfalso; eapply dfrac_error_unreadable, r.
      rewrite dfrac_error_discarded //.
    + rewrite dfrac_error_discarded Herr in Hop'.
      destruct (x' ⋅ y); inv Hop'; done.
  - destruct Hop as (? & ? & ? & ? & -> & -> & -> & ?); simpl in *.
    destruct x'; try done; simpl in *.
    hnf in H; subst; done.
Qed.

Definition shared_ora_mixin : OraMixin shared.
Proof.
  split; try done.
  - intros ??? H Hord z.
    pose proof (H z) as Hxz.
    pose proof (shared_op_alt x z) as Hop.
    destruct (readable_dfrac_dec _); [|destruct (dfrac_error _) eqn: Herr].
    + destruct Hop as (? & Hv1 & Hz); rewrite Hz in Hxz.
      destruct z; try done.
      destruct Hxz as [Hd Hv]; simpl in *.
      pose proof (shared_op_alt y (YES dq rsh v)) as Hop.
      destruct (readable_dfrac_dec _); last by contradiction n0; eapply readable_dfrac_order, r; eapply ora_order_op, shared_orderN_implies.
      destruct Hop as (? & Hv2 & ->).
      split.
      * etrans; first done.
        by eapply ora_order_op, shared_orderN_implies.
      * rewrite -Some_order -Hv2 /=.
        destruct (val_of y); try done; apply agree_increasing.
    + destruct (x ⋅ z), z; try done.
      inv Hxz; inv Hop.
      rewrite /op /shared_op_instance.
      destruct y; [rewrite eq_dec_refl // | hnf; rewrite share_op_bot //].
    + destruct Hop as (? & ? & ? & ? & -> & -> & ? & ?).
      destruct y; inv Hord; done.
  - intros ???? Hvalid Hord.
    pose proof (shared_op_alt y1 y2) as Hop.
    destruct (readable_dfrac_dec _); [|destruct (dfrac_error _) eqn: Herr].
    + destruct Hop as (? & Hval & Heq).
      rewrite Heq in Hord; destruct x; try done.
      destruct Hord as [Hd Hv].
      rewrite -Some_orderN -Hval in Hv; apply ora_op_extend in Hv as (v1 & v2 & ? & Hv1 & Hv2); last by destruct Hvalid.
      destruct y1, y2; try done; inv Hv1; inv Hv2.
      * eexists (YES _ rsh0 _), (YES _ rsh1 _); split; [|split; split; try done].
        rewrite /op /shared_op_instance in Heq |- *.
        destruct (readable_dfrac_dec _); done.
      * eexists (YES _ rsh0 _), (NO _ _); split; [|split; [split|]; try done].
        rewrite /op /shared_op_instance in Heq |- *.
        if_tac; try done.
        destruct (readable_dfrac_dec _); done.
      * eexists (NO _ _), (YES _ rsh1 _); split; [|split; [|split]; try done].
        rewrite /op /shared_op_instance in Heq |- *.
        if_tac; try done.
        rewrite comm in Hd; destruct (readable_dfrac_dec _); done.
    + destruct (y1 ⋅ y2); inv Hop.
      destruct x; inv Hord.
      exists y1, y2; done.
    + destruct Hop as (? & ? & ? & ? & -> & -> & Heq & ?).
      eexists _, _; split; last done.
      destruct x; inv Hord; done. 
  - intros ??? Hvalid Hord.
    destruct x, y; try done.
    + destruct Hord as [Hd Hv].
      apply ora_extend in Hv as (v' & ? & ?); last by destruct Hvalid.
      eexists (YES _ rsh0 _); split; [|split; done].
      split; done.
    + inv Hord.
      eexists; split; last done; done.
  - intros ? [|] [|]; try done.
    intros [-> ?%ora_dist_orderN]; split; auto.
  - intros ? [|] [|]; try done.
    intros [? ?%ora_orderN_S]; split; auto.
  - intros ? [|] [|] [|]; try done.
    + intros [??] [??]; split; etrans; eauto.
    + intros [=] [=]; subst; done.
  - apply shared_orderN_op.
  - intros ? [|] [|]; try done.
    + intros [??] [??]; split; eapply ora_validN_orderN; eauto.
    + intros ? [=]; subst; done.
  - split.
    + destruct x, y; try done.
      intros [??]; split; auto.
    + intros H; pose proof (H 0) as H0; destruct x, y; try done.
      destruct H0; split; try done.
      apply ora_order_orderN; intros; eapply H.
  - inversion 1.
Qed.
Canonical Structure sharedR : ora := Ora shared shared_ora_mixin.

End shared.
