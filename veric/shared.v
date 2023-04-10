(* An algebra of share-annotated values, where shares may be readable or unreadable,
   but unreadable shares don't give access to the value. *)

From iris.algebra Require Export agree.
From iris.algebra Require Import updates local_updates proofmode_classes big_op.
From VST.msl Require Import shares.
From VST.veric Require Export base share_alg dfrac.
From iris_ora.algebra Require Export ora agree.
From iris.prelude Require Import options.

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

Global Instance YES_ne dq rsh : NonExpansive (YES dq rsh).
Proof. done. Qed.

Global Instance YES_proper dq rsh : Proper (equiv ==> equiv) (YES dq rsh).
Proof. done. Qed.

Lemma YES_irrel dq rsh1 rsh2 v : YES dq rsh1 v ≡ YES dq rsh2 v.
Proof. done. Qed.

(* CMRA *)
Existing Instance share_valid_instance.

Local Instance shared_validN_instance : ValidN shared := λ n x,
  match x with
  | YES dq _ v => ✓ dq ∧ ✓{n} v
  | NO sh _ => ✓ sh
  end.
Local Instance shared_valid_instance : Valid shared := λ x,
  match x with
  | YES dq _ v => ✓ dq ∧ ✓ v
  | NO sh _ => ✓ sh
  end.

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

Lemma share_op_readable' : forall sh1 sh2, readable_share sh1 \/ readable_share sh2 -> ✓(sh1 ⋅ sh2) -> readable_share (sh1 ⋅ sh2).
Proof.
  intros.
  edestruct (share_op_join sh1 sh2) as [(? & ? & J) _]; try done.
  eapply readable_share_join; eauto.
Qed.

Lemma share_op_readable : forall sh1 sh2, readable_share sh1 \/ readable_share sh2 -> ~readable_share (sh1 ⋅ sh2) -> sh1 ⋅ sh2 = Share.bot.
Proof.
  intros.
  destruct (eq_dec (sh1 ⋅ sh2) Share.bot); first done.
  contradiction H0; apply share_op_readable'; auto.
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

Lemma dfrac_op_readable' : forall d1 d2, readable_dfrac d1 \/ readable_dfrac d2 -> ✓(d1 ⋅ d2) -> readable_dfrac (d1 ⋅ d2).
Proof.
  intros ??? Hvalid.
  destruct d1, d2; try done; try solve [intros ?; subst; destruct Hvalid; done].
  apply share_op_readable'; auto.
Qed.

Lemma dfrac_op_readable : forall d1 d2, readable_dfrac d1 \/ readable_dfrac d2 -> ~readable_dfrac (d1 ⋅ d2) -> dfrac_error (d1 ⋅ d2) = true.
Proof.
  destruct d1, d2; simpl; intros; try done; if_tac; try done.
  exfalso; contradiction H1; apply share_op_readable; auto.
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

Definition val_of s := match s with YES _ _ v => Some v | _ => None end.

Lemma shared_validN : forall n x, ✓{n} x ↔ ✓ dfrac_of x ∧ ✓{n} val_of x.
Proof.
  intros ? [|]; try done.
  by intuition.
Qed.

Lemma shared_valid : forall x, ✓ x ↔ ✓ dfrac_of x ∧ ✓ val_of x.
Proof.
  intros [|]; try done.
  by intuition.
Qed.

Lemma dfrac_error_invalid : forall d, dfrac_error d = true -> ~ ✓ d.
Proof.
  destruct d; try done; simpl; if_tac; subst; intros ? Hv; try done.
  by destruct Hv.
Qed.

Lemma YES_op' : forall dq1 dq2 rsh1 rsh2 v1 v2, YES dq1 rsh1 v1 ⋅ YES dq2 rsh2 v2 =
  match readable_dfrac_dec (dq1 ⋅ dq2) with
      | left rsh => YES (dq1 ⋅ dq2) rsh (v1 ⋅ v2)
      | right _ => NO Share.bot bot_unreadable
      end.
Proof. done. Qed.

Lemma YES_op : forall dq1 dq2 rsh1 rsh2 rsh v1 v2, YES dq1 rsh1 v1 ⋅ YES dq2 rsh2 v2 ≡ YES (dq1 ⋅ dq2) rsh (v1 ⋅ v2).
Proof.
  intros; rewrite YES_op'.
  by destruct (readable_dfrac_dec _).
Qed.

Lemma NO_YES_op' : forall sh1 dq2 rsh1 rsh2 v2, NO sh1 rsh1 ⋅ YES dq2 rsh2 v2 =
  if eq_dec sh1 Share.bot then NO Share.bot bot_unreadable else
  match readable_dfrac_dec (DfracOwn sh1 ⋅ dq2) with
      | left rsh => YES (DfracOwn sh1 ⋅ dq2) rsh v2
      | right _ => NO Share.bot bot_unreadable
      end.
Proof.
  intros. rewrite /op /shared_op_instance.
  if_tac; try done.
  rewrite (comm _ dq2) //.
Qed.

Lemma NO_YES_op : forall sh1 dq2 rsh1 rsh2 rsh v2, NO sh1 rsh1 ⋅ YES dq2 rsh2 v2 ≡ YES (DfracOwn sh1 ⋅ dq2) rsh v2.
Proof.
  intros; rewrite NO_YES_op'.
  if_tac.
  - exfalso; subst; destruct dq2; try done; rewrite /= bot_op_share in rsh; try done; contradiction bot_unreadable.
  - by destruct (readable_dfrac_dec _).
Qed.

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

Lemma dfrac_of_op' : forall x y, dfrac_of (x ⋅ y) = if dfrac_error (dfrac_of x ⋅ dfrac_of y) then DfracOwn Share.bot else dfrac_of x ⋅ dfrac_of y.
Proof.
  intros; pose proof (shared_op_alt x y) as Hop.
  destruct (readable_dfrac_dec _).
  - destruct Hop as (? & ? & ->).
    destruct (dfrac_error _) eqn: Herr; last done.
    exfalso; eapply dfrac_error_unreadable; eauto.
  - destruct (dfrac_error _); first by destruct (x ⋅ y); inv Hop.
    destruct Hop as (? & ? & ? & ? & -> & -> & -> & ?); done.
Qed.

Lemma dfrac_of_op : forall x y, (dfrac_error (dfrac_of x ⋅ dfrac_of y) = true ∧ dfrac_of (x ⋅ y) = DfracOwn Share.bot) ∨ (dfrac_of (x ⋅ y) = dfrac_of x ⋅ dfrac_of y).
Proof.
  intros.
  rewrite dfrac_of_op'.
  destruct (dfrac_error _); auto.
Qed.

Lemma shared_dist_implies : forall n x y, x ≡{n}≡ y -> dfrac_of x = dfrac_of y ∧ val_of x ≡{n}≡ val_of y.
Proof.
  intros ? [|] [|]; inversion 1; subst; try done.
  by split; last constructor.
Qed.

Lemma shared_includedN : forall n x y, x ≼{n} y -> y ≡ NO Share.bot bot_unreadable ∨ (dfrac_of x ≼{n} dfrac_of y ∧ val_of x ≼{n} val_of y).
Proof.
  intros ??? [z H].
  pose proof (shared_op_alt x z) as Hop.
  destruct (readable_dfrac_dec _); [|destruct (dfrac_error _)].
  - destruct Hop as (? & Hval & Heq); rewrite Heq in H.
    destruct y; try done.
    destruct H as [-> Hv]; right; split.
    + by eexists.
    + rewrite /= Hv -Hval; by eexists.
  - rewrite Hop in H; destruct y; inv H; auto.
  - destruct Hop as (? & ? & ? & ? & -> & -> & Heq & ?).
    destruct y; inv H.
    right; split; auto.
    by eexists (DfracOwn _).
Qed.

Lemma YES_incl_NO : forall n dq rsh v sh nsh, YES dq rsh v ≼{n} NO sh nsh -> sh = Share.bot.
Proof.
  intros; apply shared_includedN in H as [H | [_ H]]; first by inv H.
  apply option_includedN in H as [? | (? & ? & ? & ? & ?)]; done.
Qed.

Lemma YES_incl_YES : forall n dq1 rsh1 v1 dq2 rsh2 v2, YES dq1 rsh1 v1 ≼{n} YES dq2 rsh2 v2 ->
  dq1 ≼ dq2 ∧ v1 ≼{n} v2.
Proof.
  intros; apply shared_includedN in H as [H | [??]]; try done.
  rewrite -Some_includedN_total //.
Qed.

Lemma val_of_op' : forall x y, val_of (x ⋅ y) = if dfrac_error (dfrac_of x ⋅ dfrac_of y) then None else val_of x ⋅ val_of y.
Proof.
  intros.
  pose proof (shared_op_alt x y) as Hop.
  destruct (readable_dfrac_dec _).
  - destruct Hop as (? & -> & ->).
    destruct (dfrac_error _) eqn: Herr; last done.
    exfalso; eapply dfrac_error_unreadable, r; auto.
  - destruct (dfrac_error _) eqn: Herr; first by destruct (x ⋅ y); inv Hop.
    by destruct Hop as (? & ? & ? & ? & -> & -> & -> & ?).
Qed.

Lemma val_of_op : forall x y, dfrac_error (dfrac_of x ⋅ dfrac_of y) = false -> val_of (x ⋅ y) = val_of x ⋅ val_of y.
Proof.
  intros.
  rewrite val_of_op' H //.
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

Local Instance shared_pcore_instance : PCore shared := λ x,
  match x with
  | YES DfracDiscarded rsh v | YES (DfracBoth _) rsh v => Some (YES DfracDiscarded I v)
  | NO sh _ => if eq_dec sh Share.bot then Some x else None
  | _ => None
  end.

Lemma pcore_YES : forall dq rsh v cx, pcore (YES dq rsh v) = Some cx ↔
  pcore dq = Some DfracDiscarded /\ cx = YES DfracDiscarded I v.
Proof.
  intros; destruct dq; intuition; subst; try done; try by inv H.
Qed.

Lemma pcore_NO : forall sh rsh cx, pcore (NO sh rsh) = Some cx ↔
  sh = Share.bot /\ cx = NO sh rsh.
Proof.
  rewrite /pcore /shared_pcore_instance.
  intuition; subst; try by (if_tac in H; inv H).
  apply eq_dec_refl.
Qed.

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

Lemma dfrac_error_discarded : forall x, dfrac_error (DfracDiscarded ⋅ x) = dfrac_error x.
Proof.
  destruct x; done.
Qed.

Definition shared_cmra_mixin : CmraMixin shared.
Proof.
  split; try done.
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
  - intros ? [|] [|] ? H Hcore; try done.
    + destruct H as [-> ?]; apply pcore_YES in Hcore as [? ->].
      eexists; rewrite pcore_YES //.
    + inv H; apply pcore_NO in Hcore as [-> ->].
      eexists; rewrite pcore_NO //.
  - intros n [|] [|]; try done.
    + intros [-> H] [??]; split; by rewrite -?H.
    + intros H; hnf in H; subst; done.
  - intros [|]; intuition.
    + by destruct H.
    + split; apply cmra_valid_validN, H.
    + apply (H 0).
  - intros ? [|]; try done.
    intros [??]; split; last apply cmra_validN_S; done.
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
  - intros [|] ? Hcore.
    + apply pcore_YES in Hcore as [H ->].
      rewrite /op /shared_op_instance.
      destruct (readable_dfrac_dec _).
      * split; last apply agree_idemp.
        apply cmra_pcore_l in H; apply H.
      * apply dfrac_op_readable in n; auto.
        rewrite dfrac_error_discarded in n.
        contradiction (dfrac_error_unreadable dq).
    + apply pcore_NO in Hcore as [-> ->].
      rewrite /op /shared_op_instance.
      hnf; rewrite share_op_bot //.
  - intros [|] ? Hcore.
    + apply pcore_YES in Hcore as [? ->]; done.
    + apply pcore_NO in Hcore as [-> ->].
      rewrite /pcore /shared_pcore_instance eq_dec_refl //.
  - intros ??? [z H] Hcore.
    pose proof (shared_op_alt x z) as Hop.
    destruct x.
    + apply pcore_YES in Hcore as [? ->].
      destruct (readable_dfrac_dec _).
      * destruct Hop as (? & Hval & Hop).
        rewrite Hop in H; destruct y; try done.
        destruct H as [-> H].
        eexists; rewrite pcore_YES; split; first split; try done.
        { destruct dq, (dfrac_of z); done. }
        exists (YES DfracDiscarded I v0); split; try done.
        rewrite -agree_included H -Some_included_total -Hval; eexists; done.
      * destruct (dfrac_error _) eqn: Herr; last by destruct Hop as (? & ? & ? & ? & ? & ?).
        rewrite Hop in H; destruct y; inv H.
        eexists; rewrite pcore_NO; split; first done.
        exists (NO Share.bot bot_unreadable); rewrite /op /shared_op_instance.
        rewrite eq_dec_refl //.
    + apply pcore_NO in Hcore as [-> ->].
      destruct (readable_dfrac_dec _).
      { exfalso; clear Hop; destruct (dfrac_of z); simpl in r; rewrite ?bot_op_share in r; done. }
      destruct (dfrac_error _) eqn: Herr.
      * rewrite Hop in H; destruct y; inv H.
        eexists; rewrite pcore_NO; split; first done.
        exists (NO Share.bot rsh); rewrite /op /shared_op_instance.
        hnf; rewrite share_op_bot //.
      * destruct (dfrac_of z); rewrite /= ?bot_op_share eq_dec_refl // in Herr.
  - intros.
    destruct x; hnf.
    + rewrite /op /shared_op_instance in H.
      destruct y.
      * destruct (readable_dfrac_dec _); last done.
        destruct H; split; [eapply cmra_valid_op_l | eapply cmra_validN_op_l]; eauto.
      * if_tac in H; try done.
        destruct (readable_dfrac_dec _); last done.
        destruct H; split; auto; eapply cmra_valid_op_l; eauto.
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

(* updates *)
Lemma writable_update : forall sh rsh v v', writable0_share sh -> ✓ v' ->
  YES (DfracOwn sh) rsh v ~~> YES (DfracOwn sh) rsh v'.
Proof.
  intros; intros ? [|] Hvalid; simpl in *; last by destruct Hvalid.
  pose proof (shared_op_alt (YES (DfracOwn sh) rsh v) c) as Hop.
  pose proof (shared_op_alt (YES (DfracOwn sh) rsh v') c) as Hop'.
  repeat destruct (readable_dfrac_dec _); try done.
  - destruct Hop as (? & ? & Hop); rewrite Hop /= in Hvalid; destruct Hvalid as [Hsh Hv].
    destruct c; try done.
    { rewrite comm in Hsh; apply dfrac_valid_own_readable in Hsh as [??]; done. }
    destruct Hop' as (? & Hval & Hop'); rewrite Hop' /=.
    split; try done.
    rewrite -Some_validN -Hval /= Some_validN //.
  - simpl in *; destruct (dfrac_error _); first by rewrite Hop in Hvalid.
    by destruct Hop as (? & ? & ? & ? & ? & ?).
Qed.

Local Instance shared_orderN : OraOrderN shared := λ n x y, y ≡ NO Share.bot bot_unreadable ∨ dfrac_of x ≼ₒ dfrac_of y ∧ val_of x ≼ₒ{n} val_of y.

Local Instance shared_order : OraOrder shared := λ x y, y ≡ NO Share.bot bot_unreadable ∨ dfrac_of x ≼ₒ dfrac_of y ∧ val_of x ≼ₒ val_of y.

Lemma dfrac_error_fail : forall x y, dfrac_error (dfrac_of x ⋅ dfrac_of y) = true -> x ⋅ y ≡ NO Share.bot bot_unreadable.
Proof.
  intros; pose proof (shared_op_alt x y) as Hop.
  rewrite H in Hop.
  destruct (readable_dfrac_dec _); try done.
  exfalso; eapply dfrac_error_unreadable; eauto.
Qed.

Local Instance YES_discard_increasing rsh v : Increasing (YES DfracDiscarded rsh v).
Proof.
  intros ?; hnf; simpl; right.
  destruct (dfrac_error (DfracDiscarded ⋅ dfrac_of y)) eqn: Herr.
  - pose proof (dfrac_error_fail (YES DfracDiscarded rsh v) y Herr) as Hfail.
    destruct (YES _ _ _ ⋅ _) eqn: Heq; inv Hfail.
    rewrite dfrac_error_discarded in Herr.
    destruct y; first by exfalso; eapply dfrac_error_unreadable; eauto.
    simpl in Herr.
    if_tac in Herr; subst; try done.
    split; hnf; auto.
  - edestruct dfrac_of_op as [(Herr' & _) | ->]; first by rewrite Herr' // in Herr.
    rewrite val_of_op // /= Some_op_opM.
    split; [apply discard_increasing|].
    destruct y; apply agree_increasing.
Qed.

Local Instance fail_absorb rsh : LeftAbsorb equiv (NO Share.bot rsh) op.
Proof.
  intros x.
  rewrite /op /shared_op_instance.
  destruct x; first by rewrite eq_dec_refl.
  hnf; rewrite bot_op_share //.
Qed.

Local Instance fail_increasing rsh : Increasing (NO Share.bot rsh).
Proof.
  intros ?; hnf; simpl; left.
  apply fail_absorb.
Qed.

Lemma readable_dfrac_order : forall dq dq', dq ≼ₒ dq' -> readable_dfrac dq -> readable_dfrac dq'.
Proof.
  intros ?? [-> | <-]; try done.
  destruct dq; try done.
  intros; hnf; intros ->.
  contradiction bot_unreadable.
Qed.

Lemma dfrac_error_order : forall dq dq', dq ≼ₒ dq' -> dfrac_error dq = dfrac_error dq'.
Proof.
  intros ?? [-> | <-]; try done.
  rewrite (comm _ dq) dfrac_error_discarded //.
Qed.

Lemma shared_orderN_op : ∀ (n : nat) (x x' y : shared), x ≼ₒ{n} x' → x ⋅ y ≼ₒ{n} x' ⋅ y.
Proof.
  intros.
  destruct H as [H | [??]].
  - destruct x'; inv H.
    left; by rewrite fail_absorb.
  - right.
    rewrite !dfrac_of_op' !val_of_op'.
    erewrite dfrac_error_order; last by apply ora_order_op.
    destruct (dfrac_error _); last by split; [apply ora_order_op | apply ora_orderN_op].
    split; hnf; auto.
Qed.

Definition shared_ora_mixin : OraMixin shared.
Proof.
  split.
  - intros [|] ?.
    + rewrite pcore_YES; intros [? ->]; apply _.
    + rewrite pcore_NO; intros [-> ->]; apply _.
  - intros ??? H Hord z.
    destruct Hord as [Hno | [Hdy Hvy]].
    { destruct y; inv Hno.
      left; by rewrite fail_absorb. }
    pose proof (H z) as Hxz.
    pose proof (shared_op_alt x z) as Hop.
    destruct (readable_dfrac_dec _); [|destruct (dfrac_error _) eqn: Herr].
    + destruct Hop as (? & Hv1 & Hz); rewrite Hz in Hxz.
      destruct Hxz as [? | [Hd Hv]]; first done; simpl in *.
      pose proof (shared_op_alt y z) as Hop.
      destruct (readable_dfrac_dec _); last by contradiction n0; eapply readable_dfrac_order, r; apply ora_order_op.
      destruct Hop as (? & Hv2 & ->).
      right; split.
      * etrans; first done.
        by eapply ora_order_op.
      * rewrite /= -Hv2.
        destruct (val_of y), (val_of z); try done; apply agree_increasing.
    + left; apply dfrac_error_fail.
      erewrite <- dfrac_error_order; first done.
      by apply ora_order_op.
    + destruct Hop as (? & shz & ? & rshz & -> & -> & ? & ?); simpl in *.
      destruct Hxz as [? | [Hd Hv]]; first done; simpl in *.
      pose proof (shared_op_alt y (NO shz rshz)) as Hop.
      destruct (readable_dfrac_dec _).
      * destruct Hop as (? & Hv2 & ->).
        right; simpl; split; last apply agree_increasing.
        destruct Hdy as [<- | <-]; try done.
        etrans; first done.
        rewrite (comm _ _ DfracDiscarded) -assoc (comm _ DfracDiscarded); right; done.
      * destruct (dfrac_error _) eqn: Herr'; first by left; rewrite Hop.
        destruct Hop as (? & ? & ? & ? & -> & [=] & -> & ?); subst.
        destruct Hd as [Hd | ?]; try done.
        injection Hd as Hd.
        symmetry in Hd; apply share_op_join in Hd as (? & ? & J); last by intros ->.
        by eapply sepalg.join_canc in J; last apply bot_join_eq.
  - intros ???? [H | [Hd Hv]] Hcore.
    { destruct y; inv H. eexists; rewrite pcore_NO; split; [eauto | by left]. }
    destruct x, y; try done; simpl in *.
    + rewrite pcore_YES in Hcore; destruct Hcore as [? ->].
      eexists; rewrite pcore_YES; split; [split; last done|].
      { destruct Hd as [<- | <-]; try done.
        destruct dq; done. }
      right; split; first left; done.
    + rewrite pcore_NO in Hcore; destruct Hcore as [-> ->].
      destruct Hd as [<- | <-]; done.
    + rewrite pcore_NO in Hcore; destruct Hcore as [-> ->].
      destruct Hd as [[=] | ?]; subst; try done.
      eexists; rewrite pcore_NO; split; first eauto.
      by left.
  - intros ???? Hvalid [? | [Hd Hv]].
    { eexists _, _; split; first left; done. }
    pose proof (shared_op_alt y1 y2) as Hop.
    rewrite dfrac_of_op' in Hd; rewrite val_of_op' in Hv.
    destruct (dfrac_error (dfrac_of y1 ⋅ dfrac_of y2)) eqn: Herr.
    { destruct (readable_dfrac_dec _).
      { exfalso; by eapply dfrac_error_unreadable, r. }
      eexists _, _; split; last done.
      destruct (y1 ⋅ y2); inv Hop; simpl in *.
      by right. }
    destruct (readable_dfrac_dec _).
    + destruct Hop as (? & Hval & H).
      apply shared_validN in Hvalid as [??].
      apply ora_op_extend in Hv as (v1 & v2 & ? & Hv1 & Hv2); last done.
      destruct y1, y2; try done; inv Hv1; inv Hv2.
      * exists (YES dq rsh x1), (YES dq0 rsh0 x2); split; last done.
        right; rewrite YES_op'; destruct (readable_dfrac_dec _); done.
      * eexists (YES dq rsh x1), _; split; last done.
        right; rewrite /op /shared_op_instance.
        if_tac.
        { subst; rewrite op_dfrac_error // in Herr; apply eq_dec_refl. }
        destruct (readable_dfrac_dec _); done.
      * eexists _, (YES dq rsh0 x1); split; last done.
        right; rewrite NO_YES_op'.
        if_tac.
        { subst; rewrite (comm _ (dfrac_of _)) op_dfrac_error // in Herr; apply eq_dec_refl. }
        destruct (readable_dfrac_dec _); done.
    + destruct Hop as (? & ? & ? & ? & -> & -> & H & ?).
      eexists _, _; split; last done.
      rewrite H; right; done.
  - intros ??? Hvalid [? | [Hd Hv]].
    { destruct x; inv H; done. }
    apply shared_validN in Hvalid as [??].
    apply ora_extend in Hv as (? & ? & Hval); last done.
    destruct y; inv Hval.
    + exists (YES dq rsh x1); split; first right; done.
    + eexists; split; first right; done.
  - intros ??? [Hd Hv]%shared_dist_implies.
    right; split; [hnf; auto | by apply ora_dist_orderN].
  - intros ??? [H | [? ?%ora_orderN_S]].
    + destruct y; inv H; by left.
    + by right.
  - intros ???? Hord [H | [Hd Hv]].
    { destruct z; inv H; by left. }
    destruct Hord as [Hy | [??]].
    { destruct y; inv Hy; simpl in *.
      left; destruct Hd.
      * destruct z; simpl in *; subst; try done.
        inv H; done.
      * destruct z; simpl in *; subst; done. }
    right; split; etrans; eauto.
  - apply shared_orderN_op.
  - intros ??? H [Hno | [??]]; first by rewrite Hno in H.
    rewrite !shared_validN in H |- *; destruct H.
    split; first apply ora_discrete_valid; by eapply ora_validN_orderN.
  - split.
    + intros [? | [??]] ?; first by left.
      right; split; last apply ora_order_orderN; done.
    + intros H; pose proof (H 0) as H0; destruct H0 as [? | [??]]; first by left.
      destruct (decide (dfrac_of y = DfracOwn Share.bot)).
      { destruct y; simpl in *; subst; left; first contradiction bot_unreadable.
        by inv e. }
      right; split; first done.
      apply ora_order_orderN; intros n1.
      destruct (H n1) as [? | [??]]; first destruct y; done.
  - intros ??? Hcore; pose proof (shared_op_alt x y) as Hop.
    inversion Hcore as [?? Heq Hcore'|]; subst.
    destruct (readable_dfrac_dec _).
    + destruct Hop as (? & ? & ->).
      symmetry in Hcore'; destruct x; simpl in *.
      * rewrite pcore_YES in Hcore'; destruct Hcore' as [Hd ->].
        destruct (ora_pcore_order_op dq DfracDiscarded (dfrac_of y)) as (dq' & Hdq' & Hdisc); first by rewrite Hd.
        assert (dq' = DfracDiscarded) as -> by (destruct Hdisc; subst; auto).
        apply leibniz_equiv in Hdq'.
        eexists; erewrite (proj2 (pcore_YES _ _ _ _)) by done.
        split; first done.
        destruct cx; inv Heq; right; split; try done.
        rewrite /= -H -H1 comm; destruct (val_of y); try done; apply agree_increasing.
      * rewrite pcore_NO in Hcore'; destruct Hcore' as [-> ->].
        exfalso; destruct (dfrac_of y); try done; rewrite /= bot_op_share // in r.
    + destruct (dfrac_error _) eqn: Herr; first by destruct (x ⋅ y); inv Hop; eexists; rewrite /pcore /shared_pcore_instance eq_dec_refl; split; last left.
      destruct Hop as (? & ? & ? & ? & -> & -> & -> & ?).
      symmetry in Hcore'; rewrite pcore_NO in Hcore'; destruct Hcore' as [-> ->].
      eexists; rewrite /pcore /shared_pcore_instance if_true; last by rewrite bot_op_share.
      split; first done; left; hnf; rewrite bot_op_share //.
Qed.

Canonical Structure sharedR : ora := Ora shared shared_ora_mixin.

Global Instance shared_discrete : OfeDiscrete V -> OraDiscrete sharedR.
Proof.
  intros ?; split.
  - intros [|] [|]; try done.
    intros [??]; split; try done.
    by apply agree_cmra_discrete.
  - intros [|]; try done.
    intros [??]; split; try done.
    by apply agree_cmra_discrete.
  - intros [|] [|]; try done.
    intros [Hno | [??]]; first by inv Hno.
    by right; split; last apply agree_ora_discrete.
Qed.

Global Instance discarded_core_id rsh v : OraCoreId (YES DfracDiscarded rsh v).
Proof.
  hnf.
  rewrite /pcore /ora_pcore /=.
  constructor; apply YES_irrel.
Qed.

End shared.

Arguments YES {_} _ _ _.
Arguments NO {_} _ _.
Arguments dfrac_of {_} _.
Arguments val_of {_} _.
