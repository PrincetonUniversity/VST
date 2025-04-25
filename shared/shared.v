(* An algebra of share-annotated values, where shares may be readable or unreadable,
   but unreadable shares don't give access to the value. *)

From iris.algebra Require Export agree.
From iris.algebra Require Import updates local_updates proofmode_classes big_op.
Set Warnings "-notation-overridden,-hiding-delimiting-key".
From VST.shared Require Export share_alg dshare.
From iris_ora.algebra Require Export ora agree.
Set Warnings "notation-overridden,hiding-delimiting-key".
From iris.prelude Require Import options.

Section shared.

Context `{ST : ShareType}.

Definition readable_share' (s : shareO) := match s with Share sh => share_readable sh | _ => False end.

Definition readable_dfrac_dec dq : { readable_dfrac dq } + { ¬readable_dfrac dq }.
destruct dq; simpl.
- destruct s; last by right; intros [].
  apply readable_dec.
- destruct s; last by right; intros [].
  by left.
Defined.

Context (V : ofe).

Inductive shared :=
| YES (dq : dfrac) (rsh : readable_dfrac dq) (v : agree V)
| NO (sh : shareO) (rsh : ¬readable_share' sh).

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

Local Instance shared_unit_instance : Unit shared := NO ε unreadable_bot.

Local Definition err := NO ShareBot id.

Lemma op_unreadable_shares : forall sh1 sh2, ~readable_share' sh1 -> ~readable_share' sh2 -> ~readable_share' (sh1 ⋅ sh2).
Proof.
  intros.
  intros X.
  destruct (sh1 ⋅ sh2) eqn: Hop; last done.
  apply share_op_join in Hop as (? & ? & -> & -> & J).
  eapply join_unreadable; eauto.
Qed.

Local Instance shared_op_instance : Op shared := λ x y,
  match x, y with
  | YES dqx _ vx, YES dqy _ vy =>
      match readable_dfrac_dec (dqx ⋅ dqy) with
      | left rsh => YES (dqx ⋅ dqy) rsh (vx ⋅ vy)
      | right _ => err
      end
  | YES dq _ v, NO sh _ | NO sh _, YES dq _ v =>
      match readable_dfrac_dec (dq ⋅ DfracOwn sh) with
      | left rsh => YES (dq ⋅ DfracOwn sh) rsh v
      | right _ => err
      end
  | NO shx rshx, NO shy rshy => NO (shx ⋅ shy) (op_unreadable_shares _ _ rshx rshy)
  end.

Definition dfrac_error df := match df with DfracOwn ShareBot | DfracBoth ShareBot => true | _ => false end.

Lemma share_op_readable' : forall sh1 sh2, readable_share' sh1 \/ readable_share' sh2 -> ✓(sh1 ⋅ sh2) -> readable_share' (sh1 ⋅ sh2).
Proof.
  intros ??? (? & ? & ? & -> & -> & Hop & J)%share_valid2_joins.
  rewrite Hop; destruct H; eapply readable_mono; eauto; rewrite share_op_comm //.
Qed.

Lemma share_op_readable : forall sh1 sh2, readable_share' sh1 \/ readable_share' sh2 -> ~readable_share' (sh1 ⋅ sh2) -> sh1 ⋅ sh2 = ShareBot.
Proof.
  intros.
  destruct (sh1 ⋅ sh2) eqn: Hop; last done.
  contradiction H0; rewrite -Hop; apply share_op_readable'; auto.
  rewrite Hop //.
Qed.

Lemma dfrac_op_readable' : forall d1 d2, readable_dfrac d1 \/ readable_dfrac d2 -> ✓(d1 ⋅ d2) -> readable_dfrac (d1 ⋅ d2).
Proof.
  intros ??? Hvalid.
  destruct d1, d2; simpl in *; try by destruct Hvalid as (? & -> & ?).
  apply share_op_readable'; auto.
Qed.

Lemma dfrac_op_readable : forall d1 d2, readable_dfrac d1 \/ readable_dfrac d2 -> ~readable_dfrac (d1 ⋅ d2) -> dfrac_error (d1 ⋅ d2) = true.
Proof.
  destruct d1 as [[|]|[|]], d2 as [[|]|[|]]; simpl; try done; destruct (_ ⋅ _) eqn: Hop; try done.
  intros H ?; apply (share_op_readable (Share _) (Share _)) in H.
  - rewrite H // in Hop.
  - rewrite Hop //.
Qed.

Lemma op_dfrac_error : forall d1 d2, dfrac_error d2 = true -> dfrac_error (d1 ⋅ d2) = true.
Proof.
  destruct d1 as [[|]|[|]], d2 as [[|]|[|]]; done.
Qed.

Lemma dfrac_error_unreadable : forall d, dfrac_error d = true -> ~readable_dfrac d.
Proof.
  destruct d as [[|]|[|]]; try done; simpl; tauto.
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
  destruct d as [[|]|[|]]; try done; simpl; intros ? Hv; try done.
  by destruct Hv as (? & ? & ?).
Qed.

Lemma YES_op' : forall dq1 dq2 rsh1 rsh2 v1 v2, YES dq1 rsh1 v1 ⋅ YES dq2 rsh2 v2 =
  match readable_dfrac_dec (dq1 ⋅ dq2) with
      | left rsh => YES (dq1 ⋅ dq2) rsh (v1 ⋅ v2)
      | right _ => err
      end.
Proof. done. Qed.

Lemma YES_op : forall dq1 dq2 rsh1 rsh2 rsh v1 v2, YES dq1 rsh1 v1 ⋅ YES dq2 rsh2 v2 ≡ YES (dq1 ⋅ dq2) rsh (v1 ⋅ v2).
Proof.
  intros; rewrite YES_op'.
  by destruct (readable_dfrac_dec _).
Qed.

Lemma NO_YES_op' : forall sh1 dq2 rsh1 rsh2 v2, NO sh1 rsh1 ⋅ YES dq2 rsh2 v2 =
  match readable_dfrac_dec (DfracOwn sh1 ⋅ dq2) with
      | left rsh => YES (DfracOwn sh1 ⋅ dq2) rsh v2
      | right _ => err
      end.
Proof.
  intros. rewrite {1}/op /shared_op_instance.
  rewrite (comm _ dq2) //.
Qed.

Lemma NO_YES_op : forall sh1 dq2 rsh1 rsh2 rsh v2, NO sh1 rsh1 ⋅ YES dq2 rsh2 v2 ≡ YES (DfracOwn sh1 ⋅ dq2) rsh v2.
Proof.
  intros; rewrite NO_YES_op'.
  by destruct (readable_dfrac_dec _).
Qed.

Lemma shared_op_alt : forall x y, match readable_dfrac_dec (dfrac_of x ⋅ dfrac_of y) with
  | left rsh => exists v, val_of x ⋅ val_of y = Some v /\ x ⋅ y = YES (dfrac_of x ⋅ dfrac_of y) rsh v
  | right rsh => if dfrac_error (dfrac_of x ⋅ dfrac_of y) then x ⋅ y ≡ err
      else exists shx shy rshx rshy, x = NO shx rshx /\ y = NO shy rshy /\ x ⋅ y = NO (shx ⋅ shy) (op_unreadable_shares _ _ rshx rshy) /\ ✓ (shx ⋅ shy)
  end.
Proof.
  intros [|] [|]; rewrite /op /shared_op_instance.
  - destruct (readable_dfrac_dec _); eauto.
    apply dfrac_op_readable in n; auto.
    rewrite n //.
  - destruct (readable_dfrac_dec _); eauto.
    apply dfrac_op_readable in n; auto.
    rewrite n //.
  - rewrite comm; destruct (readable_dfrac_dec _); eauto.
    apply dfrac_op_readable in n; auto.
    rewrite n //.
  - destruct (readable_dfrac_dec _).
    { exfalso; eapply op_unreadable_shares, r; auto. }
    destruct (dfrac_error _) eqn: Herr.
    { hnf; simpl in Herr.
      destruct (_ ⋅ _); done. }
    eexists _, _, _, _; repeat (split; first done).
    simpl in Herr.
    destruct (_ ⋅ _) eqn: Hop; try done.
    setoid_rewrite Hop; done.
Qed.

Lemma dfrac_of_op' : forall x y, dfrac_of (x ⋅ y) = if dfrac_error (dfrac_of x ⋅ dfrac_of y) then DfracOwn ShareBot else dfrac_of x ⋅ dfrac_of y.
Proof.
  intros; pose proof (shared_op_alt x y) as Hop.
  destruct (readable_dfrac_dec _).
  - destruct Hop as (? & ? & ->).
    destruct (dfrac_error _) eqn: Herr; last done.
    exfalso; eapply dfrac_error_unreadable; eauto.
  - destruct (dfrac_error _); first by destruct (x ⋅ y); inversion Hop; subst.
    destruct Hop as (? & ? & ? & ? & -> & -> & -> & ?); done.
Qed.

Lemma dfrac_of_op : forall x y, (dfrac_error (dfrac_of x ⋅ dfrac_of y) = true ∧ dfrac_of (x ⋅ y) = DfracOwn ShareBot) ∨ (dfrac_of (x ⋅ y) = dfrac_of x ⋅ dfrac_of y).
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

Lemma shared_dist' : forall n x y, x ≡{n}≡ y <-> dfrac_of x = dfrac_of y ∧ val_of x ≡{n}≡ val_of y.
Proof.
  split; first apply shared_dist_implies.
  destruct x, y; simpl; intros [[=] Hv]; subst; try done.
  by apply Some_dist_inj in Hv.
Qed.

Lemma shared_includedN : forall n x y, x ≼{n} y -> y ≡ err ∨ (dfrac_of x ≼{n} dfrac_of y ∧ val_of x ≼{n} val_of y).
Proof.
  intros ??? [z H].
  pose proof (shared_op_alt x z) as Hop.
  destruct (readable_dfrac_dec _); [|destruct (dfrac_error _)].
  - destruct Hop as (? & Hval & Heq); rewrite Heq in H.
    destruct y; try done.
    destruct H as [-> Hv]; right; split.
    + by eexists.
    + rewrite /= Hv -Hval; by eexists.
  - rewrite Hop in H; destruct y; inversion H; subst; auto.
  - destruct Hop as (? & ? & ? & ? & -> & -> & Heq & ?).
    destruct y; inversion H; subst.
    right; split; auto.
    by eexists (DfracOwn _).
Qed.

Lemma shared_included : forall x y, x ≼ y -> y ≡ err ∨ (dfrac_of x ≼ dfrac_of y ∧ val_of x ≼ val_of y).
Proof.
  intros ?? [z H].
  pose proof (shared_op_alt x z) as Hop.
  destruct (readable_dfrac_dec _); [|destruct (dfrac_error _)].
  - destruct Hop as (? & Hval & Heq); rewrite Heq in H.
    destruct y; try done.
    destruct H as [-> Hv]; right; split.
    + by eexists.
    + rewrite /= Hv -Hval; by eexists.
  - rewrite Hop in H; destruct y; inversion H; subst; auto.
  - destruct Hop as (? & ? & ? & ? & -> & -> & Heq & ?).
    destruct y; inversion H; subst.
    right; split; auto.
    by eexists (DfracOwn _).
Qed.

Local Instance shared_err_absorb rsh : LeftAbsorb equiv (NO ShareBot rsh) op.
Proof.
  intros x.
  rewrite /op /shared_op_instance /=.
  destruct x; try done.
  destruct (readable_dfrac_dec _); try done.
  destruct dq as [[|]|[|]]; done.
Qed.

Lemma YES_incl_NO : forall n dq rsh v sh nsh, YES dq rsh v ≼{n} NO sh nsh -> sh = ShareBot.
Proof.
  intros; apply shared_includedN in H as [H | [_ H]]; first by inversion H; subst.
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
  - destruct (dfrac_error _) eqn: Herr; first by destruct (x ⋅ y); inversion Hop; subst.
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
      destruct (x ⋅ y); try done; simpl in *.
      by subst.
    + by destruct Hop as (? & ? & ? & ? & -> & -> & -> & ?).
Qed.

Local Instance shared_pcore_instance : PCore shared := λ x,
  Some (match x with
  | YES (DfracBoth _) rsh v => YES DfracDiscarded I v
  | NO sh _ => match sh with ShareBot => err | _ => ε end
  | _ => ε
  end).

(*Lemma pcore_YES : forall dq rsh v cx, pcore (YES dq rsh v) = Some cx ↔
  pcore dq = Some DfracDiscarded /\ cx = YES DfracDiscarded I v.
Proof.
  intros; destruct dq; intuition; subst; try done; try by inversion H; subst.
Qed.

Lemma pcore_NO : forall sh rsh cx, pcore (NO sh rsh) = Some cx ↔
  sh = Share.bot /\ cx = NO sh rsh.
Proof.
  rewrite /pcore /shared_pcore_instance.
  intuition; subst; try by (if_tac in H; inversion H; subst).
  apply eq_dec_refl.
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

Lemma dfrac_error_discarded : forall x, dfrac_error (DfracDiscarded ⋅ x) = dfrac_error x.
Proof.
  destruct x; simpl; rewrite left_id //.
Qed.

Lemma share_op_None : forall (s : shareO), s ⋅ ShareBot = ShareBot.
Proof.
  by destruct s.
Qed.

Local Instance shared_unit_left_id : LeftId equiv (ε : shared) op.
Proof.
  intros [|]; rewrite /op /=.
  - rewrite right_id.
    destruct (readable_dfrac_dec _); done.
  - hnf; rewrite left_id //.
Qed.

Definition shared_cmra_mixin : CmraMixin shared.
Proof.
  apply cmra_total_mixin; try done.
  - intros [|] ? [|] [|]; try done.
    + intros [-> H]; hnf.
      rewrite /op /shared_op_instance.
      destruct (readable_dfrac_dec _); rewrite ?H //.
    + intros H; hnf in H; subst; done.
    + intros [-> H]; hnf.
      rewrite /op /shared_op_instance.
      destruct (readable_dfrac_dec _); rewrite ?H //.
    + intros H; hnf in H; subst; done.
  - intros ? [|] [|]; try done.
    + intros [<- ?]; destruct dq; done.
    + intros [=]; subst.
      destruct sh0; done.
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
        by inversion Hv; subst.
    + rewrite Hop1.
      rewrite -dfrac_error_assoc in Herr.
      destruct (readable_dfrac_dec _).
      { exfalso; eapply dfrac_error_unreadable; eauto. }
      rewrite Herr in Hop2; rewrite Hop2 //.
    + destruct Hop1 as (? & shyz & ? & ? & -> & Hyz & Hxyz & ?).
      pose proof (shared_op_alt y z) as Hop3; rewrite Hyz in Hop3.
      destruct (readable_dfrac_dec (dfrac_of y ⋅ dfrac_of z)); first by destruct Hop3 as (? & ? & ?).
      rewrite dfrac_error_op Hyz /= in Hop3.
      destruct shyz; last by rewrite share_op_None in H; destruct H.
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
      by inversion Hv; subst.
    + destruct (dfrac_error _) eqn: Herr; first by rewrite Hop1 Hop2.
      destruct Hop1 as (? & ? & ? & ? & -> & -> & -> & ?), Hop2 as (? & ? & ? & ? & [=] & [=] & -> & ?); subst.
      hnf; by rewrite (@cmra_comm shareR).
  - intros [|].
    + rewrite /op /shared_op_instance /core /pcore /shared_pcore_instance /=.
      destruct dq.
      * rewrite /ε /shared_unit_instance right_id.
        destruct (readable_dfrac_dec _); done.
      * rewrite comm dfrac_op_both_discarded.
        destruct (readable_dfrac_dec _); try done.
        split; first done.
        apply agree_idemp.
    + destruct sh; try done; simpl.
      rewrite left_id //.
  - intros [|].
    + destruct dq; done.
    + destruct sh; done.
  - intros ?? (z & H).
    pose proof (shared_op_alt x z) as Hop.
    rewrite /core /=; destruct x.
    + destruct dq; first by eexists; rewrite left_id.
      simpl in Hop.
      destruct (readable_dfrac_dec _).
      * destruct Hop as (? & Hval & Hop).
        rewrite Hop in H; destruct y; try done.
        destruct H as [-> H].
        destruct (_ ⋅ _) eqn: Hz.
        { destruct z as [[|]|]; done. }
        exists (YES DfracDiscarded I v0).
        unshelve rewrite YES_op /=; last split; rewrite ?dfrac_op_both_discarded //.
        rewrite -agree_included H -Some_included_total -Hval; eexists; done.
      * destruct (dfrac_error _) eqn: Herr; last by destruct Hop as (? & ? & ? & ? & ? & ?).
        rewrite Hop in H; destruct y; inversion H; subst.
        exists err; done.
    + destruct sh; first by eexists; rewrite left_id.
      destruct (readable_dfrac_dec _).
      { exfalso; clear Hop; destruct (dfrac_of z); done. }
      destruct (dfrac_error _) eqn: Herr.
      * rewrite Hop in H; destruct y; inversion H; subst.
        exists err; done.
      * by destruct (dfrac_of z).
  - intros.
    destruct x; hnf.
    + rewrite /op /shared_op_instance in H.
      destruct y.
      * destruct (readable_dfrac_dec _); last by destruct H.
        destruct H; split; [eapply cmra_valid_op_l | eapply cmra_validN_op_l]; eauto.
      * destruct (readable_dfrac_dec _); last by destruct H.
        destruct H; split; auto; eapply cmra_valid_op_l; eauto.
    + destruct sh; eauto.
      rewrite /op /shared_op_instance in H.
      destruct y; try done.
      destruct (readable_dfrac_dec _); last by destruct H.
      destruct dq as [[|]|[|]]; done.
  - intros ????? Hop.
    assert (y1 ⋅ y2 ≠ err) as Hfail.
    { intros X; rewrite X in Hop; destruct x; inversion Hop; subst; done. }
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
    + destruct (readable_dfrac_dec _); try done.
      destruct x; try done.
      destruct Hop as [-> ?].
      eexists (YES dq rsh v0), _; split; last done.
      rewrite {2}/op /shared_op_instance.
      destruct (readable_dfrac_dec _); done.
    + destruct (readable_dfrac_dec _); try done.
      destruct x; try done.
      destruct Hop as [-> ?].
      eexists _, (YES dq rsh0 v0); split; last done.
      rewrite {2}/op /shared_op_instance.
      destruct (readable_dfrac_dec _); done.
    + eexists _, _; split; last done.
      symmetry; rewrite discrete_iff //.
Qed.
Canonical Structure sharedC : cmra := Cmra shared shared_cmra_mixin.

Definition shared_ucmra_mixin : UcmraMixin shared.
Proof.
  split; try done; apply _.
Qed.
Canonical Structure sharedUC : ucmra := Ucmra shared shared_ucmra_mixin.

(* updates *)
Lemma writable_update : forall sh rsh v v', share_writable sh -> ✓ v' ->
  YES (DfracOwn (Share sh)) rsh v ~~> YES (DfracOwn (Share sh)) rsh v'.
Proof.
  intros; intros ? [|] Hvalid; simpl in *; last by destruct Hvalid.
  pose proof (shared_op_alt (YES (DfracOwn (Share sh)) rsh v) c) as Hop.
  pose proof (shared_op_alt (YES (DfracOwn (Share sh)) rsh v') c) as Hop'.
  repeat destruct (readable_dfrac_dec _); try done.
  - destruct Hop as (? & ? & Hop); rewrite Hop /= in Hvalid; destruct Hvalid as [Hsh Hv].
    destruct c; try done.
    { rewrite comm in Hsh; apply dfrac_valid_own_readable in Hsh as (? & [=] & ?); subst; done. }
    destruct Hop' as (? & Hval & Hop'); rewrite Hop' /=.
    split; try done.
    rewrite -Some_validN -Hval /= Some_validN //.
  - simpl in *; destruct (dfrac_error _); first by rewrite Hop in Hvalid; destruct Hvalid.
    by destruct Hop as (? & ? & ? & ? & ? & ?).
Qed.

Lemma shared_includedN' : forall n x y, ✓{n} y -> dfrac_of x ≼{n} dfrac_of y ∧ val_of x ≼{n} val_of y -> x ≼{n} y.
Proof.
  intros ??? Hvalid [(d & Hd) (v & Hv)].
  destruct (readable_dfrac_dec d).
  - destruct y; simpl in *.
    + exists (YES d r v0).
      pose proof (shared_op_alt x (YES d r v0)).
      rewrite -Hd in H; destruct (readable_dfrac_dec dq); last done.
      destruct H as (? & Hv' & ->).
      destruct x; inversion Hv'; subst; last done.
      rewrite Some_op_opM in Hv; apply Some_dist_inj in Hv as ->.
      rewrite -cmra_op_opM_assoc agree_idemp //.
    + assert (dfrac_error (DfracOwn sh) = true).
      { rewrite Hd; eapply dfrac_op_readable; auto.
        rewrite -Hd //. }
      destruct sh; done.
  - destruct d as [sh | sh]; try done.
    + exists (NO sh n0).
      pose proof (shared_op_alt x (NO sh n0)).
      rewrite -Hd in H.
      destruct (readable_dfrac_dec (dfrac_of y)).
      * destruct H as (? & Hv' & ->).
        destruct y; try done.
        split; first done.
        apply shared_validN in Hvalid as [? Hvv].
        simpl in *.
        destruct x; inversion Hv'; subst.
        symmetry; eapply agree_valid_includedN; try done.
        rewrite -Some_includedN_total Hv /=.
        by exists v.
      * destruct y; try done; simpl in *.
        destruct sh0; try done.
        destruct H as (? & ? & ? & ? & -> & [=] & -> & ?); subst.
        injection Hd; auto.
    + destruct sh; try done.
      apply shared_validN in Hvalid as [Hvalid _]; rewrite Hd in Hvalid.
      apply cmra_valid_op_r in Hvalid as (? & ? & ?); done.
Qed.

Global Instance dfrac_of_ne n : Proper (dist n ==> eq) dfrac_of.
Proof.
  intros [|] [|]; inversion 1; subst; done.
Qed.

Global Instance YES_share_top_cancelable rsh v : Cancelable (YES (DfracOwn (Share share_top)) rsh v).
Proof.
  intros ??? (Hd & Hv)%shared_validN ?.
  destruct (dfrac_of_op (YES (DfracOwn (Share share_top)) rsh v) y) as [(_ & Hop)|Hop]; rewrite Hop // in Hd.
  pose proof (dfrac_full_exclusive _ Hd) as He.
  destruct y; simpl in *; subst; first contradiction unreadable_bot.
  inversion He; subst.
  rewrite H in Hop.
  apply (cancelable _ _ (dfrac_of z)) in Hd; first by destruct z; simpl in *; inversion Hd; subst.
  rewrite -Hop dfrac_of_op' in Hd |- *.
  destruct (dfrac_error _); done.
Qed.

Local Instance shared_orderN : OraOrderN shared := λ n x y, y ≡ err ∨ dfrac_of x ≼ₒ dfrac_of y ∧ val_of x ≼ₒ{n} val_of y.

Local Instance shared_order : OraOrder shared := λ x y, y ≡ err ∨ dfrac_of x ≼ₒ dfrac_of y ∧ val_of x ≼ₒ val_of y.

Lemma dfrac_error_fail : forall x y, dfrac_error (dfrac_of x ⋅ dfrac_of y) = true -> x ⋅ y ≡ err.
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
    destruct (YES _ _ _ ⋅ _) eqn: Heq; inversion Hfail; subst.
    rewrite dfrac_error_discarded in Herr.
    destruct y; first by exfalso; eapply dfrac_error_unreadable; eauto.
    simpl in Herr.
    destruct sh; done.
  - edestruct dfrac_of_op as [(Herr' & _) | ->]; first by rewrite Herr' // in Herr.
    rewrite val_of_op // /= Some_op_opM.
    split; [apply discard_increasing|].
    destruct y; apply agree_increasing.
Qed.

Local Instance shared_err_increasing rsh : Increasing (NO ShareBot rsh).
Proof.
  intros ?; hnf; simpl; left.
  apply shared_err_absorb.
Qed.

Local Instance shared_unit_increasing : Increasing ε.
Proof.
  intros ?; hnf.
  rewrite dfrac_of_op' val_of_op'; simpl.
  destruct (dfrac_error _) eqn: Herr; [left | right].
  - by apply dfrac_error_fail.
  - rewrite !left_id //.
Qed.

Lemma readable_dfrac_order : forall dq dq', dq ≼ₒ dq' -> readable_dfrac dq -> readable_dfrac dq'.
Proof.
  intros ?? [-> | <-]; try done.
  destruct dq as [[|]|[|]]; try done; simpl; rewrite right_id //.
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
  - destruct x'; inversion H; subst.
    left; by rewrite shared_err_absorb.
  - right.
    rewrite !dfrac_of_op' !val_of_op'.
    erewrite dfrac_error_order; last by apply ora_order_op.
    destruct (dfrac_error _); last by split; [apply ora_order_op | apply ora_orderN_op].
    split; hnf; auto.
Qed.

Definition shared_ora_mixin : OraMixin shared.
Proof.
  apply ora_total_mixin; try done.
  - intros x; rewrite /core /=; destruct x.
    + destruct dq; apply _.
    + destruct sh; try apply _.
      apply shared_err_increasing.
  - intros ??? H Hord z.
    destruct Hord as [Hno | [Hdy Hvy]].
    { destruct y; inversion Hno; subst.
      left; by rewrite shared_err_absorb. }
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
    + destruct Hop as (? & shz & ? & rshz & -> & -> & Hno & Hvalid); simpl in *.
      destruct Hxz as [Herr' | [Hd Hv]]; first by (rewrite Hno in Herr'; inversion Herr' as [Heq]; rewrite Heq in Hvalid; destruct Hvalid); simpl in *.
      pose proof (shared_op_alt y (NO shz rshz)) as Hop.
      destruct (readable_dfrac_dec _).
      * destruct Hop as (? & Hv2 & ->).
        right; simpl; split; last apply agree_increasing.
        destruct Hdy as [<- | <-]; try done.
        etrans; first done.
        rewrite (comm _ _ DfracDiscarded) -assoc (comm _ DfracDiscarded); right; done.
      * destruct (dfrac_error _) eqn: Herr'; first by left; rewrite Hop.
        destruct Hop as (? & ? & ? & ? & -> & [=] & -> & Hvalid'); subst.
        destruct Hd as [Hd | ?]; try done.
        destruct Hdy as [Hdy | ?]; try done.
        inversion Hdy; subst.
        right; split; try done.
        by left.
  - intros ??? [H | [Hd Hv]].
    { destruct y; inversion H; subst; left; done. }
    rewrite /core /=; destruct x, y; try done; simpl in *.
    + right; destruct Hd as [<- | <-], dq; rewrite ?dfrac_op_own_discarded ?dfrac_op_both_discarded // /=.
      split.
      * right; rewrite left_id //.
      * apply agree_increasing.
    + right; destruct Hd as [<- | <-]; try done.
      rewrite dfrac_op_own_discarded.
      destruct sh; split; try done.
      right; rewrite left_id //.
    + destruct Hd as [[=] | ?]; subst; try done.
      destruct sh0; [right | left]; done.
  - intros ???? Hvalid [? | [Hd Hv]].
    { eexists _, _; split; first left; done. }
    pose proof (shared_op_alt y1 y2) as Hop.
    rewrite dfrac_of_op' in Hd; rewrite val_of_op' in Hv.
    destruct (dfrac_error (dfrac_of y1 ⋅ dfrac_of y2)) eqn: Herr.
    { destruct (readable_dfrac_dec _).
      { exfalso; by eapply dfrac_error_unreadable, r. }
      eexists _, _; split; last done.
      destruct (y1 ⋅ y2); inversion Hop; subst; simpl in *.
      by right. }
    destruct (readable_dfrac_dec _).
    + destruct Hop as (? & Hval & H).
      apply shared_validN in Hvalid as [??].
      apply ora_op_extend in Hv as (v1 & v2 & ? & Hv1 & Hv2); last done.
      destruct y1, y2; try done; inversion Hv1; subst; inversion Hv2; subst.
      * exists (YES dq rsh x1), (YES dq0 rsh0 x2); split; last done.
        right; rewrite YES_op'; destruct (readable_dfrac_dec _); done.
      * eexists (YES dq rsh x1), _; split; last done.
        right; rewrite /op /shared_op_instance.
        destruct (readable_dfrac_dec _); done.
      * eexists _, (YES dq rsh0 x1); split; last done.
        right; rewrite NO_YES_op'.
        destruct (readable_dfrac_dec _); done.
    + destruct Hop as (? & ? & ? & ? & -> & -> & H & ?).
      eexists _, _; split; last done.
      rewrite H; right; done.
  - intros ??? Hvalid [? | [Hd Hv]].
    { destruct x; inversion H; subst; destruct Hvalid; done. }
    apply shared_validN in Hvalid as [??].
    apply ora_extend in Hv as (? & ? & Hval); last done.
    destruct y; inversion Hval; subst.
    + exists (YES dq rsh x1); split; first right; done.
    + eexists; split; first right; done.
  - intros ??? [Hd Hv]%shared_dist_implies.
    right; split; [hnf; auto | by apply ora_dist_orderN].
  - intros ??? [H | [? ?%ora_orderN_S]].
    + destruct y; inversion H; subst; by left.
    + by right.
  - intros ???? Hord [H | [Hd Hv]].
    { destruct z; inversion H; subst; by left. }
    destruct Hord as [Hy | [??]].
    { destruct y; inversion Hy; subst; simpl in *.
      left; destruct Hd.
      * destruct z; simpl in *; subst; try done.
        inversion H; subst; done.
      * destruct z; simpl in *; subst; done. }
    right; split; etrans; eauto.
  - apply shared_orderN_op.
  - intros ??? H [Hno | [??]]; first by rewrite Hno in H; destruct H.
    rewrite !shared_validN in H |- *; destruct H.
    split; first apply ora_discrete_valid; by eapply ora_validN_orderN.
  - split.
    + intros [? | [??]] ?; first by left.
      right; split; last apply ora_order_orderN; done.
    + intros H; pose proof (H 0) as H0; destruct H0 as [? | [??]]; first by left.
      right; split; try done.
      apply ora_order_orderN; intros n1.
      destruct (H n1) as [? | [??]]; first destruct y; done.
  - intros ??? Hcore; pose proof (shared_op_alt x y) as Hop.
    inversion Hcore as [?? Heq Hcore'|]; subst.
    rewrite /pcore /shared_pcore_instance; eexists; split; first done.
    destruct (readable_dfrac_dec _).
    + destruct Hop as (? & Hv & ->).
      destruct x; simpl in *.
      * right; destruct dq, cx; inversion Heq; subst; simpl.
        -- destruct (_ ⋅ _); try done.
           split; first by right; rewrite left_id.
           apply agree_increasing.
        -- destruct (dfrac_of y); split; simpl; try done; rewrite -H0 -Hv Some_op_opM Some_order; destruct (val_of y); try done; rewrite /= comm; apply agree_increasing.
      * destruct sh, cx; inversion Heq; subst; simpl.
        -- right; destruct (_ ⋅ _); try done; simpl.
           split; first by right; rewrite left_id.
           apply agree_increasing.
        -- destruct (dfrac_of y); done.
    + destruct (dfrac_error _) eqn: Herr; first by destruct (x ⋅ y); inversion Hop; subst; left.
      destruct Hop as (shx & shy & ? & ? & -> & -> & -> & Hv).
      destruct shx, cx; inversion Heq; subst.
      * destruct (Share sh ⋅ shy) eqn: Hop; rewrite Hop // in Hv |- *.
        right; done.
      * destruct shy, Hv; done.
Qed.

Canonical Structure sharedR : ora := Ora shared shared_ora_mixin.
Canonical Structure sharedUR : uora := Uora shared shared_ucmra_mixin.

Global Instance shared_total : OraTotal sharedR.
Proof. hnf; eauto. Qed.

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
    intros [Hno | [??]]; first by inversion Hno; subst.
    by right; split; last apply agree_ora_discrete.
Qed.

Global Instance discarded_core_id rsh v : OraCoreId (YES DfracDiscarded rsh v).
Proof.
  hnf.
  rewrite /pcore /ora_pcore /=.
  constructor; apply YES_irrel.
Qed.

Global Instance bot_core_id rsh : OraCoreId (NO (Share share_bot) rsh).
Proof.
  hnf.
  rewrite /pcore /ora_pcore /=.
  constructor; done.
Qed.

End shared.

Arguments YES {_ _ _} _ _ _.
Arguments NO {_ _ _} _ _.
Arguments dfrac_of {_ _ _} _.
Arguments val_of {_ _ _} _.
