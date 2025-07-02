(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import VST.msl.predicates_hered.
Require Import VST.msl.subtypes.

Require Import Stdlib.Wellfounded.Wellfounded.
Require Import Stdlib.funind.Recdef.

Delimit Scope pred with pred.
Local Open Scope pred.

Set Implicit Arguments.

Definition contractive {A} `{ageable A} {EO : Ext_ord A} (f: pred A -> pred A) : Prop :=
  forall P Q,  |> (P <=> Q)  |-- f P <=> f Q.

Definition nonexpansive {A} `{ageable A} {EO : Ext_ord A} (f: pred A -> pred A) : Prop :=
  forall P Q,  (P <=> Q)  |-- f P <=> f Q.

Definition HOcontractive {A} `{ageable A} {EO : Ext_ord A} (X: Type) (f: (X -> pred A) -> (X -> pred A)) : Prop :=
  forall P Q,  (ALL x:X, |> (P x <=> Q x)) |-- (ALL x:X, f P x <=> f Q x).

Definition HOnonexpansive {A} `{ageable A} {EO : Ext_ord A} (X: Type) (f: (X -> pred A) -> (X -> pred A)) : Prop :=
  forall P Q, (ALL x:X, P x <=> Q x)  |-- (ALL x:X, f P x <=> f Q x).

Module Type HO_REC.

  Parameter HORec : forall {A} `{ageable A} {EO : Ext_ord A} X (f: (X -> pred A) -> (X -> pred A)), X -> pred A.
  Axiom HORec_fold_unfold : forall {A} `{ageable A} {EO : Ext_ord A} X f (H:HOcontractive (X:=X) f),
    HORec f = f (HORec f).

  Parameter Rec : forall {A} `{ageable A} {EO : Ext_ord A} (f: pred A -> pred A), pred A.
  Axiom Rec_fold_unfold : forall {A} `{ageable A} {EO : Ext_ord A} f (H:contractive f),
    Rec f = f (Rec f).

End HO_REC.

Module HoRec : HO_REC.

Section HORec.
  Variable A:Type.
  Variable ag: ageable A.
  Variable eo: Ext_ord A.
  Variable X:Type.
  Variable f: (X-> pred A) -> (X -> pred A).

  Fixpoint HORec' (n:nat) : X -> pred A :=
    match n with
    | S n' => f (HORec' n')
    | O    => f (fun _ => FF)
    end.

  Hypothesis Hcont : HOcontractive f.

  Lemma HORec'_unage:   forall j n x a,
        (n >= level a) ->  (HORec' n x a <-> HORec' (j+n) x a).
  Proof.
  induction j; intros. simpl; intuition.
  specialize (IHj _ x a H).
   rewrite IHj. clear IHj.
  change (S j + n) with (S (j + n)).
   assert (j + n >= level a) by lia.
   clear H; rename H0 into H.
    remember (j+n) as i; clear Heqi.

   assert ((ALL  x : X , (HORec' i x <=> HORec' (S i) x)) (level a)).
   clear - H Hcont.
   remember (level a) as n; clear Heqn.
   revert n H; induction i; intros.
   replace n with 0 by lia. clear H.
   intro x.
   specialize (Hcont (fun _ => FF) (HORec' 0)).
   specialize (Hcont O).
   spec Hcont. repeat (hnf; intros). simpl in *.
   rewrite laterR_nat in H; exfalso; lia.
   specialize ( Hcont x).
    simpl in *. auto.
   intro x.
   apply (Hcont (HORec' i) (HORec' (S i))).
   intro s. intros ? ?. apply IHi.  simpl  in H0.  rewrite laterR_nat in H0; lia.
   clear - H0.
   destruct (H0 x a); auto.
   split; eauto.
  Qed.

End HORec.

Definition HORec {A} `{ag: ageable A} {EO : Ext_ord A} {X: Type} (f:  (X-> pred A) -> (X -> pred A)) (x: X) : pred A :=
     mkPred (fun a : A => app_pred (@HORec' A ag EO X f (level a) x) a).

Lemma HORec_fold_unfold {A} `{ageable A} {EO : Ext_ord A} : forall X f (H:HOcontractive (X:=X) f),
            HORec f = f (HORec f).
Proof.
  intros. rename H into ag. rename H0 into Hcont.
   unfold HORec.
    extensionality x.
    cut (forall a, HORec f x a <-> f (HORec f) x a).
    intros; apply pred_ext; hnf; firstorder.

    intro a; simpl.
    case_eq (age1 a); intros.
    apply age_level in H.
    remember (level a0) as n; clear a0 Heqn.
    destruct
      (@Hcont (HORec' f n) (HORec f) (level a)) with x a; [ | lia | ].
   rewrite H. clear a H.
    repeat (hnf; intros).
    simpl in H. apply laterR_level in H. simpl in H. unfold natLevel in H.
    assert (n >= level y) by lia.
    clear - Hcont H1.
    split; hnf; simpl; intros.
    generalize (necR_level _ _ H3); intro.
    generalize (necR_level _ _ H); intro.
    pose proof (ext_level _ _ H0) as Hl0.
    pose proof (ext_level _ _ H4) as Hl.
    apply (@HORec'_unage _ _ _ X f  Hcont (n - level x'') (level x'') b x'' ltac:(lia)).
    replace (n - level x'' + level x'') with n by lia.
    apply pred_upclosed with x'; auto.
    apply pred_nec_hereditary with a''; auto.
    specialize (H2 _ _ (necR_refl _) (ext_refl _)).
    apply (@HORec'_unage _ _ _ X f Hcont (n - level a'') (level a'') b a'' (PeanoNat.Nat.le_refl _)) in H2.
    generalize (necR_level _ _ H); intro.
    pose proof (ext_level _ _ H0) as Hl0.
    replace (n - level a'' + level a'') with n in H2 by lia.
    auto.
    split; intros.
    specialize (H2 _ _ (necR_refl _) (ext_refl _)).
    rewrite H in H2. simpl in H2.
    eapply H0 in H2; auto.
    eapply H1 in H2; auto.
    assert (app_pred (HORec' f (level a) x) a).
    rewrite H. apply H2.
     clear - H3 H4 H5 Hcont.
    apply (@HORec'_unage _ _ _ X f Hcont (level a - level x'') (level x'') x x'' (PeanoNat.Nat.le_refl _)).
    pose proof (ext_level _ _ H4).
    replace (level a - level x'' + level x'') with (level a)
        by (apply necR_level in H3; lia).
    apply pred_upclosed with x'; auto.
    apply pred_nec_hereditary with a; auto.
 (* None  case *)
    assert (level a = 0) by (apply age1_level0; auto).
    split; intros.
    destruct (@Hcont (fun _ => FF) (HORec f) (level a)) with x a; try lia.
     rewrite H0.
    repeat (hnf; intros); split; hnf; simpl; intros.
    simpl in H2.  apply laterR_level in H2. exfalso; lia.
        simpl in H2.  apply laterR_level in H2. clear - H2. simpl in H2.  unfold natLevel in H2; lia.
     specialize (H1 _ _ (necR_refl _) (ext_refl _)). rewrite H0 in H1. simpl in H1.
     eapply H2; auto.
     apply clos_rt_rt1n in H2.
    inv H2; [ | unfold age in H3; congruence].
    pose proof (ext_level _ _ H3) as <-.
    rewrite H0; simpl.
    specialize (Hcont (HORec f) (fun _ => FF)).
    specialize (Hcont 0).
    spec Hcont.
    simpl. intros. apply laterR_level in H2. simpl in H2. unfold natLevel in H2. exfalso; lia.
    specialize ( Hcont x).
    hnf in Hcont. specialize ( Hcont x'). spec Hcont. lia.
    eapply Hcont; auto.
    eapply pred_upclosed; eauto.
Qed.

Section recursive.
  Variable A:Type.
  Variable ag:ageable A.
  Variable eo:Ext_ord A.

  Variable f:pred A -> pred A.
  Variable Hc : contractive f.

  Lemma cont_HOcont : @HOcontractive A ag eo unit (fun x _ => f (x tt)).
  Proof.
    repeat intro.
    specialize ( H tt).
    eapply Hc; eauto.
  Qed.
End recursive.


Definition Rec {A} `{ageable A} {EO : Ext_ord A} f : pred A
  := HORec (fun x _ => f (x tt)) tt.

Lemma Rec_fold_unfold : forall {A} `{ageable A} {EO : Ext_ord A} f (H:contractive f),
  Rec f = f (Rec f).
Proof.
  intros.
  unfold Rec.
  pattern (HORec (fun x _ => f (x tt))) at 1.
  rewrite HORec_fold_unfold.
  auto.
  apply cont_HOcont; auto.
Qed.

End HoRec.

Export HoRec.
