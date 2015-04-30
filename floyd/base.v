Require Export Clightdefs.
Require Export veric.SeparationLogic.
Require Export msl.Extensionality.
Require Export Coqlib msl.Coqlib2 floyd.coqlib3.
Require Export veric.juicy_extspec.
Require veric.SeparationLogicSoundness.
Export SeparationLogicSoundness.SoundSeparationLogic.CSL.
Require Import veric.NullExtension.

Local Open Scope logic.

Lemma prop_and {A} {NA: NatDed A}: 
    forall P Q: Prop, prop (P /\ Q) = (prop P && prop Q).
Proof. intros. apply pred_ext. apply prop_left. intros [? ?]; normalize.
   normalize.
Qed.

Hint Rewrite <- prop_and : gather_prop.

Lemma gather_prop_left {A}{NA: NatDed A}:
  forall P Q R,  !! P && (!! Q && R) = !!(P/\Q) && R.
Proof. intros. rewrite <- andp_assoc. rewrite <- prop_and; auto.
Qed.

Lemma gather_prop_right {A}{NA: NatDed A}:
  forall P Q R,  R && !! P && !! Q = !!(P/\Q) && R.
Proof. intros. rewrite andp_assoc. rewrite andp_comm.  rewrite <- prop_and; auto.
Qed.
Hint Rewrite gather_prop_left gather_prop_right : gather_prop.

Definition not_a_prop {A} (P: A) := True.

Ltac not_a_prop := match goal with
  | |- not_a_prop  (prop _) => fail 1 
  | |- _ => apply I 
end.

Lemma flip_prop {A}{NA: NatDed A}: forall P Q, 
      not_a_prop P -> (P&& !! Q = !! Q && P).
Proof. intros. apply andp_comm. Qed.

Hint Rewrite @flip_prop using not_a_prop : gather_prop.

Lemma gather_prop3 {A}{NA: NatDed A}:
  forall P Q R,  not_a_prop R -> not_a_prop Q -> R && (!! P && Q) = !!P && (R && Q).
Proof. intros. rewrite andp_comm. rewrite andp_assoc.
        rewrite (andp_comm Q); auto.
Qed.

Hint Rewrite @gather_prop3 using not_a_prop : gather_prop.


Lemma gather_prop4 {A}{NA: NatDed A}:
  forall P Q R,  not_a_prop R -> not_a_prop Q -> (!!P && R) && Q = !!P && (R && Q).
Proof. intros. rewrite andp_assoc. auto. 
Qed.
Hint Rewrite @gather_prop4 using not_a_prop : gather_prop.

Lemma gather_prop5 {A}{NA: NatDed A}:
  forall P Q R,  not_a_prop R -> not_a_prop Q -> (R && !!P && Q) = !!P && (R && Q).
Proof. intros. rewrite andp_assoc. rewrite andp_comm. rewrite andp_assoc.
  f_equal; apply andp_comm.
Qed.
Hint Rewrite @gather_prop5 using not_a_prop : gather_prop.

Hint Rewrite @sepcon_andp_prop @sepcon_andp_prop' : gather_prop.

Hint Rewrite <- sepcon_assoc : gather_prop.

Lemma go_lower_lem1:
  forall (P1 P: Prop) (QR PQR: mpred),
      (P1 -> prop P && QR |-- PQR) ->
      (prop (P1 /\ P ) && QR |-- PQR).
Proof.
 intros.
 apply derives_extract_prop; intros [? ?].
 apply derives_trans with (!!P && QR).
 apply andp_right; auto. apply prop_right; auto.
 apply H; auto.
Qed.

Lemma go_lower_lem1':
  forall (P1 P2 P: Prop) (QR PQR: mpred),
      (prop (P1 /\ (P2 /\ P)) && QR |-- PQR) ->
      (prop ((P1 /\ P2) /\ P ) && QR |-- PQR).
Proof.
 intros.
 eapply derives_trans;  [ | apply H].
 apply andp_derives; auto.
 apply prop_derives; intuition.
Qed.

Lemma co_alignof_pos: forall co, (co_alignof co > 0)%Z.
Proof.
  intros.
  destruct (co_alignof_two_p co).
  pose proof two_power_nat_pos x.
  omega.
Qed.

Section GET_CO.

Context {cs: compspecs}.
Context {csl: compspecs_legal cs}.

Open Scope Z.

Definition co_default (s: struct_or_union): composite.
  apply (Build_composite s nil noattr 0 1 0).
  + omega.
  + exists 0%nat; auto.
  + exists 0; auto.
Defined.

Definition get_co id :=
  match cenv_cs ! id with
  | Some co => co
  | _ => co_default Struct
  end.

Lemma co_default_consistent: forall su, composite_consistent cenv_cs (co_default su).
Proof.
  intros.
  split.
  + reflexivity.
  + reflexivity.
  + destruct su; reflexivity.
  + reflexivity.
Qed.

Lemma get_co_consistent: forall id, composite_consistent cenv_cs (get_co id).
Proof.
  intros.
  unfold get_co.
  destruct (cenv_cs ! id) as [co |] eqn:CO.
  + exact (cenv_consistent_cs id co CO).
  + apply co_default_consistent.
Qed.

Lemma get_co_members_nil_sizeof_0: forall id,
  co_members (get_co id) = nil -> co_sizeof (get_co id) = 0%Z.
Proof.
  unfold get_co.
  intros.
  destruct (cenv_cs ! id) as [co |] eqn:?H; [destruct (co_su co) eqn:?H |].
  + pose proof co_consistent_sizeof cenv_cs co (cenv_consistent_cs id co H0).
    unfold sizeof_composite in H2.
    rewrite H1 in H2; clear H1.
    rewrite H in H2; clear H.
    simpl in H2.
    rewrite align_0 in H2 by apply co_alignof_pos.
    auto.
  + pose proof co_consistent_sizeof cenv_cs co (cenv_consistent_cs id co H0).
    unfold sizeof_composite in H2.
    rewrite H1 in H2; clear H1.
    rewrite H in H2; clear H.
    simpl in H2.
    rewrite align_0 in H2 by apply co_alignof_pos.
    auto.
  + reflexivity.
Qed.

Lemma get_co_members_no_replicate: forall id,
  members_no_replicate (co_members (get_co id)) = true.
Proof.
  intros.
  unfold get_co.
  destruct (cenv_cs ! id) as [co |] eqn:?H.
  + exact (cenv_legal_fieldlist id co H).
  + reflexivity.
Qed.

Lemma sizeof_Tstruct: forall id a,
  sizeof cenv_cs (Tstruct id a) = co_sizeof (get_co id).
Proof.
  intros.
  simpl sizeof. unfold get_co.
  destruct (cenv_cs ! id); auto.
Qed.

Lemma sizeof_Tunion: forall id a,
  sizeof cenv_cs (Tunion id a) = co_sizeof (get_co id).
Proof.
  intros.
  simpl sizeof. unfold get_co.
  destruct (cenv_cs ! id); auto.
Qed.

End GET_CO.
