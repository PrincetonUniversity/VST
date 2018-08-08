Require Import compcert.common.Memory.
Require Import VST.msl.seplog.
Require Import VST.msl.ageable.
Require Import VST.msl.age_to.
Require Import VST.veric.coqlib4.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.compcert_rmaps. 
Require Import VST.veric.semax.
Require Import VST.veric.juicy_extspec.

Require Import VST.veric.general_mem_lessdef.
Require Import VST.veric.age_to_resource_at.

Require Import VST.veric.general_aging_lemmas.

Set Bullet Behavior "Strict Subproofs".

Ltac hered :=
  match goal with
    H : ?P ?x |- ?P ?y => revert H
  end;
  match goal with
    |- ?P ?x -> ?P ?y =>
    cut (hereditary age P);
    [ let h := fresh "h" in intros h; apply h; auto | ]
  end.

Ltac agejoinhyp :=
  match goal with
    H : sepalg.join _ _ ?m, A : age ?m _ |- _ =>
    pose proof age1_join2 _ H A; clear H
  end.

Ltac agehyps :=
  match goal with
    H : age ?x ?y, HH : ?P ?x |- _ =>
    cut (P y);
    [ clear HH; intros HH
    | hered;
      try apply pred_hered;
      try apply predicates_hered.exactly_obligation_1]
  end.

Lemma jsafeN_age Z Jspec ge ora q n jm jmaged :
  ext_spec_stable age (JE_spec _ Jspec) ->
  age jm jmaged ->
  le n (level jmaged) ->
  @jsafeN Z Jspec ge n ora q jm ->
  @jsafeN Z Jspec ge n ora q jmaged.
Proof. intros. eapply jsafeN__age; eauto. Qed.

Lemma jsafeN_age_to Z Jspec ge ora q n l jm :
  ext_spec_stable age (JE_spec _ Jspec) ->
  le n l ->
  @jsafeN Z Jspec ge n ora q jm ->
  @jsafeN Z Jspec ge n ora q (age_to l jm).
Proof. intros. eapply jsafeN__age_to; eauto. Qed.
