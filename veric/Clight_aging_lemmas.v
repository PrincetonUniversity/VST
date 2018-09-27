Require Import compcert.common.Memory.
Require Import VST.msl.seplog.
Require Import VST.msl.ageable.
Require Import VST.msl.age_to.
Require Import VST.veric.coqlib4.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.compcert_rmaps. 
Require Import VST.veric.semax.
Require Import VST.veric.juicy_extspec.

Require Import VST.veric.mem_lessdef.
Require Import VST.veric.age_to_resource_at.

Require Import VST.veric.aging_lemmas.

Set Bullet Behavior "Strict Subproofs".

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
