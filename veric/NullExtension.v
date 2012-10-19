Load loadpath.
Require Import veric.base.
Require Import veric.Clight_new.
Require Import veric.Clight_lemmas.
Require Import veric.step_lemmas.
Require Import veric.SeparationLogic.
Require Import veric.juicy_extspec.
Require Import veric.juicy_mem.
Require Import veric.extspec.

Module NullExtension <: EXTERNAL_SPEC.

Definition Z := unit.
Definition dryspec : external_specification juicy_mem external_function unit
  := Build_external_specification juicy_mem external_function unit
     (*ext_spec_type*)
     (fun ef => False)
     (*ext_spec_pre*)
     (fun ef Hef tys vl m z => False) 
     (*ext_spec_post*)
     (fun ef Hef ty vl m z => False).

Definition Hspec : juicy_ext_spec unit .
 refine (Build_juicy_ext_spec _ dryspec _ _).
Proof.
simpl; intros; contradiction.
simpl; intros; contradiction.
Defined.

End NullExtension.
