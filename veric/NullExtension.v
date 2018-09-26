Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.base.
(*Lenb - do we need these?
  Require Import VST.veric.Clight_new.
Require Import VST.veric.Clight_lemmas.*)
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_mem.

Definition dryspec : external_specification juicy_mem external_function unit
  := Build_external_specification juicy_mem external_function unit
     (*ext_spec_type*)
     (fun ef => False)
     (*ext_spec_pre*)
     (fun ef Hef ge tys vl m z => False)
     (*ext_spec_post*)
     (fun ef Hef ge ty vl m z => False)
     (*ext_spec_exit*)
     (fun rv m z => False).

Definition Espec : OracleKind.
 refine (Build_OracleKind unit (Build_juicy_ext_spec _ dryspec _ _ _)).
Proof.
simpl; intros; contradiction.
simpl; intros; contradiction.
simpl; intros; intros ? ? ? ?; contradiction.
Defined.

