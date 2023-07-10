Require Import VST.veric.SequentialClight.
Require Import VST.floyd.proofauto.

(* Concrete instance of the Iris typeclasses for no ghost state or external calls *)
#[local] Instance default_pre : VSTGpreS unit (VSTΣ unit) := subG_VSTGpreS _.

#[export] Program Instance VST_default : VSTGS NullEspec (VSTΣ unit) := Build_VSTGS _ _ _ _.
Next Obligation.
Proof.
  split.
  - split; split; try apply _.
    + exact 1%positive.
    + exact 2%positive.
    + exact 3%positive.
    + apply lcGpreS_inG.
    + exact 4%positive.
  - split; try apply _.
    + exact 5%positive.
    + exact 6%positive.
  - split; try apply _.
    exact 7%positive.
Defined.
Next Obligation.
Proof.
  split; try apply _.
  exact 8%positive.
Defined.

(* quick notation fix, not actually what VST users are used to *)
Require Export iris.bi.ascii.
