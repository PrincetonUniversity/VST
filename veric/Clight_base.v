Require Export compcert.exportclight.Clightdefs.

Require Export VST.veric.base.
Require Export compcert.cfrontend.Ctypes.
Require Export compcert.cfrontend.Cop. (*new*)
Require Export compcert.cfrontend.Clight. 

Require Export EqNat.  (* do we need this? *)

Require Export VST.veric.Memory.

(*moved to mpred:
Instance EqDec_type: EqDec type := type_eq.
Set Implicit Arguments.

Definition funsig := (list (ident*type) * type)%type. (* argument and result signature *)
 *)

(*Open Scope Z.*)
