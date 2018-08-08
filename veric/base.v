(*moved to general_base.v
Require Export Coq.Arith.EqNat.
Require Export Coq.Relations.Relations.

Require Export compcert.exportclight.Clightdefs.
Require Export compcert.lib.Axioms.
Require Export compcert.lib.Coqlib.
Require Export compcert.lib.Integers.
Require Export compcert.lib.Floats.
Require Export compcert.lib.Maps.
Require Export compcert.common.AST.
Require Export compcert.common.Values.
Require Export compcert.common.Memdata.
Require Export compcert.common.Memtype.
Require Export compcert.common.Memory.
Require Export compcert.common.Globalenvs.
 *)
Require Export compcert.exportclight.Clightdefs.

Require Export VST.veric.general_base.
Require Export compcert.cfrontend.Ctypes.
Require Export compcert.cfrontend.Cop. (*new*)
Require Export compcert.cfrontend.Clight. 

Require Export EqNat.  (* do we need this? *)

(*moved to general_base:
Require Export VST.msl.Coqlib2. 
Require Export VST.veric.coqlib4.*)

Require Export VST.veric.Memory.

(*moved to mpred:
Instance EqDec_type: EqDec type := type_eq.
Set Implicit Arguments.

Definition funsig := (list (ident*type) * type)%type. (* argument and result signature *)
 *)

(*Open Scope Z.*)
