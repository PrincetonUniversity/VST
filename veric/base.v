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
Require Export compcert.cfrontend.Ctypes.
Require Export compcert.cfrontend.Clight.

Require Export msl.Coqlib2.
Require Export veric.coqlib4.
Require Export sepcomp.Address.

Set Implicit Arguments.

Require Export msl.eq_dec.
Instance EqDec_ident: EqDec ident := ident_eq.

Instance EqDec_byte: EqDec byte := Byte.eq_dec.

Instance EqDec_type: EqDec type := type_eq.

Instance EqDec_int64: EqDec int64 := Int64.eq_dec.
Instance EqDec_float32: EqDec float32 := Float32.eq_dec.

Instance EqDec_memval: EqDec memval.
Proof.
  hnf. repeat decide equality; apply eq_dec.
Defined.

Instance EqDec_val: EqDec val.
Proof.
hnf. decide equality; apply eq_dec.
Defined.

Instance EqDec_quantity: EqDec quantity.
Proof.
hnf. decide equality.
Defined.

Definition funsig := (list (ident*type) * type)%type. (* argument and result signature *)

Lemma range_dec: forall a b c: Z, {a <= b < c}+{~(a <= b < c)}.
Proof. intros. destruct (zle a b). destruct (zlt b c). left; split; auto.
  right;  omega. right; omega.
Qed.

(*Open Scope Z.*)