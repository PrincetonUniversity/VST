Require Export compcert.lib.Axioms.
Require Export Coqlib.
Require Export AST.
Require Export Integers.
Require Export Floats.
Require Export compcert.common.Values.
Require Export Maps.
Require Export Memdata.
Require Export Memtype.
Require Export Memory.
Require Export Globalenvs.
Require Export Ctypes.
Require Export Clight.

Require Export EqNat.
Require Export msl.Coqlib2.
Require Export veric.coqlib4.
Require Export sepcomp.Address.
Require Export Relations.

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

