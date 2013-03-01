Load loadpath.
Require Export Axioms.
Require Export Coqlib.
Require Export AST.
Require Export Integers.
Require Export Floats.
Require Export Values.
Require Export Maps.
Require Export Memdata.
Require Export Memtype.
Require Export Memory.
Require Export Globalenvs.
Require Export Ctypes.
Require Export Clight.

Require Export EqNat.
Require Export sepcomp.Coqlib2.
Require Export sepcomp.Address.
Require Export Relations.

Set Implicit Arguments.

Require Export msl.eq_dec.
Instance EqDec_ident: EqDec ident := ident_eq.

Instance EqDec_byte: EqDec byte := Byte.eq_dec.

Instance EqDec_type: EqDec type := type_eq.
Instance EqDec_memval: EqDec memval.
Proof.
  hnf. repeat decide equality; apply eq_dec.
Qed.

Definition funsig := (list (ident*type) * type)%type. (* argument and result signature *)
