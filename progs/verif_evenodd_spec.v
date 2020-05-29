Require Import VST.floyd.proofauto.
Require Import VST.progs.even.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope assert.

Definition odd_spec :=
 DECLARE _odd
  WITH z : Z, b: unit
  PRE [ tuint]
    PROP(0 <= z <= Int.max_signed) PARAMS(Vint (Int.repr z)) SEP()
  POST [ tint ]
    PROP() RETURN(Vint (if Z.odd z then Int.one else Int.zero)) SEP().

Definition even_spec :=
 DECLARE _even
  WITH z : Z
  PRE [ tuint]
    PROP(0 <= z <= Int.max_signed) PARAMS(Vint (Int.repr z)) SEP()
  POST [ tint ]
    PROP() RETURN (Vint (if Z.even z then Int.one else Int.zero)) SEP().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]
    PROP() RETURN (Vint (if Z.even 42 then Int.one else Int.zero)) SEP(has_ext tt).
