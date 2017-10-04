Require Import VST.floyd.proofauto.
Require Import VST.progs.even.
Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope assert.

Definition odd_spec :=
 DECLARE _odd
  WITH z : Z, b: unit
  PRE [ _n OF tuint]
    PROP(0 <= z <= Int.max_signed) LOCAL(temp _n (Vint (Int.repr z))) SEP()
  POST [ tint ]
    PROP() LOCAL(temp ret_temp (Vint (if Z.odd z then Int.one else Int.zero))) SEP().

Definition even_spec :=
 DECLARE _even
  WITH z : Z
  PRE [ _n OF tuint]
    PROP(0 <= z <= Int.max_signed) LOCAL(temp _n (Vint (Int.repr z))) SEP()
  POST [ tint ]
    PROP() LOCAL(temp ret_temp (Vint (if Z.even z then Int.one else Int.zero))) SEP().

Definition main_spec :=
 DECLARE _main
  WITH z : Z, v : val
  PRE [ ] PROP() LOCAL() SEP ()
  POST [ tint ]
    PROP() LOCAL(temp ret_temp (Vint (if Z.even 42 then Int.one else Int.zero))) SEP().
