Require Import VST.floyd.proofauto.
Require Import VST.progs.structcopy.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

Definition tfoo := Tstruct _foo noattr.

Definition f_spec :=
 DECLARE _f
  WITH p: val, i: Z, j: Z
  PRE  [ _p OF tptr tfoo]
      PROP  ( )
      LOCAL (temp _p p)
      SEP (data_at Ews tfoo (Vint (Int.repr i), Vint (Int.repr j)) p)
  POST [ tuint ]
      PROP() LOCAL(temp ret_temp (Vint (Int.repr (i+j))))
      SEP (data_at Ews tfoo (Vint (Int.repr i), Vint (Int.repr j)) p).


Definition Gprog : funspecs :=   ltac:(with_library prog [f_spec ]).

Lemma body_f:  semax_body Vprog Gprog f_f f_spec.
Proof.
Fail  start_function.
Abort.
