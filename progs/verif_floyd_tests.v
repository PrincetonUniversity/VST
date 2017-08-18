Require Import VST.floyd.proofauto.
Require Import VST.progs.floyd_tests.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition test_sizeof_spec :=
 DECLARE _test_sizeof
  WITH p: val, sh : share, i: Z
  PRE [ _p OF (tptr tint) ]
          PROP  (readable_share sh; 0 <= i <= Int.max_signed)
          LOCAL (temp _p p) SEP (data_at sh tint (Vint (Int.repr i)) p)
  POST [ tint ]
        PROP () LOCAL(temp ret_temp  (Vint (Int.repr 9)))
           SEP (data_at sh tint (Vint (Int.repr i)) p).

Definition Gprog : funspecs := 
        ltac:(with_library prog [test_sizeof_spec]).

Lemma body_test_sizeof_spec: semax_body Vprog Gprog f_test_sizeof test_sizeof_spec.
Proof.
start_function.
forward.
forward.
forward.
Qed.
