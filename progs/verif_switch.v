Require Import floyd.proofauto.
Require Import Coqlib.
Require Import Recdef.
Existing Instance NullExtension.Espec.
Require Import progs.switch.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition twice_spec :=
  DECLARE _twice
    WITH n : Z
    PRE [ _n OF tint ]
      PROP  (0 <= n+n <= Int.max_unsigned)
      LOCAL (temp _n (Vint (Int.repr n)))
      SEP ()
    POST [ tint ]
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr (n+n))))
      SEP ().

Definition Gprog : funspecs :=   ltac:(with_library prog [twice_spec]).

Lemma body_twice: semax_body Vprog Gprog f_twice twice_spec.
Proof.
start_function.
forward_if (PROP() LOCAL(temp _n (Vint (Int.repr (n+n)))) SEP()).
repeat forward; entailer!.
repeat forward; entailer!.
repeat forward; entailer!.
repeat forward; entailer!.
repeat forward; entailer!.
Qed.

