Require Import VST.floyd.proofauto.
Require Import Recdef.
Existing Instance NullExtension.Espec.
Require Import VST.progs.switch.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition twice_spec :=
  DECLARE _twice
    WITH n : Z
    PRE [ _n OF tint ]
      PROP  (Int.min_signed <= n+n <= Int.max_signed)
      LOCAL (temp _n (Vint (Int.repr n)))
      SEP ()
    POST [ tint ]
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr (n+n))))
      SEP ().


Definition f_spec :=
  DECLARE _f
    WITH x : Z
    PRE [ _x OF tuint ]
      PROP  (0 <= x <= Int.max_unsigned)
      LOCAL (temp _x (Vint (Int.repr x)))
      SEP ()
    POST [ tint ]
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr 1)))
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
repeat forward; entailer!.
Qed.

Lemma body_f: semax_body Vprog Gprog f_f f_spec.
Proof.
start_function.
forward_if (@FF (environ->mpred) _).
forward.
forward.
forward.
forward.
forward.
Qed.


