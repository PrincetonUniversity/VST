Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat. Import NoOracle.
Require Import Recdef.
Require Import VST.progs.switch.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition twice_spec : ident * funspec :=
  DECLARE _twice
    WITH n : Z
    PRE [ tint ]
      PROP  (Int.min_signed <= n+n <= Int.max_signed)
      PARAMS (Vint (Int.repr n))
      SEP ()
    POST [ tint ]
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr (n+n))))
      SEP ().


Definition f_spec : ident * funspec :=
  DECLARE _f
    WITH x : Z
    PRE [ tuint ]
      PROP  (0 <= x <= Int.max_unsigned)
      PARAMS (Vint (Int.repr x))
      SEP ()
    POST [ tint ]
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr 1)))
      SEP ().


Definition Gprog : funspecs :=   ltac:(with_library prog [twice_spec]).

Lemma body_twice: semax_body Vprog Gprog f_twice twice_spec.
Proof.
start_function.
forward_if (temp _n (Vint (Int.repr (n+n)))).
repeat forward; entailer!!.
repeat forward; entailer!!.
repeat forward; entailer!!.
repeat forward; entailer!!.
repeat forward; entailer!!.
repeat forward; entailer!!.
Qed.

Lemma body_f: semax_body Vprog Gprog f_f f_spec.
Proof.
start_function.
forward_if (FF : assert).
forward.
forward.
forward.
forward.
forward.
Qed.
