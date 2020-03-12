Require Import VST.floyd.proofauto.
Require Import incr.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition incr1_spec :=
 DECLARE _incr1
 WITH i: Z, a: val, sh: share, private: list val
 PRE [ tint, tptr tuint ]
    PROP (0 <= i < Int.max_signed; writable_share sh)
    PARAMS (Vint (Int.repr i); a) GLOBALS ()
    SEP(data_at sh (tarray tuint 10) private a)
 POST [ tint ]
   EX private':list val,
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr (i+1))))
    SEP(data_at sh (tarray tuint 10) private' a).

Definition incr2_spec :=
 DECLARE _incr2
 WITH i: Z, a: val
 PRE [ tint, tptr tuint ]
    PROP (0 <= i < Int.max_signed)
    PARAMS (Vint (Int.repr i); a) GLOBALS ()
    SEP()
 POST [ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr (i+1))))
    SEP().

Lemma sub_incr12:
  funspec_sub (snd incr2_spec)  (snd incr1_spec).
Proof.
do_funspec_sub. destruct w as [[[i a] sh] data]. clear H.
Exists (i,a) (data_at sh (tarray tuint 10) data a). simpl; entailer!.
intros tau ? ?. Exists data.
entailer!.
Qed.

Definition incr3_spec :=
 DECLARE _incr3
 WITH i: Z, gv: globals, sh: share, private: list val
 PRE [ tint ]
    PROP (0 <= i < Int.max_signed; writable_share sh)
    PARAMS (Vint (Int.repr i)) GLOBALS (gv)
    SEP(data_at sh (tarray tuint 10) private (gv _global_auxdata))
 POST [ tint ]
   EX private':list val,
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr (i+1))))
    SEP(data_at sh (tarray tuint 10) private' (gv _global_auxdata)).

Definition incr4_spec :=
 DECLARE _incr4
 WITH i: Z
 PRE [ tint ]
    PROP (0 <= i < Int.max_signed)
    PARAMS (Vint (Int.repr i)) GLOBALS ()
    SEP()
 POST [ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr (i+1))))
    SEP().

Lemma sub_incr34:
  funspec_sub (snd incr4_spec)  (snd incr3_spec).
Proof.
do_funspec_sub. destruct w as [[[i gv] sh] data]. clear H.
Exists i (data_at sh (tarray tuint 10) data (gv _global_auxdata)).
simpl; entailer!.
intros tau ? ?. Exists data.
entailer!.
Qed.