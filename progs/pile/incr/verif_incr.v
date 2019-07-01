Require Import VST.floyd.proofauto.
Require Import incr.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition incr1_spec :=
 DECLARE _incr1
 WITH i: Z, a: val, sh: share, private: list val
 PRE [ _i OF tint, _auxdata OF tptr tuint ]
    PROP (0 <= i < Int.max_signed; writable_share sh)
    LOCAL(temp _i (Vint (Int.repr i)); temp _auxdata a)
    SEP(data_at sh (tarray tuint 10) private a)
 POST [ tint ]
   EX private':list val,
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr (i+1))))
    SEP(data_at sh (tarray tuint 10) private' a).

Definition incr2_spec :=
 DECLARE _incr2
 WITH i: Z
 PRE [ _i OF tint, _auxdata OF tptr tuint ]
    PROP (0 <= i < Int.max_signed)
    LOCAL(temp _i (Vint (Int.repr i)))
    SEP()
 POST [ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr (i+1))))
    SEP().

Lemma sub_incr12:
  funspec_sub (snd incr2_spec)  (snd incr1_spec).
Proof.
apply NDsubsume_subsume.
split; extensionality x; reflexivity.
split3; auto.
intros [[[i a] sh] private].
Exists i (data_at sh (tarray tuint 10) private a).
rewrite !insert_SEP.
apply andp_right.
entailer!.
apply prop_right.
Exists private.
entailer!.
Qed.

Definition incr3_spec :=
 DECLARE _incr3
 WITH i: Z, gv: globals, sh: share, private: list val
 PRE [ _i OF tint ]
    PROP (0 <= i < Int.max_signed; writable_share sh)
    LOCAL(temp _i (Vint (Int.repr i)); gvars gv)
    SEP(data_at sh (tarray tuint 10) private (gv _global_auxdata))
 POST [ tint ]
   EX private':list val,
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr (i+1))))
    SEP(data_at sh (tarray tuint 10) private' (gv _global_auxdata)).

Definition incr4_spec :=
 DECLARE _incr4
 WITH i: Z
 PRE [ _i OF tint ]
    PROP (0 <= i < Int.max_signed)
    LOCAL(temp _i (Vint (Int.repr i)))
    SEP()
 POST [ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr (i+1))))
    SEP().

Lemma sub_incr34:
  funspec_sub (snd incr4_spec)  (snd incr3_spec).
Proof.
apply NDsubsume_subsume.
split; extensionality x; reflexivity.
split3; auto.
intros [[[i gv] sh] private].
Exists i (data_at sh (tarray tuint 10) private (gv _global_auxdata)).
rewrite !insert_SEP.
simpl funsig_tycontext.
apply andp_right.
forget (gv _global_auxdata) as p.
entailer!.
apply prop_right.
Exists private.
entailer!.
Qed.
