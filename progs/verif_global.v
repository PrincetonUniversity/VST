Require Import floyd.proofauto.
Require Import progs.global.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition f_spec :=
 DECLARE _f
  WITH g: val
  PRE [  ]
          PROP  ()
          LOCAL (gvar _g g)
          SEP   (data_at Ews tint (Vint (Int.repr 7)) g)
  POST [ tint ]
        PROP () LOCAL(temp ret_temp  (Vint (Int.repr 7)))
           SEP (data_at Ews tint (Vint (Int.repr 7)) g).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog [] u
  POST [ tint ] main_post prog [] u.

Definition Gprog : funspecs :=
        ltac:(with_library prog [f_spec; main_spec]).

Lemma body_f: semax_body Vprog Gprog f_f f_spec.
Proof.
start_function.
forward.  (* x = g; *)
forward.  (* return x; *)
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
name g _g.
start_function.
change (data_at Ews tuint) with (data_at Ews tint).
forward_call g.
forward.
Qed.


