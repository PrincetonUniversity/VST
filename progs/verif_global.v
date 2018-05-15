Require Import VST.floyd.proofauto.
Require Import VST.progs.global.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition h_spec :=
 DECLARE _h
  WITH gv: globals
  PRE [  ]
          PROP  ()
          LOCAL (gvars gv)
          SEP   (data_at Ews tint (Vint (Int.repr 7)) (gv _g))
  POST [ tint ]
        PROP () LOCAL(temp ret_temp  (Vint (Int.repr 7)))
           SEP (data_at Ews tint (Vint (Int.repr 7)) (gv _g)).

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog [] gv
  POST [ tint ] main_post prog [] gv.

Definition Gprog : funspecs :=
        ltac:(with_library prog [h_spec; main_spec]).

Lemma body_h: semax_body Vprog Gprog f_h h_spec.
Proof.
start_function.
forward.  (* x = g; *)
forward.  (* return x; *)
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
rewrite data_at_tuint_tint.
forward_call gv.
forward.
Qed.


