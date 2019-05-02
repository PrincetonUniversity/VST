Require Import VST.floyd.proofauto.
Require Import VST.progs.printf.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.floyd.printf.

Definition fprintf_spec :=
 DECLARE _fprintf (fprintf_placeholder_spec ___sFILE).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ] main_post prog nil gv.

Definition Gprog : funspecs :=   ltac:(with_library prog [ fprintf_spec ]).

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
repeat do_string2bytes.
repeat (sep_apply data_at_to_cstring; []).
forward_fprintf (gv __stdout) tt.
forward_fprintf (gv __stdout) (Int.repr 2, tt).
forward.
Qed.
