Require Import VST.floyd.proofauto.
Require Import VST.progs.printf.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.floyd.printf.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ] main_post prog nil gv.

Definition Gprog : funspecs :=  
   ltac:(with_library prog (ltac:(make_printf_specs prog) ++ [ main_spec ])).

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
repeat do_string2bytes.
repeat (sep_apply data_at_to_cstring; []).
forward_printf tt.
forward_fprintf (gv __stdout) ((Ers, string2bytes "line", gv ___stringlit_2), (Int.repr 2, tt)).
forward.
Qed.
