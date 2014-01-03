Require Import floyd.proofauto.
Require Import progs.float.

Local Open Scope logic.

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.


Definition Vprog : varspecs := (_s, t_struct_foo)::nil.

Definition Gprog : funspecs := 
     main_spec::nil.

Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.


Lemma body_main:  semax_body Vprog Gtot f_main main_spec.
Proof.
start_function.
name x1 _x1.
name y1 _y1.
forward.
unfold tc_expr, typecheck_expr.
Admitted.

