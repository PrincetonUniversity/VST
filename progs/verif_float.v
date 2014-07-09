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

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
name x1 _x1.
name y1 _y1.
name y2 _y2.
unfold v_s.

apply semax_pre with  (PROP() LOCAL ()
  SEP(`(mapsto Ews tuint) (`(offset_val (Int.repr 0)) (eval_var _s t_struct_foo))
        `(Vint (Int.repr 5));
      `(mapsto Ews tfloat) (`(offset_val (Int.repr 4)) (eval_var _s t_struct_foo))
        `(Vfloat (Float.singleoffloat (Float.double_of_bits (Int64.repr 4614861056357957632))));
     `(mapsto Ews tdouble) (`(offset_val (Int.repr 8)) (eval_var _s t_struct_foo))
         `(Vfloat (Float.double_of_bits (Int64.repr 0))))).
go_lower. apply andp_derives; auto. apply andp_derives; auto.
cancel.

forward.
forward.
forward.
forward.
forward.
unfold main_post.
entailer!.
Qed.
