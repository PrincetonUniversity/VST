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
name y2 _y2.
unfold v_s.
apply semax_pre with (PROP() LOCAL () 
            SEP(`(data_at Ews t_struct_foo (Vint (Int.repr 5), 
                         (Vfloat (Float.singleoffloat (Float.double_of_bits
                              (Int64.repr 4614861056357957632))),
                          Vfloat (Float.double_of_bits (Int64.repr 0)))))
                (eval_var _s t_struct_foo))).
go_lower. apply andp_derives; auto. apply andp_derives; auto.
simpl_data_at.
normalize.
repeat rewrite sepcon_assoc.
apply sepcon_derives.
eapply mapsto_field_at'.
reflexivity.
reflexivity.
simpl.
rewrite offset_offset_val. reflexivity.
apply I.
reflexivity.
apply sepcon_derives.
eapply mapsto_field_at'.
reflexivity.
reflexivity.
simpl.
rewrite offset_offset_val. reflexivity.
apply I.
reflexivity.
eapply mapsto_field_at'.
reflexivity.
reflexivity.
simpl.
rewrite offset_offset_val. reflexivity.
apply I.
reflexivity.
simpl_data_at.
forward.
forward.
forward.
forward.
forward.
unfold main_post.
entailer!.
Qed.
