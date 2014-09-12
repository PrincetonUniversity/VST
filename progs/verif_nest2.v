Require Import floyd.proofauto.
Require Import progs.nest2.

Local Open Scope logic.

Definition get_spec :=
 DECLARE _get
  WITH v : reptype' t_struct_b
  PRE  [] 
         PROP () LOCAL()
        SEP(`(data_at Ews t_struct_b (repinj _ v)) (eval_var _p t_struct_b))
  POST [ tint ]
         PROP() (LOCAL (`(eq (Vint (snd (snd v)))) (eval_id 1%positive))
         SEP (`(data_at Ews t_struct_b (repinj _ v)) (eval_var _p t_struct_b))).

Definition update22 (i: int) (v: reptype' t_struct_b) : reptype' t_struct_b :=
   (fst v, (fst (snd v), i)).

Definition set_spec :=
 DECLARE _set
  WITH i : int, v : reptype' t_struct_b
  PRE  [ _i OF tint ] 
         PROP () LOCAL(`(eq (Vint i)) (eval_id _i))
        SEP(`(data_at Ews t_struct_b (repinj _ v)) (eval_var _p t_struct_b))
  POST [ tvoid ]
        `(data_at Ews t_struct_b (repinj _ (update22 i v))) (eval_var _p t_struct_b).

Definition Vprog : varspecs := (_p, t_struct_b)::nil.

Definition Gprog : funspecs := 
    get_spec::set_spec::nil.

Lemma body_get:  semax_body Vprog Gprog f_get get_spec.
Proof.
 start_function.
name i _i.
apply (remember_value (eval_var _p t_struct_b)); intro p.
eapply semax_seq'.

ensure_normal_ret_assert;
 hoist_later_in_pre.
change (Efield (Efield (Evar _p t_struct_b) _y2 t_struct_a) _x2 tint)
 with (nested_efield (Evar _p t_struct_b) (_x2 :: _y2 :: nil) (tint :: t_struct_a :: nil)).
eapply semax_nested_efield_load_37'.
reflexivity.
reflexivity.
instantiate (1 := Struct_env). reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
entailer!.
simpl; auto.

unfold replace_nth; cbv beta;
               try (apply extract_exists_pre; intro_old_var (Sset _i (Efield (Efield (Evar _p t_struct_b) _y2 t_struct_a) _x2 tint)));
               abbreviate_semax.

simpl proj_reptype.
forward.
apply derives_refl.
Qed.

Lemma body_set:  semax_body Vprog Gprog f_set set_spec.
Proof.
 start_function.
name i_ _i.
apply (remember_value (eval_var _p t_struct_b)); intro p.

eapply semax_seq'.

ensure_normal_ret_assert;
 hoist_later_in_pre.
change (Efield (Efield (Evar _p t_struct_b) _y2 t_struct_a) _x2 tint)
 with (nested_efield (Evar _p t_struct_b) (_x2 :: _y2 :: nil) (tint :: t_struct_a :: nil)).

eapply semax_nested_efield_store_nth with (n := 0%nat).
reflexivity.
reflexivity.
instantiate (1 := Struct_env). reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
entailer!.
auto.
entailer!.

unfold replace_nth; cbv beta;
               try (apply extract_exists_pre; intro_old_var (Sassign (Efield (Efield (Evar _p t_struct_b) _y2 t_struct_a) _x2 tint)
        (Etempvar _i tint)));
               abbreviate_semax.

forward.
entailer!.
Qed.
