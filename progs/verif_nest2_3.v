Require Import floyd.proofauto.
Require Import progs.nest2.
Require Import floyd.data_at_lemmas.
Require Import floyd.data_at_load_store.

Local Open Scope logic.

Definition get_spec :=
 DECLARE _get
  WITH v : reptype' t_struct_b
  PRE  [] 
         PROP () LOCAL()
        SEP(`(data_at Ews t_struct_b (repinj _ v)) (eval_var _p t_struct_b))
  POST [ tint ]
         PROP() LOCAL (`(eq (Vint (snd (snd v)))) (eval_id 1%positive))
         SEP (`(data_at Ews t_struct_b (repinj _ v)) (eval_var _p t_struct_b)).

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

Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.
  
Lemma body_get:  semax_body Vprog Gtot f_get get_spec.
Proof.
 start_function.
name i _i.
apply (remember_value (eval_var _p t_struct_b)); intro p.

unfold_data_at 1%nat.
unfold_field_at 2%nat.

eapply semax_seq'.
+ ensure_normal_ret_assert;
  hoist_later_in_pre.

  change (Efield (Efield (Evar _p t_struct_b) _y2 t_struct_a) _x2 tint) with
         (nested_efield (Evar _p t_struct_b) (_x2 :: _y2 ::nil) (tint :: t_struct_a:: nil) ).

  eapply semax_nested_data_load'.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold eq_rect_r.
    instantiate (2:= eq_refl).
    instantiate (2:= eq_refl).
    rewrite <- eq_rect_eq.
    reflexivity.
  - repeat apply andp_right.
    * go_lower.
      apply prop_right.
      tauto.
    * instantiate (1:= (Vint (snd (snd v)))).
      go_lower.
      apply prop_right.
      tauto.
    * instantiate (1:= Ews).
      simpl typeof. simpl eval_lvalue.
      simpl. intros.
      normalize.
      cancel.
+ apply extract_exists_pre. intro_old_var (Sset _i (Efield (Efield (Evar _p t_struct_b) _y2 t_struct_a) _x2 tint)).
  abbreviate_semax.
  forward.

unfold_data_at 1%nat.
unfold_field_at 5%nat.

cancel.
Qed.

Lemma body_set:  semax_body Vprog Gtot f_set set_spec.
Proof.
 start_function.
name i_ _i.
apply (remember_value (eval_var _p t_struct_b)); intro p.

unfold_data_at 1%nat.
unfold_field_at 2%nat.

eapply semax_seq'.
+ ensure_normal_ret_assert;
  hoist_later_in_pre.
  
  change (Efield (Efield (Evar _p t_struct_b) _y2 t_struct_a) _x2 tint) with
         (nested_efield (Evar _p t_struct_b) (_x2 :: _y2 ::nil) (tint :: t_struct_a:: nil) ).

  eapply semax_nested_data_store'; [reflexivity | reflexivity | | reflexivity | 
    instantiate (2:=1%nat); reflexivity | | auto | |].
  - unfold eq_rect_r.
    instantiate (2:= eq_refl).
    instantiate (2:= eq_refl).
    rewrite <- eq_rect_eq.
    reflexivity.
  - unfold liftx, lift. simpl. intros.
    instantiate (1:= Ews).
    apply nested_data_at_nested_data_at_.
    reflexivity.
  - auto.
  - simpl. normalize.
  - instantiate (1:= (Vint i)). simpl. go_lower. normalize.
    apply prop_right.
    rewrite <- H.
    reflexivity.
+ unfold replace_nth; cbv beta.
abbreviate_semax.
forward. (* return; *)

unfold_data_at 1%nat.
unfold_field_at 5%nat.

cancel.
Qed.

