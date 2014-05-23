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

Lemma body_get:  semax_body Vprog Gprog f_get get_spec.
Proof.
 start_function.
name i _i.
apply (remember_value (eval_var _p t_struct_b)); intro p.

unfold_data_at 1%nat.
unfold_field_at 2%nat.

eapply semax_seq'.
+ rewrite nested_data_at_data_at at 1; [| reflexivity].

  unfold nested_field_lemmas.nested_field_type2, nested_field_lemmas.nested_field_offset2.
  simpl.
  
  ensure_normal_ret_assert;
  hoist_later_in_pre.

  eapply semax_data_load.
  - reflexivity.
  - unfold eq_rect_r.
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
      simpl.
      admit.
+ apply extract_exists_pre. intro_old_var (Sset _i (Efield (Efield (Evar _p t_struct_b) _y2 t_struct_a) _x2 tint)).
  abbreviate_semax.
  forward.

unfold_data_at 2%nat.
unfold_field_at 4%nat.

cancel.
Qed.

Lemma body_set:  semax_body Vprog Gprog f_set set_spec.
Proof.
 start_function.
name i_ _i.
apply (remember_value (eval_var _p t_struct_b)); intro p.

unfold_data_at 1%nat.
unfold_field_at 2%nat.

eapply semax_seq'.
+ rewrite nested_data_at_data_at at 1; [| reflexivity].

  unfold nested_field_lemmas.nested_field_type2, nested_field_lemmas.nested_field_offset2.
  simpl.
  
  
  ensure_normal_ret_assert;
  hoist_later_in_pre.
  
  eapply semax_data_store_nth; [| reflexivity | instantiate (2:= 1%nat); reflexivity | | | |].
  - unfold eq_rect_r. 
    instantiate (2:= eq_refl).
    rewrite <- eq_rect_eq.
    reflexivity.
  - simpl.
    instantiate (1:= Ews).
    admit.
  - auto.
  - simpl. normalize.
  - instantiate (1:= (Vint i)). simpl. go_lower. normalize.
    apply prop_right.
    rewrite <- H.
    reflexivity.
+ unfold replace_nth; cbv beta.
abbreviate_semax.
forward. (* return; *)

unfold_data_at 3%nat.
unfold_field_at 3%nat.

cancel.
Qed.

