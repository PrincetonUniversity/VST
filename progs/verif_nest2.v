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
rewrite data_at_field_at.
forward.
simpl proj_reptype.
forward.
rewrite data_at_field_at.
apply derives_refl.
Qed.

Lemma body_set:  semax_body Vprog Gprog f_set set_spec.
Proof.
 start_function.
name i_ _i.
rewrite data_at_field_at.
forward.
forward.
rewrite data_at_field_at.
entailer!.
Qed.
