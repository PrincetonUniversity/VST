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
simpl_data_at.
 fold t_struct_a.
forward. (* i = p.y2.x2; *)
forward. (* return i; *)
simpl_data_at.
cancel.
Qed.

Lemma body_set:  semax_body Vprog Gprog f_set set_spec.
Proof.
 start_function.
name i_ _i.
apply (remember_value (eval_var _p t_struct_b)); intro p.
simpl_data_at.  fold t_struct_a.
forward. (*   p.y2.x2 = i; *)
forward. (* return; *)
unfold at_offset, id; simpl.
forget (eval_var _p t_struct_b rho) as p.
simpl_data_at.
fold t_struct_a.
cancel.
Qed.
