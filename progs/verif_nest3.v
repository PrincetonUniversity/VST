Require Import floyd.proofauto.
Require Import progs.nest3.

Local Open Scope logic.

Definition get_spec :=
 DECLARE _get
  WITH v : reptype' t_struct_c
  PRE  [] 
         PROP () LOCAL()
        SEP(`(data_at Ews t_struct_c (repinj _ v)) (eval_var _p t_struct_c))
  POST [ tint ]
         PROP() (LOCAL (`(eq (Vint (snd (snd (snd v))))) (eval_id 1%positive))
         SEP (`(data_at Ews t_struct_c (repinj _ v)) (eval_var _p t_struct_c))).

Definition update222 (i: int) (v: reptype' t_struct_c) : reptype' t_struct_c :=
   (fst v, (fst (snd v), (fst (snd (snd v)), i))).

Definition set_spec :=
 DECLARE _set
  WITH i : int, v : reptype' t_struct_c
  PRE  [ _i OF tint ] 
         PROP () LOCAL(`(eq (Vint i)) (eval_id _i))
        SEP(`(data_at Ews t_struct_c (repinj _ v)) (eval_var _p t_struct_c))
  POST [ tvoid ]
        `(data_at Ews t_struct_c (repinj _ (update222 i v))) (eval_var _p t_struct_c).

Definition Vprog : varspecs := (_p, t_struct_c)::nil.

Definition Gprog : funspecs := 
    get_spec::set_spec::nil.

Lemma body_get:  semax_body Vprog Gprog f_get get_spec.
Proof.
 start_function.
name i _i.
forward.
forward.
cancel.
Qed.

Lemma body_get':  semax_body Vprog Gprog f_get get_spec.
Proof.
 start_function.
name i _i.
unfold_data_at 1%nat.
forward.
forward.
unfold_data_at 1%nat.
cancel.
Qed.

Lemma body_set:  semax_body Vprog Gprog f_set set_spec.
Proof.
start_function.
name i_ _i.
forward.
forward.
cancel.
Qed.
