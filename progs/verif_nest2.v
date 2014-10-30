Require Import floyd.proofauto.
Require Import progs.nest2.

Local Open Scope logic.

Definition get_spec :=
 DECLARE _get
  WITH v : reptype' t_struct_b, p : val
  PRE  [] 
        PROP ()
        LOCAL(var _p t_struct_b p)
        SEP(`(data_at Ews t_struct_b (repinj _ v) p))
  POST [ tint ]
         PROP() 
         LOCAL (temp 1%positive (Vint (snd (snd v))))
         SEP (`(data_at Ews t_struct_b (repinj _ v) p)).

Definition update22 (i: int) (v: reptype' t_struct_b) : reptype' t_struct_b :=
   (fst v, (fst (snd v), i)).

Definition set_spec :=
 DECLARE _set
  WITH i : int, v : reptype' t_struct_b, p : val
  PRE  [ _i OF tint ] 
         PROP  ()
         LOCAL (var _p t_struct_b p; 
                temp _i (Vint i))
         SEP   (`(data_at Ews t_struct_b (repinj _ v) p))
  POST [ tvoid ]
        `(data_at Ews t_struct_b (repinj _ (update22 i v)) p).

Definition Vprog : varspecs := (_p, t_struct_b)::nil.

Definition Gprog : funspecs := 
    get_spec::set_spec::nil.

Lemma body_get:  semax_body Vprog Gprog f_get get_spec.
Proof.
start_function.
name i _i.
forward.
forward.
Qed.

Lemma body_set:  semax_body Vprog Gprog f_set set_spec.
Proof.
 start_function.
name i_ _i.
forward.
forward.
Qed.
