Require Import floyd.proofauto.
Require Import progs.nest3.

Local Open Scope logic.

Definition get_spec :=
 DECLARE _get
  WITH v : reptype' t_struct_c, p: val
  PRE  [] 
        PROP  ()
        LOCAL (gvar _p p)
        SEP   (`(data_at Ews t_struct_c (repinj _ v) p))
  POST [ tint ]
        PROP  ()
        LOCAL (temp 1%positive (Vint (snd (snd (snd v)))))
        SEP   (`(data_at Ews t_struct_c (repinj _ v) p)).

Definition update222 (i: int) (v: reptype' t_struct_c) : reptype' t_struct_c :=
   (fst v, (fst (snd v), (fst (snd (snd v)), i))).

Definition set_spec :=
 DECLARE _set
  WITH i : int, v : reptype' t_struct_c, p : val
  PRE  [ _i OF tint ] 
        PROP ()
        LOCAL(temp _i (Vint i); gvar _p p)
        SEP(`(data_at Ews t_struct_c (repinj _ v) p))
  POST [ tvoid ]
        PROP() LOCAL()
        SEP(`(data_at Ews t_struct_c (repinj _ (update222 i v)) p)).

Definition Vprog : varspecs := (_p, t_struct_c)::nil.

Definition Gprog : funspecs := 
    get_spec::set_spec::nil.

Lemma body_get:  semax_body Vprog Gprog f_get get_spec.
Proof.
 start_function.
 forward.
 forward.
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
Qed.
