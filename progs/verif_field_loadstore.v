Require Import floyd.proofauto.
Require Import progs.field_loadstore.

Local Open Scope logic.

Definition sub_spec (sub_id: ident) :=
 DECLARE sub_id
  WITH v : reptype' t_struct_b, p: val
  PRE  [] 
        PROP  (is_int I8 Signed (Vint (snd (snd v))))
        LOCAL (`(eq p) (eval_var _p t_struct_b))
        SEP   (`(data_at Ews t_struct_b (repinj _ v) p))
  POST [ tint ]
        `(data_at Ews t_struct_b (repinj t_struct_b (snd (snd v), snd v)) p).

Definition Vprog : varspecs := (_p, t_struct_b)::nil.

Definition Gprog : funspecs := 
  (sub_spec _sub1)::(sub_spec _sub2)::(sub_spec _sub3)::(sub_spec _sub4)::nil.

Lemma body_sub1:  semax_body Vprog Gprog f_sub1 (sub_spec _sub1).
Proof.
  unfold sub_spec.
  start_function.
  forward.
  forward.
  forward.
Qed.

Lemma body_sub2:  semax_body Vprog Gprog f_sub2 (sub_spec _sub2).
Proof.
  unfold sub_spec.
  start_function.
  forward.
  forward.
  forward.
Qed.

Lemma body_sub3:  semax_body Vprog Gprog f_sub3 (sub_spec _sub3).
Proof.
  unfold sub_spec.
  start_function.
  forward.
  forward.
  forward.
  forward.
Qed.

Lemma body_sub4:  semax_body Vprog Gprog f_sub4 (sub_spec _sub4).
Proof.
  unfold sub_spec.
  start_function.
  forward.
  forward.
  forward.
  forward.
  forward.
Qed.