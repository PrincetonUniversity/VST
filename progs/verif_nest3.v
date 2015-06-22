Require Import floyd.proofauto.
Require Import progs.nest3.
Instance CompSpecs : compspecs := compspecs_program prog.
Instance CS_legal : compspecs_legal CompSpecs.
Proof. prove_CS_legal. Qed.

Local Open Scope logic.

Definition t_struct_c := Tstruct _c noattr.

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
 unfold_repinj.
 simpl in v.
Time forward.  (* 39.77 sec *)
Time forward.
 unfold_repinj t_struct_c.
 cancel.
Qed.  (* 84 sec *)

Lemma body_get':  semax_body Vprog Gprog f_get get_spec.
Proof.
 start_function.
 unfold_repinj.
 simpl in v.
 unfold data_at. unfold_field_at 1%nat.
 normalize. (* this line shouldn't be necessary, should be taken care of by unfold_field_at *)
Time forward. (* 18.88 sec *)
Time forward. (* 13 sec *)
Time unfold_repinj. (* 20.4 sec *)
 unfold data_at.
Time unfold_field_at 3%nat. (* 0.86 sec *)
Time cancel. (* 1.875 sec *)
Qed. (* 77 sec *)

Lemma body_set:  semax_body Vprog Gprog f_set set_spec.
Proof.
start_function.
 unfold_repinj.
Time forward. (* 137 sec *)
Time forward. (* 95 sec *)
Time unfold_repinj. (* 25.5 sec *)
Time cancel. (* 4.16 sec *)
Qed.
