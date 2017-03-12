Require Import floyd.proofauto.
Require Import progs.nest3.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

Definition t_struct_c := Tstruct _c noattr.

Definition get_spec0 :=
 DECLARE _get
  WITH v : reptype' t_struct_c, p: val
  PRE  []
        PROP  ()
        LOCAL (gvar _p p)
        SEP   (data_at Ews t_struct_c (repinj _ v) p)
  POST [ tint ]
        PROP  ()
        LOCAL (temp 1%positive (Vint (snd (snd (snd v)))))
        SEP   (data_at Ews t_struct_c (repinj _ v) p).

Definition get_spec : ident * funspec.
 let t := eval compute in (reptype' t_struct_c) in
 exact (DECLARE _get
  WITH v : t, p: val
  PRE  []
        PROP  ()
        LOCAL (gvar _p p)
        SEP   (data_at Ews t_struct_c (repinj t_struct_c v) p)
  POST [ tint ]
        PROP  ()
        LOCAL (temp 1%positive (Vint (snd (snd (snd v)))))
        SEP   (data_at Ews t_struct_c (repinj t_struct_c v) p)).
Defined.

Definition update222 (i: int) (v: reptype' t_struct_c) : reptype' t_struct_c :=
   (fst v, (fst (snd v), (fst (snd (snd v)), i))).

Definition set_spec :=
 DECLARE _set
  WITH i : int, v : reptype' t_struct_c, p : val
  PRE  [ _i OF tint ]
        PROP ()
        LOCAL(temp _i (Vint i); gvar _p p)
        SEP(data_at Ews t_struct_c (repinj _ v) p)
  POST [ tvoid ]
        PROP() LOCAL()
        SEP(data_at Ews t_struct_c (repinj _ (update222 i v)) p).

Definition Gprog : funspecs :=   ltac:(with_library prog [get_spec; set_spec]).

Lemma body_get:  semax_body Vprog Gprog f_get get_spec.
Proof.
Time start_function. (* 52 sec -> 1 sec*)
Time unfold_repinj. (* 0.386 sec *)
Time forward. (* 26.8 sec -> 6.4 sec -> 1.1 sec *)
Time forward. (* 15 sec. -> 19.5 sec -> 12.4 sec *)
Time Qed.  (* 84 sec  -> 4.5 sec -> 5.9 sec  *)

Lemma body_get':  semax_body Vprog Gprog f_get get_spec.
Proof.
 start_function.
 unfold_repinj.
 simpl in v.
 unfold data_at.
 unfold_field_at 1%nat.
 normalize. (* this line shouldn't be necessary, should be taken care of by unfold_field_at *)
Time forward. (* 18.88 sec -> 14.36 sec -> 0.9 sec *)
(*
Time forward. (* 13 sec -> 98 sec *)
unfold data_at.
 BUG! the next line takes forever
Time unfold_field_at 3%nat. (* 0.86 sec *)
rewrite prop_true_andp.
Time cancel. (* 1.875 sec *)
simplify_value_fits H3.
simplify_value_fits H5.
rewrite proj_sumbool_is_true by auto.
rewrite value_fits_eq; split; unfold list_rect;
 erewrite unfold_reptype_elim by reflexivity; assumption.
Qed. (* 77 sec *)
*)Admitted.

Lemma body_set:  semax_body Vprog Gprog f_set set_spec.
Proof.
Time start_function. (* 0.22 sec *)
(* Time unfold_repinj. (* 0.25 sec *)*)

Time forward.  (* 137 sec -> 15.8 sec *)
Time match goal with |- context [field_at _ _ _ ?X _] =>
  set (v1 := X) (* do this so the forward doesn't blow up *)
end. (* 8.3 sec *)
Time forward. (* 125 sec -> 33 sec *)
Time Qed. (* 2.74 sec *)
