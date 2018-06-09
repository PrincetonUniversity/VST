Require Import VST.floyd.proofauto.
Require Import VST.progs.nest2.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

Definition t_struct_b := Tstruct _b noattr.

Definition get_spec :=
 DECLARE _get
  WITH v : reptype' t_struct_b, gv: globals
  PRE  []
        PROP ()
        LOCAL(gvars gv)
        SEP(data_at Ews t_struct_b (repinj _ v) (gv _p))
  POST [ tint ]
         PROP()
         LOCAL (temp 1%positive (Vint (snd (snd v))))
         SEP (data_at Ews t_struct_b (repinj _ v) (gv _p)).

Definition get_spec' :=
 DECLARE _get
  WITH v : (int * (float * int))%type, gv: globals
  PRE  []
        PROP ()
        LOCAL(gvars gv)
        SEP(data_at Ews t_struct_b (repinj t_struct_b v) (gv _p))
  POST [ tint ]
         PROP()
         LOCAL (temp 1%positive (Vint (snd (snd v))))
         SEP (data_at Ews t_struct_b (repinj t_struct_b v) (gv _p)).

Definition update22 (i: int) (v: reptype' t_struct_b) : reptype' t_struct_b :=
   (fst v, (fst (snd v), i)).

Definition set_spec :=
 DECLARE _set
  WITH i : int, v : reptype' t_struct_b, gv: globals
  PRE  [ _i OF tint ]
         PROP  ()
         LOCAL (gvars gv;
                temp _i (Vint i))
         SEP   (data_at Ews t_struct_b (repinj _ v) (gv _p))
  POST [ tvoid ]
         PROP() LOCAL()
        SEP(data_at Ews t_struct_b (repinj _ (update22 i v)) (gv _p)).

Definition Gprog : funspecs :=   ltac:(with_library prog [get_spec; set_spec]).

Lemma body_get:  semax_body Vprog Gprog f_get get_spec.
Proof.
start_function.
simpl in v.
unfold_repinj.
Time forward. (* 5.989 sec  -> 2.6 -> 1.5 *)
Time forward. (* 11.1118 sec -> 7.5 *)
Time Qed.

Lemma body_get':  semax_body Vprog Gprog f_get get_spec'.
Proof.
start_function.
simpl in v.
unfold_repinj.
Time forward. (* 5.989 sec  -> 2.6*)
Time forward. (* 11.1118 sec -> 7.5 *)
Qed.

Lemma body_set:  semax_body Vprog Gprog f_set set_spec.
Proof.
 start_function.
simpl in v.
(*destruct v as [a [b c]]; simpl in *. *)
unfold_repinj.
Time forward. (* 1.23 sec *)
Time forward. (* 8.77  -> 5.25 sec *)
Time Qed.  (*  28 sec -> 3.45 sec *)

