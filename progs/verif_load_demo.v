Require Import floyd.proofauto.
Require Import progs.load_demo.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition pair_pair_t := (Tstruct _pair_pair noattr).

Definition array_size := 100.

Definition get22_spec :=
 DECLARE _get22
  WITH pps: val, i: Z, x11: int, x12: int, x21: int, x22: int, sh : share
  PRE [ _pps OF (tptr pair_pair_t), _i OF tint ]
    PROP  (readable_share sh; 0 <= i < array_size)
    LOCAL (temp _pps pps; temp _i (Vint (Int.repr i)))
    SEP   (field_at sh (tarray pair_pair_t array_size) [ArraySubsc i]
                    ((Vint x11, Vint x12), (Vint x21, Vint x22)) pps)
  POST [ tint ]
        PROP () LOCAL (temp ret_temp (Vint x22))
    SEP   (field_at sh (tarray pair_pair_t array_size) [ArraySubsc i]
                    ((Vint x11, Vint x12), (Vint x21, Vint x22)) pps).

(* The spec of "int main(void){}" always looks like this. *)
Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ] main_post prog nil u.

Definition Gprog : funspecs := ltac:(with_library prog [get22_spec; main_spec]).

Lemma body_go: semax_body Vprog Gprog f_get22 get22_spec.
Proof.
start_function.
(* int_pair_t* p = &pps[i].right; *)
forward.

(* int res = p->snd; *)
(* Either make p nice enough so that no hint is required:
replace (offset_val 8 (force_val (sem_add_pi (Tstruct _pair_pair noattr) pps (Vint (Int.repr i)))))
  with (field_address (tarray pair_pair_t array_size) [StructField _right; ArraySubsc i] pps).
*)
(* Or assert_PROP what forward asks us for: *)
assert_PROP ((offset_val 8 (force_val (sem_add_pi (Tstruct _pair_pair noattr) pps (Vint (Int.repr i)))))
  = (field_address (tarray pair_pair_t array_size) [StructField _right; ArraySubsc i] pps)). {
  entailer!. rewrite field_compatible_field_address by auto with field_compatible. reflexivity.
}
forward.

(* return res; *)
forward.
Qed.
