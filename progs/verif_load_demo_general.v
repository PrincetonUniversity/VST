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

Ltac solve_legal_nested_field_in_entailment' :=
(* same as solve_legal_nested_field_in_entailment but with the first match behind a try: *)
   try match goal with
   | |- _ |-- !! legal_nested_field ?t_root (?gfs1 ++ ?gfs0) =>
    unfold t_root, gfs0, gfs1
  end;
  first
  [ apply prop_right; apply compute_legal_nested_field_spec';
    match goal with
  | |- Forall ?F _ =>
      let F0 := fresh "F" in
      remember F as F0;
      simpl;
      subst F0
  end;
  repeat constructor; omega
  |
  apply compute_legal_nested_field_spec;
  match goal with
  | |- Forall ?F _ =>
      let F0 := fresh "F" in
      remember F as F0;
      simpl;
      subst F0
  end;
  repeat constructor;
  try solve [apply prop_right; auto; omega];
  try solve [normalize; apply prop_right; auto; omega]
  ].

Require Import floyd.new_load_tac_general.

Lemma body_go: semax_body Vprog Gprog f_get22 get22_spec.
Proof.
start_function.
(* int_pair_t* p = &pps[i].right; *)
forward.

rename sh into sh77.
(* int res = p->snd; *)
(* Either make p nice enough so that no hint is required:
replace (offset_val 8 (force_val (sem_add_pi (Tstruct _pair_pair noattr) pps (Vint (Int.repr i)))))
  with (field_address (tarray pair_pair_t array_size) [StructField _right; ArraySubsc i] pps). {
*)
(* Or assert_PROP what forward asks us for: *)
assert_PROP ((offset_val 8 (force_val (sem_add_pi (Tstruct _pair_pair noattr) pps (Vint (Int.repr i)))))
  = (field_address (tarray pair_pair_t array_size) [StructField _right; ArraySubsc i] pps))
by admit.

forward.

forward.
Qed.
