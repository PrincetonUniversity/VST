Require Import VST.floyd.proofauto.
Require Import VST.progs.store_demo.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition pair_pair_t := (Tstruct _pair_pair noattr).

Definition array_size := 100.

Definition set22_spec :=
 DECLARE _set22
  WITH pps: val, i: Z, v: int, x11: int, x12: int, x21: int, x22: int, sh : share
  PRE [ _pps OF (tptr pair_pair_t), _i OF tint, _v OF tint]
    PROP  (writable_share sh; 0 <= i < array_size)
    LOCAL (temp _pps pps; temp _i (Vint (Int.repr i)); temp _v (Vint v))
    SEP   (field_at sh (tarray pair_pair_t array_size) [ArraySubsc i] 
                    ((Vint x11, Vint x12), (Vint x21, Vint x22)) pps)
  POST [ tvoid ]
    PROP () LOCAL ()
    SEP   (field_at sh (tarray pair_pair_t array_size) [ArraySubsc i]
                    ((Vint x11, Vint x12), (Vint x21, Vint v)) pps).

Definition fiddle_spec :=
 DECLARE _fiddle
  WITH p: val, n: Z, tag: Z, contents: list Z
  PRE [ _p OF tptr tuint ]
          PROP  (Zlength contents = n)
          LOCAL (temp _p p)
          SEP (data_at Ews (tarray tuint (1+n)) 
                      (map Vint (map Int.repr (tag::contents)))
                      (offset_val (-sizeof tuint) p))
  POST [ tvoid ]
          PROP () LOCAL ()
          SEP (data_at Ews (tarray tuint (1+n)) 
                      (map Vint (map Int.repr (3::contents)))
                      (offset_val (-sizeof tuint) p)).

Definition Gprog : funspecs := ltac:(with_library prog [set22_spec; fiddle_spec]).

Lemma body_fiddle: semax_body Vprog Gprog f_fiddle fiddle_spec.
Proof.
start_function.
rename H into LEN.
assert (Zlength (tag :: contents) = 1 + n) as LEN1. {
  rewrite Zlength_cons. omega.
}
assert (N0: 0 <= n). {
  pose proof (Zlength_nonneg contents). omega.
}
assert_PROP (isptr p) as P by entailer!.
(* forward fails, but tells us to prove this: *)
assert_PROP (force_val (sem_add_ptr_int tuint Signed p (eval_unop Oneg tint (Vint (Int.repr 1)))) 
  = field_address (tarray tuint (1+n)) [ArraySubsc 0] (offset_val (-sizeof tuint) p)). {
  entailer!.
  destruct p; inversion P. simpl.
  rewrite field_compatible_field_address by auto with field_compatible.
  simpl.
  rewrite ptrofs_add_repr_0_r. reflexivity.
}

(* Now "forward" succeeds, but leaves a goal open to be proved manually: *)
forward.
(*
{ entailer!.
  change (eval_unop Oneg tint (Vint (Int.repr 1))) with (Vint (Int.neg (Int.repr 1))) in H.
  rewrite H0.
  apply isptr_field_address_lemma.
  auto with field_compatible.
}
*)
forward.
rewrite upd_Znth0. rewrite sublist_1_cons. rewrite Zlength_cons.
rewrite ?Zlength_map. replace (Z.succ (Zlength contents) - 1) with (Zlength contents) by omega.
rewrite sublist_same by (rewrite ?Zlength_map; reflexivity).
apply derives_refl.
Qed.

Lemma body_set22_root_expr: semax_body Vprog Gprog f_set22 set22_spec.
Proof.
start_function.
(* pps[i].right.snd = 0; // simple: the whole path is exposed in the syntax *)
forward.
(* int_pair_t* p = &pps[i].right; *)
forward.
simpl (temp _p _).
(* Assert_PROP what forward asks us for (only for the root expression "p"):  *)
assert_PROP (offset_val 8 (force_val (sem_add_ptr_int (Tstruct _pair_pair noattr) Signed pps (Vint (Int.repr i))))
  = field_address (tarray pair_pair_t array_size) [StructField _right; ArraySubsc i] pps) as E. {
  entailer!. rewrite field_compatible_field_address by auto with field_compatible.
  simpl.
  normalize.
}
(* p->snd = v; *)
forward.
forward.
Qed.

Lemma body_set22_full_expr: semax_body Vprog Gprog f_set22 set22_spec.
Proof.
start_function.
(* pps[i].right.snd = 0; // simple: the whole path is exposed in the syntax *)
forward.
(* int_pair_t* p = &pps[i].right; *)
forward.
simpl (temp _p _).

(* Assert_PROP what forward asks us for (for the full expression "p->snd"): *)
assert_PROP (
  offset_val 4 (offset_val 8 (force_val
    (sem_add_ptr_int (Tstruct _pair_pair noattr) Signed pps (Vint (Int.repr i)))))
  = (field_address (tarray pair_pair_t array_size)
                   [StructField _snd; StructField _right; ArraySubsc i] pps)). {
  entailer!. rewrite field_compatible_field_address by auto with field_compatible.
  simpl. normalize.  f_equal. omega.
}
(* int res = p->snd; *)
forward.
(* return res; *)
forward.
Qed.

Lemma body_set22_alt: semax_body Vprog Gprog f_set22 set22_spec.
Proof.
start_function.
(* pps[i].right.snd = 0; // simple: the whole path is exposed in the syntax *)
forward.
(* int_pair_t* p = &pps[i].right; *)
forward.
simpl (temp _p _).

(* Alternative: Make p nice enough so that no hint is required: *)
assert_PROP (offset_val 8 (force_val (sem_add_ptr_int (Tstruct _pair_pair noattr) Signed pps (Vint (Int.repr i))))
  = field_address (tarray pair_pair_t array_size) [StructField _right; ArraySubsc i] pps) as E. {
  entailer!. rewrite field_compatible_field_address by auto with field_compatible.
  normalize.
}
rewrite E. clear E.
(* int res = p->snd; *)
forward.
(* return res; *)
forward.
Qed.
