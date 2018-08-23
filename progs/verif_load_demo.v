Require Import VST.floyd.proofauto.
Require Import VST.progs.load_demo.

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

Definition uint_sum (contents : list Z) : int :=
  fold_right (fun el sum => Int.add sum (Int.repr el)) Int.zero contents.

Definition fiddle_spec :=
 DECLARE _fiddle
  WITH p: val, n: Z, tag: Z, contents: list Z
  PRE [ _p OF tptr tuint ]
          PROP  (Int.unsigned (Int.shru (Int.repr tag) (Int.repr 10)) = n)
          LOCAL (temp _p p)
          SEP (data_at Ews (tarray tuint (1+n)) 
                      (map Vint (map Int.repr (tag::contents)))
                      (offset_val (-sizeof tuint) p))
  POST [ tint ]
          PROP ( )
          LOCAL (temp ret_temp (Vint (Int.add (Int.repr (Z.land tag 255)) (uint_sum contents))))
          SEP (data_at Ews (tarray tuint (1+n)) 
                      (map Vint (map Int.repr (tag::contents)))
                      (offset_val (-sizeof tuint) p)).

Definition get_uint32_le (arr: list Z) : int :=
 (Int.or (Int.or (Int.or
            (Int.repr (Znth 0 arr))
   (Int.shl (Int.repr (Znth 1 arr)) (Int.repr  8)))
   (Int.shl (Int.repr (Znth 2 arr)) (Int.repr 16)))
   (Int.shl (Int.repr (Znth 3 arr)) (Int.repr 24))).

Definition get_little_endian_spec :=
  DECLARE _get_little_endian
  WITH input : val, in_sh : share, arr : list Z
  PRE [ _input OF (tptr tuchar) ]
    PROP (Zlength arr = 4;
          readable_share in_sh;
          forall i, 0 <= i < 4 -> 0 <= Znth i arr <= Byte.max_unsigned)
    LOCAL (temp _input input)
    SEP (data_at in_sh (tarray tuchar 4) (map Vint (map Int.repr arr)) input)
  POST [ tuint ]
    PROP() LOCAL(temp ret_temp (Vint (get_uint32_le arr)))
    SEP (data_at in_sh (tarray tuchar 4) (map Vint (map Int.repr arr)) input).

Definition Gprog : funspecs := ltac:(with_library prog
  [get22_spec; fiddle_spec; get_little_endian_spec]).


Ltac solve_arr_range H := 
 match goal with |- context [Znth ?i _] => 
   specialize (H i); spec H; [ computable | ];
   rewrite Int.unsigned_repr; rep_omega
 end.

Lemma body_get_little_endian: semax_body Vprog Gprog f_get_little_endian get_little_endian_spec.
Proof.
start_function.
assert (BMU: Byte.max_unsigned=255) by reflexivity.
forward.
entailer!. solve_arr_range H0.
forward.
forward.
entailer!. solve_arr_range H0.
forward.
forward.
entailer!. solve_arr_range H0.
forward.
entailer!. solve_arr_range H0.
forward.
Qed.

Lemma uint_sum_app: forall a b, uint_sum (a++b) = Int.add (uint_sum a) (uint_sum b).
Proof.
  intros. induction a; simpl.
  - symmetry. apply Int.add_zero_l.
  - rewrite IHa. rewrite !Int.add_assoc. f_equal. apply Int.add_commut.
Qed.

Lemma body_fiddle: semax_body Vprog Gprog f_fiddle fiddle_spec.
Proof.
start_function.
rename H into Htag.
assert_PROP (Zlength contents = n) as LEN. {
  entailer!.
  forget (Int.unsigned (Int.shru (Int.repr tag) (Int.repr 10))) as n.
  clear - H0.
  rewrite Zlength_cons in H0.
  rewrite !Zlength_map in H0.
  destruct (zlt n 0); [elimtype False | ].
  rewrite Z.max_l in H0 by omega.
  pose proof (Zlength_nonneg contents).
  omega.
  rewrite Z.max_r in H0 by omega. omega.  
}
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
forward.
(* sum = tagword & 0xff; *)
forward.
(* size = tagword >> 10; *)
forward.
(* rewrite !Znth_0_cons. *)
forward_for_simple_bound (Int.unsigned (Int.shru (Int.repr tag) (Int.repr 10))) (EX i: Z,
  PROP ( )
  LOCAL (
    temp _size (Vint (Int.shru (Int.repr tag) (Int.repr 10)));
    temp _sum (Vint (Int.add (Int.and (Int.repr tag) (Int.repr 255))
                             (uint_sum (sublist 0 i contents))));
    temp _tagword (Vint (Int.repr tag));
    temp _p p
  )
  SEP (data_at Ews (tarray tuint (1 + n)) (map Vint (map Int.repr (tag :: contents)))
          (offset_val (- sizeof tuint) p))).
- (* precondition implies invariant: *)
  entailer!.
- (* body preserves invariant: *)
  (* forward fails, but tells us to prove this: *)
  assert_PROP (force_val (sem_add_ptr_int tuint Unsigned p (Vint (Int.repr i)))
    = field_address (tarray tuint (1 + n)) [ArraySubsc (1 + i)] (offset_val (- sizeof tuint) p)). {
    entailer!.
    destruct p; inversion P. simpl.
    rewrite field_compatible_field_address by auto with field_compatible.
    simpl.
    rewrite Ptrofs.add_assoc, ptrofs_add_repr. 
    f_equal. f_equal. f_equal. omega.
  }
  forward.
  forward.
  entailer!.
  rewrite Znth_pos_cons by omega.
  autorewrite with sublist. simpl.  
  f_equal. rewrite Int.add_assoc. f_equal.
  rewrite (sublist_split 0 i (i+1)) by omega.
  rewrite sublist_len_1 by omega.
  replace (1 + i - 1) with i by omega.
  rewrite uint_sum_app. f_equal. simpl. apply Int.add_zero_l.
- (* return sum; *)
  forward. rewrite sublist_same by auto. entailer!.
Qed.

Lemma body_get22_root_expr: semax_body Vprog Gprog f_get22 get22_spec.
 Proof.
 start_function.
 (* int_pair_t* p = &pps[i].right; *)
 forward.
 simpl (temp _p _).
 (* Assert_PROP what forward asks us for (only for the root expression "p"):  *)
 assert_PROP (offset_val 8 (force_val (sem_add_ptr_int (Tstruct _pair_pair noattr) Signed pps (Vint (Int.repr i))))
   = field_address (tarray pair_pair_t array_size) [StructField _right; ArraySubsc i] pps) as E. {
   entailer!. rewrite field_compatible_field_address by auto with field_compatible.
  simpl. normalize.
 }
 (* int res = p->snd; *)
 forward.
 (* return res; *)
 forward.
 Qed.
 

Lemma body_get22_full_expr: semax_body Vprog Gprog f_get22 get22_spec.
Proof.
start_function.
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
  simpl. f_equal. omega.
}
(* int res = p->snd; *)
forward.
(* return res; *)
forward.
Qed.

Lemma body_get22_alt: semax_body Vprog Gprog f_get22 get22_spec.
Proof.
start_function.
(* int_pair_t* p = &pps[i].right; *)
forward.
simpl (temp _p _).

(* Alternative: Make p nice enough so that no hint is required: *)
assert_PROP (offset_val 8 (force_val (sem_add_ptr_int (Tstruct _pair_pair noattr) Signed pps (Vint (Int.repr i))))
  = field_address (tarray pair_pair_t array_size) [StructField _right; ArraySubsc i] pps) as E. {
  entailer!. rewrite field_compatible_field_address by auto with field_compatible.
  simpl.
  normalize.
}
rewrite E. clear E.
(* int res = p->snd; *)
forward.
(* return res; *)
forward.
Qed.
