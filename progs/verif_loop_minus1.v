Require Import VST.floyd.proofauto.
Require Import VST.progs.loop_minus1.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition sum_Z : list Z -> Z := fold_right Z.add 0.

Definition sumarray_spec :=
 DECLARE _sumarray
  WITH a: val, sh : share, contents : list Z, size: Z
  PRE [ _a OF (tptr tuint), _n OF tint ]
          PROP  (readable_share sh; 0 <= size <= Int.max_signed)
          LOCAL (temp _a a; temp _n (Vint (Int.repr size)))
          SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
  POST [ tuint ]
        PROP () LOCAL(temp ret_temp  (Vint (Int.repr (sum_Z contents))))
           SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).

Definition Gprog : funspecs := ltac:(with_library prog [sumarray_spec]).

Lemma sum_Z_app:
  forall a b, sum_Z (a++b) =  sum_Z a + sum_Z b.
Proof. intros. induction a; simpl; omega. Qed.

Lemma body_sumarray: semax_body Vprog Gprog f_sumarray sumarray_spec.
Proof.
  start_function.
  forward.
  forward_for_simple_bound
    (size - 1)
    (EX i: Z,
     PROP  ()
     LOCAL (temp _a a;
            temp _n (Vint (Int.repr size));
            temp _s (Vint (Int.repr (sum_Z (sublist 0 (i + 1) contents)))))
     SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)).
  - entailer!.
  - assert_PROP (Zlength contents = size) by
        (entailer!; do 2 rewrite Zlength_map; reflexivity).
    forward. forward. entailer!. f_equal. f_equal.
    rewrite (sublist_split 0 (i + 1) (i + 1 + 1)) by omega.
    rewrite sum_Z_app. rewrite (sublist_one (i + 1)) by omega.
    simpl. autorewrite with sublist. reflexivity.
  - forward. entailer!.  autorewrite with sublist in *. reflexivity.
Qed.
