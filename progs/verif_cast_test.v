Require Import VST.floyd.proofauto.
Require Import VST.progs.cast_test.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Local Open Scope logic.

Definition test_spec :=
 DECLARE _test
  WITH n: Z
  PRE [ _n OF tlong ]
        PROP  (0 <= n < Int.max_signed)
        LOCAL (temp _n (Vlong (Int64.repr n)))
        SEP   ()
  POST [ tuchar ]
        PROP ()
        LOCAL(temp ret_temp (Vint (Int.repr 0)))
        SEP ().

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := ltac:(with_library prog [test_spec]).

Lemma body_test:  semax_body Vprog Gprog f_test test_spec.
Proof.
start_function.
(* i64 n, b, c;  u8 d *)
forward.  (* b = n * 2; *)
forward.  (*  c = 2 * n; *)
entailer!.
rewrite Int64.signed_repr by rep_omega.
rep_omega.
forward.  (*  b = b + 4; *)
forward.  (*  b = (-4) + b; *)
entailer!.
rewrite Int64.signed_repr by rep_omega.
rep_omega.
forward.  (*  c = c - 4; *)
forward.  (*  c = 4 - c; *)
entailer!.
rewrite Int64.signed_repr by rep_omega.
rep_omega.
forward.  (*  b = b >> 8; *)
forward.  (*  c = c << 8; *)
forward.  (*  d = c & 0xff; *)
forward.  (*  d = d & b; *)
forward.  (* return d *)
entailer!. clear- H. f_equal.
rewrite Int.zero_ext_idem by computable.
replace  (- (4) + (n * 2 + 4))%Z with (n*2)%Z by omega.
replace (4 - (2*n-4)) with (8-(n*2)) by omega.
admit.  (* might be fine . . . *)
Admitted.


