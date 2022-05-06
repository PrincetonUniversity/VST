Require Import VST.floyd.proofauto.
Require Import VST.progs.cast_test.

#[export] Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Local Open Scope logic.

Definition test_spec :=
 DECLARE _test
  WITH n: Z
  PRE [ tlong ]
        PROP  (0 <= n < Int.max_signed)
        PARAMS (Vlong (Int64.repr n))
        SEP   ()
  POST [ tuchar ]
        PROP ()
        RETURN (Vint (Int.repr 0))
        SEP ().

Definition issue500_spec := 
  DECLARE _issue500
  WITH i: Int64.int
  PRE [ tlong ]
   PROP( Int64.signed i + 2147483648 <= Int64.max_signed) 
   PARAMS (Vlong i) 
   SEP()
  POST [ tlong ]
   PROP() RETURN (Vlong (Int64.add i (Int64.repr 2147483648))) SEP().

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := nil.

Lemma body_test:  semax_body Vprog Gprog f_test test_spec.
Proof.
start_function.
(* i64 n, b, c;  u8 d *)
forward.  (* b = n * 2; *)
forward.  (*  c = 2 * n; *)
forward.  (*  b = b + 4; *)
forward.  (*  b = (-4) + b; *)
forward.  (*  c = c - 4; *)
forward.  (*  c = 4 - c; *)
forward.  (*  b = b >> 8; *)
forward.  (*  c = c << 8; *)
forward.  (*  d = c & 0xff; *)
forward.  (*  d = d & b; *)
forward.  (* return d *)
entailer!. clear.
rewrite <- Int64.mul_pow2 with (n:= Int64.repr 256) by reflexivity.
rewrite mul64_repr, and64_repr.
rewrite (Z.land_ones _ 8) by computable.
rewrite Z_mod_mult.
reflexivity.
Qed.

Lemma body_issue500: semax_body Vprog Gprog f_issue500 issue500_spec.
Proof.
start_function.
forward.
Qed.

