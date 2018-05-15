Require Import List. Import ListNotations.
Require Import ZArith.
Local Open Scope Z_scope.
Require Import Integers.
Require Import VST.floyd.proofauto.
Require Import aes.sbox.
Require Import aes.GF_ops_LL.
Require Import aes.list_utils.

Definition rot8(i: int): int := 
  Int.or (Int.and (Int.shl i (Int.repr 8)) (Int.repr (-1))) (Int.shru i (Int.repr 24)).

Definition rotl1(b: int): int :=
  Int.and (Int.or (Int.shl b (Int.repr 1)) (Int.shr b (Int.repr 7))) (Int.repr 255).

Definition FSb := map Int.repr sbox.
Definition RSb := map Int.repr inv_sbox.

Definition calc_FT0(i: Z): int :=
  (Int.xor (Int.xor (Int.xor 
     (times2 (Znth i FSb)) 
     (Int.shl (Znth i FSb) (Int.repr 8)))
     (Int.shl (Znth i FSb) (Int.repr 16)))
     (Int.shl (Int.and (Int.xor (times2 (Znth i FSb)) (Znth i FSb))
                       (Int.repr 255))
              (Int.repr 24))).
Definition calc_FT1(i: Z): int := rot8 (calc_FT0 i).
Definition calc_FT2(i: Z): int := rot8 (calc_FT1 i).
Definition calc_FT3(i: Z): int := rot8 (calc_FT2 i).
Definition calc_RT0(i: Z): int :=
  Int.xor (Int.xor (Int.xor
           (mul (Int.repr 14) (Int.repr (Int.unsigned (Znth i RSb))))
  (Int.shl (mul (Int.repr  9) (Int.repr (Int.unsigned (Znth i RSb)))) (Int.repr  8)))
  (Int.shl (mul (Int.repr 13) (Int.repr (Int.unsigned (Znth i RSb)))) (Int.repr 16)))
  (Int.shl (mul (Int.repr 11) (Int.repr (Int.unsigned (Znth i RSb)))) (Int.repr 24)).
Definition calc_RT1(i: Z): int := rot8 (calc_RT0 i).
Definition calc_RT2(i: Z): int := rot8 (calc_RT1 i).
Definition calc_RT3(i: Z): int := rot8 (calc_RT2 i).

Global Opaque calc_FT0 calc_FT1 calc_FT2 calc_FT2 calc_RT0 calc_RT1 calc_RT2 calc_RT3.

Definition FT0 := fill_list 256 calc_FT0.
Definition FT1 := fill_list 256 calc_FT1.
Definition FT2 := fill_list 256 calc_FT2.
Definition FT3 := fill_list 256 calc_FT3.
Definition RT0 := fill_list 256 calc_RT0.
Definition RT1 := fill_list 256 calc_RT1.
Definition RT2 := fill_list 256 calc_RT2.
Definition RT3 := fill_list 256 calc_RT3.
Definition RCON := repeat_op_table 10 Int.one times2.

(* If entailer! and go_lower unfold these, they become too slow *)
Global Opaque FSb FT0 FT1 FT2 FT3 RSb RT0 RT1 RT2 RT3 RCON.

(* TODO Can we achieve the same with "Arguments"?
   "Arguments FSb : simpl never." (etc) does not seem to work *)

(* Instead of looking up the S-box values in a predefined list of constants, gen_tables actually
   calculates it using the following function (for i <> 0): *)
Definition calc_FSb_nonzero(i: Z): int :=
  let x := pow3 (255 - log3 (Int.repr i)) in
  (Int.xor (Int.xor (Int.xor (Int.xor        x 
                                      (rotl1 x))
                               (rotl1 (rotl1 x)))
                        (rotl1 (rotl1 (rotl1 x))))
        (Int.xor (rotl1 (rotl1 (rotl1 (rotl1 x)))) (Int.repr 99))).

(* the "repeat" and the "Qed." both take ~30s *)
Lemma FSb_equiv: forall i,
  1 <= i < 256 ->
  calc_FSb_nonzero i = Znth i FSb.
Proof.
  intros.
  repeat match goal with
  | H : ?b <= i < 256 |- _ =>
    assert (i = b \/ b + 1 <= i < 256) as C by omega;
    destruct C as [C | C];
    [ subst i; vm_compute; reflexivity
    | clear H; rename C into H; simpl in H ]
  end.
  omega.
Qed.
