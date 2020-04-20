Require Import Arith.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import List.
Require Import List. Import ListNotations.
Require Import sha.hmac_pure_lemmas.

Definition asZ (x : bool) : Z := if x then 1 else 0.

Lemma asZT: asZ true = 1. reflexivity. Qed.
Lemma asZF: asZ false = 0. reflexivity. Qed.

Definition convertByteBits bits (b : byte) : Prop :=
  exists (b0 b1 b2 b3 b4 b5 b6 b7 : bool),
   bits = [b0; b1; b2; b3; b4; b5; b6; b7] /\
   Byte.unsigned b =  (1 * (asZ b0) + 2 * (asZ b1) + 4 * (asZ b2) + 8 * (asZ b3)
         + 16 * (asZ b4) + 32 * (asZ b5) + 64 * (asZ b6) + 128 * (asZ b7)).

Lemma testbit_b2z_nonzero:
  forall i, i<>0 -> forall b, Z.testbit (Z.b2z b) i = false.
Proof.
intros.
unfold Z.testbit, Z.b2z.
destruct i; try contradiction; auto.
destruct b; simpl; auto.
Qed.

Lemma testbit_shiftl_8:
  forall a0 a1 a2 a3 a4 a5 a6 a7,
 forall i,
  Z.testbit (Z.shiftl (Z.b2z a0) 0 + Z.shiftl (Z.b2z a1) 1
             + Z.shiftl (Z.b2z a2) 2 + Z.shiftl (Z.b2z a3) 3
             + Z.shiftl (Z.b2z a4) 4 + Z.shiftl (Z.b2z a5) 5
             + Z.shiftl (Z.b2z a6) 6 + Z.shiftl (Z.b2z a7) 7)  i=
   Z.testbit (Z.shiftl (Z.b2z a0) 0) i ||
   Z.testbit (Z.shiftl (Z.b2z a1) 1) i ||
   Z.testbit (Z.shiftl (Z.b2z a2) 2) i ||
   Z.testbit (Z.shiftl (Z.b2z a3) 3) i ||
   Z.testbit (Z.shiftl (Z.b2z a4) 4) i ||
   Z.testbit (Z.shiftl (Z.b2z a5) 5) i ||
   Z.testbit (Z.shiftl (Z.b2z a6) 6) i ||
   Z.testbit (Z.shiftl (Z.b2z a7) 7) i.
Proof.
intros.
      destruct (zlt i 0).
       rewrite !Z.testbit_neg_r by auto. reflexivity.
       assert (0 <= i) by omega. clear g.
     rewrite ?Z.shiftl_spec by auto.
repeat rewrite <- Z.add_assoc.
rewrite !Z.shiftl_mul_pow2 by omega.
rewrite ?(Z.mul_comm (Z.b2z _)).
unfold Z.pow, Z.pow_pos, Pos.iter.
rewrite <- ?Z.mul_assoc.
rewrite <- ?Z.mul_add_distr_l.
rewrite ?Z.mul_1_l.
rewrite ?(Z.add_comm _ (2 * _)).
destruct (zlt i 1). {
assert (i=0) by omega; subst i; clear H l; simpl Z.sub.
rewrite ?Z.b2z_bit0.
rewrite !testbit_b2z_nonzero by omega; rewrite ?orb_false_r.
rewrite ?Z.add_bit0.
rewrite ?Z.b2z_bit0.
rewrite Z.testbit_even_0. rewrite xorb_false_l. reflexivity.
}
clear H.
do 7
match goal with H: i >= ?a |- _ =>
let i' := constr:(Z.succ a) in let i' := eval compute in i' in 
 let H' := fresh "H" in 
destruct (zlt i i'); 
  [assert (H': i=a) by omega;
      change a with (Recdef.iter _ (Z.to_nat a) Z.succ 0) in H';
      simpl Z.to_nat in H'; unfold Recdef.iter in H';
      subst i; clear H;
   rewrite Z.testbit_succ_r by omega;
   rewrite ?Z.b2z_bit0;
   rewrite !testbit_b2z_nonzero by omega; 
   rewrite ?orb_false_r, ?orb_false_l;
   rewrite ?Z.testbit_succ_r by omega;
   rewrite ?Z.add_bit0;
   rewrite ?Z.testbit_even_0;
   rewrite ?Z.b2z_bit0;
   rewrite ?orb_false_l;
   rewrite ?xorb_false_l;
   auto
    | clear H]
end.

rewrite !testbit_b2z_nonzero by omega; rewrite ?orb_false_r, ?orb_false_l.
do 7 match goal with |- Z.testbit _ ?a = false =>
  replace a with (Z.succ (Z.pred a)) by (clear; omega);
  rewrite Z.testbit_succ_r by omega
end.
rewrite testbit_b2z_nonzero by omega.
auto.
Qed.

Lemma xor_correspondence :
  forall (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : bool)
         (byte0 byte1 : byte),
    convertByteBits [b0; b1; b2; b3; b4; b5; b6; b7] byte0 ->
    convertByteBits [b8; b9; b10; b11; b12; b13; b14; b15] byte1 ->

    convertByteBits
      [xorb b0 b8; xorb b1 b9; xorb b2 b10; xorb b3 b11;
       xorb b4 b12; xorb b5 b13; xorb b6 b14; xorb b7 b15]
      (Byte.xor byte0 byte1).
Proof.
  intros.
  generalize dependent H. generalize dependent H0. intros H0 H1.
  unfold convertByteBits. unfold asZ.
  unfold Byte.xor.
  rewrite Byte.unsigned_repr.
*
  do 8 eexists. split. reflexivity.
  unfold convertByteBits in *.
  set (a0 := Byte.unsigned byte0) in *. clearbody a0.
  set (a1 := Byte.unsigned byte1) in *. clearbody a1.

  destruct H0 as [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ]] ]] ].  (* nested 8 *)
  destruct H.
  symmetry in H.
  inversion H. clear H.
  subst.

  destruct H1 as [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ]] ]] ].  (* nested 8 *)
  destruct H.
  symmetry in H.
  inversion H. clear H.
  subst.
      fold (asZ (xorb b2 b10)).
      fold (asZ (xorb b4 b12)).
      fold (asZ (xorb b6 b14)).
      fold (asZ (xorb b0 b8)).
      fold (asZ (xorb b1 b9)).
      fold (asZ (xorb b3 b11)).
      fold (asZ (xorb b5 b13)).
      fold (asZ (xorb b7 b15)).
      rewrite <- !(Z.mul_comm (asZ _)).
      rewrite <- !(Z.shiftl_mul_pow2 _ 0) by (clear; omega).
      rewrite <- !(Z.shiftl_mul_pow2 _ 1) by (clear; omega).
      rewrite <- !(Z.shiftl_mul_pow2 _ 2) by (clear; omega).
      rewrite <- !(Z.shiftl_mul_pow2 _ 3) by (clear; omega).
      rewrite <- !(Z.shiftl_mul_pow2 _ 4) by (clear; omega).
      rewrite <- !(Z.shiftl_mul_pow2 _ 5) by (clear; omega).
      rewrite <- !(Z.shiftl_mul_pow2 _ 6) by (clear; omega).
      rewrite <- !(Z.shiftl_mul_pow2 _ 7) by (clear; omega).
      apply Z.bits_inj.
      intro i.
      rewrite Z.lxor_spec.
      change asZ with Z.b2z.
      destruct (zlt i 0).
       rewrite !Z.testbit_neg_r by auto. reflexivity.
       assert (0 <= i) by omega. clear g.

       rewrite !testbit_shiftl_8.
       rewrite !Z.shiftl_spec by auto.
       destruct (zlt i 8).
       2:{  rewrite !testbit_b2z_nonzero by omega; reflexivity. }
       assert (i=0 \/ i=1 \/ i=2 \/ i=3 \/ i=4 \/ i=5 \/ i=6 \/ i=7) by omega.
       decompose [or] H0; subst i; clear;
       simpl Z.sub; rewrite ?orb_false_r;
       rewrite ?Z.b2z_bit0;
       rewrite ?testbit_b2z_nonzero by omega; simpl; auto.
*
      rewrite xor_inrange.
      all: change Byte.modulus with 256 in *.
      pose proof (Z_mod_lt (Z.lxor (Byte.unsigned byte0) (Byte.unsigned byte1)) 256).
      assert (256>0) by omega. specialize (H H2).
      change Byte.max_unsigned with 255. omega.
      all: symmetry; apply Z.mod_small; apply Byte.unsigned_range.
Qed.