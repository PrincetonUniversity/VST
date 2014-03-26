Require Import msl.eq_dec.

Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.Memory.

Definition address : Type := (block * Z)%type.

Instance EqDec_block: EqDec block := eq_block.

Instance EqDec_address: EqDec address.
Proof.
 intros [b1 z1] [b2 z2].
 destruct (eq_dec b1 b2).
 destruct (Z.eq_dec z1 z2).
 left; congruence.
 right; congruence.
 right; congruence.
Qed.

Instance EqDec_int: EqDec int := Int.eq_dec.
Instance EqDec_float: EqDec float := Float.eq_dec.

Instance EqDec_val: EqDec val.
Proof.
 hnf. decide equality.
 apply Int.eq_dec.
 apply Int64.eq_dec.
 apply Float.eq_dec.
 apply Int.eq_dec.
 apply eq_block.
Qed.

Definition adr_range (base: address) (size: Z) (loc: address) : Prop :=
 match base, loc with
 | (b, ofs) , (b', ofs') => b=b' /\ (ofs <= ofs' < ofs + size)
 end.

Lemma adr_range_dec: forall base n loc, {adr_range base n loc} + {~adr_range base n loc}.
Proof.
unfold adr_range; intros.
destruct base as [b z]; destruct loc as [b' z'].
destruct (eq_block b b').
subst b'.
destruct (zle z z').
destruct (zlt z' (z+n)).
left; auto.
right; intros [? ?]; omega.
right; intros [? ?]; omega.
right; intros [? ?]; unfold block in *; xomega.
Qed.

(*
Definition size_chunk (chunk: memory_chunk) : Z :=
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mfloat32 => 4
  | Mfloat64 => 8
  | Mfloat64al32 => 4
  end.
*)

Remark size_chunk_pos:
  forall chunk1, size_chunk chunk1 > 0.
Proof.
  destruct chunk1; simpl; omega.
Qed.

Lemma zero_in_chunk: forall ch, 0 <= 0 < size_chunk ch.
Proof.
  intros; generalize (size_chunk_pos ch); omega.
Qed.

Hint Resolve zero_in_chunk : mem.

Definition range_overlap (base1: address) (sz1: Z) (base2: address) (sz2: Z) : Prop :=
  exists loc, adr_range base1 sz1 loc /\ adr_range base2 sz2 loc.

Definition adr_add (loc: address) (ofs: Z) : address := (fst loc, snd loc + ofs).

Definition val2adr (v: val) (l: address) : Prop := 
     match v with Vptr b ofs => l = (b, Int.signed ofs) | _ => False end.
