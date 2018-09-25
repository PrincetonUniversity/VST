(* THIS FILE CONTAINS
   Lemmas that DO NOT depend on CompCert or Verifiable C,
   and that are used in the proof of the C program but are not
   used in the proof of functional_prog.v.
*)

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import List. Import ListNotations.
Require Import sha.general_lemmas.
Require Import sha.SHA256.
Require Import VST.msl.Coqlib2.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.sublist.
Require Export sha.common_lemmas.
Require Psatz.

Global Opaque CBLOCKz LBLOCKz.

Lemma Zlength_intlist_to_bytelist:
  forall l : list int,
       Zlength (intlist_to_bytelist l) = (Zlength l * 4)%Z.
Proof.
intros.
repeat rewrite Zlength_correct. rewrite length_intlist_to_bytelist.
rewrite Nat2Z.inj_mul. rewrite Z.mul_comm. reflexivity.
Qed.

Hint Rewrite Zlength_intlist_to_bytelist : sublist.

Lemma skipn_intlist_to_bytelist:
  forall i m, skipn (4*i) (intlist_to_bytelist m) = intlist_to_bytelist (skipn i m).
Proof.
induction i; intros.
reflexivity.
replace (4 * S i)%nat with (4 + 4 * i)%nat by omega.
destruct m; try reflexivity.
apply IHi.
Qed.

Lemma firstn_intlist_to_bytelist:
  forall i m, firstn (4*i) (intlist_to_bytelist m) = intlist_to_bytelist (firstn i m).
Proof.
induction i; intros.
reflexivity.
replace (4 * S i)%nat with (4 + 4 * i)%nat by omega.
destruct m; try reflexivity.
simpl. f_equal. f_equal. f_equal. f_equal.
apply IHi.
Qed.

Lemma sublist_intlist_to_bytelist:
 forall i j m,
  sublist (i * WORD) (j * WORD) (intlist_to_bytelist m) =
  intlist_to_bytelist (sublist i j m).
Proof.
intros.
unfold sublist.
change WORD with 4.
rewrite <- Z.mul_sub_distr_r.
destruct (zlt (j-i) 0).
rewrite (Z2Nat_neg _ l).
rewrite (Z2Nat_neg ((j-i)*4)) by omega.
reflexivity.
rewrite ?(Z.mul_comm _ 4).
rewrite ?Z2Nat.inj_mul by omega.
change (Z.to_nat 4) with 4%nat.
rewrite <- firstn_intlist_to_bytelist.
f_equal.
destruct (zlt i 0).
rewrite (Z2Nat_neg _ l).
rewrite (Z2Nat_neg (4*i)) by omega.
reflexivity.
rewrite ?Z2Nat.inj_mul by omega.
change (Z.to_nat 4) with 4%nat.
apply skipn_intlist_to_bytelist.
Qed.

Lemma bytelist_to_intlist_to_bytelist':
  forall nl: list byte,
  Nat.divide (Z.to_nat WORD) (length nl) ->
  intlist_to_bytelist (bytelist_to_intlist nl) = nl.
Proof.
intros nl [k H].
revert nl H; induction k; intros.
destruct nl; inv H; reflexivity.
simpl in H.
destruct nl as [ | a [ | b [ | c [ | d ?]]]]; inv H.
unfold bytelist_to_intlist; fold bytelist_to_intlist.
rewrite intlist_to_bytelist_bytes_to_int_cons by auto.
repeat f_equal; auto.
Qed.

Lemma Ndivide_Zdivide_length:
  forall {A} n (al: list A),
   0 <= n ->
   (Nat.divide (Z.to_nat n) (length al) <->
    (n | Zlength al)).
Proof.
intros; split; intros [i ?].
exists (Z.of_nat i). rewrite Zlength_correct, H0.
rewrite Nat2Z.inj_mul.
rewrite Z2Nat.id; auto.
exists (Z.to_nat i).
rewrite Zlength_correct in H0.
destruct (zeq n 0). subst.
simpl. rewrite Z.mul_0_r in H0. destruct al; inv H0.
rewrite mult_0_r. reflexivity.
assert (0 <= i).
assert (0 <= i * n) by omega.
apply Z.mul_nonneg_cancel_r in H1; auto; omega.
rewrite <- (Z2Nat.id (i*n)%Z) in H0 by omega.
apply Nat2Z.inj in H0. rewrite H0.
rewrite Z2Nat.inj_mul; auto.
Qed.

Lemma bytelist_to_intlist_to_bytelist:
  forall nl: list byte,
  Z.divide WORD (Zlength nl) ->
  intlist_to_bytelist (bytelist_to_intlist nl) = nl.
Proof.
intros.
apply bytelist_to_intlist_to_bytelist'; auto.
apply Ndivide_Zdivide_length; auto.
compute; congruence.
Qed.

Lemma length_bytelist_to_intlist: forall n l,
       length l = (Z.to_nat WORD * n)%nat ->
       length (bytelist_to_intlist l) = n.
Proof.
induction n; intros.
destruct l; inv H; reflexivity.
replace (S n) with (1 + n)%nat in H by omega.
rewrite mult_plus_distr_l in H.
destruct l as [|i0 l]; [ inv H |].
destruct l as [|i1 l]; [ inv H |].
destruct l as [|i2 l]; [ inv H |].
destruct l as [|i3 l]; [ inv H |].
simpl. f_equal. apply IHn. forget (Z.to_nat WORD * n)%nat as A. inv H; auto.
Qed.

Lemma big_endian_integer4:
 forall c0 c1 c2 c3,
  big_endian_integer (c0::c1::c2::c3::nil) =
  Int.or (Int.shl (Int.repr (Byte.unsigned c0)) (Int.repr 24)) 
     (Int.or (Int.shl (Int.repr (Byte.unsigned c1)) (Int.repr 16))
   (Int.or (Int.shl (Int.repr (Byte.unsigned c2)) (Int.repr 8)) 
          (Int.repr (Byte.unsigned c3)))).
Proof.
intros.
unfold big_endian_integer.
simpl.
apply Int.same_bits_eq; intros.
assert (Int.zwordsize=32) by reflexivity.
assert (32 < Int.max_unsigned) by (compute; auto).
autorewrite with testbit.
if_tac; simpl; auto;  try omega.
if_tac; simpl; auto; try omega.
if_tac; simpl; auto; try omega.
if_tac; simpl; auto; try omega.
if_tac; simpl; auto; try omega.
autorewrite with testbit; auto.
autorewrite with testbit; auto.
replace (i - 8 - 8) with (i-16) by omega.
rewrite orb_assoc. auto.
if_tac; simpl; auto; try omega.
autorewrite with testbit; auto.
replace (i - 8 - 8) with (i-16) by omega.
replace (i - 16 - 8) with (i-24) by omega.
repeat rewrite orb_assoc. auto.
Qed.

Local Open Scope nat.

Definition LBLOCK : nat := Z.to_nat LBLOCKz.
Definition CBLOCK : nat := Z.to_nat CBLOCKz.
Opaque LBLOCK CBLOCK.

Lemma LBLOCK_zeq: Z.of_nat LBLOCK = 16%Z.
Proof. reflexivity. Qed.

Lemma CBLOCK_zeq: (Z.of_nat CBLOCK = 64%Z).
Proof. reflexivity. Qed.

Lemma LBLOCKz_nonneg: (0 <= LBLOCKz)%Z.
Proof. change LBLOCKz with 16%Z; omega. Qed.
Hint Resolve LBLOCKz_nonneg.

Lemma LBLOCKz_pos: (0 < LBLOCKz)%Z.
Proof. change LBLOCKz with 16%Z; omega. Qed.
Hint Resolve LBLOCKz_pos.

Lemma CBLOCKz_nonneg: (0 <= CBLOCKz)%Z.
Proof. change CBLOCKz with 64%Z; omega. Qed.
Hint Resolve CBLOCKz_nonneg.

Lemma CBLOCKz_pos: (0 < CBLOCKz)%Z.
Proof. change CBLOCKz with 64%Z; omega. Qed.
Hint Resolve CBLOCKz_pos.


Local Open Scope Z.

Lemma divide_hashed:
 forall (bb: list int),
    Nat.divide LBLOCK (length bb) <->
    (LBLOCKz | Zlength bb).
Proof.
intros.
change LBLOCK with (Z.to_nat LBLOCKz).
apply Ndivide_Zdivide_length.
auto.
Qed.

Lemma hash_blocks_equation' : forall (r : registers) (msg : list int),
       hash_blocks r msg =
       match msg with
       | [] => r
       | _ :: _ => hash_blocks (hash_block r (firstn LBLOCK msg)) (skipn LBLOCK msg)
       end.
Proof. exact hash_blocks_equation. Qed.

Lemma CBLOCK_eq: CBLOCK=64%nat.
Proof. reflexivity. Qed.
Lemma LBLOCK_eq: LBLOCK=16%nat.
Proof. reflexivity. Qed.

Lemma hash_blocks_last:
 forall a bl c,
              Zlength a = 8 ->
              (LBLOCKz | Zlength bl) ->
              Zlength c = LBLOCKz ->
   hash_block (hash_blocks a bl) c = hash_blocks a (bl++ c).
Proof.
intros.
assert (POS: (0 < LBLOCK)%nat) by (rewrite LBLOCK_eq; omega).
apply divide_hashed in H0.
destruct H0 as [n ?].
rewrite Zlength_correct in H,H1.
change 8 with (Z.of_nat 8) in H.
change LBLOCKz with (Z.of_nat LBLOCK) in H1.
apply Nat2Z.inj in H.
apply Nat2Z.inj in H1.
revert a bl H H0; induction n; intros.
destruct bl; inv H0.
rewrite hash_blocks_equation'.
simpl. rewrite hash_blocks_equation'.
destruct c eqn:?. inv H1.
rewrite <- Heql in *; clear i l Heql.
rewrite firstn_same by omega.
replace (skipn LBLOCK c) with (@nil int).
rewrite hash_blocks_equation'; reflexivity.
pose proof (skipn_length c LBLOCK).
rewrite H1 in H0.
destruct (skipn LBLOCK c); try reflexivity; inv H0.
replace (S n * LBLOCK)%nat with (n * LBLOCK + LBLOCK)%nat  in H0 by
  (simpl; omega).
rewrite hash_blocks_equation'.
destruct bl.
simpl in H0.
Psatz.lia.
forget (i::bl) as bl'; clear i bl. rename bl' into bl.
rewrite IHn.
symmetry.
rewrite hash_blocks_equation.
destruct bl.
simpl in H0; Psatz.lia.
unfold app at 1; fold app.
forget (i::bl) as bl'; clear i bl. rename bl' into bl.
f_equal.
f_equal.
apply firstn_app1.
Psatz.nia.
apply skipn_app1.
Psatz.nia.
apply length_hash_block; auto. (* fixme *) change 16%nat with LBLOCK.
rewrite firstn_length. apply min_l.
Psatz.nia.
rewrite skipn_length.
apply plus_reg_l with LBLOCK.
rewrite plus_comm.
rewrite Nat.sub_add by Psatz.lia.
omega.
Qed.

Lemma length_hash_blocks: forall regs blocks,
  length regs = 8%nat ->
  (LBLOCKz | Zlength blocks) ->
  length (hash_blocks regs blocks) = 8%nat.
Proof.
intros.
destruct H0 as [n ?].
rewrite Zlength_correct in H0.
assert (POS := LBLOCKz_pos).
change LBLOCKz with (Z.of_nat LBLOCK) in *.
rewrite <- (Z2Nat.id n) in H0
 by (apply -> Z.mul_nonneg_cancel_r ; [ | apply POS]; omega).
rewrite <- Nat2Z.inj_mul in H0.
apply Nat2Z.inj in H0.
revert regs blocks H H0; induction (Z.to_nat n); intros.
  destruct blocks; inv H0.
rewrite hash_blocks_equation'; auto.
destruct blocks.
destruct LBLOCK; inv POS; inv H0.
rewrite hash_blocks_equation'; auto.
forget (i::blocks) as bb.
apply IHn0; auto.
apply length_hash_block; auto. (* fixme *) change 16%nat with LBLOCK.
rewrite firstn_length. apply min_l. simpl in H0. Psatz.nia.
rewrite skipn_length. rewrite H0; clear - POS.  simpl.
rewrite plus_comm. rewrite Nat.add_sub. auto.
Qed.

Theorem Zmod_mod_mult :
  forall n a b, (0 < a)%Z -> (0 <= b)%Z ->
  Zmod (Zmod n (a * b)) b = Zmod n b.
Proof.
intros n a [|b|b] Ha Hb.
now rewrite 2!Zmod_0_r.
rewrite (Zmod_eq n (a * Zpos b)).
rewrite Zmult_assoc.
unfold Zminus.
rewrite Zopp_mult_distr_l.
apply Z_mod_plus.
easy.
apply Zmult_gt_0_compat.
now apply Z.lt_gt.
easy.
now elim Hb.
Qed.

Lemma generate_and_pad_lemma1:
  forall hashed (dd: list byte) hashed' (dd': list byte) pad bitlen
   (PAD : pad = 0 \/ dd' = [])
   (H0 : Zlength dd' + 8 <= CBLOCKz)
   (H1 : 0 <= pad < 8)
   (H4: (LBLOCKz | Zlength hashed))
   (H7 : ((Zlength hashed * 4 + Zlength dd) * 8)%Z = bitlen)
   (H3: Zlength dd < CBLOCKz)
   (H2 : (LBLOCKz | Zlength hashed'))
   (H5 : intlist_to_bytelist hashed' ++ dd' =
     intlist_to_bytelist hashed ++ dd ++ [Byte.repr 128] ++ list_repeat (Z.to_nat pad) Byte.zero),
   let lastblock :=
               (dd' ++
                list_repeat (Z.to_nat (CBLOCKz - 8 - Zlength dd')) Byte.zero ++
                intlist_to_bytelist [hi_part bitlen; lo_part bitlen])
   in let lastblock' :=
             bytelist_to_intlist lastblock
   in forall (H99: Zlength lastblock = CBLOCKz),
 generate_and_pad (intlist_to_bytelist hashed ++ dd) = hashed' ++ lastblock'.
Proof.
intros.
apply intlist_to_bytelist_inj.
rewrite intlist_to_bytelist_app.
unfold lastblock'.
rewrite bytelist_to_intlist_to_bytelist; auto.
2: rewrite H99; exists LBLOCKz; reflexivity.
unfold lastblock.
rewrite <- app_ass. rewrite H5.
unfold generate_and_pad.
rewrite intlist_to_bytelist_app.
rewrite bytelist_to_intlist_to_bytelist; auto.
*
repeat rewrite app_ass.
f_equal. f_equal. f_equal.
rewrite <- app_ass.
f_equal.
rewrite list_repeat_app.
f_equal.
clear - H5 H2 H1 H0 PAD.
assert (Zlength dd' <= 56) by (change CBLOCKz with 64 in H0; omega).
clear H0.
replace (Zlength (intlist_to_bytelist hashed ++ dd))
  with (4*Zlength hashed' + Zlength dd' - (1+pad)).
2:{
rewrite Z.mul_comm.
rewrite <-  Zlength_intlist_to_bytelist.
rewrite <- Zlength_app.
rewrite H5.
rewrite <- app_ass.
rewrite Zlength_app.
forget (Zlength (intlist_to_bytelist hashed ++ dd)) as B.
rewrite Zlength_app.
rewrite Zlength_cons, Zlength_nil, Zlength_correct.
rewrite length_list_repeat. rewrite Z2Nat.id by omega. omega.
} 
change (Z.of_nat CBLOCK - 8) with 56.
clear H5.
rewrite <- Z2Nat.inj_add by (change CBLOCKz with 64; omega).
f_equal. {
 transitivity (- (4 * Zlength hashed' + (Zlength dd' - (1 + pad) + 9)) mod 64).
 f_equal. f_equal. omega.
 rewrite <- Z.sub_0_l.
 rewrite Zminus_mod.
 rewrite Zplus_mod.
 rewrite Z.mul_comm.
 destruct H2 as [a H2]; rewrite H2.
 rewrite <- Z.mul_assoc.
 change (LBLOCKz * 4)%Z with 64%Z.
 rewrite Zmult_mod.
 assert (64<>0) by (clear; omega).
 rewrite Z.mod_same by auto. rewrite Z.mul_0_r.
 rewrite Z.mod_0_l at 2 by auto.
 rewrite Z.add_0_l. rewrite Z.mod_mod by auto.
 replace (0 mod 64) with (64 mod 64) by reflexivity.
 change CBLOCKz with 64. change LBLOCKz with 16 in H2.
 destruct PAD; subst.
 rewrite <- Zminus_mod.
 rewrite Z.mod_small; try omega.
 rewrite Zlength_correct in H|-*; omega.
 rewrite Zlength_nil in *.
 rewrite <- Zminus_mod.
 rewrite Z.mod_small; omega.
}
 rewrite Zlength_app, Zlength_intlist_to_bytelist.
 rewrite H7.
 reflexivity.
*
 autorewrite with sublist.
 rewrite Zlength_list_repeat by (apply Z_mod_lt; compute; auto).
 forget ( Zlength hashed * 4 + Zlength dd) as d.
 change (Z.succ 0) with 1.
 change WORD with 4.
 rewrite Z.add_assoc.
 replace (d + 9) with (d + 1 + 8) by omega.
 forget (d+1) as e.
 apply Zmod_divide; try omega.
 clear.
 rewrite Zplus_mod.
 change 64 with (16*4)%Z.
 rewrite Zmod_mod_mult by omega.
 rewrite <- Z.sub_0_l.
 rewrite Zminus_mod.
 rewrite (Zplus_mod e 8).
 change (0 mod 4) with (4 mod 4).
 change (8 mod 4) with 0.
 rewrite Z.add_0_r.
  rewrite <- Zminus_mod.
  rewrite <- Zplus_mod.
 replace (e + (4 - e mod 4)) with (4 + (e - e mod 4)) by omega.
 rewrite Zplus_mod. rewrite Z.mod_same by omega.
 rewrite Zminus_mod.   rewrite Z.mod_mod by omega.
 rewrite Z.sub_diag. reflexivity.
Qed.
