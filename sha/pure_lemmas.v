(* THIS FILE CONTAINS
   Lemmas that DO NOT depend on CompCert or Verifiable C,
   and that are used in the proof of the C program but are not
   used in the proof of functional_prog.v.
*)

Require Import Coqlib.
Require Import Integers. 
Require Import List. Import ListNotations. 
Require Import general_lemmas.
Require Import sha.SHA256.
Require Import msl.Coqlib2. 
Require Import floyd.coqlib3. 
Require Import floyd.sublist. 
Require Export sha.common_lemmas. 
Require Psatz.

Global Opaque CBLOCKz LBLOCKz.

Lemma Zlength_intlist_to_Zlist:
  forall l : list int,
       Zlength (intlist_to_Zlist l) = (Zlength l * 4)%Z.
Proof.
intros.
repeat rewrite Zlength_correct. rewrite length_intlist_to_Zlist.
rewrite Nat2Z.inj_mul. rewrite Z.mul_comm. reflexivity.
Qed.

Hint Rewrite Zlength_intlist_to_Zlist : sublist.

Lemma skipn_intlist_to_Zlist:
  forall i m, skipn (4*i) (intlist_to_Zlist m) = intlist_to_Zlist (skipn i m).
Proof.
induction i; intros.
reflexivity.
replace (4 * S i)%nat with (4 + 4 * i)%nat by omega.
destruct m; try reflexivity.
apply IHi.
Qed.

Lemma firstn_intlist_to_Zlist:
  forall i m, firstn (4*i) (intlist_to_Zlist m) = intlist_to_Zlist (firstn i m).
Proof.
induction i; intros.
reflexivity.
replace (4 * S i)%nat with (4 + 4 * i)%nat by omega.
destruct m; try reflexivity.
simpl. f_equal. f_equal. f_equal. f_equal. 
apply IHi.
Qed.

Lemma sublist_intlist_to_Zlist:
 forall i j m,
  sublist (i * WORD) (j * WORD) (intlist_to_Zlist m) =
  intlist_to_Zlist (sublist i j m).
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
rewrite <- firstn_intlist_to_Zlist.
f_equal.
destruct (zlt i 0).
rewrite (Z2Nat_neg _ l).
rewrite (Z2Nat_neg (4*i)) by omega.
reflexivity.
rewrite ?Z2Nat.inj_mul by omega.
change (Z.to_nat 4) with 4%nat.
apply skipn_intlist_to_Zlist.
Qed.

Lemma sublist_singleton:
  forall {A} i (al: list A) d,
    0 <= i < Zlength al ->
    sublist i (i+1) al = [Znth i al d].
Proof.
intros.
unfold sublist.
replace (i+1-i) with 1 by omega.
change (Z.to_nat 1) with 1%nat.
unfold Znth.
rewrite if_false by omega.
assert (Z.to_nat i < length al)%nat.
destruct H.
rewrite Zlength_correct in H0.
apply Nat2Z.inj_lt.
rewrite Z2Nat.id by omega. auto.
clear H.
revert al H0; induction (Z.to_nat i); destruct al; intros;
  try (simpl in *; omega);  try reflexivity.
simpl in H0.
simpl nth.
rewrite <- (IHn al) by omega.
reflexivity.
Qed.

Lemma Zlist_to_intlist_to_Zlist:
  forall nl: list Z, 
  NPeano.divide (Z.to_nat WORD) (length nl) ->
  Forall isbyteZ nl ->
  intlist_to_Zlist (Zlist_to_intlist nl) = nl.
Proof.
intros nl [k H].
revert nl H; induction k; intros.
destruct nl; inv H; reflexivity.
simpl in H.
destruct nl as [ | a [ | b [ | c [ | d ?]]]]; inv H.
inv H0. inv H4. inv H5. inv H6.
unfold Zlist_to_intlist; fold Zlist_to_intlist.
rewrite intlist_to_Zlist_Z_to_int_cons by auto.
repeat f_equal; auto.
Qed.

Lemma length_Zlist_to_intlist: forall n l, 
       length l = (Z.to_nat WORD * n)%nat -> 
       length (Zlist_to_intlist l) = n.
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

(*
Lemma big_endian_integer_ext:
 forall f f', (forall z, (0 <= z < WORD)%Z -> f z = f' z) ->
    big_endian_integer f = big_endian_integer f'.
Proof.
unfold big_endian_integer;
intros.
repeat f_equal; intros; apply H; repeat split; compute; auto; congruence.
Qed.
*)

Lemma big_endian_integer4:
 forall c0 c1 c2 c3,
  big_endian_integer (c0::c1::c2::c3::nil) =
  Int.or (Int.shl c0 (Int.repr 24)) (Int.or (Int.shl c1 (Int.repr 16))
   (Int.or (Int.shl c2 (Int.repr 8)) c3)).
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
    NPeano.divide LBLOCK (length bb) <->
    (LBLOCKz | Zlength bb).
Proof.
intros; split; intros [n ?].
exists (Z.of_nat n). rewrite Zlength_correct, H.
rewrite Nat2Z.inj_mul; auto.
exists (Z.to_nat n).
rewrite Zlength_correct in H.
assert (0 <= n).
assert (0 <= n * LBLOCKz) by omega.
apply Z.mul_nonneg_cancel_r in H0; auto.
rewrite <- (Z2Nat.id (n*LBLOCKz)%Z) in H by omega.
apply Nat2Z.inj in H. rewrite H.
change LBLOCK with (Z.to_nat LBLOCKz).
rewrite Z2Nat.inj_mul; auto.
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
(*change LBLOCK with 16%nat in H0.*)
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
rewrite NPeano.Nat.sub_add by Psatz.lia.
omega.
(*Psatz.lia.*)
(*
rewrite H0. assert (Hn: (n*LBLOCK >= 0)%nat).
  remember ((n * LBLOCK)%nat). clear. omega.
  omega. 
*)
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
rewrite plus_comm. rewrite NPeano.Nat.add_sub. auto.
(*simpl in H0. rewrite H0; clear - POS. Psatz.lia.*)
Qed.
