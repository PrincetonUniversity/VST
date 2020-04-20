(* Lemmas used by the hmac proofs that are independent of C/CompCert/VST*)

Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.
Require Import sha.general_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.SHA256.
Require Import sha.pure_lemmas.     (* sha *)
Require Import sha.spec_sha.
(*Require Import sublist.*)

Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.

Lemma str_to_bytes_length: forall k,
      String.length k = length (str_to_bytes k).
Proof. intros. induction k; simpl; auto. Qed.

Lemma first64_sixtyfour {A} (a:A):
      firstn 64 (HMAC_SHA256.sixtyfour a) = HMAC_SHA256.sixtyfour a.
Proof. apply firstn_precise. simpl. reflexivity. Qed.

Lemma length_SF {A} (x:A): length (HMAC_SHA256.sixtyfour x) = 64%nat.
Proof.
  unfold HMAC_SHA256.sixtyfour.
  rewrite length_list_repeat; trivial.
Qed.

Lemma Zlength_mkArgZ k pad: Zlength (HMAC_SHA256.mkArg k pad) = Z.of_nat (min (length k) 64).
Proof. intros. repeat rewrite Zlength_correct.
   unfold HMAC_SHA256.mkArg, HMAC_SHA256.sixtyfour.
   repeat rewrite map_length.
   rewrite combine_length, length_list_repeat . trivial.
Qed.

Lemma nth_zeropad_left {d d'}: forall l i (I: 0<= i < Zlength l),
      nth (Z.to_nat i) (HMAC_SHA256.zeroPad l) d = nth (Z.to_nat i) l d'.
Proof. unfold HMAC_SHA256.zeroPad. intros.
  destruct I.
  apply Z2Nat.inj_lt in H0; try omega.
  rewrite Zlength_correct, Nat2Z.id in H0.
  rewrite app_nth1; trivial.
  apply nth_indep; trivial.
Qed.

Lemma mkKey_left {d d'}: forall l (L: false = (Zlength l >? 64))
        i (I: 0<= i < Zlength l),
      nth (Z.to_nat i) (HMAC_SHA256.mkKey l) d = nth (Z.to_nat i) l d'.
Proof.
  unfold HMAC_SHA256.mkKey. intros. simpl. rewrite <- L.
  apply nth_zeropad_left; trivial.
Qed.

Lemma nth_zeropad_right {d} l i (I: Zlength l <= i < 64):
      nth (Z.to_nat i) (HMAC_SHA256.zeroPad l) d = Byte.zero.
Proof. unfold HMAC_SHA256.zeroPad.
  specialize (Zlength_nonneg l). intros.
  rewrite app_nth2. rewrite nth_list_repeat'. trivial.
  apply minus_lt_compat_r. destruct I. apply Z2Nat.inj_lt in H1. apply H1.
  omega.
  omega.
  destruct I. apply Z2Nat.inj_le in H0; trivial.
    rewrite Zlength_correct, Nat2Z.id in H0. apply H0.
    omega.
  destruct I. apply Z2Nat.inj_le in H0; trivial.
    rewrite Zlength_correct, Nat2Z.id in H0. apply H0.
    omega.
Qed.

Lemma mkKey_right {d}: forall l (L: false = (Zlength l >? 64))
        i (I: Zlength l <= i < 64),
      nth (Z.to_nat i) (HMAC_SHA256.mkKey l) d = Byte.zero.
Proof.
  unfold HMAC_SHA256.mkKey. intros. simpl. rewrite <- L.
  apply nth_zeropad_right; trivial.
Qed.

Lemma zeroPad_BlockSize: forall k, (length k <= SHA256.BlockSize)%nat ->
  length (HMAC_SHA256.zeroPad k) = SHA256.BlockSize%nat.
Proof. unfold HMAC_SHA256.zeroPad. intros. rewrite app_length, (*length_Nlist*) length_list_repeat. omega.
Qed.

Lemma length_SHA256': forall l,
  length (functional_prog.SHA_256' l) = SHA256.DigestLength.
Proof. intros. unfold functional_prog.SHA_256'. simpl.
  rewrite length_intlist_to_bytelist, functional_prog.length_process_msg. reflexivity.
Qed.

Lemma mkKey_length l: length (HMAC_SHA256.mkKey l) = SHA256.BlockSize.
Proof. intros. unfold HMAC_SHA256.mkKey.
  remember (Zlength l >? Z.of_nat SHA256.BlockSize) as z.
  destruct z. apply zeroPad_BlockSize.
    rewrite length_SHA256'.
    apply Nat2Z.inj_le. simpl. omega.
  apply zeroPad_BlockSize.
    rewrite Zlength_correct in Heqz.
    apply Nat2Z.inj_le.
    specialize (Zgt_cases (Z.of_nat (Datatypes.length l)) (Z.of_nat SHA256.BlockSize)). rewrite <- Heqz. trivial.
Qed.

Lemma mkKey_atBlockSize s: length s = SHA256.BlockSize%nat ->
      HMAC_SHA256.mkKey s = s.
Proof. unfold HMAC_SHA256.mkKey. rewrite Zlength_correct.
  intros. rewrite H.
  simpl. unfold HMAC_SHA256.zeroPad. rewrite H. simpl.
  apply app_nil_r.
Qed.

Lemma HMAC_length d k: length (HMAC256 d k) = 32%nat.
Proof.
  unfold HMAC_SHA256.HMAC, HMAC_SHA256.OUTER.
  apply length_SHA256'.
Qed.
Lemma HMAC_Zlength d k: Zlength (HMAC256 d k) = 32.
Proof.
  rewrite Zlength_correct, HMAC_length. reflexivity.
Qed.