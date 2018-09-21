Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import List. Import ListNotations.
Require Import sha.general_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.SHA256.
Require Import sha.pure_lemmas.
Require Import sha.functional_prog.

(* Lemma 1: M = Prefix(Pad(M)) *)

(* TODO: replace InWords with InBlocks 4? *)
Inductive InWords : list byte -> Prop :=
  | words_nil : InWords []
  | words_word : forall (a b c d : byte) (msg : list byte),
                   InWords msg -> InWords (a :: b :: c :: d :: msg).

(* *** New definition for this lemma. *)
Definition pad (msg : list byte) : list byte :=
  let n := Zlength msg in
  msg ++ [Byte.repr 128%Z]
      ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) Byte.zero
      ++ intlist_to_bytelist (([Int.repr (n * 8 / Int.modulus); Int.repr (n * 8)])%list).

Definition generate_and_pad' (msg : list byte) : list int :=
  bytelist_to_intlist (pad msg).


(* ----------------- ^ Definitions *)

Lemma fstpad_len :
  forall (msg : list byte),
    Datatypes.length (msg ++ [Byte.repr 128]
                 ++ list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) Byte.zero)
= (Datatypes.length msg + (S (Z.to_nat (- (Zlength msg + 9) mod 64))))%nat.
Proof.
  intros msg.
  simpl.
  rewrite -> app_length.
  simpl.
  rewrite -> length_list_repeat.
  reflexivity.
Qed.

Lemma InWords_len4 : forall (l : list byte),
                       Nat.divide (Z.to_nat WORD) (length l) -> InWords l.
Proof.
  intros l [x H].
  revert l H.
  induction x.
  intros l H. simpl in H.
  destruct l.
    apply words_nil.
    simpl in H. inversion H.
  intros l H.
  destruct l as [ | a [ | b [ | c [ | d ? ]]]].
    inversion H.
    inversion H.
    inversion H.
    inversion H.
    specialize (IHx l).
      apply words_word.
      apply IHx.
      simpl in H. inversion H.
      simpl. apply H1.
Qed.

(* TODO: clear out the SearchAbouts / clean up proof *)
Lemma pad_len_64_mod : forall (msg : list byte),
                           (Zlength (pad msg)) mod 64 = 0.
Proof.
  intros msg.
  unfold pad.
  rewrite -> Zlength_correct.
  repeat rewrite -> app_length.
  simpl.
  assert (succ: forall (n : nat), S n = (n + 1)%nat).
    intros. induction n. reflexivity. omega.
  rewrite -> succ.
  assert ((length msg +
      (length (list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) Byte.zero) + 8 +
       1))%nat = (length msg +
      (length (list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) Byte.zero) + 9))%nat) by omega.
  rewrite -> H. clear H.

  rewrite -> Zlength_correct.
  rewrite -> length_list_repeat.

  repeat rewrite -> Nat2Z.inj_add.
  rewrite -> Z2Nat.id.

  assert (move : forall (a b c : Z), a + (b + c) = (a + c) + b).
  intros. omega.

  rewrite -> move.
  rewrite -> Zplus_mod_idemp_r.

  assert (Z_9 : 9 = Z.of_nat (9%nat)). reflexivity.
  rewrite -> Z_9.

  repeat rewrite <- Nat2Z.inj_add.

  assert (forall (x : Z), x + (-x) = 0). intros. omega.

  rewrite -> H.
  reflexivity.

  * apply Z.mod_pos_bound.
    omega.
Qed.

(* more usable versions *)
Lemma pad_len_64 : forall (msg : list byte), exists (n : Z),
                           Zlength (pad msg) = 64 * n /\ n >= 0.
Proof.
  intros msg.
  pose proof pad_len_64_mod msg as pad_len_mod.
  rewrite -> Zmod_divides in *. 2: omega.

  destruct pad_len_mod.
  exists x.
  split.
  apply H.
  specialize (Zlength_nonneg (pad msg)); intros. omega.
Qed.

Lemma pad_len_64_nat : forall (msg : list byte), exists (n : nat),
                           (length (pad msg))%nat = (64 * n)%nat.
Proof.
  intros msg.
  pose proof pad_len_64 msg as pad_len_64.

  rewrite -> Zlength_correct in *.
  destruct pad_len_64.
  exists (Z.to_nat x).
  destruct H.

  assert (app_each : Z.to_nat (Z.of_nat (length (pad msg))) = Z.to_nat (64 * x)).
    rewrite -> H. reflexivity.

  rewrite -> Nat2Z.id in app_each.

  rewrite -> app_each.
(*  SearchAbout (Z.to_nat (_ * _)).*)
  rewrite -> Z2Nat.inj_mul.
  assert (n_64 : Z.to_nat 64 = 64%nat). reflexivity.

  rewrite -> n_64.
  reflexivity.

  * omega.
  * omega.
Qed.

Lemma total_pad_len_Zlist : forall (msg : list byte), exists (n : nat),
     length
       (msg ++ [Byte.repr 128] ++ list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) Byte.zero)
     =  (n * Z.to_nat WORD (* 4 *))%nat.
Proof.
  intros msg.
  pose proof pad_len_64_nat msg as pad_len_64_nat.

  unfold pad in *.
  repeat rewrite -> app_length in *.
  destruct pad_len_64_nat.
  assert (sym: (64 * x)%nat = (x * 64)%nat) by omega.
  rewrite -> sym in *. clear sym.

  simpl in *.
  assert (Pos.to_nat 4 = 4%nat) by reflexivity.
  (*rewrite -> H0. clear H0.*)

  rewrite -> length_list_repeat in *.

  assert (add_both: (length msg + S (Z.to_nat (- (Zlength msg + 9) mod 64) ))%nat =
      (x * 64 - 8)%nat) by omega. clear H.

  rewrite -> add_both.
  assert ((x * 64 - 8)%nat = (4 * (16 * x - 2))%nat) by omega.

  rewrite -> H.
  exists (16 * x - 2)%nat.
  omega.
Qed.

Lemma pad_inwords :
  forall (msg : list byte),
    InWords (msg ++ [Byte.repr 128]
                 ++ list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) Byte.zero).
Proof.
  intros msg.
  apply InWords_len4.
  pose proof total_pad_len_Zlist.
  specialize (H msg).
  unfold Nat.divide.
  apply H.
Qed.

Definition fulllen (len : Z) :=
  len + 1%Z + (- (len + 9) mod 64).

Lemma app_left : forall (a b c d : list byte),
   a ++ b ++ c ++ d = (a ++ b ++ c) ++ d.
(* a ++ (b ++ (c ++ d)) = (a ++ (b ++ c)) ++ d *)
Proof.
   intros a b c d.
   assert (b ++ (c ++ d) = (b ++ c) ++ d) as assert1.
     rewrite -> app_assoc. reflexivity.
   rewrite -> assert1.
   rewrite -> app_assoc.
   reflexivity.
Qed.

(* can use extensionality *)
Theorem pad_compose_equal : forall (msg : list byte),
                              generate_and_pad' msg = generate_and_pad msg.
Proof.
  intros msg.
  unfold generate_and_pad'.
  unfold pad.
  unfold generate_and_pad.
  (* need il => ZIL (IZL il), and
     ZIL a ++ Zil b = ZIL (a ++ b) (with length a being a multiple of 4)
   *)
  pose proof pad_inwords as pad_inwords.
  specialize (pad_inwords msg).
  rewrite -> app_left.
  induction pad_inwords.
  (* case none *)
    assert (forall l : list byte, [] ++ l = l) as Happend. reflexivity.
    specialize (Happend (intlist_to_bytelist
        [Int.repr (Zlength msg * 8 / Int.modulus);
        Int.repr (Zlength msg * 8)])).
    rewrite -> Happend.
    rewrite -> intlist_to_bytelist_to_intlist.
    reflexivity.
  (* case a :: b :: c :: d :: msg0 *)
    Opaque intlist_to_bytelist.
    simpl.
    apply f_equal.
    apply IHpad_inwords.
Qed.


(* ------------------------------------------------ *)

(* Lemma 2: |M1| = |M2| -> |Pad(M1)| = |Pad(M2)| *)

Theorem length_equal_pad_length : forall (msg1 : list byte) (msg2 : list byte),
     Zlength msg1  = Zlength msg2 ->
     Zlength (generate_and_pad msg1) = Zlength (generate_and_pad msg2).
Proof.
  intros m1 m2 H.
  repeat rewrite -> functional_prog.length_generate_and_pad.
  rewrite -> H.
  reflexivity.
Qed.

(* ------------------------------------------------ *)

(* Lemma 3: |M1| =/= |M2| ->
last block of Pad(M1) =/= last block of Pad(M2)

or, if one-to-one property is desired (for HMAC), only need to prove that
the padded messages differ
*)

