Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.
Require Import Coq.ZArith.BinInt. (* Z *)
Require Import Coq.ZArith.Zcomplements. (* Zlength *)
Require Import compcert.lib.Integers.          (* byte *)
Require Import Coq.Numbers.Natural.Peano.NPeano.

Require Import Coq.Strings.Ascii.
Require Import Coq.Program.Tactics.
Require Import sha.XorCorrespondence. (* Blist *)
Require Import sha.Bruteforce.
Require Import sha.general_lemmas.
Require Import sha.hmac_pure_lemmas.

Definition Blist := list bool.
Open Scope Z_scope.

Inductive InBlocks {A : Type} (n : nat) : list A -> Prop :=
  | InBlocks_nil : InBlocks n []
  | InBlocks_block : forall (front back full : list A),
                   length front = n ->
                   full = front ++ back ->
                   InBlocks n back ->
                   InBlocks n full.

Lemma InBlocks_len : forall {A : Type} (l : list A) (n : nat),
                       PeanoNat.Nat.divide (n) (length l) -> InBlocks n l.
Proof.
  intros A l n div.
  destruct div.
  revert A l n H.
  induction x; intros; simpl in *.
  - destruct l; simpl in *. constructor. inversion H.
  - destruct (list_splitLength _ _ _ H) as [l1 [l2 [L [L1 L2]]]]. clear H; subst.
    apply IHx in L2. clear IHx.
    apply (InBlocks_block _ l1 l2); trivial.
Qed.

(* ----- Inductive *)

Inductive bytes_bits_lists : Blist -> list byte -> Prop :=
  | eq_empty : bytes_bits_lists nil nil
  | eq_cons : forall (bits : Blist) (bytes : list byte)
                     (b0 b1 b2 b3 b4 b5 b6 b7 : bool) (b : byte),
                bytes_bits_lists bits bytes ->
                convertByteBits [b0; b1; b2; b3; b4; b5; b6; b7] b ->
                bytes_bits_lists (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bits)
                                 (b :: bytes).

(* ----- Computational *)

(* TODO: assumes Z is positive and in range, does not use Z.positive *)

Definition div_mod (num : Z) (denom : Z) : bool * Z :=
  (Z.gtb (num / denom) 0, num mod denom).

Definition byteToBits (byte : byte) : Blist :=
  let (b7, rem7) := div_mod (Byte.unsigned byte) 128 in
  let (b6, rem6) := div_mod rem7 64 in
  let (b5, rem5) := div_mod rem6 32 in
  let (b4, rem4) := div_mod rem5 16 in
  let (b3, rem3) := div_mod rem4 8 in
  let (b2, rem2) := div_mod rem3 4 in
  let (b1, rem1) := div_mod rem2 2 in
  let (b0, rem0) := div_mod rem1 1 in
  [b0; b1; b2; b3; b4; b5; b6; b7].

Fixpoint bytesToBits (bytes : list byte) : Blist :=
  match bytes with
    | [] => []
    | byte :: xs => byteToBits byte ++ bytesToBits xs
  end.

Definition bitsToByte (bits : Blist) : byte :=
  Byte.repr 
  match bits with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: nil =>
      (1 * (asZ b0) + 2 * (asZ b1) + 4 * (asZ b2) + 8 * (asZ b3)
      + 16 * (asZ b4) + 32 * (asZ b5) + 64 * (asZ b6) + 128 * (asZ b7))
    | _ => -1                  (* should not happen *)
  end.

Fixpoint bitsToBytes (bits : Blist) : list byte :=
  match bits with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: xs =>
      bitsToByte [b0; b1; b2; b3; b4; b5; b6; b7] :: bitsToBytes xs
    | _ => []
  end.

(*
Definition isbyteZ i := (0 <= i < 256)%Z.

Lemma bitsToByte_isbyteZ b0 b1 b2 b3 b4 b5 b6 b7:
      isbyteZ (bitsToByte [b0; b1; b2; b3; b4; b5; b6; b7]).
Proof. simpl. unfold asZ, isbyteZ.
  destruct b0; destruct b1; destruct b2; destruct b3;
  destruct b4; destruct b5; destruct b6; destruct b7; simpl; omega.
Qed.
*)

(* -------------------- Various theorems and lemmas *)

Lemma byteToBits_length bt: length (byteToBits bt) = 8%nat.
Proof. reflexivity. Qed.

Lemma bytes_bits_length : forall (bits : Blist) (bytes : list byte),
  bytes_bits_lists bits bytes -> length bits = (length bytes * 8)%nat.
Proof.
  intros bits bytes corr.
  induction corr.
  - reflexivity.
  - simpl. repeat f_equal. apply IHcorr.
Qed.

Lemma bytesToBits_app : forall (l1 l2 : list byte),
                          bytesToBits (l1 ++ l2) = bytesToBits l1 ++ bytesToBits l2.
Proof.
  induction l1; intros.
  * reflexivity.
  *
    simpl. rewrite -> IHl1. reflexivity.
Qed.

Lemma bytesToBits_len : forall (l : list byte),
                          length (bytesToBits l) = (length l * 8)%nat.
Proof.
  induction l; intros; try reflexivity.
  -
    simpl.
    rewrite -> IHl.
    reflexivity.
Qed.

(* Prove by brute force (test all Z in range) *)
Theorem byte_bit_byte_id : forall (b : byte),
                                bitsToByte (byteToBits b) = b.
Proof.
  intros.
  rewrite <- (Byte.repr_unsigned b) at 2.
  unfold  byteToBits.
  pose proof (Byte.unsigned_range b).
  set (x := Byte.unsigned b)  in *. clearbody x.
  change Byte.modulus with 256 in H.
  unfold bitsToByte. f_equal.
  do_range H reflexivity.
Qed.

Theorem bits_byte_bits_id : forall (b0 b1 b2 b3 b4 b5 b6 b7 : bool),
                              [b0; b1; b2; b3; b4; b5; b6; b7] =
                              byteToBits (bitsToByte [b0; b1; b2; b3; b4; b5; b6; b7]).
Proof.
  intros.
  destruct b0; destruct b1; destruct b2; destruct b3;
  destruct b4; destruct b5; destruct b6; destruct b7;
  reflexivity.
Qed.

Theorem bytes_bits_bytes_id : forall (bytes : list byte),
                                bitsToBytes (bytesToBits bytes) = bytes.
Proof.
  intros bytes.
  induction bytes as [ | byte bytes].
  - reflexivity.
  -
    unfold bytesToBits.
    fold bytesToBits.
    unfold byteToBits.
    unfold bitsToBytes.
    Opaque bitsToByte. Opaque bitsToBytes. Opaque bytesToBits.
    simpl.
    Transparent bitsToBytes. fold bitsToBytes.
    rewrite -> IHbytes.

    Transparent bitsToByte.
    unfold bitsToByte. f_equal.
    apply byte_bit_byte_id.
Qed.


(* ------------------ Theorems relating inductive and computational definitions *)

Theorem bytes_bits_def_eq : forall (bytes : list byte),
                              bytes_bits_lists (bytesToBits bytes) bytes.
Proof.
  intros bytes.
  induction bytes as [ | byte bytes ].
  -
    simpl. apply eq_empty.
  -
    Transparent bytesToBits.
    apply eq_cons.

    *
      apply IHbytes.
    *
      unfold convertByteBits.
      do 8 eexists.
      split.
      +
        reflexivity.
      +
        pose proof (Byte.unsigned_range byte). change Byte.modulus with 256 in H.
        set (b := Byte.unsigned byte) in *. clearbody b.
        do_range H reflexivity.
Qed.

Theorem bytes_bits_comp_ind : forall (bits : Blist) (bytes : list byte),
                               bits = bytesToBits bytes ->
                               bytes_bits_lists bits bytes.
Proof.
  intros bits bytes corr.
  rewrite -> corr.
  apply bytes_bits_def_eq.
Qed.

Theorem bytes_bits_ind_comp : forall (bits : Blist) (bytes : list byte),
                                 bytes_bits_lists bits bytes ->
                                 bytes = bitsToBytes bits.
Proof.
  intros bits bytes corr.
  induction corr.
  - reflexivity.
  - rewrite -> IHcorr; clear IHcorr corr.
    unfold bitsToBytes.
      fold bitsToBytes.
      f_equal. unfold convertByteBits in H.
        destruct H as [b8 [b9 [b10 [b11 [b12 [b13 [b14 [b15 [B BT]]]]]]]]].
        inversion B; clear B. subst.
        rewrite <- (Byte.repr_unsigned b). rewrite BT.
        reflexivity.
Qed.

Theorem bits_bytes_ind_comp : forall (bits : Blist) (bytes : list byte),
                                 bytes_bits_lists bits bytes ->
                                 bits = bytesToBits bytes.
Proof.
  intros bits bytes corr.
  induction corr.
  - reflexivity.
  -
    unfold convertByteBits in H.
    destruct_exists.
    destruct H7.
    rewrite <- (Byte.repr_unsigned b). rewrite H8. clear H8.
    inversion H7.
    subst.
    clear H7.
    unfold bytesToBits.
    fold bytesToBits.
    assert (list_8 : forall {A : Type} (e0 e1 e2 e3 e4 e5 e6 e7 : A) (l : list A),
                       e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: l =
                       [e0; e1; e2; e3; e4; e5; e6; e7] ++ l).
    reflexivity.
    rewrite -> list_8.
    f_equal.
    apply bits_byte_bits_id.
Qed.

(* ----------------------------- *)
(* Relating bits to bytes *)

Lemma bitsToBytes_app : forall (l m : Blist),
                          InBlocks 8 l ->
                          bitsToBytes (l ++ m) = bitsToBytes l ++ bitsToBytes m.
Proof.
  intros l m len_l. revert m.
  induction len_l.
  * intros. reflexivity.
  *
    intros m.
    rewrite -> H0.
    rewrite <- app_assoc.
    destruct front as [ | x0 [| x1 [ | x2 [ | x3 [ | x4 [ | x5 [ | x6 [ | x7 ]]]]]]]];
      inversion H.
    unfold bitsToBytes.
    Opaque bitsToByte.
    simpl.
    fold bitsToBytes.
    apply list_nil in H2.
    rewrite -> H2.
    simpl.
    rewrite -> IHlen_l.
    reflexivity.
Qed.

Lemma bitsToBytes_len_gen : forall (l : Blist) (n : nat),
                          length l = (n * 8)%nat ->
                          length (bitsToBytes l) = n.
Proof.
  intros l n len.
  assert (blocks : InBlocks 8 l).
    apply InBlocks_len. rewrite -> len. exists n. reflexivity.
  revert n len.
  induction blocks.
  * intros. simpl in *. omega.
  *
    intros n len.
    rewrite -> H0.
    rewrite -> bitsToBytes_app.
    rewrite -> app_length.
    rewrite -> H0 in len.
    rewrite -> app_length in len.
    rewrite -> H in len.

    destruct n as [ | n'].
    (* strange that destruct works here but not after [rewrite -> IHblocks] *)
    - simpl in *.
      inversion len.
    -
      destruct front as [ | x0 [| x1 [ | x2 [ | x3 [ | x4 [ | x5 [ | x6 [ | x7 ]]]]]]]];
      inversion H.

      simpl.
      apply list_nil in H2.
      rewrite -> H2. simpl.
      assert (minus : forall (n m : nat), n = m -> (n - 8)%nat = (m - 8)%nat).
        intros. omega.
      apply minus in len.
      simpl in len.
      assert (min_zero : forall (n : nat), (n - 0)%nat = n). intros. omega.
      repeat rewrite -> min_zero in len.
      clear H2 minus min_zero.
      specialize (IHblocks n').
      rewrite -> IHblocks.
      reflexivity.
      apply len.
      -
        apply InBlocks_len.
        rewrite -> H. unfold PeanoNat.Nat.divide.
        exists 1%nat. reflexivity.
Qed.

Lemma bitsToBytes_len : forall (l : Blist),
                          length l = 512%nat ->
                          Zlength (bitsToBytes l) = 64%Z.
Proof.
  intros l len.
  rewrite -> Zlength_correct.
  pose proof bitsToBytes_len_gen as len_gen.
  specialize (len_gen l 64%nat).
  rewrite -> len_gen.
  - reflexivity.
  - apply len.
Qed.

Lemma bits_bytes_bits_id : forall (l : Blist),
                             InBlocks 8 l ->
                             bytesToBits (bitsToBytes l) = l.
Proof.
  intros l len.
  induction len.
  - reflexivity.
  -
    rewrite -> H0.
    destruct front as [ | x0 [| x1 [ | x2 [ | x3 [ | x4 [ | x5 [ | x6 [ | x7 ]]]]]]]];
      inversion H.
    simpl.
    apply list_nil in H2. rewrite -> H2. simpl.
    rewrite -> IHlen.

    destruct x0; destruct x1; destruct x2; destruct x3;
    destruct x4; destruct x5; destruct x6; destruct x7; reflexivity.
Qed.

Lemma bytes_bits_lists_append:
  forall (l1 : Blist) (l2 : list byte) (m1 : Blist) (m2 : list byte),
    bytes_bits_lists l1 l2
    -> bytes_bits_lists m1 m2
    -> bytes_bits_lists (l1 ++ m1) (l2 ++ m2).
Proof.
  intros l1 l2 m1 m2.
  intros fst_eq snd_eq.
  generalize dependent m1. generalize dependent m2.
  induction fst_eq; intros.
  - repeat rewrite app_nil_l.
    apply snd_eq.
  - simpl.
    apply eq_cons.
    + apply IHfst_eq.
      apply snd_eq.
    + apply H.
Qed.


Lemma bytesToBits_nil_inv l: nil = bytesToBits l -> l = nil.
Proof. destruct l; trivial. simpl; intros. discriminate. Qed.

Lemma bytesToBits_cons b l:
      bytesToBits (b::l) = byteToBits b ++ bytesToBits l.
Proof. reflexivity. Qed.

Lemma byteToBits_injective: forall a b,
      byteToBits a = byteToBits b ->
      a = b.
Proof. intros.
assert (bitsToByte (byteToBits a) = bitsToByte (byteToBits b)).
  rewrite H; trivial.
clear H.
rewrite ?byte_bit_byte_id in H0. trivial.
Qed.

Lemma bytesToBits_injective: forall b1 b2, bytesToBits b1 = bytesToBits b2 ->
       b1=b2.
Proof. induction b1.
  intros; destruct b2; trivial. discriminate.
  destruct b2. discriminate.
  do 2 rewrite bytesToBits_cons.
  intros. destruct (app_inj1 _ _ _ _ H). reflexivity.
  rewrite (IHb1 _ H1).
  rewrite (byteToBits_injective _ _ H0). trivial.
Qed.

Lemma bitsToBytes_injective8 b1 b2 (B: bitsToBytes b1 = bitsToBytes b2)
       (L1: PeanoNat.Nat.divide 8 (length b1))
       (L2: PeanoNat.Nat.divide 8 (length b2)): b1 = b2.
Proof. intros.
  assert (bytesToBits (bitsToBytes b1) = bytesToBits (bitsToBytes b2)).
    rewrite B; trivial.
  rewrite bits_bytes_bits_id in H.
    rewrite bits_bytes_bits_id in H. trivial.
    apply InBlocks_len; assumption.
  apply InBlocks_len; assumption.
Qed.

Lemma bitsToByte_cons: forall bits h t, (h::t) = bitsToBytes bits ->
      exists b0, exists b1, exists b2, exists b3,
      exists b4, exists b5, exists b6, exists b7, exists xs,
      bits = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: xs /\
      h = bitsToByte [b0; b1; b2; b3; b4; b5; b6; b7] /\
      t = bitsToBytes xs.
Proof. intros.
  destruct bits. inv H.
  destruct bits. inv H.
  destruct bits. inv H.
  destruct bits. inv H.
  destruct bits. inv H.
  destruct bits. inv H.
  destruct bits. inv H.
  destruct bits; inv H.
  eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
  split. reflexivity.
  split; reflexivity.
Qed.

Definition intsToBits (l : list Int.int) : list bool :=
  bytesToBits (intlist_to_bytelist l).

Definition bitsToInts (l : Blist) : list Int.int :=
  bytelist_to_intlist (bitsToBytes l).
