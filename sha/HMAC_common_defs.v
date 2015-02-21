Require Import Integers.
Require Import Recdef.
Require Import List. Import ListNotations.
Require Import Arith.
Require Import Coqlib.
Require Import pure_lemmas.
Require Import SHA256.
Require Import hmac_pure_lemmas.
Require Import ByteBitRelations.
Require Import HMAC_functional_prog.
Require Import sha_padding_lemmas.

Definition Blist := list bool.

Definition concat {A : Type} (l : list (list A)) : list A :=
  flat_map id l.

(* Replacing splitVector *)
Definition splitList {A : Type} (n : nat) (l : list A) : (list A * list A) :=
  (firstn n l, skipn n l).

(* Replacing BVxor *)
Definition BLxor (xs : Blist) (ys : Blist) :=
  map (fun p => xorb (fst p) (snd p)) (combine xs ys).

Lemma skipn_length:
  forall {A} n (al: list A), 
    (length al >= n)%nat -> 
    (length (skipn n al) = length al - n)%nat.
Proof.
 induction n; destruct al; simpl; intros; auto.
 apply IHn. omega.
Qed.

Function hash_blocks_bits (hash_block_bit : Blist -> Blist -> Blist) (r: Blist)
         (msg: Blist) {measure length msg} : Blist :=
  match msg with
  | nil => r
  | _ => hash_blocks_bits hash_block_bit (hash_block_bit r (firstn 512 msg)) (skipn 512 msg)
  end.
Proof. intros.
 destruct (lt_dec (length msg) 512). 
 rewrite skipn_short. simpl; omega. rewrite <- teq; omega.
 rewrite skipn_length. simpl; omega. rewrite <- teq; omega.
Defined.


(* TODO use neater definition with conversion functions *)
(* TODO split out of HMAC_spec_pad *)

Definition c := (32 * 8)%nat.
Definition p := (32 * 8)%nat.
Definition b := (c + p)%nat.
Definition BlockSize := 64.
Definition BlockSize_Bits := BlockSize * 8.

Definition intsToBits (l : list int) : list bool :=
  bytesToBits (SHA256.intlist_to_Zlist l).

Definition bitsToInts (l : Blist) : list int :=
  SHA256.Zlist_to_intlist (bitsToBytes l).

Definition sha_iv : Blist :=
  intsToBits SHA256.init_registers.

Definition sha_h (regs : Blist) (block : Blist) : Blist :=
  intsToBits (SHA256.hash_block (bitsToInts regs) (bitsToInts block)).

Definition sha_splitandpad (msg : Blist) : Blist :=
  bytesToBits (sha_padding_lemmas.pad (bitsToBytes msg)).

(* artifact of app_fpad definition *)
Definition fpad_inner (msg : list Z) : list Z :=
  (let n := BlockSize + Zlength msg in
  [128%Z]
    ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0
    ++ intlist_to_Zlist ([Int.repr (n * 8 / Int.modulus); Int.repr (n * 8)]))%list.

Definition fpad (msg : Blist) : Blist :=
  bytesToBits (fpad_inner (bitsToBytes msg)).

(* --------------- *)

Lemma list_nil : forall {A : Type} (l : list A),
                   length l = 0%nat -> l = nil.
Proof.
  intros A l len.
  induction l. reflexivity. inversion len.
Qed.

Lemma BLxor_length : forall (l1 l2 : Blist) (n : nat),
                       length l1 = n ->
                       length l2 = n ->
                       length (BLxor l1 l2) = n.
Proof.
  intros l1 l2 n len1 len2.
  revert l1 l2 len1 len2.
  induction n as [ | n'].
  - intros. apply list_nil in len1. apply list_nil in len2.
    subst. reflexivity.
  - intros l1 l2 len1 len2.
    destruct l1; destruct l2; inversion len1; inversion len2.
    simpl.
    rewrite -> map_length.
    rewrite -> combine_length.
    rewrite H0. rewrite H1. simpl.
    f_equal.
    apply min_l.
    omega.
Qed.

Lemma split_append_id : forall {A : Type} (len : nat) (l1 l2 : list A),
                               length l1 = len -> length l2 = len ->
                               splitList len (l1 ++ l2) = (l1, l2).
Proof.
  induction len; intros l1 l2 len1 len2.
  -
    assert (H: forall {A : Type} (l : list A), length l = 0%nat -> l = []).
      intros. destruct l.
      reflexivity. inversion H.
    apply H in len1. apply H in len2.
    subst. reflexivity.
  -
    unfold splitList.
    rewrite -> firstn_exact. rewrite -> skipn_exact.
    * reflexivity. * assumption. * assumption.
Qed.


Lemma fold_left_iv_length: forall k (HK: forall iv x, length iv = k -> length (sha_h iv x) = k) l iv x , 
  length iv = k ->
  length (fold_left sha_h l (sha_h iv x)) = k.
Proof. intros k HK l.
  induction l. simpl. apply HK. 
  simpl. intros.  rewrite IHl. trivial. apply HK. trivial.
Qed. 


(* modified version of sha_padding_lemmas.pad *)
Definition pad_inc (msg : list Z) : list Z := 
  let n := BlockSize + Zlength msg in
  msg ++ [128%Z] 
      ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0
      ++ intlist_to_Zlist ([Int.repr (n * 8 / Int.modulus); Int.repr (n * 8)]).

Definition sha_splitandpad_inc (msg : Blist) : Blist :=
  bytesToBits (pad_inc (bitsToBytes msg)).

Lemma sha_splitandpad_inc_nil: length (sha_splitandpad_inc nil) = 512%nat.
Proof. reflexivity. Qed.

Lemma add_blocksize_length l n: 0<=n ->
      BinInt.Z.add n (Zcomplements.Zlength l) = Zcomplements.Zlength ((Coqlib.list_repeat (Z.to_nat n) true) ++ l).
Proof. intros. do 2 rewrite Zlength_correct.
  rewrite app_length, length_list_repeat, Nat2Z.inj_add, Z2Nat.id; trivial.
Qed. 

Lemma pad_inc_length: forall l, exists k, (0 < k /\ length (pad_inc l) = k*64)%nat.
Proof. unfold pad_inc.
  induction l. 
  simpl. exists (1%nat). omega.
  destruct IHl as [k [K HK]]. repeat rewrite app_length in *. rewrite length_list_repeat in *.
  rewrite pure_lemmas.length_intlist_to_Zlist in *.
  remember (BinInt.Z.to_nat
        (BinInt.Z.modulo
           (BinInt.Z.opp
              (BinInt.Z.add (BinInt.Z.add BlockSize (Zcomplements.Zlength l))
                 9)) 64)).
  remember (BinInt.Z.to_nat
      (BinInt.Z.modulo
         (BinInt.Z.opp
            (BinInt.Z.add
               (BinInt.Z.add BlockSize (Zcomplements.Zlength (a :: l))) 9))
         64)).
  simpl. simpl in HK.
  assert ((BinInt.Z.add
                   (BinInt.Z.add BlockSize (Zcomplements.Zlength (a :: l))) 9) =
          BinInt.Z.add 1 (BinInt.Z.add
                   (BinInt.Z.add BlockSize (Zcomplements.Zlength l)) 9)).
        rewrite BinInt.Z.add_assoc. f_equal.
          rewrite BinInt.Z.add_assoc. rewrite (BinInt.Z.add_comm 1). rewrite <- (BinInt.Z.add_assoc _ 1).
          f_equal. 
          repeat rewrite Zcomplements.Zlength_correct. 
          apply (Znat.Nat2Z.inj_add 1 (length l)).
   rewrite H in Heqn0; clear H. 
   remember (BinInt.Z.add (BinInt.Z.add BlockSize (Zcomplements.Zlength l)) 9). clear Heqz.
   subst n n0. rewrite Z.opp_add_distr. rewrite <- (Z.add_comm (-z)). remember (-z) as zz. clear Heqzz.
   simpl.
   destruct (zeq (zz mod 64) 0).
     rewrite e in HK.
     assert ((zz+-1) mod 64 = 63). clear - e.  apply Zmod_divides in e. 2:omega. 
        destruct e. subst. rewrite Zplus_mod. rewrite Z.mul_comm. rewrite Z_mod_mult. simpl.
        rewrite Zmod_mod. apply Zmod_unique with (a:=(-1)). omega. omega.
     rewrite H. clear H e. simpl in *. exists (S k). omega.
   assert ((zz + -1) mod 64 = (zz mod 64) - 1 /\ 0 <= (zz mod 64) - 1). 
     clear -n. rewrite Zplus_mod. assert (0 <= zz mod 64 < 64). apply Z.mod_pos_bound. omega.
     split. 2: omega.
     symmetry. eapply Z.mod_unique. left. omega.
     assert (63 = -1 mod 64). eapply Z.mod_unique. left; omega. instantiate (1:=-1). omega.
     rewrite <- H0. instantiate (1:=1). omega.
   destruct H. rewrite H. clear H.   
   assert (Z.to_nat (zz mod 64 - 1) = minus (Z.to_nat (zz mod 64)) 1).
     clear - n H0. remember (zz mod 64).  clear Heqz. rewrite Z2Nat.inj_sub. reflexivity. omega. 
   rewrite H; clear H. rewrite <- NPeano.Nat.add_sub_swap. rewrite minus_Sn_m. simpl. exists k. omega.
   omega. apply (Z2Nat.inj_le 1). omega. omega. omega.
Qed. 

Lemma sha_splitandpad_inc_length: forall m, exists k, 
      (0<k /\ length (sha_splitandpad_inc m) = k * 512)%nat.
Proof. intros. unfold sha_splitandpad_inc.
  destruct (pad_inc_length (bitsToBytes m)) as [k [K HK]].
  rewrite bytesToBits_len, HK. exists k. split. trivial. omega.
Qed.


Lemma sha_splitandpad_inc_InBlocks m : InBlocks 512 (sha_splitandpad_inc m).
Proof. intros. apply InBlocks_len.
  destruct (sha_splitandpad_inc_length m) as [k [K HK]].
  rewrite HK. exists k. trivial.
Qed.

Lemma sha_iv_length: length sha_iv = 256%nat.
Proof. reflexivity. Qed.

Lemma hash_blocks_bits_len: forall r l, length r = 256%nat -> 
      InBlocks 512 l ->
      length (hash_blocks_bits sha_h r l) = 256%nat.
Proof. intros r l.
  apply hash_blocks_bits_ind.
  intros. trivial.
  intros. destruct _x. contradiction. subst msg; clear y.
  inv H1.
  apply H; clear H. unfold sha_h, intsToBits.
 rewrite bytesToBits_len, length_intlist_to_Zlist.
  rewrite length_hash_block. omega.
  unfold bitsToInts. erewrite length_Zlist_to_intlist. reflexivity.
    rewrite bitsToBytes_len_gen with (n:=32%nat). reflexivity. apply H0.
  unfold bitsToInts. erewrite length_Zlist_to_intlist. reflexivity.
    erewrite bitsToBytes_len_gen with (n:=64%nat). reflexivity.
    rewrite H3, firstn_exact. apply H2. apply H2.
    rewrite H3, skipn_exact. assumption. apply H2. 
Qed.

Lemma sha_h_length iv blk: length iv = c -> length blk = b ->
      length (sha_h iv blk) = c.
Proof. intros.
 unfold sha_h, intsToBits.
  rewrite bytesToBits_len, pure_lemmas.length_intlist_to_Zlist.
  rewrite common_lemmas.length_hash_block. reflexivity.
  unfold bitsToInts. erewrite pure_lemmas.length_Zlist_to_intlist. reflexivity. 
  erewrite bitsToBytes_len_gen. reflexivity.
  rewrite H; reflexivity.
  unfold bitsToInts. erewrite pure_lemmas.length_Zlist_to_intlist. reflexivity. 
  erewrite bitsToBytes_len_gen. reflexivity.
  rewrite H0; reflexivity.
Qed.
