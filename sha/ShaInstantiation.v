Require Import compcert.lib.Integers.
Require Import Recdef.
Require Import List. Import ListNotations.
Require Import Arith.
Require Import compcert.lib.Coqlib.
Require Import sha.general_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.ByteBitRelations.
Require Import sha.HMAC_common_defs.

Require Import sha.SHA256.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import sha.hmac_common_lemmas.

Require Import sha.pure_lemmas.
Require Import sha.sha_padding_lemmas.
Require Import VST.floyd.sublist. (*for Forall_list_repeat*)
Import List.

Definition c := (32 * 8)%nat.
Definition p := (32 * 8)%nat.
Definition b := (c + p)%nat.
Definition BlockSize := 64.
Definition BlockSize_Bits := BlockSize * 8.

Definition sha_iv : Blist :=
  intsToBits SHA256.init_registers.

Definition sha_h (regs : Blist) (block : Blist) : Blist :=
  intsToBits (SHA256.hash_block (bitsToInts regs) (bitsToInts block)).

Definition sha_splitandpad (msg : Blist) : Blist :=
  bytesToBits (sha_padding_lemmas.pad (bitsToBytes msg)).

(* artifact of app_fpad definition *)
Definition fpad_inner (msg : list byte) : list byte :=
  (let n := BlockSize + Zlength msg in
  [Byte.repr 128%Z]
    ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) Byte.zero
    ++ intlist_to_bytelist ([Int.repr (n * 8 / Int.modulus); Int.repr (n * 8)]))%list.

Lemma fpad_inner_length l (L:length l = p): (length (fpad_inner (bitsToBytes l)) * 8)%nat = p.
Proof.
  unfold fpad_inner. repeat rewrite app_length.
  rewrite length_list_repeat, length_intlist_to_bytelist.
  rewrite (mult_comm 4), plus_comm, Zlength_correct.
  rewrite bitsToBytes_len_gen with (n:=32%nat).
    reflexivity.
    apply L.
Qed.

Definition fpad (msg : Blist) : Blist :=
  bytesToBits (fpad_inner (bitsToBytes msg)).

Lemma fpad_length msg (M:length msg = c): length (fpad msg) = p.
unfold fpad. rewrite bytesToBits_len. apply fpad_inner_length.
apply M. (*we're exploiting the fact that c=p here*)
Qed.

(* --------------- *)
Lemma xor_equiv_byte: forall xpad XPAD k K, 
                          bytes_bits_lists xpad (HMAC_SHA256.sixtyfour XPAD) ->
                          ((length K) * 8)%nat = (c + p)%nat ->
                          bytes_bits_lists k K ->
bytes_bits_lists (BLxor k xpad) (HMAC_SHA256.mkArg K XPAD).
Proof. intros.  apply inner_general_mapByte; try assumption.
Qed.


Lemma fold_left_iv_length: forall k (HK: forall iv x, length iv = k -> length (sha_h iv x) = k) l iv x ,
  length iv = k ->
  length (fold_left sha_h l (sha_h iv x)) = k.
Proof. intros k HK l.
  induction l. simpl. apply HK.
  simpl. intros.  rewrite IHl. trivial. apply HK. trivial.
Qed.


(* modified version of sha_padding_lemmas.pad *)
Definition pad_inc (msg : list byte) : list byte :=
  let n := BlockSize + Zlength msg in
  msg ++ [Byte.repr 128%Z]
      ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) Byte.zero
      ++ intlist_to_bytelist ([Int.repr (n * 8 / Int.modulus); Int.repr (n * 8)]).

Definition sha_splitandpad_inc (msg : Blist) : Blist :=
  bytesToBits (pad_inc (bitsToBytes msg)).

Lemma sha_splitandpad_inc_nil: length (sha_splitandpad_inc nil) = 512%nat.
Proof. reflexivity. Qed.

Lemma pad_inc_length: forall l, exists k, (0 < k /\ length (pad_inc l) = k*64)%nat.
Proof. unfold pad_inc.
  induction l.
  simpl. exists (1%nat). omega.
  destruct IHl as [k [K HK]]. repeat rewrite app_length in *. rewrite length_list_repeat in *.
  rewrite length_intlist_to_bytelist in *.
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
        reflexivity. (* rewrite Zmod_mod. apply Zmod_unique with (a:=(-1)). omega. omega.*)
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

(*now in HMAC_common_defs
Lemma hash_blocks_bits_len: forall h
          (HH: forall x y, length x = c -> length y = b -> length (h x y)  = c)
          r l, length r = c ->
      InBlocks b l ->
      length (hash_blocks_bits h r l) = c.
Proof. intros h HH r l.
  apply hash_blocks_bits_ind.
  intros. trivial.
  intros. destruct _x. contradiction. subst msg; clear y.
  inv H1.
  apply H; clear H. rewrite HH. trivial. trivial.
    rewrite H3, firstn_exact. apply H2. apply H2.
    rewrite H3, skipn_exact. assumption. apply H2.
Qed.*)

Lemma B: (0<b)%nat. unfold b; simpl. omega. Qed.

Lemma hash_blocks_bits_len': forall r l, length r = 256%nat ->
      InBlocks 512 l ->
      length (hash_blocks_bits _ B sha_h r l) = 256%nat.
Proof. intros r l.
  apply hash_blocks_bits_ind.
  intros. trivial.
  intros. destruct _x. contradiction. subst msg; clear y.
  inv H1.
  apply H; clear H. unfold sha_h, intsToBits.
  rewrite bytesToBits_len, length_intlist_to_bytelist.
  rewrite length_hash_block. omega.
  unfold bitsToInts. erewrite length_bytelist_to_intlist. reflexivity.
    rewrite bitsToBytes_len_gen with (n:=32%nat). reflexivity. apply H0.
  unfold bitsToInts. erewrite length_bytelist_to_intlist. reflexivity.
    erewrite bitsToBytes_len_gen with (n:=64%nat). reflexivity.
    rewrite H3, firstn_exact. apply H2. apply H2.
    rewrite H3, skipn_exact. assumption. apply H2.
Qed.

Lemma sha_h_length iv blk: length iv = c -> length blk = b ->
      length (sha_h iv blk) = c.
Proof. intros.
 unfold sha_h, intsToBits.
  rewrite bytesToBits_len, length_intlist_to_bytelist.
  rewrite common_lemmas.length_hash_block. reflexivity.
  unfold bitsToInts. erewrite pure_lemmas.length_bytelist_to_intlist. reflexivity.
  erewrite bitsToBytes_len_gen. reflexivity.
  rewrite H; reflexivity.
  unfold bitsToInts. erewrite pure_lemmas.length_bytelist_to_intlist. reflexivity.
  erewrite bitsToBytes_len_gen. reflexivity.
  rewrite H0; reflexivity.
Qed.

(*******Injectivity of pad_inc*************************)

Lemma pad_injective_aux (l1 l2: list byte) k
     (K : k * Int.modulus + (BlockSize + Zlength l1) * 8 =
          (BlockSize + Zlength l2) * 8)
     (N : k <> 0):
     - (BlockSize + Zlength l2 + 9) mod 64 = - (BlockSize + Zlength l1 + 9) mod 64.
Proof. repeat rewrite <- Z.add_assoc. unfold BlockSize.
         repeat rewrite Z.opp_add_distr.
         rewrite (Zplus_mod (-(64))).
         assert (- (64) mod 64 = 0). reflexivity. rewrite H.
         rewrite (Zplus_mod (-(64))). rewrite H. simpl.
         repeat rewrite Zmod_mod.
         f_equal. f_equal.
         rewrite Zplus_mod. rewrite (Zplus_mod (- Zlength l1)).
         assert (Z12: - Zlength l2 mod 64 = - Zlength l1 mod 64).
         { clear H. repeat rewrite Z.mul_add_distr_r in K.
           assert (k * Int.modulus + Zlength l1 * 8 = Zlength l2 * 8). omega.
           clear K.
           assert (KK: k * (Int.modulus/8) + Zlength l1 = Zlength l2).
              rewrite <- (Zdiv_unique (k * Int.modulus + Zlength l1 * 8) 8 (Zlength l2) 0).
              2: rewrite Z.add_0_r; trivial. 2: omega.
              clear H. remember (Zlength l1) as z; clear Heqz.
              remember ((Int.modulus / 8)).
              assert (Int.modulus = z0 * 8). subst.
                rewrite <- max_unsigned_modulus, int_max_unsigned_eq. trivial.
              rewrite H; clear H Heqz0. rewrite Z.mul_assoc.
              rewrite (Z_div_plus_full_l (k*z0) 8 (z*8)). 2: omega.
              rewrite Z_div_mult_full. trivial. omega.
           rewrite <- KK; clear H KK.
           rewrite Z.opp_add_distr.
           rewrite Zplus_mod.
           assert (KM: - (k * (Int.modulus / 8)) mod 64 = 0).
             apply Zmod_unique with (a:=-k * 8388608). 2: omega. rewrite Zplus_0_r.
             rewrite <- max_unsigned_modulus, int_max_unsigned_eq. simpl.
             rewrite Zopp_mult_distr_l, <- Z.mul_assoc. reflexivity.
           rewrite KM. simpl. apply Z.mod_mod. omega.
         }
         rewrite Z12; trivial.
Qed.

Lemma pad_injective_Case5 l1 l2
  (H0 : (l1 ++ Byte.repr 128 :: nil) ++
        list_repeat (Z.to_nat (- (BlockSize + Zlength l1 + 9) mod 64)) Byte.zero =
        (l2 ++ Byte.repr 128 :: nil) ++
        list_repeat (Z.to_nat (- (BlockSize + Zlength l2 + 9) mod 64)) Byte.zero)
  (H : (BlockSize + Zlength l1) * 8 =
       ((BlockSize + Zlength l2) * 8) mod Int.modulus)
  (Nonneg1 : 0 <= (BlockSize + Zlength l1) * 8)
  (l : (BlockSize + Zlength l1) * 8 < Int.modulus):
  length l1 = length l2.
Proof. symmetry in H.
       destruct (mod_exists _ _ _ H) as [k K].
       specialize Int.modulus_pos; intros; omega.
       destruct (zeq k 0).
         subst. clear - K.
         assert (Zlength l1 = Zlength l2). omega.
         repeat rewrite Zlength_correct in H.
         rewrite <- (Nat2Z.id (length l1)).
         rewrite <- (Nat2Z.id (length l2)).
         rewrite H. reflexivity.
       clear H.
       assert (length ((l1 ++ Byte.repr 128 :: nil) ++
                list_repeat (Z.to_nat (- (BlockSize + Zlength l1 + 9) mod 64)) Byte.zero)
             = length ((l2 ++ Byte.repr 128 :: nil) ++
                list_repeat (Z.to_nat (- (BlockSize + Zlength l2 + 9) mod 64)) Byte.zero)).
       rewrite H0; trivial.
       clear H0. repeat rewrite app_length in H.
       repeat rewrite length_list_repeat in H.
       clear - K n H.
       rewrite (pad_injective_aux l1 l2 k K n) in H. omega.
Qed.

Lemma pad_inc_injective: forall l1 l2, pad_inc l1 = pad_inc l2 -> l1=l2.
Proof. intros.
remember (beq_nat (length l1) (length l2)) as d.
destruct d.
{ apply beq_nat_eq in Heqd.
  unfold pad_inc in H. repeat rewrite Zlength_correct in H.
  rewrite <- Heqd in H.
  eapply app_inv_tail. apply H. }
{ symmetry in Heqd; apply beq_nat_false in Heqd.
  unfold pad_inc in H.
  repeat rewrite app_assoc in H.
  destruct (app_inv_length2 _ _ _ _ H); clear H. reflexivity.
  apply intlist_to_bytelist_inj in H1.
  apply cons_inv in H1. destruct H1 as [_ Y].
  apply cons_inv in Y. destruct Y as [Y _].
  assert (Int.unsigned (Int.repr ((BlockSize + Zlength l1) * 8)) = Int.unsigned (Int.repr ((BlockSize + Zlength l2) * 8))).
    rewrite Y; trivial.
  elim Heqd; clear Heqd Y.
  repeat rewrite Int.unsigned_repr_eq in H.
  assert (Nonneg1: 0 <= (BlockSize + Zlength l1) * 8).
    specialize (Zlength_nonneg l1). intros; unfold BlockSize; omega.
  assert (Nonneg2: 0 <= (BlockSize + Zlength l2) * 8).
    specialize (Zlength_nonneg l2). intros; unfold BlockSize; omega.
  remember (zlt ((BlockSize + Zlength l1) * 8) Int.modulus).
  destruct s; clear Heqs.
  {  rewrite Zmod_small in H. 2: split; assumption.
     remember (zlt ((BlockSize + Zlength l2) * 8) Int.modulus).
     destruct s; clear Heqs.
     { (*Case 3*)
       rewrite Zmod_small in H. 2: split; assumption.
       clear - H.
       assert (Zlength l1 = Zlength l2). omega.
       repeat rewrite Zlength_correct in H0.
       rewrite <- (Nat2Z.id (length l1)).
       rewrite <- (Nat2Z.id (length l2)).
       rewrite H0. reflexivity. }
     { (*Case 5*) clear g Nonneg2.
       apply pad_injective_Case5; assumption. } }
  { clear g Nonneg1.
    remember (zlt ((BlockSize + Zlength l2) * 8) Int.modulus).
    destruct s; clear Heqs.
    { (*Case 5, symmetric version*)
       rewrite (Zmod_small ((BlockSize + Zlength l2) * 8)) in H. 2: split; assumption.
       symmetry. symmetry in H. symmetry in H0.
       apply pad_injective_Case5; assumption. }
    { clear Nonneg2 g.
      remember ((BlockSize + Zlength l1) * 8) as z1.
      remember ((BlockSize + Zlength l2) * 8) as z2.

      rewrite Zmod_eq in H. 2: apply Int.modulus_pos. remember (z1 / Int.modulus) as k1; clear Heqk1.
      rewrite Zmod_eq in H. 2: apply Int.modulus_pos. remember (z2 / Int.modulus) as k2; clear Heqk2.
      destruct (zeq k1 k2).
      { subst. clear -H.
        assert (Zlength l1 = Zlength l2). omega.
        repeat rewrite Zlength_correct in H0.
        rewrite <- (Nat2Z.id (length l1)).
        rewrite <- (Nat2Z.id (length l2)).
        rewrite H0. reflexivity. }
      { assert (length ((l1 ++ Byte.repr 128 :: nil) ++
                 list_repeat (Z.to_nat (- (BlockSize + Zlength l1 + 9) mod 64)) Byte.zero)
              = length ((l2 ++ Byte.repr 128 :: nil) ++
                 list_repeat (Z.to_nat (- (BlockSize + Zlength l2 + 9) mod 64)) Byte.zero)).
          rewrite H0; trivial.
        clear H0. repeat rewrite app_length in H1.
        repeat rewrite length_list_repeat in H1.
        rewrite (pad_injective_aux l2 l1 (k1-k2)) in H1.
          omega.
          rewrite Z.mul_sub_distr_r; omega.
          omega. } } } }
Qed.
(********************************************************************)

Lemma block_8 A (l:list A): length l = b -> InBlocks 8 l.
Proof.
  intros len. apply InBlocks_len. exists 64%nat. apply len.
Qed.

Lemma sha_splitandpad_app : forall (l m : Blist),
                         length l = b ->
                         sha_splitandpad (l ++ m) = l ++ sha_splitandpad_inc m.
Proof.
  intros l m len.
  unfold sha_splitandpad. unfold sha_splitandpad_inc.
  unfold pad. unfold pad_inc.

  rewrite -> bitsToBytes_app.
  rewrite -> Zlength_app.
  repeat rewrite -> bytesToBits_app.
  rewrite -> bits_bytes_bits_id.
  rewrite <- app_assoc.
  repeat f_equal.
  unfold b, c, p in *. simpl in *.

  * apply bitsToBytes_len. apply len.
  * apply bitsToBytes_len. apply len.
  * apply bitsToBytes_len. apply len.
  * apply block_8. apply len.
  * apply block_8. apply len.
Qed.

(*
Module SHAHF <: Hashfunction.
(* TODO use neater definition with conversion functions *)
(* TODO split out of HMAC_spec_pad *)

Definition c := (32 * 8)%nat.
Definition p := (32 * 8)%nat.
Definition b := (c + p)%nat.
Definition BlockSize := 64.

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

Lemma isbyteZ_pad_inc l (B:Forall isbyteZ l): Forall isbyteZ (pad_inc l).
Proof. unfold pad_inc.
  apply Forall_app. split. trivial.
  apply Forall_app. split. constructor. split; omega. trivial.
  apply Forall_app. split. apply Forall_list_repeat. split; omega.
  apply isbyte_intlist_to_Zlist.
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

(*******Injectivity of pad_inc*************************)

Lemma pad_injective_aux (l1 l2: list Z) k
     (K : k * Int.modulus + (BlockSize + Zlength l1) * 8 =
          (BlockSize + Zlength l2) * 8)
     (N : k <> 0):
     - (BlockSize + Zlength l2 + 9) mod 64 = - (BlockSize + Zlength l1 + 9) mod 64.
Proof. repeat rewrite <- Z.add_assoc. unfold BlockSize.
         repeat rewrite Z.opp_add_distr.
         rewrite (Zplus_mod (-(64))).
         assert (- (64) mod 64 = 0). reflexivity. rewrite H.
         rewrite (Zplus_mod (-(64))). rewrite H. simpl.
         repeat rewrite Zmod_mod.
         rewrite Zplus_mod. rewrite (Zplus_mod (- Zlength l1)).
         assert (Z12: - Zlength l2 mod 64 = - Zlength l1 mod 64).
         { clear H. repeat rewrite Z.mul_add_distr_r in K.
           assert (k * Int.modulus + Zlength l1 * 8 = Zlength l2 * 8). omega.
           clear K.
           assert (KK: k * (Int.modulus/8) + Zlength l1 = Zlength l2).
              rewrite <- (Zdiv_unique (k * Int.modulus + Zlength l1 * 8) 8 (Zlength l2) 0).
              2: rewrite Z.add_0_r; trivial. 2: omega.
              clear H. remember (Zlength l1) as z; clear Heqz.
              remember ((Int.modulus / 8)).
              assert (Int.modulus = z0 * 8). subst.
                rewrite <- max_unsigned_modulus, int_max_unsigned_eq. trivial.
              rewrite H; clear H Heqz0. rewrite Z.mul_assoc.
              rewrite (Z_div_plus_full_l (k*z0) 8 (z*8)). 2: omega.
              rewrite Z_div_mult_full. trivial. omega.
           rewrite <- KK; clear H KK.
           rewrite Z.opp_add_distr.
           rewrite Zplus_mod.
           assert (KM: - (k * (Int.modulus / 8)) mod 64 = 0).
             apply Zmod_unique with (a:=-k * 8388608). 2: omega. rewrite Zplus_0_r.
             rewrite <- max_unsigned_modulus, int_max_unsigned_eq. simpl.
             rewrite Zopp_mult_distr_l, <- Z.mul_assoc. reflexivity.
           rewrite KM. simpl. apply Z.mod_mod. omega.
         }
         rewrite Z12; trivial.
Qed.

Lemma pad_injective_Case5 l1 l2
  (H0 : (l1 ++ 128 :: nil) ++
        list_repeat (Z.to_nat (- (BlockSize + Zlength l1 + 9) mod 64)) 0 =
        (l2 ++ 128 :: nil) ++
        list_repeat (Z.to_nat (- (BlockSize + Zlength l2 + 9) mod 64)) 0)
  (H : (BlockSize + Zlength l1) * 8 =
       ((BlockSize + Zlength l2) * 8) mod Int.modulus)
  (Nonneg1 : 0 <= (BlockSize + Zlength l1) * 8)
  (l : (BlockSize + Zlength l1) * 8 < Int.modulus):
  length l1 = length l2.
Proof. symmetry in H.
       destruct (mod_exists _ _ _ H) as [k K].
       specialize Int.modulus_pos; intros; omega.
       destruct (zeq k 0).
         subst. clear - K.
         assert (Zlength l1 = Zlength l2). omega.
         repeat rewrite Zlength_correct in H.
         rewrite <- (Nat2Z.id (length l1)).
         rewrite <- (Nat2Z.id (length l2)).
         rewrite H. reflexivity.
       clear H.
       assert (length ((l1 ++ 128 :: nil) ++
                list_repeat (Z.to_nat (- (BlockSize + Zlength l1 + 9) mod 64)) 0)
             = length ((l2 ++ 128 :: nil) ++
                list_repeat (Z.to_nat (- (BlockSize + Zlength l2 + 9) mod 64)) 0)).
       rewrite H0; trivial.
       clear H0. repeat rewrite app_length in H.
       repeat rewrite length_list_repeat in H.
       clear - K n H.
       rewrite (pad_injective_aux l1 l2 k K n) in H. omega.
Qed.

Lemma pad_inc_injective: forall l1 l2, pad_inc l1 = pad_inc l2 -> l1=l2.
Proof. intros.
remember (beq_nat (length l1) (length l2)) as d.
destruct d.
{ apply beq_nat_eq in Heqd.
  unfold pad_inc in H. repeat rewrite Zlength_correct in H.
  rewrite <- Heqd in H.
  eapply app_inv_tail. apply H. }
{ symmetry in Heqd; apply beq_nat_false in Heqd.
  unfold pad_inc in H.
  repeat rewrite app_assoc in H.
  destruct (app_inv_length2 _ _ _ _ H); clear H. reflexivity.
  apply pure_lemmas.intlist_to_Zlist_inj in H1.
  apply cons_inv in H1. destruct H1 as [_ Y].
  apply cons_inv in Y. destruct Y as [Y _].
  assert (Int.unsigned (Int.repr ((BlockSize + Zlength l1) * 8)) = Int.unsigned (Int.repr ((BlockSize + Zlength l2) * 8))).
    rewrite Y; trivial.
  elim Heqd; clear Heqd Y.
  repeat rewrite Int.unsigned_repr_eq in H.
  assert (Nonneg1: 0 <= (BlockSize + Zlength l1) * 8).
    specialize (Zlength_nonneg l1). intros; unfold BlockSize; omega.
  assert (Nonneg2: 0 <= (BlockSize + Zlength l2) * 8).
    specialize (Zlength_nonneg l2). intros; unfold BlockSize; omega.
  remember (zlt ((BlockSize + Zlength l1) * 8) Int.modulus).
  destruct s; clear Heqs.
  {  rewrite Zmod_small in H. 2: split; assumption.
     remember (zlt ((BlockSize + Zlength l2) * 8) Int.modulus).
     destruct s; clear Heqs.
     { (*Case 3*)
       rewrite Zmod_small in H. 2: split; assumption.
       clear - H.
       assert (Zlength l1 = Zlength l2). omega.
       repeat rewrite Zlength_correct in H0.
       rewrite <- (Nat2Z.id (length l1)).
       rewrite <- (Nat2Z.id (length l2)).
       rewrite H0. reflexivity. }
     { (*Case 5*) clear g Nonneg2.
       apply pad_injective_Case5; assumption. } }
  { clear g Nonneg1.
    remember (zlt ((BlockSize + Zlength l2) * 8) Int.modulus).
    destruct s; clear Heqs.
    { (*Case 5, symmetric version*)
       rewrite (Zmod_small ((BlockSize + Zlength l2) * 8)) in H. 2: split; assumption.
       symmetry. symmetry in H. symmetry in H0.
       apply pad_injective_Case5; assumption. }
    { clear Nonneg2 g.
      remember ((BlockSize + Zlength l1) * 8) as z1.
      remember ((BlockSize + Zlength l2) * 8) as z2.

      rewrite Zmod_eq in H. 2: apply Int.modulus_pos. remember (z1 / Int.modulus) as k1; clear Heqk1.
      rewrite Zmod_eq in H. 2: apply Int.modulus_pos. remember (z2 / Int.modulus) as k2; clear Heqk2.
      destruct (zeq k1 k2).
      { subst. clear -H.
        assert (Zlength l1 = Zlength l2). omega.
        repeat rewrite Zlength_correct in H0.
        rewrite <- (Nat2Z.id (length l1)).
        rewrite <- (Nat2Z.id (length l2)).
        rewrite H0. reflexivity. }
      { assert (length ((l1 ++ 128 :: nil) ++
                 list_repeat (Z.to_nat (- (BlockSize + Zlength l1 + 9) mod 64)) 0)
              = length ((l2 ++ 128 :: nil) ++
                 list_repeat (Z.to_nat (- (BlockSize + Zlength l2 + 9) mod 64)) 0)).
          rewrite H0; trivial.
        clear H0. repeat rewrite app_length in H1.
        repeat rewrite length_list_repeat in H1.
        rewrite (pad_injective_aux l2 l1 (k1-k2)) in H1.
          omega.
          rewrite Z.mul_sub_distr_r; omega.
          omega. } } } }
Qed.
(********************************************************************)

Lemma block_8 A (l:list A): length l = b -> InBlocks 8 l.
Proof.
  intros len. apply InBlocks_len. exists 64%nat. apply len.
Qed.




Lemma xor_equiv_byte: forall xpad XPAD k K, isbyteZ XPAD ->
                          bytes_bits_lists xpad (HP.HMAC_SHA256.sixtyfour XPAD) ->
                          bytes_bits_lists k (map Byte.unsigned K) ->
bytes_bits_lists (BLxor k xpad) (HP.HMAC_SHA256.mkArgZ K (Byte.repr XPAD)).
Proof. intros.  apply inner_general_mapByte; try assumption.
       rewrite <- SF_ByteRepr; trivial.
Qed.

  Definition hf_c := (32 * 8)%nat.
  Definition hf_p := (32 * 8)%nat.
  Definition hf_b := (hf_c + hf_p)%nat.
  Definition hf_iv := intsToBits SHA256.init_registers.
  Definition hf_h := sha_h.
(*  Definition hf_pad_inc := pad_inc.
  Definition hf_splitandpad_inc (msg : Blist) : Blist := bytesToBits (hf_pad_inc (bitsToBytes msg)).
  Definition hf_pad_inc_injective := pad_inc_injective.*)

  Definition hf_iv_length := sha_iv_length.
  Definition hf_h_length := sha_h_length.
  Definition hf_block_8 := block_8.
End SHAHF.
*)
