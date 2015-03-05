Require Import Integers.
Require Import Recdef.
Require Import List. Import ListNotations.
Require Import Arith.
Require Import Coqlib.
Require Import pure_lemmas.
Require Import SHA256.
Require Import hmac_pure_lemmas.
Require Import sha_padding_lemmas.
Require Import ByteBitRelations.
Require Import HMAC_functional_prog.
Require Import hmac_common_lemmas.

Definition Blist := list bool.

Definition concat {A : Type} (l : list (list A)) : list A :=
  flat_map id l.

(* Replacing splitVector *)
Definition splitList {A : Type} (n : nat) (l : list A) : (list A * list A) :=
  (firstn n l, skipn n l).

(* Replacing BVxor *)
Definition BLxor (xs : Blist) (ys : Blist) :=
  map (fun p => xorb (fst p) (snd p)) (combine xs ys).

Theorem xor_eq : forall (n : nat) (v1 v2 : Bvector.Bvector n),
                   BLxor (Vector.to_list v1) (Vector.to_list v2) = 
                   Vector.to_list (Bvector.BVxor n v1 v2).
Proof.
  eapply Vector.rect2.
  reflexivity.
  intros. simpl. rewrite (VectorToList_cons _ _ (xorb a b)).
   rewrite <- H. clear H. unfold BLxor. 
   rewrite VectorToList_combine. reflexivity.
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
