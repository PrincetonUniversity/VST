Require Import Coqlib.
Require Import Bvector.
Require Import List.
Require Import Integers.
Require Import BinNums.
(*Require Import Arith.*)
Require Import common_lemmas.
Require Import HMAC_functional_prog.
Require Import sha_padding_lemmas.
Require Import ByteBitRelations.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.
Require Import HMAC_spec_list.
Require Import HMAC_spec_abstract.
Require Import HMAC_common_defs.

Require Import Blist.

Lemma of_length_proof_irrel n a: forall M, 
      Vector.to_list (@of_list_length bool n a M) = a.
Proof. intros.
  unfold of_list_length. destruct M. apply Vector.to_list_of_list_opp. 
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
                rewrite <- initialize.max_unsigned_modulus.
                rewrite client_lemmas.int_max_unsigned_eq. simpl. trivial.
              rewrite H; clear H Heqz0. rewrite Z.mul_assoc.
              rewrite (Z_div_plus_full_l (k*z0) 8 (z*8)). 2: omega. 
              rewrite Z_div_mult_full. trivial. omega.
           rewrite <- KK; clear H KK.
           rewrite Z.opp_add_distr.  
           rewrite Zplus_mod.
           assert (KM: - (k * (Int.modulus / 8)) mod 64 = 0).
             apply Zmod_unique with (a:=-k * 8388608). 2: omega. rewrite Zplus_0_r.
             rewrite <- initialize.max_unsigned_modulus.
             rewrite client_lemmas.int_max_unsigned_eq. simpl.
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
remember (beq_nat (length l1) (length l2)).
destruct b.
{ apply beq_nat_eq in Heqb. 
  unfold pad_inc in H. repeat rewrite Zlength_correct in H.
  rewrite <- Heqb in H.
  eapply app_inv_tail. apply H. }
{ symmetry in Heqb; apply beq_nat_false in Heqb.
  unfold pad_inc in H.
  repeat rewrite app_assoc in H.
  destruct (app_inv_length2 _ _ _ _ H); clear H. reflexivity.
  apply pure_lemmas.intlist_to_Zlist_inj in H1.
  apply cons_inv in H1. destruct H1 as [_ Y].
  apply cons_inv in Y. destruct Y as [Y _].
  assert (Int.unsigned (Int.repr ((BlockSize + Zlength l1) * 8)) = Int.unsigned (Int.repr ((BlockSize + Zlength l2) * 8))).
    rewrite Y; trivial.
  elim Heqb; clear Heqb Y.
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

Section EQUIV.

Definition h_v (iv:Bvector c) (blk:Bvector b): Bvector c :=
  of_list_length _
   (sha_h_length (Vector.to_list iv) (Vector.to_list blk) (VectorToList_length _)
               (VectorToList_length _)).

Lemma h_eq : forall (block_v : Bvector b) (block_l : Blist)
               (HVL: block_l = Vector.to_list block_v)
               ivA ivB (IV: ivA = Vector.to_list ivB),
               sha_h ivA block_l = Vector.to_list (h_v ivB block_v).
Proof. intros. unfold h_v, of_list_length. 
  destruct (sha_h_length (Vector.to_list ivB) (Vector.to_list block_v)
      (VectorToList_length ivB) (VectorToList_length block_v)). 
  symmetry. subst. apply Vector.to_list_of_list_opp.
Qed. 

Definition iv_v : Bvector c := Vector.of_list sha_iv.

Lemma iv_eq : sha_iv = Vector.to_list iv_v.
Proof. unfold iv_v. 
  rewrite <- Vector.to_list_of_list_opp.
  reflexivity.
Qed.

Lemma opad_length:
  length (bytesToBits (HP.HMAC_SHA256.sixtyfour
                       (Integers.Byte.unsigned HP.Opad))) = b.
Proof. rewrite bytesToBits_len, length_SF. reflexivity. Qed. 
 
Definition opad_v: Bvector b := of_list_length _ opad_length.

Lemma ipad_length:
  length (bytesToBits (HP.HMAC_SHA256.sixtyfour
                       (Integers.Byte.unsigned HP.Ipad))) = b.
Proof. rewrite bytesToBits_len, length_SF. reflexivity. Qed. 
 
Definition ipad_v: Bvector b := of_list_length _ ipad_length.

Lemma fpad_length (v:Bvector c): length (fpad (Vector.to_list v)) = p.
Proof. unfold fpad, fpad_inner. rewrite bytesToBits_len.
  repeat rewrite app_length. rewrite length_list_repeat, pure_lemmas.length_intlist_to_Zlist.
  rewrite (mult_comm 4), plus_comm, Zlength_correct.
  rewrite bitsToBytes_len_gen with (n:=32%nat).
    reflexivity.
    apply VectorToList_length.
Qed. 

Definition fpad_v (v:Bvector c): Bvector p := of_list_length _ (fpad_length v).
  
Lemma fpad_eq : forall (v : Bvector c) (l : Blist),
                  l = Vector.to_list v ->
                  fpad l = Vector.to_list (fpad_v v).
Proof. intros. unfold fpad_v, of_list_length. 
  destruct (fpad_length v).
  rewrite Vector.to_list_of_list_opp.
  subst; reflexivity.
Qed.

Fixpoint splitAndPad_aux (m:list Blist) (M: Forall (fun x => length x = 512%nat) m): 
           list (Bvector b) :=
(match m as l return (Forall (fun x => length x = 512%nat) l) -> list (Bvector b) with
  nil => fun F => nil
|  cons h t => fun F => cons (of_list_length h (Forall_inv F)) 
                    (splitAndPad_aux t (Forall_tl _ _ _ _ F))
 end) M.

Lemma splitAndPad_aux_consD h t M: 
      splitAndPad_aux (cons h t) M
      = (of_list_length h (Forall_inv M)) 
         :: (splitAndPad_aux t (Forall_tl _ _ _ _ M)).
Proof. reflexivity. Qed. 

Lemma splitAndPad_aux_nil m M: m=nil -> splitAndPad_aux m M= nil.
Proof. intros; subst. reflexivity. Qed.

Lemma length_splitandpad_inner_aux: forall ssm pf,
  Forall2
  (fun (bv : Vector.t bool b) (bl : list bool) => bl = Vector.to_list bv)
  (splitAndPad_aux (toBlocks ssm) pf)
  (toBlocks ssm).
Proof. 
  intros ssm. remember (toBlocks ssm). generalize dependent ssm.
  induction l.
  { simpl; intros. constructor. }
  { intros. rewrite toBlocks_equation in Heql.
    destruct ssm. discriminate.
    remember ( Compare_dec.leb (length (b :: ssm)) 511) as d.
    destruct d. exfalso. 
           rewrite Heql in pf. apply Forall_inv in pf.  clear Heql. 
           rewrite firstn_length in pf.
           symmetry in Heqd. apply leb_complete in Heqd. 
           eapply NPeano.Nat.min_l_iff in pf. omega.
    rewrite splitAndPad_aux_consD.
    constructor.
      rewrite of_length_proof_irrel. trivial.
    eapply (IHl (skipn 512 (b :: ssm))).
      remember (firstn 512 (b :: ssm)) as zz.
      remember (toBlocks (skipn 512 (b :: ssm))) as yy.
      clear - Heql. inversion Heql. trivial. }
Qed.

Definition splitAndPad_v (m: Blist): list (Bvector b).
  apply (splitAndPad_aux (sha_splitandpad_blocks m)).
  apply InBlocks_Forall_512. apply sha_splitandpad_inc_InBlocks.
Defined.

Lemma splitAndPad_nil: exists pf,
  splitAndPad_v nil = 
  cons (@of_list_length bool 512 (sha_splitandpad_inc nil) pf) nil. 
Proof. unfold splitAndPad_v, sha_splitandpad_blocks.
  remember (InBlocks_Forall_512 (sha_splitandpad_inc_InBlocks nil)). clear Heqf.
  remember (toBlocks (sha_splitandpad_inc nil)).
  rewrite toBlocks_equation in Heql.
  remember (sha_splitandpad_inc nil) as m.
  destruct m. exfalso. clear Heql f l.
    unfold sha_splitandpad_inc in Heqm. 
    assert (@length bool nil = length (bytesToBits (pad_inc (bitsToBytes nil)))).
      rewrite <- Heqm; trivial.
    simpl in H; clear Heqm. omega.
  rewrite leb_correct_conv in Heql.
    2: rewrite Heqm; simpl; omega.
  rewrite firstn_same in Heql.
    2: rewrite Heqm; simpl; omega.
  rewrite skipn_short in Heql.
    2: rewrite Heqm; simpl; omega.
  rewrite toBlocks_equation in Heql. subst l.
  simpl. eexists. reflexivity.
Qed.

Lemma length_splitandpad_inner m :
   Forall2
     (fun (bv : Vector.t bool b) (bl : list bool) => bl = Vector.to_list bv)
     (splitAndPad_v m) (sha_splitandpad_blocks m).
Proof. apply length_splitandpad_inner_aux. Qed.

(* Note implicit assumption that the key is of the right length
   is now OK, since we're comapring to HP.HMAC_SHA256.HmacCore, not HMAC. *)
Lemma Equivalence (P : Blist -> Prop) (HP: forall msg, P msg -> NPeano.divide 8 (length msg))
      (kv : Bvector b) (m : Message P):
      Vector.to_list (HMAC_spec.HMAC h_v iv_v (wrappedSAP splitAndPad_v)
                      fpad_v opad_v ipad_v kv m) = 
      bytesToBits (HP.HMAC_SHA256.HmacCore (Integers.Byte.repr 54) (Integers.Byte.repr 92)
                              (bitsToBytes (Message2Blist m))
                              (map Integers.Byte.repr (bitsToBytes (Vector.to_list kv)))).
Proof.
  (*intros kv msg LM*)
  assert (LK : length (Vector.to_list kv) = b).
    { apply VectorToList_length. }
  erewrite <- HMAC_eq; try reflexivity.
  2: apply fpad_eq.
  2: apply h_eq.
  2: apply length_splitandpad_inner.
  rewrite HMAC_spec_list.HMAC_list_concat; trivial.
  2: apply VectorToList_length.
  2: apply VectorToList_length.
  rewrite <- HMAC_spec_list.saP_eq.
  rewrite <- HMAC_spec_concat.HMAC_concat_pad; trivial.
  2: apply VectorToList_length.
  2: apply VectorToList_length.
(*  eapply bits_bytes_ind_comp.
    apply isbyte_hmac.*)
  eapply HMAC_spec_pad.HMAC_Pad.HMAC_Pad_Concrete_equiv'.

  split; omega.
  split; omega.

  (* key length *)
  { rewrite map_length. rewrite bitsToBytes_len_gen with (n:=64%nat). 
    reflexivity.
    rewrite LK; reflexivity. }

  (* key length *)
  { rewrite Zlength_map. rewrite bitsToBytes_len. reflexivity. apply LK. }

  (* TODO: maybe replace bytes_bits_lists with bytesToBits? Since bytes_bits_comp_ind
     is used a lot *)

  (* key *)
  { rewrite map_unsigned_Brepr_isbyte.
      apply bytes_bits_comp_ind. 
      eapply HMAC_spec_pad.HMAC_Pad.bitsToBytes_isbyteZ; reflexivity.
      rewrite  bits_bytes_bits_id; trivial.
      apply HMAC_spec_concat.block_8. assumption.
      eapply HMAC_spec_pad.HMAC_Pad.bitsToBytes_isbyteZ. reflexivity. }

  (* uses fact that message is in blocks of 8 *)
  { apply bytes_bits_comp_ind.
    eapply HMAC_spec_pad.HMAC_Pad.bitsToBytes_isbyteZ; reflexivity.
    rewrite bits_bytes_bits_id; trivial. 
    apply sha_padding_lemmas.InBlocks_len. 
    apply HP. destruct m. simpl; trivial. }

  (* opad *)
  { apply bytes_bits_comp_ind.
    apply pure_lemmas.Forall_list_repeat. unfold HP.Opad. omega.
    apply of_length_proof_irrel. }

  (* ipad *)
  { apply bytes_bits_comp_ind. 
    apply pure_lemmas.Forall_list_repeat. unfold HP.Ipad. omega.
    apply of_length_proof_irrel. }

Qed.
End EQUIV.
Print Assumptions Equivalence.