Set Implicit Arguments.
Require Import Coqlib.
Require Import Integers.
Require Import general_lemmas.
Require Import ByteBitRelations.
Require Import HMAC_common_defs.
Require Import HMAC_spec_pad.

(*The sha-specific imports*)
Require Import SHA256. 
Require Import HMAC_functional_prog. 
Require Import hmac_common_lemmas.
Require Import sha_padding_lemmas. (*for pad_len_64_nat*)
Require Import ShaInstantiation.

(*Derived lemmas
Lemma front_equiv_SHA256 :
  forall (back : Blist) (BACK : list int) (front : Blist) (FRONT : list int),
    (length front)%nat = 512%nat ->
    (length FRONT)%nat = 16%nat ->
    front ++ back = convert (FRONT ++ BACK) ->
    front = convert FRONT.
Proof. intros. eapply front_equiv; try eassumption. omega. Qed. 

Lemma back_equiv_SHA256 :
  forall (back : Blist) (BACK : list int) (front : Blist) (FRONT : list int),
    (length front)%nat = 512%nat ->
    (length FRONT)%nat = 16%nat ->
    front ++ back = convert (FRONT ++ BACK) ->
    back = convert BACK.
Proof. intros. eapply back_equiv; try eassumption. omega. Qed. 
*)

(*Lemma fold_equiv_blocks_SHA256 :
  forall (l : Blist) (acc : Blist)
         (L : list int) (ACC : list int),
      InBlocks ShaInstantiation.b l ->
      InBlocks 16 L ->
      l = convert L ->
      acc = convert ACC ->
      hash_blocks_bits _ ShaInstantiation.B sha_h acc l = convert (hash_blocks ACC L).
Proof. intros. eapply fold_equiv_blocks.
  3: apply SHA256.hash_blocks_equation.
  reflexivity. reflexivity. trivial. trivial. trivial. trivial.
Qed.

Lemma splitandpad_equiv : forall (bits : Blist) (bytes : list Z),
                            bytes_bits_lists bits bytes ->
                            bytes_bits_lists
                              (sha_splitandpad bits)
                              (pad bytes).
Proof.
  intros bits bytes inputs_eq.
  unfold concat.
  unfold sha_splitandpad.
  specialize (bytesBitsLists_isbyteZ _ _ inputs_eq). intros isbyteZ_Bytes.

  apply bytes_bits_ind_comp in inputs_eq. 2: apply isbyteZ_Bytes.
  rewrite inputs_eq.
  apply bytes_bits_def_eq.
  rewrite <- inputs_eq. apply pad_isbyteZ. trivial.
Qed.
*)

Lemma gap_divide16 bits: NPeano.divide 16 (length (generate_and_pad' (bitsToBytes bits))).
Proof.
    unfold generate_and_pad'.
    destruct (pad_len_64_nat (bitsToBytes bits)).
     rewrite pure_lemmas.length_Zlist_to_intlist with (n:=(x*16)%nat). 
       exists x. trivial.
     rewrite H. unfold WORD. rewrite (mult_comm (Z.to_nat 4)). rewrite mult_comm.
        rewrite <- mult_assoc. reflexivity.
Qed.

Lemma equiv_pad_SHA256 : forall (bits : Blist) (bytes : list Z),
                    bytes_bits_lists bits bytes ->
                    bytes_bits_lists
                      (HMAC_Pad.hash_words_padded c p B sha_h sha_iv sha_splitandpad bits)
                      (HP.SHA256.Hash bytes).
Proof. intros.
  eapply HMAC_Pad.equiv_pad with (gap:=generate_and_pad').
  2: reflexivity.
  2: apply hash_blocks_equation.
  reflexivity. reflexivity.
  apply gap_divide16.
  intros. unfold sha_splitandpad. f_equal. 
    apply bytes_bits_ind_comp in H.
    { subst bytes. unfold generate_and_pad'.
      rewrite pure_lemmas.Zlist_to_intlist_to_Zlist; trivial.
        destruct (pad_len_64_nat (bitsToBytes bits0)). rewrite H.
          exists ((x*16)%nat). rewrite mult_comm, <- mult_assoc. reflexivity.
        apply pad_isbyteZ. eapply bitsToBytes_isbyteZ. reflexivity. }
    apply (bytesBitsLists_isbyteZ _ _ H).
  intros; unfold HP.SHA256.Hash.
    rewrite -> functional_prog.SHA_256'_eq. unfold SHA256.SHA_256.
    rewrite <- pad_compose_equal; reflexivity.
  assumption.
Qed.

(* Relates the HMAC padded spec to the HMAC functional program *)
Theorem HMAC_pad_concrete (K : list byte) (M H : list Z) (OP IP : Z)
                          (k m h : Blist) (op ip : Blist) (ipByte: isbyteZ IP) (opByte: isbyteZ OP):
  ((length K) * 8)%nat = (c + p)%nat ->
  Zlength K = Z.of_nat HP.SHA256.BlockSize ->
  bytes_bits_lists k (map Byte.unsigned K) ->
  bytes_bits_lists m M ->
  bytes_bits_lists op (HP.HMAC_SHA256.sixtyfour OP) ->
  bytes_bits_lists ip (HP.HMAC_SHA256.sixtyfour IP) ->
  HMAC_Pad.HMAC c p B sha_h sha_iv sha_splitandpad op ip k m = h ->
  HP.HMAC_SHA256.HmacCore (Byte.repr IP) (Byte.repr OP) M K = H ->
  bytes_bits_lists h H.
Proof.
  intros padded_key_len padded_key_len_byte padded_keys_eq msgs_eq ops_eq ips_eq.
  intros HMAC_abstract HMAC_concrete.

  intros.

  rewrite <- HMAC_abstract. rewrite <- HMAC_concrete.

  unfold HMAC_Pad.HMAC. unfold HP.HMAC_SHA256.HmacCore. unfold HP.HMAC_SHA256.OUTER. unfold HP.HMAC_SHA256.INNER.
  unfold HP.HMAC_SHA256.outerArg. unfold HP.HMAC_SHA256.innerArg.

  unfold HMAC_Pad.HMAC_2K. unfold HMAC_Pad.GHMAC_2K. rewrite -> split_append_id.

  { apply equiv_pad_SHA256.
    apply bytes_bits_lists_append.
    apply xor_equiv_byte; trivial. 

    apply equiv_pad_SHA256.
    apply bytes_bits_lists_append.
    - apply xor_equiv_byte; trivial.
    - assumption. }
  { apply BLxor_length; erewrite bytes_bits_length; try eassumption.
         rewrite map_length, padded_key_len. reflexivity.
         unfold HP.HMAC_SHA256.sixtyfour.
         rewrite -> length_list_repeat. reflexivity. }
  { apply BLxor_length; erewrite bytes_bits_length; try eassumption.
         rewrite map_length, padded_key_len. reflexivity.
         unfold HP.HMAC_SHA256.sixtyfour.
         rewrite -> length_list_repeat. reflexivity. }
Qed.

Theorem HMAC_pad_concrete' (K : list byte) (M : list Z) (OP IP : Z)
                           (k m : Blist) (op ip : Blist) (ipByte: isbyteZ IP) (opByte: isbyteZ OP):
  ((length K) * 8)%nat = (c + p)%nat ->
  Zlength K = Z.of_nat HP.SHA256.BlockSize ->
  bytes_bits_lists k (map Byte.unsigned K) ->
  bytes_bits_lists m M ->
  bytes_bits_lists op (HP.HMAC_SHA256.sixtyfour OP) ->
  bytes_bits_lists ip (HP.HMAC_SHA256.sixtyfour IP) ->
  HMAC_Pad.HMAC c p B sha_h sha_iv sha_splitandpad op ip k m = 
  bytesToBits (HP.HMAC_SHA256.HmacCore (Byte.repr IP) (Byte.repr OP) M K).
Proof. intros.  
  eapply bits_bytes_ind_comp.
    apply isbyte_hmaccore.
    eapply (HMAC_pad_concrete _ ipByte opByte); try reflexivity; trivial. 
Qed.
