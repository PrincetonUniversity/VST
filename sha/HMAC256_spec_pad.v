Set Implicit Arguments.
Require Import VST.msl.Axioms.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import sha.general_lemmas.
Require Import sha.ByteBitRelations.
Require Import sha.HMAC_common_defs.
Require Import sha.HMAC_spec_pad.

(*The sha-specific imports*)
Require Import sha.SHA256.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import sha.hmac_common_lemmas.
Require Import sha.sha_padding_lemmas. (*for pad_len_64_nat*)
Require Import sha.ShaInstantiation.

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
*)
Lemma splitandpad_equiv : forall (bits : Blist) (bytes : list byte),
                            bytes_bits_lists bits bytes ->
                            bytes_bits_lists
                              (sha_splitandpad bits)
                              (pad bytes).
Proof.
  intros bits bytes inputs_eq.
  unfold concat.
  unfold sha_splitandpad.

  apply bytes_bits_ind_comp in inputs_eq.
  rewrite inputs_eq.
  apply bytes_bits_def_eq.
Qed.

Lemma gap_divide16 bits: NPeano.Nat.divide 16 (length (generate_and_pad' (bitsToBytes bits))).
Proof.
    unfold generate_and_pad'.
    destruct (pad_len_64_nat (bitsToBytes bits)).
     rewrite pure_lemmas.length_bytelist_to_intlist with (n:=(x*16)%nat).
       exists x. trivial.
     rewrite H. unfold WORD. rewrite (mult_comm (Z.to_nat 4)). rewrite mult_comm.
        rewrite <- mult_assoc. reflexivity.
Qed.


Module I256 <: INST.
Definition shah : Blist -> Blist ->  Blist := sha_h.
Definition hashblock : list int -> list int -> list int := SHA256.hash_block.
Definition HHB : shah =
      (fun rgs bl : Blist =>
       intsToBits (hashblock (bitsToInts rgs) (bitsToInts bl))).
  reflexivity. Qed.
Definition hashblocks: list int -> list int -> list int := SHA256.hash_blocks.
Definition d:nat := 16%nat.
Definition HBS_eq : forall r msg : list int,
         hash_blocks r msg =
         match msg with
         | List.nil => r
         | _ :: _ => hash_blocks (hash_block r (firstn d msg)) (skipn d msg)
         end := hash_blocks_equation.
End I256.

Module PAD := HMAC_Pad SHA256 I256.

(* Relates the HMAC padded spec to the HMAC functional program *)
Theorem HMAC_pad_concrete (K : list byte) (M H : list byte) (OP IP : byte)
                          (k m h : Blist) (op ip : Blist):
  ((length K) * 8)%nat = (c + p)%nat ->
  bytes_bits_lists k K ->
  bytes_bits_lists m M ->
  bytes_bits_lists op (HMAC_SHA256.sixtyfour OP) ->
  bytes_bits_lists ip (HMAC_SHA256.sixtyfour IP) ->
  sha.HMAC_spec_pad.HMAC c p B sha_h sha_iv sha_splitandpad op ip k m = h ->
  HMAC_SHA256.HmacCore IP OP M K = H ->
  bytes_bits_lists h H.
Proof. intros.
assert (sha_splitandpad =
        (fun bits : Blist =>
   bytesToBits (intlist_to_bytelist (generate_and_pad (bitsToBytes bits))))).
  clear.
  apply extensionality. intros l. unfold sha_splitandpad.
  f_equal. rewrite <- pad_compose_equal. unfold generate_and_pad'.
  rewrite pure_lemmas.bytelist_to_intlist_to_bytelist. trivial.
  destruct (pad_len_64_nat (bitsToBytes l)). rewrite Zlength_correct, H. exists (Z.of_nat (x*16)). do 2 rewrite Nat2Z.inj_mul. rewrite Z.mul_comm, <- Z.mul_assoc.  reflexivity.
rewrite H7 in H5; clear H7.
eapply PAD.HMAC_pad_concrete with (c:=c)(p:=p)(IP:=IP)(OP:=OP)(B:=B)(ip:=ip)(op:=op)(m:=m)(K:=K)
  (ir:=SHA256.init_registers)(gap:=generate_and_pad); try reflexivity; try eassumption.
- intros. rewrite <- pad_compose_equal. apply gap_divide16.
- intros; unfold SHA256.Hash.
  rewrite functional_prog.SHA_256'_eq; reflexivity.
- unfold SHA256.BlockSize.
  unfold c, p in H0. omega.
Qed.

Theorem HMAC_pad_concrete' (K : list byte) (M : list byte) (OP IP : byte)
                           (k m : Blist) (op ip : Blist):
  ((length K) * 8)%nat = (c + p)%nat ->
  Zlength K = Z.of_nat SHA256.BlockSize ->
  bytes_bits_lists k K ->
  bytes_bits_lists m M ->
  bytes_bits_lists op (HMAC_SHA256.sixtyfour OP) ->
  bytes_bits_lists ip (HMAC_SHA256.sixtyfour IP) ->
  sha.HMAC_spec_pad.HMAC c p B sha_h sha_iv sha_splitandpad op ip k m =
  bytesToBits (HMAC_SHA256.HmacCore IP OP M K).
Proof. intros.
  eapply bits_bytes_ind_comp.
    eapply HMAC_pad_concrete; try reflexivity; trivial.
Qed.

(*earlier /additional proofs
Lemma equiv_pad_SHA256 : forall (bits : Blist) (bytes : list Z),
                    bytes_bits_lists bits bytes ->
                    bytes_bits_lists
                      (sha.HMAC_spec_pad.hash_words_padded c p B sha_h sha_iv sha_splitandpad bits)
                      (HP.SHA256.Hash bytes).
Proof. intros.
Locate equiv_pad.
  eapply sha.HMAC_spec_pad.equiv_pad with (gap:=generate_and_pad').
  reflexivity.
  apply hash_blocks_equation.
  reflexivity.
  reflexivity.
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

Theorem HMAC_pad_concrete (K : list byte) (M H : list Z) (OP IP : Z)
                          (k m h : Blist) (op ip : Blist) (ipByte: isbyteZ IP) (opByte: isbyteZ OP):
  ((length K) * 8)%nat = (c + p)%nat ->
  bytes_bits_lists k (map Byte.unsigned K) ->
  bytes_bits_lists m M ->
  bytes_bits_lists op (HP.HMAC_SHA256.sixtyfour OP) ->
  bytes_bits_lists ip (HP.HMAC_SHA256.sixtyfour IP) ->
  HMAC_Pad.HMAC c p B sha_h sha_iv sha_splitandpad op ip k m = h ->
  HP.HMAC_SHA256.HmacCore (Byte.repr IP) (Byte.repr OP) M K = H ->
  bytes_bits_lists h H.
Proof.
  intros padded_key_len padded_keys_eq msgs_eq ops_eq ips_eq.
  intros HMAC_abstract HMAC_concrete.

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
*)
