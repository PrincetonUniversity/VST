Set Implicit Arguments.

Require Import compcert.lib.Coqlib.
Require Import Coq.Program.Basics. (* for function composition: ∘ *)
Require Import List. Import ListNotations.
Require Import compcert.lib.Integers.
Require Import sha.general_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.ByteBitRelations.
Require Import sha.HMAC_common_defs.

Local Open Scope program_scope.

Section HMAC.
  Variable c:nat.
  Variable p:nat.
  Definition b := (c+p)%nat.
  Variable B: (0<b)%nat.

  (* The compression function *)
  Variable h : Blist -> Blist -> Blist.

  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Blist.

  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star k (m : Blist) :=
    hash_blocks_bits b B h k m.

  (* The composition of the keyed hash function with the IV. *)
  Definition hash_words := h_star iv.

  Variable splitAndPad : Blist -> Blist.

  Definition hash_words_padded : Blist -> Blist :=
    hash_words ∘ splitAndPad.

  (* constant-length padding. *)
  Variable fpad : Blist.

  Definition app_fpad (x : Blist) : Blist :=
    x ++ fpad.
  Definition h_star_pad k x :=
    app_fpad (h_star k x).

  (* The "two-key" version of GHMAC and HMAC. *)
  (* Concatenate (K xor opad) and (K xor ipad) *)
  Definition GHMAC_2K (k : Blist) m :=
    let (k_Out, k_In) := splitList b k in (* concat earlier, then split *)
      let h_in := (hash_words_padded (k_In ++ m)) in
        hash_words_padded (k_Out ++ h_in).

  Definition HMAC_2K (k : Blist) (m : Blist) :=
    (* GHMAC_2K k (splitAndPad m). *)
    GHMAC_2K k m.

  (* opad and ipad are constants defined in the HMAC spec. *)
  Variable opad ipad : Blist.

  Definition HMAC (k : Blist) :=
    HMAC_2K (BLxor k opad ++ BLxor k ipad).

  (*The following hypotheses and constructions from the abstract spec
    do not need to be enforced/repeated here

  Hypothesis splitAndPad_1_1 :
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 -> b1 = b2.

  Definition GNMAC k m :=
    let (k_Out, k_In) := splitList c k in
    h k_Out (h_star_pad k_In m).

  Definition GHMAC (k : Blist) :=
    GHMAC_2K (BLxor k opad ++ BLxor k ipad).
  *)
End HMAC.

Definition convert (l : list int) : list bool :=
  bytesToBits (intlist_to_bytelist l).

(* Front/back equivalence theorems *)

Lemma front_equiv b d (DB32: (d*32)%nat = b):
  forall (back : Blist) (BACK : list int) (front : Blist) (FRONT : list int),
    (length front)%nat = b ->
    (length FRONT)%nat = d ->
    front ++ back = convert (FRONT ++ BACK) ->
    front = convert FRONT.
Proof.
  intros back BACK front FRONT f_len F_len concat_eq.
  unfold convert in *.
  rewrite -> intlist_to_bytelist_app in concat_eq.
  rewrite -> bytesToBits_app in concat_eq.

  assert (back = skipn b (front ++ back)).
    rewrite skipn_exact; trivial.
  assert (bytesToBits (intlist_to_bytelist BACK) = skipn b (front ++ back)).
    rewrite concat_eq; clear concat_eq.
    rewrite skipn_exact; trivial.
    rewrite bytesToBits_len, length_intlist_to_bytelist, F_len. omega.
  rewrite H, H0 in concat_eq; clear H H0.
  eapply app_inv_tail. eassumption.
Qed.

Lemma back_equiv b d (DB32: (d*32)%nat = b):
  forall (back : Blist) (BACK : list int) (front : Blist) (FRONT : list int),
    (length front)%nat = b ->
    (length FRONT)%nat = d ->
    front ++ back = convert (FRONT ++ BACK) ->
    back = convert BACK.
Proof.
  intros back BACK front FRONT f_len F_len concat_eq.
  assert (front ++ back = convert (FRONT ++ BACK)) as concat_eq'. apply concat_eq.
  unfold convert in *.
  rewrite -> intlist_to_bytelist_app in concat_eq.
  rewrite -> bytesToBits_app in concat_eq.

  assert (front_eq : front = convert FRONT).
    pose proof front_equiv DB32 back BACK front FRONT.
    apply H.
    * assumption.
    * assumption.
    * apply concat_eq'.
    * rewrite -> front_eq in concat_eq.
      unfold convert in *.
      eapply app_inv_head. eassumption.
Qed.

Module Type INST.
Parameter shah : Blist -> Blist ->  Blist.
Parameter hashblock : list int -> list int -> list int.
Parameter HHB : shah =
      (fun rgs bl : Blist =>
       intsToBits (hashblock (bitsToInts rgs) (bitsToInts bl))).

Parameter hashblocks: list int -> list int -> list int.
Parameter d:nat.

Parameter HBS_eq : forall r msg : list int,
         hashblocks r msg =
         match msg with
         | [] => r
         | _ :: _ => hashblocks (hashblock r (firstn d msg)) (skipn d msg)
         end.
End INST.

Require Import sha.HMAC_functional_prog. (*Just for HMAC_FUN*)


Module HMAC_Pad (HF:HP.HASH_FUNCTION) (I:INST).
(*Module HMAC_Pad.Declare Module HF:HP.HASH_FUNCTION.*)
Module HM:= HP.HMAC_FUN HF.

(*Module PadConcrete (HF:HP.HASH_FUNCTION).*)

(*From hmac_common_lemmas TODO: Isolate*)
(*Lemma SF_ByteRepr x: isbyteZ x ->
                     HM.sixtyfour x =
                     map Byte.unsigned (HM.sixtyfour (Byte.repr x)).
Proof. intros. unfold HM.sixtyfour.
 rewrite map_list_repeat.
 rewrite Byte.unsigned_repr; trivial. destruct H.
 assert (BMU: Byte.max_unsigned = 255). reflexivity. omega.
Qed.
*)
(*From hmac_common_lemmas TODO: Isolate*)
(*Lemma length_SF {A} (a:A) :length (HM.sixtyfour a) = HF.BlockSize.
Proof. apply length_list_repeat. Qed.
*)
(*From SHaInstantiation -- TODO: Isolate*)
Lemma xor_equiv_byte: forall xpad XPAD k K, 
                          bytes_bits_lists xpad (HM.sixtyfour XPAD) ->
                          length K= HF.BlockSize ->
                          bytes_bits_lists k K ->
bytes_bits_lists (BLxor k xpad) (HM.mkArg K XPAD).
Proof. intros. apply inner_general_mapByte; try assumption.
Qed.
(*
Lemma isbyte_hmaccore ipad opad m k:
   Forall isbyteZ (HM.HmacCore (Byte.repr ipad) (Byte.repr opad) m k).
Proof. apply HF.Hash_isbyteZ. Qed. *)

(*Parameter *)
Lemma hash_block_equiv:
  forall (bits : Blist) (bytes : list byte)
         (regs : Blist) REGS,
    regs = bytesToBits (intlist_to_bytelist REGS) ->
    bits = bytesToBits bytes ->
    I.shah regs bits =
    bytesToBits (intlist_to_bytelist
                   (I.hashblock REGS (bytelist_to_intlist bytes))).
Proof.
  intros bits bytes regs REGS regs_eq input_eq.
  rewrite I.HHB. unfold intsToBits.
  apply f_equal.
  apply f_equal.
  rewrite -> regs_eq; clear regs_eq.
  rewrite -> input_eq; clear input_eq.
  unfold bitsToInts.
  rewrite bytes_bits_bytes_id.
  rewrite -> bytes_bits_bytes_id.
  rewrite -> intlist_to_bytelist_to_intlist.
  reflexivity.
Qed.

Lemma fold_equiv_blocks b (B:(0<b)%nat) (DB32: (I.d*32)%nat=b):
  forall (l : Blist) (acc : Blist)
         (L : list int) (ACC : list int),
      InBlocks b l ->
      InBlocks I.d L ->
      l = convert L ->
      acc = convert ACC ->
      hash_blocks_bits b B I.shah acc l = convert (I.hashblocks ACC L).
Proof.
  intros l acc L ACC bit_blocks bytes_blocks inputs_eq acc_eq.

  revert acc ACC L inputs_eq acc_eq bytes_blocks.
  induction bit_blocks; intros.
  *
    revert acc ACC inputs_eq acc_eq.
    induction bytes_blocks; intros.

    - rewrite I.HBS_eq.
      rewrite -> hash_blocks_bits_equation.
      apply acc_eq.
    - rewrite -> H0 in *.
      unfold convert in inputs_eq.
      destruct front.
      { simpl in H. rewrite <- H in *; omega. }
      { simpl in inputs_eq. inversion inputs_eq. }

  *
    revert front back full H H0 bit_blocks IHbit_blocks acc ACC
           inputs_eq acc_eq.
    induction bytes_blocks; intros.

    -
      simpl in inputs_eq.
      rewrite -> H0 in inputs_eq.
      unfold convert in inputs_eq.
      destruct front.
      { simpl in H. subst b. omega. }
      { simpl in inputs_eq. inversion inputs_eq. }

    - clear IHbytes_blocks. intros. rewrite I.HBS_eq.
      rewrite -> hash_blocks_bits_equation.
      repeat rewrite -> length_not_emp.
      rewrite -> H0.
      rewrite -> H2.
      rewrite firstn_exact; trivial.
      rewrite firstn_exact; trivial.
      rewrite skipn_exact; trivial.
      rewrite skipn_exact; trivial.
      apply IHbit_blocks; auto; clear  IHbit_blocks.
      + rewrite -> H0 in inputs_eq.
        rewrite -> H2 in inputs_eq.
        eapply (back_equiv DB32); eassumption.
      + rewrite (@hash_block_equiv front0 (intlist_to_bytelist front) acc ACC); auto.
        rewrite -> intlist_to_bytelist_to_intlist.
        reflexivity.
        { rewrite -> H0 in inputs_eq.
          rewrite -> H2 in inputs_eq.
          apply (front_equiv DB32 back0 back front0 front H1 H inputs_eq). }
     + rewrite -> H0. rewrite -> app_length. rewrite -> H. omega.
     + rewrite -> H2. rewrite -> app_length. rewrite -> H1. omega.
Qed.

Lemma equiv_pad shaiv shasplitandpad c p (B: (0< b c p)%nat) (DB32: (I.d*32 =b c p)%nat)
     ir (IVIR: shaiv = convert ir)
       gap (GAP: forall bits, NPeano.Nat.divide I.d (length (gap (bitsToBytes bits))))
       (sap_gap: forall bits, shasplitandpad bits = bytesToBits (intlist_to_bytelist (gap (bitsToBytes bits))))
       HASH
       (HSH: forall (m:list byte), HASH m = intlist_to_bytelist (I.hashblocks ir (gap m))):
       forall (bits : Blist) (bytes : list byte),
                    bytes_bits_lists bits bytes ->
                    bytes_bits_lists
                      (hash_words_padded c p B I.shah shaiv shasplitandpad bits)
                      (HASH bytes).
Proof.
  intros bits bytes input_eq.
  unfold hash_words_padded.
  change ((hash_words c p B I.shah shaiv ∘ shasplitandpad) bits) with
  (hash_words c p B I.shah shaiv (shasplitandpad bits)).
    unfold hash_words.
    unfold h_star. rewrite HSH; clear HSH.
    apply bytes_bits_comp_ind.
    { apply bytes_bits_ind_comp in input_eq.
        { subst bytes. rewrite sap_gap; clear sap_gap.
          eapply (fold_equiv_blocks B DB32).
          3: reflexivity.
          3: assumption.
          apply InBlocks_len. rewrite bytesToBits_len, length_intlist_to_bytelist.
             rewrite <- DB32. destruct (GAP bits). rewrite H. exists x.
             rewrite mult_comm, mult_assoc.
             assert ((8*4= 32)%nat) by omega. rewrite H0. rewrite mult_comm, <- mult_assoc. trivial.
          apply InBlocks_len. apply GAP.
        }
    }
Qed.

Theorem HMAC_pad_concrete splitandpad c p (B: (0< b c p)%nat) (BS: (HF.BlockSize * 8)%nat = b c p)
        (DB32: (I.d*32 =b c p)%nat)
         ir (*ie initial_regs*) gap (*ie generate_and_pad*)
         (GAP: forall bits, NPeano.Nat.divide I.d (length (gap (bitsToBytes bits))))
         (sap_gap: forall bits, splitandpad bits = bytesToBits (intlist_to_bytelist (gap (bitsToBytes bits))))
         (HSH: forall (m:list byte), HF.Hash m = intlist_to_bytelist (I.hashblocks ir (gap m)))
         (K : list byte) (M H : list byte) (OP IP : byte)
                          (k m h : Blist) (op ip : Blist):
  length K = HF.BlockSize ->
  bytes_bits_lists k K ->
  bytes_bits_lists m M ->
  bytes_bits_lists op (HM.sixtyfour OP) ->
  bytes_bits_lists ip (HM.sixtyfour IP) ->
  HMAC c p B I.shah (convert ir) splitandpad op ip k m = h ->
  HM.HmacCore IP OP M K = H ->
  bytes_bits_lists h H.
Proof.
  intros padded_key_len padded_keys_eq msgs_eq ops_eq ips_eq HMAC_abstract HMAC_concrete.
  rewrite <- HMAC_abstract. rewrite <- HMAC_concrete.
  unfold HMAC. unfold HM.HmacCore. unfold HM.OUTER. unfold HM.INNER.
  unfold HM.outerArg. unfold HM.innerArg.

  unfold HMAC_2K. unfold GHMAC_2K. rewrite -> split_append_id.

  { eapply equiv_pad.
    apply DB32. reflexivity. apply GAP. assumption. assumption.
    apply bytes_bits_lists_append.
    apply xor_equiv_byte; trivial.

    eapply equiv_pad.
    apply DB32. reflexivity. apply GAP. assumption. assumption.
    apply bytes_bits_lists_append.
    - apply xor_equiv_byte; trivial.
    - assumption. }

  { apply BLxor_length; erewrite bytes_bits_length; try eassumption.
         rewrite padded_key_len. apply BS.
         rewrite HM.length_SF. apply BS. }

  { apply BLxor_length; erewrite bytes_bits_length; try eassumption.
         rewrite padded_key_len. apply BS.
         rewrite HM.length_SF. apply BS. }
Qed.

Theorem HMAC_pad_concrete' splitandpad c p (B: (0< b c p)%nat) (BS: (HF.BlockSize * 8)%nat =b c p)
        (DB32: (I.d*32 =b c p)%nat)
         ir (*ie initial_regs*) gap (*ie generate_and_pad*)
         (GAP: forall bits, NPeano.Nat.divide I.d (length (gap (bitsToBytes bits))))
         (sap_gap: splitandpad = fun bits => bytesToBits (intlist_to_bytelist (gap (bitsToBytes bits))))
         (HSH: forall (m:list byte), HF.Hash m = intlist_to_bytelist (I.hashblocks ir (gap m)))
         (K : list byte) (M : list byte) (OP IP : byte)
                          (k m : Blist) (op ip : Blist):
  length K = HF.BlockSize ->
  bytes_bits_lists k K ->
  bytes_bits_lists m M ->
  bytes_bits_lists op (HM.sixtyfour OP) ->
  bytes_bits_lists ip (HM.sixtyfour IP) ->
  bytes_bits_lists
     (HMAC c p B I.shah (convert ir) splitandpad op ip k m)
     (HM.HmacCore IP OP M K).
Proof.
  intros. eapply HMAC_pad_concrete; try reflexivity.
  eassumption. eassumption. eassumption. eassumption. eassumption. eassumption.
  eassumption. eassumption. eassumption.  rewrite sap_gap. trivial.
Qed.

End HMAC_Pad.
(*
Lemma equiv_pad_SHA256 HASH c p B sap h iv: forall (bits : Blist) (bytes : list Z),
                    bytes_bits_lists bits bytes ->
                    bytes_bits_lists
                      (HMAC_Pad.hash_words_padded c p B h iv sap bits)
                      (HASH bytes).
Proof. intros.
  eapply HMAC_Pad.equiv_pad (*with (gap:=generate_and_pad')*).
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
*)
