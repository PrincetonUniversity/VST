Require Import compcert.lib.Coqlib.
Require Import Bvector.
Require Import List.
Require Import compcert.lib.Integers.
Require Import BinNums.
Require Import sha.general_lemmas.
Require Import sha.ByteBitRelations.
Require Import sha.hmac_pure_lemmas.
Require Import sha.HMAC_common_defs.
Require Import sha.HMAC_spec_pad.
Require Import sha.HMAC_spec_concat.
Require Import sha.HMAC_spec_abstract.

Require Import fcf.Blist.

Lemma of_length_proof_irrel {A:Set} n (l: list A) M:
      Vector.to_list (@of_list_length _ n l M) = l.
Proof. destruct M. apply Vector.to_list_of_list_opp. Qed.

Require Import sha.HMAC_functional_prog. (*Just for HMAC_FUN*)

Module Type EQUIV_Inst (HF:HP.HASH_FUNCTION).

(*Section EQUIV.*)
  Parameter c:nat.
  Parameter C: NPeano.Nat.divide 8 c.
  Parameter p:nat.
  Definition b := (c+p)%nat.
  Parameter B: (0<b)%nat.
  Parameter BS: (HF.BlockSize * 8)%nat = b.

  Parameter h: Blist -> Blist -> Blist. (*To be instantiated to sha_h*)
  Parameter h_length
     : forall iv blk : list bool,
       length iv = c -> length blk = b -> length (h iv blk) = c. (*instantiation: sha_h_length*)

  Parameter ir: list int.
(*  Definition iv: Blist := convert ir. (*sha_iv*)*)
  Parameter iv_length: length (convert ir) = c. (*sha_iv_length*)
  (*Definition iv_v : Bvector c := of_list_length _ iv_length. (*Vector.of_list iv.*)*)
  Parameter iv_v : Bvector c.
  Parameter iv_eq : convert ir = Vector.to_list iv_v.
(*  Proof. unfold iv_v. rewrite of_length_proof_irrel. trivial.
  Qed.*)

  Parameter fpad_v : Bvector c -> Bvector p.
  Parameter fpad : Blist -> Blist.
  Parameter fpad_length: forall msg, length msg = c -> length (fpad msg) = p.
  Parameter fpad_eq: forall v l, l = Vector.to_list v ->
                    fpad l = Vector.to_list (fpad_v v).

  Parameter splitAndPad : Blist -> Blist.
  Parameter splitAndPad_v : Blist -> list (Bvector b).


  Parameter splitandpad_blocks: Blist -> list Blist.

  Parameter sap_fpad: forall l m, length l = b ->
                     InBlocks 8 m ->
                     splitAndPad (l ++ m) = l ++ HMAC_Concat.app_fpad fpad m.

  Parameter shasplitandpad_blocks_b:
           forall m, Forall (fun x => length x = b) (splitandpad_blocks m).

  Definition sap' (m:Blist):= concat (splitandpad_blocks m). (*plays role of sha_splitandpad_inc*)

  Parameter sap_app : forall (l m : Blist),
                         length l = b ->
                         splitAndPad (l ++ m) = l ++ sap' m.

  Parameter sap'_InBlocks: forall m, InBlocks b (sap' m).

  Parameter hashblock : list int -> list int -> list int.
  Parameter HHB : h =
      (fun rgs bl : Blist =>
       intsToBits (hashblock (bitsToInts rgs) (bitsToInts bl))).

  Parameter hashblocks: list int -> list int -> list int.
  Parameter d:nat.

  Parameter HBS_eq : forall r msg : list int,
         hashblocks r msg =
         match msg with
         | List.nil => r
         | _ :: _ => hashblocks (hashblock r (firstn d msg)) (skipn d msg)
         end.
  Parameter D: (d * 32)%nat = b.

  Parameter gap:list byte -> list int.
  Parameter GAP: forall bits, NPeano.Nat.divide d (length (gap (bitsToBytes bits))).
  Parameter sap_gap: splitAndPad = fun bits => bytesToBits (intlist_to_bytelist (gap (bitsToBytes bits))).

  Parameter HASH: forall m, HF.Hash m = intlist_to_bytelist (hashblocks ir (gap m)).

  Parameter FOLD_HB_eq: forall l ls, length l = (c + p)%nat ->
     Forall (fun x => length x = (c + p)%nat) ls ->
     fold_left h (l :: ls) (Vector.to_list iv_v) =
          hash_blocks_bits (HMAC_spec_concat.HMAC_Concat.b c p) B h
          (Vector.to_list iv_v) (l ++ concat ls).

  Parameter length_splitandpad_inner: forall m,
    Forall2
     (fun (bv : Vector.t bool b) (bl : list bool) => bl = Vector.to_list bv)
     (splitAndPad_v m) (splitandpad_blocks m).
End EQUIV_Inst.

Module HMAC_Equiv (HF:HP.HASH_FUNCTION) (EQ: EQUIV_Inst HF).
Module I<:INST.
  Definition shah : Blist -> Blist ->  Blist := EQ.h.
  Definition hashblock : list int -> list int -> list int :=EQ.hashblock.
  Definition HHB : shah =
      (fun rgs bl : Blist =>
       intsToBits (hashblock (bitsToInts rgs) (bitsToInts bl))) := EQ.HHB.
  Definition hashblocks: list int -> list int -> list int := EQ.hashblocks.
  Definition d:nat := EQ.d.

  Definition HBS_eq : forall r msg : list int,
         hashblocks r msg =
         match msg with
         | List.nil => r
         | _ :: _ => hashblocks (hashblock r (firstn d msg)) (skipn d msg)
         end := EQ.HBS_eq.
End I.

(*Module HM:= HP.HMAC_FUN HF.*)
Module PAD := HMAC_Pad HF I.

  Definition h_v (iv:Bvector EQ.c) (blk:Bvector EQ.b): Bvector EQ.c :=
    of_list_length _
       (EQ.h_length _ _ (VectorToList_length _ iv) (VectorToList_length _ blk)).

  Lemma h_eq : forall (block_v : Bvector EQ.b) (block_l : Blist)
               (HVL: block_l = Vector.to_list block_v)
               ivA ivB (IV: ivA = Vector.to_list ivB),
               EQ.h ivA block_l = Vector.to_list (h_v ivB block_v).
  Proof. intros. unfold h_v, of_list_length.
    destruct (EQ.h_length (Vector.to_list ivB) (Vector.to_list block_v)
      (VectorToList_length EQ.c ivB) (VectorToList_length EQ.b block_v)).
    symmetry. subst. apply Vector.to_list_of_list_opp.
  Qed.

  Definition ipd := Byte.repr 54.
  Definition opd :=Byte.repr 92.

  Definition IPAD:=bytesToBits (PAD.HM.sixtyfour ipd).
  Definition OPAD:=bytesToBits (PAD.HM.sixtyfour opd).

  Lemma IL: length IPAD = EQ.b.
    unfold IPAD. rewrite bytesToBits_len, PAD.HM.length_SF, <- EQ.BS; trivial.
  Qed.
  Lemma OL: length OPAD = EQ.b.
    unfold OPAD. rewrite bytesToBits_len, PAD.HM.length_SF, <- EQ.BS; trivial.
  Qed.

  Definition ipad_v: Bvector EQ.b := of_list_length _ IL.
  Definition opad_v : Bvector EQ.b := of_list_length _ OL.
  Lemma OPADX:bytes_bits_lists (Vector.to_list opad_v) (PAD.HM.sixtyfour opd).
    apply bytes_bits_comp_ind.
      unfold PAD.HM.sixtyfour.
    unfold opad_v. rewrite of_length_proof_irrel. reflexivity.
  Qed.

  Lemma IPADX:bytes_bits_lists (Vector.to_list ipad_v) (PAD.HM.sixtyfour ipd).
    apply bytes_bits_comp_ind.
      unfold PAD.HM.sixtyfour.
    unfold ipad_v. rewrite of_length_proof_irrel. reflexivity.
  Qed.

Lemma BS_pos: (0< HF.BlockSize)%nat.
Proof.
  assert ((0 < HF.BlockSize * 8)%nat).
    rewrite EQ.BS. apply EQ.B.
  omega.
Qed.

  Lemma opad_ne_ipad : opad_v <> ipad_v.
  intros N.
  assert ((Vector.to_list ipad_v)  = bytesToBits (PAD.HM.sixtyfour ipd)  ).
    apply bits_bytes_ind_comp; trivial.
    apply IPADX.
  assert ((Vector.to_list opad_v)  = bytesToBits (PAD.HM.sixtyfour opd)  ).
    apply bits_bytes_ind_comp; trivial.
    apply OPADX.
  rewrite N, H in H0; clear N H.
  apply bytesToBits_injective in H0; trivial.
  unfold PAD.HM.sixtyfour in H0.
  apply list_repeat_injective in H0. inv H0.
  apply BS_pos.
Qed.

Lemma Equivalence (P : Blist -> Prop) (HP: forall msg, P msg -> NPeano.Nat.divide 8 (length msg))
      (kv : Bvector EQ.b) (m : HMAC_Abstract.Message P):
      Vector.to_list (HMAC_spec.HMAC h_v EQ.iv_v (HMAC_Abstract.wrappedSAP _ _ EQ.splitAndPad_v)
                      EQ.fpad_v opad_v ipad_v kv m) =
      bytesToBits (PAD.HM.HmacCore ipd opd
                     (bitsToBytes (HMAC_Abstract.Message2Blist m))
                     (bitsToBytes (Vector.to_list kv))).
Proof.
  assert (LK : length (Vector.to_list kv) = EQ.b).
    { apply VectorToList_length. }
  erewrite <- HMAC_Abstract.HMAC_abstract_list; try reflexivity.
  2: apply h_eq.
  2: apply EQ.fpad_eq.
  2: apply EQ.length_splitandpad_inner.
  erewrite HMAC_spec_list.HMAC_List.HMAC_list_concat with (B:=EQ.B)(sap':=EQ.sap').
  2: apply EQ.fpad_length.
  2: apply EQ.shasplitandpad_blocks_b.
  2: reflexivity.
  2: apply EQ.h_length.
  2: apply VectorToList_length.
  2: apply VectorToList_length.
  2: apply VectorToList_length.
  2: apply EQ.FOLD_HB_eq.
  2: apply LK.

  erewrite <- HMAC_spec_concat.HMAC_Concat.HMAC_concat_pad.
  2: apply EQ.C.
  5: apply EQ.h_length.
  5: apply VectorToList_length.
  5: apply VectorToList_length.
  5: apply VectorToList_length.
  5: apply VectorToList_length.
  2: apply EQ.sap_app.
  2: apply EQ.sap_fpad.
  2: apply EQ.sap'_InBlocks.
  rewrite <- EQ.iv_eq.
  apply bits_bytes_ind_comp.
  eapply (PAD.HMAC_pad_concrete' _ _ EQ.B EQ.BS EQ.D EQ.ir _ EQ.GAP EQ.sap_gap EQ.HASH).
            erewrite bitsToBytes_len_gen. reflexivity.
            rewrite LK. rewrite EQ.BS; trivial.
            apply bytes_bits_comp_ind.
              rewrite bits_bytes_bits_id; trivial.
              apply InBlocks_len. rewrite LK, <- EQ.BS. eexists; reflexivity.
    apply bytes_bits_comp_ind.
              rewrite bits_bytes_bits_id; trivial.
              apply InBlocks_len. destruct m. simpl. apply HP. assumption.
    apply OPADX. apply IPADX. (*
    apply bytes_bits_comp_ind.
             unfold PAD.HM.sixtyfour. apply Forall_list_repeat. apply EQ.isbyteZ_Ipad.
             unfold opad_v. rewrite of_length_proof_irrel. reflexivity.
    apply bytes_bits_comp_ind.
             unfold PAD.HM.sixtyfour. apply Forall_list_repeat. apply EQ.isbyteZ_Ipad.
             unfold ipad_v. rewrite of_length_proof_irrel. reflexivity.*)
Qed.
   (*

Lemma opad_length: length (bytesToBits (HP.HMAC_SHA256.sixtyfour
                       (Integers.Byte.unsigned HP.Opad))) = b.
Proof. rewrite bytesToBits_len, length_SF. reflexivity. Qed.

Definition opad_v: Bvector b := of_list_length _ opad_length.

Lemma ipad_length: length (bytesToBits (HP.HMAC_SHA256.sixtyfour
                       (Integers.Byte.unsigned HP.Ipad))) = b.
Proof. rewrite bytesToBits_len, length_SF. reflexivity. Qed.

Definition ipad_v: Bvector b := of_list_length _ ipad_length.

Lemma Equivalence (P : Blist -> Prop) (HP: forall msg, P msg -> NPeano.divide 8 (length msg))
      (kv : Bvector b) (m : HMAC_Abstract.Message P):
      Vector.to_list (HMAC_spec.HMAC h_v iv_v (HMAC_Abstract.wrappedSAP _ _ splitAndPad_v)
                      fpad_v opad_v ipad_v kv m) =
      bytesToBits (HP.HMAC_SHA256.HmacCore (Integers.Byte.repr 54) (Integers.Byte.repr 92)
                              (bitsToBytes (HMAC_Abstract.Message2Blist m))
                              (map Integers.Byte.repr (bitsToBytes (Vector.to_list kv)))).
Proof.
  assert (LK : length (Vector.to_list kv) = b).
    { apply VectorToList_length. }
  erewrite <- HMAC_Abstract.HMAC_abstract_list; try reflexivity.
  2: apply h_eq.
  2: apply fpad_eq.
  2: apply length_splitandpad_inner.
  rewrite HMAC256_spec_list.HMAC_list_concat_sap_instantiated; trivial.
  2: apply sha_h_length.
  2: apply VectorToList_length.
  2: apply VectorToList_length.
  2: apply fold_hash_blocks_eq.
(*  rewrite <- sha_splitandpad_inc_eq.*)
  rewrite <- HMAC256_spec_concat.HMAC_concat_pad_sap_instantiated; trivial.
  2: apply sha_h_length.
  2: apply VectorToList_length.
  2: apply VectorToList_length.
  eapply HMAC256_spec_pad.HMAC_pad_concrete'.

  split; omega.
  split; omega.

  (* key length *)
  { rewrite map_length, bitsToBytes_len_gen with (n:=64%nat).
    reflexivity.
    rewrite LK; reflexivity. }

  (* key length *)
  { rewrite Zlength_map, bitsToBytes_len. reflexivity. apply LK. }

  (* TODO: maybe replace bytes_bits_lists with bytesToBits? Since bytes_bits_comp_ind
     is used a lot *)

  (* key *)
  { rewrite map_unsigned_Brepr_isbyte.
      apply bytes_bits_comp_ind.
      eapply bitsToBytes_isbyteZ; reflexivity.
      rewrite  bits_bytes_bits_id; trivial.
      apply block_8. assumption.
      eapply bitsToBytes_isbyteZ. reflexivity. }

  (* uses fact that message is in blocks of 8 *)
  { apply bytes_bits_comp_ind.
    eapply bitsToBytes_isbyteZ; reflexivity.
    rewrite bits_bytes_bits_id; trivial.
    apply InBlocks_len.
    apply HP. destruct m. simpl; trivial. }

  (* opad *)
  { apply bytes_bits_comp_ind.
    apply Forall_list_repeat. unfold HP.Opad. omega.
    apply of_length_proof_irrel. }

  (* ipad *)
  { apply bytes_bits_comp_ind.
    apply Forall_list_repeat. unfold HP.Ipad. omega.
    apply of_length_proof_irrel. }

Qed.*)
End HMAC_Equiv.