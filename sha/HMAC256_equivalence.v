Require Import compcert.lib.Coqlib.
Require Import Bvector.
Require Import List.
Require Import compcert.lib.Integers.
Require Import BinNums.
Require Import VST.msl.Axioms.
Require Import fcf.Blist.

Require Import sha.ByteBitRelations.
Require Import sha.hmac_pure_lemmas.
Require Import sha.general_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC_common_defs.
Require Import sha.HMAC_spec_abstract.
Require Import sha.HMAC_equivalence.

(*SHA256-specific Modules*)
Require Import sha.common_lemmas.
Require Import sha.HMAC256_functional_prog.
Require Import sha.sha_padding_lemmas.
Require Import sha.ShaInstantiation.
Require Import sha.hmac_common_lemmas.
Require Import sha.HMAC256_spec_pad.
Require Import sha.HMAC256_spec_concat.
Require Import sha.HMAC256_spec_list. (*for toBlocks*)

(*
Lemma of_length_proof_irrel {A:Set} n (l: list A) M:
      Vector.to_list (@of_list_length _ n l M) = l.
Proof. destruct M. apply Vector.to_list_of_list_opp. Qed.
*)
(*Section EQUIV.*)
(*Definition h_v (iv:Bvector c) (blk:Bvector b): Bvector c :=
  of_list_length _
   (sha_h_length _ _ (VectorToList_length _ iv) (VectorToList_length _ blk)).

Lemma h_eq : forall (block_v : Bvector b) (block_l : Blist)
               (HVL: block_l = Vector.to_list block_v)
               ivA ivB (IV: ivA = Vector.to_list ivB),
               sha_h ivA block_l = Vector.to_list (h_v ivB block_v).
Proof. intros. unfold h_v, of_list_length.
  destruct (sha_h_length (Vector.to_list ivB) (Vector.to_list block_v)
      (VectorToList_length c ivB) (VectorToList_length b block_v)).
  symmetry. subst. apply Vector.to_list_of_list_opp.
Qed.
*)

Definition iv_v : Bvector c := Vector.of_list sha_iv.

Lemma iv_eq : sha_iv = Vector.to_list iv_v.
Proof. unfold iv_v.
  rewrite <- Vector.to_list_of_list_opp.
  reflexivity.
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
*)
Lemma fpad_length (v:Bvector c): length (fpad (Vector.to_list v)) = p.
Proof. unfold fpad, fpad_inner. rewrite bytesToBits_len.
  repeat rewrite app_length. rewrite length_list_repeat, length_intlist_to_bytelist.
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
  remember (InBlocks_Forall_512 _ (sha_splitandpad_inc_InBlocks nil)). clear Heqf.
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
  rewrite sublist.firstn_same in Heql.
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

Lemma C: NPeano.Nat.divide 8 c.
  exists 32%nat. reflexivity.
Qed.

Module EQ256 <: EQUIV_Inst SHA256.
  Definition c := c.
  Definition C := C.
  Definition p := p.
  Definition b := b.
  Definition B := B.
  Definition BS: (SHA256.BlockSize * 8)%nat = b. reflexivity. Qed.
  Definition h := sha_h.
  Definition h_length := sha_h_length.
(*  Definition h_v := h_v.
  Definition h_eq := h_eq.*)
  Definition ir: list int := SHA256.init_registers.
(*  Definition iv:= sha_iv.*)
  Lemma iv_length: length (HMAC_spec_pad.convert ir) = c.
     apply sha_iv_length. Qed.
  (*Definition iv_length := sha_iv_length.*)
  Definition iv_v: Bvector c := iv_v. (*of_list_length _ iv_length.*)
  Lemma iv_eq: HMAC_spec_pad.convert ir  = Vector.to_list iv_v.
  Proof. reflexivity. Qed.
  (*
  Definition ipd:Z := 54.
  Definition opd:Z:=92.
  Lemma isbyteZ_Ipad: isbyteZ ipd.
    unfold ipd. split; omega. Qed.
  Lemma isbyteZ_Opad: isbyteZ opd.
    unfold opd. split; omega. Qed.*)
  Definition fpad_v := fpad_v.
  Definition fpad := fpad.
  Definition fpad_length msg: length msg = c -> length (fpad msg) = p.
  Proof. apply ShaInstantiation.fpad_length. Qed.
  Definition fpad_eq := fpad_eq.
  Definition splitAndPad := sha_splitandpad.
  Definition splitAndPad_v := splitAndPad_v.
  Definition splitandpad_blocks := sha_splitandpad_blocks.
  Definition sap_fpad:=sha_splitandpad_fpad.
  Definition shasplitandpad_blocks_b:= sha_splitandpad_blocks_512.
  Definition sap' m := concat (splitandpad_blocks m).
  Definition sap_app:forall (l m : Blist),
                         length l = b ->
                         splitAndPad (l ++ m) = l ++ sap' m.
  Proof. intros. rewrite sha_splitandpad_app; trivial.
    f_equal. unfold sap', splitandpad_blocks, sha_splitandpad_blocks.
    rewrite concat_toBlocks_id; trivial.
    apply sha_splitandpad_inc_InBlocks.
  Qed.
  Lemma sap'_InBlocks m: InBlocks b (sap' m).
    apply concat_InBlocks. apply sha_splitandpad_blocks_512. Qed.
  Definition hashblock : list int -> list int -> list int := SHA256.hash_block.
  Lemma HHB : h =
      (fun rgs bl : Blist =>
       intsToBits (hashblock (bitsToInts rgs) (bitsToInts bl))).
    reflexivity. Qed.

  Definition hashblocks: list int -> list int -> list int:= SHA256.hash_blocks.
  Definition d := 16%nat.

  Definition HBS_eq : forall r msg : list int,
         hashblocks r msg =
         match msg with
         | List.nil => r
         | _ :: _ => hashblocks (hashblock r (firstn d msg)) (skipn d msg)
         end := SHA256.hash_blocks_equation.
  Lemma D: (d * 32)%nat = b. reflexivity. Qed.

  Definition gap:list byte -> list int := SHA256.generate_and_pad.
  Lemma GAP: forall bits, NPeano.Nat.divide d (length (gap (bitsToBytes bits))).
    intros. rewrite <- pad_compose_equal. apply gap_divide16. Qed.

  Lemma sap_gap: splitAndPad = fun bits => bytesToBits (intlist_to_bytelist (gap (bitsToBytes bits))).
  Proof. apply extensionality. intros l. unfold splitAndPad, sha_splitandpad.
    f_equal. rewrite <- pad_compose_equal. unfold generate_and_pad'.
    rewrite pure_lemmas.bytelist_to_intlist_to_bytelist. trivial.
    destruct (pad_len_64_nat (bitsToBytes l)). rewrite Zlength_correct, H. exists (Z.of_nat(x*16)). do 2 rewrite Nat2Z.inj_mul. rewrite Z.mul_comm, <- Z.mul_assoc. reflexivity.
  Qed.

  Lemma HASH m: SHA256.Hash m = intlist_to_bytelist (hashblocks ir (gap m)).
     unfold SHA256.Hash.
     rewrite functional_prog.SHA_256'_eq; reflexivity.
  Qed.

  Lemma FOLD_HB_eq: forall l ls, length l = (c + p)%nat ->
     Forall (fun x => length x = (c + p)%nat) ls ->
     fold_left h (l :: ls) (Vector.to_list iv_v) =
          hash_blocks_bits (HMAC_spec_concat.HMAC_Concat.b c p) B h
          (Vector.to_list iv_v) (l ++ concat ls).
  Proof. intros.
     assert (SH: sha_iv = Vector.to_list iv_v). rewrite <- iv_eq; trivial.
     rewrite <- SH; apply (fold_hash_blocks_eq _ _ H H0).
  Qed.

  Lemma length_splitandpad_inner m:
    Forall2
     (fun (bv : Vector.t bool b) (bl : list bool) => bl = Vector.to_list bv)
     (splitAndPad_v m) (splitandpad_blocks m).
  Proof. apply length_splitandpad_inner. Qed.

End EQ256.

Module EQ := HMAC_Equiv SHA256 EQ256.

(* Note we're comparing to HP.HMAC_SHA256.HmacCore, not HMAC. *)
Lemma Equivalence (P : Blist -> Prop) (HP: forall msg, P msg -> NPeano.Nat.divide 8 (length msg))
      (kv : Bvector b) (m : HMAC_Abstract.Message P):
      Vector.to_list (HMAC_spec.HMAC EQ.h_v iv_v (HMAC_Abstract.wrappedSAP _ _ splitAndPad_v)
                      fpad_v EQ.opad_v EQ.ipad_v kv m) =
      bytesToBits (HMAC_SHA256.HmacCore EQ.ipd EQ.opd
                              (bitsToBytes (HMAC_Abstract.Message2Blist m))
                               (bitsToBytes (Vector.to_list kv))).
Proof.
  specialize (EQ.Equivalence _ HP kv m); intros.
  unfold EQ.h_v in H.
  unfold EQ256.c, EQ256.p, EQ256.splitAndPad_v in H.
  unfold EQ256.fpad_v in H.
  unfold EQ256.b in H. apply H.
Qed.

(* Earlier explicit proof:
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
  erewrite HMAC256_spec_list.HMAC_list_concat_sap_instantiated. (*; trivial.*)
SearchAbout sha_splitandpad_inc.
(*sap' to be instantiated to sha_splitandpad_inc*)
  2: apply sha_h_length.
  2: apply VectorToList_length.
  2: apply VectorToList_length.
  2: apply VectorToList_length.
  2: apply fold_hash_blocks_eq.
  2: apply LK.
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

Qed.
End EQUIV. *)