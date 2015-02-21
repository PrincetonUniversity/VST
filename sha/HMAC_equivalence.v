Require Import Coqlib.
Require Import Bvector.
Require Import List.
Require Import BinNums.
(*Require Import Arith.*)
Require Import common_lemmas.
Require Import HMAC_functional_prog.
Require Import ByteBitRelations.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.
Require Import HMAC_spec_list.
Require Import HMAC_spec_abstract.
Require Import HMAC_common_defs.


(* TODO Duplicates the definition in Blist.v - could eliminate this after merging with FCF*)
Definition of_list_length (A : Set)(m : nat)(ls : list A)(pf : length ls = m) : Vector.t A m :=
  match pf with
    | eq_refl => Vector.of_list ls
  end. 

Lemma of_length_proof_irrel n a: forall M, 
      Vector.to_list (of_list_length bool n a M) = a.
Proof. intros.
  unfold of_list_length. destruct M. apply Vector.to_list_of_list_opp. 
Qed.

Section EQUIV.

Definition h_v (iv:Bvector c) (blk:Bvector b): Bvector c :=
  of_list_length _ _ _
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
                       (Integers.Byte.unsigned HP.Opad))) = HMAC_spec_abstract.b.
Proof. rewrite bytesToBits_len, length_SF. reflexivity. Qed. 
 
Definition opad_v: Bvector b := of_list_length _ _ _ opad_length.

Lemma ipad_length:
  length (bytesToBits (HP.HMAC_SHA256.sixtyfour
                       (Integers.Byte.unsigned HP.Ipad))) = b.
Proof. rewrite bytesToBits_len, length_SF. reflexivity. Qed. 
 
Definition ipad_v: Bvector b := of_list_length _ _ _ ipad_length.

Lemma fpad_length (v:Bvector c): length (fpad (Vector.to_list v)) = p.
Proof. unfold fpad, fpad_inner. rewrite bytesToBits_len.
  repeat rewrite app_length. rewrite length_list_repeat, pure_lemmas.length_intlist_to_Zlist.
  rewrite (mult_comm 4), plus_comm, Zlength_correct.
  rewrite bitsToBytes_len_gen with (n:=32%nat).
    reflexivity.
    apply VectorToList_length.
Qed. 

Definition fpad_v (v:Bvector c): Bvector p := of_list_length _ _ _ (fpad_length v).
  
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
|  cons h t => fun F => cons (of_list_length _ _ h (Forall_inv F)) 
                    (splitAndPad_aux t (Forall_tl _ _ _ _ F))
 end) M.

Lemma splitAndPad_aux_consD h t M: 
      splitAndPad_aux (cons h t) M
      = (of_list_length _ _ h (Forall_inv M)) 
         :: (splitAndPad_aux t (Forall_tl _ _ _ _ M)).
Proof. reflexivity. Qed. 

Lemma splitAndPad_aux_nil m M: m=nil -> splitAndPad_aux m M= nil.
Proof. intros; subst. reflexivity. Qed.

Definition splitAndPad_v (m: Blist): list (Bvector b).
  apply (splitAndPad_aux (toBlocks (sha_splitandpad_inc m))).
  apply InBlocks_Forall_512. apply sha_splitandpad_inc_InBlocks.
Defined.

Lemma splitAndPad_nil: exists pf,
  splitAndPad_v nil = 
  cons (of_list_length bool 512 (sha_splitandpad_inc nil) pf) nil. 
Proof. unfold splitAndPad_v. 
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
    
Lemma length_splitandpad_inner m :
   Forall2
     (fun (bv : Vector.t bool b) (bl : list bool) => bl = Vector.to_list bv)
     (splitAndPad_v m) (sha_splitandpad_blocks m).
Proof. apply length_splitandpad_inner_aux. Qed.


(* Note implicit assumption that the key is of the right length
   is now OK, since we're comapring to HP.HMAC_SHA256.HmacCore, not HMAC. *)

Lemma Equivalence : forall (kv : Bvector b) (m : Blist),
      NPeano.divide 8 (length m) ->
      Vector.to_list (HMAC_spec.HMAC h_v iv_v splitAndPad_v
                      fpad_v opad_v ipad_v kv m) = 
      bytesToBits (HP.HMAC_SHA256.HmacCore (Integers.Byte.repr 54) (Integers.Byte.repr 92)
                              (bitsToBytes m)
                              (map Integers.Byte.repr (bitsToBytes (Vector.to_list kv)))).
Proof.
  intros kv m LM.
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
    apply sha_padding_lemmas.InBlocks_len; trivial. }

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
