Require Import List. Import ListNotations.
Require Import sha.general_lemmas.
Require Import sha.ByteBitRelations.
Require Import sha.HMAC_spec_concat.
Require Import sha.HMAC_spec_pad.

(*SHA256-specific files*)
Require Import sha.sha_padding_lemmas. (*for pad.*)
Require Import sha.ShaInstantiation.

Lemma sha_splitandpad_fpad : forall (l m : Blist),
                  length l = b ->
                  InBlocks 8 m ->
                  sha_splitandpad (l ++ m) = l ++ HMAC_Concat.app_fpad fpad m.
Proof.
  intros l m len len_m.
  unfold HMAC_Concat.app_fpad.
  unfold sha_splitandpad. unfold fpad.
  unfold pad. unfold fpad_inner.

  rewrite -> bitsToBytes_app.
  repeat rewrite -> bytesToBits_app.
  repeat rewrite -> bits_bytes_bits_id.
  rewrite <- app_assoc.
  rewrite -> sublist.Zlength_app.
  repeat f_equal.

  * apply bitsToBytes_len. apply len.
  * apply bitsToBytes_len. apply len.
  * apply bitsToBytes_len. apply len.
  * apply len_m.
  * apply block_8. apply len.
  * apply block_8. apply len.
Qed.

Theorem HMAC_concat_pad_sap_instantiated
        h (HH: forall x y, length x = c -> length y = b -> length (h x y)  = c)
        iv (IV: length iv = c) (op ip : Blist) (IL: length ip = b) (OL: length op = b)
        : forall (k m : Blist), length k = b ->
  sha.HMAC_spec_pad.HMAC c p B h iv sha_splitandpad op ip k m =
  HMAC_Concat.HMAC c p B h iv sha_splitandpad_inc fpad op ip k m.
Proof. intros.
  apply HMAC_Concat.HMAC_concat_pad; trivial.
  exists 32%nat. reflexivity.
  apply sha_splitandpad_app.
  apply sha_splitandpad_fpad.
  apply sha_splitandpad_inc_InBlocks.
Qed.

Theorem HMAC_concat_pad_explicit : forall (k m : Blist) (op ip : Blist),
                            length k = b ->
                            length ip = b ->
                            length op = b ->
  sha.HMAC_spec_pad.HMAC c p B sha_h sha_iv sha_splitandpad op ip k m =
  HMAC_Concat.HMAC c p B sha_h sha_iv sha_splitandpad_inc fpad op ip k m.
Proof.
  intros k m op ip len_k len_ip len_op.
  apply HMAC_concat_pad_sap_instantiated; trivial.
    apply sha_h_length.
Qed.
