Set Implicit Arguments.

Require Import List.
Require Import Bvector.
Require Import HMAC_common_defs.
Require Import SHA256.
Require Import HMAC_spec_pad.
Require Import Coq.Program.Basics.
Require Import Coqlib.
Require Import ByteBitRelations.
Require Import sha_padding_lemmas.

Module HMAC_Concat.

Section HMAC.

  Variable c p : nat.
  Definition b := (c + p)%nat.
  
  (* The compression function *)
  Variable h : Blist -> Blist -> Blist.
  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Blist.

  (* splitAndPad concat'ed, normal fold replaced by firstn/splitn manual fold *)

  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star k (m : Blist) :=
    hash_blocks_bits h k m.
  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words := h_star iv.

  Variable splitAndPad : Blist -> Blist.
  Hypothesis splitAndPad_1_1 : 
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.

  (* fpad can be a constant *)
  Variable fpad : Blist -> Blist. 
  Definition app_fpad (x : Blist) : Blist :=
    x ++ fpad x.

  Definition h_star_pad k x :=
    app_fpad (h_star k x).

  Definition GNMAC k m :=
    let (k_Out, k_In) := splitList c k in
    h k_Out (app_fpad (h_star k_In m)).

  (* The "two-key" version of GHMAC and HMAC. *)
  Definition GHMAC_2K (k : Blist) m :=
    let (k_Out, k_In) := splitList b k in
      let h_in := (hash_words (k_In ++ m)) in 
        hash_words (k_Out ++ app_fpad h_in).
  
  Definition HMAC_2K (k : Blist) (m : Blist) :=
    GHMAC_2K k (splitAndPad m).

  (* opad and ipad are constants defined in the HMAC spec. *)
  Variable opad ipad : Blist.
  Hypothesis opad_ne_ipad : opad <> ipad.

  Definition GHMAC (k : Blist) :=
    GHMAC_2K (BLxor k opad ++ BLxor k ipad).

  Definition HMAC (k : Blist) :=
    HMAC_2K (BLxor k opad ++ BLxor k ipad).

End HMAC.

End HMAC_Concat.

Lemma h_star_eq :
  HMAC_Pad.h_star = HMAC_Concat.h_star.
Proof. reflexivity. Qed.

Lemma block_8 : forall (l : Blist), length l = b -> InBlocks 8 l.
Proof.
  intros l len. apply InBlocks_len. exists 64%nat. apply len. 
Qed.

Lemma splitandpad_eq : forall (l m : Blist),
                         length l = b ->
                         sha_splitandpad (l ++ m) = l ++ sha_splitandpad_inc m.
Proof.
  intros l m len.
  unfold sha_splitandpad. unfold sha_splitandpad_inc.
  unfold pad. unfold pad_inc.

  rewrite -> bitsToBytes_app.
  rewrite -> common_lemmas.Zlength_app.
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

Lemma fpad_eq : forall (l m : Blist),
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
  rewrite -> common_lemmas.Zlength_app.
  repeat f_equal.

  * apply bitsToBytes_len. apply len.
  * apply bitsToBytes_len. apply len.
  * apply bitsToBytes_len. apply len.
  * apply len_m.
  * apply block_8. apply len.
  * apply block_8. apply len.
Qed. 

Lemma NPeano_divide_trans a b c: NPeano.divide a b -> 
      NPeano.divide b c -> NPeano.divide a c.
Proof. intros. destruct H; destruct H0. subst.
  exists (x0 * x)%nat. apply mult_assoc.
Qed. 

Theorem HMAC_concat_pad : forall (k m : Blist) (op ip : Blist),
                            length k = b ->
                            length ip = b ->
                            length op = b -> 
  HMAC_Pad.HMAC c p sha_h sha_iv sha_splitandpad op ip k m =
  HMAC_Concat.HMAC c p sha_h sha_iv sha_splitandpad_inc fpad op ip k m.
Proof.
  intros k m op ip len_k len_ip len_op.
  unfold c, p in *. simpl in *.
  unfold HMAC_Pad.HMAC. unfold HMAC_Concat.HMAC.
  unfold HMAC_Pad.HMAC_2K. unfold HMAC_Concat.HMAC_2K.
  unfold HMAC_Pad.GHMAC_2K. unfold HMAC_Concat.GHMAC_2K.

  repeat rewrite -> split_append_id.
  unfold HMAC_Pad.hash_words_padded. unfold compose.
  unfold HMAC_Concat.hash_words.
  unfold HMAC_Pad.hash_words.
  rewrite -> h_star_eq.
  
  (* show the two inputs to h_star are equal *)
  f_equal.

  rewrite <- splitandpad_eq.
  rewrite <- fpad_eq.           (* wants the InBlocks 8 *)
  reflexivity.

  * apply BLxor_length. apply len_k. apply len_op.
  *
    unfold HMAC_Concat.h_star.
    apply InBlocks_len.
    rewrite hash_blocks_bits_len.
      exists (32%nat).  simpl. omega.
      apply sha_iv_length.
      rewrite splitandpad_eq.
               econstructor.
                 2: reflexivity.
                 apply BLxor_length. apply len_k. apply len_ip.
                 apply sha_splitandpad_inc_InBlocks.
                 apply BLxor_length. apply len_k. apply len_ip.
  * apply BLxor_length. apply len_k. apply len_ip.
  * apply BLxor_length. apply len_k. apply len_op.
  * apply BLxor_length. apply len_k. apply len_ip.
  * apply BLxor_length. apply len_k. apply len_op.
  * apply BLxor_length. apply len_k. apply len_ip.
Qed.
