Set Implicit Arguments.

Require Import List.
Require Import sha.ByteBitRelations. (*For InBlocks*)
Require Import sha.HMAC_common_defs.
Require Import sha.HMAC_spec_pad.

(*Parameter c:nat.
Parameter p:nat.
Parameter b:nat.*)

Module HMAC_Concat.
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

  (* The composition of the keyed hash function with the IV.*)
  Definition hash_words := h_star iv.

  (* splitAndPad concat'ed, normal fold replaced by firstn/splitn manual fold *)
  Variable splitAndPad : Blist -> Blist.

  (* fpad can be a constant *)
  Variable fpad : Blist -> Blist.
  Definition app_fpad (x : Blist) : Blist :=
    x ++ fpad x.

  Definition h_star_pad k x :=
    app_fpad (h_star k x).

  (* The "two-key" version of GHMAC and HMAC. *)
  Definition GHMAC_2K (k : Blist) m :=
    let (k_Out, k_In) := splitList b k in
      let h_in := (hash_words (k_In ++ m)) in
        hash_words (k_Out ++ app_fpad h_in).

  Definition HMAC_2K (k : Blist) (m : Blist) :=
    GHMAC_2K k (splitAndPad m).

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
    h k_Out (app_fpad (h_star k_In m)).

  Hypothesis opad_ne_ipad : opad <> ipad.

  Definition GHMAC (k : Blist) :=
    GHMAC_2K (BLxor k opad ++ BLxor k ipad).
  *)

End HMAC.

Lemma h_star_eq :
  sha.HMAC_spec_pad.h_star = h_star.
Proof. reflexivity. Qed.

Theorem HMAC_concat_pad c p (C: NPeano.Nat.divide 8 c) B sap sap' fp
        (sap_sap': forall l m, length l = (c+p)%nat ->
                          sap (l ++ m) = l ++ sap' m)
        (sap_appfpad: forall (l m : Blist),
                  length l = (c+p)%nat ->
                  InBlocks 8 m ->
                  sap (l ++ m) = l ++ app_fpad fp m)
        (InBlocks_sap': forall m, InBlocks (c+p)%nat (sap' m))
        h (HH: forall x y, length x = c -> length y = (c+p)%nat -> length (h x y)  = c)
        iv (IV: length iv = c) (op ip : Blist) (IL: length ip = (c+p)%nat) (OL: length op = (c+p)%nat)
        : forall (k m : Blist), length k = (c+p)%nat ->
  sha.HMAC_spec_pad.HMAC c p B h iv sap op ip k m =
  HMAC_Concat.HMAC c p B h iv sap' fp op ip k m.
Proof.
  intros k m len_k.
  unfold sha.HMAC_spec_pad.HMAC. unfold HMAC.
  unfold sha.HMAC_spec_pad.HMAC_2K. unfold HMAC_2K.
  unfold sha.HMAC_spec_pad.GHMAC_2K. unfold GHMAC_2K.

  repeat rewrite -> split_append_id; try apply BLxor_length; trivial.
  unfold sha.HMAC_spec_pad.hash_words_padded. unfold Basics.compose.
  unfold hash_words.
  unfold sha.HMAC_spec_pad.hash_words.
  rewrite -> h_star_eq.
  f_equal.

  rewrite <- sap_sap'; try apply BLxor_length; trivial.
  rewrite <- sap_appfpad; try apply BLxor_length; trivial.

  unfold HMAC_Concat.h_star.
    apply InBlocks_len.
    erewrite hash_blocks_bits_len; try eassumption.
      (*exists (32%nat); reflexivity.*)
      rewrite sap_sap'.
               econstructor.
                 2: reflexivity.
                 apply BLxor_length; trivial.
                 apply InBlocks_sap'.
                 apply BLxor_length; trivial.
Qed.

End HMAC_Concat.
