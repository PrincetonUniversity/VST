Set Implicit Arguments.

Require Import List. (*Import ListNotations.*)
Require Import sha.ByteBitRelations.
Require Import sha.HMAC_common_defs.
Require Import sha.HMAC_spec_concat.

Module HMAC_List.

Section HMAC.
  Variable c:nat.
  Variable p:nat.
  Definition b := (c+p)%nat.

  (* The compression function *)
  Variable h : Blist -> Blist -> Blist.

  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Blist.

  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star k (m : list (Blist)) :=
    fold_left h m k.

  (* The composition of the keyed hash function with the IV. *)
  Definition hash_words := h_star iv.

  Variable splitAndPad : Blist -> list (Blist).

  (* fpad can be a constant *)
  Variable fpad : Blist -> Blist.
  Definition app_fpad (x : Blist) : Blist :=
    x ++ fpad x.

  Definition h_star_pad k x :=
    app_fpad (h_star k x).

  (* The "two-key" version of GHMAC and HMAC. *)
  Definition GHMAC_2K (k : Blist) m :=
    let (k_Out, k_In) := splitList b k in
      let h_in := (hash_words (k_In :: m)) in
        hash_words (k_Out :: (app_fpad h_in) :: nil).

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
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.

  Definition GNMAC k m :=
    let (k_Out, k_In) := splitList c k in
    h k_Out (app_fpad (h_star k_In m)).

  Hypothesis opad_ne_ipad : opad <> ipad.

  Definition GHMAC (k : Blist) :=
    GHMAC_2K (BLxor k opad ++ BLxor k ipad).
  *)

End HMAC.

Lemma fpad_list_concat_eq :
  HMAC_List.app_fpad = HMAC_Concat.app_fpad.
Proof. reflexivity. Qed.

Theorem HMAC_list_concat c p B fpad
        (fpad_length: forall msg, length msg = c -> length (fpad msg) = p) sap
        (sap_b: forall m, Forall (fun x => length x = (c+p)%nat) (sap m))
        sap' (sap_sap': forall m, sap' m = concat (sap m))
        h (HH: forall x y, length x = c -> length y = (c+p)%nat -> length (h x y)  = c)
        iv (IV: length iv = c) (op ip : Blist) (IL: length ip = (c+p)%nat) (OL: length op = (c+p)%nat)
        (FOLD_hash_blocks_eq : forall (l : Blist) (ls : list Blist),
               length l = (c+p)%nat ->
               Forall (fun x : list bool => length x = (c+p)%nat) ls ->
               fold_left h (l :: ls) iv =
               hash_blocks_bits _ B h iv (l ++ concat ls))
        : forall (k m : Blist), length k = (c+p)%nat ->
  HMAC_List.HMAC c p h iv sap fpad op ip k m =
  HMAC_Concat.HMAC c p B h iv sap' fpad op ip k m.
Proof.
  intros k m k_len.
  unfold HMAC. unfold HMAC_Concat.HMAC.
  unfold HMAC_2K. unfold HMAC_Concat.HMAC_2K.
  unfold GHMAC_2K. unfold HMAC_Concat.GHMAC_2K.

  repeat rewrite -> split_append_id.
  unfold hash_words. unfold HMAC_Concat.hash_words.
  rewrite -> fpad_list_concat_eq.

  rewrite sap_sap'.
  unfold h_star.
  unfold HMAC_Concat.h_star.
  rewrite concat_app.
  rewrite <- FOLD_hash_blocks_eq.
  rewrite <- FOLD_hash_blocks_eq.
  reflexivity.

  * apply BLxor_length; trivial.
  * apply sap_b.
  * apply BLxor_length; trivial.
  * unfold HMAC_Concat.app_fpad.

    constructor. 2: constructor.
    rewrite app_length. rewrite <- FOLD_hash_blocks_eq.
      2: apply BLxor_length; trivial.
      2: apply sap_b.
    assert (C: length (fold_left h (BLxor k ip :: sap m) iv) =c).
      rewrite FOLD_hash_blocks_eq; trivial.
        apply hash_blocks_bits_len; trivial.
        econstructor. 2: reflexivity.
         erewrite BLxor_length. reflexivity. assumption. assumption.
         apply concat_InBlocks; apply sap_b.
         erewrite BLxor_length. reflexivity. assumption. assumption.
    rewrite fpad_length; trivial. f_equal. rewrite <- C. reflexivity.

  * apply BLxor_length; trivial.
  * apply BLxor_length; trivial.
  * apply BLxor_length; trivial.
  * apply BLxor_length; trivial.
Qed.

End HMAC_List.
