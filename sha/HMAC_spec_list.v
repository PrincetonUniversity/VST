Set Implicit Arguments.

Require Import msl.Axioms.

Require Import Bvector.
Require Import List. Import ListNotations.
Require Import HMAC_common_defs.
Require Import Arith.
Require Import HMAC_spec_concat.
Require Import ByteBitRelations.
Require Import sha_padding_lemmas.
Require Import pure_lemmas.
Require Import common_lemmas.
Require Import hmac_pure_lemmas.

Module HMAC_List.

Section HMAC.

  (*Variable c p : nat.
  Definition b := c + p.*)
  
  (* The compression function *)
  Variable h : Blist -> Blist -> Blist.
  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Blist.
  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star k (m : list (Blist)) :=
    fold_left h m k.
  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words := h_star iv.

  Variable splitAndPad : Blist -> list (Blist).

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
      let h_in := (hash_words (k_In :: m)) in 
        hash_words (k_Out :: (app_fpad h_in) :: nil).
  
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

End HMAC_List.

Require Import SHA256.
Require Import Coqlib.

Function toBlocks (l : Blist) {measure length l} : list Blist :=
  (match l with
    | nil => nil
    | _ :: _ => if leb (length l) 511 then [firstn 512 l] 
                else firstn 512 l :: toBlocks (skipn 512 l)
  end)%list.
Proof.
  intros. subst. remember (b :: l0) as l. clear Heql.
  apply leb_complete_conv in teq0.
  rewrite skipn_length; omega.
Qed.

Lemma toBlocks_injective: forall l1 l2 (BLKS: toBlocks l1 = toBlocks l2)
     (F1: InBlocks 512 l1)
     (F2: InBlocks 512 l2), l1 = l2.
Proof.
 intros l1. 
  remember (toBlocks l1). generalize dependent l1.
  induction l. simpl; intros.
    rewrite toBlocks_equation in *.
    destruct l1.
      destruct l2; trivial.
      destruct (Compare_dec.leb (length (b :: l2)) 511); discriminate.
    destruct (Compare_dec.leb (length (b :: l1)) 511); discriminate.

  intros.
    rewrite toBlocks_equation in Heql, BLKS.
    destruct l1; try discriminate. destruct l2; try discriminate.
    inversion F1; clear F1. rewrite H0 in Heql.
    assert (L1: (511 < length (front ++ back))%nat).
      rewrite app_length, H. omega.
    rewrite leb_correct_conv in Heql; trivial.
    rewrite firstn_exact in Heql; trivial.
    rewrite skipn_exact in Heql; trivial.
    inversion Heql; clear Heql. subst a l.

    inversion F2; clear F2. rewrite H4 in BLKS. 
    assert (L2: (511 < length (front0 ++ back0))%nat).
      rewrite app_length, H3. omega.
    rewrite leb_correct_conv in BLKS; trivial.
    rewrite firstn_exact in BLKS; trivial.
    rewrite skipn_exact in BLKS; trivial.
    inversion BLKS; clear BLKS. subst front0 full0 full.
    specialize (IHl _ H9 _ (eq_refl _) H5 H1). subst back0.
    rewrite <- H4 in H0. assumption.
Qed.

Definition sha_splitandpad_blocks (msg : Blist) : list Blist :=
  toBlocks (sha_splitandpad_inc msg).

Definition sha_splitandpad_inc' (msg : Blist) : Blist :=
  concat (sha_splitandpad_blocks msg).

Lemma concat_toBlocks_id : forall (l : Blist),
                             InBlocks 512 l ->
                             concat (toBlocks l) = l.
Proof.
  intros l len.
  unfold concat.
  induction len.

  * rewrite -> toBlocks_equation. reflexivity.
  *
    rewrite -> toBlocks_equation.
    destruct full. 
      assert (@length bool nil = length (front ++ back)). rewrite <- H0; reflexivity. 
      rewrite app_length, H in H1. remember (length back). clear - H1. rewrite plus_comm in H1. simpl in H1. omega.
    rewrite H0, app_length, H, leb_correct_conv. 2: omega.
    rewrite -> firstn_exact; trivial.
    rewrite -> skipn_exact; trivial.
    (*rewrite -> length_not_emp.*)
    simpl.
    rewrite -> IHlen.
    unfold id.
    reflexivity.
Qed.

Lemma InBlocks_Forall_512 b: (InBlocks 512 b) ->
      Forall (fun x : list bool => length x = 512%nat) (toBlocks b).
Proof. intros.
  remember (toBlocks b). generalize dependent b.
  induction l. simpl; intros. constructor.
  simpl; intros. rewrite toBlocks_equation in Heql. destruct b. discriminate.
  inversion H; clear H.
  rewrite H1, app_length, H0 in Heql. 
  rewrite leb_correct_conv in Heql. 2: omega.
  rewrite firstn_exact in Heql; trivial.
  rewrite skipn_exact in Heql; trivial. inversion Heql; clear Heql.
  constructor. trivial.
  subst l. apply (IHl _ H2 (eq_refl _)).
Qed.

Lemma sha_splitandpad_blocks_512 m:
      Forall (fun x => length x = 512%nat) (sha_splitandpad_blocks m).
Proof. apply InBlocks_Forall_512. apply sha_splitandpad_inc_InBlocks. 
Qed.

(* since sha_splitandpad_inc is used instead of the modified version in the Concat-Pad proof *)
Lemma sha_splitandpad_inc_eq : sha_splitandpad_inc = sha_splitandpad_inc'.
Proof.
  extensionality msg.
  unfold sha_splitandpad_inc'. unfold sha_splitandpad_blocks.
  rewrite toBlocks_equation. 
  remember (sha_splitandpad_inc msg). 
  destruct b. reflexivity. unfold sha_splitandpad_inc in Heqb. rewrite Heqb. clear Heqb.
  destruct (sha_splitandpad_inc_length msg) as [k [K HK]].
  unfold sha_splitandpad_inc in HK. rewrite HK.
  rewrite leb_correct_conv. 2: omega.
  remember (pad_inc (bitsToBytes msg)). clear Heql.
  symmetry. 
  assert (HH: firstn 512 (bytesToBits l) :: toBlocks (skipn 512 (bytesToBits l)) = toBlocks  (bytesToBits l)).
    remember (bytesToBits l) as bits. rewrite (toBlocks_equation bits).
    destruct bits. destruct l; simpl in *. omega. discriminate.
    (*rewrite Heqbits. clear Heqbits. *)
    rewrite leb_correct_conv. trivial. rewrite HK. omega. 
  rewrite HH. apply concat_toBlocks_id.
  apply InBlocks_len. rewrite HK. exists k. omega.
Qed.

Lemma concat_length {A}: forall L (l:list A), In l L -> (length (concat L) >= length l)%nat.
Proof.  unfold concat. induction L; simpl; intros. contradiction.
  rewrite app_length. 
  destruct H; subst. unfold id. omega.
  specialize (IHL _ H). omega.
Qed.

Lemma toBlocks_app_split l1 l2: length l1 = 512%nat ->
      toBlocks (l1 ++ l2) = toBlocks l1 ++ toBlocks l2.
Proof. intros.
  rewrite toBlocks_equation. rewrite app_length. 
  rewrite firstn_exact; trivial.
  rewrite skipn_exact; trivial.
  remember (l1 ++ l2).
  destruct l. 
  { assert (@length bool nil = length (l1 ++ l2)). rewrite <- Heql; trivial.
    rewrite app_length, H in H0. rewrite plus_comm in H0. simpl in H0. omega. }
  { rewrite  leb_correct_conv. 2: rewrite H, plus_comm; omega.
    remember (toBlocks l2).
    rewrite toBlocks_equation.
    destruct l1. simpl in H; omega. 
    rewrite leb_correct_conv. 2: rewrite H; omega.
    rewrite firstn_same. 2: rewrite H; omega. 
    rewrite skipn_short. 2: rewrite H; omega. 
    rewrite toBlocks_equation. trivial. }
Qed. 

Lemma len_min : forall {A : Type} (l : list A), (length l >= 0)%nat.
Proof. intros. destruct l; simpl. omega. omega. Qed.

Theorem fold_hash_blocks_eq_ind : forall (l : list Blist) (iv : Blist),
                                    Forall (fun x => length x = 512%nat) l ->
                                    fold_left sha_h l iv =
                                    hash_blocks_bits sha_h iv (concat l).
Proof.
  intros l.
  induction l as [ | l ls]; intros iv len_l.

  * simpl. reflexivity.
  *
    rewrite -> Forall_forall in len_l.
    Opaque firstn. Opaque skipn.  simpl.
    unfold id.
    rewrite hash_blocks_bits_equation.    
    rewrite -> firstn_exact. rewrite -> skipn_exact.
    rewrite -> length_not_emp.
    apply IHls.
    apply Forall_forall; intros.
    apply len_l.
    apply in_cons.
    apply H.
    
  -
    rewrite -> app_length.
    assert (length l = 512%nat). apply len_l. unfold In. auto.
    rewrite -> H.
    specialize (len_min ls).
    omega.

  - apply len_l. unfold In. auto.

  - apply len_l. unfold In. auto.
Qed.

Theorem fold_hash_blocks_eq : forall (l : Blist) (ls : list Blist),
                                length l = 512%nat ->
                                Forall (fun x => length x = 512%nat) ls ->
                                fold_left sha_h (l :: ls) sha_iv =
                                hash_blocks_bits sha_h sha_iv (l ++ concat ls).
Proof.
  intros l ls len_l len_ls.
  pose proof fold_hash_blocks_eq_ind as fold_ind.
  simpl.
  rewrite hash_blocks_bits_equation.    
  rewrite -> firstn_exact. rewrite -> skipn_exact.
  rewrite -> length_not_emp.
  apply fold_ind.
  * apply len_ls.
  *
    rewrite -> app_length.
    rewrite len_l.
    specialize (len_min ls).
    omega.
  * apply len_l.
  * apply len_l.
Qed.

Lemma fpad_list_concat_eq :
  HMAC_List.app_fpad = HMAC_Concat.app_fpad.
Proof. reflexivity. Qed.

Lemma mult_triv x : forall y, y=2%nat -> (x * y = x*2)%nat.
Proof. intros. subst. omega. Qed.

Theorem HMAC_list_concat : forall (k m : Blist) (op ip : Blist),
                             length k = b ->
                             length op = b ->
                             length ip = b ->
  HMAC_List.HMAC sha_h sha_iv sha_splitandpad_blocks fpad op ip k m =
  (* Note use of sha_splitandpad_blocks and sha_splitandpad_inc' (= concat the blocks) *)
  HMAC_Concat.HMAC sha_h sha_iv sha_splitandpad_inc' fpad op ip k m.
Proof.
  intros k m op ip k_len op_len ip_len.
  unfold c, p in *. simpl in *.
  unfold HMAC_List.HMAC. unfold HMAC_Concat.HMAC.
  unfold HMAC_List.HMAC_2K. unfold HMAC_Concat.HMAC_2K.
  unfold HMAC_List.GHMAC_2K. unfold HMAC_Concat.GHMAC_2K.

  repeat rewrite -> split_append_id.
  unfold HMAC_List.hash_words. unfold HMAC_Concat.hash_words.
  rewrite -> fpad_list_concat_eq.

  unfold HMAC_List.h_star.
  unfold HMAC_Concat.h_star.

  unfold sha_splitandpad_inc'.
  (* Check fold_hash_blocks_eq. *)
  rewrite <- fold_hash_blocks_eq. (* important *)
  assert (forall (l1 l2 : Blist), l1 ++ l2 = l1 ++ concat (l2 :: nil)) as create_concat.
    intros. unfold concat. simpl.
    rewrite -> app_nil_r. reflexivity.

  rewrite -> create_concat.
  rewrite <- fold_hash_blocks_eq. (* again *)
  reflexivity.

  * apply BLxor_length. apply k_len. apply op_len.
  * unfold HMAC_Concat.app_fpad.
    unfold fpad.

    constructor. 2: constructor.
    rewrite app_length, fold_hash_blocks_eq.
      2: apply BLxor_length; trivial. 
      2: apply sha_splitandpad_blocks_512.
    assert (IB: InBlocks 512 (BLxor k ip ++ concat (sha_splitandpad_blocks m))).
      unfold sha_splitandpad_blocks. 
      rewrite concat_toBlocks_id. 2: apply sha_splitandpad_inc_InBlocks.
      econstructor.
        2: reflexivity.
        2: apply sha_splitandpad_inc_InBlocks.
        apply BLxor_length; trivial.
    rewrite bytesToBits_len.
        unfold fpad_inner. repeat rewrite app_length. 
        rewrite Coqlib.length_list_repeat, pure_lemmas.length_intlist_to_Zlist.
        rewrite (mult_triv 4). 2: reflexivity.
    rewrite (hash_blocks_bits_len sha_iv _ sha_iv_length IB). 
    rewrite Zlength_correct. 
    erewrite bitsToBytes_len_gen with (n:=32%nat).
    reflexivity.
    apply (hash_blocks_bits_len sha_iv _ sha_iv_length IB).
  * apply BLxor_length. apply k_len. apply ip_len.
  * 
  (*  Forall (fun x : list bool => length x = 512%nat)
     (sha_splitandpad_blocks m) *)
    apply sha_splitandpad_blocks_512.
  * apply BLxor_length. apply k_len. apply op_len.
  * apply BLxor_length. apply k_len. apply ip_len.
Qed.  
