
Require Import VST.msl.Axioms. (*for extensionality*)
Require Import Arith.
Require Import List. Import ListNotations.
Require Import sha.general_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.ByteBitRelations.
Require Import sha.HMAC_common_defs.
Require Import sha.HMAC_spec_list.
Require Import sha.HMAC_spec_concat.
Require Import sha.ShaInstantiation.

Require Import Omega.

(*
Definition ltb (n m:nat):bool := if beq_nat n m then false else leb n m.
Lemma ltb_char n m: ltb n m = true <-> (n<m)%nat.
  unfold ltb. remember (beq_nat n m). destruct b; symmetry in Heqb; split; intros.
    inv H. apply beq_nat_true in Heqb. subst. omega.
   apply beq_nat_false in Heqb. apply leb_complete in H. omega.
   apply leb_correct. omega.
Qed.
*)

Function toBlocks (l : Blist) {measure length l} : list Blist :=
  (match l with
    | nil => nil
    | _ :: _ => if leb (List.length l) 511 then [firstn 512 l]
                else firstn 512 l :: toBlocks (skipn 512 l)
  end)%list.
Proof.
  intros. subst. remember ((b :: l0)%list) as l. clear Heql.
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
(*
Definition sha_splitandpad_inc' (msg : Blist) : Blist :=
  concat (sha_splitandpad_blocks msg).
*)
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

Lemma concat_toBlocks_id l: InBlocks 512 l -> concat (toBlocks l) = l.
Proof.
  intros len.
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

Theorem HMAC_list_concat_sap_instantiated
        h (HH: forall x y, length x = c -> length y = b -> length (h x y)  = c)
        iv (IV: length iv = c) (op ip : Blist) (IL: length ip = b) (OL: length op = b)
        (FOLD_hash_blocks_eq : forall (l : Blist) (ls : list Blist),
               length l = b ->
               Forall (fun x : list bool => length x = b) ls ->
               fold_left h (l :: ls) iv =
               hash_blocks_bits _ B h iv (l ++ concat ls))
        : forall (k m : Blist), length k = b ->
  HMAC_List.HMAC c p h iv sha_splitandpad_blocks fpad op ip k m =
  (* Note use of sha_splitandpad_blocks and sha_splitandpad_inc' (= concat the blocks) *)
  HMAC_Concat.HMAC c p B h iv sha_splitandpad_inc fpad op ip k m.
Proof. intros.
  apply HMAC_List.HMAC_list_concat; trivial.
    apply fpad_length.
    apply sha_splitandpad_blocks_512.
    unfold sha_splitandpad_blocks; intros. rewrite concat_toBlocks_id; trivial.
      apply sha_splitandpad_inc_InBlocks.
Qed.

Lemma len_min : forall {A : Type} (l : list A), (length l >= 0)%nat.
Proof. intros. destruct l; simpl. omega. omega. Qed.

Theorem fold_hash_blocks_eq_ind : forall (l : list Blist) (iv : Blist),
                                    Forall (fun x => length x = 512%nat) l ->
                                    fold_left sha_h l iv =
                                    hash_blocks_bits _ B sha_h iv (concat l).
Proof.
  intros l.
  induction l as [ | l ls]; intros iv len_l.

  * simpl. reflexivity.
  *
    rewrite -> Forall_forall in len_l. simpl.
    rewrite hash_blocks_bits_equation.
    rewrite -> firstn_exact, -> skipn_exact, -> length_not_emp.
  - apply IHls.
    apply Forall_forall; intros.
    apply len_l.
    apply in_cons.
    apply H.
  - rewrite -> app_length.
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
                                hash_blocks_bits _ B sha_h sha_iv (l ++ concat ls).
Proof.
  intros l ls len_l len_ls.
  pose proof fold_hash_blocks_eq_ind as fold_ind.
  simpl.
  rewrite hash_blocks_bits_equation.
  rewrite -> firstn_exact. rewrite -> skipn_exact.
  rewrite -> length_not_emp.
  apply fold_ind.
  * apply len_ls.
  * rewrite -> app_length.
    rewrite len_l.
    specialize (len_min ls).
    omega.
  * apply len_l.
  * apply len_l.
Qed.

Theorem HMAC_list_concat_explicit : forall (k m : Blist) (op ip : Blist),
                             length k = b ->
                             length op = b ->
                             length ip = b ->
  HMAC_List.HMAC c p sha_h sha_iv sha_splitandpad_blocks fpad op ip k m =
  (* Note use of sha_splitandpad_blocks and sha_splitandpad_inc' (= concat the blocks) *)
  HMAC_Concat.HMAC c p B sha_h sha_iv sha_splitandpad_inc fpad op ip k m.
Proof.
  intros k m op ip k_len op_len ip_len.
  apply HMAC_list_concat_sap_instantiated; trivial.
    apply sha_h_length.
    apply fold_hash_blocks_eq.
Qed.


(* since sha_splitandpad_inc is used instead of the modified version in the Concat-Pad proof
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
  assert (HH: (firstn 512 (bytesToBits l) :: toBlocks (skipn 512 (bytesToBits l))
               = toBlocks  (bytesToBits l))%list).
    remember (bytesToBits l) as bits. rewrite (toBlocks_equation bits).
    destruct bits. destruct l; simpl in *. omega. discriminate.
    (*rewrite Heqbits. clear Heqbits. *)
    rewrite leb_correct_conv. trivial. rewrite HK. omega.
  rewrite HH. apply concat_toBlocks_id.
  apply InBlocks_len. rewrite HK. exists k. omega.
Qed.*)

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
    rewrite sublist.firstn_same. 2: rewrite H; omega.
    rewrite skipn_short. 2: rewrite H; omega.
    rewrite toBlocks_equation. trivial. }
Qed.