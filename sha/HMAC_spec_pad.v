Set Implicit Arguments.

Require Import Coqlib.
Require Import Coq.Program.Basics. (* for function composition: ∘ *)
Require Import List. Import ListNotations.
Require Import Integers.
Require Import general_lemmas.
Require Import hmac_pure_lemmas.
Require Import ByteBitRelations.
Require Import HMAC_common_defs.

Module HMAC_Pad.

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
  bytesToBits (intlist_to_Zlist l).

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
  rewrite -> intlist_to_Zlist_app in concat_eq.
  rewrite -> bytesToBits_app in concat_eq.

  assert (back = skipn b (front ++ back)).
    rewrite skipn_exact; trivial.
  assert (bytesToBits (intlist_to_Zlist BACK) = skipn b (front ++ back)).
    rewrite concat_eq; clear concat_eq. 
    rewrite skipn_exact; trivial.
    rewrite bytesToBits_len, length_intlist_to_Zlist, F_len. omega.
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
  rewrite -> intlist_to_Zlist_app in concat_eq.
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

Lemma hash_block_equiv shah hashblock
     (HHB: shah= fun rgs bl => intsToBits (hashblock (bitsToInts rgs) (bitsToInts bl))):
  forall (bits : Blist) (bytes : list Z)
         (regs : Blist) REGS,
    Forall isbyteZ bytes ->
    regs = bytesToBits (intlist_to_Zlist REGS) ->
    bits = bytesToBits bytes ->
    shah regs bits =
    bytesToBits (intlist_to_Zlist
                   (hashblock REGS (Zlist_to_intlist bytes))).
Proof.
  intros bits bytes regs REGS bytes_inrange regs_eq input_eq.
  subst shah. unfold intsToBits.
  apply f_equal.
  apply f_equal.
  rewrite -> regs_eq; clear regs_eq.
  rewrite -> input_eq; clear input_eq.
  unfold bitsToInts.
  rewrite bytes_bits_bytes_id.
  rewrite -> bytes_bits_bytes_id.
  rewrite -> intlist_to_Zlist_to_intlist.
  reflexivity.
  * apply bytes_inrange.
  * apply isbyte_intlist_to_Zlist. 
Qed.

(*shah = sha_h, hashblock=hash_block, hashblocks=hash_blocks *)
Lemma fold_equiv_blocks b (B:(0<b)%nat) d (DB32: (d*32)%nat=b)
      shah hashblock hashblocks
     (HHB: shah= fun rgs bl => intsToBits (hashblock (bitsToInts rgs) (bitsToInts bl)))
     (HBS_eq: forall r msg, hashblocks r msg =
       match msg with
       | [] => r
       | _ :: _ => hashblocks (hashblock r (firstn d msg)) (skipn d msg)
       end):
  forall (l : Blist) (acc : Blist)
         (L : list int) (ACC : list int),
      InBlocks b l ->
      InBlocks d L ->
      l = convert L ->
      acc = convert ACC ->
      hash_blocks_bits b B shah acc l = convert (hashblocks ACC L).
Proof. 
  intros l acc L ACC bit_blocks bytes_blocks inputs_eq acc_eq.
  
  revert acc ACC L inputs_eq acc_eq bytes_blocks.
  induction bit_blocks; intros.
  *
    revert acc ACC inputs_eq acc_eq.
    induction bytes_blocks; intros.

    - rewrite HBS_eq.
      rewrite -> hash_blocks_bits_equation.
      apply acc_eq. 
    - rewrite -> H0 in *.
      unfold convert in inputs_eq. 
      destruct front.
      { simpl in H. subst d; omega. }
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

    - clear IHbytes_blocks. intros. rewrite HBS_eq; clear HBS_eq.
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
      + 
        rewrite  (@hash_block_equiv _ _ HHB front0 (intlist_to_Zlist front) acc ACC); auto.
        rewrite -> intlist_to_Zlist_to_intlist.
        reflexivity.
        { apply isbyte_intlist_to_Zlist. }
        { rewrite -> H0 in inputs_eq.
          rewrite -> H2 in inputs_eq.
          apply (front_equiv DB32 back0 back front0 front H1 H inputs_eq). }
     + rewrite -> H0. rewrite -> app_length. rewrite -> H. omega.
     + rewrite -> H2. rewrite -> app_length. rewrite -> H1. omega.
Qed.

Lemma equiv_pad shah shaiv shasplitandpad c p (B: (0< b c p)%nat) d (DB32: (d*32 =b c p)%nat)
      hashblock hashblocks
     (HHB: shah= fun rgs bl => intsToBits (hashblock (bitsToInts rgs) (bitsToInts bl)))
     (HBS_eq: forall r msg, hashblocks r msg =
       match msg with
       | [] => r
       | _ :: _ => hashblocks (hashblock r (firstn d msg)) (skipn d msg)
       end) 
     ir (IVIR: shaiv = convert ir)
       gap (GAP: forall bits, NPeano.divide d (length (gap (bitsToBytes bits))))
       (sap_gap: forall bits, shasplitandpad bits = bytesToBits (intlist_to_Zlist (gap (bitsToBytes bits))))
       HASH
       (HSH: forall (m:list Z), HASH m = intlist_to_Zlist (hashblocks ir (gap m))):
       forall (bits : Blist) (bytes : list Z),
                    bytes_bits_lists bits bytes ->
                    bytes_bits_lists
                      (hash_words_padded c p B shah shaiv shasplitandpad bits)
                      (HASH bytes).
Proof.
  intros bits bytes input_eq.
  unfold hash_words_padded.
  change ((hash_words c p B shah shaiv ∘ shasplitandpad) bits) with
  (hash_words c p B shah shaiv (shasplitandpad bits)).
    unfold hash_words.
    unfold h_star. rewrite HSH; clear HSH. 
    apply bytes_bits_comp_ind.
    { apply isbyte_intlist_to_Zlist. }
    { apply bytes_bits_ind_comp in input_eq.
        { subst bytes. rewrite sap_gap; clear sap_gap.
          eapply (fold_equiv_blocks B DB32 _ _ HHB HBS_eq).
          3: reflexivity.
          3: assumption.
          apply InBlocks_len. rewrite bytesToBits_len, length_intlist_to_Zlist.
             rewrite <- DB32. destruct (GAP bits). rewrite H. exists x.
             rewrite mult_comm, mult_assoc.
             assert ((8*4= 32)%nat) by omega. rewrite H0. rewrite mult_comm, <- mult_assoc. trivial.
          apply InBlocks_len. apply GAP.
        } 
        apply (bytesBitsLists_isbyteZ _ _ input_eq).
    }
Qed.

End HMAC_Pad.
