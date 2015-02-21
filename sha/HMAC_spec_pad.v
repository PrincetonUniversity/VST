Set Implicit Arguments.

Require Import List. Import ListNotations.
Require Import Arith.

Require Import Integers.
Require Import Coqlib.
Require Import sha_padding_lemmas.
Require Import functional_prog.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import SHA256.
Require Import ByteBitRelations.
Require Import XorCorrespondence.
Require Import HMAC_functional_prog. 
Require Import HMAC_common_defs.
Require Import hmac_common_lemmas.
Require Import hmac_pure_lemmas.
(* TODO remove useless imports *)

Require Import Coq.Program.Basics. (* for function composition: ∘ *)

Module HMAC_Pad.

Local Open Scope program_scope.

Section HMAC.

(* b = block size
   c = digest (output) size
   p = padding = b - c (fixed) *)
  Variable c p : nat.
  Definition b := (c + p)%nat.

  (* The compression function *)
  Variable h : Blist -> Blist -> Blist.
  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Blist.
  (* The iteration of the compression function gives a keyed hash function on lists of words. *)

  Definition h_star k (m : Blist) :=
    hash_blocks_bits h k m.
  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words := h_star iv.

  Variable splitAndPad : Blist -> Blist.

  Definition hash_words_padded : Blist -> Blist :=
    hash_words ∘ splitAndPad.

  (* ----- *)

  Hypothesis splitAndPad_1_1 :
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.

  (* constant-length padding. *)
  Variable fpad : Blist.

  Definition app_fpad (x : Blist) : Blist :=
    x ++ fpad.
  Definition h_star_pad k x :=
    app_fpad (h_star k x).

  (* TODO fix this -- not used by HAMC *)
  Definition GNMAC k m :=
    let (k_Out, k_In) := splitList c k in
    h k_Out (h_star_pad k_In m).

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

Definition GHMAC (k : Blist) :=
  GHMAC_2K (BLxor k opad ++ BLxor k ipad).

Definition HMAC (k : Blist) :=
  HMAC_2K (BLxor k opad ++ BLxor k ipad).

End HMAC.

(* ----------------------------------------------- *)

(*Definition c:nat := (HMAC_progZ.SHA256_.DigestLength * 8)%nat.*)
Definition c:nat := (HP.SHA256.DigestLength * 8)%nat.
Definition p:=(32 * 8)%nat.

Definition sha_iv : Blist :=
  bytesToBits (SHA256.intlist_to_Zlist SHA256.init_registers).

Definition sha_h (regs : Blist) (block : Blist) : Blist :=
  bytesToBits (SHA256.intlist_to_Zlist
                 (SHA256.hash_block (SHA256.Zlist_to_intlist (bitsToBytes regs))
                                     (SHA256.Zlist_to_intlist (bitsToBytes block))
              )).

Definition sha_splitandpad (msg : Blist) : Blist :=
  bytesToBits (sha_padding_lemmas.pad (bitsToBytes msg)).

Definition convert (l : list int) : list bool :=
  bytesToBits (SHA256.intlist_to_Zlist l).


(* ------------------------------------------------- *)
(* Neat conversion functions (TODO move rest of spec over *)

(*
Definition c := (HMAC_progZ.SHA256.DigestLength * 8)%nat.
Definition p := (32 * 8)%nat.

Definition intsToBits (l : list int) : list bool :=
  bytesToBits (SHA256.intlist_to_Zlist l).

Definition bitsToInts (l : Blist) : list int :=
  SHA256.Zlist_to_intlist (bitsToBytes l).

Definition sha_iv : Blist :=
  intsToBits SHA256.init_registers.

Definition sha_h (regs : Blist) (block : Blist) : Blist :=
  intsToBits (SHA256.hash_block (bitsToInts regs) (bitsToInts block)).

Definition sha_splitandpad (msg : Blist) : Blist :=
  bytesToBits (sha_padding_lemmas.pad (bitsToBytes msg)).
*)


(* -------------------------------------------------------- LEMMAS *)

(* Lemma 1: ++ equivalence on list *)
(* Lemma 2: xor equivalence on list *)
(* Lemma 3: SHA (iterated hash) equivalence on list *)

Lemma concat_equiv :
  forall (l1 : Blist) (l2 : list Z) (m1 : Blist) (m2 : list Z),
    bytes_bits_lists l1 l2
    -> bytes_bits_lists m1 m2
    -> bytes_bits_lists (l1 ++ m1) (l2 ++ m2).
Proof.
  intros l1 l2 m1 m2.
  intros fst_eq snd_eq.
  generalize dependent m1. generalize dependent m2.
  induction fst_eq; intros.
  - repeat rewrite app_nil_l.
    apply snd_eq.
  - simpl.
    apply eq_cons.
    + apply IHfst_eq.
      apply snd_eq.
    + apply H.
Qed.

(* --------------------------------- *)

(* Lemma 2 *)

(* Prove that the inner xor lemma is true on at least one example *)
Section XOR_Example.

 Definition k:Blist := concat (list_repeat 64 [true; true; false; false; true; false; true; true]).
 Definition K:list Z := list_repeat 64 211.

 Lemma conv : convertByteBits [true; true; false; false; true; false; true; true] 211.
   repeat eexists.
  (* eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists. *)
  (* split. reflexivity. simpl. reflexivity. *)
 Qed.
 Lemma kKcorrect: bytes_bits_lists k K.
   unfold K, k. simpl.
   repeat constructor; try apply conv.
  Qed.


 Definition ip:Blist := concat (list_repeat 64 [false; true; false; false; true; false; true; true]).
 Definition IP:Z := 210.
 Transparent Byte.repr.

Definition byte_to_64list (byte : byte) : list Z :=
   (*map Byte.unsigned (HMAC_progZ.HMAC_SHA256.sixtyfour byte).*)
   map Byte.unsigned (HP.HMAC_SHA256.sixtyfour byte).

 Lemma ip_conv : convertByteBits [false; true; false; false; true; false; true; true] 210.
   repeat eexists.
 Qed.
 Lemma ipcorrect: bytes_bits_lists ip (HP.HMAC_SHA256.sixtyfour IP).
   unfold ip, IP. simpl. unfold byte_to_64list, HP.HMAC_SHA256.sixtyfour. simpl.
   repeat constructor; try apply ip_conv.
  Qed.

Lemma ONE: convertByteBits [true; false; false; false; false; false; false; false] 1.
  repeat eexists. Qed.

Lemma inner_fst_equiv_example : exists k (ip  : Blist) K (IP : Z),
                          ((length K) * 8)%nat = (c + p)%nat /\
                          Zlength K = Z.of_nat HP.SHA256.BlockSize /\
                          (* TODO: first implies this *)
                          bytes_bits_lists k K /\
                          bytes_bits_lists ip (HP.HMAC_SHA256.sixtyfour IP) /\
                          bytes_bits_lists (BLxor k ip)
                                           ((HP.HMAC_SHA256.mkArgZ (map Byte.repr (HP.HMAC_SHA256.mkKey K)) (Byte.repr IP))).

Proof.
  exists k, ip, K, IP. repeat split.
   apply kKcorrect. apply ipcorrect.
  unfold k, K, ip, IP. simpl. unfold BLxor. simpl.
  repeat constructor; apply ONE.
Qed.

End XOR_Example.

(* See XorCorrespondence.v *)

(*
Lemma inner_general_map : forall (ip : Blist) (IP_list : list Z) (k : Blist) (K : list Z),
                            bytes_bits_lists ip IP_list ->
                            bytes_bits_lists k K ->
     bytes_bits_lists (BLxor k ip)
                      (map (fun p0 : Z * Z => Z.lxor (fst p0) (snd p0))
                           (combine K IP_list)).
Proof.
  intros ip IP_list k K ip_eq k_eq.
  unfold BLxor. simpl.
  generalize dependent ip. generalize dependent IP_list.
  induction k_eq; intros.
  - simpl. constructor.
  -
    induction ip_eq.
    +
      simpl. constructor.
    +
      simpl.
      constructor.
      * apply IHk_eq.
        apply ip_eq.
      *
        apply xor_correspondence.
        apply H. apply H0.
Qed.*)
Lemma inner_general_mapByte : forall (ip : Blist) (IP_list : list byte) (k : Blist) (K : list byte),
                            bytes_bits_lists ip (map Byte.unsigned IP_list) ->
                            bytes_bits_lists k (map Byte.unsigned K) ->
     bytes_bits_lists (BLxor k ip)
                      (map Byte.unsigned
                           (map (fun p0 : byte * byte => Byte.xor (fst p0) (snd p0))
                                (combine K IP_list))).
Proof.
  intros ip IP_list k K ip_eq k_eq.
  unfold BLxor. simpl.
  remember (map Byte.unsigned IP_list). remember (map Byte.unsigned K) as KL.
  generalize dependent K. generalize dependent IP_list. generalize dependent ip. generalize dependent l.
  induction k_eq.
  - simpl; intros. destruct K0; simpl in *. constructor. discriminate.
  - intros l ip ip_eq.
    induction ip_eq; simpl; intros.
    + destruct IP_list; simpl in *. 2: discriminate.
      destruct K0; simpl in *. discriminate. constructor.
    + destruct IP_list. discriminate. simpl in Heql. inversion Heql; clear Heql. subst byte0 bytes0.
      destruct K0; simpl in HeqKL. discriminate. inversion HeqKL; clear HeqKL; subst.
      simpl.
      constructor.
      * eapply IHk_eq; try reflexivity.
        apply ip_eq.
      * unfold Byte.xor. rewrite Byte.unsigned_repr.
        apply xor_correspondence. apply H. apply H0.
        destruct (@isbyteZ_xor (Byte.unsigned i0) (Byte.unsigned i)).
        apply isByte_ByteUnsigned.
        apply isByte_ByteUnsigned. 
        assert (BMU: Byte.max_unsigned = 255). reflexivity. omega.
Qed.

Lemma SF_ByteRepr x: isbyteZ x ->
                     HP.HMAC_SHA256.sixtyfour x = 
                     map Byte.unsigned (HP.HMAC_SHA256.sixtyfour (Byte.repr x)).
Proof. intros. unfold HP.HMAC_SHA256.sixtyfour.
 rewrite pure_lemmas.map_list_repeat.
 rewrite Byte.unsigned_repr; trivial. destruct H. 
 assert (BMU: Byte.max_unsigned = 255). reflexivity. omega.
Qed.

Lemma xor_equiv_byte: forall xpad XPAD k K, isbyteZ XPAD ->
                          bytes_bits_lists xpad (HP.HMAC_SHA256.sixtyfour XPAD) ->
                          ((length K) * 8)%nat = (c + p)%nat ->
                          bytes_bits_lists k (map Byte.unsigned K) ->
bytes_bits_lists (BLxor k xpad) (HP.HMAC_SHA256.mkArgZ K (Byte.repr XPAD)).
Proof. intros.  apply inner_general_mapByte; try assumption.
       rewrite <- SF_ByteRepr; trivial.
Qed.
(*      unfold HP.HMAC_SHA256.sixtyfour. 
  intros xpad XPAD k K.
  intros xpad_equiv len_k (*zlen_k*) k_equiv.
  unfold HP.HMAC_SHA256.mkArgZ, HP.HMAC_SHA256.mkArg, HP.HMAC_SHA256.mkKey.
  apply inner_general_mapByte. assumption.
  unfold HP.HMAC_SHA256.sixtyfour.
  apply inner_general_mapByte.
  simpl. (*rewrite zlen_k. simpl.*) unfold HP.HMAC_SHA256.zeroPad.
  assert (byte_key_length_blocksize: length K = 64%nat).
    * unfold p, c in *. simpl in *. omega.
  *
    rewrite byte_key_length_blocksize.  simpl.  rewrite app_nil_r.
    apply inner_general_map.

  - apply xpad_equiv.
  - apply k_equiv.
Qed.*)

(*
Lemma xor_equiv_Z : forall (xpad  : Blist) (XPAD : Z)
                                           (k : Blist) (K : list Z),
                          bytes_bits_lists xpad (HP.HMAC_SHA256.sixtyfour XPAD) ->
                          ((length K) * 8)%nat = (c + p)%nat ->
                          Zlength K = Z.of_nat HP.SHA256.BlockSize ->
                          (* TODO: first implies this *)
                          bytes_bits_lists k K ->
                          bytes_bits_lists (BLxor k xpad)
       (HP.HMAC_SHA256.mkArgZ (map Byte.repr (HP.HMAC_SHA256.mkKey K)) (Byte.repr XPAD)).
Proof.
  intros xpad XPAD k K.
  intros xpad_equiv len_k zlen_k k_equiv.
  unfold HP.HMAC_SHA256.mkArgZ, HP.HMAC_SHA256.mkArg, HP.HMAC_SHA256.mkKey.
  Opaque HP.HMAC_SHA256.sixtyfour.
  simpl. rewrite zlen_k. simpl. unfold HP.HMAC_SHA256.zeroPad.
  assert (byte_key_length_blocksize: length K = 64%nat).
    * unfold p, c in *. simpl in *. omega.
  *
    rewrite byte_key_length_blocksize.  simpl.  rewrite app_nil_r.
    apply inner_general_map.

  - apply xpad_equiv.
  - apply k_equiv.
Qed.*)

(* ------------------------------------------------------ *)
(* Lemma 3 *)

(* --- abstract version *)

Parameter A B : Type.
Parameter convert_BA : B -> A.
Parameter convert_AB : A -> B.

Fixpoint iterate {A : Type} (n : nat) (f : A -> A) (x : A) :=
  match n with
    | O => x
    | S n' => f (iterate n' f x) (* or [iterate n' f (f x)] *)
  end.

Definition id {X : A} (x : A) : A := x.
Definition wrap (F : B -> B) : A -> A :=
  convert_BA ∘ F ∘ convert_AB.
Definition roundtrip : B -> B :=
  convert_AB ∘ convert_BA.

Lemma roundtrip_id :
  forall (X : B), convert_AB (convert_BA X) = X.
Proof. Admitted. (* Axiom *)

Lemma once_eq :
    forall (x : A) (X : B) (f : A -> A) (F : B -> B),
      x = convert_BA X ->
      f = wrap F ->
      X = roundtrip X ->
      f x = convert_BA (F X).
Proof.
  intros x X f F inputs_eq f_def roundtrip_id.
  unfold roundtrip in *.
  rewrite -> inputs_eq.
  rewrite -> f_def.
  unfold wrap in *.
  change ((convert_BA ∘ F ∘ convert_AB) (convert_BA X)) with
    (convert_BA (F ((convert_AB ∘ convert_BA) X))).
  rewrite <- roundtrip_id.
  reflexivity.
Qed.

(* a simplified version of fold_equiv *)
Lemma iterate_equiv :
  forall (x : A) (X : B) (f : A -> A) (F : B -> B) (n : nat),
    x = convert_BA X ->
    f = wrap F ->
    X = roundtrip X ->
    iterate n f x = convert_BA (iterate n F X).
Proof.
  intros. revert x X f F H H0 H1.
  induction n as [ | n']; intros x X f F input_eq func_wrap roundtrip';
  unfold wrap in *; unfold roundtrip in *.
  -
    simpl. apply input_eq.
  -
    simpl.
    pose proof once_eq as once_eq.
    apply once_eq.
    apply IHn'; assumption.
    * unfold wrap. apply func_wrap.
    * symmetry. apply roundtrip_id.
Qed.

(* ----- concrete version *)

(* Definition of InBlocks in sha_padding_lemmas *)

Lemma bitsToByte_cons: forall bits h t, (h::t) = bitsToBytes bits -> 
      exists b0, exists b1, exists b2, exists b3, 
      exists b4, exists b5, exists b6, exists b7, exists xs,
      bits = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: xs /\
      h = bitsToByte [b0; b1; b2; b3; b4; b5; b6; b7] /\
      t = bitsToBytes xs.
Proof. intros.
  destruct bits. inv H.
  destruct bits. inv H.
  destruct bits. inv H.
  destruct bits. inv H.
  destruct bits. inv H.
  destruct bits. inv H.
  destruct bits. inv H.
  destruct bits; inv H.
  eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
  split. reflexivity.
  split; reflexivity.
Qed.

(* Lemmas stating that various operations result in bytes in range *)

Lemma bitsToByte_isbyteZ b0 b1 b2 b3 b4 b5 b6 b7:
      isbyteZ (bitsToByte [b0; b1; b2; b3; b4; b5; b6; b7]).
Proof. simpl. unfold asZ, isbyteZ.
  destruct b0; destruct b1; destruct b2; destruct b3;
  destruct b4; destruct b5; destruct b6; destruct b7; simpl; omega.
Qed.

Lemma bitsToBytes_isbyteZ: forall bytes bits,
                             bytes = bitsToBytes bits -> Forall isbyteZ bytes.
Proof. intros bytes.
  induction bytes; simpl; intros.
     constructor.
  apply bitsToByte_cons in H.
  destruct H as [b0 [b1 [b2 [b3 [b4 [b5 [b6 [b7 [xs [BITS [A BYTES]]]]]]]]]]].
  constructor.
     subst. apply bitsToByte_isbyteZ.
     eauto. 
Qed.

Lemma convertByteBits_isbyteZ b0 b1 b2 b3 b4 b5 b6 b7 byte:
      convertByteBits [b0; b1; b2; b3; b4; b5; b6; b7] byte ->
      isbyteZ byte.
Proof. intros.
  destruct H as [b8 [b9 [b10 [b11 [b12 [b13 [b14 [b15 [BITS ZZ]]]]]]]]].
  inversion BITS. subst. clear BITS.
  unfold asZ, isbyteZ.
  destruct b8; destruct b9; destruct b10; destruct b11;
  destruct b12; destruct b13; destruct b14; destruct b15; simpl; omega.
Qed.

Lemma bytesBitsLists_isbyteZ bytes bits: bytes_bits_lists bits bytes -> Forall isbyteZ bytes.
Proof. intros.
  induction H. constructor.
  constructor; trivial. eapply convertByteBits_isbyteZ. apply H0. 
Qed.

Lemma pad_isbyteZ: forall l, Forall isbyteZ l -> Forall isbyteZ (pad l).
Proof. intros. unfold pad.
  apply pure_lemmas.Forall_app.
  split; trivial.
  apply pure_lemmas.Forall_app.
  split. constructor. unfold isbyteZ; omega. constructor. 
  apply pure_lemmas.Forall_app.
  split. apply pure_lemmas.Forall_list_repeat. unfold isbyteZ; omega.
  apply pure_lemmas.isbyte_intlist_to_Zlist.
Qed.  

(* --------------------------- end bytes/bits proofs *)

Lemma splitandpad_equiv : forall (bits : Blist) (bytes : list Z),
                            bytes_bits_lists bits bytes ->
                            bytes_bits_lists
                              (sha_splitandpad bits)
                              (sha_padding_lemmas.pad bytes).
Proof.
  intros bits bytes inputs_eq.
  unfold concat.
  unfold sha_splitandpad.
  specialize (bytesBitsLists_isbyteZ inputs_eq). intros isbyteZ_Bytes.

  apply bytes_bits_ind_comp in inputs_eq. 2: apply isbyteZ_Bytes.
  rewrite inputs_eq.
  apply bytes_bits_def_eq.
  rewrite <- inputs_eq. apply pad_isbyteZ. trivial.
Qed.

Lemma hash_block_equiv :
  forall (bits : Blist) (bytes : list Z)
         (regs : Blist) (REGS : SHA256.registers),
    Forall isbyteZ bytes ->
    (length bits)%nat = 512%nat ->
    (length bytes)%nat = 64%nat -> (* removes firstn 16 (Zlist->intlist bytes) *)

    regs = bytesToBits (SHA256.intlist_to_Zlist REGS) ->
    bits = bytesToBits bytes ->

    sha_h regs bits =
    bytesToBits (SHA256.intlist_to_Zlist
                   (SHA256.hash_block REGS
                                      (SHA256.Zlist_to_intlist bytes))).
Proof.
  intros bits bytes regs REGS bytes_inrange bits_blocksize bytes_blocksize regs_eq input_eq.
  unfold sha_h.
  apply f_equal.
  apply f_equal.

  rewrite -> regs_eq.
  rewrite -> input_eq.
  rewrite -> bytes_bits_bytes_id.
  rewrite -> bytes_bits_bytes_id.
  rewrite -> pure_lemmas.intlist_to_Zlist_to_intlist.
  reflexivity.
  * apply bytes_inrange.
  * apply pure_lemmas.isbyte_intlist_to_Zlist. 
Qed.

(* Front/back equivalence theorems *)

(*NEW proof*) Lemma front_equiv :
  forall (back : Blist) (BACK : list int) (front : Blist) (FRONT : list int),
    (length front)%nat = 512%nat ->
    (length FRONT)%nat = 16%nat ->
    front ++ back = convert (FRONT ++ BACK) ->
    front = convert FRONT.
Proof.
  intros back BACK front FRONT f_len F_len concat_eq.
  unfold convert in *.
  rewrite -> pure_lemmas.intlist_to_Zlist_app in concat_eq.
  rewrite -> bytesToBits_app in concat_eq.

  assert (back = skipn 512 (front ++ back)).
    rewrite skipn_exact; trivial.
  assert (bytesToBits (intlist_to_Zlist BACK) = skipn 512 (front ++ back)).
    rewrite concat_eq; clear concat_eq. 
    rewrite skipn_exact; trivial.
    rewrite bytesToBits_len, pure_lemmas.length_intlist_to_Zlist, F_len; omega.
  rewrite H, H0 in concat_eq; clear H H0.
  eapply app_inv_tail. eassumption.
Qed. 

Lemma back_equiv :
  forall (back : Blist) (BACK : list int) (front : Blist) (FRONT : list int),
    (length front)%nat = 512%nat ->
    (length FRONT)%nat = 16%nat ->
    front ++ back = convert (FRONT ++ BACK) ->
    back = convert BACK.
Proof.
  intros back BACK front FRONT f_len F_len concat_eq.
  assert (front ++ back = convert (FRONT ++ BACK)) as concat_eq'. apply concat_eq.
  unfold convert in *.
  rewrite -> pure_lemmas.intlist_to_Zlist_app in concat_eq.
  rewrite -> bytesToBits_app in concat_eq.

  assert (front_eq : front = convert FRONT).
    pose proof front_equiv back BACK front FRONT.
    apply H.
    * assumption.
    * assumption.
    * apply concat_eq'.
    * rewrite -> front_eq in concat_eq.
      unfold convert in *.
      eapply app_inv_head. eassumption.
Qed.

(* --------- *)
    
(* it's more of an iteration theorem than a fold theorem *)
(* conversion function: bytesToBits @ SHA256.intlist_to_Zlist *)
Lemma fold_equiv_blocks :
  forall (l : Blist) (acc : Blist)
         (L : list int) (ACC : list int),
    (* length assumptions about list *)
      InBlocks 512 l ->
      InBlocks 16 L ->
      l = convert L ->
      acc = convert ACC ->
      hash_blocks_bits sha_h acc l = convert (SHA256.hash_blocks ACC L).
Proof.
  intros l acc L ACC bit_blocks bytes_blocks inputs_eq acc_eq.
  
  revert acc ACC L inputs_eq acc_eq bytes_blocks.
  induction bit_blocks; intros.
  *
    revert acc ACC inputs_eq acc_eq.
    induction bytes_blocks; intros.

    -                             (* both empty *)
      rewrite -> SHA256.hash_blocks_equation.
      rewrite -> hash_blocks_bits_equation.
      apply acc_eq.

    -
      rewrite -> H0 in *.
      unfold convert in inputs_eq. 
      destruct front.
      { inversion H. }
      { simpl in inputs_eq. inversion inputs_eq. }

  *
    revert front back full H H0 bit_blocks IHbit_blocks acc ACC
           inputs_eq acc_eq.
    induction bytes_blocks; intros.
    (* TODO: clear IHbytes_blocks *)

    -
      simpl in inputs_eq.
      rewrite -> H0 in inputs_eq.
      unfold convert in inputs_eq.
      destruct front.
      { inversion H. }
      { simpl in inputs_eq. inversion inputs_eq. }

    - 
      rewrite -> SHA256.hash_blocks_equation.
      rewrite -> hash_blocks_bits_equation.
      repeat rewrite -> length_not_emp.

      rewrite -> H0.
      rewrite -> H2.
      (* TODO: generalize these (it's true by hyp) *)
      assert (H_first_512 : firstn 512 (front0 ++ back0) = front0).
        apply firstn_exact. assumption.
      assert (H_skip_512 : skipn 512 (front0 ++ back0) = back0).
        apply skipn_exact. assumption.
      assert (H_first_16 : firstn 16 (front ++ back) = front).
        apply firstn_exact. assumption.
      assert (H_skip_16 : skipn 16 (front ++ back) = back).
        apply skipn_exact. assumption.

      rewrite -> H_first_512.
      rewrite -> H_skip_512.
      rewrite -> H_first_16.
      rewrite -> H_skip_16.

      apply IHbit_blocks; auto; clear IHbytes_blocks IHbit_blocks.
      +
        rewrite -> H0 in inputs_eq.
        rewrite -> H2 in inputs_eq.
        apply (back_equiv back0 back front0 front H1 H inputs_eq).
      + 
        pose proof hash_block_equiv as hash_block_equiv.
        specialize (hash_block_equiv front0 (SHA256.intlist_to_Zlist front) acc ACC).
        rewrite -> hash_block_equiv; auto. clear hash_block_equiv.
        rewrite -> pure_lemmas.intlist_to_Zlist_to_intlist.
        reflexivity.
        { apply pure_lemmas.isbyte_intlist_to_Zlist. }
        {
          rewrite -> pure_lemmas.length_intlist_to_Zlist.
          rewrite -> H.
          omega.
        }
        {
          rewrite -> H0 in inputs_eq.
          rewrite -> H2 in inputs_eq.

          (*NEW*) apply (front_equiv back0 back front0 front H1 H inputs_eq).
        }
     +
       rewrite -> H0. rewrite -> app_length. rewrite -> H. omega.
     +
       rewrite -> H2. rewrite -> app_length. rewrite -> H1. omega.
Qed.

Lemma SHA_equiv_pad : forall (bits : Blist) (bytes : list Z),
                    bytes_bits_lists bits bytes ->
                    bytes_bits_lists
                      (hash_words_padded sha_h sha_iv sha_splitandpad bits)
                      (HP.SHA256.Hash bytes).

Proof.
  intros bits bytes input_eq.
  unfold HP.SHA256.Hash.
  rewrite -> functional_prog.SHA_256'_eq.
  unfold SHA256.SHA_256.
  unfold hash_words_padded.
  change ((hash_words sha_h sha_iv ∘ sha_splitandpad) bits) with
  (hash_words sha_h sha_iv (sha_splitandpad bits)).

  -
    repeat rewrite <- sha_padding_lemmas.pad_compose_equal in *.
    unfold sha_padding_lemmas.generate_and_pad' in *.
    unfold hash_words.
    unfold h_star.

    pose proof splitandpad_equiv as splitandpad_equiv.
    specialize (splitandpad_equiv bits bytes input_eq).

      apply bytes_bits_comp_ind.
      pose proof fold_equiv_blocks as fold_equiv_blocks.
      apply pure_lemmas.isbyte_intlist_to_Zlist. 
      (* TODO: in-range preserved by hash_blocks and intlist_to_Zlist *)
      apply fold_equiv_blocks.
      *                         (* padding -> blocks of 512 *)
        unfold sha_splitandpad in *.
        apply bytes_bits_length in input_eq.
        pose proof pad_len_64_nat (bitsToBytes bits) as pad_len_64.
        apply InBlocks_len.
        rewrite -> bytesToBits_len.
        (* eexists. *)
        destruct pad_len_64.
        rewrite -> H.
        exists x.
        omega.
      *
        pose proof pad_len_64_nat bytes as pad_len_64.
        apply InBlocks_len.
        destruct pad_len_64.

        assert (H' : length (pad bytes) = (Z.to_nat WORD * (16 * x))%nat).
          rewrite -> H.
          assert (Z.to_nat WORD = 4%nat) by reflexivity.
          rewrite -> H0.
          omega.

        apply pure_lemmas.length_Zlist_to_intlist in H'.
        rewrite H'.
        eexists x.
        omega.

      * unfold sha_splitandpad.
        unfold convert.
        rewrite -> pure_lemmas.Zlist_to_intlist_to_Zlist.
        f_equal.
        apply bytes_bits_ind_comp in input_eq.
        rewrite -> input_eq.
        reflexivity.
        + 
          eapply bytesBitsLists_isbyteZ. eassumption.
        +
          pose proof pad_len_64_nat bytes as pad_len_64.
          destruct pad_len_64.
          rewrite -> H.
          assert (four : Z.to_nat WORD = 4%nat) by reflexivity.
          rewrite -> four.
          exists (x * 16)%nat.
          omega.
        + apply pad_isbyteZ. eapply bytesBitsLists_isbyteZ. eassumption.

     * unfold sha_iv. reflexivity.
Qed.

(* --------------------------------------- *)

(* MAIN THEOREM *)

(* Relates the HMAC padded spec to the HMAC functional program (version that uses Z) *)
Theorem HMAC_Pad_Concrete_equiv : forall
                            (K : list byte) (M H : list Z) (OP IP : Z)
                            (k m h : Blist) (op ip : Blist) (ipByte: isbyteZ IP) (opByte: isbyteZ OP),
  ((length K) * 8)%nat = (c + p)%nat ->
  Zlength K = Z.of_nat HP.SHA256.BlockSize ->
  (* TODO: first implies this *)
  bytes_bits_lists k (map Byte.unsigned K) ->
  bytes_bits_lists m M ->
  bytes_bits_lists op (HP.HMAC_SHA256.sixtyfour OP) ->
  bytes_bits_lists ip (HP.HMAC_SHA256.sixtyfour IP) ->
  HMAC c p sha_h sha_iv sha_splitandpad op ip k m = h ->
  HP.HMAC_SHA256.HmacCore (Byte.repr IP) (Byte.repr OP) M K = H ->
  bytes_bits_lists h H.
Proof.
  intros K M H OP IP k m h op ip ipByte opByte.
  intros padded_key_len padded_key_len_byte padded_keys_eq msgs_eq ops_eq ips_eq.
  intros HMAC_abstract HMAC_concrete.

  intros.
  unfold p, c in *.
  simpl in *.

  rewrite <- HMAC_abstract. rewrite <- HMAC_concrete.

  unfold HMAC. unfold HP.HMAC_SHA256.HmacCore. unfold HP.HMAC_SHA256.OUTER. unfold HP.HMAC_SHA256.INNER.
  unfold HP.HMAC_SHA256.outerArg. unfold HP.HMAC_SHA256.innerArg.

  unfold HMAC_2K. unfold GHMAC_2K. rewrite -> split_append_id.

  simpl.
  
  (* Major lemmas *)
  apply SHA_equiv_pad.
  apply concat_equiv.
  apply xor_equiv_byte; trivial. 

  *
    apply SHA_equiv_pad.
    apply concat_equiv.

  - apply xor_equiv_byte; trivial.
  - assumption.
    (* xors preserve length : TODO factor this out*)
    *
      (* Locate padded_keys_eq. *)
      unfold b in *. simpl. unfold BLxor. rewrite -> list_length_map.
      rewrite -> combine_length.
      erewrite bytes_bits_length; try eassumption. rewrite map_length, padded_key_len.
      apply Min.min_l. erewrite bytes_bits_length; try eassumption.
      unfold HP.HMAC_SHA256.sixtyfour.
      rewrite -> length_list_repeat. unfold HP.SHA256.BlockSize; simpl; omega.
(*      pose proof bytes_bits_length op (HP.HMAC_SHA256.sixtyfour OP) as ops_len.
      rewrite -> ops_len.
      pose proof bytes_bits_length k (map Byte.unsigned K) as keys_len.
      (*rewrite -> keys_len. *)
      rewrite -> padded_key_len.
      Transparent HMAC_progZ.HMAC_SHA256.sixtyfour.
      unfold HMAC_progZ.HMAC_SHA256.sixtyfour.
      rewrite -> length_list_repeat.
      reflexivity.
      apply padded_keys_eq.     (* given: bytes_bits_lists k K *)
      apply ops_eq.             (* given: bytes_bits_lists op (64 OP) *)
*)
    *
      unfold b in *. simpl. unfold BLxor. rewrite -> list_length_map.
      rewrite -> combine_length.
      erewrite bytes_bits_length; try eassumption. rewrite map_length, padded_key_len.
      apply Min.min_l. erewrite bytes_bits_length; try eassumption.
      unfold HP.HMAC_SHA256.sixtyfour.
      rewrite -> length_list_repeat. unfold HP.SHA256.BlockSize; simpl; omega.
(*
      unfold b in *. simpl. unfold BLxor. rewrite -> list_length_map.
      rewrite -> combine_length.
      pose proof bytes_bits_length ip (HMAC_progZ.HMAC_SHA256.sixtyfour IP) as ips_len.
      rewrite -> ips_len.
      pose proof bytes_bits_length k K as keys_len.
      rewrite -> keys_len.
      rewrite -> padded_key_len.
      unfold HMAC_progZ.HMAC_SHA256.sixtyfour.
      rewrite -> length_list_repeat.
      reflexivity.
      apply padded_keys_eq.
      apply ips_eq.*)
Qed.

Lemma isbyte_hmaccore ipad opad m k: 
   Forall isbyteZ (HP.HMAC_SHA256.HmacCore (Byte.repr ipad) (Byte.repr opad) m k).
Proof. apply isbyte_sha. Qed.

Theorem HMAC_Pad_Concrete_equiv' : forall
                            (K : list byte) (M : list Z) (OP IP : Z)
                            (k m : Blist) (op ip : Blist) (ipByte: isbyteZ IP) (opByte: isbyteZ OP),
  ((length K) * 8)%nat = (c + p)%nat ->
  Zlength K = Z.of_nat HP.SHA256.BlockSize ->
  (* TODO: first implies this *)
  bytes_bits_lists k (map Byte.unsigned K) ->
  bytes_bits_lists m M ->
  bytes_bits_lists op (HP.HMAC_SHA256.sixtyfour OP) ->
  bytes_bits_lists ip (HP.HMAC_SHA256.sixtyfour IP) ->
  HMAC c p sha_h sha_iv sha_splitandpad op ip k m = 
  bytesToBits (HP.HMAC_SHA256.HmacCore (Byte.repr IP) (Byte.repr OP) M K).
Proof. intros.  
  exploit HMAC_Pad_Concrete_equiv. apply ipByte. apply opByte.
      apply H. assumption. apply H1. apply H2. apply H3. apply H4.
  reflexivity. reflexivity.
  intros.
  apply bits_bytes_ind_comp. 2: assumption.
  apply isbyte_hmaccore.
Qed.

End HMAC_Pad.
(* TODO move this End to the end of the spec definition + rename and recompile things *)
