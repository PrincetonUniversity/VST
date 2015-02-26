Require Import Coqlib.
Require Import Bvector.
Require Import List.
Require Import Integers.
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
Require Import sha_padding_lemmas.
Require Import SHA256.
Require Import pure_lemmas.
Require Import HMAC_equivalence.

Lemma splitAndPad_v_to_sha_splitandpad_blocks l:
   map Vector.to_list (splitAndPad_v l) = sha_splitandpad_blocks l.
Proof. apply Forall2_map. apply length_splitandpad_inner. Qed.

Lemma splitAndPad_v_eq_inverse: forall l m, splitAndPad_v l = splitAndPad_v m ->
      sha_splitandpad_blocks l = sha_splitandpad_blocks m.
Proof. intros. do 2 rewrite <- splitAndPad_v_to_sha_splitandpad_blocks.
  rewrite H. trivial.
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
    apply cons_inv in Heql; destruct Heql. subst a l.

    inversion F2; clear F2. rewrite H4 in BLKS. 
    assert (L2: (511 < length (front0 ++ back0))%nat).
      rewrite app_length, H3. omega.
    rewrite leb_correct_conv in BLKS; trivial.
    rewrite firstn_exact in BLKS; trivial.
    rewrite skipn_exact in BLKS; trivial.
    apply cons_inv in BLKS; destruct BLKS. subst front0 full0 full.
    specialize (IHl _ H8 _ (eq_refl _) H5 H1). subst back0.
    rewrite <- H4 in H0. assumption.
Qed.
 
Lemma bytesToBits_nil_inv l: nil = bytesToBits l -> l = nil.
Proof. destruct l; trivial. simpl; intros. discriminate. Qed.  

Lemma bytesToBits_cons b l:
      bytesToBits (b::l) = byteToBits b ++ bytesToBits l.
Proof. reflexivity. Qed.

Lemma byteToBits_injective: forall a b,
      byteToBits a = byteToBits b ->
      isbyteZ a -> isbyteZ b -> a = b. 
Proof. intros. unfold isbyteZ in *. 
assert (bitsToByte (byteToBits a) = bitsToByte (byteToBits b)).
  rewrite H; trivial.
clear H.
rewrite byte_bit_byte_id in H2; trivial.
rewrite byte_bit_byte_id in H2; trivial.
Qed.
  
Lemma bytesToBits_injective: forall b1 b2, bytesToBits b1 = bytesToBits b2 -> 
      Forall isbyteZ b1 -> Forall isbyteZ b2 -> b1=b2.
Proof. induction b1.
  intros; destruct b2; trivial. discriminate.
  destruct b2. discriminate.
  do 2 rewrite bytesToBits_cons.
  intros. destruct (app_inj1 _ _ _ _ H). reflexivity.
  rewrite (IHb1 _ H3).
  rewrite (byteToBits_injective _ _ H2). trivial.
    eapply Forall_inv; eassumption.
    eapply Forall_inv; eassumption.
    eapply Forall_tl; eassumption. 
    eapply Forall_tl; eassumption. 
Qed.

Lemma IntModulus32: Int.modulus = 2^32. reflexivity. Qed.

Lemma Intsize_monotone a b: 0 <= Int.unsigned (Int.repr a) <= Int.unsigned (Int.repr b) -> 
                          Int.size (Int.repr a) <= Int.size (Int.repr b).
Proof. apply Int.Zsize_monotone. Qed.
  
Lemma isByte_mono: forall x y, 0<=y<=x -> isbyteZ x -> isbyteZ y.
Proof. intros. destruct H0. split; omega. Qed.

Lemma isbyteZ_pad_inc l (B:Forall isbyteZ l): Forall isbyteZ (pad_inc l).
Proof. unfold pad_inc.
  apply Forall_app. split. trivial. 
  apply Forall_app. split. constructor. split; omega. trivial.
  apply Forall_app. split. apply Forall_list_repeat. split; omega.
  apply isbyte_intlist_to_Zlist.
Qed.

Lemma splitAndPad_1to1 b1 b2: splitAndPad_v b1 = splitAndPad_v b2 -> b1 = b2.
Proof. intros.
  apply splitAndPad_v_eq_inverse in H.
  unfold sha_splitandpad_blocks in H.
  apply toBlocks_injective in H; try apply sha_splitandpad_inc_InBlocks.
  unfold sha_splitandpad_inc in H.
  apply bytesToBits_injective in H. 
    apply pad_inc_injective in H. admit. (*Hole: injectivity of bitsToBytes!!*)
  apply isbyteZ_pad_inc. eapply HMAC_spec_pad.HMAC_Pad.bitsToBytes_isbyteZ. reflexivity.
  apply isbyteZ_pad_inc. eapply HMAC_spec_pad.HMAC_Pad.bitsToBytes_isbyteZ. reflexivity.
Qed.

Lemma opad_ne_ipad : opad_v <> ipad_v.
  intros N. 
  assert (Vector.to_list opad_v = Vector.to_list ipad_v). rewrite N; trivial.
  unfold opad_v, ipad_v in H. 
  repeat rewrite of_length_proof_irrel in H.
  unfold HP.Opad, HP.Ipad in H. simpl in H.
  discriminate.
Qed.

(* A definition of a PRF in the form of a predicate. *)
Set Implicit Arguments.

Require Import FCF.
(*Require Import HMAC_spec.*)
Require Import PRF.
Require Import NMAC_to_HMAC.
Require Import hF.
(*Require Import GHMAC_PRF.
*)
Require Import HMAC_PRF.

Definition isPRF {D R Key:Set} (RndKey:Comp Key) (RndR: Comp R) (f: Key -> D -> R) 
                         (ED:EqDec D) (ER:EqDec R) advantage adversary :=
        PRF_Advantage RndKey RndR f _ _ adversary <= advantage.
(*Section HMAC_is_PRF.*)
Variable tau : Rat.
Variable epsilon : Rat.
Variable sigma : Rat.
Variable A : OracleComp Blist (Bvector c) bool. (*I seem to need this variable here, too*)
(*Hypothesis*)
Parameter A_wf : well_formed_oc A.

(* Assume h is a tau-PRF against adversary (PRF_h_A h_star_pad A_GHMAC) *)
(*Hypothesis*)
Definition h_PRF := isPRF ({ 0 , 1 }^c) ({ 0 , 1 }^c) h_v (Bvector_EqDec (b c p)) (Bvector_EqDec c) tau 
                         (PRF_h_A (h_star_pad h_v fpad_v) 
                                  (HMAC_PRF.A_GHMAC p splitAndPad_v A)).

(* We could make similar predicates for the other definitions, or just
assume the inequalities*)
(*Hypothesis*)
Definition h_star_WCR := cAU.Adv_WCR (list_EqDec (Bvector_EqDec (b c p)))
             (Bvector_EqDec (b c p)) (h_star_pad h_v fpad_v)
       ({ 0 , 1 }^c) (au_F_A (A_GHMAC p splitAndPad_v A)) <= epsilon.

(*Hypothesis*)
Definition dual_h_RKA :=
    RKA_Advantage _ _ _ ({ 0 , 1 }^b c p) ({ 0 , 1 }^c) (dual_f h_v) (BVxor (b c p))
      (HMAC_RKA_A h_v iv_v fpad_v opad_v ipad_v (A_GHMAC p splitAndPad_v A)) <= sigma.

Theorem HMAC_isPRF (HH1: h_PRF) (HH2: h_star_WCR) (HH3: dual_h_RKA):
        isPRF (Rnd (b c p)) (Rnd c) 
              (HMAC h_v iv_v splitAndPad_v
                              fpad_v opad_v ipad_v)
              _ _ (tau + epsilon + sigma) A.
Proof. unfold isPRF.
  specialize (HMAC_PRF h_v iv_v splitAndPad_v splitAndPad_1to1
                              fpad_v opad_ne_ipad A_wf).
  intros.
  eapply leRat_trans. apply H. clear H. 
  unfold h_PRF, isPRF in HH1.
  unfold HMAC_common_defs.b in *. unfold HMAC_spec.b in *. unfold b in *. unfold GHMAC_PRF.b in *. unfold GNMAC_PRF.b in *.  unfold HMAC_spec.b in *.
  remember (@PRF_Advantage (Bvector (c + p)) (Bvector c) (Bvector c) ({ 0 , 1 }^c)
        ({ 0 , 1 }^c) h_v (Bvector_EqDec (c + p)) (Bvector_EqDec c)
        (@PRF_h_A (c + p) c c (@h_star_pad c p h_v fpad_v)
           (@A_GHMAC c p splitAndPad_v A))). clear Heqr.
  unfold h_star_WCR in HH2.
  unfold HMAC_common_defs.b in *. unfold HMAC_spec.b in *. unfold b in *. unfold GHMAC_PRF.b in *. unfold GNMAC_PRF.b in *.  unfold HMAC_spec.b in *.
  remember (@cAU.Adv_WCR (Bvector c) (list (Bvector (c + p))) (Bvector (c + p))
        (@list_EqDec (Bvector (c + p)) (Bvector_EqDec (c + p)))
        (Bvector_EqDec (c + p)) (@h_star_pad c p h_v fpad_v) ({ 0 , 1 }^c)
        (@au_F_A (c + p) c (@A_GHMAC c p splitAndPad_v A))).
  clear Heqr0.
  unfold dual_h_RKA in HH3.
  unfold HMAC_common_defs.b in *. unfold HMAC_spec.b in *. unfold b in *. unfold GHMAC_PRF.b in *. unfold GNMAC_PRF.b in *.  unfold HMAC_spec.b in *.
  remember (@RKA_Advantage (Bvector (c + p)) (Bvector c) (Bvector c)
        (Bvector (c + p)) (Bvector_EqDec (c + p)) (Bvector_EqDec c)
        (Bvector_EqDec c) ({ 0 , 1 }^c + p) ({ 0 , 1 }^c)
        (@dual_f (Bvector c) (Bvector (c + p)) (Bvector c) h_v)
        (BVxor (c + p))
        (@HMAC_RKA_A c p h_v iv_v fpad_v opad_v ipad_v
           (@A_GHMAC c p splitAndPad_v A)) ).
  clear Heqr1.
  rewrite ratAdd_comm. 
  apply ratAdd_leRat_compat; trivial. apply ratAdd_leRat_compat; trivial. (*What's the "omega" tactic for Rat?*)
Qed.

(*Here's the same stuff but enclosed in a section - but uwhen 
  closing the section, Coq runs out of memory...
Section HMAC_is_PRF.
Variable tau : Rat.
Variable epsilon : Rat.
Variable sigma : Rat.
Variable A : OracleComp Blist (Bvector c) bool. (*I seem to need this variable here, too*)
Hypothesis A_wf : well_formed_oc A.

(* Assume h is a tau-PRF against adversary (PRF_h_A h_star_pad A_GHMAC) *)
Hypothesis h_PRF : isPRF ({ 0 , 1 }^c) ({ 0 , 1 }^c) h_v (Bvector_EqDec (b c p)) (Bvector_EqDec c) tau 
                         (PRF_h_A (h_star_pad h_v fpad_v) 
                                  (HMAC_PRF.A_GHMAC p splitAndPad_v A)).

(* We could make similar predicates for the other definitions, or just
assume the inequalities*)
Hypothesis h_star_WCR : cAU.Adv_WCR (list_EqDec (Bvector_EqDec (b c p)))
             (Bvector_EqDec (b c p)) (h_star_pad h_v fpad_v)
       ({ 0 , 1 }^c) (au_F_A (A_GHMAC p splitAndPad_v A)) <= epsilon.

Hypothesis dual_h_RKA :
    RKA_Advantage _ _ _ ({ 0 , 1 }^b c p) ({ 0 , 1 }^c) (dual_f h_v) (BVxor (b c p))
      (HMAC_RKA_A h_v iv_v fpad_v opad_v ipad_v (A_GHMAC p splitAndPad_v A)) <= sigma.

Theorem HMAC_isPRF:
        isPRF (Rnd (b c p)) (Rnd c) 
              (HMAC h_v iv_v splitAndPad_v
                              fpad_v opad_v ipad_v)
              _ _ (tau + epsilon + sigma) A.
Proof. unfold isPRF.
  specialize (HMAC_PRF h_v iv_v splitAndPad_v splitAndPad_1to1
                              fpad_v opad_ne_ipad A_wf).
  intros.
  eapply leRat_trans. apply H. clear H. 
  unfold isPRF in h_PRF.
  unfold HMAC_common_defs.b in *. unfold HMAC_spec.b in *. unfold b in *. unfold GHMAC_PRF.b in *. unfold GNMAC_PRF.b in *.  unfold HMAC_spec.b in *.
  remember (@PRF_Advantage (Bvector (c + p)) (Bvector c) (Bvector c) ({ 0 , 1 }^c)
        ({ 0 , 1 }^c) h_v (Bvector_EqDec (c + p)) (Bvector_EqDec c)
        (@PRF_h_A (c + p) c c (@h_star_pad c p h_v fpad_v)
           (@A_GHMAC c p splitAndPad_v A))). clear Heqr.
  remember (@cAU.Adv_WCR (Bvector c) (list (Bvector (c + p))) (Bvector (c + p))
        (@list_EqDec (Bvector (c + p)) (Bvector_EqDec (c + p)))
        (Bvector_EqDec (c + p)) (@h_star_pad c p h_v fpad_v) ({ 0 , 1 }^c)
        (@au_F_A (c + p) c (@A_GHMAC c p splitAndPad_v A))).
  clear Heqr0.
  remember (@RKA_Advantage (Bvector (c + p)) (Bvector c) (Bvector c)
        (Bvector (c + p)) (Bvector_EqDec (c + p)) (Bvector_EqDec c)
        (Bvector_EqDec c) ({ 0 , 1 }^c + p) ({ 0 , 1 }^c)
        (@dual_f (Bvector c) (Bvector (c + p)) (Bvector c) h_v)
        (BVxor (c + p))
        (@HMAC_RKA_A c p h_v iv_v fpad_v opad_v ipad_v
           (@A_GHMAC c p splitAndPad_v A)) ).
  clear Heqr1.
  rewrite ratAdd_comm. 
  apply ratAdd_leRat_compat; trivial. apply ratAdd_leRat_compat; trivial. (*What's the "omega" tactic for Rat?*)
Qed.
End HMAC_is_PRF. Runs out of memory*) 
