Require Import List.
Require Import sha.ByteBitRelations.
Require Import sha.hmac_pure_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC_spec_abstract.
Require Import sha.HMAC_equivalence.

Require Import sha.HMAC_isPRF.

Require Import sha.SHA256.
Require Import sha.pure_lemmas.
Require Import sha.HMAC256_functional_prog.
Require Import sha.sha_padding_lemmas.
Require Import sha.ShaInstantiation.
Require Import sha.hmac_common_lemmas.
Require Import sha.HMAC256_spec_pad.
Require Import sha.HMAC256_spec_list.
Require Import sha.HMAC256_equivalence.

Lemma splitAndPad_v_to_sha_splitandpad_blocks l:
   map Vector.to_list (splitAndPad_v l) = sha_splitandpad_blocks l.
Proof. apply Forall2_map. apply length_splitandpad_inner. Qed.

Lemma splitAndPad_v_eq_inverse: forall l m, splitAndPad_v l = splitAndPad_v m ->
      sha_splitandpad_blocks l = sha_splitandpad_blocks m.
Proof. intros. do 2 rewrite <- splitAndPad_v_to_sha_splitandpad_blocks.
  rewrite H. trivial.
Qed.

Lemma splitAndPad_1to1 b1 b2 (B:splitAndPad_v b1 = splitAndPad_v b2)
       (L1: NPeano.Nat.divide 8 (length b1))
       (L2: NPeano.Nat.divide 8 (length b2)): b1 = b2.
Proof. intros.
  apply splitAndPad_v_eq_inverse in B.
  unfold sha_splitandpad_blocks in B.
  apply toBlocks_injective in B; try apply sha_splitandpad_inc_InBlocks.
  unfold sha_splitandpad_inc in B.
  apply bytesToBits_injective in B.
    apply pad_inc_injective in B.
    apply (bitsToBytes_injective8 _ _ B L1 L2).
Qed.
(*longer proof now in HAMC_equivalence
Lemma opad_ne_ipad : EQ.opad_v <> EQ.ipad_v.
  intros N.
  assert (Vector.to_list EQ.opad_v = Vector.to_list EQ.ipad_v). rewrite N; trivial.
  unfold EQ.opad_v, EQ.ipad_v in H.
  repeat rewrite of_length_proof_irrel in H.
  unfold HP.Opad, HP.Ipad in H. simpl in H.
  discriminate.
Qed.
*)

Module PARS256 <: HMAC_is_PRF_Parameters SHA256 EQ256.

  Parameter P : Blist -> Prop.
  Parameter HP: forall m, P m -> NPeano.Nat.divide 8 (length m).

  Lemma splitAndPad_1to1: forall b1 b2 (B:EQ256.splitAndPad_v b1 = EQ256.splitAndPad_v b2)
       (L1: NPeano.Nat.divide 8 (length b1))
       (L2: NPeano.Nat.divide 8 (length b2)), b1 = b2.
   Proof. apply splitAndPad_1to1. Qed.
End PARS256.


(* A definition of a PRF in the form of a predicate. *)
Set Implicit Arguments.

Require Import fcf.FCF.
Require Import fcf.PRF.
Require Import hmacfcf.NMAC_to_HMAC.
Require Import hmacfcf.hF.
Require Import hmacfcf.HMAC_PRF.

Module PRFMod := HMAC_is_PRF SHA256 EQ256 PARS256.

Theorem HMAC256_isPRF A (A_wf : well_formed_oc A) tau epsilon sigma
        (HH1: PRFMod.h_PRF A tau) (HH2: PRFMod.h_star_WCR A epsilon) (HH3: PRFMod.dual_h_RKA A sigma):
        PRFMod.isPRF ({ 0 , 1 }^b EQ256.c EQ256.p) ({ 0 , 1 }^EQ256.c)
          (HMAC PRFMod.M.h_v EQ256.iv_v
             (HMAC_Abstract.wrappedSAP EQ256.c EQ256.p EQ256.splitAndPad_v)
             EQ256.fpad_v PRFMod.M.opad_v PRFMod.M.ipad_v) PRFMod.Message_eqdec
         (Bvector_EqDec EQ256.c) (tau + epsilon + sigma) A.
Proof. apply (PRFMod.HMAC_isPRF A_wf HH1 HH2 HH3). Qed.

Lemma OpadsEQ: PRFMod.M.opad_v =  EQ.opad_v.
Proof.
   specialize EQ.OPADX. specialize PRFMod.M.OPADX. intros.
  eapply to_list_eq_inv.
    rewrite (bits_bytes_ind_comp _ _ H); clear H.
    rewrite (bits_bytes_ind_comp _ _ H0); reflexivity.
Qed.

Lemma IpadsEQ: PRFMod.M.ipad_v =  EQ.ipad_v.
Proof.
  specialize EQ.IPADX. specialize PRFMod.M.IPADX. intros.
  eapply to_list_eq_inv.
    rewrite (bits_bytes_ind_comp _ _ H); clear H.
    rewrite (bits_bytes_ind_comp _ _ H0); reflexivity.
Qed.

Theorem HMAC256_isPRF' A (A_wf : well_formed_oc A) tau epsilon sigma
        (HH1: PRFMod.h_PRF A tau) (HH2: PRFMod.h_star_WCR A epsilon) (HH3: PRFMod.dual_h_RKA A sigma):
        PRFMod.isPRF (Rnd (b EQ256.c EQ256.p)) (Rnd EQ256.c)
              (HMAC EQ.h_v iv_v (HMAC_Abstract.wrappedSAP _ _ splitAndPad_v)
                              fpad_v EQ.opad_v EQ.ipad_v)
              PRFMod.Message_eqdec _ (tau + epsilon + sigma) A.
Proof. rewrite <- IpadsEQ, <- OpadsEQ. apply (HMAC256_isPRF A_wf HH1 HH2 HH3). Qed.

Print Assumptions HMAC256_isPRF'.
