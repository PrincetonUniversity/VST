Require Import compcert.lib.Coqlib.
Require Import Bvector.
Require Import List.
Require Import compcert.lib.Integers.
Require Import BinNums.
Require Import sha.common_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.ByteBitRelations.
Require Import sha.hmac_pure_lemmas.
Require Import sha.HMAC_common_defs.
Require Import sha.HMAC_spec_list.
Require Import sha.HMAC_spec_abstract.
Require Import sha.HMAC_equivalence.

(*SHA_specific stuff
Require Import SHA256.
Require Import pure_lemmas.
Require Import sha_padding_lemmas.
Require Import ShaInstantiation.
Require Import hmac_common_lemmas.
Require Import HMAC256_spec_pad.
Require Import HMAC256_spec_list.
Require Import HMAC256_equivalence.

Lemma splitAndPad_v_to_sha_splitandpad_blocks l:
   map Vector.to_list (splitAndPad_v l) = sha_splitandpad_blocks l.
Proof. apply Forall2_map. apply length_splitandpad_inner. Qed.

Lemma splitAndPad_v_eq_inverse: forall l m, splitAndPad_v l = splitAndPad_v m ->
      sha_splitandpad_blocks l = sha_splitandpad_blocks m.
Proof. intros. do 2 rewrite <- splitAndPad_v_to_sha_splitandpad_blocks.
  rewrite H. trivial.
Qed.

Lemma splitAndPad_1to1 b1 b2 (B:splitAndPad_v b1 = splitAndPad_v b2)
       (L1: NPeano.divide 8 (length b1))
       (L2: NPeano.divide 8 (length b2)): b1 = b2.
Proof. intros.
  apply splitAndPad_v_eq_inverse in B.
  unfold sha_splitandpad_blocks in B.
  apply toBlocks_injective in B; try apply sha_splitandpad_inc_InBlocks.
  unfold sha_splitandpad_inc in B.
  apply bytesToBits_injective in B.
    apply pad_inc_injective in B.
    apply (bitsToBytes_injective8 _ _ B L1 L2).
  apply isbyteZ_pad_inc. eapply bitsToBytes_isbyteZ. reflexivity.
  apply isbyteZ_pad_inc. eapply bitsToBytes_isbyteZ. reflexivity.
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
*)
(* A definition of a PRF in the form of a predicate. *)
Set Implicit Arguments.

Require Import FCF.FCF.
Require Import FCF.PRF.
Require Import hmacfcf.NMAC_to_HMAC.
Require Import hmacfcf.hF.
Require Import hmacfcf.HMAC_PRF.

Module Type HMAC_is_PRF_Parameters (HF:HP.HASH_FUNCTION) (EQ: EQUIV_Inst HF).
  Parameter P : Blist -> Prop.
  Parameter HP: forall m, P m -> NPeano.Nat.divide 8 (length m).

  Parameter splitAndPad_1to1: forall b1 b2 (B:EQ.splitAndPad_v b1 = EQ.splitAndPad_v b2)
       (L1: NPeano.Nat.divide 8 (length b1))
       (L2: NPeano.Nat.divide 8 (length b2)), b1 = b2.
End HMAC_is_PRF_Parameters.

Module HMAC_is_PRF (HF:HP.HASH_FUNCTION) (EQ: EQUIV_Inst HF) (PARS:HMAC_is_PRF_Parameters HF EQ).

Definition isPRF {D R Key:Set} (RndKey:Comp Key) (RndR: Comp R) (f: Key -> D -> R)
                         (ED:EqDec D) (ER:EqDec R) advantage adversary :=
        PRF_Advantage RndKey RndR f _ _ adversary <= advantage.
(*
Parameter P : Blist -> Prop.
Parameter HP: forall m, P m -> NPeano.divide 8 (length m).

Parameter splitAndPad_1to1: forall b1 b2 (B:EQ.splitAndPad_v b1 = EQ.splitAndPad_v b2)
       (L1: NPeano.divide 8 (length b1))
       (L2: NPeano.divide 8 (length b2)), b1 = b2.
*)
Lemma wrappedSAP_1_1_local (msg1 msg2 : HMAC_Abstract.Message PARS.P):
      HMAC_Abstract.wrappedSAP _ _ EQ.splitAndPad_v msg1 = HMAC_Abstract.wrappedSAP _ _ EQ.splitAndPad_v msg2 -> msg1 = msg2.
Proof. apply HMAC_Abstract.wrappedSAP_1_1. intros.
  apply PARS.HP in H0; apply PARS.HP in H1.
  apply PARS.splitAndPad_1to1; trivial.
Qed.

Definition msg_eqb (msg1 msg2:HMAC_Abstract.Message PARS.P): bool.
destruct msg1 as [m1 M1].
destruct msg2 as [m2 M2].
apply (list_EqDec bool_EqDec). apply m1. apply m2.
Defined.

Lemma Message_eqdec: EqDec (HMAC_Abstract.Message PARS.P).
apply (Build_EqDec msg_eqb).
intros; unfold msg_eqb. destruct x as [m1 M1]. destruct y as [m2 M2].
destruct (eqb_leibniz m1 m2).
split; intros.
  apply H in H1; clear H H0. apply Extensionality.exist_ext. trivial.
  apply H0; clear H H0. apply EqdepFacts.eq_sig_fst in H1. trivial.
Qed.

Module M := HMAC_Equiv HF EQ.

(* Assume h is a tau-PRF against adversary (PRF_h_A h_star_pad A_GHMAC) *)
Definition h_PRF (A : OracleComp (HMAC_Abstract.Message PARS.P) (Bvector EQ.c) bool) tau :=
           isPRF ({ 0 , 1 }^EQ.c) ({ 0 , 1 }^EQ.c) M.h_v (Bvector_EqDec (b EQ.c EQ.p)) (Bvector_EqDec EQ.c) tau
                         (PRF_h_A (h_star_pad M.h_v EQ.fpad_v)
                                  (HMAC_PRF.A_GHMAC EQ.p Message_eqdec (HMAC_Abstract.wrappedSAP _ _ EQ.splitAndPad_v) A)).

(* We could make similar predicates for the other definitions, or just
assume the inequalities
Definition h_star_WCR (A : OracleComp (HMAC_Abstract.Message PARS.P) (Bvector EQ.c) bool) epsilon :=
       cAU.Adv_WCR (list_EqDec (Bvector_EqDec (b EQ.c EQ.p)))
             (Bvector_EqDec (b EQ.c EQ.p)) (h_star_pad M.h_v EQ.fpad_v)
       ({ 0 , 1 }^EQ.c) (au_F_A (A_GHMAC EQ.p Message_eqdec (HMAC_Abstract.wrappedSAP _ _ EQ.splitAndPad_v) A)) <= epsilon.*)
Definition h_star_WCR (A : OracleComp (HMAC_Abstract.Message PARS.P) (Bvector EQ.c) bool) epsilon := cAU.Adv_WCR (list_EqDec (Bvector_EqDec (HMAC_spec.b EQ.c EQ.p))) (Bvector_EqDec EQ.c) (h_star EQ.p M.h_v)
  ({ 0 , 1 }^ EQ.c) (Y EQ.fpad_v (au_F_A (A_GHMAC EQ.p Message_eqdec (HMAC_Abstract.wrappedSAP EQ.c EQ.p EQ.splitAndPad_v) A))) <=
epsilon.

Definition dual_h_RKA (A : OracleComp (HMAC_Abstract.Message PARS.P) (Bvector EQ.c) bool) sigma:=
    RKA_Advantage _ _ _ ({ 0 , 1 }^b EQ.c EQ.p) ({ 0 , 1 }^EQ.c) (dual_f M.h_v) (BVxor (b EQ.c EQ.p))
      (HMAC_RKA_A M.h_v EQ.iv_v EQ.fpad_v M.opad_v M.ipad_v (A_GHMAC EQ.p Message_eqdec (HMAC_Abstract.wrappedSAP _ _ EQ.splitAndPad_v) A)) <= sigma.

Theorem HMAC_isPRF A (A_wf : well_formed_oc A) tau epsilon sigma
        (HH1: h_PRF A tau) (HH2: h_star_WCR A epsilon) (HH3: dual_h_RKA A sigma):
        isPRF (Rnd (b EQ.c EQ.p)) (Rnd EQ.c)
              (HMAC M.h_v EQ.iv_v (HMAC_Abstract.wrappedSAP _ _ EQ.splitAndPad_v)
                              EQ.fpad_v M.opad_v M.ipad_v)
              Message_eqdec _ (tau + epsilon + sigma) A.
Proof. unfold isPRF.
  eapply leRat_trans.
    apply (HMAC_PRF M.h_v EQ.iv_v Message_eqdec (HMAC_Abstract.wrappedSAP _ _ EQ.splitAndPad_v) wrappedSAP_1_1_local
                              EQ.fpad_v M.opad_ne_ipad A_wf).
  rewrite ratAdd_comm.
  apply ratAdd_leRat_compat.
    apply ratAdd_leRat_compat. apply HH1. apply HH2.
    apply HH3.
Qed.
End HMAC_is_PRF.
