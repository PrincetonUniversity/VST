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
Require Import ShaInstantiation.
Require Import HMAC256_spec_pad.
Require Import HMAC256_spec_list.

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
Require Import PRF.
Require Import NMAC_to_HMAC.
Require Import hF.
Require Import HMAC_PRF.

Section HMAC_is_PRF.
Definition isPRF {D R Key:Set} (RndKey:Comp Key) (RndR: Comp R) (f: Key -> D -> R) 
                         (ED:EqDec D) (ER:EqDec R) advantage adversary :=
        PRF_Advantage RndKey RndR f _ _ adversary <= advantage.

Variable P : Blist -> Prop.
Variable HP: forall m, P m -> NPeano.divide 8 (length m).

Lemma wrappedSAP_1_1_local (msg1 msg2 : HMAC_Abstract.Message P):
      HMAC_Abstract.wrappedSAP _ _ splitAndPad_v msg1 = HMAC_Abstract.wrappedSAP _ _ splitAndPad_v msg2 -> msg1 = msg2.
Proof. apply HMAC_Abstract.wrappedSAP_1_1. intros.
  apply HP in H0; apply HP in H1.
  apply splitAndPad_1to1; trivial.
Qed. 

Definition msg_eqb (msg1 msg2:HMAC_Abstract.Message P): bool.
destruct msg1 as [m1 M1].
destruct msg2 as [m2 M2].
apply (list_EqDec bool_EqDec). apply m1. apply m2.
Defined.

Lemma Message_eqdec: EqDec (HMAC_Abstract.Message P).
apply (Build_EqDec msg_eqb). 
intros; unfold msg_eqb. destruct x as [m1 M1]. destruct y as [m2 M2].
destruct (eqb_leibniz m1 m2). 
split; intros.
  apply H in H1; clear H H0. apply Extensionality.exist_ext. trivial.
  apply H0; clear H H0. apply EqdepFacts.eq_sig_fst in H1. trivial.
Qed.

(* Assume h is a tau-PRF against adversary (PRF_h_A h_star_pad A_GHMAC) *)
Definition h_PRF (A : OracleComp (HMAC_Abstract.Message P) (Bvector c) bool) tau := 
           isPRF ({ 0 , 1 }^c) ({ 0 , 1 }^c) h_v (Bvector_EqDec (b c p)) (Bvector_EqDec c) tau 
                         (PRF_h_A (h_star_pad h_v fpad_v) 
                                  (HMAC_PRF.A_GHMAC p Message_eqdec (HMAC_Abstract.wrappedSAP _ _ splitAndPad_v) A)).

(* We could make similar predicates for the other definitions, or just
assume the inequalities*)
Definition h_star_WCR (A : OracleComp (HMAC_Abstract.Message P) (Bvector c) bool) epsilon := 
       cAU.Adv_WCR (list_EqDec (Bvector_EqDec (b c p)))
             (Bvector_EqDec (b c p)) (h_star_pad h_v fpad_v)
       ({ 0 , 1 }^c) (au_F_A (A_GHMAC p Message_eqdec (HMAC_Abstract.wrappedSAP _ _ splitAndPad_v) A)) <= epsilon.

Definition dual_h_RKA (A : OracleComp (HMAC_Abstract.Message P) (Bvector c) bool) sigma:=
    RKA_Advantage _ _ _ ({ 0 , 1 }^b c p) ({ 0 , 1 }^c) (dual_f h_v) (BVxor (b c p))
      (HMAC_RKA_A h_v iv_v fpad_v opad_v ipad_v (A_GHMAC p Message_eqdec (HMAC_Abstract.wrappedSAP _ _ splitAndPad_v) A)) <= sigma.

Theorem HMAC_isPRF A (A_wf : well_formed_oc A) tau epsilon sigma 
        (HH1: h_PRF A tau) (HH2: h_star_WCR A epsilon) (HH3: dual_h_RKA A sigma):
        isPRF (Rnd (b c p)) (Rnd c) 
              (HMAC h_v iv_v (HMAC_Abstract.wrappedSAP _ _ splitAndPad_v)
                              fpad_v opad_v ipad_v)
              Message_eqdec _ (tau + epsilon + sigma) A.
Proof. unfold isPRF.
  eapply leRat_trans. 
    apply (HMAC_PRF h_v iv_v Message_eqdec (HMAC_Abstract.wrappedSAP _ _ splitAndPad_v) wrappedSAP_1_1_local
                              fpad_v opad_ne_ipad A_wf).
  rewrite ratAdd_comm. 
  apply ratAdd_leRat_compat.
    apply ratAdd_leRat_compat. apply HH1. apply HH2.
    apply HH3.
Qed.
End HMAC_is_PRF. 
