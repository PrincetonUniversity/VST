(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import FCF.FCF.
Require Import hmacfcf.HMAC_spec.
Require Import FCF.PRF.
Require Import hmacfcf.NMAC_to_HMAC.
Require Import hmacfcf.hF.
Require Import hmacfcf.GNMAC_PRF.

Section GHMAC_PRF.

  Variable c p : nat.
  Definition b := @b c p.
  Variable h : Bvector c -> Bvector b -> Bvector c.
  Variable iv : Bvector c.

  Variable fpad : Bvector c -> Bvector p.
  Variable opad ipad : Bvector b.
  Hypothesis opad_ne_ipad : opad <> ipad.

  Definition GHMAC := GHMAC h iv fpad opad ipad.

  Variable A : OracleComp (list (Bvector b)) (Bvector c) bool.
  Hypothesis A_wf : well_formed_oc A.

  Theorem GHMAC_PRF :
    PRF_Advantage (Rnd b) (Rnd c) GHMAC _ _ A <=
     RKA_Advantage _ _ _  ({ 0 , 1 }^b) ({ 0 , 1 }^c)
     (dual_f h) (BVxor b) (HMAC_RKA_A h iv fpad opad ipad A) +
   (PRF_Advantage ({ 0 , 1 }^c) ({ 0 , 1 }^c) h _ _
     (PRF_h_A (h_star_pad h fpad) A) +
    cAU.Adv_WCR _ _
      (h_star_pad h fpad) ({ 0 , 1 }^c)
      (au_F_A A)).

    eapply leRat_trans.
    unfold PRF_Advantage.
    eapply ratDistance_le_trans.

    eapply A_HMAC_NMAC_close.
    trivial.
    specialize (GNMAC_PRF h fpad A_wf); intuition.
    unfold A_NMAC.
    eapply H.
    reflexivity.

  Qed.

End GHMAC_PRF.