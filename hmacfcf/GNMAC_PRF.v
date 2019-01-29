(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)


Set Implicit Arguments.

Require Import FCF.FCF.
Require Import hmacfcf.HMAC_spec.
Require Import FCF.PRF.
Require Import hmacfcf.hF.

Section GNMAC_PRF.

  Variable c p : nat.
  Definition b := @HMAC_spec.b c p.
  Variable h : Bvector c -> Bvector b -> Bvector c.

  Variable fpad : Bvector c -> Bvector p.
  Definition app_fpad := @app_fpad c p fpad.
  Definition h_star := h_star p h.
  Definition h_star_pad := fun k x => app_fpad (h_star k x).

  Variable A : OracleComp (list (Bvector b)) (Bvector c) bool.
  Hypothesis A_wf : well_formed_oc A.

  Definition GNMAC := GNMAC h fpad.

  Theorem GNMAC_PRF :
     PRF_Advantage (Rnd (c + c)) (Rnd c) GNMAC _ _ A <=
     PRF_Advantage ({ 0 , 1 }^c) ({ 0 , 1 }^c) h (Bvector_EqDec b)
     _
     (PRF_h_A (h_star_pad) A) +
     cAU.Adv_WCR _ _ (h_star_pad)  ({ 0 , 1 }^c) (au_F_A A).

    specialize (hF_PRF h h_star_pad A_wf); intuition.

  Qed.

End GNMAC_PRF.