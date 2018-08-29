(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import fcf.FCF.
Require Import hmacfcf.HMAC_spec.
Require Import fcf.PRF.
Require Import hmacfcf.NMAC_to_HMAC.
Require Import hmacfcf.hF.
Require Import hmacfcf.GHMAC_PRF.

Section HMAC_PRF.

  Variable c p : nat.
  Definition b := @b c p.
  Variable h : Bvector c -> Bvector b -> Bvector c.
  Variable iv : Bvector c.

  Variable Message : Set.
  Hypothesis Message_EqDec : EqDec Message.
  Variable splitAndPad : Message -> list (Bvector b).

  Hypothesis splitAndPad_1_1 :
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.

  Variable fpad : Bvector c -> Bvector p.
  Definition h_star_pad := h_star_pad h fpad.
  Variable opad ipad : Bvector b.
  Hypothesis opad_ne_ipad : opad <> ipad.

  Section h_star_WCR.

    Definition h_star := h_star _ h.

    Variable Z : OracleComp (list (Bvector (HMAC_spec.b c p))) (Bvector (HMAC_spec.b c p))
    (list (Bvector (HMAC_spec.b c p)) * list (Bvector (HMAC_spec.b c p))).

    Definition Y : OracleComp (list (Bvector (HMAC_spec.b c p))) (Bvector c)
    (list (Bvector (HMAC_spec.b c p)) * list (Bvector (HMAC_spec.b c p))) :=
      [x, _] <--$2 OC_Run _ _ _ Z (fun _ d => r <--$ OC_Query _ d; $ ret ((app_fpad fpad r), tt)) tt;
      $ ret x.

      Theorem Vector_append_inj_first :
        forall (A : Set)(a : nat)(a1 a2 : Vector.t A a)(b : nat)(b1 b2 : Vector.t A b),
          Vector.append a1 b1 = Vector.append a2 b2 ->
          a1 = a2.

        induction a1; intuition.
        rewrite vector_0 in *.
        trivial.
        destruct (vector_S a2).
        destruct H2.
        subst.
        repeat rewrite <- splitVector.Vector_cons_app_assoc in H.

        inversion H.
        apply vector_cons_eq in H.
        f_equal.
        eapply IHa1.
        eauto.
      Qed.

    Theorem WCR_h_star_pad_impl_h_star :
        cAU.Adv_WCR _ _ h_star_pad
                    ({ 0 , 1 }^c) Z <=
        cAU.Adv_WCR _ _ h_star
                    ({ 0 , 1 }^c) Y.

      unfold cAU.Adv_WCR, cAU.Adv_WCR_G.
      comp_skip.
      unfold Y.
      eapply comp_spec_impl_le.
      simpl.
      inline_first.
      comp_skip.
      eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun a b => fst b = a)).
      trivial.
      intuition.
      subst.
      unfold cAU.WCR_Oracle.
      inline_first.
      comp_simp.
      inline_first.
      comp_simp.
      simpl.
      eapply comp_spec_ret.
      intuition.
      simpl in *.
      intuition.
      destruct b2.
      simpl in *.
      subst.
      comp_simp.
      simpl.
      comp_simp.
      inline_first.
      comp_simp.
      eapply comp_spec_ret.
      intuition.
      unfold h_star_pad in *.
      case_eq (eqb a b1); intuition;
      rewrite H3 in H2;
      simpl in *.
      discriminate.
      apply eqbBvector_sound in H2.
      unfold HMAC_spec.h_star_pad, HMAC_spec.app_fpad in *.

      eapply Vector_append_inj_first in H2.
      unfold h_star, NMAC_to_HMAC.h_star.
      rewrite H2.
      eapply eqbBvector_complete.
    Qed.

  End h_star_WCR.

  Definition HMAC := HMAC h iv splitAndPad fpad opad ipad.
  Definition GHMAC := GHMAC h iv fpad opad ipad.

  Variable A : OracleComp Message (Bvector c) bool.
  Hypothesis A_wf : well_formed_oc A.

  Definition A_GHMAC : OracleComp (list (Bvector b)) (Bvector c) bool :=
    [b, _] <--$2 OC_Run _ _ _ A
    (fun _ q =>
      ls <- splitAndPad q;
      r <--$ OC_Query _ ls;
    $ ret (r, tt)) tt;
    $ ret b.

  Theorem GHMAC_to_HMAC :
    PRF_Advantage (Rnd b) (Rnd c) HMAC _ _ A ==
    PRF_Advantage (Rnd b) (Rnd c) GHMAC _ _ A_GHMAC.

    unfold PRF_Advantage.
    eapply ratDistance_eqRat_compat.

    unfold PRF_G_A, HMAC, HMAC_spec.HMAC, GHMAC, NMAC_to_HMAC.GHMAC.
    comp_skip.
    unfold A_GHMAC.
    eapply comp_spec_eq_impl_eq.
    simpl.
    inline_first.
    comp_skip.
    eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _  _ (fun a b => True)); intuition.
    unfold f_oracle.
    unfold HMAC_2K, HMAC_spec.GHMAC.
    inline_first.
    comp_simp.
    inline_first.
    comp_simp.
    simpl.
    eapply comp_spec_ret; intuition.

    simpl in *.
    comp_simp.
    simpl.
    inline_first.
    comp_simp.
    intuition; subst.
    eapply comp_spec_eq_refl.


    unfold PRF_G_B, A_GHMAC.
    eapply comp_spec_eq_impl_eq.

    simpl.
    inline_first.
    comp_skip.
    eapply (@oc_comp_spec_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun a b => forall x, arrayLookup _ (snd b) (splitAndPad x) = arrayLookup _ a x)).
    intuition.

    intuition.
    inline_first.
    unfold RndR_func, randomFunc.
    rewrite H.
    case_eq ( arrayLookup Message_EqDec x1 a ); intuition.
    comp_simp.
    inline_first.
    comp_simp.
    simpl.
    eapply comp_spec_ret; intuition.

    inline_first.
    comp_skip.
    comp_simp.
    inline_first.
    comp_simp.
    simpl.
    eapply comp_spec_ret; intuition.
    simpl.
    case_eq (eqb x a); intuition.
    rewrite eqb_leibniz in H5.
    subst.
    rewrite eqb_refl.
    trivial.

    case_eq (eqb (splitAndPad x) (splitAndPad a)); intuition.
    rewrite eqb_leibniz in H6.
    apply splitAndPad_1_1 in H6.
    subst.
    rewrite eqb_refl in H5.
    discriminate.

    simpl in *.
    intuition; subst.
    comp_simp.
    simpl.
    inline_first.
    comp_simp.
    eapply comp_spec_eq_refl.

  Qed.

  Theorem HMAC_PRF:
    PRF_Advantage (Rnd b) (Rnd c) HMAC _ _ A <=
    RKA_Advantage _ _ _  ({ 0 , 1 }^b)
     ({ 0 , 1 }^c) (dual_f h) (BVxor b)
     (HMAC_RKA_A h iv fpad opad ipad A_GHMAC) +
   (PRF_Advantage ({ 0 , 1 }^c) ({ 0 , 1 }^c) h _ _
      (PRF_h_A h_star_pad A_GHMAC) +
    cAU.Adv_WCR _ _ h_star
      ({ 0 , 1 }^c) (Y (au_F_A A_GHMAC))).

    rewrite GHMAC_to_HMAC.

    eapply leRat_trans.
    apply GHMAC_PRF.
    trivial.
    unfold A_GHMAC.
    econstructor.
    econstructor.
    trivial.
    intuition.
    econstructor.
    econstructor.
    intuition.
    econstructor.
    wftac.
    intuition.
    econstructor.
    wftac.

    eapply ratAdd_leRat_compat; try reflexivity.
    eapply ratAdd_leRat_compat; try reflexivity.
    eapply WCR_h_star_pad_impl_h_star.
  Qed.

  Print Assumptions HMAC_PRF.

End HMAC_PRF.