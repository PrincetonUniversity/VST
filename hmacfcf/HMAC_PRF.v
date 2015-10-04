
Set Implicit Arguments.

Require Import FCF.
Require Import HMAC_spec.
Require Import PRF.
Require Import NMAC_to_HMAC.
Require Import hF.
Require Import GHMAC_PRF.

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
    case_eq (arrayLookup Message_EqDec x1 a ); intuition.
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
    cAU.Adv_WCR _ _ h_star_pad
      ({ 0 , 1 }^c) (au_F_A A_GHMAC)).

    rewrite GHMAC_to_HMAC.

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
  Qed.

  Print Assumptions HMAC_PRF.

End HMAC_PRF.