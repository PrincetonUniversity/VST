(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import FCF.FCF.
Require Import FCF.PRF.
Require Import FCF.CompFold.

Section PRF_Convert.

  Variable K D R : Set.
  Variable K' D' R' : Set.

  Hypothesis D'_EqDec : EqDec D'.
  Hypothesis R'_EqDec : EqDec R'.
  Hypothesis D_EqDec : EqDec D.
  Hypothesis R_EqDec : EqDec R.
  Hypothesis K_EqDec : EqDec K.

  Variable RndK' : Comp K'.
  Variable RndR : Comp R.

  Variable f : K -> D -> R.

  Variable k_f : K' -> K.
  Variable d_f : D' -> D.
  Hypothesis d_f_1_1 : 
    forall x y,
      x <> y ->
      d_f x <> d_f y.

  Variable r_f : R -> R'.

  Definition f' (k : K')(d : D') : R' :=
      r_f (f (k_f k) (d_f d)).

  Definition RndR' :=
    r <-$ RndR;
    ret (r_f r).

  Definition RndK :=
    k <-$ RndK';
    ret (k_f k).

  Variable A : OracleComp D' R' bool.

  Definition f'_o (x : unit)(d : D') : OracleComp D R (R' * unit) :=
    r <--$ OC_Query _ (d_f d);
    $ ret (r_f r, tt).

  Definition A_f : OracleComp D R bool :=
    [b, _] <--$2 OC_Run _ _ _ A f'_o tt;
    $ ret b.

  Theorem PRF_Convert_Adv : 
    PRF_Advantage RndK' RndR' f' _ _ A ==
    PRF_Advantage RndK RndR f _ _ A_f.

    unfold PRF_Advantage.
    eapply ratDistance_eqRat_compat.
    
    unfold PRF_G_A.
    unfold RndK.
    inline_first.
    comp_skip.
    comp_simp.
    unfold A_f.

    eapply comp_spec_eq_impl_eq.
    simpl.
    inline_first.
    comp_skip.
    eapply (oc_comp_spec_eq _ _ _ _ _ _ (fun a b => True)).
    intuition.
    intuition.
    unfold f_oracle.
    inline_first.
    comp_simp.
    inline_first.
    comp_simp.
    simpl.
    eapply comp_spec_ret.
    intuition.
    
    simpl in *.
    comp_simp.
    simpl.
    comp_simp.
    inline_first.
    comp_simp.
    intuition; subst.
    eapply comp_spec_ret; intuition.

    unfold PRF_G_B.
    unfold RndR'.
    unfold A_f.
    eapply comp_spec_eq_impl_eq.
    simpl.
    inline_first.
    comp_skip.
    eapply (oc_comp_spec_eq _ _ _ _ _ _ 
                            (fun a b => 
                               forall x, 
                                 match (arrayLookup _ a x) with
                                   | None => arrayLookup _ (snd b) (d_f x) = None
                                   | Some y => exists y',
                                                 arrayLookup _ (snd b) (d_f x) = Some y'
                                                 /\ r_f y' = y
                                 end
                                   )
                            ).
    intuition.
    simpl.
    trivial.

    intuition.
    inline_first.

    unfold RndR_func, randomFunc.
    pose proof H.
    specialize (H a).
    
    case_eq ( arrayLookup D'_EqDec x1 a); intuition.
    rewrite H1 in H.
    destruct H.
    intuition.
    rewrite H2.
    comp_simp.
    subst.
    inline_first.
    comp_simp.
    simpl.
    eapply comp_spec_ret; intuition.

    rewrite H1 in H.
    rewrite H.

    inline_first.
    assert R.
    eapply comp_base_exists.
    eauto.
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
    econstructor.
    intuition.

    assert (eqb (d_f x) (d_f a) = false).
    case_eq ( eqb (d_f x) (d_f a)); intuition.
    rewrite eqb_leibniz in H6.
    exfalso.
    destruct (EqDec_dec _ x a).
    subst.
    rewrite eqb_refl in H5.
    discriminate.
    eapply d_f_1_1.
    intros.
    eapply n.
    eapply H7.
    trivial.

    rewrite H6.

    eapply H0.

    comp_simp.
    simpl in *.
    inline_first.
    comp_simp.
    intuition.
    subst.
    eapply comp_spec_eq_refl.

  Qed.


End PRF_Convert.