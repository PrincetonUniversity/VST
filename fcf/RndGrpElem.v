(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)


(* Sampling an element from a finite cyclic group *)
Require Import fcf.FCF.
Require Export fcf.GroupTheory.

Local Open Scope group_scope.

Definition RndGrpElem`{FCG : FiniteCyclicGroup}{eqd : EqDec GroupElement} :=
    n <-$ [0 .. order);
    ret (g^n).

Section RndGrpElem.

  Context`{FCG : FiniteCyclicGroup}.
  Hypothesis GroupElement_EqDec : EqDec GroupElement. 

  Theorem RndGrpElem_wf : well_formed_comp RndGrpElem.

    unfold RndGrpElem.
    wftac.

  Qed.

  Theorem groupExp_closed : forall k,
    In (g^k) (getSupport RndGrpElem).

    intuition.
    erewrite groupExp_mod.
    simpl.
    eapply in_getUnique.
    eapply in_flatten.
    econstructor.
    split.
    eapply in_map_iff.
    econstructor.
    split.
    eauto.
    eapply filter_In.
    split.
    eapply in_getUnique.
    eapply in_flatten.
    econstructor.
    split.
    eapply in_map_iff.
    econstructor.
    split.
    eapply eq_refl.
    eapply in_getAllBvectors.
    simpl.
    left.
    eapply eq_refl.
    2:{
      rewrite bvToNat_natToBv_inverse.
      simpl.
      left.
      eapply eq_refl.
      eapply lognat_monotonic.
      eapply modNat_lt.
    }
    rewrite bvToNat_natToBv_inverse.
    unfold ltNatBool.
    destruct (lt_dec (modNat k order) order); trivial.
    exfalso.
    eapply n.
    eapply modNat_lt.
    eapply lognat_monotonic.
    eapply modNat_lt.

    apply g_generator.
  Qed.

  Theorem RndGrpElem_uniform : forall x y,
    evalDist RndGrpElem x == evalDist RndGrpElem y.

    intuition.
    unfold RndGrpElem.

    eapply (evalDist_iso 
              (fun z => (modNat (z + (modNatAddInverse (groupLog g y) order) + (groupLog g x))) order) 
              (fun z => (modNat (z + (groupLog g y) + (modNatAddInverse (groupLog g x) order)) order))); intuition.

    rewrite <- plus_assoc.
    rewrite <- modNat_plus.
    assert ((x0 + groupLog g y + modNatAddInverse (groupLog g x) order +
      (modNatAddInverse (groupLog g y) order + groupLog g x)) = 
    ((groupLog g y + modNatAddInverse (groupLog g y) order) + 
      (groupLog g x + modNatAddInverse (groupLog g x) order +
      x0)))%nat.
    omega.
    rewrite H0.
    rewrite modNat_plus.
    rewrite modNatAddInverse_correct.
    rewrite plus_0_l.
    rewrite modNat_plus.
    rewrite modNatAddInverse_correct.
    rewrite plus_0_l.
    eapply modNat_eq.
    eapply RndNat_support_lt.
    trivial.

    rewrite <- plus_assoc.
    rewrite <- modNat_plus.
    assert ((x0 + modNatAddInverse (groupLog g y) order + groupLog g x +
      (groupLog g y + modNatAddInverse (groupLog g x) order)) = 
    (groupLog g x + modNatAddInverse (groupLog g x) order + 
      (groupLog g y + modNatAddInverse (groupLog g y) order + x0)))%nat.
    omega.
    rewrite H0.
    rewrite modNat_plus.
    rewrite modNatAddInverse_correct.
    rewrite plus_0_l.
    rewrite modNat_plus.
    rewrite modNatAddInverse_correct.
    rewrite plus_0_l.
    eapply modNat_eq.
    eapply RndNat_support_lt.
    trivial.

    eapply in_getSupport_RndNat.
    eapply modNat_lt.

    eapply RndNat_uniform.
    eapply modNat_lt.

    eapply RndNat_support_lt.
    trivial.

    subst.
    rewrite <- groupExp_mod.
    simpl.
    destruct (EqDec_dec GroupElement_EqDec (groupExp g x0) y); subst.
    rewrite groupExp_mod.
    rewrite modNat_plus.
    rewrite modNatAddInverse_correct_gen.
    rewrite plus_0_l.
    rewrite <- groupExp_mod.
    rewrite group_cyclic.
    destruct (EqDec_dec GroupElement_EqDec x x).
    intuition.
    congruence.
    apply g_generator.
    apply g_generator.

    symmetry.
    eapply groupLog_correct.
    apply g_generator.
    apply g_generator.

    destruct (EqDec_dec GroupElement_EqDec
         (groupExp g (x0 + modNatAddInverse (groupLog g y) order + groupLog g x)) x); intuition.
    exfalso.
    eapply n.
    rewrite groupExp_plus in e.
    rewrite group_cyclic in e.
    eapply ident_l_unique in e.
    rewrite <- (@groupIdent _ _ _ _ _ _ _ _ FCG g) in e.
    eapply groupExp_eq in e.
    rewrite (@modNat_eq order 0) in e.
    eapply modNatAddInverse_sum_0 in e.
    rewrite groupExp_mod.
    rewrite e.
    rewrite <- groupExp_mod.
    rewrite group_cyclic.
    trivial.
    apply g_generator.
    apply g_generator.
    apply g_generator.

    eapply posnat_pos.

    apply g_generator.
    apply g_generator.
    apply g_generator.
    apply g_generator.
  Qed. 

  Theorem RndGrpElem_spec : 
    forall x y,
      comp_spec (fun a b => a = x <-> b = y) RndGrpElem RndGrpElem.

    intuition.
    eapply eq_impl_comp_spec; eauto using RndGrpElem_wf.
    eapply RndGrpElem_uniform.

  Qed.

End RndGrpElem.

Notation "'RndG'" := (RndGrpElem)
  (right associativity, at level 75) : comp_scope.