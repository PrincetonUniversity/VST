(* Copyright 2012-2017 by Adam Petcher and FCF Contributors.	*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* An argument that is used to prove that the "two worlds" style of security definition is equivalent to the "coin flipping" style. *)

Set Implicit Arguments.

Require Import fcf.FCF.
Require Import fcf.Crypto.
Require Import fcf.Asymptotic.

Theorem evalDist_bool_support : 
  forall (c : Comp bool)(ls : list bool),
    well_formed_comp c ->
    ls = getSupport c ->
    sumList ls (evalDist c) == evalDist c false + evalDist c true.
  
  intuition.
  specialize (support_NoDup c); intuition.
  rewrite <- H0 in H1.
  
  destruct ls; intuition.
  specialize (getSupport_length_nz H); intuition.
  rewrite <- H0 in H2.
  simpl in *.
  omega.
  
  destruct b.
  
  destruct ls.
  unfold sumList; simpl.
  
  eapply ratAdd_eqRat_compat.
  symmetry.
  eapply getSupport_not_In_evalDist.
  intuition.
  rewrite <- H0 in H2.
  simpl in *.
  intuition.
  intuition.
  
  destruct b.
  inversion H1; clear H1; subst.
  simpl in *.
  intuition.
  
  destruct ls.
  
  unfold sumList.
  simpl.
  rewrite <- ratAdd_0_l.
  eapply ratAdd_comm.
  
  destruct b.
  inversion H1; clear H1; subst.
  simpl in *.
  intuition.
  inversion H1; clear H1; subst.
  simpl in *.
  intuition.
  inversion H5; clear H5; subst.
  simpl in *; intuition.
  
  destruct ls.
  unfold sumList; simpl.
  
  rewrite ratAdd_comm.
  eapply ratAdd_eqRat_compat.
  intuition.
  symmetry.
  eapply getSupport_not_In_evalDist.
  intuition.
  rewrite <- H0 in H2.
  simpl in *.
  intuition.

  destruct b.
  
  destruct ls.
  
  unfold sumList.
  simpl.
  rewrite <- ratAdd_0_l.
  intuition.
  
  destruct b.
  inversion H1; clear H1; subst.
  simpl in *.
  intuition.
  inversion H5; clear H5; subst.
  simpl in *; intuition.
  inversion H1; clear H1; subst.
  simpl in *; intuition.
  inversion H1; clear H1; subst.
  simpl in *; intuition.      
  
Qed.
    
Theorem evalDist_bool_complement : 
  forall (c : Comp bool),
    well_formed_comp c ->
    evalDist c false == ratSubtract 1 (evalDist c true).
  
  intuition.
  eapply (eqRat_ratAdd_same_r (evalDist c true)).
  symmetry.
  rewrite ratAdd_comm.
  rewrite ratSubtract_ratAdd_inverse_2.
  
  specialize (@evalDist_lossless _ c); intuition.
  rewrite <- H1.
  clear H1.
  eapply evalDist_bool_support.
  intuition.
  intuition.
  
  eapply evalDist_le_1.
Qed.

Theorem rndBool_bind : 
  forall 
    (f : bool -> Comp bool),
    Pr[b <-$ {0, 1}; f b] == (1 / 2) * Pr[f true] + (1 / 2) * Pr[f false].
  
  intuition.
  simpl.
  destruct (bind_eq_dec ({ 0 , 1 }^1) (fun m : Bvector 1 => ret Vector.hd m)
    false true).
  discriminate.
  
  unfold sumList.
  simpl.
  destruct (EqDec_dec bool_EqDec true false).
  discriminate.
  destruct (EqDec_dec bool_EqDec false true).
  discriminate.
  destruct (EqDec_dec bool_EqDec true true).
  destruct (EqDec_dec bool_EqDec false false).
  
  repeat rewrite <- ratAdd_0_l.
  repeat rewrite ratMult_0_r.
  repeat rewrite <- ratAdd_0_r.
  repeat rewrite <- ratAdd_0_l.
  repeat rewrite ratMult_1_r.
  eapply ratAdd_eqRat_compat;
    eapply ratMult_eqRat_compat; intuition.
  
  intuition.
  intuition.
Qed.

Section TwoWorldsEquiv.

  Variable f : nat -> bool -> Comp bool.

  Hypothesis f_wf : forall n b, well_formed_comp (f n b).

  Section TwoWorldsEquiv_eta.
    Variable eta : nat.
  
    Definition StandardDef_G :=
      b <-$ {0, 1};
      b' <-$ f eta b;
      ret (eqb b b').


    Theorem StandardDef_equiv_2W_h : 
      | Pr[StandardDef_G] - 1 / 2 | == (1 / 2) * | Pr[f eta true] - Pr[f eta false] |.
      
      unfold StandardDef_G.
      
      rewrite rndBool_bind.
      
      assert ( Pr[b' <-$ f eta true; ret eqb true b'] == Pr[f eta true]).
      symmetry.
      rewrite <- evalDist_right_ident.
      comp_skip.
      fcf_compute.
      rewrite H.
      clear H.
      
      assert ( Pr  [b' <-$ f eta false; ret eqb false b' ] == (ratSubtract 1 (Pr[f eta false]))).
      assert (Pr  [b' <-$ f eta false; ret eqb false b' ]  == evalDist (f eta false) false).
      symmetry.
      rewrite <- evalDist_right_ident.
      comp_skip.
      fcf_compute.
      rewrite H.
      clear H.
      
      eapply evalDist_bool_complement.
      wftac.
      
      rewrite H.
      clear H.
      
      rewrite <- ratMult_distrib.
      rewrite <- (ratMult_1_r (1/2)) at 2.
      
      rewrite ratMult_ratDistance_factor_l.
      eapply ratMult_eqRat_compat; intuition.
      
      assert ((Pr  [f eta false])  + ratSubtract 1 (Pr  [f eta false]) == 1).
      rewrite <- ratSubtract_ratAdd_assoc.
      eapply ratSubtract_ratAdd_inverse.
      
      eapply evalDist_le_1.
      unfold eq_dec.
      
      rewrite <- H at 2.
      
      rewrite ratDistance_add_same_r.
      reflexivity.

      Grab Existential Variables.
      exact _.
      exact _.
    Qed.
    
    Theorem Def_equiv_2W : 
      | Pr[StandardDef_G] - 1 / 2 | == (1 / 2) * | Pr[f eta false] - Pr[f eta true] |.
      
      rewrite StandardDef_equiv_2W_h.
      rewrite ratDistance_comm.
      intuition.
      
    Qed.

    End TwoWorldsEquiv_eta.
  
    Theorem TwoWorlds_equiv_f : 
      negligible (fun eta => (| Pr[f eta false] - Pr[f eta true] |)) -> 
      negligible (fun eta => | Pr[StandardDef_G eta] - 1 / 2 |).

      unfold negligible.
      intuition.
      destruct (H c).
      exists x.
      intuition.
      eapply H0.
      intuition.
      rewrite H2.
      rewrite Def_equiv_2W.

      rewrite ratMult_comm.
      eapply ratMult_small_le.
      
      eapply rat_le_1.
      simpl.
      omega.
      
    Qed.

    Theorem TwoWorlds_equiv_b : 
      negligible (fun eta => | Pr[StandardDef_G eta] - 1 / 2 |) ->
      negligible (fun eta => (| Pr[f eta false] - Pr[f eta true] |)).

      unfold negligible.
      intuition.
      edestruct (H (1 + c)%nat).
      exists (S x)%nat.
      intuition.
      eapply H0.
      omega.

      assert ((RatIntro (S O)
        (@natToPosnat (expnat x0 (plus (S O) c))
           (@expnat_nz (plus (S O) c) x0 pf_nz))) == (1 / x0) * (1 / (expnat x0 c))).

      simpl.
      rewrite <- ratMult_denom.
      eapply eqRat_terms; intuition.

      rewrite H3.
      clear H3.
      rewrite H2.

      eapply leRat_trans.
      2:{
        eapply eqRat_impl_leRat.
        symmetry.
        eapply Def_equiv_2W.
      }

      eapply ratMult_leRat_compat; intuition.
      unfold leRat.
      eapply leRat_terms; intuition.
      unfold natToPosnat, posnatToNat.
      omega.

    Qed.

    Theorem TwoWorlds_equiv : 
      negligible (fun eta => (| Pr[f eta false] - Pr[f eta true] |)) <->
      negligible (fun eta => | Pr[StandardDef_G eta] - 1 / 2 |).

      intuition.
      eapply TwoWorlds_equiv_f; intuition.
      eapply TwoWorlds_equiv_b; intuition.

    Qed.
      

End TwoWorldsEquiv.