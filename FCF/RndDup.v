(* Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* A basic argument about encountering a specific value in a list of randomly-generated values. *)

Require Import FCF.FCF.
Require Import FCF.CompFold.

Section RndDup.

  Variable eta : nat.
  
  Definition RndDup_G (A : Set)(ls : list A) (x : Bvector eta) :=
    rs <-$ compMap _ (fun _ => {0, 1} ^ eta) ls;
      ret (if (in_dec (EqDec_dec _) x rs) then true else false).

  (*
  Definition RndDup_G q (x : Bvector eta) :=
    rs <-$ compMap _ (fun _ => {0, 1} ^ eta) (allNatsLt q);
    ret (if (in_dec (EqDec_dec _) x rs) then true else false).
   *)

  Theorem bool_Comp_seq : 
    forall (A : Set)(c1 : Comp bool)(c2 : bool -> Comp A) a,
      evalDist (b <-$ c1; c2 b) a ==
      (evalDist c1 true * evalDist (c2 true) a) + 
      (evalDist c1 false * evalDist (c2 false) a).

    intros.
    simpl.

    remember (getSupport c1) as ls.
    destruct ls.
    unfold sumList.
    simpl.
    assert (Pr  [c1 ] == 0).
    eapply getSupport_not_In_evalDist.
    rewrite <- Heqls.
    simpl.
    intuition.

    rewrite H.
    assert (evalDist c1 false == 0).
    eapply getSupport_not_In_evalDist.
    rewrite <- Heqls.
    simpl.
    intuition.
    rewrite H0.
    repeat rewrite ratMult_0_l.
    eapply ratAdd_0_l.
    
    destruct b.
    destruct ls.
    unfold sumList.
    simpl.
    rewrite <- ratAdd_0_l.
    rewrite ratAdd_0_r at 1.
    eapply ratAdd_eqRat_compat.
    intuition.
    symmetry.
    
    assert (evalDist c1 false == 0).
    eapply getSupport_not_In_evalDist.
    rewrite <- Heqls.
    simpl.
    intuition.
    rewrite H.
    eapply ratMult_0_l.

    destruct b.
    exfalso.
    assert (NoDup (true :: true :: ls))%list.
    rewrite Heqls.
    eapply getSupport_NoDup.
    inversion H; clear H; subst.
    simpl in *.
    intuition.

    destruct ls.

    unfold sumList.
    simpl.
    rewrite <- ratAdd_0_l.
    intuition.

    destruct b.
    assert (NoDup (true :: false :: true :: ls)%list).
    rewrite Heqls.
    eapply getSupport_NoDup.
    inversion H; clear H; subst.
    simpl in *.
    intuition.
    assert (NoDup (true :: false :: false  :: ls)%list).
    rewrite Heqls.
    eapply getSupport_NoDup.
    inversion H; clear H; subst.
    inversion H3; clear H3; subst.
    simpl in *.
    intuition.

    destruct ls.
    unfold sumList.
    simpl.
    eapply ratAdd_eqRat_compat; intuition.
    assert ( Pr  [c1 ] == 0).
    eapply getSupport_not_In_evalDist.
    rewrite <- Heqls.
    simpl.
    intuition.
    rewrite H.
    rewrite ratMult_0_l.
    intuition.

    destruct b.
    destruct ls.
    unfold sumList.
    simpl.
    rewrite <- ratAdd_0_l.
    eapply ratAdd_comm.


    destruct b.
    assert (NoDup (false :: true :: true :: ls)%list).
    rewrite Heqls.
    eapply getSupport_NoDup.
    inversion H; clear H; subst.
    inversion H3; clear H3; subst.
    simpl in *.
    intuition.

    assert (NoDup (false :: true :: false  :: ls)%list).
    rewrite Heqls.
    eapply getSupport_NoDup.
    inversion H; clear H; subst.
    simpl in *.
    intuition.

    assert (NoDup (false :: false  :: ls)%list).
    rewrite Heqls.
    eapply getSupport_NoDup.
    inversion H; clear H; subst.
    simpl in *.
    intuition.
    
  Qed.

  Theorem Prob_or_indep : 
    forall (c1 c2 : Comp bool),
      well_formed_comp c2 ->
      Pr[b1 <-$ c1; b2 <-$ c2; ret (b1 || b2)] == Pr[c1] + (evalDist c1 false) * Pr[c2].

    intuition.
    
    rewrite bool_Comp_seq.

    assert (Pr  [b2 <-$ c2; ret true || b2 ] == 1).
    comp_irr_l.
    rewrite evalDist_ret_1; simpl; intuition.
    rewrite H0.
    clear H0.
    
    assert (Pr  [b2 <-$ c2; ret false || b2 ] == Pr[c2]).
    rewrite bool_Comp_seq.
    rewrite evalDist_ret_1.
    rewrite evalDist_ret_0.
    rewrite ratMult_0_r.
    rewrite <- ratAdd_0_r.
    eapply ratMult_1_r.
    simpl.
    intuition.
    simpl; intuition.
    rewrite H0.
    clear H0.
    rewrite ratMult_1_r.
    
    intuition.
  Qed.

  Theorem evalDist_right_ident_eqb : 
    forall (A : Set)(eqd : EqDec A)(c : Comp A)(a : A),
      Pr[x <-$ c; ret (eqb a x)] == evalDist c a.

    intuition.
    symmetry.
    rewrite <-(@evalDist_right_ident _ eqd).
    comp_skip.
    simpl.
    repeat match goal with
             |- context [ if ?X then _ else _ ] => destruct X
           end; rewrite ?@eqb_leibniz in *; reflexivity || congruence.
    
  Qed.

  Theorem Prob_or_indep_le : 
    forall (c1 c2 : Comp bool),
      Pr[b1 <-$ c1; b2 <-$ c2; ret (b1 || b2)] <= Pr[c1] + Pr[c2].

    intuition.
    
    rewrite bool_Comp_seq.

    eapply ratAdd_leRat_compat.
    eapply leRat_trans.
    eapply ratMult_leRat_compat.
    eapply leRat_refl.
    eapply evalDist_le_1.
    eapply eqRat_impl_leRat.
    eapply ratMult_1_r.

    eapply leRat_trans.
    eapply ratMult_leRat_compat.
    eapply evalDist_le_1.
    eapply leRat_refl.
    rewrite ratMult_1_l.
    unfold orb.
    rewrite evalDist_right_ident.
    intuition.
  Qed.


  Theorem ratS_num': 
    forall n d, 
      RatIntro (S n) d == (RatIntro 1 d) + (RatIntro n d).

    intuition.
    rattac.
    rewrite mult_plus_distr_r.
    f_equal.
    eapply mult_assoc.
  Qed.

  Theorem RndDup_P :
    forall (A : Set)(ls : list A) x,
      Pr [RndDup_G _ ls x] <= (length ls) / expnat 2 eta.

    unfold RndDup_G in *.
    induction ls; intros.
    
    unfold compMap.
    comp_simp.
    destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) x nil).
    simpl in *. intuition.
    rewrite evalDist_ret_0; intuition.
    symmetry.
    eapply rat_num_0.

    eapply leRat_trans.
    (* posnat existential is added here *)

    eapply eqRat_impl_leRat.
    eapply evalDist_seq_eq.

    intros.
    eapply compMap_cons.
    intros.
    eapply eqRat_refl.

    inline_first.

    comp_at comp_inline leftc 1%nat.
    dist_at dist_ret leftc 2%nat.


    assert (
        Pr 
          [a0 <-$ { 0 , 1 }^eta;
           a1 <-$ (foreach  (_ in ls){ 0 , 1 }^eta);
           ret (if in_dec (EqDec_dec (Bvector_EqDec eta)) x (a0 :: a1)
                then true
                else false) ] ==
        Pr 
          [b1 <-$ (a0 <-$ { 0 , 1 }^eta; ret (eqb x a0));
           b2 <-$ (a1 <-$ (foreach  (_ in ls){ 0 , 1 }^eta); 
                   ret (if (in_dec (EqDec_dec _) x a1) then true else false));
           ret (b1 || b2) ]
      ).

    inline_first.
    comp_skip.
    comp_simp.
    comp_inline_r.
    comp_skip.
    comp_simp.
    case_eq (eqb x x0); intuition.
    destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) x (x0 :: x1)).
    simpl.
    intuition.

    rewrite eqb_leibniz in H1.
    subst.
    simpl in *.
    intuition.

    destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) x x1).
    destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) x (x0 :: x1)).
    simpl.
    intuition.

    simpl in *.
    intuition.

    destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) x (x0 :: x1)).
    simpl in i, n; intuition.
    subst.
    rewrite eqb_refl in H1.
    congruence.

    simpl.
    intuition.

    rewrite H.
    clear H.

    rewrite Prob_or_indep_le.
    rewrite IHls.

    assert (Pr  [a0 <-$ { 0 , 1 }^eta; ret eqb x a0 ] == 1 / expnat 2 eta) as HA. {
      rewrite evalDist_right_ident_eqb.
      simpl.
      intuition.
    } rewrite HA; clear HA.

    eapply eqRat_impl_leRat.
    simpl.

    rewrite (ratS_num' (length ls)).
    reflexivity.

    Grab Existential Variables.
    eapply 1.
  Qed.
End RndDup.
