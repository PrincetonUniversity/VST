(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import fcf.FCF.
Require Import fcf.CompFold.
Local Open Scope list_scope.

Fixpoint hasDups (A : Set)(eqd : EqDec A)(ls : list A) :=
  match ls with
    | nil => false
    | a :: ls' =>
      if (in_dec (EqDec_dec _) a ls') then true else
        (hasDups _ ls')
  end.


Theorem hasDups_false_NoDup : 
  forall (A : Set)(eqd : EqDec A)(ls : list A),
    hasDups _ ls = false <->
    NoDup ls.
  
  induction ls; intuition; simpl in *.
  econstructor.
  
  destruct (in_dec (EqDec_dec eqd) a ls).
  discriminate.
  econstructor; intuition.
  
  inversion H1; clear H1; subst.
  destruct (in_dec (EqDec_dec eqd) a ls);
    intuition.
  
Qed.

Theorem hasDups_true_not_NoDup : 
  forall (A : Set)(eqd : EqDec A)(ls : list A),
    hasDups eqd ls = true <-> (~ NoDup ls).

  induction ls; intuition; simpl in *.
  exfalso.
  eapply H.
  econstructor.
       
  inversion H2; clear H2; subst.
  destruct (in_dec (EqDec_dec eqd) a ls); intuition.
  destruct (in_dec (EqDec_dec eqd) a ls); intuition.
  eapply H0.
  intuition.
  eapply H1.
  econstructor; intuition.
  
Qed.

Theorem hasDups_inj_equiv : 
  forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B)(lsa : list A)(inj : A -> B),
    (forall a1 a2, inj a1 = inj a2 -> a1 = a2) ->
    hasDups _ lsa = hasDups _ (map inj lsa).
  
  induction lsa; intuition; simpl in *.
  destruct (in_dec (EqDec_dec eqda) a lsa);
    destruct (in_dec (EqDec_dec eqdb) (inj a) (map inj lsa));
    intuition.
  exfalso.
  apply n.
  apply in_map_iff.
  econstructor.
  intuition.
  apply in_map_iff in i.
  destruct i.
  intuition.
  apply H in H1.
  subst.
  intuition.
Qed.

Require Import Permutation.

Theorem Permutation_hasDups : 
  forall (A : Set)(eqd : EqDec A)(ls1 ls2 : list A),
    Permutation ls1 ls2 ->
    hasDups eqd ls1 = hasDups eqd ls2.
  
  intuition.
  case_eq ( hasDups eqd ls1); intuition.
  apply hasDups_true_not_NoDup in H0.
  intuition.
  case_eq (hasDups eqd ls2); intuition.
  apply hasDups_false_NoDup in H1; intuition.
  
  exfalso.
  eapply H0.
  eapply permutation_NoDup.
  eapply Permutation_sym.
  eauto.
  trivial.
  
  eapply hasDups_false_NoDup in H0; intuition.
  case_eq (hasDups eqd ls2); intuition.
  apply hasDups_true_not_NoDup in H1.
  exfalso.
  apply H1.
  eapply permutation_NoDup;
    eauto.
     
Qed.

Require Import fcf.RndInList.

Section DupProb.

  Variable A B : Set.
  Hypothesis eqdb : EqDec B.
  Variable eta : nat.

  Theorem dupProb : 
    forall (ls : list A),
      Pr[x <-$ compMap _ (fun _ => {0, 1}^eta) ls; ret (hasDups _ x)] <= 
      (length ls ^ 2 / 2 ^ eta).

    Local Opaque evalDist.

    induction ls; intuition; simpl in *.

    comp_simp.
    simpl.
    rewrite evalDist_ret_0.
    eapply rat0_le_all.
    intuition.

    assert (
        Pr 
   [x <-$
    (b <-$ { 0 , 1 }^eta;
     lsb' <-$ compMap (Bvector_EqDec eta) (fun _ : A => { 0 , 1 }^eta) ls;
     ret b :: lsb'); ret hasDups (Bvector_EqDec eta) x ]
   ==
   Pr 
   [p <-$ 
      (b <-$ { 0 , 1 }^eta;
       lsb' <-$ compMap (Bvector_EqDec eta) (fun _ : A => { 0 , 1 }^eta) ls;
       ret (b, lsb'));
     ret hasDups (Bvector_EqDec eta) (snd p) || if (in_dec (EqDec_dec _) (fst p) (snd p)) then true else false ]
   ).

    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    comp_simp.
    simpl.
    destruct (in_dec (EqDec_dec (Bvector_EqDec eta)) x x0).
    rewrite orb_true_r.
    reflexivity.
    rewrite orb_false_r.
    reflexivity. 
    rewrite H.
    clear H.

    rewrite evalDist_orb_le.

    assert (
        (length ls / 2^eta + (length ls ^ 2) / 2 ^ eta)
          <=
        (S (length ls * 1 + length ls * S (length ls * 1)) / 2 ^ eta)
              ).
    
    eapply leRat_trans.
    2:{
      eapply leRat_terms.
      eapply le_n_Sn.
      reflexivity.
    }

    eapply leRat_trans.
    2:{
      eapply eqRat_impl_leRat.
      symmetry.
      eapply ratAdd_num.
    }

    eapply ratAdd_leRat_compat.
    eapply leRat_terms; omega.
    eapply leRat_terms; intuition.
    simpl.
    eapply mult_le_compat; intuition.

    eapply leRat_trans.
    2:{
      eapply H.
    }
    rewrite ratAdd_comm.
    eapply ratAdd_leRat_compat.

    assert (
        Pr 
   [x <-$
    (b <-$ { 0 , 1 }^eta;
     lsb' <-$ compMap (Bvector_EqDec eta) (fun _ : A => { 0 , 1 }^eta) ls;
     ret (b, lsb'));
    ret (if in_dec (EqDec_dec (Bvector_EqDec eta)) (fst x) (snd x)
         then true
         else false) ]
   ==
   Pr 
   [
     lsb' <-$ compMap (Bvector_EqDec eta) (fun _ : A => { 0 , 1 }^eta) ls;
     b <-$ { 0 , 1 }^eta;
     ret (if in_dec (EqDec_dec (Bvector_EqDec eta)) b lsb'
         then true
         else false) ]
   ).

    comp_swap_r.
    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    simpl.
    reflexivity.
    rewrite H0.
    clear H0.
    comp_irr_l.
    eapply compMap_wf.
    intuition.
    wftac.
    eapply RndInList_prob.
    erewrite compMap_length; eauto.

    eapply leRat_trans.
    2:{
      eapply IHls.
    }
    inline_first.
    comp_irr_l.
    wftac.
    inline_first.
    comp_skip.
    simpl.
    reflexivity.
  Qed.

End DupProb.

