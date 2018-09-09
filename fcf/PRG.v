(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
(* Construction of a pseudorangom generator from a one-way permutations on bit vector with an associated hard core predicate. *)

Set Implicit Arguments.

Require Import fcf.FCF.
Require Import fcf.SemEquiv.

Section OneWayPermutation.

  Variable n : nat.

  Variable f : Bvector n -> Bvector n.
  Variable f_inv : Bvector n -> Bvector n.
  
  Hypothesis f_inv1 : forall v, f (f_inv v) = v.
  Hypothesis f_inv2 : forall v, f_inv (f v) = v.

  Variable A : Bvector n -> Comp (Bvector n).

  Definition OWP_G :=
    c <-$ {0, 1} ^ n;
    a <-$ A (f c);
    ret (eqb a c).

  Definition OWP_Advantage := | (Pr[OWP_G])  - (1 / (2 ^ n)) |.

End OneWayPermutation.


Section HardCorePredicate.

  Variable n : nat.
  Variable f : Bvector n -> Bvector n.
  Variable b : Bvector n -> bool.

  Variable A : Bvector n -> bool -> Comp bool.

  Definition HCP_G1 :=
    r <-$ {0, 1} ^ n;
    g <-$ (A (f r) (b r));
    ret g.

  Definition HCP_G2 :=
    rb <-$ {0, 1};
    r <-$ {0, 1} ^ n;
    g <-$ (A (f r) rb);
    ret g.
   
  Definition HCP_Advantage := | (Pr[HCP_G1]) - (Pr[HCP_G2]) | .
      
End HardCorePredicate.

Definition vector_firstPart_h(A : Set)(m1 m2 : nat)(v : Vector.t A (m1 + m2)) : {ls : list A | length ls = m1}.
refine (exist _ (firstn m1 (Vector.to_list v)) _).
eapply eq_trans.
apply firstn_length.
rewrite to_list_length.
eapply min_l.
omega.
Defined.

Fixpoint firstPart(A : Set)(m1 m2 : nat)(v : Vector.t A (m1 + m2)) : Vector.t A m1 :=
  of_sig_list (vector_firstPart_h m1 m2 v).

Theorem skipn_length : forall (A : Set) n0 (ls : list A),
  length (skipn n0 ls) = (length ls) - n0.
  
  induction n0; intuition; simpl in *.
  
  destruct ls; simpl.
  trivial.
  eauto.
Qed.

Definition vector_secondPart_h(A : Set)(m1 m2 : nat)(v : Vector.t A (m1 + m2)) : {ls : list A | length ls = m2}.
refine (exist _ (skipn m1 (Vector.to_list v)) _).
rewrite skipn_length.
rewrite to_list_length.
omega.
Defined.

Fixpoint secondPart(A : Set)(m1 m2 : nat)(v : Vector.t A (m1 + m2)) : Vector.t A m2 :=
  of_sig_list (vector_secondPart_h m1 m2 v).

Section OWP_impl_HCP.

  Variable n : nat.

  (* f is a one-way permutation *)
  Variable f : Bvector n -> Bvector n.
  Variable f_inv : Bvector n -> Bvector n.
  
  Hypothesis f_inv1 : forall v, f (f_inv v) = v.
  Hypothesis f_inv2 : forall v, f_inv (f v) = v.

  Variable A : Bvector (n + n) -> bool -> Comp bool.

  Definition dotProduct(n : nat)(v1 v2 : Bvector n) :=
    Vector.fold_left2 (fun acc b1 b2 => (xorb acc (andb b1 b2))) false v1 v2.

  (* f' is a one-way function for vectors of length n + n *)
  Definition f'(v : Bvector (n + n)) := 
    Vector.append (f (firstPart n n v)) (secondPart n n v).
  Definition b(v : Bvector (n + n)) := (dotProduct (firstPart n n v) (secondPart n n v)).

  Definition OWP_HCP_B(v : Bvector n) : Comp (Bvector n) :=
    ret v.

  Theorem OWP_HCP : 
    HCP_Advantage f' b A <= (OWP_Advantage f OWP_HCP_B).

  Abort.

End OWP_impl_HCP.

Section PseudorandomGenerator.

  Variable n1 : nat.
  Variable n2 : nat.
  Variable f : Bvector n1 -> Bvector n2.
  Hypothesis n2_greater : n2 > n1.

  Variable A : Bvector n2 -> Comp bool.

  Definition PRG_G1 :=
    r <-$ {0, 1} ^ n1;
    g <-$ (A (f r));
    ret g.

  Definition PRG_G2 :=
    r <-$ {0, 1} ^ n2;
    g <-$ (A r);
    ret g.

  Definition PRG_Advantage := | (Pr[PRG_G1]) - (Pr[PRG_G2]) |.
End PseudorandomGenerator.

Require Import fcf.DetSem.

Section OWP_HCP_Impl_PRG.

  Variable n : nat.
  Hypothesis n_pos : n > 0.

  (* f is a one-way permutation *)
  Variable f : Bvector n -> Bvector n.
  Variable f_inv : Bvector n -> Bvector n.

  Hypothesis f_inv1 : forall v, f (f_inv v) = v.
  Hypothesis f_inv2 : forall v, f_inv (f v) = v.
    
  (* b is a hard-core predicate for f *)
  Variable b : Bvector n -> bool.
  
  Definition OWP_HCP_PRG_fun(v : Bvector n) :=
    (b v) :: (f v).

  (* The PRG distinguisher adversary. *)
  Variable A : Bvector (S n) -> Comp bool.
  Hypothesis wf_A : forall v, well_formed_comp (A v).

  Definition B (v : Bvector n)(b : bool) : Comp bool :=
    (A (b :: v)).


  (* Something equivalent to the following is in the library already, right? *)
  Lemma rnd_concat_eq : forall (v : Bvector (S n)),
    evalDist ({0, 1} ^ (S n)) v ==
    evalDist (rb <-$ {0, 1}; r <-$ {0, 1} ^ n; ret (rb :: r)) v.

    intuition.
    dist_inline_first.
    eapply det_eq_impl_dist_sem_eq; wftac.
    unfold evalDet_equiv.
    intuition.

    inversion H; clear H; subst.
    inversion H0; clear H0; subst.
    simpl in *.
    case_eq (shiftOut s (S n)); intuition.
    rewrite H in H4.
    destruct p.
    inversion H4; clear H4; subst.
    simpl in *.
    inversion H5; clear H5; subst.
    destruct s; simpl in *; try congruence.
    case_eq (shiftOut s n); intuition;
    rewrite H0 in H; try congruence.
    destruct p.
    inversion H; clear H; subst.
    econstructor.
    eapply evalDet_steps_trans.
    eapply evalDet_steps_bind_done.
    econstructor.
    eauto.
    simpl.
    
    rewrite shiftOut_0.
    econstructor.
    eauto.
    simpl.
    econstructor.
    eapply evalDet_steps_trans.
    eapply evalDet_steps_bind_done.
    econstructor.
    eauto.
    simpl.
    econstructor.
    eapply evalDet_steps_trans.
    eapply evalDet_steps_bind_done.
    econstructor.
    eauto.
    simpl.
    rewrite H0.
    econstructor.
    eauto.
    simpl.
    econstructor.
    econstructor.
    eauto.
    simpl.
    econstructor.
    
    rewrite H in H4.
    inversion H4; clear H4; subst.
    
    inversion H0; clear H0; subst.
    simpl in *.
    destruct s; simpl in *.
    econstructor.
    econstructor.
    eauto.
    simpl.
    econstructor.

    case_eq (shiftOut s n); intuition.
    rewrite H in H4.
    destruct p.
    inversion H4; clear H4; subst.
    simpl in *.
    inversion H5; clear H5; subst.
    rewrite H in H4.
    econstructor.
    econstructor.
    eauto.
    simpl.
    rewrite shiftOut_0.
    econstructor.
    eauto.
    simpl.
    econstructor.
    eauto.
    simpl.
    econstructor.
    eauto.
    simpl.
    rewrite H.
    econstructor.


    inversion H; clear H; subst.
    inversion H0; clear H0; subst.
    simpl in *.
    case_eq (shiftOut s 1); intuition;
    rewrite H in H4.
    destruct p.
    inversion H4; clear H4; subst.
    simpl in *.
    inversion H5; clear H5; subst.
    simpl in *.
    inversion H4; clear H4; subst.
    simpl in *.
    case_eq (shiftOut b1 n); intuition;
    rewrite H0 in H5.
    destruct p.
    inversion H5; clear H5; subst.
    simpl in *.
    inversion H6; clear H6; subst.
    simpl in *.
    inversion H5; clear H5; subst.
    econstructor.
    econstructor.
    eauto.
    simpl.
    destruct s; simpl in *; try discriminate.
    rewrite shiftOut_0 in H.
    inversion H; clear H; subst.
    rewrite H0.
    econstructor.
    eauto.
    simpl.
    econstructor.
    inversion H5.
    inversion H4.
    
    inversion H0; clear H0; subst.
    simpl in *.
    destruct s.
    simpl in *.
    econstructor.
    econstructor.
    eauto.
    simpl.
    econstructor.

    simpl in *.
    rewrite shiftOut_0 in H4.
    inversion H4; clear H4; subst.
    simpl in *.
    inversion H3; clear H3; subst.
    simpl in *.
    inversion H4; clear H4; subst.
    simpl in *.
    case_eq (shiftOut s n); intuition;
    rewrite H in H3.
    destruct p.
    inversion H3; clear H3; subst.
    simpl in *.
    inversion H5; clear H5; subst.
    simpl in *.
    inversion H4.

    econstructor.
    econstructor.
    eauto.
    simpl.
    rewrite H.
    econstructor.
  Qed.


  Theorem OWP_HCP_PRG : 
    PRG_Advantage OWP_HCP_PRG_fun A <= (HCP_Advantage f b B).

    unfold OWP_HCP_PRG_fun, PRG_Advantage, PRG_G1, PRG_G2, HCP_Advantage, HCP_G1, HCP_G2, B.
    
    eapply eqRat_impl_leRat.
    eapply ratDistance_eqRat_compat.
    intuition.

    eapply eqRat_trans.
    eapply evalDist_seq_eq.

    eapply rnd_concat_eq.
    intuition.
    eapply eqRat_refl.

    dist_inline_first.
    comp_skip.
    comp_simp.
    inline_first.

    eapply (distro_iso_eq f f_inv); intuition. 
    simpl; eauto using in_getAllBvectors.
    
    apply uniformity.

    comp_simp.

    intuition.
   
  Qed.
    


End OWP_HCP_Impl_PRG.


Print Assumptions OWP_HCP_PRG. 
   