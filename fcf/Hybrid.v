(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import fcf.FCF.
Require Import fcf.CompFold.

Open Scope list_scope.

Section DistSingle.

  Variable A B : Set.
  Hypothesis B_EqDec : EqDec B.
  Variable c1 c2 : A -> Comp B.
  Variable A_State : Set.
  Variable A1 : Comp (A * A_State).
  Variable A2 : A_State -> B -> Comp bool.

  Definition DistSingle_G(c : A -> Comp B) :=
    [a, s_A] <-$2 A1;
    b <-$ c a;
    A2 s_A b.

  Definition DistSingle_Adv :=
    | Pr[DistSingle_G c1] - Pr[DistSingle_G c2] |.

End DistSingle.

Section ListHybrid.

  Variable A B State : Set.
  Variable defA : A.
  Variable c1 c2 : A -> Comp B.
  Hypothesis c1_wf : forall a, well_formed_comp (c1 a).
  Hypothesis c2_wf : forall a, well_formed_comp (c2 a).
  Hypothesis A_EqDec : EqDec A.
  Hypothesis B_EqDec : EqDec B.
  Hypothesis State_EqDec : EqDec State.
  Variable A1 : Comp ((list A) * State).
  Variable A2 : State -> list B -> Comp bool.

  Variable maxA : nat.
  Hypothesis maxA_correct : 
    forall ls s_A, 
      In (ls, s_A) (getSupport A1) ->
      (length ls <= maxA)%nat.

  Definition ListHybrid_G (c : A -> Comp B) :=
    [lsA, s_A] <-$2 A1;
    lsB <-$ compMap _ c lsA;
    A2 s_A lsB.

  Definition ListHybrid_Advantage :=
    | Pr[ListHybrid_G c1] - Pr[ListHybrid_G c2] |.

  Definition G_hybrid i :=
    [lsA, s_A] <-$2 A1;
    lsA1 <- firstn i lsA;
    lsA2 <- skipn i lsA;
    lsB1 <-$ compMap _ c1 lsA1;
    lsB2 <-$ compMap _ c2 lsA2;
    A2 s_A (lsB1 ++ lsB2).
  
  Theorem G_2_hybrid_eq : 
    Pr[ListHybrid_G c2] == Pr[G_hybrid 0].
    
    unfold ListHybrid_G, G_hybrid.
    comp_skip.
    comp_simp.
    eapply comp_spec_eq_impl_eq.
    simpl.
    comp_simp.
    simpl.
    eapply comp_spec_eq_refl.
    
  Qed.

    
  Theorem skipn_ge_nil : 
    forall (A : Type)(ls : list A)(n : nat),
      n >= length ls ->
      skipn n ls = nil.
    
    induction ls; destruct n; intuition; simpl in *.
    omega.
    eapply IHls.
    omega.
    
  Qed.

  Theorem G_1_hybrid_eq : 
    Pr[ListHybrid_G c1] == Pr[G_hybrid maxA].
    
    unfold ListHybrid_G, G_hybrid.
    comp_skip.
    comp_simp.
    rewrite firstn_ge_all.
    comp_skip.     

    rewrite skipn_ge_nil.
    eapply comp_spec_eq_impl_eq.
    simpl.
    comp_simp.
    rewrite app_nil_r.
    eapply comp_spec_eq_refl.
    eauto.
    eauto.
    
  Qed.                             

  Definition B1 i :=
    [lsA, s_A] <-$2 A1;
    lsA1 <- firstn i lsA;
    a <- nth i lsA defA;
    lsA2 <- skipn (S i) lsA;
    incla <- if (lt_dec i (length lsA)) then true else false;
    ret (a, (incla, lsA1, lsA2, s_A)).                                                

  Definition B2 (e : bool * _ * _ * _) b :=
      let '(incla, lsA1, lsA2, s_A) := e in 
      lsB1 <-$ compMap _ c1 lsA1;
        lsB2 <-$ compMap _ c2 lsA2;
        lsB <- if incla then (lsB1 ++ (b :: lsB2)) else lsB1;
      A2 s_A lsB.

  Local Open Scope list_scope.

  Theorem compMap_unroll : 
    forall (A B : Set)(eqdb : EqDec B)(c : A -> Comp B)(ls : list A)(def : A),
      ls <> nil ->
      comp_spec eq (compMap _ c ls) (x <-$ c (hd def ls); y <-$ compMap _ c (tl ls); ret (x :: y)).
    
    induction ls; intuition; simpl in *.
    comp_skip.
    
  Qed.

  Theorem skipn_lt_nil_false : 
    forall (A : Type)(ls : list A)(n : nat),
      n < length ls ->
      skipn n ls = nil ->
      False.
    
    induction ls; intuition; simpl in *.
    omega.
    destruct n; simpl in *; intuition.
    discriminate.
    eapply IHls; eauto.
    omega.
    
  Qed.

  Theorem hd_skip_eq_nth : 
    forall (A : Type)(def : A)(ls : list A)(n : nat),
      hd def (skipn n ls) = nth n ls def.
    
    induction ls; destruct n; intuition; simpl in *.
    eauto.
    
  Qed.

  Theorem tl_skipn_eq : 
    forall (A : Type)(ls : list A)(n : nat),
      tl (skipn n ls) = skipn (S n) ls.
    
    induction ls; intuition; simpl in *.
    rewrite skipn_nil.
    trivial.
    
    destruct n; simpl in *.
    trivial.
    eauto.

  Qed.

  Theorem skipn_gt_nil : 
    forall (A : Type)(ls : list A)(n : nat),
      n >= length ls ->
      skipn n ls = nil.
    
    induction ls; destruct n; intuition; simpl in *.
    omega.
    eapply IHls; eauto.
    omega.
    
  Qed.

  Theorem G_hybrid_DistSingle_eq : 
    forall i,
      Pr[G_hybrid i] == Pr[DistSingle_G (B1 i) B2 c2].

    intuition.
    unfold G_hybrid, DistSingle_G, B1, B2.
    inline_first.
    comp_skip.
    comp_simp.
    comp_swap_r.
    comp_skip.

    eapply comp_spec_eq_impl_eq.
    destruct (lt_dec i (length l)).
    eapply comp_spec_eq_trans.
    eapply comp_spec_seq_eq; eauto with inhabited.
    eapply compMap_unroll.
    intuition.
    
    
    eapply skipn_lt_nil_false;
      eauto.

    intuition.
    eapply comp_spec_eq_refl.
    inline_first.
    comp_skip.


    rewrite hd_skip_eq_nth.
    eapply comp_spec_eq_refl.
    subst.
    inline_first.

    
    rewrite tl_skipn_eq.
    comp_skip.

    rewrite skipn_gt_nil; intuition.
    simpl.
    comp_simp.
    rewrite app_nil_r.
    comp_irr_r.
    comp_irr_r.
    eapply compMap_wf.
    intuition.
  Qed.
     
  Theorem compMap_unroll_tl : 
    forall (A B : Set)(def : A)(eqdb : EqDec B)(c : A -> Comp B)(ls : list A) n,
      length ls = S n ->
      comp_spec eq (compMap _ c ls) (y <-$ compMap _ c (firstn n ls); x <-$ c (nth n ls def); ret (y ++ x :: nil)).
    
    induction ls; intuition; simpl in *.
    omega.
    
    destruct n.
    destruct ls.
    simpl in *.
    comp_simp.
    comp_skip.
    simpl.
    eapply comp_spec_eq_refl.
    simpl in*.
    omega.
    
    simpl.
    inline_first.
    comp_skip.
    eapply comp_spec_eq_trans.
    eapply comp_spec_seq_eq; eauto with inhabited.
    intros.
    eapply comp_spec_eq_refl.
    inline_first.
    comp_skip.
    inline_first.
    comp_simp.
    comp_skip.
    rewrite <- app_comm_cons.
    eapply comp_spec_eq_refl.
    
  Qed.
             
  Theorem firstn_firstn : 
    forall (A : Type)(ls : list A)(n1 n2 : nat),
      (n1 <= n2)%nat ->
      firstn n1 (firstn n2 ls) = firstn n1 ls.
    
    induction ls; destruct n1; destruct n2; intuition; simpl in *.
    omega.
    
    f_equal.
    eapply IHls.
    omega.
       
  Qed.

  Theorem nth_firstn : 
    forall (A : Set)(def : A)(ls : list A)(n1 n2 : nat),
      (n1 < n2)%nat ->
      nth n1 (firstn n2 ls) def = nth n1 ls def.
    
    induction ls; destruct n1; destruct n2; intuition; simpl in *.
    omega.
    omega.
    eapply IHls.
    omega.
  Qed.

  Theorem G_hybrid_DistSingle_S_eq : 
    forall i,
      Pr[G_hybrid (S i)] == Pr[DistSingle_G (B1 i) B2 c1].

    intuition.
    unfold G_hybrid, DistSingle_G, B1, B2.
    inline_first.
    comp_skip.
    comp_simp.
    eapply comp_spec_eq_impl_eq.
    destruct (lt_dec i (length l)).

    eapply comp_spec_eq_trans.
    eapply comp_spec_seq_eq; eauto with inhabited.
    eapply compMap_unroll_tl.
    rewrite firstn_length.
    eapply min_l.
    omega.
    intuition.
    eapply comp_spec_eq_refl.
    inline_first.


    rewrite firstn_firstn.
    comp_swap_r.
    comp_skip.
    inline_first.

    
    rewrite nth_firstn.
    comp_skip.
    comp_skip.
    rewrite <- app_assoc.
    rewrite <- app_comm_cons.
    simpl.
    eapply comp_spec_eq_refl.
    omega.
    omega.

    comp_irr_r.

    repeat rewrite firstn_ge_all.
    comp_skip.
    comp_skip.
    rewrite skipn_gt_nil in H3.
    simpl in *.
    intuition.
    subst.
    rewrite app_nil_r.
    eapply comp_spec_eq_refl.
    omega.
    omega.
    omega.
    
  Qed.
        
  Theorem hybrid_incr_close : 
    forall i,
  | Pr[G_hybrid i] - Pr[G_hybrid (S i)] | == DistSingle_Adv c1 c2 (B1 i) B2. 
    
    intuition.
    unfold DistSingle_Adv.

    rewrite G_hybrid_DistSingle_eq.
    rewrite G_hybrid_DistSingle_S_eq.
    eapply ratDistance_comm.
  Qed.
         
  Theorem ratDistance_sequence_sum : 
    forall (f : nat -> Rat)(n : nat),
  | f O - f n | <= sumList (forNats n) (fun i => | f i - f (S i) |).
    
    induction n; intuition; simpl in *.
    unfold sumList.
    simpl.
    eapply eqRat_impl_leRat.
    rewrite <- ratIdentityIndiscernables.
    intuition.
    
    eapply leRat_trans.
    2:{
      eapply eqRat_impl_leRat.
      symmetry.
      eapply sumList_cons.
    }
    simpl.
    eapply leRat_trans.
    eapply ratDistance_le_trans.
    eapply IHn.
    eapply leRat_refl.
    rewrite ratAdd_comm.
    intuition.
    
  Qed.
  
  Theorem Single_impl_ListHybrid_sum :
    ListHybrid_Advantage
    <=
    sumList (forNats maxA) (fun i => DistSingle_Adv c1 c2 (B1 i) B2).

    unfold ListHybrid_Advantage.
    rewrite G_1_hybrid_eq.
    rewrite G_2_hybrid_eq.
    rewrite ratDistance_comm.
    rewrite (@ratDistance_sequence_sum (fun i => Pr[G_hybrid i])); intuition.
    eapply sumList_le.
    intuition.
    eapply eqRat_impl_leRat.
    eapply hybrid_incr_close.

  Qed.

  Variable maxDistance : Rat.
  Hypothesis maxDistance_correct : 
    forall i, DistSingle_Adv c1 c2 (B1 i) B2 <= maxDistance.

  Theorem Single_impl_ListHybrid : 
    ListHybrid_Advantage <= maxA / 1 * maxDistance.

    rewrite Single_impl_ListHybrid_sum.
    eapply leRat_trans.
    eapply sumList_le.
    intros.
    eapply maxDistance_correct.
    rewrite sumList_body_const.
    rewrite forNats_length.
    rewrite ratMult_comm.
    intuition.

  Qed.
End ListHybrid.
