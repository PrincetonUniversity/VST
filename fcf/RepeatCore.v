(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* This file contains two high level arguments:

  1) (DistSingle) When an adversary cannot distinguish two distributions when given one sample, then he cannot distinguish the distributions when given polynomially many samples.

  2) (RepeatCore) When an adversary cannot distinguish two distributions when given a polynomial number of samples, he cannot distinguish the distributions when given one sample from some "core" of the distributions that has polynomial size. 

*)

Set Implicit Arguments.

Require Import fcf.FCF.
Require Import fcf.CompFold.
Require Import fcf.RndNat.
Require Export fcf.Hybrid.

Local Open Scope list_scope.


(* An argument showing that two distributions are indistinguishable even when multiple samples are given to the adversary. *)

Section DistMult.

  Variable A B : Set.
  Hypothesis B_EqDec : EqDec B.
  Variable c1 c2 : A -> Comp B.
  Variable A_State : Set.
  Variable A1 : Comp (A * A_State).
  Variable A2 : A_State -> list B -> Comp bool.

  Variable n : nat.

  Definition DistMult_G(c : A -> Comp B) :=
    [a, s_A] <-$2 A1;
    b <-$ compMap _ (fun _ => (c a)) (forNats n);
    A2 s_A b.

  Definition DistMult_Adv :=
    | Pr[DistMult_G c1] - Pr[DistMult_G c2] |.

End DistMult.


Section DistSingle_impl_Mult.

  Variable A B : Set.
  Variable A_EqDec : EqDec A.
  Variable B_EqDec : EqDec B.
  Variable c1 c2 : A -> Comp B.
  Variable A_State : Set.
  Variable A_State_EqDec : EqDec A_State.
  Variable A1 : Comp (A * A_State).
  Variable A2 : A_State -> list B -> Comp bool.
  
  Hypothesis c1_wf : forall a, well_formed_comp (c1 a).
  Hypothesis c2_wf : forall a, well_formed_comp (c2 a).

  (* Produce a list of length n derived from c1, and c2.  The first i values come from c1, and the rest come from c2. *)
  Definition computeHybrid(n i : nat) a : Comp (list B) :=
    b1 <-$ compMap _ (fun _ => (c1 a)) (forNats i);
    b2 <-$ compMap _ (fun _ => (c2 a)) (forNats (minus n i));
    ret (b1 ++ b2).

  Variable n : nat.
  Hypothesis n_pos : n > 0.

  Theorem hybrid_replace_c1_equiv : 
    forall i x a,
      i < n ->
      evalDist 
        (b <-$ (c1 a);
         hybrid <-$ computeHybrid n i a;
         ret (listReplace hybrid i b b)) x ==
      evalDist (computeHybrid n (S i) a) x.

    induction n; destruct i; intuition; try omega.
    unfold computeHybrid.
    unfold minus.
    fold minus.
    rewrite <- minus_n_O.
    unfold forNats.
    fold forNats.
    unfold compMap.
    fold compMap.
    inline_first.
    comp_skip.
    inline_first.
    comp_simp.
    comp_irr_l.
    inline_first.
    comp_skip.
    simpl.
    intuition.

    unfold computeHybrid.
    unfold minus.
    fold minus.
    unfold forNats.
    fold forNats.
    unfold compMap.
    fold compMap.

    inline_first.
    do 2 comp_at comp_inline leftc 1%nat.
    comp_swap_l.
    comp_skip.

    assert 
      (evalDist
     (a1 <-$
      (lsb' <-$
       (b <-$ (c1 a);
        lsb' <-$ compMap B_EqDec (fun _ : nat => (c1 a)) (forNats i);
        ret b :: lsb'); ret x0 :: lsb');
      a2 <-$ compMap B_EqDec (fun _ : nat => (c2 a)) (forNats (n0 - S i));
      ret a1 ++ a2) x == 
       evalDist
     (ls <-$ (computeHybrid n0 (S i) a);
      ret (x0 :: ls)) x).

    unfold computeHybrid.
    unfold forNats.
    fold forNats.
    unfold compMap.
    fold compMap.
    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    comp_simp.
    inline_first.
    comp_skip.
    comp_simp.
    simpl.
    intuition.
    rewrite H1.
    clear H1.
    eapply eqRat_trans.
    2:{
      comp_skip.
      eapply eqRat_refl.
    }
    unfold computeHybrid.
    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    comp_simp.
    simpl.
    intuition.

  Qed.


  Theorem hybrid_replace_c2_equiv : 
    forall i x a,
      i < n ->
      evalDist 
        (b <-$ (c2 a);
         hybrid <-$ computeHybrid n i a;
         ret (listReplace hybrid i b b)) x ==
      evalDist (computeHybrid n i a) x.

    induction n; destruct i; intuition; try omega.

    unfold computeHybrid.
    unfold minus.
    unfold forNats.
    fold forNats.
    unfold compMap.
    fold compMap.
    comp_simp.
    inline_first.
    comp_skip.
    inline_first.
    comp_irr_l.
    inline_first.
    comp_skip.
    comp_simp.
    simpl.
    intuition.
   
    unfold computeHybrid.
    unfold minus.
    fold minus.
    unfold forNats.
    fold forNats.
    unfold compMap.
    fold compMap.
    inline_first.
    do 2 comp_at comp_inline leftc 1%nat.
    comp_swap_l.
    comp_skip.

    assert (evalDist
     (a1 <-$
      (lsb' <-$ compMap B_EqDec (fun _ : nat => (c1 a)) (forNats i);
       ret x0 :: lsb');
      a2 <-$ compMap B_EqDec (fun _ : nat => (c2 a)) (forNats (n0 - i));
      ret a1 ++ a2) x == 
            evalDist
     (ls <-$ 
         (a1 <-$ compMap B_EqDec (fun _ : nat => (c1 a)) (forNats i);
          a2 <-$ compMap B_EqDec (fun _ : nat => (c2 a)) (forNats (n0 - i));
          ret a1 ++ a2);
         ret (x0 :: ls)) x).

    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    comp_simp.
    rewrite app_comm_cons.
    intuition.
    rewrite H1.
    clear H1.
    eapply eqRat_trans.
    2:{
      comp_skip.
      eapply IHn0.
      omega.
      omega.
      eapply eqRat_refl.
    }
    unfold computeHybrid.
    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    inline_first.
    comp_skip.
    comp_simp.
    simpl.
    intuition.
  Qed.

  Definition B1 : Comp (A * (A * A_State)) :=
    [a, s_A] <-$2 A1;
    ret (a, (a, s_A)). 

  Definition B2(s : A * A_State)(b : B) : Comp bool :=
    [a, s_A] <-2 s;
    i <-$ [0 .. n);
    rndHybrid <-$ computeHybrid n i a;
    distHybrid <- listReplace rndHybrid i b b;
    A2 s_A distHybrid.

  Definition DistSingle_G1(c : A -> Comp B) :=
    [a, s_A] <-$2 B1; 
    b <-$ (c a); 
    B2 s_A b.

  Theorem DistSingle_G1_equiv : 
      DistSingle_Adv c1 c2 B1 B2 ==
      (| Pr[DistSingle_G1 c1] - Pr[DistSingle_G1 c2] |).

    unfold DistSingle_Adv, DistSingle_G1, DistSingle_G.
    intuition.

  Qed.

  Definition DistSingle_G2(c : A -> Comp B) :=
    [a, s_A] <-$2 A1;
    i <-$ [ 0  .. n);
    distHybrid <-$
               (b <-$ c a;
                rndHybrid <-$ computeHybrid n i a;
                ret (listReplace rndHybrid i b b)); 
    A2 s_A distHybrid.

  Theorem DistSingle_G2_equiv : 
    forall c, 
      Pr[DistSingle_G1 c] == Pr[DistSingle_G2 c].

    intuition.
    unfold DistSingle_G1, DistSingle_G2.
    unfold B1, B2.
    inline_first.
    comp_skip.
    comp_simp.
    comp_swap_l.
    comp_skip.
    inline_first.
    comp_skip.
    comp_inline_r.
    comp_skip.
    comp_simp.
    intuition.

  Qed.

  Definition DistSingle_G3_c2 :=
    i <-$ [ 0  .. n);
    [a, s_A] <-$2 A1;
    distHybrid <-$ computeHybrid n i a;
    A2 s_A distHybrid.

  Definition DistSingle_G3_c1 :=
    i <-$ [ 0  .. n);
    [a, s_A] <-$2 A1;
    distHybrid <-$ computeHybrid n (S i) a;
    A2 s_A distHybrid.

  Theorem DistSingle_G3_c2_equiv : 
    Pr[DistSingle_G2 c2] == Pr[DistSingle_G3_c2].

    unfold DistSingle_G2, DistSingle_G3_c2.
    comp_swap_r.
    comp_skip.
    comp_simp.
    comp_skip.
    comp_skip.
    eapply hybrid_replace_c2_equiv.
    eapply RndNat_support_lt; intuition.
    
  Qed.

  Theorem DistSingle_G3_c1_equiv : 
    Pr[DistSingle_G2 c1] == Pr[DistSingle_G3_c1].

    unfold DistSingle_G2, DistSingle_G3_c1.
    comp_swap_r.
    comp_skip.
    comp_simp.
    comp_skip.
    comp_skip.
    eapply hybrid_replace_c1_equiv.
    eapply RndNat_support_lt; intuition.
    
  Qed.

  Theorem compMap_computeHybrid_0_equiv : 
    forall s_A a, 
      Pr  [b <-$ compMap B_EqDec (fun _ : nat => (c2 a)) (forNats n); A2 s_A b ] ==
      Pr  [x <-$ computeHybrid n 0 a; A2 s_A x ].
    
    intuition.
    unfold computeHybrid.
    unfold forNats.
    fold forNats.
    inline_first.
    unfold compMap.
    fold compMap.
    comp_simp.
    inline_first.
    rewrite <- minus_n_O.
    comp_skip.
    comp_simp.
    simpl.
    intuition.
  Qed.
  
  Theorem compMap_computeHybrid_n_equiv : 
    forall s_A a,
    Pr  [b <-$ compMap B_EqDec (fun _ : nat => (c1 a)) (forNats n); A2 s_A b ] ==
    Pr  [x <-$ computeHybrid n n a; A2 s_A x ].

    intuition.
    unfold computeHybrid.
    inline_first.
    comp_skip.
    
    inline_first.
    rewrite minus_diag.
    unfold forNats.
    unfold compMap.
    comp_simp.
    rewrite app_nil_r.
    intuition.
  Qed.

  Theorem DistSingle_impl_Mult : 
    DistMult_Adv _ c1 c2 A1 A2 n <= (n / 1) * (DistSingle_Adv c1 c2 B1 B2).

    eapply leRat_trans.
    2:{
      eapply eqRat_impl_leRat.
      rewrite DistSingle_G1_equiv.
      rewrite DistSingle_G2_equiv.
      rewrite DistSingle_G2_equiv.
      rewrite DistSingle_G3_c1_equiv.
      rewrite DistSingle_G3_c2_equiv.
      eapply eqRat_refl.
    }
    
    eapply leRat_trans.
    2:{
      eapply eqRat_impl_leRat.
      unfold DistSingle_G3_c1, DistSingle_G3_c2.
      rewrite rndNat_sumList.
      rewrite rndNat_sumList.
      rewrite sumList_factor_constant_l.
      rewrite sumList_factor_constant_l.
      rewrite ratMult_ratDistance_factor_l.
      eapply eqRat_refl.
    }

    eapply leRat_trans.
    2:{
      eapply eqRat_impl_leRat.
      rewrite <-ratMult_assoc.
      rewrite ratMult_eq_rat1.
      rewrite ratMult_1_l.
      rewrite ratDistance_comm.
      rewrite sumList_forNats_distance.
      eapply eqRat_refl.
    }

    unfold DistMult_Adv.
    unfold DistMult_G.
    rewrite ratDistance_comm.
    eapply eqRat_impl_leRat.
    eapply ratDistance_eqRat_compat.

    eapply evalDist_seq; intuition.
    comp_simp.

    eapply compMap_computeHybrid_0_equiv.

    eapply evalDist_seq; intuition.
    comp_simp.
    eapply compMap_computeHybrid_n_equiv.

    Grab Existential Variables.
    econstructor; intuition.

  Qed.

End DistSingle_impl_Mult.

Section RepeatCore.

  Variable A B : Set.
  Hypothesis B_EqDec : EqDec B.
  Variable P : B -> bool.
  Variable c1 c2 : A -> Comp B.

  Variable A_State : Set.
  Variable A1 : Comp (A * A_State ).
  Variable A2 : A_State -> B -> Comp bool.
  
  Definition RepeatCore_G(c : A -> Comp B) :=
    [a, s_A] <-$2 A1;
    b <-$ Repeat (c a) P;
    A2 s_A b.

  Definition RepeatCore_Adv :=
    | Pr[RepeatCore_G c1] - Pr[RepeatCore_G c2] |.

End RepeatCore.


Section DistMult_impl_RepeatCore.

  Variable A B : Set.
  Hypothesis B_EqDec : EqDec B.
  Variable P : B -> bool.
  Variable c1 c2 : A -> Comp B.

  Variable A_State : Set.
  Variable A1 : Comp (A * A_State).
  Variable A2 : A_State -> B -> Comp bool.
  Hypothesis A1_wf : well_formed_comp A1.
  Hypothesis A2_wf : forall s_A b, well_formed_comp (A2 s_A b).

  Hypothesis c1_wf : forall a s_A, In (a, s_A) (getSupport A1) -> well_formed_comp (c1 a).
  Hypothesis c1_repeat_wf : forall a s_A, In (a, s_A) (getSupport A1) -> exists b, In b (filter P (getSupport (c1 a))).

  Hypothesis c2_wf : forall a s_A, In (a, s_A) (getSupport A1) -> well_formed_comp (c2 a).
  Hypothesis c2_repeat_wf : forall a s_A, In (a, s_A) (getSupport A1) -> exists b, In b (filter P (getSupport (c2 a))).

  Variable n : nat.

  (* Assume A1 can effectively distinguish the cores as in RepeatCore_G, construct an adversary B that can distinguish the entire distributions given multiple samples as in DistMult_G. *)

  Definition DM_RC_G1(c : A -> Comp B) :=
    [a, s_A] <-$2 A1;
    p <-$ Repeat (b <-$ (c a); g <-$ (A2 s_A b); ret (b, g)) (fun p => P (fst p)); 
    ret (snd p).

  Theorem DM_RC_G1_equiv :
    forall c x,
      (forall a s_A, In (a, s_A) (getSupport A1) -> well_formed_comp (c a)) ->
      (forall a s_A, In (a, s_A) (getSupport A1) -> exists b, In b (filter P (getSupport (c a)))) ->
      evalDist (RepeatCore_G P A1 A2 c) x == evalDist (DM_RC_G1 c) x.

    intuition.
    unfold RepeatCore_G, DM_RC_G1.
    comp_skip.

    comp_simp.
    assert (evalDist (b0 <-$ Repeat (c a) P; A2 a0 b0) x 
                      ==
                      evalDist (p <-$ (b0 <-$ Repeat (c a) P; b <-$ A2 a0 b0; ret (b0, b)); ret (snd p)) x).
    inline_first.
    comp_skip.
    inline_first.
    rewrite <- evalDist_right_ident.
    comp_skip.
    comp_simp.
    simpl.
    reflexivity.
    rewrite H2.
    comp_skip.
    
    eapply repeat_fission; intuition.
    eauto.
    eauto.
  Qed.

  Definition DM_RC_G2(c : A -> Comp B) :=
    [a, s_A] <-$2 A1;
    p <-$ Repeat (b <-$ (c a); g <-$ (A2 s_A b); ret (b, g)) (fun p => P (fst p));
    ret (Some (snd p)).

  Theorem DM_RC_G2_equiv :
     forall c x,
       evalDist (DM_RC_G1 c) x == evalDist (DM_RC_G2 c) (Some x).

     intuition.
     unfold DM_RC_G1, DM_RC_G2.
     comp_skip.
     comp_simp.
     comp_skip.
     dist_compute.
   Qed.

  Definition DM_RC_G3(c : A -> Comp B) :=
    [a, s_A] <-$2 A1;
    ls <-$ compMap _ (fun _ => b <-$ c a; g <-$ (A2 s_A b); ret (b, g)) (forNats n);
    ret hd_error (map (fun x => snd x) (filter (fun p => P (fst p)) ls)).

  Theorem DM_RC_G2_G3_close : 
     forall (c : A -> Comp B) k x,
       (forall a s_A, In (a, s_A) (getSupport A1) -> well_formed_comp (c a)) ->
       (forall a s_A, In (a, s_A) (getSupport A1) -> exists b, In b (filter P (getSupport (c a)))) ->
       (forall a s_A, In (a, s_A) (getSupport A1) -> Pr[b <-$ c a; ret (negb (P b))] <= k) ->
       | evalDist (DM_RC_G2 c) x - evalDist (DM_RC_G3 c) x | <= expRat k n.

     intuition.
     unfold DM_RC_G2, DM_RC_G3.

     eapply evalDist_bind_distance; intuition.

     rewrite ratDistance_comm.
     eapply leRat_trans.

     eapply compMap_Repeat_close.
     wftac.

     edestruct H0.
     eauto.
     apply filter_In in H3.
     intuition.
     specialize (A2_wf b0 x0).
     apply well_formed_val_exists in A2_wf.
     destruct A2_wf.
     econstructor.
     eapply filter_In.
     intuition.
     eapply getSupport_In_Seq.
     eauto.
     eapply getSupport_In_Seq.
     eauto.
     simpl.
     intuition.
     simpl.
     trivial.

     eapply expRat_leRat_compat.
     eapply leRat_trans.
     2:{
      eapply H1.
      eauto.
     }
     comp_inline_l.
     comp_skip.
     inline_first.
     comp_irr_l.
     simpl.
     intuition.
  Qed.

  Definition DM_RC_G4(c : A -> Comp B) :=
     [a, s_A] <-$2 A1;
     allB <-$ compMap _ (fun _ => (c a)) (forNats n);
     allB_G <-$ compMap _ (fun b => g <-$ (A2 s_A b); ret (b, g)) allB;
     ret hd_error (map (fun x => snd x) (filter (fun p => P (fst p)) allB_G)).

  Theorem DM_RC_G4_equiv : 
     forall c x, 
     evalDist (DM_RC_G3 c) x == evalDist (DM_RC_G4 c) x.

     intuition.
     unfold DM_RC_G3, DM_RC_G4.
     comp_skip.
     symmetry.
     comp_simp.
     rewrite <- evalDist_assoc; intuition.
     comp_skip.
     eapply comp_spec_eq_impl_eq.
     eapply (@compMap_fission_eq _ _ _ _ _ _ _ _ _ _ _ _ eq); intuition.
     simpl.
     eapply comp_spec_eq_refl.

     subst.
     simpl.
     eapply eq_impl_comp_spec_eq.
     intuition.
     comp_at comp_inline rightc 1%nat.
     comp_swap_r.
     inline_first.
     comp_skip.
     comp_skip.
     comp_simp.
     intuition.
   Qed.
   
   Definition DM_RC_G5(c : A -> Comp B) :=
     [a, s_A] <-$2 A1;
     allB <-$ compMap _ (fun _ => (c a)) (forNats n);
     allG <-$ compMap _ (A2 s_A) (filter P allB);
     ret hd_error allG.

   Theorem DM_RC_G5_equiv : 
     forall (c : A -> Comp B) x,
       evalDist (DM_RC_G4 c) x ==
     evalDist (DM_RC_G5 c) x.

     intuition.
     unfold DM_RC_G4, DM_RC_G5.
     comp_skip.
     comp_simp.
     comp_skip.
     symmetry.
     eapply eqRat_trans.
     comp_skip.
     eapply compMap_filter.
     intuition.
     eapply eqRat_refl.
     inline_first.
     comp_skip.

     dist_compute.
   Qed.

   Definition DM_RC_G6(c : A -> Comp B) :=
    [a, s_A] <-$2 A1;
    opt_b' <-$ (
             b <-$ compMap B_EqDec (fun _ : nat => (c a)) (forNats n);
             ret head (filter P b));
    match opt_b' with
      | Some b' => A2 s_A b'
      | None => ret false
    end.

   Theorem DM_RC_G6_equiv : 
     forall (c : A -> Comp B),
       evalDist (DM_RC_G5 c) (Some true) ==
     evalDist (DM_RC_G6 c) true.

     unfold DM_RC_G5, DM_RC_G6.
     intuition.
     comp_skip.
     comp_simp.
     inline_first.
     comp_skip.
     rewrite compMap_head.
     comp_simp.
     destruct (hd_error (filter P x)).
     symmetry.
     rewrite <- evalDist_right_ident.
     comp_skip.
     dist_compute.
     dist_compute.
     intuition.     

     Grab Existential Variables.
     intuition.

   Qed.

   Definition DM_RC_B2 s_A (b : list B) :=
    core_b <- filter P b;
    opt_b' <- head core_b;
    match opt_b' with
        | None => ret false
        | Some b' => A2 s_A b'
    end.

  Theorem DistMult_G_equiv : 
    forall c, 
      Pr[DM_RC_G6 c] == Pr[DistMult_G _ A1 DM_RC_B2 n c] .

    intuition.
    unfold DistMult_G, DM_RC_G6, DM_RC_B2.
    comp_skip.
    comp_simp.
    inline_first.
    comp_skip.
  Qed.

  Variable k1 : Rat.
   Hypothesis c1_fail_prob : 
     forall a s_A, In (a, s_A) (getSupport A1) -> Pr[b <-$ c1 a; ret (negb (P b))] <= k1.
   Variable k2 : Rat.
   Hypothesis c2_fail_prob : 
     forall a s_A, In (a, s_A) (getSupport A1) -> Pr[b <-$ c2 a; ret (negb (P b))] <= k2.

  Theorem DistMult_impl_RepeatCore :
    RepeatCore_Adv P c1 c2 A1 A2 <= 
    DistMult_Adv _ c1 c2 A1 DM_RC_B2 n + 
    expRat k1 n +
    expRat k2 n.

    unfold RepeatCore_Adv, DistMult_Adv.
    repeat rewrite DM_RC_G1_equiv.
    repeat rewrite DM_RC_G2_equiv.

    eapply leRat_trans.
    eapply ratDistance_le_trans.
    eapply DM_RC_G2_G3_close; intuition.
    eauto.
    rewrite ratDistance_comm.
    eapply ratDistance_le_trans.
    eapply DM_RC_G2_G3_close; intuition.
    eauto.
    repeat rewrite DM_RC_G4_equiv.
    repeat rewrite DM_RC_G5_equiv.
    repeat rewrite DM_RC_G6_equiv.
    repeat rewrite DistMult_G_equiv.
    eapply leRat_refl.

    rewrite <- ratAdd_assoc.
    rewrite ratAdd_comm.
    rewrite <- ratAdd_assoc.
    rewrite ratDistance_comm.
    intuition.

    intuition.
    intuition.
    intuition.
    intuition.

  Qed.


End DistMult_impl_RepeatCore.

Section TrueSingle_impl_Mult.

  Variable A B : Set.
  Hypothesis B_EqDec : EqDec B.
  Variable c : A -> Comp B.
  Variable A1 : Comp A.
  Variable Q : B -> bool.

  Definition TrueSingle_G := 
    a <-$ A1;
    b <-$ c a;
    ret (Q b).

  Variable n : nat.

  Definition TrueMult_G :=
    a <-$ A1;
    bs <-$ compMap _ (fun _ => (c a)) (forNats n);
    ret (fold_left (fun b x => b || (Q x)) bs false).

  Theorem TrueSingle_impl_Mult :
    Pr[TrueMult_G] <= (n / 1) * Pr[TrueSingle_G].

    unfold TrueMult_G, TrueSingle_G.

    simpl in *.
    
    eapply leRat_trans.
    2:{
      eapply eqRat_impl_leRat.
      eapply sumList_factor_constant_l.
    }
    eapply sumList_le.
    intuition.

    eapply leRat_trans.
    2:{
      eapply eqRat_impl_leRat.
      symmetry.
      rewrite ratMult_comm.
      eapply ratMult_assoc.
    }
    eapply ratMult_leRat_compat.
    intuition.

    specialize (@compMap_Q_eq_compFold _ _ Q n (c a) false); intuition.
    rewrite H0.
    rewrite prob_sum_le_mult.
    rewrite ratMult_comm.
    eapply ratMult_leRat_compat; intuition.

    Local Transparent evalDist.
    simpl.
    reflexivity.

  Qed.

End TrueSingle_impl_Mult.

Section TrueMult_impl_Repeat.

  Variable A B : Set.
  Hypothesis eqdb : EqDec B.
  Variable A1 : Comp A.
  Hypothesis A1_wf : 
    well_formed_comp A1.
  Variable c : A -> Comp B.
  Variable f P : B -> bool.

  Hypothesis c_wf :
    forall x, In x (getSupport A1) -> well_formed_comp (c x).       

  Hypothesis Repeat_c_terminating : 
    forall x, In x (getSupport A1) -> 
              exists x1 : B, In x1 (filter P (getSupport (c x))).

  Definition TrueRepeat_G :=
    a <-$ A1;
    b <-$ Repeat (c a) P;
    ret (f b).

  Variable n : nat.
  Variable failProb : Rat.
  Hypothesis failProb_correct : 
    forall (a : A), 
      In a (getSupport A1) ->
      Pr[x <-$ c a; ret negb (P x)] <= failProb.

  Definition TrueRepeat_G1 :=
    a <-$ A1;
    bs <-$ compMap _ (fun _ => c a) (forNats n);
    b_opt <- hd_error (filter P bs);
    b' <-$ Repeat (c a) P;
    b <- match b_opt with
           | None => b'
           | Some x => x
         end;
    ret (f b).

   Theorem  TrueRepeat_G_G1_equiv :
     Pr[ TrueRepeat_G] == Pr[TrueRepeat_G1].

     unfold TrueRepeat_G, TrueRepeat_G1.
     inline_first.
     comp_skip.
     
     assert (Pr  [b <-$ Repeat (c x) P; ret f b ] ==
             Pr  [b <-$ (y <-$ compMap _ (fun _ => (c x)) (forNats n);
                   match (hd_error (filter P y)) with
                     | None => Repeat (c x) P
                     | Some z => ret z
                   end); ret f b ]).

     comp_skip.
     eapply Repeat_unroll_n.
     eauto.
     eauto.

     rewrite H0.
     clear H0.
     inline_first.
     comp_skip.
     case_eq (hd_error (filter P x0)); intuition.
     comp_irr_r.
     edestruct Repeat_c_terminating; eauto.
     eapply well_formed_Repeat.
     unfold eq_dec.
     intuition.
     eapply (EqDec_dec _).
     eauto.
     eauto.

     reflexivity.

   Qed.

   Definition TrueRepeat_G2 :=
     a <-$ A1;
     bs <-$ compMap _ (fun _ => c a) (forNats n);
     b_opt <- hd_error (filter P bs);
     b' <-$ Repeat (c a) P;
     b <- match b_opt with
           | None => b'
           | Some x => x
          end;
     ret (f b, if b_opt then false else true).

   Theorem TrueRepeat_G1_G2_equiv : 
     Pr [TrueRepeat_G1] <= Pr[x <-$ TrueRepeat_G2; ret (fst x || snd x)].

     unfold TrueRepeat_G1, TrueRepeat_G2.
     repeat (inline_first; comp_skip).
     destruct (hd_error (filter P x0)).
     comp_simp.
     dist_compute.
     rewrite e in n0.
     simpl in *.
     intuition.
     eapply rat0_le_all.

     comp_simp.
     dist_compute.
     rewrite e in n0.
     simpl in *.
     intuition.
     eapply rat0_le_all.
    
   Qed.

   Definition TrueRepeat_G3 :=
     a <-$ A1;
     bs <-$ compMap _ (fun _ => c a) (forNats n);
     b_opt <- hd_error (filter P bs);
     b' <-$ Repeat (c a) P;
     b <- match b_opt with
           | None => b'
           | Some x => x
          end;
     ret (fold_left (fun b x => b || (f x)) bs false, if b_opt then false else true).

   Theorem TrueRepeat_G2_G3_equiv : 
     Pr[x <-$ TrueRepeat_G2; ret (fst x || snd x)] <= 
     Pr[x <-$ TrueRepeat_G3; ret (fst x || snd x)].

     unfold TrueRepeat_G2, TrueRepeat_G3.
     repeat (inline_first; comp_skip).
     comp_simp.
     eapply comp_spec_impl_le.
     eapply 
       comp_spec_ret.
     simpl.
     
     case_eq ( hd_error (filter P x0)); intuition.
     rewrite orb_false_r in *.

     eapply fold_left_orb_true_in.
     eapply filter_In.

     eapply hd_error_Some_In.
     eauto.
     trivial.
     
   Qed.

   Definition TrueRepeat_G3_bad :=
      a <-$ A1;
     compFold _ (fun b _ => x <-$ c a; ret b && negb (P x)) true (forNats n).

   Theorem G3_TrueMult_equiv : 
     Pr[x <-$ TrueRepeat_G3; ret (fst x)] ==
     Pr[TrueMult_G _ c A1 f n].

     unfold TrueRepeat_G3, TrueMult_G.
     inline_first.
     comp_skip.
     inline_first.
     comp_skip.
     inline_first.
     comp_irr_l.
     edestruct Repeat_c_terminating; eauto.
     eapply well_formed_Repeat.
     unfold eq_dec; intuition.
     eapply (EqDec_dec _).
     eauto.
     eauto.

     simpl.
     intuition.
   Qed.

   Theorem TrueRepeat_G1_bad_equiv :
      Pr  [x <-$ TrueRepeat_G3; ret snd x ] == 
      Pr[TrueRepeat_G3_bad].

     unfold TrueRepeat_G3, TrueRepeat_G3_bad.

     inline_first.
     comp_skip.
     
     assert(
         Pr 
   [x0 <-$
    (bs <-$ compMap eqdb (fun _ : nat => c x) (forNats n);
     _ <-$ Repeat (c x) P;
     ret (fold_left (fun (b : bool) (x0 : B) => b || f x0) bs false,
         if hd_error (filter P bs) then false else true)); 
    ret snd x0 ]
   ==
   Pr 
   [x0 <-$
    (_ <-$ Repeat (c x) P;
      bs <-$ compMap eqdb (fun _ : nat => c x) (forNats n);
     
     ret (fold_left (fun (b : bool) (x0 : B) => b || f x0) bs false,
         if hd_error (filter P bs) then false else true)); 
    ret snd x0 ]
   ).
     
     comp_skip.
     comp_swap_r.
     comp_skip.
     rewrite H0.
     clear H0.

     inline_first.
     comp_irr_l.
     edestruct Repeat_c_terminating.
     eauto.
     eapply well_formed_Repeat.
     unfold eq_dec; intuition.
     eapply (EqDec_dec _).
     eauto.
     eauto.

     assert (
         Pr 
   [x1 <-$
    (bs <-$ compMap eqdb (fun _ : nat => c x) (forNats n);
     ret (fold_left (fun (b : bool) (x1 : B) => b || f x1) bs false,
         if hd_error (filter P bs) then false else true)); 
    ret snd x1 ]
   ==
   Pr 
   [bs <-$ compMap eqdb (fun _ : nat => c x) (forNats n);
     ret (fold_left (fun b z => b && negb (P z)) bs true)]
   ).

     inline_first.
     comp_skip.
     eapply comp_spec_eq_impl_eq.
     simpl.
     eapply comp_spec_ret.

     eapply hd_filter_false_eq_and_false.
 
     rewrite H1.
     clear H1.

     symmetry.
     eapply comp_spec_eq_impl_eq.
     eapply comp_spec_eq_trans.
     eapply fold_map_fission_spec_eq.
     intros.
     eapply comp_spec_eq_refl.
     comp_skip.

     eapply compFold_ret_eq.

   Qed.

   Theorem TrueRepeat_G2_bad_small :
      Pr[TrueRepeat_G3_bad] <= expRat failProb n.

      unfold TrueRepeat_G3_bad.
      comp_irr_l.

      rewrite prob_fold_and_eq_exp.
      eapply expRat_leRat_compat.
      intuition.
    Qed.

   Theorem TrueRepeat_G3_eq_sum : 
     Pr[x <-$ TrueRepeat_G3; ret (fst x || snd x)] <=
     Pr[TrueMult_G _ c A1 f n] + expRat failProb n.

     rewrite  evalDist_orb_le.
     rewrite G3_TrueMult_equiv.
     rewrite TrueRepeat_G1_bad_equiv .
     rewrite TrueRepeat_G2_bad_small.
     intuition.
   Qed.

      
    Theorem TrueMult_impl_Repeat :
      Pr[TrueRepeat_G] <= 
      Pr[TrueMult_G _ c A1 f n] + (expRat failProb n). 

      rewrite TrueRepeat_G_G1_equiv.
      rewrite TrueRepeat_G1_G2_equiv.
      rewrite TrueRepeat_G2_G3_equiv.
      eapply TrueRepeat_G3_eq_sum.

    Qed.

End TrueMult_impl_Repeat.

