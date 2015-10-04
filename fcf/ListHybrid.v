
Require Import FCF.
Require Import CompFold.

Local Open Scope list_scope.

Theorem skipn_S : 
  forall (A: Type)(defA : A)(ls : list A)(n : nat),
    n < length ls ->
    skipn n ls = 
    nth n ls defA :: skipn (S n) ls.
  
  induction ls; intuition; simpl in *.
  destruct n; try omega.

  destruct n.
  simpl.
  trivial.

  simpl.
  eapply IHls.
  omega.
Qed.

Theorem firstn_S : 
  forall (A: Type)(defA : A)(n : nat)(ls : list A),
    n < length ls ->
    firstn (S n) ls = 
    (firstn n ls) ++ ((nth n ls defA) :: nil).
  
  induction n; intuition; simpl in *.
  destruct ls; simpl in *.
  omega.
  trivial.

  destruct ls; simpl in *.
  omega.
  f_equal.
  eapply IHn.
  omega.
Qed.

  
Section ListHybrid.
  
  Variable A B C S_A : Set.
  Hypothesis eqdb : EqDec B.
  Variable defA : A.

  Variable A1 : Comp (list A * S_A).
  Variable A2 : S_A -> A -> Comp B.
  Variable A2' :  S_A -> A -> Comp B.
  Variable A3 : S_A -> list B -> Comp C.

  Hypothesis A1_wf : well_formed_comp A1.
  Hypothesis A2_wf :  forall x y, well_formed_comp (A2 x y).
  Hypothesis A2'_wf : forall x y, well_formed_comp (A2' x y).

  Variable numA : nat.
  Hypothesis numA_correct : 
    forall lsa s,
      In (lsa, s) (getSupport A1) ->
      length lsa = numA.

  Definition LH_G0  :=
    [lsa, s_A] <-$2 A1;
    lsb <-$ compMap _ (A2 s_A) lsa;
    A3 s_A lsb.

  Definition LH_G1 :=
    [lsa, s_A] <-$2 A1;
    lsb <-$ compMap _ (A2' s_A) lsa;
    A3 s_A lsb.

  Definition LH_Gn n :=
    [lsa, s_A] <-$2 A1;
    lsa1 <- firstn n lsa;
    lsa2 <- skipn n lsa;
    lsb1 <-$ compMap _ (A2' s_A) lsa1;
    lsb2 <-$ compMap _ (A2 s_A) lsa2;
    A3 s_A (lsb1 ++ lsb2).

  Definition LH_G_0  n :=
    [lsa, s_A] <-$2 A1;
    lsa1 <- firstn n lsa;
    a <- nth n lsa defA;
    lsa2 <- skipn (S n) lsa;
    lsb1 <-$ compMap _ (A2' s_A) lsa1;
    b <-$ A2 s_A a;
    lsb2 <-$ compMap _ (A2 s_A) lsa2;
    A3 s_A (lsb1 ++ (b :: lsb2)).

  Definition LH_G_1  n :=
    [lsa, s_A] <-$2 A1;
    lsa1 <- firstn n lsa;
    a <- nth n lsa defA;
    lsa2 <- skipn (S n) lsa;
    lsb1 <-$ compMap _ (A2' s_A) lsa1;
    b <-$ A2' s_A a;
    lsb2 <-$ compMap _ (A2 s_A) lsa2;
    A3 s_A (lsb1 ++ (b :: lsb2)).

  Variable F : nat -> Rat.
  
  Theorem list_hybrid_close_h : 
    (forall n c, | (evalDist (LH_Gn n) c) - (evalDist (LH_Gn (S n)) c) | <= F n) ->
  forall x n c,
  | (evalDist (LH_Gn n) c) - (evalDist (LH_Gn (n + x)) c) | <= sumList (map (plus n) (allNatsLt x)) F.

    
    Local Opaque evalDist.

    induction x; intuition; simpl in *.
    rewrite plus_0_r.
    eapply leRat_trans.
    eapply eqRat_impl_leRat.
    rewrite <- ratIdentityIndiscernables.
    intuition.
    eapply rat0_le_all.

    eapply leRat_trans.
    eapply ratDistance_le_trans.
    eapply H.
    assert (n + S x = S n + x)%nat.
    omega.
    rewrite H0.
    clear H0.
    eapply IHx.

    rewrite map_app.
    simpl.
    


    eapply eqRat_impl_leRat.
    rewrite ratS_num.
    rewrite ratMult_distrib_r.
    eapply ratAdd_eqRat_compat; intuition.
    symmetry.
    eapply ratMult_1_l.
    
  Qed.

  Theorem list_hybrid_close : 
    forall k c,
      (forall n c, n < numA -> | (evalDist (LH_G_0 n) c) - (evalDist (LH_G_1 n) c) | <= k) ->
  | (evalDist (LH_G0) c) - (evalDist (LH_G1) c) | <= (numA)/1 * k.
    
    intuition.

    assert (evalDist (LH_G0) c == evalDist (LH_Gn 0) c).
    unfold LH_G0, LH_Gn.
    comp_skip.
    comp_simp.
    simpl.
    comp_simp.
    simpl.
    comp_skip.

    rewrite H0.
    clear H0.

    assert (evalDist (LH_G1) c == evalDist (LH_Gn numA) c).
    unfold LH_G1, LH_Gn.
    comp_skip.
    comp_simp.

    specialize (firstn_skipn (length l) l); intuition.
    rewrite <- H1 at 1.
    eapply eqRat_trans.
    eapply evalDist_seq_eq.
    intros.
    eapply compMap_app.
    intuition.
    reflexivity.
    inline_first.
    clear H1.
    comp_skip.
    erewrite numA_correct; eauto.
    intuition.
    inline_first.

    Theorem skipn_length_nil : 
      forall (A : Type)(ls : list A)(n : nat),
        n >= length ls ->
        skipn n ls = nil.

      induction ls; intuition; simpl in *.
      destruct n; simpl in *; trivial.

      destruct n; simpl in *.
      omega.
      eapply IHls.
      omega.
    Qed.
             
    repeat rewrite skipn_length_nil.
    simpl.
    comp_simp.
    intuition.
    erewrite numA_correct; intuition; eauto.
    intuition.
    
    rewrite H0.
    clear H0.

    assert (numA = (0 + numA))%nat.
    omega.
    rewrite H0 at 1.
    clear H0.
    rewrite list_hybrid_close_h.
    eapply leRat_refl.
    intuition.

    Theorem LH_Gn_0_equiv : 
      forall (n : nat) c,
        n < numA ->
        evalDist (LH_Gn n) c == evalDist (LH_G_0 n) c.

      intuition.
      unfold LH_Gn, LH_G_0.
      comp_skip; comp_simp.
      comp_skip.

      erewrite skipn_S.
      simpl.
      inline_first.
      comp_skip.
      reflexivity.
      inline_first.
      comp_skip.
      erewrite numA_correct; intuition; eauto.
   
    Qed.

    Theorem LH_Gn_1_equiv : 
      forall (n : nat) c,
        n < numA ->
        evalDist (LH_Gn (S n)) c == evalDist (LH_G_1 n) c.

      intuition.
      unfold LH_Gn, LH_G_1.
      comp_skip.
      comp_simp.

      rewrite (firstn_S _ defA).

      assert (evalDist (lsb1 <-$ (foreach  (x in firstn n l ++ nth n l defA :: nil) A2' s x);
    lsb2 <-$ (foreach  (x in skipn (S n) l)A2 s x); A3 s (lsb1 ++ lsb2) ) c ==
              evalDist (lsb1 <-$ (r1 <-$ compMap _ (A2' s) (firstn n l);
                           r2 <-$ compMap _ (A2' s) (nth n l defA :: nil);
                           ret (r1 ++ r2));
    lsb2 <-$ (foreach  (x in skipn (S n) l)A2 s x); A3 s (lsb1 ++ lsb2) ) c
                ).

      comp_skip.
      eapply compMap_app.
      rewrite H1.
      clear H1.
      inline_first.
      comp_skip.
      inline_first.
      comp_skip.
      inline_first.

      comp_skip.
      reflexivity.
      
      rewrite <- app_assoc.
      rewrite <- app_comm_cons.
      simpl.
      intuition.
      erewrite numA_correct; intuition; eauto.

    Qed.

    destruct (ge_dec n numA).
    unfold LH_Gn.
    eapply evalDist_bind_distance; intuition.
    
    comp_simp.
    repeat rewrite firstn_ge_all; try omega.
    eapply evalDist_bind_distance; intuition.
    eapply compMap_wf;
    intuition.

    repeat rewrite skipn_length_nil; try omega.
    eapply leRat_trans.
    eapply eqRat_impl_leRat.
    rewrite <- ratIdentityIndiscernables.
    intuition.
    eapply rat0_le_all.

    erewrite numA_correct; eauto.
    erewrite numA_correct; eauto.
    erewrite numA_correct; eauto.
    erewrite numA_correct; eauto.

    rewrite LH_Gn_0_equiv.
    rewrite LH_Gn_1_equiv.
    eapply H.
    omega.
    omega.
    omega.
  Qed.


End ListHybrid.

Require Import Encryption.


Section ListEncrypt.

  Variable A C S_A : Set.
  Hypothesis EqDec_C : EqDec C.

  Variable Key Plaintext Ciphertext : Set.
  Hypothesis EqDec_Ciphertext :  EqDec Ciphertext.
  Variable KeyGen : Comp Key.
  Variable Enc : Key -> Plaintext -> Comp Ciphertext.

  Variable A1 : Comp (list A * S_A).
  Variable A2 : S_A -> A -> OracleComp Plaintext Ciphertext C.
  Variable A3 : S_A -> list C -> Comp bool.

  Definition LE_G0 :=
    [ls, s_A] <-$2 A1;
    lsc <-$ compMap _ (fun x => 
                         k <-$ KeyGen; 
                       [b, _] <-$2 (A2 s_A x) _ _ (EncryptOracle Enc _ k) tt;
                      ret b) ls;
    A3 s_A lsc.
  

End ListEncrypt.