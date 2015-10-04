
(* A proof that an encryption scheme based on a pseudorandom function is secure according to the "weak" form of IND-CPA.  This is a simple asymptotic proof that can be used for learning purposes. *)  

Set Implicit Arguments.

Require Import MCF.
Require Import PRF.
Require Import Encryption.
Require Import Procedure.

Local Open Scope type_scope.

Require Import WC_PolyTime.

Section PRF_Encryption_concrete.
  
  Variable eta : nat.
  
  Definition Key := Bvector eta.
  Definition Plaintext := Bvector eta.
  Definition Ciphertext := Bvector eta * Bvector eta.

  Variable f : Bvector eta -> Bvector eta -> Bvector eta.

  Definition PRFE_KeyGen := 
    {0, 1} ^ eta.
  
  Definition PRFE_Encrypt (k : Key )(p : Plaintext) :=
    r <-$ {0, 1} ^ eta;
    ret (r, p xor (f k r)).
  
  Definition PRFE_Decrypt (k : Key)(c : Ciphertext) :=
    (snd c) xor (f k (fst c)).
    
  Theorem PRF_Encrypt_correct : 
    forall k p c,
      In c (getSupport (PRFE_Encrypt k p)) ->
      PRFE_Decrypt k c = p.
    
    intuition.
    unfold PRFE_Encrypt, PRFE_Decrypt in *.
    repeat simp_in_support.
    simpl.
    rewrite BVxor_assoc.
    rewrite BVxor_same_id.
    rewrite BVxor_id_r.
    intuition.
  Qed.
  
  Section PRF_Encryption_IND_CPA_weak_concrete.
  
    Variable (A : IND_CPA_Adversary_weak_concrete Plaintext Ciphertext).

    Local Open Scope list_scope.
    
    (* The constructed adversary procedures against the PRF *)
    Definition PRF_A1 (x : unit) := (d <-$ {0, 1} ^ eta; ret (d :: nil, d)).
    
    Definition PRF_A2 p := 
      [p0, p1] <-$2{A} A tt;
      b <-$ {0, 1};
      pb <- if b then p1 else p0;
        c <- (fst p, pb xor (hd (oneVector eta) (snd p)));
        b' <-$ A c;
        ret (eqb b b').

    Hint Resolve A2_SA_EqDec : typeclass_instances.

    (* An equivalent second procedure that makes it a bit easier to reason about cost.  This is what we will actually use to construct the adversary. *)
    Definition PRF_A2' p := 
      b_pb_x <-$
      (x <-$ (fst A) tt;
        b <-$ {0, 1};
        pb <-$ ret (if b then (snd (fst x)) else (fst (fst x)));
        ret (b, pb, x));

      b' <-$ (snd A) (snd (snd b_pb_x)) (fst p, (snd (fst b_pb_x)) xor (hd (oneVector eta) (snd p)));
      ret (eqb (fst (fst b_pb_x)) b').

    Theorem PRF_A2'_equiv : 
      forall x y,
        evalDist (PRF_A2 x) y == evalDist (PRF_A2' x) y.

      unfold PRF_A2, PRF_A2'.
      intuition.
      do 2 (inline_first; comp_skip; comp_simp).
      inline_first.
      comp_simp.
      eapply eqRat_refl.
    Qed.

    Theorem PRF_A1_wf : 
      forall x, well_formed_comp (PRF_A1 x).

      intuition.
      unfold PRF_A1.
      wftac.
    Qed.
  
    Theorem PRF_A2'_wf : 
      forall x, well_formed_comp (PRF_A2' x).

      intuition.
      unfold PRF_A2'.
      wftac.

      destruct A. simpl. intuition.
      destruct A. simpl. intuition.
    Qed.

    Context `{constant_cost_relation}.

    Theorem PRF_A1_cost : cost PRF_A1 0%nat.
      
      unfold PRF_A1.
      eapply constant_cost_const.

    Qed.

    Variable A2_cost : nat.
    Hypothesis A2_cost_correct : 
      cost (@A2_A2 _ _ _ _ A) A2_cost.

    (* This proof got broken when we made some changes to the cost model.  Need to fix it. *)
    
    Theorem PRF_A2'_cost : cost PRF_A2' (A2_cost + 3)%nat.
      
    Admitted.

    Definition PRF_A : PRF_NA_Adversary_concrete (Bvector eta) (Bvector eta).

      econstructor.
      Focus 2.
      eapply PRF_A1_wf.
      intuition.
      eapply PRF_A2'_wf.
    Defined.
    
    Definition G1 :=
      key <-$ PRFE_KeyGen;
      [p0, p1] <-$2{A} A tt;
      b <-$ {0, 1};
      pb <- if b then p1 else p0;
        c <-$ PRFE_Encrypt key pb;
        b' <-$ A c;
        ret (eqb b b').
    
    Theorem G1_equiv : 
      Pr[IND_CPA_SecretKey_weak_G PRFE_KeyGen PRFE_Encrypt A] == Pr[G1].
      
      intuition.
      eapply eqRat_refl.
    Qed.
    
    Definition G2_0 :=
      lsD <-$ (d <-$ {0, 1} ^ eta; ret (d :: nil, d));
      lsR <-$ (k <-$ {0, 1} ^ eta; ret (map (f k) (fst lsD)));
      PRF_A2 (snd lsD, lsR).

    Definition G2_1 :=
      lsD <-$ (d <-$ {0, 1} ^ eta; ret (d :: nil, d));
      lsR <-$ (k <-$ {0, 1} ^ eta; ret (map (f k) (fst lsD)));
      PRF_A2' (snd lsD, lsR).
    
    Definition G2 :=
      lsD <-${PRF_A} PRF_A tt;
      lsR <-$ (k <-$ {0, 1} ^ eta; ret (map (f k) lsD));
      PRF_A lsR.
    
    Theorem G2_0_equiv : 
      Pr[G1] == Pr[G2_0].
      
      unfold G1, G2_0, PRF_A2.
      unfold PRFE_KeyGen, PRFE_Encrypt.
      
      intuition.
      comp_at comp_inline rightc 1%nat.
      dist_swap_r.
      comp_skip.
      comp_at comp_swap rightc 1%nat.
      dist_swap_r.
      comp_skip.
      
      destruct x0.
      destruct p.
      comp_at comp_swap rightc 1%nat.
      dist_swap_r.
      comp_skip.
      
      inline_first.
      comp_skip.
      
      comp_simp.
      comp_skip.
      simpl.
      eapply eqRat_refl.
      
    Qed.

    Theorem G2_1_equiv : 
      Pr[G2_0] == Pr[G2_1].

      unfold G2_0, G2_1.
      comp_skip.
      comp_skip.
      eapply PRF_A2'_equiv.

    Qed.
    
    Theorem G2_equiv : 
      Pr[G2_1] == Pr[G2].
      
      unfold G2_0, G2.

      comp_skip.
      simpl. intuition.

      destruct x.
      simpl. intuition.

    Qed.
    
    Definition randomFunc_Bvector := @randomFunc (Bvector eta) (Bvector eta) (Rnd eta) _.
    
    Definition G3 :=
      lsD <-${PRF_A} PRF_A tt;
      [lsR, _] <-$2 oracleMap _ _ (randomFunc_Bvector) nil lsD;
      PRF_A lsR.
    
    Theorem G3_equiv : 
      | Pr[G2] - Pr[G3] | == PRF_NA_Advantage (Rnd eta) (Rnd eta) f _ _ PRF_A.
      
      unfold PRF_NA_Advantage, G2, G3.
      unfold PRF_NA_G_A, PRF_NA_G_B.

      eapply eqRat_refl.
      
    Qed.

    Definition G4 :=
      d <-$ {0, 1} ^ eta;
      r <-$ {0, 1} ^ eta;
      [p0, p1] <-$2{A} A tt;
      b <-$ {0, 1};
      pb <- if b then p1 else p0;
        c <- (d, pb xor r);
        b' <-$ A c;
        ret (eqb b b').
  
    Theorem G4_equiv : 
      Pr[G3] == Pr[G4].
      
      unfold G3, G4.

      unfold Adversary_2_concrete_prod.
      unfold fst, snd.
      unfold PRF_A1, PRF_A2.
      inline_first.
      comp_skip.
      unfold oracleMap.
      unfold CompFold.compFold.
      unfold randomFunc_Bvector.
      unfold randomFunc.
      unfold arrayLookup.
      inline_first.

      comp_skip.
      inline_first.
      comp_skip.
      simpl.
      intuition.

      dist_simp.
      inline_first.
      comp_skip.

      dist_simp.
      inline_first.
      unfold fst, snd, Adversary_2_concrete_prod.

      comp_skip.
      simpl; intuition.

    Qed.
    
    Definition G5 :=
      d <-$ {0, 1} ^ eta;
      r <-$ {0, 1} ^ eta;
      [p0, p1] <-$2{A} A tt;
      c <- (d, r);
      b' <-$ A c;
      b <-$ {0, 1};
      ret (eqb b b').
    
    Definition G5_0 :=
      d <-$ {0, 1} ^ eta;
      [p0, p1] <-$2{A} A tt;
      b <-$ {0, 1};
      pb <- if b then p1 else p0;
        r <-$ (z <-$ {0, 1} ^ eta; ret (pb xor z));
        c <- (d, r);
        b' <-$ A c;
        ret (eqb b b').
    
    Definition G5_1 :=
      d <-$ {0, 1} ^ eta;
      [p0, p1] <-$2{A} A tt;
      b <-$ {0, 1};
      pb <- if b then p1 else p0;
        r <-$ {0, 1} ^ eta;
        c <- (d, r);
        b' <-$ A c;
        ret (eqb b b').
    
    Theorem G5_0_equiv : 
      Pr[G4] == Pr[G5_0].
      
      intuition.
      unfold G4, G5_0.
      
      comp_skip.
      dist_swap_l.
      comp_skip.
      comp_simp.
      dist_swap_l.
      comp_skip.
      
      inline_first.
      comp_skip.
      comp_simp.
      intuition.
    Qed.
    
    Require Import OTP.
    
    Theorem G5_1_equiv : 
      Pr[G5_0] == Pr[G5_1].
      
      intuition.
      unfold G5_0, G5_1.
      do 3 (comp_skip; dist_simp).

      eapply eqRat_symm.
      eapply comp_spec_eq_impl_eq.
      eapply comp_spec_seq; eauto with inhabited.
      eapply xor_OTP.

      intuition; subst.
      eapply comp_spec_eq_refl.
    Qed.
    
    Theorem G5_equiv : 
      Pr[G5_1] == Pr[G5].
      
      intuition.
      unfold G5_1, G5.
      comp_skip.
      dist_swap_r.
      comp_skip.
      comp_simp.
      dist_swap_l.
      comp_skip.
      dist_swap_l.
      comp_skip.
    Qed.
    
    Theorem one_half_equiv : 
      Pr[G5] == 1/2.
      
      intuition.
      unfold G5.
      
      do 3 (dist_irr_l; wftac; comp_simp).
      destruct A; intuition.
      
      (dist_irr_l; wftac; comp_simp).
      destruct A; intuition.

      dist_compute.
      
    Qed.    
  
    Theorem PRF_EncryptSecure_concrete : 
      IND_CPA_SecretKey_weak_Advantage PRFE_KeyGen PRFE_Encrypt A <= 
      PRF_NA_Advantage (Rnd eta) (Rnd eta) f _ _ PRF_A.
      
      unfold IND_CPA_SecretKey_weak_Advantage.
      rewrite G1_equiv.
      rewrite G2_0_equiv.
      rewrite G2_1_equiv.
      rewrite G2_equiv.
      
      eapply leRat_trans. 
      eapply ratDistance_le_trans.
      eapply eqRat_impl_leRat.
      eapply G3_equiv.
      rewrite G4_equiv.
      rewrite G5_0_equiv.
      rewrite G5_1_equiv.
      rewrite G5_equiv.
      rewrite one_half_equiv.
      eapply eqRat_impl_leRat.
      rewrite <- ratIdentityIndiscernables.
      intuition.
      rewrite <- ratAdd_0_r.
      intuition.
    Qed.

  End PRF_Encryption_IND_CPA_weak_concrete.
    
End PRF_Encryption_concrete.

Require Import Asymptotic.
Require Import ExpectedPolyTime.

Section PRF_Encryption.

  Context `{constant_cost_relation}.
  Definition efficient := poly_time_nonuniform cost.

  Hypothesis list_hd_cost : 
    forall (A : Type),
      cost (fun p => @hd A (fst p) (snd p)) 1%nat.
  
  Variable f : forall n, Bvector n -> Bvector n -> Bvector n.

  Section PRF_Encryption_IND_CPA_weak.

    Variable (A : IND_CPA_Adversary_weak efficient Plaintext Ciphertext).
    
    Theorem PRF_A1_efficient_h : 
      efficient _ _ PRF_A1.
      
      unfold efficient, poly_time_nonuniform.
 
      exists (fun n => 0)%nat.
      intuition.

      econstructor.
      econstructor.
      econstructor.
      intuition.
      
      exists 0%nat.

      split.
      eapply (PRF_A1_cost).
      eauto.
      omega.

      Grab Existential Variables.
      eapply O.
      eapply O.

    Qed.
   
    Theorem PRF_A2'_efficient_h : 
      efficient _ _ (fun n => PRF_A2' (A n)).
      
      unfold efficient, poly_time_nonuniform.
      
      destruct (A2_A2_efficient A).
      destruct H0.

      exists (fun n => x n + 3)%nat.
      split.

      clear H1.
      unfold polynomial.

      destruct H0.
      destruct H0.
      destruct H0.
      exists x0%nat.
      exists x1%nat.
      exists (x2 + 3)%nat.
      intuition.
      specialize (H0 n).
      omega.
 
      intuition.
      destruct (H1 n).
      destruct H2.
      exists (x0 + 3)%nat.
      split.
      eapply PRF_A2'_cost;
      eauto.
      omega.
    Qed.

    Theorem PRF_A1_efficient : 
      efficient _ _ (fun n => (PRF_A (@f n) (A n)).(A2_A1)).

      unfold A2_A1, PRF_A.
      eapply PRF_A1_efficient_h.

    Qed.

    Theorem PRF_A2_efficient : 
      efficient _ _ (fun n => (@A2_A2 _ _ _ _ (PRF_A (@f n) (A n)))).

      unfold A2_A2, PRF_A.
      eapply PRF_A2'_efficient_h.

    Qed.

    Definition PRF_A_Adversary : 
      PRF_NA_Adversary efficient Bvector Bvector.

      econstructor.

      eapply PRF_A1_efficient.
      eapply PRF_A2_efficient.
    
    Defined.

  End PRF_Encryption_IND_CPA_weak.  
      
  Theorem PRFE_IND_CPA_weak : 
    NA_PRF efficient _ _ _ Rnd Rnd f _ _ -> 
    IND_CPA_SecretKey_weak efficient PRFE_KeyGen (fun n => PRFE_Encrypt (@f n)).

    unfold IND_CPA_SecretKey_weak.
    unfold negligible.
    intuition.
    edestruct (H0 (@PRF_A_Adversary A)).

    edestruct (A2_A2_efficient A).
    intuition.
    
    econstructor.
    intuition.
    edestruct H4.
    eapply H1.
    eauto.
    rewrite H5.
    intuition.
    eapply PRF_EncryptSecure_concrete.
    eapply H7.
  Qed.

  (* Print Assumptions PRFE_IND_CPA_weak.*)

End PRF_Encryption.



