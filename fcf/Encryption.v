(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* indistinguishability-based security definitions for encryption schemes. *)

Set Implicit Arguments.
Unset Strict Implicit.
Require Import fcf.FCF.
Require Import fcf.CompFold.
Require Export fcf.Hybrid.

Local Open Scope type_scope.
Local Open Scope comp_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Fixpoint oc_compMap(A B C D : Set)(eqdb : EqDec B)(c : A -> OracleComp C D B)(ls : list A) : OracleComp C D (list B) :=
  match ls with
    | nil => $ (ret nil)
    | a :: ls' =>
      b <--$ c a;
      lsb' <--$ oc_compMap _ c ls';
      $ (ret (b :: lsb'))
  end. 

Section Encryption_SecretKey_concrete.

  Variable Plaintext Ciphertext Key : Set.
  Variable KeyGen : Comp Key.
  Variable Encrypt : Key -> Plaintext -> Comp Ciphertext.
  Variable Decrypt : Key -> Ciphertext -> Plaintext.

  Section IND_CPA_SecretKey_concrete.
    
    Variable State : Set.
    Variable A1 : OracleComp Plaintext Ciphertext (Plaintext * Plaintext * State).
    Variable A2 : State -> Ciphertext -> OracleComp Plaintext Ciphertext bool.

    Hypothesis Ciphertext_EqDec : EqDec Ciphertext.
    Hypothesis Plaintext_EqDec : EqDec Plaintext.

    Definition EncryptOracle(k : Key)(x : unit)(p : Plaintext) :=
      c <-$ Encrypt k p;
      ret (c, tt).

    Hypothesis Encrypt_wf : 
      forall k p,
        well_formed_comp (Encrypt k p).

    Theorem EncryptOracle_wf : 
      forall k x p,
        well_formed_comp (EncryptOracle k x p).

      intuition.
      unfold EncryptOracle.
      wftac.

    Qed.
 
    Definition IND_CPA_SecretKey_G :=
      key <-$ KeyGen ;
      [b, _] <-$2 
      (
        [p0, p1, s_A] <--$3 A1;
        b <--$$ {0, 1};
        pb <- if b then p1 else p0;
          c <--$$ Encrypt key pb;
          b' <--$ A2 s_A c;
          $ ret eqb b b'
      )
      _ _ (EncryptOracle key) tt;
      ret b.
    
    Definition IND_CPA_SecretKey_Advantage := | Pr[IND_CPA_SecretKey_G] - 1 / 2 |.
     
  End IND_CPA_SecretKey_concrete.

  Section IND_CPA_SecretKey_O_concrete.
    
    Variable A : OracleComp Plaintext Ciphertext bool.

    Hypothesis Ciphertext_EqDec : EqDec Ciphertext.
    Variable ptDefault : Plaintext.

    Definition EncryptNothingOracle (k : Key)(x : unit)(p : Plaintext)  := 
      c <-$ Encrypt k ptDefault;
      ret (c, tt).

    Definition IND_CPA_SecretKey_O_G0 :=
      key <-$ KeyGen ;
      [b, _] <-$2 A _ _ (EncryptOracle _ key) tt;
      ret b.

    Definition IND_CPA_SecretKey_O_G1 :=
      key <-$ KeyGen ;
      [b, _] <-$2 A _ _ (EncryptNothingOracle key) tt;
      ret b.

    Definition IND_CPA_SecretKey_O_Advantage := | Pr[IND_CPA_SecretKey_O_G0] - Pr[IND_CPA_SecretKey_O_G1]  |.
     
  End IND_CPA_SecretKey_O_concrete.

  (* The reduction from iterated IND-CPA goes through the following definition.  There is probably no reason to use this definition in a security proof.  *)
  Section IND_CPA_SecretKey_O_concrete_3Proc.
    
    Variable A B State : Set.
    Hypothesis B_EqDec : EqDec B.
    Variable A1 : Comp (A * State).
    Variable A2 : A -> OracleComp Plaintext Ciphertext B.
    Variable A3 : State -> B -> Comp bool.

    Hypothesis Ciphertext_EqDec : EqDec Ciphertext.
    Variable ptDefault : Plaintext.

    Definition IND_CPA_SecretKey_O_3Proc_G0 :=
      [a, s_A] <-$2 A1;
      key <-$ KeyGen ;
      [b, _] <-$2 (A2 a) _ _ (EncryptOracle _ key) tt;
      A3 s_A b.

    Definition IND_CPA_SecretKey_O_3Proc_G1 :=
      [a, s_A] <-$2 A1;
      key <-$ KeyGen ;
      [b, _] <-$2 (A2 a) _ _ (EncryptNothingOracle _ ptDefault key) tt;
      A3 s_A b.

    Definition IND_CPA_SecretKey_O_3Proc_Advantage := | Pr[IND_CPA_SecretKey_O_3Proc_G0] - Pr[IND_CPA_SecretKey_O_3Proc_G1]  |.

    Definition A_c :=
      [a, s_A] <--$2$ A1;
      x <--$ A2 a;
      $ A3 s_A x.

    Theorem IND_CPA_SecretKey_2Proc_impl_O : 
      IND_CPA_SecretKey_O_3Proc_Advantage == IND_CPA_SecretKey_O_Advantage A_c _ ptDefault.  

      unfold IND_CPA_SecretKey_O_3Proc_Advantage, IND_CPA_SecretKey_O_Advantage.
      unfold IND_CPA_SecretKey_O_3Proc_G0, IND_CPA_SecretKey_O_3Proc_G1.
      unfold IND_CPA_SecretKey_O_G0, IND_CPA_SecretKey_O_G1.
      unfold A_c.

      Local Opaque evalDist.
      simpl.
      eapply ratDistance_eqRat_compat.
      comp_at comp_inline rightc 1%nat.
      comp_swap_r.
      inline_first.
      comp_skip.
      comp_simp.
      comp_skip.
      simpl.
      inline_first.
      comp_skip.
      comp_simp.
      inline_first.
      rewrite <- evalDist_right_ident.
      comp_skip.
      comp_simp.
      reflexivity.

      comp_at comp_inline rightc 1%nat.
      comp_swap_r.
      inline_first.
      comp_skip.
      comp_simp.
      comp_skip.
      simpl.
      inline_first.
      comp_skip.
      comp_simp.
      inline_first.
      rewrite <- evalDist_right_ident.
      comp_skip.
      comp_simp.
      reflexivity.
    Qed.                                                     
     
  End IND_CPA_SecretKey_O_concrete_3Proc.

  Section IND_CPA_SecretKey_OI_concrete.
    
    Variable A B S_A: Set.
    Variable defA : A.
    Variable A1 : Comp (list A * S_A).
    Variable A2 : A -> OracleComp Plaintext Ciphertext B.
    Variable A3 : S_A -> list B -> Comp bool.

    Hypothesis Ciphertext_EqDec : EqDec Ciphertext.
    Hypothesis A_EqDec : EqDec A.
    Hypothesis B_EqDec : EqDec B.
    Hypothesis S_A_EqDec : EqDec S_A.
    Variable ptDefault : Plaintext.

    Definition IND_CPA_SecretKey_OI_G0 :=
      [lsa, s_A] <-$2 A1;
      lsb <-$ compMap _ 
               (fun x => 
                 key <-$ KeyGen; 
                 [b, _] <-$2 (A2 x) _ _ (EncryptOracle _ key) tt; 
                 ret b
               ) lsa;
      A3 s_A lsb.

     Definition IND_CPA_SecretKey_OI_G1 :=
      [lsa, s_A] <-$2 A1;
      lsb <-$ compMap _ 
               (fun x => 
                 key <-$ KeyGen; 
                 [b, _] <-$2 (A2 x) _ _ (EncryptNothingOracle _ ptDefault key) tt; 
                 ret b
               ) lsa;
      A3 s_A lsb.

    Definition IND_CPA_SecretKey_OI_Advantage := 
    | Pr[IND_CPA_SecretKey_OI_G0] - Pr[IND_CPA_SecretKey_OI_G1]  |.    

  Section IND_CPA_SecretKey_OI_impl_O.

    Hypothesis KeyGen_wf : 
      well_formed_comp KeyGen.
    Hypothesis A2_wf : 
      forall a,
        well_formed_oc (A2 a).

    Variable maxA : nat.
    Hypothesis maxA_correct : 
      forall ls s_A,
        In (ls, s_A) (getSupport A1) ->
        length ls <= maxA.

    Variable IND_CPA_Adv : Rat.
    
    Hypothesis IND_CPA_Adv_correct : 
      (forall i,
      IND_CPA_SecretKey_O_Advantage (A_c 
        (B1 defA _ _ A1 i) 
        A2
         (B2
          (fun x : A =>
           key <-$ KeyGen;
           z <-$
           (A2 x) unit unit_EqDec (EncryptOracle Ciphertext_EqDec key) tt;
           [b, _]<-2 z; ret b)
          (fun x : A =>
           key <-$ KeyGen;
           z <-$
           (A2 x) unit unit_EqDec
             (EncryptNothingOracle Ciphertext_EqDec ptDefault key) tt;
           [b, _]<-2 z; ret b) B_EqDec A3)
         )
         _ 
         ptDefault
      <= IND_CPA_Adv)%rat.
     

    Theorem IND_CPA_SecretKey_OI_G0_Hybrid : 
      Pr[IND_CPA_SecretKey_OI_G0] == Pr[ListHybrid_G _ A1 A3
                                       (fun x => 
                 key <-$ KeyGen; 
                 [b, _] <-$2 (A2 x) _ _ (EncryptOracle _ key) tt; 
                 ret b
               )].

      reflexivity.
    Qed.

    Theorem IND_CPA_SecretKey_OI_G1_Hybrid : 
      Pr[IND_CPA_SecretKey_OI_G1] == Pr[ListHybrid_G _ A1 A3
                                       (fun x => 
                 key <-$ KeyGen; 
                 [b, _] <-$2 (A2 x) _ _ (EncryptNothingOracle _ ptDefault key) tt; 
                 ret b
               )].

      reflexivity.
    Qed.

    Hypothesis Encrypt_wf : 
      forall k p,
        well_formed_comp (Encrypt k p).

    Theorem IND_CPA_OI_impl_O : 
      (IND_CPA_SecretKey_OI_Advantage <= maxA / 1 * IND_CPA_Adv)%rat.

      unfold IND_CPA_SecretKey_OI_Advantage.
      rewrite IND_CPA_SecretKey_OI_G0_Hybrid.
      rewrite IND_CPA_SecretKey_OI_G1_Hybrid.
      eapply leRat_trans.
      eapply Single_impl_ListHybrid.
      intuition.
      
      wftac.
      eapply oc_comp_wf_inv.
      eauto.
      intuition.
      unfold EncryptOracle; wftac.
      intuition.
      assert ((fun x => True) s').
      trivial.
      eapply H3.
      simpl.
      trivial.
      
      4:{
        reflexivity.
      }

      intuition.
      wftac.
      unfold EncryptNothingOracle.
      eapply oc_comp_wf_inv.
      trivial.
      intuition.
      wftac.
      intuition.
      assert ((fun x => True) s').
      trivial.
      eauto.
      simpl.
      trivial.
      intuition.
  
      intuition.
      eapply leRat_trans.
      2:{
        eapply IND_CPA_Adv_correct.
      }
      unfold DistSingle_Adv.
      eapply leRat_trans.
      2:{
        eapply eqRat_impl_leRat.
        apply IND_CPA_SecretKey_2Proc_impl_O.
      }
      unfold IND_CPA_SecretKey_O_3Proc_Advantage.
      eapply eqRat_impl_leRat.

      unfold DistSingle_G.
      unfold IND_CPA_SecretKey_O_3Proc_G0.
      eapply ratDistance_eqRat_compat;

      repeat (try comp_skip; try reflexivity; comp_simp; inline_first).

    Qed.

  End  IND_CPA_SecretKey_OI_impl_O.

  End IND_CPA_SecretKey_OI_concrete.

End Encryption_SecretKey_concrete.

Require Import fcf.Asymptotic.
Require Import fcf.Admissibility.

Section Encryption_SecretKey.

  Variable Plaintext Ciphertext Key : DataTypeFamily.

  Hypothesis Ciphertext_EqDec : forall n, EqDec (Ciphertext n).

  Variable KeyGen : forall n, Comp (Key n).
  Variable Encrypt : forall n, Key n -> Plaintext n -> Comp (Ciphertext n).
  Variable Decrypt : forall n, Key n -> Ciphertext n -> Plaintext n.

  Variable admissible_A1 : pred_oc_fam.
  Variable admissible_A2 : pred_oc_func_2_fam.

  Definition IND_CPA_SecretKey :=
    forall (State : nat -> Set)
      (A1 : forall n, OracleComp (Plaintext n) (Ciphertext n) (Plaintext n * Plaintext n * State n))
        (A2 : forall n, State n -> Ciphertext n -> OracleComp (Plaintext n) (Ciphertext n) bool),
        admissible_A1 A1 ->
        admissible_A2 A2 ->
        (forall n, EqDec (State n)) ->
      negligible 
      (fun n => IND_CPA_SecretKey_Advantage (KeyGen n) (@Encrypt n) (A1 n) (A2 n) _).

End Encryption_SecretKey.
