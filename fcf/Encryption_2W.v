
(* A "two worlds" style of definition for encryption and a proof that it is equivalent to the standard definition. *)

Set Implicit Arguments.

Require Import Crypto.
Require Import Encryption.
Require Import EfficientProcedure.
Require Import TwoWorldsEquiv.
Require Import Asymptotic.

Section Encryption_SecretKey_2W.

  Context `{EncryptionScheme_SecretKey}.
  
  Section IND_CPA_SecretKey_2W.
    
    Context`{A : IND_CPA_Adversary Efficient Plaintext Ciphertext}.
    
    Section IND_CPA_SecretKey_2W_eta.
      
      Variable eta : nat.

      Definition IND_CPA_SecretKey_G_A :=
        key <-$ {KeyGen} eta;
        [p0, p1] <-$2{A} A eta;
        c <-$ {Encrypt} eta key p0;
        A c.
      
      Definition IND_CPA_SecretKey_G_B :=
        key <-$ {KeyGen} eta;
        [p0, p1] <-$2{A} A eta;
        c <-$ {Encrypt} eta key p1;
        A c.
    
      Definition IND_CPA_SecretKey_Advantage_2W := 
      | Pr[IND_CPA_SecretKey_G_A] - Pr[IND_CPA_SecretKey_G_B] |.

    End IND_CPA_SecretKey_2W_eta.

    Local Open Scope rat_scope.

    Definition IND_CPA_SecretKey_W eta (b : bool) :=
      key <-$ {KeyGen} eta;
      [p0, p1] <-$2{A} A eta;
      pb <- if b then p1 else p0;
      c <-$ {Encrypt} eta key pb;
      A c.

    Definition IND_CPA_SecretKey_G0 :=
      StandardDef_G IND_CPA_SecretKey_W.

    Theorem IND_CPA_SecretKey_G0_equiv : forall eta, 
      Pr[IND_CPA_SecretKey_G eta] == Pr[IND_CPA_SecretKey_G0 eta].

      unfold IND_CPA_SecretKey_G, IND_CPA_SecretKey_G0, IND_CPA_SecretKey_W, StandardDef_G.
      intuition.

      do 2
      (comp_at comp_inline rightc 1%nat;
      comp_swap_r;
      comp_skip).
      comp_skip.
      inline_first.
      intuition.
      
    Qed.

    End IND_CPA_SecretKey_2W.

    Definition IND_CPA_SecretKey_2W :=
      forall `(A : IND_CPA_Adversary Efficient Plaintext Ciphertext),
        negligible IND_CPA_SecretKey_Advantage_2W.
    
    Theorem IND_CPA_SecretKey_equiv : 
      forall `(A : IND_CPA_Adversary Efficient Plaintext Ciphertext),
        negligible IND_CPA_SecretKey_Advantage_2W <->
        negligible IND_CPA_SecretKey_Advantage.
      
      intuition.
      
    (* The forward proof *)
      
      eapply negligible_eq.
      eapply TwoWorlds_equiv_f.
      Focus 3.
      intuition.
      unfold IND_CPA_SecretKey_Advantage.
      rewrite IND_CPA_SecretKey_G0_equiv.
      eapply eqRat_refl.
      
      intuition.
      unfold IND_CPA_SecretKey_W.
      wftac.
      destruct KeyGen; simpl in *; intuition.
      
      simpl.
      destruct A1; simpl in *; intuition.
      
      destruct Encrypt; simpl in *; intuition.
      
      intuition.
      simpl.
      destruct A2; simpl in *; intuition.
      
      eapply negligible_eq.
      eapply H0.
      intuition.
      unfold IND_CPA_SecretKey_Advantage_2W, IND_CPA_SecretKey_G_A, IND_CPA_SecretKey_G_B, IND_CPA_SecretKey_W.
      eapply ratDistance_eqRat_compat;
        comp_skip;
        comp_skip.

    (* The backward proof *)
      
      eapply negligible_eq.
      eapply TwoWorlds_equiv_b.
      Focus 2.
      eapply negligible_eq.
      eapply H0.
      intuition.
      unfold IND_CPA_SecretKey_Advantage.
      rewrite IND_CPA_SecretKey_G0_equiv.
      eapply eqRat_refl.
      
      intuition.
      unfold IND_CPA_SecretKey_W.
      wftac.
      destruct KeyGen; simpl in *; intuition.
      
      simpl.
      destruct A1; simpl in *; intuition.
      
      destruct Encrypt; simpl in *; intuition.
      
      intuition.
      simpl.
      destruct A2; simpl in *; intuition.
      
      intuition.
      unfold IND_CPA_SecretKey_Advantage_2W, IND_CPA_SecretKey_G_A, IND_CPA_SecretKey_G_B, IND_CPA_SecretKey_W.
      eapply ratDistance_eqRat_compat;
        comp_skip;
        comp_skip.
      
    Qed.

End Encryption_SecretKey_2W.