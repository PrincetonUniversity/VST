Set Implicit Arguments.
Require Import FCF.FCF.

Local Open Scope list_scope.

Section Signature.

  Variable Message : Set.
  Variable Signature : Set.
  Variable PrivateKey : Set.
  Variable PublicKey : Set.

  Hypothesis Message_EqDec : EqDec Message.
  Hypothesis Signature_EqDec : EqDec Signature.    

  Variable KeyGen : Comp (PrivateKey * PublicKey).
  Variable Sign : PrivateKey -> Message -> Comp Signature.
  Variable Verify : PublicKey -> Message -> Signature -> bool.

  Section UF_CMA.
    
    Definition SignOracle k state m :=
      sig <-$ Sign k m;
      ret (sig, m :: state).

    Variable A : PublicKey -> OracleComp Message Signature (Message * Signature).

    Definition UF_CMA_G :=
      [pri, pub] <-$2 KeyGen;
      [m, s, ls] <-$3 A pub _ _ (SignOracle pri) nil;
      ret (if (in_dec (EqDec_dec _) m ls) then false else
      (Verify pub m s)).
    
    Definition UF_CMA_Advantage :=
      Pr[UF_CMA_G].

  End UF_CMA.

End Signature.