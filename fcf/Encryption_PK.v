(* Definitions for public key encryption. *)

Set Implicit Arguments.
Require Import Crypto.

Local Open Scope rat_scope.

Section IND_CPA.

  Variable Plaintext : Set.
  Variable Ciphertext : Set.
  Variable PrivateKey : Set.
  Variable PublicKey : Set.
    
  Variable KeyGen : Comp (PrivateKey * PublicKey).
  Variable Encrypt : Plaintext -> PublicKey -> Comp Ciphertext.
    
  Variable A_state : Set.
  Variable A1 : PublicKey -> Comp (Plaintext * Plaintext * A_state).
  Variable A2 : (Ciphertext * A_state) -> Comp bool.
  
  Definition IND_CPA_G :=
    [prikey, pubkey] <-$2 KeyGen;
    [p0, p1, a_state] <-$3 (A1 pubkey);
    b <-$ {0, 1};
    pb <- if b then p0 else p1;
                         c <-$ (Encrypt pb pubkey);
                         b' <-$ (A2 (c, a_state));
                         ret (eqb b b').
  
  Definition IND_CPA_Advantage := | Pr[IND_CPA_G] - 1 / 2 |.      

  Definition IND_CPA (epsilon : Rat) :=
    | Pr[IND_CPA_G] - 1 / 2 | <= epsilon.
                                                                                                    
End IND_CPA.
