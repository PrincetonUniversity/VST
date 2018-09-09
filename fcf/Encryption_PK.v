(* Copyright 2012-2017 by Adam Petcher.                *
 * Use of this source code is governed by the license described    *
 * in the LICENSE file at the root of the source tree.        *)
(* Definitions for public key encryption. *)

Set Implicit Arguments.
Require Import fcf.FCF.

Local Open Scope rat_scope.
Local Open Scope list_scope.

Section Encryption.

  Variable Plaintext : Set.
  Variable Ciphertext : Set.
  Variable PrivateKey : Set.
  Variable PublicKey : Set.

  Hypothesis Plaintext_EqDec : EqDec Plaintext.
  Hypothesis Ciphertext_EqDec : EqDec Ciphertext.
    
  Variable KeyGen : Comp (PrivateKey * PublicKey).
  Variable Encrypt : Plaintext -> PublicKey -> Comp Ciphertext.
  Variable Decrypt : Ciphertext -> PrivateKey -> Plaintext.
    
Section IND_CPA.

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

Section IND_CCA1.

  Variable A_state : Set.
  Variable A1 : PublicKey -> OracleComp Ciphertext Plaintext (Plaintext * Plaintext * A_state).
  Variable A2 : (Ciphertext * A_state) -> Comp bool.

  Definition DecryptOracle k (s : unit) c :=
    ret (Decrypt c k, tt).
  
  Definition IND_CCA1_G :=
    [prikey, pubkey] <-$2 KeyGen;
    [r, _] <-$2 (A1 pubkey) _ _ (DecryptOracle prikey) tt;
    [p0, p1, a_state] <-3 r;
    b <-$ {0, 1};
    pb <- if b then p0 else p1;
    c <-$ (Encrypt pb pubkey);
    b' <-$ (A2 (c, a_state));
    ret (eqb b b').
  
  Definition IND_CCA1_Advantage := | Pr[IND_CCA1_G] - 1 / 2 |.      

End IND_CCA1.

Section IND_CCA2.

  Variable A_state : Set.
  Variable A1 : PublicKey -> OracleComp Ciphertext Plaintext (Plaintext * Plaintext * A_state).
  Variable A2 : (Ciphertext * A_state) -> OracleComp Ciphertext (option Plaintext) bool.

  Definition RestrictedDecryptOracle k c' (s : unit) c := 
    if (eqb c c') then ret (None, tt) else
    ret (Some (Decrypt c k), tt).

  Definition IND_CCA2_G :=
    [prikey, pubkey] <-$2 KeyGen;
    [r, _] <-$2 (A1 pubkey) _ _ (DecryptOracle prikey) tt;
    [p0, p1, a_state] <-3 r;
    b <-$ {0, 1};
    pb <- if b then p0 else p1;
    c <-$ (Encrypt pb pubkey);
    [b', _] <-$2 A2 (c, a_state) _ _ (RestrictedDecryptOracle prikey c) tt;
    ret (eqb b b').
  
  Definition IND_CCA2_Advantage := | Pr[IND_CCA2_G] - 1 / 2 |.      

End IND_CCA2.

Section IND_CCA2_O.

  Variable ptDefault : Plaintext.

  Inductive A_cmd : Set :=
    | Enc (p : Plaintext) : A_cmd
    | Dec (c : Ciphertext) : A_cmd.

  Variable A : PublicKey -> OracleComp A_cmd (sum Ciphertext Plaintext) bool.

  Definition EncryptOracle (pub : PublicKey)(s : list Ciphertext)(p : Plaintext) :=
    c <-$ Encrypt p pub;
    ret (c, c :: s).

  Definition EncryptNothingOracle (pub : PublicKey)(s : list Ciphertext)(p : Plaintext) :=
    c <-$ Encrypt ptDefault pub;
    ret (c, c :: s).

  Definition O encryptO (pri : PrivateKey) (s : list Ciphertext)(c : A_cmd) :=
    match c with
      | Enc p => [c, s] <-$2 encryptO s p; ret (inl c, c :: s)
      | Dec c => if (in_dec (EqDec_dec _) c s) then ret (inl c, s) else
          ret (inr (Decrypt c pri), s)
    end.

  Definition G encryptO :=
    [prikey, pubkey] <-$2 KeyGen;
    [b , _] <-$2 (A pubkey) _ _ (O (encryptO pubkey) prikey) nil;
    ret b.

  Definition G_A := G EncryptOracle.
  Definition G_B := G EncryptNothingOracle.

  Definition IND_CCA2_O_Advantage :=
    | Pr[G_A] - Pr[G_B] |.

End IND_CCA2_O.


                                                                                      
End Encryption.