
Set Implicit Arguments.

Require Import Crypto.
Require Import Encryption.
Require Import CompFold.

Section EncryptClassify.

  Variable Plaintext Ciphertext Key : Set.
  Variable KeyGen : Comp Key.
  Variable Encrypt : Key -> Plaintext -> Comp Ciphertext.
  Variable Decrypt : Key -> Ciphertext -> Plaintext.

  Hypothesis Ciphertext_EqDec : EqDec Ciphertext.

  Variable A_State : Set.
  Variable A1 : (Plaintext -> Comp Ciphertext) -> Comp (list (Plaintext * Plaintext) * (Plaintext * Plaintext) * A_State).
  Variable A2 : A_State -> (Plaintext -> Comp Ciphertext) -> list (Ciphertext * bool) -> Ciphertext -> Comp bool.

  Definition IND_CPA_SecretKey_Class_G :=
    key <-$ KeyGen ;
    [lsP, p, s_A] <-$3 A1 (Encrypt key);
    [p0, p1] <-2 p;
    lsC <-$ compMap _ (fun p => b <-$ {0, 1}; p_b <- if b then (snd p) else (fst p); c_b <-$ Encrypt key p_b; ret (c_b, b)) lsP;
    b <-$ {0, 1};
    pb <- if b then p1 else p0;
    c <-$ Encrypt key pb;
    b' <-$ A2 s_A (Encrypt key) lsC c;
    ret (eqb b b').
    

End EncryptClassify.