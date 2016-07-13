Require Import floyd.proofauto.
Require Import hmacdrbg.hmac_drbg.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined. 
