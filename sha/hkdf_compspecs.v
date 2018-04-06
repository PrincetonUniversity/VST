Require Import VST.floyd.proofauto.
Require Import sha.hkdf.

Instance CompSpecs : compspecs. 
Proof. make_compspecs prog. Defined. 
