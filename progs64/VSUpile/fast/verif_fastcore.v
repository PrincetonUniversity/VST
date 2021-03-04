Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Require Import spec_stdlib.

Require Import verif_stdlib.
Require Import verif_fastpile.
Require Import verif_fastonepile.
Require Import verif_fastapile.
Require Import verif_fasttriang.

Definition PrivPILE: spec_fastpile_private.FastpilePrivateAPD := PILEPRIV M.
Definition PILE: spec_fastpile.PileAPD := spec_fastpile_private.pilepreds PrivPILE. 

Definition ONEPILE : spec_onepile.OnePileAPD := ONEPILE PILE.

Definition Onepile_Pile_VSU :=
  ltac:(linkVSUs (PilePrivateVSU M) (OnepileVSU M PILE) ). 

Definition Apile_Onepile_Pile_VSU :=
  ltac:(linkVSUs (Onepile_Pile_VSU) (ApileVSU M PrivPILE)). 

Definition Triang_Apile_Onepile_Pile_VSU :=
  ltac:(linkVSUs Apile_Onepile_Pile_VSU (TriangVSU M PILE)). 

Definition Core_VSU :=
  ltac:(linkVSUs MallocFreeVSU Triang_Apile_Onepile_Pile_VSU).
