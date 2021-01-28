Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Require Import VST.floyd.linking.

Require Import spec_stdlib.

Require Import verif_stdlib.
Require Import verif_pile.
Require Import verif_onepile.
Require Import verif_apile.
Require Import verif_triang.

Definition PrivPILE: spec_pile_private.PilePrivateAPD M := PILEPRIV M.
Definition PILE: spec_pile.PileAPD := spec_pile_private.pilepreds PrivPILE. 

Definition ONEPILE : spec_onepile.OnePileAPD := ONEPILE PILE.

Definition Onepile_Pile_VSU :=
  ltac:(linkVSUs (PilePrivateVSU M) (OnepileVSU M PILE) ). 

(* Eval simpl in map fst (VSU_Exports Onepile_Pile_VSU).  *)
 (* Pile_new, Pile_add, Pile_count, Pile_free, Onepile_init, Onepile_add, Onepile_count *)

Definition Apile_Onepile_Pile_VSU :=
  ltac:(linkVSUs (Onepile_Pile_VSU) (ApileVSU M PrivPILE)). 

Definition Triang_Apile_Onepile_Pile_VSU :=
  ltac:(linkVSUs Apile_Onepile_Pile_VSU (TriangVSU M PILE)). 

Definition Core_VSU :=
  privatizeExports 
  ltac:(linkVSUs MallocFreeVSU Triang_Apile_Onepile_Pile_VSU)
  [stdlib._malloc; stdlib._free; stdlib._exit; pile._Pile_new;
   pile._Pile_add; pile._Pile_count; pile._Pile_free].