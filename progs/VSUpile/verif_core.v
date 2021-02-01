Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Require Import VST.floyd.linking.

Require Import spec_stdlib.

Require Import verif_stdlib.
Require Import verif_pile.
Require Import verif_onepile.
Require Import verif_apile.
Require Import verif_triang.

Section CORE_VSU.
(* This Section demonstrates that one can link together several VSUs
  that are all parametrized by an _abstract_ external library,
  in this case the MallocFree VSU, without actually having an implementation
   of that external library.  That is, they are linked based on the APD/ASI,
   even without access to the VSU. *)
Variable M : MallocFreeAPD.
Definition PrivPILE: spec_pile_private.PilePrivateAPD M := PILEPRIV M.
Definition PILE: spec_pile.PileAPD := spec_pile_private.pilepreds PrivPILE. 

Definition Onepile_Pile_VSU :=
  ltac:(linkVSUs (PilePrivateVSU M) (OnepileVSU M PILE) ). 

(* Eval simpl in map fst (VSU_Exports Onepile_Pile_VSU).  *)
 (* Pile_new, Pile_add, Pile_count, Pile_free, Onepile_init, Onepile_add, Onepile_count *)

Definition Apile_Onepile_Pile_VSU :=
  ltac:(linkVSUs Onepile_Pile_VSU (ApileVSU M PrivPILE)). 

Definition Triang_Apile_Onepile_Pile_VSU :=
  ltac:(linkVSUs Apile_Onepile_Pile_VSU (TriangVSU M PILE)).
End CORE_VSU.

Definition Core_VSU :=
  ltac:(linkVSUs MallocFreeVSU (Triang_Apile_Onepile_Pile_VSU verif_stdlib.M)).