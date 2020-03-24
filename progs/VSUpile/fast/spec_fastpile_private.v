Require Import VST.floyd.proofauto.
Require Import fastpile.
Require Import spec_stdlib.
Require Import spec_fastpile.
Require Import PileModel.

Instance FastpileCompSpecs : compspecs. make_compspecs prog. Defined.

(*In contrast to spec_pile_private, the APD here is not 
  defined parametrically in a MallocFree-APD.*)
Section FastPilePrivateAPD.

(*Previously called pilerep, and will be used to instantiate spec_pile.pilerep,
  but given a different name for didactic purposes and to avoid qualified names*)
Definition fastprep (sigma: list Z) (p: val) : mpred :=
 EX s:Z, !! (0 <= s <= Int.max_signed /\
   Forall (Z.le 0) sigma /\
  (0 <= sumlist sigma <= Int.max_signed -> s=sumlist sigma))
   &&  data_at Ews tpile (Vint (Int.repr s)) p.
Opaque fastprep.

Record FastpilePrivateAPD := {
  pilepreds :> PileAPD;
  pile_rep_exposed: pilerep pilepreds = fastprep
}.
End FastPilePrivateAPD.

(*However, as PileASI requires a MallocFree-APD we have to make
  FastpilePrivateASI depend on one, too. That's reasonable, since
  fastpile still mallocs and frees memory.*)
Section FastpilePrivateASI.
Variable M: MallocFreeAPD.
Variable FASTPILEPRIV:FastpilePrivateAPD.

Definition FastpilePrivateASI:funspecs := PileASI M FASTPILEPRIV.

End FastpilePrivateASI.
