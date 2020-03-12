Require Import VST.floyd.proofauto.
Require Import fastpile.
Require Import spec_stdlib.
Require Import spec_fastpile.

Instance FastpileCompSpecs : compspecs. make_compspecs prog. Defined.

(*On contrast to spec_pile_private, the predicate bundle here is not 
  defined parametrically in a MemMGRPredicates bundle.*)
Section PilePrivatePreds.

(*Previsouly called pilerep, and will be used to instantiate spec_pile.pilerep,
  but given a different name for didactic purposes and to avoid qualified names*)
Definition fastprep (sigma: list Z) (p: val) : mpred :=
 EX s:Z, !! (0 <= s <= Int.max_signed /\
   Forall (Z.le 0) sigma /\
  (0 <= sumlist sigma <= Int.max_signed -> s=sumlist sigma))
   &&  data_at Ews tpile (Vint (Int.repr s)) p.
Opaque fastprep.

Record FastpilePrivatePredicates := {
  pilepreds :> PilePredicates;
  pile_rep_exposed:  spec_fastpile.pilerep pilepreds = fastprep
}.
End PilePrivatePreds.

(*However, as PileASI requires a MemMGRPredicates bundle we have to make
  FastpilePrivateASI  depend in one, too.*)
Section FastpilePrivateASI.
Variable M: MemMGRPredicates.
Variable FASTPILEPRIV:FastpilePrivatePredicates.

Definition FastpilePrivateASI:funspecs := PileASI M FASTPILEPRIV.

End FastpilePrivateASI.
