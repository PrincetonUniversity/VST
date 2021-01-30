Require Import VST.floyd.proofauto.
Require Import pile.
Require Import spec_stdlib.
Require Import spec_pile.

Instance PileCompSpecs : compspecs. make_compspecs prog. Defined.
Definition tlist := Tstruct _list noattr.

(*Here we have case where one APD is defined parametrically in another one*)
Section PilePrivatePreds.
Variable M: MallocFreeAPD.

Fixpoint listrep (sigma: list Z) (x: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val,
       !! (0 <= h <=  Int.max_signed) && 
      data_at Ews tlist (Vint (Int.repr h), y) x 
     * malloc_token M Ews tlist x
     * listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.
Opaque listrep.

(*Previously called pilerep, and will be used to instantiate spec_pile.pilerep,
  but given a different name for didactic purposes and to avoid qualified names*)
Definition prep (sigma: list Z) (p: val) : mpred :=
  EX x:val, data_at Ews tpile x p * listrep sigma x.

Record PilePrivateAPD := {
  pilepreds :> PileAPD;
  pile_rep_exposed: pilerep pilepreds = prep
}.
End PilePrivatePreds.
Arguments pilepreds {M} p.

Section PilePrivateASI.

Variable M: MallocFreeAPD.
Variable PILEPRIV:PilePrivateAPD M.

Definition PilePrivateASI:funspecs := PileASI M PILEPRIV.

End PilePrivateASI.