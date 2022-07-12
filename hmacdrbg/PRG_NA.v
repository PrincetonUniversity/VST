Set Implicit Arguments.

Require Import fcf.FCF.
Require Import fcf.CompFold.
Require Import fcf.PRF.

Section PRG_Nonadaptive.

Variable S R : Set.
Hypothesis S_EqDec : EqDec S.
Hypothesis R_EqDec : EqDec R.
Variable RndR : Comp R.
Variable Instantiate: Comp S.
Variable Generate : S -> nat -> Comp (list R * S).

Variable A1 : Comp (list nat).
Variable A2 : list (list R) -> Comp bool.

Definition PRG_G1: Comp bool :=
  s <-$ Instantiate;
  requestList <-$ A1;
  [bits, _] <-$2 oracleMap _ _ Generate s requestList;
  A2 bits. 

Definition Generate_ideal n :=
  compMap _ (fun _ => RndR) (forNats n).

Definition PRG_G2 : Comp bool :=
  requestList <-$ A1;
  bits <-$ compMap _ Generate_ideal requestList;
  A2 bits.

Definition PRG_Nonadaptive_Advantage :=
  | Pr[PRG_G1] - Pr[PRG_G2] |.

End PRG_Nonadaptive.
