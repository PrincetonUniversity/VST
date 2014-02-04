Require Import MirrorShard.CancelTacBedrock.
Require Import MirrorShard.Expr MirrorShard.SepExpr.
Require Import MirrorShard.SepHeap MirrorShard.SepCancel.
Require Import MirrorShard.SepLemma.
Require Import sep.
Require Import FMapInterface.
Require Import SimpleInstantiation.
Require Import MirrorShard.ExprUnifySynGenRec.


Module SH := SepHeap.Make VericSepLogic Sep.
Module SL := SepLemma VericSepLogic Sep.
Module FM := FMapList.Make NatMap.Ordered_nat.
Module SUBST := SimpleInstantiation.Make FM.
Module UNIFY := ExprUnifySynGenRec.Make SUBST.
Module UNF := Unfolder.Make VericSepLogic Sep SH SUBST UNIFY SL.

Module CancelModule := CancelTacBedrock.Make VericSepLogic Sep SH SL SUBST UNIFY UNF.

(*CancelModule.canceller some things...*)