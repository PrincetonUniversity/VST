Require Export VST.msl.msl_standard.
Require Export Coq.Logic.Classical.

Tactic Notation "LEM" constr(P) :=
  (destruct (classic (P))).
