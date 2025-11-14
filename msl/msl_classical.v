Require Export VST.msl.msl_standard.
Require Export Stdlib.Logic.Classical.

Tactic Notation "LEM" constr(P) :=
  (destruct (classic (P))).
