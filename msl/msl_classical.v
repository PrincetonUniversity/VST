Require Export msl_standard.
Require Export Classical.

Tactic Notation "LEM" constr(P) :=
  (destruct (classic (P))).
