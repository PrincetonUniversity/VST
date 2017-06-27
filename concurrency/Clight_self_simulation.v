Require Import Clight.

Require Import concurrency.self_simulation.

Definition Clight_self_simulation (p: program) :
    self_simulation (Clight.semantics2 p) Clight.get_mem.
Admitted.
    