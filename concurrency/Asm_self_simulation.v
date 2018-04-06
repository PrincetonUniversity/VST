Require Import compcert.ia32.Asm.

Require Import VST.concurrency.self_simulation.

Definition Asm_self_simulation tp:
  self_simulation (ia32.Asm.semantics tp) _ State.
(*ia32.Asm.get_mem*)
Admitted.

