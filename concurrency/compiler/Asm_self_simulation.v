Require Import compcert.x86.Asm.

Require Import VST.concurrency.compiler.self_simulation.

Require Import VST.concurrency.common.Asm_core.

Section AsmSelfSim.

  Context (ge:genv).
  Lemma Asm_self_simulation:
    self_simulation _ (Asm_core_sem ge).
  Admitted.

End AsmSelfSim.
