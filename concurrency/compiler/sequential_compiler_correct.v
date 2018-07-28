Require Import compcert.common.ExposedSimulations.
Require Import compcert.cfrontend.Clight.
Require Import compcert.x86.Asm.


Module Type CompCert_correctness.

Parameter CompCert_compiler: Clight.program -> option Asm.program.
Hypothesis simpl_clight_semantic_preservation:
  forall (p:Clight.program) (tp:Asm.program),
  CompCert_compiler p = Some tp ->
  fsim_properties_inj (Clight.semantics2 p) (Asm.semantics tp) Clight.get_mem Asm.get_mem.


End CompCert_correctness.
