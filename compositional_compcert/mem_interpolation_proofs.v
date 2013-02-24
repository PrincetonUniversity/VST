Load loadpath.
Require Import compositional_compcert.mem_interpolants.
Require Import compositional_compcert.mem_interpolation_EE.
Require Import compositional_compcert.mem_interpolation_EI.
Require Import compositional_compcert.mem_interpolation_IE.
Require Import compositional_compcert.mem_interpolation_II.

Module MemoryInterpolations <: MemoryInterpolationAxioms.
Definition  interpolate_II := interpolate_II.
Definition  interpolate_EI := interpolate_EI.
Definition  interpolate_IE := interpolate_IE.
Definition  interpolate_EE := interpolate_EE.
End MemoryInterpolations.

