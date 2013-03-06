Load loadpath.
Require Import sepcomp.mem_interpolants.
Require Import sepcomp.i_EE.
Require Import sepcomp.i_EI.
Require Import sepcomp.i_IE.
Require Import sepcomp.i_II.

Module MemoryInterpolations <: MemoryInterpolationAxioms.
Definition  interpolate_II := interpolate_II.
Definition  interpolate_EI := interpolate_EI.
Definition  interpolate_IE := interpolate_IE.
Definition  interpolate_EE := interpolate_EE.
End MemoryInterpolations.

