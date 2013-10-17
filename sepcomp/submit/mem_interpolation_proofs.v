Require Import sepcomp.mem_interpolants.
Require Import sepcomp.mem_interpolation_EE.
Require Import sepcomp.mem_interpolation_EI.
Require Import sepcomp.mem_interpolation_IE.
Require Import sepcomp.mem_interpolation_II.

Module MemoryInterpolations <: MemoryInterpolationAxioms.
Definition interpolate_II := interpolate_II.
Definition interpolate_EI := interpolate_EI.
Definition interpolate_IE := interpolate_IE.
Definition interpolate_EE := interpolate_EE.
Definition interpolate_II_HeqMKI := interpolate_II_HeqMKI.
End MemoryInterpolations.

