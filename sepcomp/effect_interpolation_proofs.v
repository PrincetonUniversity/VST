Require Import sepcomp.effect_interpolants.
Require Import sepcomp.effect_interpolation_II.
Require Import sepcomp.mem_interpolation_II.

Module EffectInterpolations <: EffectInterpolationAxioms.
Definition effect_interp_II := EFF_interp_II.
Definition interpolate_II_strongHeqMKI:= interpolate_II_strongHeqMKI.
End EffectInterpolations.

