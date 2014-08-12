Require Import effect_interpolants.
Require Import effect_interpolation_II.
Require Import mem_interpolation_II.

Module EffectInterpolations <: EffectInterpolationAxioms.
Definition effect_interp_II := EFF_interp_II.
Definition interpolate_II_strongHeqMKI:= interpolate_II_strongHeqMKI.
End EffectInterpolations.

