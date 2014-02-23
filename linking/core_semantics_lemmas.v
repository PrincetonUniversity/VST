Require Import ZArith.

Require Import compcert.common.AST. (*for mksignature*)
Require Import compcert.common.Globalenvs.

Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

Definition Coresem2CoreSemantics {G C M} (csem: @Coresem.t G C M) := 
  Build_CoreSemantics G C M
   (@Coresem.initial_core _ _ _ csem) 
   (@Coresem.at_external _ _ _ csem)
   (@Coresem.after_external _ _ _ csem)
   (@Coresem.halted _ _ _ csem)
   (@Coresem.corestep _ _ _ csem)
   (@Coresem.corestep_not_at_external _ _ _ csem)
   (@Coresem.corestep_not_halted _ _ _ csem)
   (@Coresem.at_external_halted_excl _ _ _ csem)
   (@Coresem.after_at_external_excl _ _ _ csem).

Coercion Coresem2CoreSemantics : Coresem.t >-> CoreSemantics.

(* Uniform interface to inhabited CoreSemantics-like types [t] *)

Module Type CORESEM.

Axiom M : Type. (*memories*)

Axiom t : forall (G C: Type), Type.

Declare Instance instance {G C: Type} `{T : t G C} : @Coresem.t G C M.

End CORESEM.

(* Instances of CORESEM for CoopCoreSem, EffectSem *)

Arguments core_instance {G C M} _.

Instance coop_instance (G C : Type) (csem : @CoopCoreSem G C) 
  : @Coresem.t G C Memory.mem := core_instance csem.

Module Coopsem <: CORESEM.

Definition M := Memory.mem.

Definition t (G C: Type) := @CoopCoreSem G C.

Definition instance (G C: Type) (csem : t G C) := core_instance csem.

End Coopsem.

Definition Coopsem2CoreSemantics {G C} (csem : @Coopsem.t G C) 
  : @CoreSemantics G C Memory.mem := Coopsem.instance csem.

Coercion Coopsem2CoreSemantics : Coopsem.t >-> CoreSemantics.

Instance effect_instance (G C : Type) (csem : @EffectSem G C) 
  : @Coresem.t G C Memory.mem := core_instance csem.

Module EffectsemCore <: CORESEM.

Definition M := Memory.mem.

Definition t (G C: Type) := @EffectSem G C.

Definition instance (G C: Type) (csem : t G C) := effect_instance csem.

End EffectsemCore.

Definition EffectsemCore2CoreSemantics {G C} (csem : @EffectsemCore.t G C) 
  : @CoreSemantics G C Memory.mem := EffectsemCore.instance csem.

Coercion EffectsemCore2CoreSemantics : EffectsemCore.t >-> CoreSemantics.

(* Module type wrapper over effect semantics *)

Definition Effsem2EffectSem {G C} (sem: @Effsem.t G C) := 
  @Build_EffectSem G C 
   (@Effsem.sem _ _ sem)
   (@Effsem.effstep _ _ sem)
   (@Effsem.effax1 _ _ sem)
   (@Effsem.effax2 _ _ sem)
   (@Effsem.effstep_valid _ _ sem).

Coercion Effsem2EffectSem : Effsem.t >-> EffectSem.

Definition Effsem2Coresem {G C} (sem : @Effsem.t G C) 
  : @Coresem.t G C Memory.mem := coop_instance sem.

Coercion Effsem2Coresem : Effsem.t >-> Coresem.t.

Module Type EFFSEM.

Axiom t : forall (G C: Type), Type.

Declare Instance instance {G C: Type} `{T : t G C} : @Effsem.t G C.

End EFFSEM.

(* Instance of EFFSEM for EffectSem *)

Module Effectsem <: EFFSEM.

Definition t (G C: Type) := @EffectSem G C.

Definition instance (G C : Type) (sem : t G C) := effsem_instance _ _ sem.

End Effectsem.

Definition Effectsem_to_EffectSem {G C} (sem : @Effectsem.t G C) 
  : @EffectSem G C := sem.

Coercion Effectsem_to_EffectSem : Effectsem.t >-> EffectSem.

Definition Effectsem_to_CoreSemantics {G C} (sem : @Effectsem.t G C) 
  : @CoreSemantics G C Memory.mem := sem.

Coercion Effectsem_to_CoreSemantics : Effectsem.t >-> CoreSemantics.

Definition Effectsem_to_Coresem {G C} (sem : @Effectsem.t G C) 
  : @Coresem.t G C Memory.mem := Effectsem.instance sem.

Coercion Effectsem_to_Coresem : Effectsem.t >-> Coresem.t.

  