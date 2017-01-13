Require Import ListSet.

Require Import sepcomp.extspec.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.rg_semantics.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.linking.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Set Implicit Arguments.

(**  "Compilable" Extensions *)

Module CompilabilityInvariant. Section CompilabilityInvariant.
 Variables
  (F_S V_S F_T V_T: Type) (** source and target extension global environments *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: Type) (** global environments of core semantics *)
  (cS cT: Type) (** corestates of source and target core semantics *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: CoopCoreSem (Genv.t F_S V_S) xS) (** extended source semantics *)
  (esemT: CoopCoreSem (Genv.t F_T V_T) xT) (** extended target semantics *)
 (** a set of core semantics *)
  (csemS: CoopCoreSem (Genv.t fS vS) cS)
 (** a set of core semantics *)
  (csemT: CoopCoreSem (Genv.t fT vT) cT)
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext). (** extension signature *)

 Variables
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T)
  (ge_coreS: Genv.t fS vS) (ge_coreT: Genv.t fT vT).

 Variable (E_S: @Extension.Sig mem Z Zint Zext (Genv.t F_S V_S) xS esemS
   _ (*_*) cS csemS).
 Variable (E_T: @Extension.Sig mem Z Zint Zext (Genv.t F_T V_T) xT esemT
   _ (*_*) cT csemT).

 Variable entry_points: list (val*val*signature). (*TODO: SHOULD PERHAPS BE GENERALIZED*)
 Variable core_data: Type.
 Variable match_state: core_data -> meminj -> cS -> mem -> cT -> mem -> Prop.
 Variable core_ord: core_data -> core_data -> Prop.
 Implicit Arguments match_state [].
 Implicit Arguments core_ord [].

 Notation PROJ_CORE := (Extension.proj_core).
 Infix "\o" := (Extension.zmult) (at level 66, left associativity).
 Notation zint_invar_after_external := (Extension.zint_invar_after_external).

 Definition match_states (cd: core_data) (j: meminj) (s1: xS) m1 (s2: xT) m2 :=
   match_state cd j (PROJ_CORE E_S s1) m1 (PROJ_CORE E_T s2) m2 /\
   Extension.proj_zint E_S s1 = Extension.proj_zint E_T s2.

 Inductive Sig: Type := Make: forall

  (match_state_runnable: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 -> runnable csemS c1=runnable csemT c2)

  (match_state_inj: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 -> Mem.inject j m1 m2)

  (match_state_preserves_globals: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 ->
    Events.meminj_preserves_globals ge_coreS j)

 (extension_diagram: forall s1 m1 s1' m1' s2 m2 ef sig args1 args2 cd j,
   let c1 := PROJ_CORE E_S s1 in
   let c2 := PROJ_CORE E_T s2 in
   runnable csemS c1=false ->
   runnable csemT c2=false ->
   at_external csemS c1 = Some (ef, sig, args1) ->
   at_external csemT c2 = Some (ef, sig, args2) ->
   match_states cd j s1 m1 s2 m2 ->
   Mem.inject j m1 m2 ->
   Events.meminj_preserves_globals ge_S j ->
   Forall2 (val_inject j) args1 args2 ->
   corestep esemS ge_S s1 m1 s1' m1' ->
   exists s2', exists m2', exists cd', exists j',
     inject_incr j j' /\
     Events.inject_separated j j' m1 m2 /\
     match_states cd' j' s1' m1' s2' m2' /\
     Mem.unchanged_on (Events.loc_unmapped j) m1 m1' /\
     Mem.unchanged_on (Events.loc_out_of_reach j m1) m2 m2' /\
     ((corestep_plus esemT ge_T s2 m2 s2' m2') \/
      corestep_star esemT ge_T s2 m2 s2' m2' /\ core_ord cd' cd))

 (at_external_match: forall s1 m1 s2 m2 ef sig args1 args2 cd j,
   let c1 := PROJ_CORE E_S s1 in
   let c2 := PROJ_CORE E_T s2 in
   runnable csemS c1=runnable csemT c2 ->
   at_external esemS s1 = Some (ef, sig, args1) ->
   at_external csemS c1 = Some (ef, sig, args1) ->
   match_state cd j c1 m1 c2 m2 ->
   Mem.inject j m1 m2 ->
   Events.meminj_preserves_globals ge_S j ->
   Forall2 (val_inject j) args1 args2 ->
   at_external csemT c2 = Some (ef, sig, args2) ->
   at_external esemT s2 = Some (ef, sig, args2))

  (initial_diagram: forall v1 vals1 s1 m1 v2 vals2 m2 j sig,
    In (v1, v2, sig) entry_points ->
    initial_core esemS ge_S v1 vals1 = Some s1 ->
    Mem.inject j m1 m2 ->
    Forall2 (val_inject j) vals1 vals2 ->
    exists cd, exists s2,
      initial_core esemT ge_T v2 vals2 = Some s2 /\
      match_states cd j s1 m1 s2 m2)

 (halted_diagram: forall cd j c1 m1 c2 m2 v1,
   match_states cd j c1 m1 c2 m2 ->
   halted esemS c1 = Some v1 ->
   exists v2, val_inject j v1 v2 /\
     halted esemT c2 = Some v2 /\
     Mem.inject j m1 m2),
 Sig.

End CompilabilityInvariant. End CompilabilityInvariant.

Module CompilableExtension. Section CompilableExtension.
 Variables
  (F_S V_S F_T V_T: Type) (** source and target extension global environments *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: Type) (** global environments of core semantics *)
  (cS cT: Type) (** corestates of source and target core semantics *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: CoopCoreSem (Genv.t F_S V_S) xS) (** extended source semantics *)
  (esemT: CoopCoreSem (Genv.t F_T V_T) xT) (** extended target semantics *)
  (csemS: CoopCoreSem (Genv.t fS vS) cS)
  (csemT: CoopCoreSem (Genv.t fT vT) cT)
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext). (** extension signature *)

 Variables
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T)
  (ge_coreS: Genv.t fS vS) (ge_coreT: Genv.t fT vT).

 Variable (E_S: @Extension.Sig mem Z Zint Zext (Genv.t F_S V_S) xS esemS _ cS csemS).
 Variable (E_T: @Extension.Sig mem Z Zint Zext (Genv.t F_T V_T) xT esemT _ cT csemT).

 Variable entry_points: list (val*val*signature).
 Variable core_data: Type.
 Variable match_state: core_data -> meminj -> cS -> mem -> cT -> mem -> Prop.
 Implicit Arguments match_state [].
 Variable core_ord: core_data -> core_data -> Prop.

 Import Extension.

 Definition match_states (cd: core_data) (j: meminj) (s1: xS) m1 (s2: xT) m2 :=
   match_state cd j (proj_core E_S s1) m1 (proj_core E_T s2) m2 /\
   Extension.proj_zint E_S s1 = Extension.proj_zint E_T s2.

 Import Forward_simulation_inj_exposed.

 Record Sig: Type := Make {
   _ : Forward_simulation_inject esemS esemT
         ge_S ge_T entry_points core_data match_states core_ord
 }.

End CompilableExtension. End CompilableExtension.

Module EXTENSION_COMPILABILITY. Section EXTENSION_COMPILABILITY.
 Variables
  (F_S V_S F_T V_T: Type) (** source and target extension global environments *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: Type) (** global environments of core semantics *)
  (cS cT: Type) (** corestates of source and target core semantics *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: CoopCoreSem (Genv.t F_S V_S) xS) (** extended source semantics *)
  (esemT: CoopCoreSem (Genv.t F_T V_T) xT) (** extended target semantics *)
  (csemS: CoopCoreSem (Genv.t fS vS) cS)
  (csemT: CoopCoreSem (Genv.t fT vT) cT)
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext). (** extension signature *)

 Variables
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T)
  (ge_coreS: Genv.t fS vS) (ge_coreT: Genv.t fT vT).

 Variable (E_S: @Extension.Sig mem Z Zint Zext (Genv.t F_S V_S) xS esemS _ cS csemS).
 Variable (E_T: @Extension.Sig mem Z Zint Zext (Genv.t F_T V_T) xT esemT _ cT csemT).

 Variable entry_points: list (val*val*signature).
 Variable core_data: Type.
 Variable match_state: core_data -> meminj -> cS -> mem -> cT -> mem -> Prop.
 Implicit Arguments match_state [].
 Variable core_ord: core_data -> core_data -> Prop.

 Import Extension.

 Definition match_states (cd: core_data) (j: meminj) (s1: xS) m1 (s2: xT) m2 :=
   match_state cd j (proj_core E_S s1) m1 (proj_core E_T s2) m2 /\
   Extension.proj_zint E_S s1 = Extension.proj_zint E_T s2.

 Import Forward_simulation_inj_exposed.

 Record Sig: Type := Make {
   _ : Forward_simulation_inject csemS csemT ge_coreS ge_coreT
         entry_points core_data match_state core_ord ->
       genvs_domain_eq ge_S ge_T ->
       genvs_domain_eq ge_S ge_coreS ->
       genvs_domain_eq ge_T ge_coreT ->
       core_compatible ge_S ge_coreS E_S ->
       core_compatible ge_T ge_coreT E_T ->
       CompilabilityInvariant.Sig
         esemS esemT csemS csemT ge_S ge_T ge_coreS E_S E_T
         entry_points match_state core_ord ->
       CompilableExtension.Sig esemS esemT csemS csemT ge_S ge_T E_S E_T
         entry_points match_state core_ord
 }.

End EXTENSION_COMPILABILITY. End EXTENSION_COMPILABILITY.
