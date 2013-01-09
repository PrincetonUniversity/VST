Load loadpath.
Require Import ListSet.

Require Import veric.sim.
Require Import veric.extspec.
Require Import veric.rg_sim.
Require Import veric.extension.

Require Import Axioms.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.

Set Implicit Arguments.

(**  "Compilable" Extensions *)

(*This is an [F,V]-independent definition of meminj_preserves_globals*)
Definition meminj_preserves_globals (globals: (block->Prop)*(block->Prop)) f :=
  (forall b, fst globals b -> f b = Some (b, 0)) /\
  (forall b, snd globals b -> f b = Some (b, 0)) /\
  (forall b1 b2 delta, snd globals b2 -> f b1 = Some (b2, delta) -> b1=b2).

Definition genv2blocks {F V: Type} (ge: Genv.t F V) := 
  (fun b => exists id, Genv.find_symbol ge id = Some b,
   fun b => exists gv, Genv.find_var_info ge b = Some gv).

(** Some administrative requirements on the interactions between
   extensions and inner cores. Perhaps some of these conditions could be 
   merged with those for "safe" extensions. *)

Section CoreCompatible.
Variables 
 (G xT M D Z Zint Zext: Type) (gT: nat -> Type) (cT: nat -> Type) (dT: nat -> Type)
 (esem: CoreSemantics G xT M D) 
 (csem: forall i:nat, CoreSemantics (gT i) (cT i) M (dT i))
 (csig: ef_ext_spec M Z)
 (esig: ef_ext_spec M Zext)
 (handled: list AST.external_function).

Variables (ge: G) (genv_map : forall i:nat, gT i).
Variable E: Extension.Sig gT cT dT Zint esem csem csig esig handled.

Import Extension.

Inductive core_compatible: Type := CoreCompatible: forall
  (** When the active thread is runnable, a step in the extended
     semantics can be tracked back to a corestep of the active
     thread. *)
  (runnable_corestep: forall s m s' m' c,
    runnable (csem (active E s)) c=true -> 
    proj_core E (active E s) s = Some c -> 
    corestep esem ge s m s' m' -> 
    exists c', corestep (csem (active E s)) (genv_map (active E s)) c m c' m' /\ 
     proj_core E (active E s) s' = Some c') 

  (** After a corestep of the active inner core, the active thread's new
     corestate is appropriately injected into the extended state. *)
  (corestep_pres: forall s (c: cT (active E s)) m c' s' m',
    proj_core E (active E s) s = Some c -> 
    corestep (csem (active E s)) (genv_map (active E s)) c m c' m' -> 
    corestep esem ge s m s' m' -> 
    active E s = active E s' /\ 
    proj_core E (active E s) s' = Some c')
  (** A corestep of the currently active core forces a corestep of the
     extended semantics*)
  (corestep_prog: forall s (c: cT (active E s)) m c' m',
    proj_core E (active E s) s = Some c -> 
    corestep (csem (active E s)) (genv_map (active E s)) c m c' m' -> 
    exists s', corestep esem ge s m s' m')

  (** Other cores remain unchanged after coresteps of the active core. *)
  (corestep_others_forward: forall s s' (c: cT (active E s')) m c' m',
    active E s=active E s' -> 
    proj_core E (active E s') s' = Some c' -> 
    corestep (csem (active E s')) (genv_map (active E s')) c m c' m' -> 
    corestep esem ge s m s' m' -> 
    forall j, (active E s)<>j -> proj_core E j s = proj_core E j s')
  (corestep_others_backward: forall s c m s' c' m' n,
    proj_core E (active E s) s = Some c -> 
    corestepN (csem (active E s)) (genv_map (active E s)) n c m c' m' -> 
    corestepN esem ge n s m s' m' -> 
    forall j, (active E s)<>j -> proj_core E j s = proj_core E j s')

  (** The active core doesn't change along active coresteps. *)
  (after_ext_pres: forall s (c: cT (active E s)) c' s' retv,
    proj_core E (active E s) s = Some c -> 
    after_external (csem (active E s)) retv c = Some c' -> 
    after_external esem retv s = Some s' -> 
    active E s=active E s')
  (** The extension state can be updated to match AfterExternal on the 
     active core. *)
  (after_ext_prog: forall s (c: cT (active E s)) c' retv,
    proj_core E (active E s) s = Some c -> 
    after_external (csem (active E s)) retv c = Some c' -> 
    exists s', after_external esem retv s = Some s' /\
     proj_core E (active E s) s' = Some c')

  (** AfterExternal on extension cores leaves all but the active
     corestate unchanged. *)
  (after_ext_others: forall s s' retv,
    after_external esem retv s = Some s' -> 
    forall j, (active E s)<>j -> 
     proj_core E j s = proj_core E j s')

  (** REPEATED HERE TO GET AROUND A BUG IN PROGRAM: 
     HYP (1) NOT GENERATED WHEN PROVING OBLIGATION *)
  (at_extern_call: forall s ef sig args,
    at_external esem s = Some (ef, sig, args) -> 
    exists c, proj_core E (active E s) s = Some c /\
     at_external (csem (active E s)) c = Some (ef, sig, args)),
  core_compatible.

End CoreCompatible.

(** Rely-Guarantee Simulations *)

Module RelyGuaranteeSimulation. Section RelyGuaranteeSimulation.
 Variables (F1 V1 C1 INIT1 G2 C2 INIT2: Type).
 Variables 
  (sourceC: CoreSemantics (Genv.t F1 V1) C1 mem INIT1)
  (targetC: CoreSemantics G2 C2 mem INIT2) 
  (ge1: Genv.t F1 V1) (ge2: G2) 
  (entry_points: list (val * val * signature))
  (core_data: Type)
  (match_state: core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop).

 Import Sim_inj_exposed.

 Inductive Sig: Type := Make: forall
  (match_state_runnable: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 -> runnable sourceC c1=runnable targetC c2)
  (match_state_inj: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 -> Mem.inject j m1 m2)
  (match_state_preserves_globals: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 -> 
    Events.meminj_preserves_globals ge1 j)

  (rely: forall (ge1: Genv.t F1 V1) cdC m1 m1' f f' m2 m2' c1 c2,
    (** Rely *)
    Mem.inject f m1 m2 -> 
    meminj_preserves_globals (genv2blocks ge1) f -> 
    Mem.inject f' m1' m2' -> 
    mem_unchanged_on (loc_unmapped f) m1 m1' ->
    mem_unchanged_on (loc_out_of_reach f m1) m2 m2' ->
    inject_incr f f' -> 
    inject_separated f f' m1 m2 -> 

    (** Match is stable *)
    match_state cdC f c1 m1 c2 m2 -> 
    match_state cdC f' c1 m1' c2 m2')
    
  (guarantee: forall ge1 ge2 cd m1 m1' f m2 m2' c1 c2 c1' c2' n,
    Mem.inject f m1 m2 -> 
    meminj_preserves_globals (genv2blocks ge1) f -> 
    match_state cd f c1 m1 c2 m2 -> 
    corestep sourceC ge1 c1 m1 c1' m1' -> 
    corestepN targetC ge2 n c2 m2 c2' m2' -> 

    (** Guarantee *)
    mem_unchanged_on (loc_unmapped f) m1 m1' /\
    mem_unchanged_on (loc_out_of_reach f m1) m2 m2'),
  Sig.

End RelyGuaranteeSimulation. End RelyGuaranteeSimulation.

Definition val_inject_opt (j: meminj) (v1 v2: option val) :=
  match v1, v2 with Some v1', Some v2' => val_inject j v1' v2'
  | None, None => True
  | _, _ => False
  end.

Module CompilabilityInvariant. Section CompilabilityInvariant. 
 Variables
  (F_S V_S F_T V_T: Type) (** source and target extension global environments *)
  (D_S D_T: Type) (** source and target extension initialization data *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: nat -> Type) (** global environments of core semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: nat -> Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: CoreSemantics (Genv.t F_S V_S) xS mem D_S) (** extended source semantics *)
  (esemT: CoreSemantics (Genv.t F_T V_T) xT mem D_T) (** extended target semantics *)
  (csemS: forall i:nat, CoreSemantics (Genv.t (fS i) (vS i)) (cS i) mem (dS i)) (** a set of core semantics *)
  (csemT: forall i:nat, CoreSemantics (Genv.t (fT i) (vT i)) (cT i) mem (dT i)) (** a set of core semantics *)
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext) (** extension signature *)
  (handled: list AST.external_function) (** functions handled by this extension *)
  (threads_max: nat).

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T) 
  (genv_mapS: forall i:nat, Genv.t (fS i) (vS i))
  (genv_mapT: forall i:nat, Genv.t (fT i) (vT i)).

 Variable (E_S: Extension.Sig (fun i => Genv.t (fS i) (vS i)) cS dS Zint esemS csemS
                  csig esig handled).
 Variable (E_T: Extension.Sig (fun i => Genv.t (fT i) (vT i)) cT dT Zint esemT csemT 
                  csig esig handled).

 Variable entry_points: list (val*val*signature). (*TODO: SHOULD PERHAPS BE GENERALIZED*)
 Variable core_data: forall i: nat, Type.
 Variable match_state: forall i: nat, 
   core_data i -> meminj -> cS i -> mem -> cT i -> mem -> Prop.
 Variable core_ord: forall i: nat, (core_data i) -> (core_data i) -> Prop.
 Implicit Arguments match_state [].
 Implicit Arguments core_ord [].

 Notation PROJ_CORE := (Extension.proj_core).
 Infix "\o" := (Extension.zmult) (at level 66, left associativity). 
 Notation ACTIVE := (Extension.active).
 Notation active_proj_core := (Extension.active_proj_core).
 Notation notat_external_handled := (Extension.notat_external_handled).
 Notation at_external_not_handled := (Extension.at_external_not_handled).
 Notation ext_upd_at_external := (Extension.ext_upd_at_external).

 Definition core_datas := forall i:nat, core_data i.

 Definition core_ords cd1 cd2 := 
  exists i, (i < threads_max)%nat /\
   (forall j, (j < i)%nat -> cd1 j=cd2 j) /\ core_ord i (cd1 i) (cd2 i)%nat.

 Variable (R: meminj -> xS -> mem -> xT -> mem -> Prop).

 Definition match_states (cd: core_datas) (j: meminj) (s1: xS) m1 (s2: xT) m2 :=
   R j s1 m1 s2 m2 /\ ACTIVE E_S s1=ACTIVE E_T s2 /\
   forall i c1, PROJ_CORE E_S i s1 = Some c1 -> 
     exists c2, PROJ_CORE E_T i s2 = Some c2 /\ 
       match_state i (cd i) j c1 m1 c2 m2.

 Inductive Sig: Type := Make: forall  
 (corestep_rel: forall cd j j' s1 c1 m1 c1' m1' s2 c2 m2 c2' m2' s1' s2' n cd', 
   PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
   match_states cd j s1 m1 s2 m2 -> 
   Mem.inject j m1 m2 -> 
   meminj_preserves_globals (genv2blocks ge_S) j -> 
   inject_incr j j' -> 
   Events.inject_separated j j' m1 m2 -> 
   corestep (csemS (ACTIVE E_S s1)) (genv_mapS (ACTIVE E_S s1)) c1 m1 c1' m1' -> 
   corestepN (csemT (ACTIVE E_S s1)) (genv_mapT (ACTIVE E_S s1)) n c2 m2 c2' m2' ->
   corestep esemS ge_S s1 m1 s1' m1' -> 
   corestepN esemT ge_T n s2 m2 s2' m2' -> 
   match_state (ACTIVE E_S s1) cd' j' c1' m1' c2' m2' -> 
   Events.mem_unchanged_on (Events.loc_unmapped j) m1 m1' -> 
   Events.mem_unchanged_on (Events.loc_out_of_reach j m1) m2 m2' -> 
   R j' s1' m1' s2' m2')

 (after_external_rel: forall cd j j' s1 m1 s2 m2 s1' m1' s2' m2' ret1 ret2 ef sig args1,
   match_states cd j s1 m1 s2 m2 -> 
   inject_incr j j' -> 
   Events.inject_separated j j' m1 m2 -> 
   Mem.inject j' m1' m2' -> 
   mem_forward m1 m1'-> 
   Events.mem_unchanged_on (Events.loc_unmapped j) m1 m1' -> 
   mem_forward m2 m2' -> 
   Events.mem_unchanged_on (Events.loc_out_of_reach j m1) m2 m2' -> 
   at_external esemS s1 = Some (ef, sig, args1) -> 
   after_external esemS ret1 s1 = Some s1' -> 
   after_external esemT ret2 s2 = Some s2' -> 
   R j' s1' m1' s2' m2')   
 
 (extension_diagram: forall s1 m1 s1' m1' s2 c1 c2 m2 ef sig args1 args2 cd j,
   PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
   runnable (csemS (ACTIVE E_S s1)) c1=false -> 
   runnable (csemT (ACTIVE E_S s1)) c2=false -> 
   at_external (csemS (ACTIVE E_S s1)) c1 = Some (ef, sig, args1) -> 
   at_external (csemT (ACTIVE E_S s1)) c2 = Some (ef, sig, args2) -> 
   match_states cd j s1 m1 s2 m2 -> 
   Mem.inject j m1 m2 -> 
   Events.meminj_preserves_globals ge_S j -> 
   Forall2 (val_inject j) args1 args2 -> 
   Forall2 Val.has_type args2 (sig_args sig) -> 
   corestep esemS ge_S s1 m1 s1' m1' -> 
   exists s2', exists m2', exists cd', exists j',
     inject_incr j j' /\
     Events.inject_separated j j' m1 m2 /\
     match_states cd' j' s1' m1' s2' m2' /\
     Events.mem_unchanged_on (Events.loc_unmapped j) m1 m1' /\
     Events.mem_unchanged_on (Events.loc_out_of_reach j m1) m2 m2' /\
     ((corestep_plus esemT ge_T s2 m2 s2' m2') \/
      corestep_star esemT ge_T s2 m2 s2' m2' /\ core_ords cd' cd))

 (at_external_match: forall s1 m1 s2 c1 c2 m2 ef sig args1 args2 cd j,
   ACTIVE E_S s1=ACTIVE E_T s2 -> 
   PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
   runnable (csemS (ACTIVE E_S s1)) c1=runnable (csemT (ACTIVE E_S s1)) c2 -> 
   at_external esemS s1 = Some (ef, sig, args1) -> 
   at_external (csemS (ACTIVE E_S s1)) c1 = Some (ef, sig, args1) -> 
   match_state (ACTIVE E_S s1) cd j c1 m1 c2 m2 -> 
   Mem.inject j m1 m2 -> 
   Events.meminj_preserves_globals ge_S j -> 
   Forall2 (val_inject j) args1 args2 -> 
   Forall2 Val.has_type args2 (sig_args sig) -> 
   at_external (csemT (ACTIVE E_S s1)) c2 = Some (ef, sig, args2) -> 
   at_external esemT s2 = Some (ef, sig, args2))

 (make_initial_core_diagram: forall v1 vals1 s1 m1 v2 vals2 m2 j sig,
   In (v1, v2, sig) entry_points -> 
   make_initial_core esemS ge_S v1 vals1 = Some s1 -> 
   Mem.inject j m1 m2 -> 
   Forall2 (val_inject j) vals1 vals2 -> 
   Forall2 Val.has_type vals2 (sig_args sig) -> 
   exists cd, exists s2, 
     make_initial_core esemT ge_T v2 vals2 = Some s2 /\
     match_states cd j s1 m1 s2 m2)
 
 (safely_halted_step: forall cd j c1 m1 c2 m2 v1,
   match_states cd j c1 m1 c2 m2 -> 
   safely_halted esemS c1 = Some v1 -> 
   exists v2, val_inject j v1 v2 /\
     safely_halted esemT c2 = Some v2 /\ Mem.inject j m1 m2)
     
 (safely_halted_diagram: forall cd j m1 m1' m2 rv1 s1 s2 s1' c1 c2,
   match_states cd j s1 m1 s2 m2 -> 
   PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
   PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
   safely_halted (csemS (ACTIVE E_S s1)) c1 = Some rv1 -> 
   corestep esemS ge_S s1 m1 s1' m1' ->  
   exists rv2, 
     safely_halted (csemT (ACTIVE E_S s1)) c2 = Some rv2 /\
     val_inject j rv1 rv2 /\
   exists s2', exists m2', exists cd', exists j', 
     inject_incr j j' /\
     Events.inject_separated j j' m1 m2 /\
     corestep esemT ge_T s2 m2 s2' m2' /\
     match_states cd' j' s1' m1' s2' m2' /\
     Events.mem_unchanged_on (Events.loc_unmapped j) m1 m1' /\
     Events.mem_unchanged_on (Events.loc_out_of_reach j m1) m2 m2'
),
 Sig.

End CompilabilityInvariant. End CompilabilityInvariant.

Definition genvs_domain_eq {F1 F2 V1 V2: Type} (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) :=
  (forall b, fst (genv2blocks ge1) b <-> fst (genv2blocks ge2) b) /\
  (forall b, snd (genv2blocks ge1) b <-> snd (genv2blocks ge2) b).

Module CompilableExtension. Section CompilableExtension. 
 Variables
  (F_S V_S F_T V_T: Type) (** global environments *)
  (D_S D_T: Type) (** source and target extension initialization data *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: nat -> Type) (** global environments of core semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: nat -> Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: CoreSemantics (Genv.t F_S V_S) xS mem D_S) (** extended source semantics *)
  (esemT: CoreSemantics (Genv.t F_T V_T) xT mem D_T) (** extended target semantics *)
  (csemS: forall i:nat, CoreSemantics (Genv.t (fS i) (vS i)) (cS i) mem (dS i)) (** a set of core semantics *)
  (csemT: forall i:nat, CoreSemantics (Genv.t (fT i) (vT i)) (cT i) mem (dT i)) (** a set of core semantics *)
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext) (** extension signature *)
  (handled: list AST.external_function). (** functions handled by this extension *)

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T)
  (genv_mapS: forall i:nat, Genv.t (fS i) (vS i))
  (genv_mapT: forall i:nat, Genv.t (fT i) (vT i)).
 
 Variable (E_S: Extension.Sig (fun i => Genv.t (fS i) (vS i)) cS dS Zint esemS csemS
                  csig esig handled).
 Variable (E_T: Extension.Sig (fun i => Genv.t (fT i) (vT i)) cT dT Zint esemT csemT
                  csig esig handled).

 Variable entry_points: list (val*val*signature).
 Variable core_data: forall i: nat, Type.
 Variable match_state: forall i: nat, 
   core_data i -> meminj -> cS i -> mem -> cT i -> mem -> Prop.
 Implicit Arguments match_state [].

 Notation PROJ_CORE := (Extension.proj_core).
 Infix "\o" := (Extension.zmult) (at level 66, left associativity). 
 Notation ACTIVE := (Extension.active).
 Notation active_proj_core := (Extension.active_proj_core).
 Notation notat_external_handled := (Extension.notat_external_handled).
 Notation at_external_not_handled := (Extension.at_external_not_handled).
 Notation ext_upd_at_external := (Extension.ext_upd_at_external).

 Import Sim_inj_exposed.

 Record Sig: Type := Make {
   core_datas: Type;
   core_ords: core_datas -> core_datas -> Prop;
   match_states: core_datas -> meminj -> xS -> mem -> xT -> mem -> Prop;
   _ : Forward_simulation_inject D_S D_T esemS esemT ge_S ge_T 
          entry_points core_datas match_states core_ords
 }.

End CompilableExtension. End CompilableExtension.

Module EXTENSION_COMPILABILITY. Section EXTENSION_COMPILABILITY.
 Variables
  (F_S V_S F_T V_T: Type) (** global environments *)
  (D_S D_T: Type) (** source and target extension initialization data *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: nat -> Type) (** global environments of core semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: nat -> Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: CoreSemantics (Genv.t F_S V_S) xS mem D_S) (** extended source semantics *)
  (esemT: CoreSemantics (Genv.t F_T V_T) xT mem D_T) (** extended target semantics *)
  (csemS: forall i:nat, CoreSemantics (Genv.t (fS i) (vS i)) (cS i) mem (dS i)) (** a set of core semantics *)
  (csemT: forall i:nat, CoreSemantics (Genv.t (fT i) (vT i)) (cT i) mem (dT i)) (** a set of core semantics *)
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext) (** extension signature *)
  (handled: list AST.external_function) (** functions handled by this extension *)
  (threads_max: nat).  

 Variables 
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T)
  (genv_mapS: forall i:nat, Genv.t (fS i) (vS i))
  (genv_mapT: forall i:nat, Genv.t (fT i) (vT i)).
 
 Variable (E_S: Extension.Sig (fun i => Genv.t (fS i) (vS i)) cS dS Zint esemS csemS
                  csig esig handled).
 Variable (E_T: Extension.Sig (fun i => Genv.t (fT i) (vT i)) cT dT Zint esemT csemT
                  csig esig handled).

 Variable entry_points: list (val*val*signature).
 Variable core_data: forall i: nat, Type.
 Variable match_state: forall i: nat, 
   core_data i -> meminj -> cS i -> mem -> cT i -> mem -> Prop.
 Variable core_ord: forall i: nat, core_data i -> core_data i -> Prop.
 Implicit Arguments match_state [].

 Import Sim_inj_exposed.
 Import Extension.

 Definition core_datas := forall i:nat, core_data i.

 Variable (R: meminj -> xS -> mem -> xT -> mem -> Prop).

 Definition match_states (cd: core_datas) (j: meminj) (s1: xS) m1 (s2: xT) m2 :=
   R j s1 m1 s2 m2 /\ active E_S s1=active E_T s2 /\
   forall i c1, proj_core E_S i s1 = Some c1 -> 
     exists c2, proj_core E_T i s2 = Some c2 /\ 
       match_state i (cd i) j c1 m1 c2 m2.

 Record Sig: Type := Make {
   _ : (forall i: nat, RelyGuaranteeSimulation.Sig (csemS i) (csemT i) 
         (genv_mapS i) (match_state i)) -> 
       genvs_domain_eq ge_S ge_T -> 
       (forall i: nat, genvs_domain_eq ge_S (genv_mapS i)) -> 
       (forall i: nat, genvs_domain_eq ge_T (genv_mapT i)) -> 
       core_compatible ge_S genv_mapS E_S -> 
       core_compatible ge_T genv_mapT E_T -> 
       (forall i:nat, Forward_simulation_inject (dS i) (dT i) (csemS i) (csemT i) 
         (genv_mapS i) (genv_mapT i) entry_points 
         (core_data i) (@match_state i) (@core_ord i)) -> 
       CompilabilityInvariant.Sig fS fT vS vT threads_max ge_S ge_T 
         genv_mapS genv_mapT E_S E_T entry_points core_data match_state core_ord R -> 
       CompilableExtension.Sig esemS esemT ge_S ge_T entry_points
 }.

End EXTENSION_COMPILABILITY. End EXTENSION_COMPILABILITY. 
