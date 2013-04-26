Require Import ListSet.

Require Import sepcomp.extspec.
Require Import sepcomp.Address.
Require Import sepcomp.core_semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.rg_forward_simulations.

Require Import AST. (*for typ*)
Require Import Values. (*for val*)
Require Import Integers.

Set Implicit Arguments.

(** * Extensions *)

Module Extension. Section Extension. Variables
 (M: Type) (** memories *)
 (Z: Type) (** external states *)
 (Zint: Type) (** portion of Z implemented by extension *)
 (Zext: Type) (** portion of Z external to extension *)
 (G: Type) (** global environments of extended semantics *)
 (D: Type) (** extension initialization data *)
 (xT: Type) (** corestates of extended semantics *)
 (esem: CoreSemantics G xT M D) (** extended semantics *)
 (esig: ef_ext_spec M Zext) (** extension signature *)
 (gT: nat -> Type) (** global environments of core semantics *)
 (dT: nat -> Type) (** initialization data *)
 (cT: nat -> Type) (** corestates of core semantics *)
 (csem: forall i:nat, CoreSemantics (gT i) (cT i) M (dT i)) (** a set of core semantics *)
 (csig: ef_ext_spec M Z). (** client signature *)

 Record Sig := Make {
  proj_max_cores: xT -> nat;
  proj_core: forall (i j:nat), xT -> option (cT j); (*i is thread_id; j is module type index*)
  proj_core_max: forall i j s, i>=proj_max_cores s -> proj_core i j s=None;
  active : xT -> nat; 
  active_proj_core : forall s, exists j c, proj_core (active s) j s=Some c;
  proj_zint: xT -> Zint; 
  proj_zext: Z -> Zext;
  zmult: Zint -> Zext -> Z;
  zmult_proj: forall zint zext, proj_zext (zmult zint zext)=zext;

  proj_core_types: forall (i u u': nat) c c' s,
    proj_core i u s = Some c -> 
    proj_core i u' s = Some c' -> 
    u=u';
 
  zint_invar_after_external: forall ef sig args ret s s',
   at_external esem s = Some (ef, sig, args) -> 
   after_external esem ret s = Some s' -> proj_zint s=proj_zint s';

  handled (ef: AST.external_function) :=
   forall (s: xT) j (c: cT j) sig args,
    proj_core (active s) j s = Some c ->
    at_external (csem j) c = Some (ef, sig, args) ->
    at_external esem s = None;

  linkable: linkable proj_zext handled csig esig;

  handled_invar: 
   forall j s c s' c' ef sig args sig' args',
    proj_core (active s) j s = Some c ->
    at_external (csem j) c = Some (ef, sig, args) ->
    at_external esem s = None -> 
    proj_core (active s') j s' = Some c' ->
    at_external (csem j) c' = Some (ef, sig', args') ->
    at_external esem s' = None
 }.

End Extension. End Extension.

Implicit Arguments Extension.Sig [M G D xT].
Implicit Arguments Extension.Make [G xT cT M D Z Zint Zext].

(** Some administrative requirements on the interactions between extensions and
   inner cores. Perhaps some of these conditions could be merged with those for
   "safe" extensions. *)

Section CoreCompatible. Variables 
 (M: Type) (** memories *)
 (Z: Type) (** external states *)
 (Zint: Type) (** portion of Z implemented by extension *)
 (Zext: Type) (** portion of Z external to extension *)
 (G: Type) (** global environments of extended semantics *)
 (D: Type) (** extension initialization data *)
 (xT: Type) (** corestates of extended semantics *)
 (esem: CoreSemantics G xT M D) (** extended semantics *)
 (esig: ef_ext_spec M Zext) (** extension signature *)
 (gT: nat -> Type) (** global environments of core semantics *)
 (dT: nat -> Type) (** initialization data *)
 (cT: nat -> Type) (** corestates of core semantics *)
 (csem: forall i:nat, CoreSemantics (gT i) (cT i) M (dT i)) (** a set of core semantics *)
 (csig: ef_ext_spec M Z). (** client signature *)

 Import Extension.

 Variables (ge: G) (genv_map : forall u: nat, gT u).
 Variable E: Extension.Sig Z Zint Zext esem esig gT dT cT csem csig.

 Inductive core_compatible: Type := CoreCompatible: forall
 (** When the active thread is runnable, a step in the extended semantics can be
    tracked back to a corestep of the active thread. *)
 (runnable_corestep: forall j s m s' m' c,
   runnable (csem j) c=true -> 
   proj_core E (active E s) j s = Some c -> 
   corestep esem ge s m s' m' -> 
   exists c', corestep (csem j) (genv_map j) c m c' m' /\ 
    proj_core E (active E s) j s' = Some c') 

 (** After a corestep of the active inner core, the active thread's new
    corestate is appropriately injected into the extended state. Note that 
    this condition typically imposes determinism on the inner core semantics. 
    We can live with this because we are in general dealing with deterministic 
    semantics.  To weaken the determinism condition, one could make proj_core 
    a relation, or equivalently, have proj_core project a /set/ of corestates; 
    but at the current stage, the conveniences of proj_core-as-function appear to 
    outweigh the disadvantages. *)
 (corestep_pres: forall j s (c: cT j) m c' s' m1' m2',
   proj_core E (active E s) j s = Some c -> 
   corestep (csem j) (genv_map j) c m c' m1' -> 
   corestep esem ge s m s' m2' -> 
   active E s = active E s' /\ 
   proj_core E (active E s) j s' = Some c' /\
   m1'=m2')

 (** A corestep of the currently active core forces a corestep of the 
    extended semantics *)
 (corestep_prog: forall j s (c: cT j) m c' m',
   proj_core E (active E s) j s = Some c -> 
   corestep (csem j) (genv_map j) c m c' m' -> 
   exists s', corestep esem ge s m s' m')

 (** Other cores remain unchanged after coresteps of the active core. *)
 (corestep_others_forward: forall j s s' (c: cT j) m c' m',
   active E s=active E s' -> 
   proj_core E (active E s') j s' = Some c' -> 
   corestep (csem j) (genv_map j) c m c' m' -> 
   corestep esem ge s m s' m' -> 
   forall i u, (active E s)<>i -> proj_core E i u s = proj_core E i u s')
 (corestep_others_backward: forall j s c m s' c' m' n,
   proj_core E (active E s) j s = Some c -> 
   corestepN (csem j) (genv_map j) n c m c' m' -> 
   corestepN esem ge n s m s' m' -> 
   forall i u, (active E s)<>i -> proj_core E i u s = proj_core E i u s')

 (** The active core id doesn't change along active coresteps. *)
 (after_ext_pres: forall j s (c: cT j) c' s' retv,
   proj_core E (active E s) j s = Some c -> 
   after_external (csem j) retv c = Some c' -> 
   after_external esem retv s = Some s' -> 
   active E s=active E s')

 (** Extension states can be updated to match after_external on the 
    active core. *)
 (after_ext_prog: forall j s (c: cT j) c' retv,
   proj_core E (active E s) j s = Some c -> 
   after_external (csem j) retv c = Some c' -> 
   exists s', after_external esem retv s = Some s' /\
    proj_core E (active E s) j s' = Some c')

 (** after_external on extension cores leaves all but the active corestate
    unchanged. *)
 (after_ext_others: forall j0 s s' retv,
   after_external esem retv s = Some s' -> 
   forall j, (active E s)<>j -> 
    proj_core E j j0 s = proj_core E j j0 s')

 (*Hypothesis repeated from extension signature to get around a bug in [Program]*)
 (at_extern_call: forall s ef sig args,
   at_external esem s = Some (ef, sig, args) -> 
   exists j c, proj_core E (active E s) j s = Some c /\
    at_external (csem j) c = Some (ef, sig, args)),
 core_compatible.

End CoreCompatible.
