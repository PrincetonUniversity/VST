Load loadpath.
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
Require Import Memory.

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
  proj_core: forall i:nat, xT -> option (cT i); 
  proj_core_max: forall i s, i>=proj_max_cores s -> proj_core i s=None;
  active : xT -> nat; 
  active_proj_core : forall s, exists c, proj_core (active s) s=Some c;
  proj_zint: xT -> Zint; 
  proj_zext: Z -> Zext;
  zmult: Zint -> Zext -> Z;
  zmult_proj: forall zint zext, proj_zext (zmult zint zext)=zext;
 
  zint_invar_after_external: forall ef sig args ret s s',
   at_external esem s = Some (ef, sig, args) -> 
   after_external esem ret s = Some s' -> proj_zint s=proj_zint s';

  handled (ef: AST.external_function) :=
   forall (s: xT) (c: cT (active s)) sig args,
    proj_core (active s) s = Some c ->
    at_external (csem (active s)) c = Some (ef, sig, args) ->
    at_external esem s = None;

  linkable: linkable proj_zext handled csig esig;

  handled_invar: 
   forall s c s' c' ef sig args sig' args',
    proj_core (active s) s = Some c ->
    at_external (csem (active s)) c = Some (ef, sig, args) ->
    at_external esem s = None -> 
    proj_core (active s') s' = Some c' ->
    at_external (csem (active s')) c' = Some (ef, sig', args') ->
    at_external esem s' = None
 }.

End Extension. End Extension.

Implicit Arguments Extension.Sig [M G D xT].
Implicit Arguments Extension.Make [G xT cT M D Z Zint Zext].

(** Some administrative requirements on the interactions between extensions and
   inner cores. Perhaps some of these conditions could be merged with those for
   "safe" extensions. *)

Require Import Coqlib.

Section CoreCompatible. Variables 
 (Z: Type) (** external states *)
 (Zint: Type) (** portion of Z implemented by extension *)
 (Zext: Type) (** portion of Z external to extension *)
 (G: Type) (** global environments of extended semantics *)
 (D: Type) (** extension initialization data *)
 (xT: Type) (** corestates of extended semantics *)
 (esem: RelyGuaranteeSemantics G xT D) (** extended semantics *)
 (esig: ext_spec Zext) (** extension signature *)
 (gT: nat -> Type) (** global environments of core semantics *)
 (dT: nat -> Type) (** initialization data *)
 (cT: nat -> Type) (** corestates of core semantics *)
 (csem: forall i:nat, RelyGuaranteeSemantics (gT i) (cT i) (dT i)) (** a set of core semantics *)
 (csig: ext_spec Z). (** client signature *)

 Variables (ge: G) (genv_map : forall i:nat, gT i).
 Variable E: Extension.Sig Z Zint Zext esem esig gT dT cT csem csig.

 Import Extension.

 Inductive core_compatible: Type := CoreCompatible: forall
 (** Private blocks over coresteps *)
 (private_corestep: forall s c m s' c' m',
   proj_core E (active E s) s = Some c -> 
   corestep (csem (active E s)) (genv_map (active E s)) c m c' m' -> 
   corestep esem ge s m s' m' -> 
   forall b: block, b >= Mem.nextblock m -> 
     (private_block esem s' b <-> private_block (csem (active E s)) c' b))

 (** When the active thread is runnable, a step in the extended semantics can be
    tracked back to a corestep of the active thread. *)
 (runnable_corestep: forall s m s' m' c,
   runnable (csem (active E s)) c=true -> 
   proj_core E (active E s) s = Some c -> 
   corestep esem ge s m s' m' -> 
   exists c', corestep (csem (active E s)) (genv_map (active E s)) c m c' m' /\ 
    proj_core E (active E s) s' = Some c') 

 (** After a corestep of the active inner core, the active thread's new
    corestate is appropriately injected into the extended state. Note that 
    this condition typically imposes determinism on the inner core semantics. 
    We can live with this because we are in general dealing with deterministic 
    semantics.  To weaken the determinism condition, one could make proj_core 
    a relation, or equivalently, have proj_core project a /set/ of corestates; 
    but at the current stage, the conveniences of proj_core-as-function appear to 
    outweigh the disadvantages. *)
 (corestep_pres: forall s (c: cT (active E s)) m c' s' m',
   proj_core E (active E s) s = Some c -> 
   corestep (csem (active E s)) (genv_map (active E s)) c m c' m' -> 
   corestep esem ge s m s' m' -> 
   active E s = active E s' /\ 
   proj_core E (active E s) s' = Some c')

 (** A corestep of the currently active core forces a corestep of the 
    extended semantics *)
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

 (** The active core id doesn't change along active coresteps. *)
 (after_ext_pres: forall s (c: cT (active E s)) c' s' retv,
   proj_core E (active E s) s = Some c -> 
   after_external (csem (active E s)) retv c = Some c' -> 
   after_external esem retv s = Some s' -> 
   active E s=active E s')

 (** Extension states can be updated to match after_external on the 
    active core. *)
 (after_ext_prog: forall s (c: cT (active E s)) c' retv,
   proj_core E (active E s) s = Some c -> 
   after_external (csem (active E s)) retv c = Some c' -> 
   exists s', after_external esem retv s = Some s' /\
    proj_core E (active E s) s' = Some c')

 (** after_external on extension cores leaves all but the active corestate
    unchanged. *)
 (after_ext_others: forall s s' retv,
   after_external esem retv s = Some s' -> 
   forall j, (active E s)<>j -> 
    proj_core E j s = proj_core E j s')

 (*Hypothesis repeated from extension signature to get around a bug in [Program]*)
 (at_extern_call: forall s ef sig args,
   at_external esem s = Some (ef, sig, args) -> 
   exists c, proj_core E (active E s) s = Some c /\
    at_external (csem (active E s)) c = Some (ef, sig, args)),
 core_compatible.

End CoreCompatible.

