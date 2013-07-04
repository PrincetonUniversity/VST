Load loadpath.
Require Import ListSet.

Require Import sepcomp.extspec.
Require Import sepcomp.Address.
Require Import sepcomp.core_semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.forward_simulations.

Require Import compcert.common.AST. (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.lib.Integers.

Set Implicit Arguments.

Definition runnable {G C M} (csem: CoreSemantics G C M) (c: C) :=
  match at_external csem c, halted csem c with 
  | None, None => true
  | _, _ => false
  end.

Module Extension. Section Extension. Variables
 (M: Type) (** memories *)
 (Z: Type) (** external states *)
 (Zint: Type) (** portion of Z implemented by extension *)
 (Zext: Type) (** portion of Z external to extension *)
 (G: Type) (** global environments of extended semantics *)
 (xT: Type) (** corestates of extended semantics *)
 (esem: CoreSemantics G xT M (*D*)) (** extended semantics *)
 (esig: ef_ext_spec M Zext) (** extension signature *)
 (gT: Type) (** global environment of core semantics *)
 (cT: Type) (** corestate of core semantics *)
 (csem: CoreSemantics gT cT M) (** core semantics *)
 (csig: ef_ext_spec M Z). (** client signature *)

 Record Sig := Make {
  proj_core: xT -> cT;
  proj_zint: xT -> Zint; 
  proj_zext: Z -> Zext;
  zmult: Zint -> Zext -> Z;
  zmult_proj: forall zint zext, proj_zext (zmult zint zext)=zext;
 
  zint_invar_after_external: forall ef sig args ret s s',
   at_external esem s = Some (ef, sig, args) -> 
   after_external esem ret s = Some s' -> proj_zint s=proj_zint s';

  handled (ef: AST.external_function) :=
   forall (s: xT) (c: cT) sig args,
    let c := proj_core s in
    at_external csem c = Some (ef, sig, args) ->
    at_external esem s = None;

(*  linkable: linkable proj_zext handled csig esig;*)

  handled_invar: 
   forall s c s' c' ef sig args sig' args',
    proj_core s = c -> 
    at_external csem c = Some (ef, sig, args) ->
    at_external esem s = None -> 
    proj_core s' = c' ->
    at_external csem c' = Some (ef, sig', args') ->
    at_external esem s' = None
 }.

End Extension. End Extension.

Implicit Arguments Extension.Sig [M G xT].
Implicit Arguments Extension.Make [G xT cT M Z Zint Zext].

(** Some administrative requirements on the interactions between extensions and
   inner cores. Perhaps some of these conditions could be merged with those for
   "safe" extensions. *)

Section CoreCompatible. Variables 
 (M: Type) (** memories *)
 (Z: Type) (** external states *)
 (Zint: Type) (** portion of Z implemented by extension *)
 (Zext: Type) (** portion of Z external to extension *)
 (G: Type) (** global environments of extended semantics *)
 (xT: Type) (** corestates of extended semantics *)
 (esem: CoreSemantics G xT M (*D*)) (** extended semantics *)
 (esig: ef_ext_spec M Zext) (** extension signature *)
 (gT: Type) (** global environments of core semantics *)
 (dT: Type) (** initialization data *)
 (cT: Type) (** corestates of core semantics *)
 (csem: CoreSemantics gT cT M) (** core semantics *)
 (csig: ef_ext_spec M Z). (** client signature *)

 Variables (ge: G) (geT: gT).
 Variable E: Extension.Sig Z Zint Zext esem gT cT csem.

 Import Extension.

 Inductive core_compatible: Type := CoreCompatible: forall
 (** When the active thread is runnable, a step in the extended semantics can be
    tracked back to a corestep of the active thread. *)
 (runnable_corestep: forall s m s' m',
   let c := proj_core E s in
   runnable csem c=true -> 
   corestep esem ge s m s' m' -> 
   corestep csem geT c m (proj_core E s') m')

 (** After a corestep of the active inner core, the active thread's new
    corestate is appropriately injected into the extended state. Note that 
    this condition typically imposes determinism on the inner core semantics. 
    We can live with this because we are in general dealing with deterministic 
    semantics.  To weaken the determinism condition, one could make proj_core 
    a relation, or equivalently, have proj_core project a /set/ of corestates; 
    but at the current stage, the conveniences of proj_core-as-function appear to 
    outweigh the disadvantages. *)
 (corestep_pres: forall s m c' s' m',
   let c := proj_core E s in
   corestep csem geT c m c' m' -> 
   corestep esem ge s m s' m' -> 
   proj_core E s' = c')

 (** A corestep of the currently active core forces a corestep of the 
    extended semantics *)
 (corestep_prog: forall s m c' m',
   let c := proj_core E s in
   corestep csem geT c m c' m' -> 
   exists s', corestep esem ge s m s' m')

 (at_external_proj: forall s ef sig args, 
   at_external esem s = Some (ef, sig, args) ->
   at_external csem (proj_core E s) = Some (ef, sig, args))

 (halted_proj: forall s, halted esem s = halted csem (proj_core E s))

 (** Extension states can be updated to match after_external on the 
    active core. *)
 (after_ext_prog: forall s c' retv,
   let c := proj_core E s in 
   after_external csem retv c = Some c' -> 
   exists s', after_external esem retv s = Some s' /\
    proj_core E s' = c'),
 core_compatible.

End CoreCompatible.

