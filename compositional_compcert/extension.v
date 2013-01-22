Load loadpath.
Require Import ListSet.

Require Import compositional_compcert.extspec.
Require Import compositional_compcert.Address.
Require Import compositional_compcert.core_semantics.
Require Import compositional_compcert.step_lemmas.
Require Import compositional_compcert.forward_simulations.
Require Import compositional_compcert.rg_forward_simulations.

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

(** * Safe Extensions *)

Section SafeExtension. Variables
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

 Variables (ge: G) (genv_map : forall i:nat, gT i).

 Import Extension.

 Definition all_safe (E: Sig Z Zint Zext esem esig gT dT cT csem csig)
   (n: nat) (z: Z) (w: xT) (m: M) :=
  forall i c, proj_core E i w = Some c -> 
  safeN (csem i) csig (genv_map i) n z c m.

 Definition safe_extension (E: Sig Z Zint Zext esem esig gT dT cT csem csig) :=
  forall n s m z, all_safe E n (zmult E (proj_zint E s) z) s m -> 
  safeN esem (link_ext_spec (handled E) esig) ge n z s m.

End SafeExtension.

Module SafetyInvariant. Section SafetyInvariant. Variables
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

 Variables (ge: G) (genv_map : forall i:nat, gT i).
 Variable E: Extension.Sig Z Zint Zext esem esig gT dT cT csem csig.

Definition proj_zint := E.(Extension.proj_zint). 
Coercion proj_zint : xT >-> Zint.

Definition proj_zext := E.(Extension.proj_zext).
Coercion proj_zext : Z >-> Zext.

Notation ALL_SAFE := (all_safe genv_map E). 
Notation PROJ_CORE := E.(Extension.proj_core).
Notation "zint \o zext" := (E.(Extension.zmult) zint zext) 
  (at level 66, left associativity). 
Notation ACTIVE := (E.(Extension.active)).
Notation active_proj_core := E.(Extension.active_proj_core).
Notation zint_invar_after_external := E.(Extension.zint_invar_after_external).

Inductive safety_invariant: Type := SafetyInvariant: forall 
 (** Coresteps preserve the all-safety invariant. *)
 (core_pres: forall n z (s: xT) c m s' c' m', 
   ALL_SAFE (S n) (s \o z) s m -> 
   PROJ_CORE (ACTIVE s) s = Some c -> 
   corestep (csem (ACTIVE s)) (genv_map (ACTIVE s)) c m c' m' -> 
   corestep esem ge s m s' m' -> 
   ALL_SAFE n (s' \o z) s' m')

 (** Corestates satisfying the invariant can corestep. *)
 (core_prog: forall n z s m (c: cT (ACTIVE s)),
   ALL_SAFE (S n) z s m -> 
   PROJ_CORE (ACTIVE s) s = Some c -> 
   runnable (csem (ACTIVE s)) c=true -> 
   exists c', exists s', exists m', 
    corestep (csem (ACTIVE s)) (genv_map (ACTIVE s)) c m c' m' /\ 
    corestep esem ge s m s' m' /\
    PROJ_CORE (ACTIVE s) s' = Some c')

 (** "Handled" steps respect function specifications. *)
 (handled_pres: forall s z m (c: cT (ACTIVE s)) s' m' 
     (c': cT (ACTIVE s)) ef sig args P Q x, 
  let i := ACTIVE s in PROJ_CORE i s = Some c -> 
   at_external (csem i) c = Some (ef, sig, args) -> 
   Extension.handled E ef -> 
   spec_of ef csig = (P, Q) -> 
   P x (sig_args sig) args (s \o z) m -> 
   corestep esem ge s m s' m' -> 
   PROJ_CORE i s' = Some c' -> 
    ((at_external (csem i) c' = Some (ef, sig, args) /\ 
      P x (sig_args sig) args (s' \o z) m' /\ i <> ACTIVE s') \/
    (exists ret, after_external (csem i) ret c = Some c' /\ 
      Q x (sig_res sig) ret (s' \o z) m')))

 (** "Handled" states satisfying the invariant can step or are safely halted;
    core states that remain "at_external" over handled steps are unchanged. *)
 (handled_prog: forall n (z: Zext) (s: xT) m c,
   ALL_SAFE (S n) (s \o z) s m -> 
   PROJ_CORE (ACTIVE s) s = Some c -> 
   runnable (csem (ACTIVE s)) c=false -> 
   at_external esem s = None -> 
   (exists s', exists m', corestep esem ge s m s' m' /\ 
     forall i c, PROJ_CORE i s = Some c -> 
       exists c', PROJ_CORE i s' = Some c' /\
        (forall ef args ef' args', 
          at_external (csem i) c = Some (ef, args) -> 
          at_external (csem i) c' = Some (ef', args') -> c=c')) \/
   (exists rv, safely_halted esem s = Some rv))

 (** Safely halted threads remain halted. *)
 (safely_halted_halted: forall s m s' m' i c rv,
   PROJ_CORE i s = Some c -> 
   safely_halted (csem i) c = Some rv -> 
   corestep esem ge s m s' m' -> PROJ_CORE i s' = Some c)

 (** Safety of other threads is preserved when handling one step of blocked
    thread [i]. *)
 (handled_rest: forall s m s' m' c,
   PROJ_CORE (ACTIVE s) s = Some c -> 
   ((exists ef, exists sig, exists args, 
      at_external (csem (ACTIVE s)) c = Some (ef, sig, args)) \/ 
     exists rv, safely_halted (csem (ACTIVE s)) c = Some rv) -> 
   at_external esem s = None -> 
   corestep esem ge s m s' m' -> 
   (forall j c0, ACTIVE s <> j ->  
    (PROJ_CORE j s' = Some c0 -> PROJ_CORE j s = Some c0) /\
    (forall n z z', PROJ_CORE j s = Some c0 -> 
      safeN (csem j) csig (genv_map j) (S n) (s \o z) c0 m -> 
      safeN (csem j) csig (genv_map j) n (s' \o z') c0 m')))

 (** If the extended machine is at external, then the active thread is at
    external (an extension only implements external functions, it doesn't
    introduce them). *)
 (at_extern_call: forall s ef sig args,
   at_external esem s = Some (ef, sig, args) -> 
   exists c, PROJ_CORE (ACTIVE s) s = Some c /\
    at_external (csem (ACTIVE s)) c = Some (ef, sig, args))

 (** Inject the results of an external call into the extended machine state. *)
 (at_extern_ret: forall z s (c: cT (ACTIVE s)) m z' m' tys args ty ret c' ef sig x 
    (P: ext_spec_type esig ef -> list typ -> list val -> Zext -> M -> Prop) 
    (Q: ext_spec_type esig ef -> option typ -> option val -> Zext -> M -> Prop),
   PROJ_CORE (ACTIVE s) s = Some c -> 
   at_external esem s = Some (ef, sig, args) -> 
   spec_of ef esig = (P, Q) -> 
   P x tys args (s \o z) m -> Q x ty ret z' m' -> 
   after_external (csem (ACTIVE s)) ret c = Some c' -> 
   exists s': xT, 
    z' = s' \o z' /\
    after_external esem ret s = Some s' /\ 
    PROJ_CORE (ACTIVE s) s' = Some c')

 (** Safety of other threads is preserved when returning from an external 
    function call. *)
 (at_extern_rest: forall z s (c: cT (ACTIVE s)) m z' s' m' tys args ty ret c' ef x sig
    (P: ext_spec_type esig ef -> list typ -> list val -> Zext -> M -> Prop) 
    (Q: ext_spec_type esig ef -> option typ -> option val -> Zext -> M -> Prop),
   PROJ_CORE (ACTIVE s) s = Some c -> 
   at_external esem s = Some (ef, sig, args) -> 
   spec_of ef esig = (P, Q) -> 
   P x tys args (s \o z) m -> Q x ty ret z' m' -> 
   after_external (csem (ACTIVE s)) ret c = Some c' -> 
   after_external esem ret s = Some s' -> 
   PROJ_CORE (ACTIVE s) s' = Some c' ->  
   (forall j (CS0: CoreSemantics (gT j) (cT j) M (dT j)) c0, ACTIVE s <> j -> 
    (PROJ_CORE j s' = Some c0 -> PROJ_CORE j s = Some c0) /\
    (forall ge n, PROJ_CORE j s = Some c0 -> 
      safeN CS0 csig ge (S n) (s \o z) c0 m -> 
      safeN CS0 csig ge n (s' \o z') c0 m'))),
 safety_invariant.

End SafetyInvariant. End SafetyInvariant.

Module EXTENSION_SAFETY. Section EXTENSION_SAFETY. Variables
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

 Variables (ge: G) (genv_map : forall i:nat, gT i).
 Variable E: Extension.Sig Z Zint Zext esem esig gT dT cT csem csig.

Import SafetyInvariant.

Record Sig := Make {_: safety_invariant ge genv_map E -> 
                       safe_extension ge genv_map E}.

End EXTENSION_SAFETY. End EXTENSION_SAFETY.

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

 Variables (ge: G) (genv_map : forall i:nat, gT i).
 Variable E: Extension.Sig Z Zint Zext esem esig gT dT cT csem csig.

Import Extension.

Inductive core_compatible: Type := CoreCompatible: forall
 (** When the active thread is runnable, a step in the extended semantics can be
    tracked back to a corestep of the active thread. *)
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

 (** A corestep of the currently active core forces a corestep of the extended
    semantics*)
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

 (** Extension states can be updated to match after_external on the active
    core. *)
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

 (** Hypothesis repeated from extension signature to get around a bug in
 [Program]. *)
 (at_extern_call: forall s ef sig args,
   at_external esem s = Some (ef, sig, args) -> 
   exists c, proj_core E (active E s) s = Some c /\
    at_external (csem (active E s)) c = Some (ef, sig, args)),
 core_compatible.

End CoreCompatible.

