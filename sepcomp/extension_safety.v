Require Import ListSet.

Require Import sepcomp.extspec.
Require Import sepcomp.Address.
Require Import sepcomp.core_semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.extension.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.rg_forward_simulations.

Require Import AST. (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import Integers.

Set Implicit Arguments.

(** * Safe Extensions *)

Section SafeExtension. Variables
 (M: Type) (** memories *)
 (Z: Type) (** external states *)
 (Zint: Type) (** portion of Z implemented by extension *)
 (Zext: Type) (** portion of Z external to extension *)
 (G: Type) (** global environments of extended semantics *)
(* (D: Type) (** extension initialization data *)*)
 (xT: Type) (** corestates of extended semantics *)
 (esem: CoreSemantics G xT M (*D*)) (** extended semantics *)
 (esig: ef_ext_spec M Zext) (** extension signature *)
 (gT: nat -> Type) (** global environments of core semantics *)
 (*(dT: nat -> Type) (** initialization data *)*)
 (cT: nat -> Type) (** corestates of core semantics *)
 (csem: forall i:nat, CoreSemantics (gT i) (cT i) M (*(dT i)*)) (** a set of core semantics *)
 (csig: ef_ext_spec M Z). (** client signature *)

 Variables (ge: G) (genv_map : forall i:nat, gT i).

 Import Extension.

(* Definition all_safe (E: Sig Z Zint Zext esem esig gT dT cT csem csig)
                     (n: nat) (z: Z) (w: xT) (m: M) :=
  forall i c, proj_core E i w = Some c -> 
   (i = Extension.active E w -> safeN (csem i) csig (genv_map i) n z c m) /\
   (i <> Extension.active E w -> 
     exists z0, exists m0, exists ef, exists sig, exists args, 
      at_external (csem i) c = Some (ef, sig, args) /\
      safeN (csem i) csig (genv_map i) n z0 c m0).*)

 Definition all_safe (E: Sig Z Zint Zext esem esig gT (*dT*) cT csem csig)
                     (n: nat) (z: Z) (w: xT) (m: M) :=
  forall i c, proj_core E i w = Some c -> safeN (csem i) csig (genv_map i) n z c m.

 Definition safe_extension (E: Sig Z Zint Zext esem esig gT (*dT*) cT csem csig) :=
  forall n s m z, all_safe E n (zmult E (proj_zint E s) z) s m -> 
  safeN esem (link_ext_spec (handled E) esig) ge n z s m.

End SafeExtension.

Module SafetyInvariant. Section SafetyInvariant. Variables
 (M: Type) (** memories *)
 (Z: Type) (** external states *)
 (Zint: Type) (** portion of Z implemented by extension *)
 (Zext: Type) (** portion of Z external to extension *)
 (G: Type) (** global environments of extended semantics *)
(* (D: Type) (** extension initialization data *)*)
 (xT: Type) (** corestates of extended semantics *)
 (esem: CoreSemantics G xT M (*D*)) (** extended semantics *)
 (esig: ef_ext_spec M Zext) (** extension signature *)
 (gT: nat -> Type) (** global environments of core semantics *)
(* (dT: nat -> Type) (** initialization data *)*)
 (cT: nat -> Type) (** corestates of core semantics *)
 (csem: forall i:nat, CoreSemantics (gT i) (cT i) M (*(dT i)*)) (** a set of core semantics *)
 (csig: ef_ext_spec M Z). (** client signature *)

 Variables (ge: G) (genv_map : forall i:nat, gT i).
 Variable E: Extension.Sig Z Zint Zext esem esig gT (*dT*) cT csem csig.

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
   (exists rv, halted esem s = Some rv))

 (** Safely halted threads remain halted. *)
 (halted_halted: forall s m s' m' i c rv,
   PROJ_CORE i s = Some c -> 
   halted (csem i) c = Some rv -> 
   corestep esem ge s m s' m' -> PROJ_CORE i s' = Some c)

 (** Safety of other threads is preserved when handling one step of blocked
    thread [i]. *)
 (handled_rest: forall s m s' m' c,
   PROJ_CORE (ACTIVE s) s = Some c -> 
   ((exists ef, exists sig, exists args, 
      at_external (csem (ACTIVE s)) c = Some (ef, sig, args)) \/ 
     exists rv, halted (csem (ACTIVE s)) c = Some rv) -> 
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
   (forall j (CS0: CoreSemantics (gT j) (cT j) M (*(dT j)*)) c0, ACTIVE s <> j -> 
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
(* (D: Type) (** extension initialization data *)*)
 (xT: Type) (** corestates of extended semantics *)
 (esem: CoreSemantics G xT M (*D*)) (** extended semantics *)
 (esig: ef_ext_spec M Zext) (** extension signature *)
 (gT: nat -> Type) (** global environments of core semantics *)
 (dT: nat -> Type) (** initialization data *)
 (cT: nat -> Type) (** corestates of core semantics *)
 (csem: forall i:nat, CoreSemantics (gT i) (cT i) M (*(dT i)*)) (** a set of core semantics *)
 (csig: ef_ext_spec M Z). (** client signature *)

 Variables (ge: G) (genv_map : forall i:nat, gT i).
 Variable E: Extension.Sig Z Zint Zext esem esig gT (*dT*) cT csem csig.

Import SafetyInvariant.

Record Sig := Make {_: safety_invariant ge genv_map E -> 
                       safe_extension ge genv_map E}.

End EXTENSION_SAFETY. End EXTENSION_SAFETY.
