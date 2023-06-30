(* Clight SEmantics for Machines*)

(*
  We define event semantics for 
  - Clight_new: the core semantics defined by VST
  - Clightcore: the core semantics derived from 
    CompCert's Clight
*)

Require Import compcert.common.Memory.
Require Import VST.veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

Require Import List. Import ListNotations.

(* The concurrent machinery*)
(*Require Import VST.concurrency.common.core_semantics.*)
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.common.permissions.

Import Ctypes. 
Require Import compcert.cfrontend.Clight.
Import Cop.
Arguments sizeof {env} !t / .

(*Semantics*)
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop. 
Require Import VST.sepcomp.event_semantics.
Require Import VST.veric.Clight_evsem.

  Lemma at_external_SEM_eq:
     forall ge c m, semantics.at_external (CLC_evsem ge) c m =
     match c with
     | Callstate (External ef _ _ _) args _ => 
         if ef_inline ef then None else Some (ef, args)
     | _ => None
   end.
  Proof. auto. Qed.

  #[export] Instance ClightSem ge : Semantics :=
    { semG := G; semC := C; semSem := CLC_evsem ge; the_ge := ge }.
