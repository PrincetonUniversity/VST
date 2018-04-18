Require Import compcert.common.Memory.


Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.HybridMachineSig.
Require Import VST.concurrency.semantics.
Require Import VST.concurrency.juicy_machine. Import Concur.
Require Import VST.concurrency.HybridMachine. Import Concur.
(*Require Import VST.concurrency.HybridMachine_lemmas. *)
Require Import VST.concurrency.lksize.
Require Import VST.concurrency.permissions.

(*Semantics*)
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clightnew_coop.
Require Import VST.sepcomp.event_semantics.

Section ClightSEM.
  Definition F: Type := fundef.
  Definition V: Type := type.
  Definition G := genv.
  Definition C := corestate.
  Definition getEnv (g:G): Genv.t F V := genv_genv g.
  (* We might want to define this properly or
     factor the machines so we don't need events here. *)

  Class ClightSEM := { CLN_evsem :> @EvSem G C;
    CLN_msem : msem CLN_evsem = CLN_memsem;
    Sem := CLN_evsem;
    step_decay: forall g c m tr c' m',
      event_semantics.ev_step (Sem) g c m tr c' m' ->
      decay m m';
    initial_core_nomem: forall n ge m v vl q om,
      initial_core Sem n ge m v vl = Some (q, om) -> om=None;
    initial_core_mem_congr: forall n ge m m' v vl,
      initial_core Sem n ge m v vl = initial_core Sem n ge m' v vl;
    at_external_SEM_eq:
     forall ge c m, at_external Sem ge c m =
      match c with
      | State _ _ _ => None
      | ExtCall ef args _ _ _ _ => Some (ef, args)
      end }.

  Instance ClightSem {CSEM : ClightSEM} : Semantics := { semG := G; semC := C; semSem := CLN_evsem }.

End ClightSEM.
