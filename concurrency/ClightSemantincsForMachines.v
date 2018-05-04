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

  (* This should be a version of CLN_memsem annotated with memory events. *)
  Program Definition CLN_evsem ge : @EvSem C := {| msem := CLN_memsem ge |}.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

  Lemma CLN_msem : forall ge, msem (CLN_evsem ge) = CLN_memsem ge.
  Proof. auto. Qed.

  Notation Sem := CLN_evsem.
  Lemma step_decay: forall g c m tr c' m',
      event_semantics.ev_step (Sem g) c m tr c' m' ->
      decay m m'.
  Admitted.

  Lemma initial_core_mem_congr: forall n ge m m' q v vl,
    initial_core (Sem ge) n m q v vl <-> initial_core (Sem ge) n m' q v vl.
  Proof. reflexivity. Qed.

  Lemma at_external_SEM_eq:
     forall ge c m, at_external (Sem ge) c m =
      match c with
      | State _ _ _ => None
      | ExtCall ef args _ _ _ _ => Some (ef, ef_sig ef, args)
      end.
  Proof. auto. Qed.

  Instance ClightSem ge : Semantics := { semG := G; semC := C; semSem := CLN_evsem ge; the_ge := ge }.

End ClightSEM.
