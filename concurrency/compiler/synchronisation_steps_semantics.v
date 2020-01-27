
Require Import Omega.

Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.ExposedSimulations.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Require Import VST.concurrency.lib.tactics.
Require Import VST.concurrency.common.Compcert_lemmas.
Require Import VST.concurrency.common.permissions. Import permissions.
Require Import VST.concurrency.common.semantics. 
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.advanced_permissions.
Require Import VST.concurrency.compiler.CoreSemantics_sum.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.compiler.HybridMachine_simulation.


Require Import VST.concurrency.lib.Coqlib3.

Require Import VST.concurrency.memsem_lemmas.
Import BinNums.

Import BinInt.
Import List.
Import Integers.
Import Ptrofs.
Import Basics.
Import FunctionalExtensionality.

Require Import VST.concurrency.compiler.Clight_self_simulation.
Require Import VST.concurrency.compiler.Asm_self_simulation.
Require Import VST.concurrency.compiler.diagrams.
Require Import VST.concurrency.compiler.mem_equiv.
Require Import VST.concurrency.lib.pair.
Require Import VST.concurrency.compiler.inject_virtue.
Require Import VST.concurrency.compiler.concur_match.
Require Import VST.concurrency.lib.Coqlib3.

Set Nested Proofs Allowed.
Set Bullet Behavior "Strict Subproofs".

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_definitions.
Import bounded_maps.

Import HybridMachineSig.

Notation vone:= (Vint Int.one).
Notation vzero:= (Vint Int.zero).

Definition build_release_event addr dmap m:=
  Events.release addr (Some (build_delta_content dmap m)).
Definition build_acquire_event addr dmap m:=
  Events.acquire addr (Some (build_delta_content dmap m)).

(*TODO: Check if these guys are used/useful*)
Inductive release: val -> mem -> delta_map ->  mem -> Prop  :=
| ReleaseAngel:
    forall b ofs m dpm m' m_release
      (* change the permission to be able to lock *)
      lock_perms Hlt,
      Mem.store AST.Mint32 (@restrPermMap lock_perms m Hlt)
                b (unsigned ofs) vone = Some m_release ->
      (* return to the new, transfered permissions*)
      forall new_perms Hlt',
        (* Need to relate new_perms and dpm *)
        new_perms = computeMap (getCurPerm m) dpm ->
        m' = @restrPermMap new_perms m_release Hlt' ->
        release (Vptr b ofs) m dpm m'.
Inductive acquire: val -> mem -> delta_map ->  mem -> Prop  :=
| AcquireAngel:
    forall b ofs m dpm m' m_release
      (* change the permission to be able to lock *)
      lock_perms Hlt,
      Mem.store AST.Mint32 (@restrPermMap lock_perms m Hlt)
                b (unsigned ofs) vzero = Some m_release ->
      (* return to the new, transfered permissions*)
      forall new_perms Hlt',
        (* Need to relate new_perms and dpm 
             having them equiv is the same because,
             by lemma [restrPermMap_access_equiv],
             the restriction is the same.
         *)
        (*access_map_equiv new_perms (computeMap (getCurPerm m) dpm) ->*)
        new_perms = computeMap (getCurPerm m) dpm ->
        m' = @restrPermMap new_perms m_release Hlt' ->
        acquire (Vptr b ofs) m dpm m'.


Inductive extcall_release: Events.extcall_sem:=
| ExtCallRelease:
    forall ge m m' m'' m''' b ofs e dpm e',
      mem_interference m e m' ->
      release (Vptr b ofs) m' dpm m'' ->
      mem_interference m'' e' m''' ->
      extcall_release ge (Vptr b ofs :: nil) m
                      (Events.Event_acq_rel e dpm e' :: nil)
                      Vundef m'''.

Inductive extcall_acquire: Events.extcall_sem:=
| ExtCallAcquire:
    forall ge m m' m'' m''' b ofs e dpm e',
      mem_interference m e m' ->
      acquire (Vptr b ofs) m' dpm m'' ->
      mem_interference m'' e' m''' ->
      extcall_acquire ge (Vptr b ofs :: nil) m
                      (Events.Event_acq_rel e dpm e' :: nil)
                      Vundef m'''.

Axiom ReleaseExists:
  forall ge args m ev r m',
    Events.external_functions_sem "release" UNLOCK_SIG
                                  ge args m ev r m' =
    extcall_release ge args m ev r m'. 
Axiom AcquireExists:
  forall ge args m ev r m',
    Events.external_functions_sem "acquire" LOCK_SIG
                                  ge args m ev r m' =
    extcall_acquire ge args m ev r m'.



(*Don't return *)


Definition doesnt_return FUN:=
  forall (res : val) (ge : Senv.t) (args : list val) (m : mem) 
    (ev : Events.trace) (m' : mem),
    Events.external_call FUN ge args m ev res m' -> res = Vundef.


Lemma unlock_doesnt_return:
  doesnt_return UNLOCK.
Proof.
  intros ? * Hext_call.
  unfold Events.external_call in Hext_call.
  rewrite ReleaseExists in Hext_call.
  inversion Hext_call; reflexivity.
Qed.


(* "consecutive" *)

  (*Acquire and release are "consecutive" (i.e., allocate consecutive blocks)*)
  Definition consecutive_sem name sig:=
    forall ge arg m1 t v m2,
      Events.external_functions_sem name sig ge arg m1 t v m2 ->
      forall lev dpm lev' t',
        t = Events.Event_acq_rel lev dpm lev' :: t' ->
        consecutive (Mem.nextblock m1) (lev++lev').
  Lemma acquire_is_consec: consecutive_sem "acquire" LOCK_SIG.
  Proof. pose proof AcquireExists; intros ? **; subst.
         rewrite H in H0; inv H0.
         eapply consecutive_until_consecutive,consecutive_until_cat.
         - eapply interference_consecutive_until; eauto.
         - replace (Mem.nextblock m') with (Mem.nextblock m'').
           + eapply interference_consecutive_until; eauto.
           + inv H11. simpl. apply Mem.nextblock_store in H2; rewrite H2.
             reflexivity.
  Qed.
  Lemma release_is_consec: consecutive_sem "release" UNLOCK_SIG.
  Proof. pose proof ReleaseExists; intros ? **; subst.
         rewrite H in H0; inv H0.
         eapply consecutive_until_consecutive,consecutive_until_cat.
         - eapply interference_consecutive_until; eauto.
         - replace (Mem.nextblock m') with (Mem.nextblock m'').
           + eapply interference_consecutive_until; eauto.
           + inv H11. simpl. apply Mem.nextblock_store in H2; rewrite H2.
             reflexivity.
  Qed.