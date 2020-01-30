
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

(*Auxiliary definitions*)
Definition empty_dmap:delta_map:= PTree.Leaf.
Lemma get_empty_dmap:
  forall b ofs, EventsAux.dmap_get empty_dmap b ofs = None.
Proof.
  intros. unfold EventsAux.dmap_get, empty_dmap, "!!"; simpl.
  rewrite PTree.gleaf; auto.
Qed.
Lemma inject_delta_map_empty:
  forall mu, EventsAux.inject_delta_map mu empty_dmap empty_dmap.
Proof.
  econstructor.
  - intros. rewrite get_empty_dmap in H; congruence.
  - intros. rewrite get_empty_dmap in H; congruence.
Qed.


(*sync steps semantics *)

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

Inductive mklock: val -> mem ->  mem -> Prop  :=
| MkLockSem:
    forall b ofs m new_perm m' m'' Hlt ,
      lock_update_mem_strict b (unsigned ofs) m m' vzero ->
      new_perm = 
      setPermBlock (Some Nonempty) b (unsigned ofs)
                   (getCurPerm m') LKSIZE_nat ->
      m'' = @restrPermMap new_perm m' Hlt ->
      mklock (Vptr b ofs) m m''.

Inductive freelock: val -> mem ->  mem -> Prop  :=
| FreeLockSem:
    forall b ofs m new_perm m' m'' Hlt,
      lock_update_mem_strict b (unsigned ofs) m m' vone ->
      new_perm = 
      setPermBlock (Some Nonempty) b (unsigned ofs)
                   (getCurPerm m') LKSIZE_nat ->
      m'' = @restrPermMap new_perm m' Hlt ->
      freelock (Vptr b ofs) m m''.


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
Inductive extcall_mklock: Events.extcall_sem:=
| ExtCallMklock:
    forall ge m m' m'' m''' b ofs e e',
      mem_interference m e m' ->
      mklock (Vptr b ofs) m' m'' ->
      mem_interference m'' e' m''' ->
      extcall_mklock ge (Vptr b ofs :: nil) m
                     (Events.Event_acq_rel e empty_dmap e' :: nil)
                     Vundef m'''.

Inductive extcall_freelock: Events.extcall_sem:=
| ExtCallFreelock:
    forall ge m m' m'' m''' b ofs e e',
      mem_interference m e m' ->
      freelock (Vptr b ofs) m' m'' ->
      mem_interference m'' e' m''' ->
      extcall_freelock ge (Vptr b ofs :: nil) m
                       (Events.Event_acq_rel e empty_dmap e' :: nil)
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
Axiom MakeLockExists:
  forall ge args m ev r m',
    Events.external_functions_sem "makelock" UNLOCK_SIG
                                  ge args m ev r m' =
    extcall_mklock ge args m ev r m'. 
Axiom FreeLockExists:
  forall ge args m ev r m',
    Events.external_functions_sem "freelock" UNLOCK_SIG
                                  ge args m ev r m' =
    extcall_freelock ge args m ev r m'.



(*Don't return *)


Definition doesnt_return FUN:=
  forall (res : val) (ge : Senv.t) (args : list val) (m : mem) 
    (ev : Events.trace) (m' : mem),
    Events.external_call FUN ge args m ev res m' -> res = Vundef.


Lemma unlock_doesnt_return: doesnt_return UNLOCK.
Proof.
  intros ? * Hext_call.
  unfold Events.external_call in Hext_call.
  rewrite ReleaseExists in Hext_call.
  inversion Hext_call; reflexivity.
Qed.

Lemma mklock_doesnt_return: doesnt_return MKLOCK.
Proof. 
  intros ? * Hext_call.
  unfold Events.external_call in Hext_call.
  rewrite MakeLockExists in Hext_call.
  inversion Hext_call; reflexivity.
Qed.

Lemma freelock_doesnt_return: doesnt_return FREE_LOCK.
Proof. 
  intros ? * Hext_call.
  unfold Events.external_call in Hext_call.
  rewrite FreeLockExists in Hext_call.
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


Lemma makelock_is_consec: consecutive_sem "makelock" UNLOCK_SIG.
Proof. pose proof MakeLockExists; intros ? **; subst.
       rewrite H in H0; inv H0.
       eapply consecutive_until_consecutive,consecutive_until_cat.
       - eapply interference_consecutive_until; eauto.
       - replace (Mem.nextblock m') with (Mem.nextblock m'').
         + eapply interference_consecutive_until; eauto.
         + inv H11. inv H2. simpl.
           apply Mem.nextblock_store in Hstore; rewrite Hstore.
           reflexivity.
Qed.


Lemma freelock_is_consec: consecutive_sem "freelock" UNLOCK_SIG.
Proof. pose proof FreeLockExists; intros ? **; subst.
       rewrite H in H0; inv H0.
       eapply consecutive_until_consecutive,consecutive_until_cat.
       - eapply interference_consecutive_until; eauto.
       - replace (Mem.nextblock m') with (Mem.nextblock m'').
         + eapply interference_consecutive_until; eauto.
         + inv H11. inv H2. simpl.
           apply Mem.nextblock_store in Hstore; rewrite Hstore.
           reflexivity.
Qed.