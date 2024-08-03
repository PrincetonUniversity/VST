(** * Bare (no permissions) Interleaving Machine *)

Require Import compcert.lib.Axioms.

Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.concurrency.common.pos.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap. (*The finite maps*)
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import Coq.Program.Program.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import VST.concurrency.common.threads_lemmas.
Require Import Coq.ZArith.ZArith.
Require Import VST.concurrency.common.threadPool.

Module BareMachine.

  Import event_semantics Events ThreadPool.

  Section BareMachine.
    (** Assume some threadwise semantics *)
    Context {Sem: Semantics}.

    (** This machine has no permissions or other logical info *)
    Instance resources : Resources :=
      {| res := unit; lock_info := unit |}.

    Notation C:= (@semC Sem).
    Notation G:= (@semG Sem).
    Notation semSem:= (@semSem Sem).

    Existing Instance OrdinalPool.OrdinalThreadPool.
    
    (** Memories*)
    Definition richMem: Type := mem.
    Definition dryMem: richMem -> mem:= id.
    
    Notation thread_pool := (@t resources Sem).

    (** The state respects the memory*)
    Definition mem_compatible (tp : thread_pool) (m : mem) : Prop := True.
    Definition invariant (tp : thread_pool) := True.

    (** Steps*)
    Inductive thread_step {tid0 tp m} (cnt: containsThread tp tid0)
              (Hcompatible: mem_compatible tp m) :
      thread_pool -> mem -> seq mem_event -> Prop :=
    | step_thread :
        forall (tp':thread_pool) c m' (c' : C) ev
          (Hcode: getThreadC cnt = Krun c)
          (Hcorestep: ev_step semSem c m ev c' m')
          (Htp': tp' = updThreadC cnt (Krun c')),
          thread_step cnt Hcompatible tp' m' ev.

    Inductive ext_step {tid0 tp m} (*Can we remove genv from here?*)
              (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
      thread_pool -> mem -> sync_event -> Prop :=
    | step_acquire :
        forall (tp' : thread_pool) c m' b ofs
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external semSem c m =
                         Some (LOCK, Vptr b ofs::nil))
          (Hload: Mem.load Mint32 m b (Ptrofs.intval ofs) = Some (Vint Int.one))
          (Hstore: Mem.store Mint32 m b (Ptrofs.intval ofs) (Vint Int.zero) = Some m')
          (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
          ext_step cnt0 Hcompat tp' m' (acquire (b, Ptrofs.intval ofs) None)

    | step_release :
        forall (tp':thread_pool) c m' b ofs
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external semSem c m =
                         Some (UNLOCK, Vptr b ofs::nil))
          (Hstore: Mem.store Mint32 m b (Ptrofs.intval ofs) (Vint Int.one) = Some m')
          (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
          ext_step cnt0 Hcompat tp' m' (release (b, Ptrofs.intval ofs) None)

    | step_create :
        forall (tp_upd tp':thread_pool) c b ofs arg
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external semSem c m =
                         Some (CREATE, Vptr b ofs::arg::nil))
          (Htp_upd: tp_upd = updThreadC cnt0 (Kresume c Vundef))
          (Htp': tp' = addThread tp_upd (Vptr b ofs) arg tt),
          ext_step cnt0 Hcompat tp' m (spawn (b, Ptrofs.intval ofs) None None)

    | step_mklock :
        forall  (tp': thread_pool) c m' b ofs
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external semSem c m =
                          Some (MKLOCK, Vptr b ofs::nil))
           (Hstore: Mem.store Mint32 m b (Ptrofs.intval ofs) (Vint Int.zero) = Some m')
           (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
          ext_step cnt0 Hcompat tp' m' (mklock (b, Ptrofs.intval ofs))

    | step_freelock :
        forall (tp' tp'': thread_pool) c b ofs
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external semSem c m =
                         Some (FREE_LOCK, Vptr b ofs::nil))
          (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
          ext_step cnt0 Hcompat  tp' m (freelock (b,Ptrofs.intval ofs))

    | step_acqfail :
        forall  c b ofs
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external semSem c m =
                          Some (LOCK, Vptr b ofs::nil))
           (Hload: Mem.load Mint32 m b (Ptrofs.intval ofs) = Some (Vint Int.zero)),
          ext_step cnt0 Hcompat tp m (failacq (b, Ptrofs.intval ofs)).

    Definition threadStep: forall {tid0 ms m},
        containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> seq mem_event -> Prop:=
      @thread_step.

    Definition syncStep (isCoarse:bool) :
      forall {tid0 ms m},
        containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> sync_event -> Prop:=
      @ext_step.

    Lemma threadStep_at_Krun:
      forall i tp m cnt cmpt tp' m' tr,
        @threadStep i tp m cnt cmpt tp' m' tr ->
        (exists q, @getThreadC _ _ _ i tp cnt = Krun q).
    Proof.
      intros.
      inversion H; subst;
        now eauto.
    Qed.

   Lemma threadStep_equal_run:
    forall i tp m cnt cmpt tp' m' tr,
      @threadStep i tp m cnt cmpt tp' m' tr ->
      forall j,
        (exists cntj q, @getThreadC _ _ _ j tp cntj = Krun q) <->
        (exists cntj' q', @getThreadC _ _ _ j tp' cntj' = Krun q').
   Proof.
     intros. split.
     - intros [cntj [ q running]].
       inversion H; subst.
        assert (cntj':=cntj).
        eapply (cntUpdateC (Krun c')) in cntj'.
        exists cntj'.
        destruct (NatTID.eq_tid_dec i j).
        + subst j; exists c'.
          rewrite gssThreadCC; reflexivity.
        + exists q.
          erewrite <- gsoThreadCC; eauto.
      - intros [cntj' [ q' running]].
        inversion H; subst.
        assert (cntj:=cntj').
        eapply cntUpdateC' with (c0:=Krun c') in cntj; eauto.
        exists cntj.
        destruct (NatTID.eq_tid_dec i j).
        + subst j; exists c.
          rewrite <- Hcode.
          f_equal.
          apply cnt_irr.
        + exists q'.
          erewrite <- gsoThreadCC in running; eauto.
   Qed.


    Lemma syncstep_equal_run:
      forall b i tp m cnt cmpt tp' m' tr,
        @syncStep b i tp m cnt cmpt tp' m' tr ->
        forall j,
          (exists cntj q, @getThreadC _ _ _ j tp cntj = Krun q) <->
          (exists cntj' q', @getThreadC _ _ _ j tp' cntj' = Krun q').
    Proof.
  intros b i tp m cnt cmpt tp' m' tr H j; split.
      - intros [cntj [ q running]].
        destruct (NatTID.eq_tid_dec i j).
        + subst j. generalize running; clear running.
          inversion H; subst;
            match goal with
            | [ H: getThreadC ?cnt = Kblocked ?c |- _ ] =>
              replace cnt with cntj in H by apply cnt_irr;
                intros HH; rewrite HH in H; inversion H
            end.
        + (*this should be easy to automate or shorten*)
          inversion H; subst;
            try (exists (cntUpdateC (Kresume c Vundef) cnt cntj),
                    q;
                    intros;
                    erewrite <- gsoThreadCC;
                    now eauto).
          * exists (cntAdd _ _ _
                      (cntUpdateC (Kresume c Vundef) _ cntj)), q.
            erewrite gsoAddCode .
            erewrite <- gsoThreadCC; eassumption.
          * do 2 eexists; eauto.
      - intros [cntj [ q running]].
        destruct (NatTID.eq_tid_dec i j).
        + subst j. generalize running; clear running;
                     inversion H; subst; intros;
          try (rewrite gssThreadCC in running;
               discriminate).
          * (*add thread*)
            assert (cntj':=cntj).
            eapply cntAdd' in cntj'; destruct cntj' as [ [HH HHH] | HH].
            ** exfalso.
              assert (Heq: getThreadC cntj = getThreadC HH)
                by (rewrite gsoAddCode; reflexivity).
              rewrite Heq in running.
              rewrite gssThreadCC in running.
              discriminate.
            ** erewrite gssAddCode in running; eauto.
               discriminate.
          * (* fail acq*)
            do 2 eexists; eauto.
        + generalize running; clear running.
          inversion H; subst;
            intros;
            try (exists (cntUpdateC' _  cnt cntj), q;
                 rewrite <- running;
                 erewrite <- gsoThreadCC; now eauto).
          * (*Add thread case*)
            assert (cntj':=cntj).
            eapply cntAdd' in cntj'; destruct cntj' as [ [HH HHH] | HH].
            ** pose proof (cntUpdateC' _ _ HH) as cntj0.
              exists cntj0, q.
              rewrite <- running.
              erewrite gsoAddCode with (cntj1 := HH).
              erewrite <- gsoThreadCC;
                now eauto.
            ** exfalso.
               erewrite gssAddCode in running; eauto.
               discriminate.
          * eauto.
            Unshelve.
            apply cntUpdateC;
              now eauto.
    Qed.

    Lemma syncstep_not_running:
      forall b i tp m cnt cmpt tp' m' tr,
        @syncStep b i tp m cnt cmpt tp' m' tr ->
        forall cntj q, ~ @getThreadC _ _ _ i tp cntj = Krun q.
    Proof.
      intros.
      inversion H;
        match goal with
        | [ H: getThreadC ?cnt = _ |- _ ] =>
          erewrite (cnt_irr _ _ _ cnt);
            rewrite H; intros AA; inversion AA
        end.
    Qed.
    
    Definition init_mach (_ : option unit) (m: mem)
               (tp:thread_pool)(m':mem)(v:val)(args:list val) : Prop :=
      exists c, initial_core semSem 0 m c m' v args /\ tp = mkPool (Krun c) tt.

    Definition install_perm tp m tid (Hcmpt: mem_compatible tp m) (Hcnt: containsThread tp tid) m' :=
      m = m'.

    Definition add_block tp m tid (Hcmpt: mem_compatible tp m) (Hcnt: containsThread tp tid) (m': mem) := tt.

    (** The signature of the Bare Machine *)
    Instance BareMachineSig: HybridMachineSig.MachineSig :=
      (HybridMachineSig.Build_MachineSig
                                       richMem
                                       dryMem
                                       mem_compatible
                                       invariant
                                       install_perm
                                       add_block
                                       (@threadStep)
                                       threadStep_at_Krun
                                       threadStep_equal_run
                                       (@syncStep)
                                       syncstep_equal_run
                                       syncstep_not_running
                                       init_mach
      ).

  End BareMachine.
  Set Printing All.
End BareMachine.

