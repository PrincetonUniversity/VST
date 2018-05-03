(** * Bare (no permissions) Interleaving Machine *)

Require Import compcert.lib.Axioms.

Require Import VST.concurrency.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.concurrency.pos.
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.addressFiniteMap. (*The finite maps*)
Require Import VST.concurrency.pos.
Require Import VST.concurrency.lksize.
Require Import VST.concurrency.semantics.
Require Import VST.concurrency.permissions.
Require Import VST.concurrency.HybridMachineSig.
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
Require Import VST.concurrency.threads_lemmas.
Require Import Coq.ZArith.ZArith.
Require Import VST.concurrency.threadPool.

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
                         Some (LOCK, LOCK_SIG, Vptr b ofs::nil))
          (Hload: Mem.load Mint32 m b (Ptrofs.intval ofs) = Some (Vint Int.one))
          (Hstore: Mem.store Mint32 m b (Ptrofs.intval ofs) (Vint Int.zero) = Some m')
          (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
          ext_step cnt0 Hcompat tp' m' (acquire (b, Ptrofs.intval ofs) None)

    | step_release :
        forall (tp':thread_pool) c m' b ofs
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external semSem c m =
                         Some (UNLOCK, UNLOCK_SIG, Vptr b ofs::nil))
          (Hstore: Mem.store Mint32 m b (Ptrofs.intval ofs) (Vint Int.one) = Some m')
          (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
          ext_step cnt0 Hcompat tp' m' (release (b, Ptrofs.intval ofs) None)

    | step_create :
        forall (tp_upd tp':thread_pool) c b ofs arg
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external semSem c m =
                         Some (CREATE, CREATE_SIG, Vptr b ofs::arg::nil))
          (Htp_upd: tp_upd = updThreadC cnt0 (Kresume c Vundef))
          (Htp': tp' = addThread tp_upd (Vptr b ofs) arg tt),
          ext_step cnt0 Hcompat tp' m (spawn (b, Ptrofs.intval ofs) None None)

    | step_mklock :
        forall  (tp': thread_pool) c m' b ofs
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external semSem c m =
                          Some (MKLOCK, UNLOCK_SIG, Vptr b ofs::nil))
           (Hstore: Mem.store Mint32 m b (Ptrofs.intval ofs) (Vint Int.zero) = Some m')
           (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
          ext_step cnt0 Hcompat tp' m' (mklock (b, Ptrofs.intval ofs))

    | step_freelock :
        forall (tp' tp'': thread_pool) c b ofs
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external semSem c m =
                         Some (FREE_LOCK, UNLOCK_SIG, Vptr b ofs::nil))
          (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
          ext_step cnt0 Hcompat  tp' m (freelock (b,Ptrofs.intval ofs))

    | step_acqfail :
        forall  c b ofs
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external semSem c m =
                          Some (LOCK, LOCK_SIG, Vptr b ofs::nil))
           (Hload: Mem.load Mint32 m b (Ptrofs.intval ofs) = Some (Vint Int.zero)),
          ext_step cnt0 Hcompat tp m (failacq (b, Ptrofs.intval ofs)).

    Inductive threadHalted': forall {tid0 ms},
        containsThread ms tid0 -> Prop:=
    | thread_halted':
        forall tp c tid0 i
          (cnt: containsThread tp tid0)
          (*Hinv: invariant tp*)
          (Hcode: getThreadC cnt = Krun c)
          (Hcant: core_semantics.halted semSem c i),
          threadHalted' cnt.

    Definition threadStep: forall {tid0 ms m},
        containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> seq mem_event -> Prop:=
      @thread_step.

    Definition threadHalted: forall {tid0 ms},
        containsThread ms tid0 -> Prop:= @threadHalted'.

    Definition syncStep (isCoarse:bool) :
      forall {tid0 ms m},
        containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> sync_event -> Prop:=
      @ext_step.

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
    Admitted.
    (*NOTE: Admit for now, but proof is same as HybridMachine. The question is do we want this lemma to be part of the spec? *)

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
    
(*    Lemma threadStep_not_unhalts:
      forall g i tp m cnt cmpt tp' m' tr,
        @threadStep g i tp m cnt cmpt tp' m' tr ->
        forall j cnt cnt',
          (@threadHalted j tp cnt) ->
          (@threadHalted j tp' cnt') .
    Proof.
      intros; inversion H; inversion H0; subst.
      destruct (NatTID.eq_tid_dec i j).
      - subst j. simpl in Hcorestep.
        eapply ev_step_ax1 in Hcorestep.
        eapply corestep_not_halted in Hcorestep.
        replace cnt1 with cnt in Hcode0 by apply cnt_irr.
        rewrite Hcode0 in Hcode; inversion Hcode;
          subst c0.
        rewrite Hcorestep in Hcant; inversion Hcant.
      - econstructor; eauto.
        erewrite <- gsoThreadCC; eauto.
    Qed.*)

    

    Lemma syncstep_equal_halted:
      forall b i tp m cnti cmpt tp' m' tr,
        @syncStep b i tp m cnti cmpt tp' m' tr ->
        forall j cnt cnt',
          (@threadHalted j tp cnt) <->
          (@threadHalted j tp' cnt').
    Proof.
      intros; split; intros HH; inversion HH; subst;
        econstructor; subst; eauto.
      - destruct (NatTID.eq_tid_dec i j).
        + subst j.
          inversion H;
            match goal with
            | [ H: getThreadC ?cnt = Krun ?c,
                   H': getThreadC ?cnt' = Kblocked ?c' |- _ ] =>
              replace cnt with cnt' in H by apply cnt_irr;
                rewrite H' in H; inversion H
            end.
        + (* XXX: this broke, I don't know what age_getThreadCode is*)
          (* inversion H; subst; *)
          (*   try erewrite <- age_getThreadCode; *)
          (*   try rewrite gLockSetCode; *)
          (*   try rewrite gRemLockSetCode; *)
          (*   try erewrite gsoAddCode; eauto; *)
          (*     try rewrite gsoThreadCode; try eassumption. *)
          (* * eapply cntUpdate; eauto. eapply cnt. *)
          (* * { (*AQCUIRE*) *)
          (*     replace cnt' with cnt0 by apply cnt_irr; *)
      (*     exact Hcode. } *)
          admit.  
      - (* destruct (NatTID.eq_tid_dec i j). *)
        (* + subst j. *)
        (*   inversion H; subst; *)
        (*     match goal with *)
        (*     | [ H: getThreadC ?cnt = Krun ?c, *)
        (*            H': getThreadC ?cnt' = Kblocked ?c' |- _ ] => *)
        (*       try erewrite <- age_getThreadCode in H; *)
        (*         try rewrite gLockSetCode in H; *)
        (*         try rewrite gRemLockSetCode in H; *)
        (*         try erewrite gsoAddCode in H; eauto; *)
        (*           try rewrite gssThreadCode in H; *)
        (*           try solve[inversion H] *)
        (*     end. *)
        (* * apply threadPool.cntUpdate; eauto. apply cnt. *)
        (* * { (*AQCUIRE*) *)
        (*     replace cnt with cnt0 by apply cnt_irr; *)
        (*     exact Hcode. } *)
        (* + *)
          (* inversion H; subst; *)
          (*   match goal with *)
          (*   | [ H: getThreadC ?cnt = Krun ?c, *)
          (*          H': getThreadC ?cnt' = Kblocked ?c' |- _ ] => *)
          (*     try erewrite <- age_getThreadCode in H; *)
          (*       try rewrite gLockSetCode in H; *)
          (*       try rewrite gRemLockSetCode in H; *)
          (*       try erewrite gsoAddCode in H; eauto; *)
          (*         try rewrite gsoThreadCode in H; *)
          (*         try solve[inversion H]; eauto *)
          (*   end. *)
          (* * apply threadPool.cntUpdate; eauto. apply cnt. *)
          (*   { (*AQCUIRE*) *)
          (*     replace cnt with cnt0 by apply cnt_irr; *)
          (*       exact Hcode. } *)
        admit.
        Grab Existential Variables.
        all:admit.

        (* eauto. eauto. eauto. *)
        
    Admitted.

     Lemma threadHalt_update:
      forall i j, i <> j ->
                  forall tp cnt cnti c' cnt',
                    (@threadHalted j tp cnt) <->
                    (@threadHalted j (@updThreadC _ _ _ i tp cnti c') cnt') .
    Proof.
      intros; split; intros HH; inversion HH; subst;
        econstructor; eauto.
      erewrite <- (gsoThreadCC H); exact Hcode.
      erewrite (gsoThreadCC H); exact Hcode.
    Qed.

    Definition init_mach (_ : option unit) (m: mem)
               (tp:thread_pool)(v:val)(args:list val) : Prop :=
      exists c, initial_core semSem 0 m c v args /\ tp = mkPool (Krun c) tt.

    Definition install_perm tp m tid (Hcmpt: mem_compatible tp m) (Hcnt: containsThread tp tid) m' :=
      m = m'. 
    (** The signature of the Bare Machine *)
    Instance BareMachineSig: HybridMachineSig.MachineSig :=
      (HybridMachineSig.Build_MachineSig
                                       richMem
                                       dryMem
                                       mem_compatible
                                       invariant
                                       install_perm
                                       (@threadStep)
                                       threadStep_equal_run
                                       (@syncStep)
                                       syncstep_equal_run
                                       syncstep_not_running
                                       (@threadHalted)
                                       threadHalt_update
                                       syncstep_equal_halted
(*                                       threadStep_not_unhalts*)
                                       init_mach
      ).

  End BareMachine.
  Set Printing All.
End BareMachine.

