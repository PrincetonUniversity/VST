(** * Bare (no permissions) Interleaving Machine *)

Require Import compcert.lib.Axioms.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.
Require Import concurrency.pos.
Require Import concurrency.scheduler.
Require Import concurrency.addressFiniteMap. (*The finite maps*)
Require Import concurrency.pos.
Require Import concurrency.lksize.
Require Import concurrency.semantics.
Require Import concurrency.permissions.
Require Import concurrency.HybridMachineSig.
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
Require Import concurrency.threads_lemmas.
Require Import Coq.ZArith.ZArith.
Require Import concurrency.threadPool.

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

    Instance ordinalPool : (@ThreadPool.ThreadPool resources Sem) := @OrdinalPool.OrdinalThreadPool resources Sem.

    (** Memories*)
    Definition richMem: Type := mem.
    Definition dryMem: richMem -> mem:= id.

    (** Permissions on the memory are erased *)
    Definition diluteMem: mem -> mem := erasePerm.

    Notation thread_pool := (@t resources Sem).

    (** The state respects the memory*)
    Definition mem_compatible (tp : thread_pool) (m : mem) : Prop := True.
    Definition invariant (tp : thread_pool) := True.

    (** Steps*)
    Inductive thread_step genv {tid0 tp m} (cnt: containsThread tp tid0)
              (Hcompatible: mem_compatible tp m) :
      thread_pool -> mem -> seq mem_event -> Prop :=
    | step_thread :
        forall (tp':thread_pool) c m' (c' : C) ev
          (Hcode: getThreadC cnt = Krun c)
          (Hcorestep: ev_step semSem genv c m ev c' m')
          (Htp': tp' = updThreadC cnt (Krun c')),
          thread_step genv cnt Hcompatible tp' m' ev.

    Inductive ext_step (genv:G) {tid0 tp m} (*Can we remove genv from here?*)
              (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
      thread_pool -> mem -> sync_event -> Prop :=
    | step_acquire :
        forall (tp' : thread_pool) c m' b ofs
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external semSem genv c m =
                         Some (LOCK, Vptr b ofs::nil))
          (Hload: Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.one))
          (Hstore: Mem.store Mint32 m b (Int.intval ofs) (Vint Int.zero) = Some m')
          (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
          ext_step genv cnt0 Hcompat tp' m' (acquire (b, Int.intval ofs) None)

    | step_release :
        forall (tp':thread_pool) c m' b ofs
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external semSem genv c m =
                         Some (UNLOCK, Vptr b ofs::nil))
          (Hstore: Mem.store Mint32 m b (Int.intval ofs) (Vint Int.one) = Some m')
          (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
          ext_step genv cnt0 Hcompat tp' m' (release (b, Int.intval ofs) None)

    | step_create :
        forall (tp_upd tp':thread_pool) c b ofs arg
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external semSem genv c m =
                         Some (CREATE, Vptr b ofs::arg::nil))
          (Htp_upd: tp_upd = updThreadC cnt0 (Kresume c Vundef))
          (Htp': tp' = addThread tp_upd (Vptr b ofs) arg tt),
          ext_step genv cnt0 Hcompat tp' m (spawn (b, Int.intval ofs) None None)

    | step_mklock :
        forall  (tp': thread_pool) c m' b ofs
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external semSem genv c m =
                          Some (MKLOCK, Vptr b ofs::nil))
           (Hstore: Mem.store Mint32 m b (Int.intval ofs) (Vint Int.zero) = Some m')
           (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
          ext_step genv cnt0 Hcompat tp' m' (mklock (b, Int.intval ofs))

    | step_freelock :
        forall (tp' tp'': thread_pool) c b ofs
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external semSem genv c m =
                         Some (FREE_LOCK, Vptr b ofs::nil))
          (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
          ext_step genv cnt0 Hcompat  tp' m (freelock (b,Int.intval ofs))

    | step_acqfail :
        forall  c b ofs
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external semSem genv c m =
                          Some (LOCK, Vptr b ofs::nil))
           (Hload: Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.zero)),
          ext_step genv cnt0 Hcompat tp m (failacq (b, Int.intval ofs)).

    Definition threadStep (genv : G): forall {tid0 ms m},
        containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> seq mem_event -> Prop:=
      @thread_step genv.

   Lemma threadStep_equal_run:
    forall g i tp m cnt cmpt tp' m' tr,
      @threadStep g i tp m cnt cmpt tp' m' tr ->
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

    Definition syncStep (isCoarse:bool) (genv :G) :
      forall {tid0 ms m},
        containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> sync_event -> Prop:=
      @ext_step genv.

    Lemma syncstep_equal_run:
      forall b g i tp m cnt cmpt tp' m' tr,
        @syncStep b g i tp m cnt cmpt tp' m' tr ->
        forall j,
          (exists cntj q, @getThreadC _ _ _ j tp cntj = Krun q) <->
          (exists cntj' q', @getThreadC _ _ _ j tp' cntj' = Krun q').
    Proof.
        intros b g i tp m cnt cmpt tp' m' tr H j; split.
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
        inversion H; subst.
        * exists (cntUpdateC (Kresume c Vundef) cnt cntj), q.
          erewrite <- gsoThreadCC; eassumption.
        * exists (cntUpdateC (Kresume c Vundef) cnt cntj), q.
          erewrite <- gsoThreadCC; eassumption.
        * exists (cntAdd _ _ _
                    (cntUpdateC (Kresume c Vundef) cnt cntj)), q.
          erewrite @gsoAddCode with (j := j); eauto. 
          erewrite <- gsoThreadCC; eassumption.
          eapply cntUpdateC;
            now eauto.
        * exists (cntUpdateC (Kresume c Vundef) cnt cntj), q.
          erewrite <- gsoThreadCC; eassumption.
        * exists (cntRemoveL (b0, Int.intval ofs)
                        (cntUpdateC (Kresume c Vundef) cnt cntj)), q.
          erewrite <- gsoThreadCC; eassumption.
        * exists cntj, q; assumption.
    - intros [cntj [ q running]].
      destruct (NatTID.eq_tid_dec i j).
      + subst j. generalize running; clear running.
        inversion H; subst;
          try rewrite gRemLockSetCode;
          try rewrite gssThreadCC;
          try solve[intros HH; inversion HH].
        { (*addthread*)
          assert (cntj':=cntj).
          eapply cntAdd' in cntj'; destruct cntj' as [ [HH HHH] | HH].
          * erewrite gsoAddCode; eauto.
            subst; rewrite gssThreadCC; intros AA; inversion AA.
          * erewrite gssAddCode . intros AA; inversion AA.
            assumption. }
          { (*AQCUIRE*)
            replace cntj with cnt by apply cnt_irr.
            rewrite Hcode; intros HH; inversion HH. }
      + generalize running; clear running.
        inversion H; subst;
          try rewrite gRemLockSetCode;
          try (erewrite <- gsoThreadCC; [|eauto]);
        try (intros HH;
        match goal with
        | [ H: getThreadC ?cnt = Krun ?c |- _ ] =>
          exists cntj, c; exact H
        end).
      (*Add thread case*)
        assert (cntj':=cntj).
        eapply cntAdd' in cntj'; destruct cntj' as [ [HH HHH] | HH].
        * erewrite gsoAddCode; eauto.
          destruct (NatTID.eq_tid_dec i j);
            [subst; rewrite gssThreadCC; intros AA; inversion AA|].
          erewrite <- gsoThreadCC; eauto.
        * erewrite gssAddCode . intros AA; inversion AA.
          assumption.
          Grab Existential Variables.
          all: eauto.
    Qed.

    Lemma syncstep_not_running:
      forall b g i tp m cnt cmpt tp' m' tr,
        @syncStep b g i tp m cnt cmpt tp' m' tr ->
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

    Inductive threadHalted: forall {tid0 ms},
        containsThread ms tid0 -> Prop:=
    | thread_halted:
        forall tp c tid0
          (cnt: containsThread tp tid0)
          (Hcode: getThreadC cnt = Krun c)
          (Hcant: halted semSem c),
          threadHalted cnt.

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

    Lemma syncstep_equal_halted:
      forall b g i tp m cnti cmpt tp' m' tr,
        @syncStep b g i tp m cnti cmpt tp' m' tr ->
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
        + inversion H; subst;
            try (erewrite gsoAddCode; eauto);
            try erewrite <- gsoThreadCC; try (eassumption);
              try (eapply cntUpdateC; eauto).
          { (*AQCUIRE*)
            replace cnt' with cnt0 by apply cnt_irr;
              exact Hcode. }
      - destruct (NatTID.eq_tid_dec i j).
        + subst j.
          inversion H; subst;
            match goal with
            | [ H: getThreadC ?cnt = Krun ?c,
                   H': getThreadC ?cnt' = Kblocked ?c' |- _ ] =>
                try erewrite gsoAddCode in H; eauto;
                  try erewrite gssThreadCC in H;
                  try solve[inversion H]
            end;
            try (eapply cntUpdateC; eauto).
          { (*AQCUIRE*)
            replace cnt with cnt0 by apply cnt_irr;
              exact Hcode. }
        +
          inversion H; subst;
            match goal with
            | [ H: getThreadC ?cnt = Krun ?c,
                   H': getThreadC ?cnt' = Kblocked ?c' |- _ ] =>
                try erewrite gsoAddCode in H; eauto;
                  try erewrite <- gsoThreadCC in H; eauto;
                    try solve[inversion H]; eauto
            end;
            try (eapply cntUpdateC; eauto).
          { (*AQCUIRE*)
            replace cnt with cnt0 by apply cnt_irr;
              exact Hcode. }

          Grab Existential Variables.
          all:eauto.
    Qed.

    Lemma threadStep_not_unhalts:
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
    Qed.

    Definition one_pos : pos := mkPos NPeano.Nat.lt_0_1.

    Definition initial_machine c :=
      OrdinalPool.mk
        one_pos
        (fun _ =>  Krun c)
        (fun _ => tt)
        empty_lset.

    Definition init_mach (_ : option unit) (ge:G) (m: mem)
               (v:val)(args:list val):option (thread_pool * option mem) :=
      match initial_core semSem 0 ge m v args with
      | Some (c, m') =>
        Some (initial_machine c, m')
      | None => None
      end.

    (** The signature of the Bare Machine *)
    Definition BareMachineSig: @HybridMachineSig.MachineSig resources Sem ordinalPool :=
      (@HybridMachineSig.Build_MachineSig resources Sem ordinalPool
                                       richMem
                                       dryMem
                                       diluteMem
                                       mem_compatible
                                       invariant
                                       threadStep
                                       threadStep_equal_run
                                       syncStep
                                       syncstep_equal_run
                                       syncstep_not_running
                                       (@threadHalted)
                                       threadHalt_update
                                       syncstep_equal_halted
                                       threadStep_not_unhalts
                                       init_mach
      ).

  End BareMachine.
End BareMachine.

