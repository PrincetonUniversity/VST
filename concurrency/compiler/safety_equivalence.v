
(** In this file we prove the equivalence between several types of safety.
    In particular, an equivalence between csafe and safe.
    - Csafe: the safety used almost everywhere else in the development
    - Ksafe: the safety used by konig theorem.
    - Safe: the coinductive safety used by konig.
    - Explicit_safety: the safety preserved by machine simulations.

   The proofs apply to all Coarse, dry hybrid machines.
*)


Require Import Coq.Strings.String.

Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.cfrontend.Clight.

Require Import VST.veric.tycontext.
Require Import VST.veric.semax_prog.

(** *Juicy safetyn*)
Require Import VST.concurrency.juicy.semax_initial.
Require Import VST.concurrency.juicy.semax_conc.
Require Import VST.concurrency.juicy.semax_to_juicy_machine.
Require Import VST.concurrency.common.permissions.

(** *Erasure Imports*)
Require Import VST.concurrency.juicy.erasure_signature.
Require Import VST.concurrency.juicy.erasure_proof.
Require Import VST.concurrency.juicy.erasure_safety.

(** *SAFETY*)
Require Import VST.concurrency.compiler.safety.
Require Import VST.concurrency.compiler.coinductive_safety.

(** *SSROMEGA*)
Require Import Omega.
Require Import VST.concurrency.common.ssromega.
Set Bullet Behavior "Strict Subproofs".

(** *Excluded middle*)
Require Import Coq.Logic.Classical_Prop.



Section SafetyEquivalence.

  (* We put in our context a generic, coarse, dry hybrid machine. *)
  Import HybridMachineSig.HybridMachineSig.
  Import HybridCoarseMachine.
  Import threadPool.
  Context (resources:semantics.Resources)
          (Sem:semantics.Semantics)
          (TP: threadPool.ThreadPool.ThreadPool).
  Definition CoreSem:= semantics.csem (event_semantics.msem (@semantics.semSem Sem)).
  Context (Machine: MachineSig).
  Existing Instance Machine.
  Existing Instance DilMem.
  Existing Instance scheduler.

  
(* Ltac definition:
   yield and diluteMem are always identity for the Corase machines. 
   this tactic allows to fold the definitions, to use constructors and lemmas. *)
Ltac fold_ids:=
  repeat match goal with
         | [ U: schedule |-  _ ] =>
           match goal with
           | [  |- context[yield U] ] => fail 1
           | [  |- context[U] ] => replace U with (yield U) by auto 
           end 
         | [ m: mem |-  _ ] =>
           match goal with
           | [  |- context[diluteMem m] ] => fail 1
           | [  |- context[m] ] => replace m with (diluteMem m) by auto 
           end 
         end.
  
  (** *Setup *)
  (** We must reorganize the types of the machine to match those 
      from konig/safety. So we change the types of MachState and MachStep
   *)

  (* A correct schedule is one where, if there is a running thread, 
     it is the first one on the scheudle*)
  Definition correct_schedule (tp:  ThreadPool.t) U : Prop:=
    match schedPeek U with
    | Some i => unique_Krun tp i
    | None => True
    end.
  
  (* Bounded memory *)
  Definition bounded_mem (m: mem) := bounded_maps.bounded_map (snd (getMaxPerm m)) .

  (* kstate, packages trace, thread pool and memory, to use konig theorem. *)
  Definition kstate:Type:= (event_trace * ThreadPool.t * mem).
  Definition cstate2kstate (st:MachState) (m:mem): kstate:=
    (snd (fst st), snd st, m).
  Definition kstate2cstate (st:kstate) U: MachState:=
    (U, fst (fst st), snd (fst st)).
  Ltac simpl_state:=
    unfold kstate2cstate, cstate2kstate in *; simpl in *.

  (* Semantics that takes a step or loops when halted. *)
  Inductive sem_with_halt: MachState -> mem -> MachState -> mem -> Prop:=
  | halted_step st m:
      is_true (ssrbool.isSome (halted_machine st)) -> sem_with_halt st m st m
  | step_step st m st' m' :
      MachStep st m st' m' ->
      sem_with_halt st m st' m'.
  Definition kstep (st: kstate) U st' U': Prop:=
    sem_with_halt (kstate2cstate st U) (snd st) (kstate2cstate st' U') (snd st').

  (* Validity *)
  (* We really only care about states where the schedule is correct. *)
  Definition valid (kst:kstate) U := correct_schedule (snd (fst kst)) U.
  (* Also we might care only about bounded states. *)
  Definition valid_bound st U :=
    valid st U /\ bounded_mem (snd st).
  Definition ksafe_kstep (st : MachState) (m : mem) : nat -> Prop :=
    ksafe _ _ (kstep) valid (cstate2kstate st m) (fst (fst st)).
  Definition safe_kstep (st : MachState) (m : mem) : Prop :=
    safe _ _ (kstep) valid (cstate2kstate st m) (fst (fst st)).



Section Csafe_KSafe.
(** *Csafe and Ksafe*)
(** Prove of equivalence between Csafe and Ksafe.
    - Csafe is the safety notion used by top level (Clight) and 
      bottom level (Asm).
    - Ksafe is the notion of safety used by konig proof.
    Proofs in this section are for all dry and not diluted Coarse hybrid machines.
*)

       
  (* All machine steps are either Core or Angel (according to csafe)*)
  Inductive CoreOrAngel: MachState -> MachState -> Prop:=
  | IsCore st tr tp':
      CoreOrAngel st (fst (fst st), seq.cat (snd (fst st)) tr, tp')
  | IsAngel st tr tp':
      CoreOrAngel st (schedSkip (fst (fst st)), seq.cat (snd (fst st)) tr, tp').
 Lemma step_CoreOrAngel: forall st m st' m',
      MachStep st m st' m' ->
      CoreOrAngel st st'.
  Proof.
    intros. inversion H;
    destruct st' as ((?&?)&?);
    simpl in *; subst;
    match goal with
    | [  |- context[seq.cat _ _] ] => econstructor
    (* If the trace hasen't change, we add nil to match the type*)
    | _ => replace (snd (fst st)) with (seq.cat (snd (fst st)) nil) by apply seq.cats0;
            econstructor
    end.
  Qed.


    Lemma csafe_monotone:
    forall n U tr tp m,
    csafe (U, tr, tp) m (S n) ->
    csafe (U, tr, tp) m (n) .
  Proof.
    induction n; [econstructor|].
    intros.
    inversion H; simpl in *; subst.
    - econstructor 2; auto.
    - econstructor 3; eauto.
    - econstructor 4; eauto.
  Qed.

  (* MachStep that doesn't change the schedule,
    Reduces the set of valid schedules... 
   *)
  Inductive has_unique_running tp:Prop :=
  | HasUniqueRun i (cnti : ThreadPool.containsThread tp i) q:
      ThreadPool.getThreadC cnti = Krun q ->
      has_unique_running tp.
  
  Lemma schedPeek_Skip:
    forall U tid
      ( HschedN : schedPeek U = Some tid)
      ( HschedS : schedSkip U = U),
      False.
  Proof.
    intros. apply schedSkip_id in HschedS; subst.
    inversion HschedN.
  Qed.
  
  Lemma unique_Krun_update:
    forall st tid,
      unique_Krun st tid ->
      forall (cnt: ThreadPool.containsThread st tid) c_new m_new cnt,
        unique_Krun (ThreadPool.updThread(tid:=tid)(tp:=st) cnt (Krun c_new) m_new) tid.
  Proof.
    intros.
    unfold unique_Krun in *.
    intros.
    destruct (Nat.eq_dec j tid).
    - subst.
      destruct (Nat.eq_dec tid tid); subst;
        now auto.
    - pose proof cnti as cnti'.
      eapply ThreadPool.cntUpdate' in cnti'.
      eapply (H _ cnti' q).
      erewrite <- ThreadPool.gsoThreadCode with (cntj' := cnti) by eauto.
      assumption.
(*      intros Hcontra.
      eapply H1.
      eapply @threadHalt_update with (cnt := cnti');
        now eauto. *)
  Qed.
      
  Lemma unique_Krun_updateC:
    forall st tid,
      unique_Krun st tid ->
      forall (cnt: ThreadPool.containsThread st tid) c_new  cnt,
        unique_Krun (ThreadPool.updThreadC(tp:=st)(tid:=tid) cnt (Krun c_new)) tid.
  Proof.
    intros.
    unfold unique_Krun in *.
    intros.
    destruct (Nat.eq_dec j tid).
    - subst.
      destruct (Nat.eq_dec tid tid); subst;
        now auto.
    - pose proof cnti as cnti'.
      eapply ThreadPool.cntUpdateC' in cnti'.
      eapply (H _ cnti' q).
      erewrite ThreadPool.gsoThreadCC with (cntj' := cnti) by eauto.
      assumption.
      (* intros Hcontra.
      eapply H1.
      eapply @threadHalt_updateC with (cnt := cnti');
        now eauto. *)
  Qed.

  Lemma MachStep_preserve_unique:
    forall U tr st tr' st' m m',
      valid (tr, st, m) U -> 
      MachStep (U,tr,st) m (U,tr',st') m' ->
      has_unique_running st'.
  Proof.
    intros.
    inversion H0; simpl in *; subst;
      try solve[exfalso; eapply schedPeek_Skip; eauto].
    - (*start*) inversion Htstep; subst.
      eapply (HasUniqueRun _ _ ltac:(eapply ThreadPool.cntUpdate)).
      eapply ThreadPool.gssThreadCode.
    - (*resume*) inversion Htstep; subst.
      
      eapply (HasUniqueRun _ _ ltac:(eapply ThreadPool.cntUpdateC)).
      eapply ThreadPool.gssThreadCC.
    - (*step*)
      pose proof Htstep as Htstep'.
      eapply threadStep_at_Krun in Htstep'.
      destruct Htstep' as [q Hget].
      eapply threadStep_equal_run with (j := tid) in Htstep.
      destruct Htstep as [Hget_eq _].
      specialize (Hget_eq ltac:(do 2 eexists; eauto)).
      destruct Hget_eq as [? [? ?]].
      econstructor;
        now eauto.
      Unshelve. all:auto.
  Qed.

    Lemma CoreStep_preserve_valid:
    forall U tr st tr' st' m m',
      valid (tr, st, m) U ->
      MachStep (U,tr,st) m (U,tr',st') m' ->
      valid (tr', st', m') U.
  Proof.
    intros.
    unfold valid, correct_schedule in *.
    inversion H0; simpl in *; subst;
      try solve[exfalso; eapply schedPeek_Skip; eauto];
      try (erewrite HschedN in *).
    - (*start*)
      inversion Htstep; subst.
      intros j cntj' q Hget'.
      destruct (Nat.eq_dec tid j); [now auto|].
      assert (cntj : ThreadPool.containsThread st j)
        by (eapply ThreadPool.cntUpdate'; eauto).
      erewrite @ThreadPool.gsoThreadCode with (cntj := cntj) in Hget' by eauto.
      specialize (H _ _ _ Hget').
      destruct (Nat.eq_dec tid j);
        now eauto.
    - (*resume*) inversion Htstep; subst.
      intros j cntj' q' Hget'.
      destruct (Nat.eq_dec tid j); [auto|].
      assert (cntj : ThreadPool.containsThread st j)
        by (eapply ThreadPool.cntUpdateC'; eauto).
      erewrite <- @ThreadPool.gsoThreadCC with (cntj := cntj) in Hget' by eauto.
      specialize (H _ _ _ Hget').
      destruct (Nat.eq_dec tid j);
        now eauto.
    - (*step*)
      pose proof Htstep as Htstep'.
      intros j cntj' q' Hget'.
      eapply @threadStep_equal_run with (j := j) in Htstep.
      destruct Htstep as [_ Hget_eq].
      specialize (Hget_eq ltac:(do 2 eexists; eauto)).
      destruct Hget_eq as [cntj [q Hgetj]].
      specialize (H _ _ _ Hgetj).
      assumption.
  Qed.

  Lemma AngelStep_preserve_valid:
    forall U U' tr st tr' st' m m',
      valid (tr, st, m) U ->
      MachStep (U,tr,st) m (schedSkip U,tr',st') m' ->
      valid (tr', st', m') U'.
  Proof.
    intros.
    inversion H0; subst; simpl in *;
      try (exfalso; eapply schedPeek_Skip; now eauto);
      subst.
    - (* suspend thread case*)
      inversion Htstep; subst.
      unfold valid, correct_schedule in *.
      destruct (schedPeek U') eqn:HU'; auto.
      rewrite HschedN in H.
      simpl in *.
      intros j cntj' q' Hget'.
      destruct (Nat.eq_dec tid j); subst.
      + rewrite ThreadPool.gssThreadCC in Hget'.
        discriminate.
      + assert (cntj: ThreadPool.containsThread st j)
          by (eapply ThreadPool.cntUpdateC'; eauto).
        erewrite <- @ThreadPool.gsoThreadCC with (cntj := cntj) in Hget' by eauto.
        specialize (H _ _ _ Hget').
        destruct (Nat.eq_dec tid j); subst;
          simpl in *; exfalso;
            now auto.
    - (* syncStep case *)
      unfold valid, correct_schedule in *.
      rewrite HschedN in H.
      simpl in *.
      destruct (schedPeek U') eqn:?; auto.
      intros j cntj' q' Hget'.
      destruct (syncstep_equal_run _ _ _ _ _ _ _ _ _ Htstep j) as [? Hrun'].
      destruct (Hrun' ltac:(do 2 eexists; eauto)) as [cntj [q Hget]].
      specialize (H _ _ _ Hget).
      destruct (Nat.eq_dec tid j); subst;
        [|exfalso; simpl in *; now auto].
      eapply @syncstep_not_running with (cntj:= cntj) (q:=q) in Htstep.
      exfalso;
        now auto.
    - unfold valid, correct_schedule in *.
      rewrite HschedN in H.
      simpl in *.
      destruct (schedPeek U'); auto.
      intros j cntj' q' Hget'.
      specialize (H _ _ _ Hget').
      destruct (Nat.eq_dec tid j); subst;
        simpl in *; exfalso; now auto.
  Qed.
  
  (* *)
  Lemma ksafe_csafe_equiv':
    forall st_ m tr,
      (forall n U, valid (tr, st_, m) U -> ksafe_kstep (U, tr, st_) m n) ->
      (forall n U, valid (tr, st_, m) U -> csafe (U, tr, st_) m n).
  Proof.
    intros st m tr HH n U.
    specialize (HH n).
    revert st m tr HH U.
    induction n; intros.
    - econstructor.
    - assert (H':=H).
      eapply HH in H.
      inversion H; subst; simpl in *.
      inversion H1; subst.
      + (* Halted *) econstructor 2; auto.
      + (* step_step *) simpl_state.
        destruct st' as ((?&?)&?); simpl in *; subst.
        (* we distinguish between Core steps and Angel steps (print csafe for more info)*)
        assert (step_cases:= (step_CoreOrAngel _ _ _ _ H0)); inversion step_cases; subst.
        * eapply CoreSafe; simpl.
          -- eassumption.
          -- eapply IHn.
             unfold ksafe_kstep, cstate2kstate.
             assumption.
             eapply CoreStep_preserve_valid in H0;
               eauto.
        *  (* AngelStep *) simpl_state.
         eapply AngelSafe; simpl.
           -- eassumption.
           -- intros.
              eapply IHn.
              unfold ksafe_kstep, cstate2kstate.
              assumption.
              eapply AngelStep_preserve_valid;
                now eauto.
  Qed.


  Lemma ksafe_csafe_equiv:
    forall tp m tr,
      (forall U, valid (tr, tp, m) U) ->
      (forall n U, ksafe_kstep (U, tr, tp) m n) ->
      (forall n U, csafe (U, tr, tp) m n).

  Proof. intros ? ? ? H ? ? ?. apply ksafe_csafe_equiv'; try apply H.
         auto.
  Qed.

  Lemma valid_unique_running:
    forall tp tr m U U' tid tid',
      schedPeek U = Some tid ->
      schedPeek U' = Some tid' ->
      valid (tr, tp, m) U ->
      valid (tr, tp, m) U' ->
      has_unique_running tp ->
      tid = tid'.
  Proof.
    unfold valid, correct_schedule; simpl.
    intros.
    destruct (schedPeek U); inversion H;
      destruct (schedPeek U'); inversion H0; subst.
    unfold unique_Krun in *.
    inversion H3.
    specialize (H1 _ _ _ H4).
    specialize (H2 _ _ _ H4).
    destruct (Nat.eq_dec tid i), (Nat.eq_dec tid' i);
      subst; auto;
        simpl in *;
        try (exfalso; now auto).
  Qed.

  Lemma csafe_first_tid:
    forall n U U' tr tp m,
      csafe (U, tr, tp) m n ->
      schedPeek U = schedPeek U' -> 
      csafe (U', tr, tp) m n.
  Proof.
    induction n; subst.
    - constructor 1.
    - intros. inversion H; subst.
      + econstructor 2; eauto.
        unfold halted_machine in *; simpl in *.
        destruct (schedPeek U); try solve [inversion H1].
        rewrite <- H0; eauto.
      + econstructor 3; eauto; simpl in *.
        inversion Hstep; simpl in *; subst;
          try match goal with
              | [ H: schedPeek ?U = Some _, H0: schedSkip U = U |- _ ] =>
                apply schedPeek_Skip in H; eauto; inversion H
              end.
        * rewrite <- H6. fold_ids.
          econstructor 1; simpl; eauto.
          rewrite <- H0; eauto.
        * rewrite <- H6. fold_ids. 
          econstructor 2; simpl; eauto.
          rewrite <- H0; eauto.
        * unfold MachStep; simpl. fold_ids.
          econstructor 3; simpl; eauto.
          rewrite <- H0; eauto.
      + econstructor 4; eauto; simpl in *.
        inversion Hstep; simpl in *; subst;
          try match goal with
              | [ H: schedPeek ?U = Some _, H0: ?U = schedSkip ?U |- _ ] =>
                eapply schedPeek_Skip in H; eauto; inversion H
              end.
        * rewrite <- H6; econstructor 4; subst; simpl in *; subst; eauto.
          rewrite <- H0; eauto. 
        * econstructor 5; subst; simpl in *; subst; eauto.
          rewrite <- H0; eauto. 
        * rewrite <- H6; econstructor 6; subst; simpl in *; subst; eauto.
          rewrite <- H0; eauto. 
  (* * rewrite <- H6; econstructor 7; subst; simpl in *; subst; eauto.
                  rewrite <- H0; eauto.  *)
  Qed.
  
  Lemma csafe_unique_running:
    forall U tr tp m n tid,
      schedPeek U = Some tid ->
      has_unique_running tp ->
      valid (tr, tp, m) U ->
      csafe (U, tr, tp) m n ->
      forall U', valid (tr, tp, m) U' ->
            csafe (U', tr, tp) m n.
  Proof.
    intros.
    destruct (schedPeek U') eqn:UU.
    2: econstructor; unfold halted_machine; simpl; try rewrite UU; auto.
    eapply csafe_first_tid; eauto.
    rewrite H, UU; f_equal.
    eapply valid_unique_running; eauto.
  Qed.
  
  Lemma csafe_ksafe_equiv:
    forall st_ m tr,
      (forall n U, valid (tr, st_, m) U -> csafe (U, tr, st_) m n) ->
      (forall n U, valid (tr, st_, m) U -> ksafe_kstep (U, tr, st_) m n).
  Proof.
    intros st m tr HH n U.
    specialize (HH n).
    revert st m tr HH U.
    induction n; intros.
    - econstructor.
    - assert (H':=H).
      eapply HH in H.
      inversion H; subst; simpl in *.
      + (* Halted *)
        econstructor.
        * constructor. simpl_state; auto.
        * eapply IHn; simpl; eauto.
          intros ? H1.
          apply HH in H1.
          eapply csafe_monotone; eauto.
      + (*CoreStep*)
        econstructor.
        * constructor 2; simpl_state.
          instantiate(1:=( seq.cat tr tr0, tp', m')); simpl.
          eauto.
        * eapply IHn.
          simpl.
          assert (Hsched: exists tid, schedPeek U = Some tid)
            by (inversion Hstep; subst;
                eexists; eauto).
          destruct Hsched.
          eapply csafe_unique_running;
            now eauto using MachStep_preserve_unique, CoreStep_preserve_valid.
      +  (*AngelStep*)
        econstructor.
        * constructor 2; simpl_state.
          instantiate(1:=( seq.cat tr tr0, tp', m')); simpl.
          eauto.
        * eapply IHn.
          eauto.
  Qed.

  Lemma csafe_ksafe_equiv_trick:
    forall st_ m tr,
      (forall U, valid (tr, st_, m) U) ->
      (forall n U, csafe (U, tr, st_) m n) ->
      (forall n U, ksafe_kstep (U, tr, st_) m n).
  Proof.
    intros ? ? ? ? VALID H ?;
    apply csafe_ksafe_equiv; try apply VALID; auto.
  Qed.    

    
End Csafe_KSafe.



Section Safety_Explicity_Safety.

  
  Definition explicit_safety (U:schedule)  (tr:event_trace) (st:machine_state) (m:mem): Prop:=
    exp_safety _ _ (fun U stm => is_true (ssrbool.isSome (halted_machine (U, fst(fst stm), snd(fst stm)))))
                   (fun U stm stm' => internal_step U (snd(fst stm)) (snd stm) (snd(fst stm')) (snd stm'))
                   (fun U stm U' stm' => external_step U (fst(fst stm)) (snd(fst stm)) (snd stm) U' (fst(fst stm')) (snd(fst stm')) (snd stm'))
                   (fun U stm => @valid (fst(fst stm),snd(fst stm), snd stm) U) U (tr,st,m).

  Definition explicit_safety_bounded (U:schedule)  (tr:event_trace)(st:machine_state) (m:mem): Prop:=
    exp_safety _ _ (fun U stm => is_true (ssrbool.isSome (halted_machine (U, fst(fst stm), snd(fst stm)))))
                   (fun U stm stm' => internal_step U (snd(fst stm)) (snd stm) (snd(fst stm')) (snd stm'))
                   (fun U stm U' stm' => external_step U (fst(fst stm))  (snd(fst stm)) (snd stm) U' (fst(fst stm')) (snd(fst stm')) (snd stm'))
                   (fun U stm => @valid_bound (fst(fst stm),snd(fst stm), snd stm) U) U (tr,st,m).

  
  (* Show that traces are irrelevant*)
  Section TracesIrrelevant.
    
        Lemma kstep_trace_irr: forall U U' tr1 tr1' tr2 tp tp' m m',
            kstep (tr1, tp, m) U (tr1', tp', m') U' -> exists tr2', kstep (tr2, tp, m) U (tr2', tp', m') U'.
        Proof.
          intros. inversion H; simpl in *; subst.
          - exists tr2. 
            constructor; eauto.
          - unfold kstate2cstate in *; simpl in *.
            inversion H0; simpl in *; subst;
              try solve[exists tr2; econstructor 2; econstructor; eauto].
            + exists tr2; econstructor 2. simpl_state; eauto. fold_ids.
              econstructor; eauto.
            + exists (seq.cat tr2
                        (List.map
                           (fun mev : event_semantics.mem_event =>
                              HybridMachineSig.Events.internal tid mev) ev)).
              simpl. econstructor. unfold kstate2cstate; simpl.
              unfold MachStep in *; simpl in *.
              fold_ids.
              auto.
              econstructor; eauto.
            + exists (seq.cat tr2 (HybridMachineSig.Events.external tid ev :: nil)).
              simpl. econstructor. unfold kstate2cstate; simpl.
              unfold MachStep in *; simpl in *.
              econstructor; eauto.
        Qed.
              
        Lemma safe_kstep_trace_irr: forall U tr tr' tp m,
            safe_kstep (U,tr,tp) m -> safe_kstep (U,tr',tp) m.
        Proof.
          unfold safe_kstep; simpl.
          unfold cstate2kstate, kstate2cstate in *; simpl in *.
          cofix foo.
          intros. inversion H.
          destruct st' as ((?&?)&?).
          destruct (kstep_trace_irr _ _ _ _ tr' _ _ _ _ H0) as (tr2' &STEP).
          econstructor; eauto.

        Qed.

        
            Lemma external_step_trace_irr: forall U U' tr1 tr1' tr2 tp tp' m m',
            external_step U tr1 tp m U' tr1' tp' m' -> exists tr2', external_step U tr2 tp m U' tr2' tp' m'.
        Proof.
          intros. inversion H; simpl in *; subst.
          - exists tr2. fold_ids.
            econstructor; eauto.
          - exists tr2. econstructor 2; eauto.
          - exists tr2. econstructor 3; eauto.
          - exists (seq.cat tr2
           (HybridMachineSig.Events.external tid ev :: nil)).
            econstructor 4; eauto.
          - exists tr2. econstructor 5; eauto.
          (* - exists tr2. econstructor 6; eauto. *)
        Qed.
        
        Lemma explicit_safety_trace_irr: forall U tr tr' tp m,
           explicit_safety U tr tp m -> explicit_safety U tr' tp m.
        Proof.
          cofix COFIX.
          intros. inversion H; simpl in *.
          - econstructor; eauto.
          - econstructor 2; eauto.
          - destruct (external_step_trace_irr _ _ _ _ tr' _ _ _ _ H0) as (?&STEP). 
            
            destruct y' as ((y1&y2)&y3); simpl in *.
            econstructor 3; simpl.
            + instantiate(1:= (x, y2, y3)).
              eauto.
            + simpl in *.
              intros. eapply COFIX.
              eapply H1 in H2.
              eapply H2.
        Qed.        
  End TracesIrrelevant.

  (* Note, unused right now *)
  Lemma explicit_safety_schedule_irr:
    forall U U' tr tp m,
      schedPeek U = schedPeek U' ->
      explicit_safety U tr tp m -> explicit_safety U' tr tp m.
  Proof.
    cofix COFIX.
    intros. inversion H0; simpl in *.
    - econstructor.
      simpl in *.
      unfold halted_machine in *. simpl in *.
      rewrite <- H.
      assumption.
    - econstructor 2; eauto.
      simpl.
      inversion H1; subst.
      rewrite H in HschedN.
      rewrite <- H7.
      econstructor; eauto.
    - inversion H1;
        try match goal with
            | [H: schedSkip _ = _ |- _] =>
              econstructor 3 with (x' := schedSkip U')
            | [ |- _] =>
              econstructor 3 with (x' := U')
            end; subst;
        try match goal with
            | [H: diluteMem _ = _ |- _] =>
              rewrite <- H; clear H
            end; eauto;
          [econstructor 1 |
           econstructor 2 |
           econstructor 3 |
           |
           econstructor 5 (*|
           econstructor 6*)];
          try (rewrite <- H); eauto.
      rewrite <- H9.
      econstructor 4; try (rewrite <- H); eauto.
  Qed.
  
  Inductive InternalOrExternal: MachState -> mem -> MachState -> mem -> Prop:=
  | IsInternal st st' m m':
      internal_step (fst (fst st)) (snd st) m (snd st') m'  ->
      InternalOrExternal st m st' m'
  | IsExternal st st' m m':
      external_step (fst (fst st)) (snd (fst st)) (snd st) m (fst (fst st')) (snd (fst st')) (snd st') m'  ->
      InternalOrExternal st m st' m'.
      
  (* All machine steps are either Internal or External (according to csafe)*)
  Lemma step_InternalOrExternal: forall st m st' m',
      MachStep st m st' m' ->
      InternalOrExternal st m st' m'.
  Proof.
    intros. inversion H;
    destruct st' as ((?&?)&?);
    simpl in *; subst.
    - constructor 2. fold_ids. econstructor; eauto.
    - constructor 2. econstructor 2; eauto.
    - constructor 1. 
      destruct st as ((?&?)&?); simpl in *.
      eapply thread_step' in Htstep; eauto.
    - constructor 2; econstructor 3; eauto.
    - constructor 2; econstructor 4; eauto.
    - constructor 2; econstructor 5; eauto.
   (* - constructor 2; econstructor 6; eauto. *)
  Qed.
  
   (*BUT, this is basically the same safety!!! *)
  Lemma safety_equivalence21: forall st m tr,
      (forall U, valid (tr, st, m) U ->
             safe_kstep (U, tr, st) m) ->
      forall U, valid (tr, st, m) U ->
            explicit_safety U tr st m.
  Proof.
    cofix COFIX.
    intros st m tr sns_all U sns.
    eapply sns_all in sns.
    inversion sns.
    unfold cstate2kstate in H; simpl in H.
    inversion H; subst.
    - (*Halted *) unfold kstate2cstate in *; simpl in *; subst.
      eapply halted_safety; simpl; assumption.
    - (*Step_step*) destruct st' as [[tr' tp] m'].
      unfold cstate2kstate, kstate2cstate in *; simpl in *; subst.
      assert (step_cases:= (step_InternalOrExternal _ _ _ _ H1)); inversion step_cases; subst.
      + (*Internal*) eapply (internal_safety).
        instantiate (1:=(tr,tp,m')); simpl in *; eauto.
        unfold cstate2kstate, kstate2cstate in *; simpl in *; subst.
        
        intros.
        eapply COFIX; eauto.
        intros.


        unfold safe_kstep, cstate2kstate, kstate2cstate in *; simpl in *; subst.
        eapply safe_kstep_trace_irr.
        
        eapply H0.
        simpl; eauto.
      +  (*External*) eapply (external_safety).
        instantiate (1:=(tr',tp,m')); simpl in *; eauto.
        unfold cstate2kstate, kstate2cstate in *; simpl in *; subst.
        
        intros.
        eapply COFIX; eauto.
  Qed.

  Lemma safety_equivalence22: forall st m tr,
      (forall U, valid (tr, st, m) U ->
           explicit_safety U tr st m) ->
           (forall U, valid (tr, st, m) U ->
                 safe_kstep (U, tr, st) m).
  Proof.
    cofix COFIX.
    intros st m tr es_all U es.
    eapply es_all in es.
    inversion es.
    - econstructor; eauto.
      + econstructor. simpl; eauto.
      + unfold cstate2kstate; simpl; intros U'' VAL.
        apply COFIX; eauto.
    - eapply step_equivalence2 in H. destruct H as (?&H); simpl in *.
      econstructor.
      + econstructor 2.
        unfold kstate2cstate, cstate2kstate in *; simpl in *.
        instantiate(1:=((seq.cat tr x) , snd(fst y'), snd y')); simpl in *.
        instantiate(1:=U).
        destruct y' as ((?&?)&?).
        eapply H. 
      + intros. destruct y' as ((?&?)&?).
        simpl in *; apply COFIX; intros; eauto.
        eapply H0 in H2. simpl in *.
        eapply explicit_safety_trace_irr.
        eapply H2.
    - eapply step_equivalence3 in H. destruct H as (?&?&STEP); simpl in *.
      destruct y' as ((y1&y2)&y3); simpl in *.
      econstructor.
      + econstructor 2.
        unfold kstate2cstate, cstate2kstate in *; simpl in *.
        instantiate(1:=(y1 , y2, y3)); simpl in *.
        instantiate(1:=x').
        eapply STEP.
      + intros. simpl in *; apply COFIX; intros; eauto.
        eapply H0 in H2. simpl in *.
        eapply explicit_safety_trace_irr.
        eapply H2.
  Qed.
  Lemma safety_equivalence2: forall st m tr,
      (forall U, valid (tr, st, m) U ->
             safe_kstep (U, tr, st) m) <->
      (forall U, valid (tr, st, m) U ->
            explicit_safety U tr st m).
  Proof.
    intros st m tr; split;
           [eapply safety_equivalence21 | apply safety_equivalence22].
  Qed.  
  
End  Safety_Explicity_Safety.



Section Csafe_Safety.

Context (finit_branch_kstep:(forall x : kstate,
        finite_on_x
          (possible_image
             (fun (x0 : kstate) (y : schedule) (x' : kstate) =>
                exists y' : schedule, kstep x0 y x' y') valid x))).


Lemma finite_state_preservation:
  forall P0 P' : SST kstate,
    konig.finite P0 -> SST_step kstate schedule kstep valid P0 P' -> konig.finite P'.
Proof.
  (* This should follow from finitebranching, lifted to sets *)
Admitted.
    
Lemma csafe_safety_trick:
  forall tr tp m,
       (forall U : schedule, valid (tr, tp,m) U) ->
       (forall (n : nat) U, csafe (U, tr, tp) m n) ->
       forall U : schedule, safe kstate schedule kstep valid (tr,tp,m) U.
Proof.
  intros ??????.
  eapply ksafe_safe; eauto.
  - eapply finite_state_preservation.
  - exact classic.
  - eapply csafe_ksafe_equiv_trick; eauto.
Qed.

Lemma csafe_safety:
  forall tr tp m,
       (forall (n : nat) U, valid (tr, tp,m) U -> csafe (U, tr, tp) m n) ->
       forall U : schedule, valid (tr, tp,m) U -> safe kstate schedule kstep valid (tr,tp,m) U.
Proof.
  intros ??????.
  eapply ksafe_safe'; eauto.
  - eapply finite_state_preservation.
  - exact classic.
  - eapply csafe_ksafe_equiv; eauto.
Qed.

Lemma safety_csafe_trick:
  forall tr tp m,
    (forall U : schedule, valid (tr, tp,m) U) ->
    (forall U : schedule, safe kstate schedule kstep valid (tr,tp,m) U) ->
    (forall (n : nat) U, csafe (U, tr, tp) m n).
Proof.
  unfold kstate2cstate; simpl.
  intros ???????.
  eapply ksafe_csafe_equiv; eauto.
  unfold ksafe_kstep.
  simpl_state.
  eapply safe_ksafe; eauto.
Qed.


Lemma safety_csafe:
  forall tr tp m,
    (forall U : schedule, valid (tr, tp,m) U -> safe kstate schedule kstep valid (tr,tp,m) U) ->
    (forall (n : nat) U, valid (tr, tp,m) U -> csafe (U, tr, tp) m n).
Proof.
  unfold kstate2cstate; simpl.
  intros ???????.
  eapply ksafe_csafe_equiv'; eauto.
  unfold ksafe_kstep.
  simpl_state.
  intros.
  eapply safe_ksafe'; eauto.
Qed.


Lemma csafe_explicit_safety:
  forall tr tp m,
       (forall (n : nat) U, valid (tr, tp,m) U -> csafe (U, tr, tp) m n) ->
       forall U, valid (tr, tp,m) U -> explicit_safety U tr tp m.
Proof.
  intros ??????.
  eapply safety_equivalence2; eauto.
  intros.
  eapply csafe_safety; eauto; simpl.
Qed.

Lemma explicit_safety_csafe:
  forall tr tp m,
    (forall U : schedule, valid (tr, tp,m) U -> explicit_safety U tr tp m) ->
    (forall (n : nat) U, valid (tr, tp,m) U -> csafe (U, tr, tp) m n).
Proof.
  intros.
  eapply safety_csafe; eauto.
  intros.
  eapply safety_equivalence22; eauto.
Qed.


Lemma csafe_explicit_safety':
  forall tr tp m,
       (forall U : schedule, valid (tr, tp,m) U) ->
       (forall (n : nat) U, csafe (U, tr, tp) m n) ->
       forall U : schedule, explicit_safety U tr tp m.
Proof.
  intros ??????.
  eapply safety_equivalence2; eauto.
  intros.
  eapply csafe_safety; eauto.
Qed.

Lemma explicit_safety_csafe':
  forall tr tp m,
    (forall U : schedule, valid (tr, tp,m) U) ->
    (forall U : schedule, explicit_safety U tr tp m) ->
    (forall (n : nat) U, csafe (U, tr, tp) m n).
Proof.
  intros.
  eapply safety_csafe_trick; eauto.
  intros.
  eapply safety_equivalence22; eauto.
Qed.

End Csafe_Safety.

End SafetyEquivalence.




(*

(*
ksafe_safe
     : forall (ST SCH : Type) (STEP : ST -> SCH -> ST -> SCH -> Prop)
         (valid : ST -> SCH -> Prop),
       (forall P : Prop, P \/ ~ P) ->
       True ->
       (forall x : ST,
        finite_on_x
          (possible_image
             (fun (x0 : ST) (y : SCH) (x' : ST) => exists y' : SCH, STEP x0 y x' y')
             valid x)) ->
       forall st : ST,
       (forall U : SCH, valid st U) ->
       (forall (n : nat) (U : SCH), ksafe ST SCH STEP valid st U n) ->
       forall U : SCH, safe ST SCH STEP valid st U
*)



















(** *Beggins old proofs (specific to clight and asm... *)




















  
Section Ksafety_Clight.
  (* Import DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryConc.
  Import DryMachineSource.THE_DRY_MACHINE_SOURCE.SCH.
  Import DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryMachine.
   *)

  Import HybridMachineSig.HybridMachineSig.
  Import HybridMachine.

  (** *Clight setup *)
  (** We define state and step to match the type of ksafe (in konig/safety)
   *)
  Parameter machine_event:Type.
  Definition new_state: Type:= list machine_event * machine_state * mem.
  Definition mk_nstate (st:MachState) m:new_state:= (snd (fst st), snd st, m).
  Definition ksafe_new_step (ge : G) (st : MachState) (m : mem) : nat -> Prop :=
    ksafe _ _ (new_step ge) new_valid (mk_nstate st m) (fst (fst st)).
  
  (** *First show Csafety -> Ksafety*)
  Lemma Clight_csafe2ksafe:
      forall ge st_ m,
        (forall U n, new_valid (nil, st_, m) U ->  csafe ge (U, nil, st_) m n) ->
        (forall U n, new_valid (nil, st_, m) U -> ksafe_new_step ge (U, nil, st_) m n).
    Proof.
      intros.
      assert (HH: forall (U : Sch), new_valid (nil, st_, m) U -> csafe ge (U, nil, st_) m n) by
      (intros; apply H; eauto). clear H.
      generalize ge st_ m HH U H0. clear.
      induction n.
      - econstructor.
      - intros. assert (VALID:= H0).
        eapply HH in H0.
        inversion H0; subst.
        + econstructor.
          * econstructor; eauto.
          * intros. unfold mk_nstate in *; simpl in *.
            eapply IHn; eauto. intros.
            apply csafe_monotone; auto.
        + econstructor.
          unfold new_step, mk_nstate, mk_ostate; simpl.
          econstructor 2.
          instantiate (1:= (nil, tp', m')); eauto.
          intros. eapply IHn; eauto.
          intros.
          simpl in Hsafe.
          clear H.
          unfold new_valid, correct_schedule in H1; simpl in *.
          destruct (schedPeek U0) eqn:PEEK0.
          2: econstructor; unfold halted; simpl;
            rewrite PEEK0; auto.
          
          eapply csafe_first_tid; eauto.
          simpl in Hstep.
          assert (new_valid (nil, tp', m') U).
          { eapply step_new_valid in Hstep.
            unfold mk_nstate in Hstep; simpl in *; eauto.
            unfold mk_nstate; simpl; eauto. }
          unfold new_valid, correct_schedule in H; simpl in *.
          inversion Hstep; subst; simpl in *;
            try match goal with
                | [ H: schedPeek ?U = Some _, H0: schedSkip U = U |- _ ] =>
                  symmetry in H0;
                    rewrite end_of_sch in H0;
                    rewrite H in H0; inversion H0
                end.
          (*All three cases are identical*)
          * (*init*)
            rewrite HschedN in *.
            rewrite PEEK0; f_equal.
            inversion Htstep; subst.
            symmetry.
            assert (HH2:forall i j, is_true (ssrbool.is_left (TID.eq_tid_dec i j)) -> i = j).
            { clear. intros. destruct (TID.eq_tid_dec i j); inversion H; auto. }
            apply HH2. eapply H1.
            -- eapply ErasureSafety.ErasureProof.DTP.gssThreadCC.
            -- intros HHH.
               unfold threadHalted in HHH.
               inversion HHH.
               simpl in Hcant.
               unfold ErasureSafety.ErasureProof.JMS.the_sem in Hcant; simpl in *.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.Sem in Hcant.
               rewrite JuicyMachineModule.THE_JUICY_MACHINE.SEM.CLN_msem in Hcant.
               inversion Hcant.
          * rewrite PEEK0, HschedN in *.
            f_equal.
            inversion Htstep; subst.
            symmetry.
            assert (HH2:forall i j, is_true (ssrbool.is_left (TID.eq_tid_dec i j)) -> i = j).
            { clear. intros. destruct (TID.eq_tid_dec i j); inversion H; auto. }
            apply HH2. eapply H1.
            -- eapply ErasureSafety.ErasureProof.DTP.gssThreadCC.
            -- intros HHH.
               unfold threadHalted in HHH.
               inversion HHH.
               simpl in Hcant.
               unfold ErasureSafety.ErasureProof.JMS.the_sem in Hcant; simpl in *.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.Sem in Hcant.
               rewrite JuicyMachineModule.THE_JUICY_MACHINE.SEM.CLN_msem in Hcant.
               inversion Hcant.
          * rewrite PEEK0, HschedN in *.
            f_equal.
            inversion Htstep; subst.
            symmetry.
            assert (HH2:forall i j, is_true (ssrbool.is_left (TID.eq_tid_dec i j)) -> i = j).
            { clear. intros. destruct (TID.eq_tid_dec i j); inversion H; auto. }
            apply HH2. eapply H1.
            -- eapply ErasureSafety.ErasureProof.DTP.gssThreadCC.
            -- intros HHH.
               unfold threadHalted in HHH.
               inversion HHH.
               simpl in Hcant.
               unfold ErasureSafety.ErasureProof.JMS.the_sem in Hcant; simpl in *.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.Sem in Hcant.
               rewrite JuicyMachineModule.THE_JUICY_MACHINE.SEM.CLN_msem in Hcant.
               inversion Hcant.
        + (*machine step*)
          simpl in *.
          econstructor.
          unfold new_step, mk_nstate, mk_ostate; simpl.
          econstructor 2.
          instantiate (1:= (nil, tp', m')); eauto.
          intros. eapply IHn; eauto.


          Unshelve.
          eapply ErasureSafety.ErasureProof.DTP.cntUpdateC; eauto.
          eapply ErasureSafety.ErasureProof.DTP.cntUpdateC; eauto.
          eapply ErasureSafety.ErasureProof.DTP.cntUpdate; eauto.
                    
    Qed.

    Lemma init_schedule:
      forall U pmap n g m p t init_mach om,
        (semantics.initial_core (MachineSemantics U pmap) n g m p t) = Some (init_mach, om) ->
        fst (fst init_mach) = U.
    Proof. intros. simpl in H. unfold init_machine,init_mach in H.
           destruct (semantics.initial_core ErasureSafety.ErasureProof.JMS.the_sem 0 g m p)
             as [[? ?] | ];
             inversion H.
           destruct pmap; inversion H; auto.
    Qed.
    Lemma init_trace:
      forall U pmap n g m p t init_mach om,
        (semantics.initial_core (MachineSemantics U pmap) n g m p t) = Some (init_mach, om) ->
        snd (fst init_mach) = nil.
    Proof. intros. simpl in H. unfold init_machine,init_mach in H.
           destruct (semantics.initial_core ErasureSafety.ErasureProof.JMS.the_sem 0 g m p)
               as [[? ?]|];
             inversion H.
           destruct pmap; inversion H; auto.
    Qed.

   (* Lemma init_schedule_all:
      forall U pmap n g m p t init_mach om,
        (semantics.initial_core (MachineSemantics U pmap) n g m p t) = Some (init_mach, om) ->
        forall U'',
        correct_schedule (U'', snd (fst init_mach), snd init_mach) ->
        schedPeek U'' = Some 1  \/ schedPeek U'' = None .
      
    Ad_itted. *)
           
    Lemma Initial_dry_ksafety:
      forall (U : semax_invariant.schedule) (n : nat),
      exists init_U init_tr init_st,
        (semantics.initial_core (MachineSemantics U (Some ( getCurPerm (juicy_mem.m_dry (init_jmem n)), empty_map)))) 0 init_genv (juicy_mem.m_dry (init_jmem n)) init_point nil =
        Some ((init_U, init_tr, init_st), None) /\
        forall n' U',
       ksafe_new_step (globalenv prog) (U', init_tr, init_st)
         (proj1_sig (init_mem CPROOF)) n'.
    Proof.
      intros.
      pose proof (Initial_dry_Csafety_stronger U n).
      destruct H as [init_U [init_tr [init_st [INIT_ok SAFE] ]]].
      do 3 eexists; split; eauto.
      
      
      pose proof (init_schedule _ _ _ _ _ _ _ _ _ INIT_ok).

      pose proof (init_trace _ _ _ _ _ _ _ _ _ INIT_ok).
        simpl in *.
        subst.
        induction n'; try solve[constructor].
      (** *Check if the schedule is empty, valid, or about to stutter*)
        intros U'; destruct U'.
      - (*nil case*)
        intros.
        econstructor.
        eapply halt_with_step.
        unfold mk_ostate, mk_nstate; auto.
        intros; eauto.
        unfold ksafe_new_step,mk_nstate in IHn'; simpl in IHn'.
        unfold mk_nstate; simpl; auto.
      - destruct (Compare_dec.zerop t).
        + subst. simpl.
          eapply Clight_csafe2ksafe; intros.
          * eapply SAFE.
          * unfold new_valid, correct_schedule, mk_ostate; simpl.
            intros j ? ? ? ?.
            unfold ThreadPool.containsThread in cnti; simpl in cnti.
            unfold init_machine,init_mach in INIT_ok.
               match goal with
               | [ H: context[semantics.initial_core ?a ?b ?c ?d ?e ?f ] |- _ ] =>
                 destruct (semantics.initial_core a b c d e f) as [[? ?]| ]
               end; inversion INIT_ok; subst.
            simpl in cnti.
            clear - cnti.
            destruct (TID.eq_tid_dec 0 j); auto.
            destruct j; try contradiction n; auto.
            inversion cnti.
        +  econstructor.
           * eapply step_with_halt.
             unfold mk_ostate, mk_nstate; simpl.
             instantiate (4:=U').
             instantiate (2:= (nil, init_st,  (proj1_sig (init_mem CPROOF))));
               simpl.
             eapply schedfail; simpl; eauto.
             -- unfold ThreadPool.containsThread; intros.
             unfold init_machine,init_mach in INIT_ok;
               match goal with
               | [ H: context[semantics.initial_core ?a ?b ?c ?d ?e ?f ] |- _ ] =>
                 destruct (semantics.initial_core a b c d e f) as [[? ?]| ]
               end; inversion INIT_ok; subst.
             simpl. intros HH.
             destruct t; try omega.
            inversion HH.
             -- unfold init_machine,init_mach in INIT_ok;
               match goal with
               | [ H: context[semantics.initial_core ?a ?b ?c ?d ?e ?f ] |- _ ] =>
                 destruct (semantics.initial_core a b c d e f) as [[? ?]| ]
               end; inversion INIT_ok; subst.
                eapply 
                  (DryMachineSource.THE_DRY_MACHINE_SOURCE.DryMachineLemmas.initial_invariant0 (getCurPerm (juicy_mem.m_dry (init_jmem n))) c).
           * intros. eapply IHn'.
    Qed.

    Lemma Initial_dry_ksafety_valid:
      forall (U : semax_invariant.schedule) (n : nat),
      exists init_U init_tr init_st,
        (semantics.initial_core (MachineSemantics U (Some ( getCurPerm (juicy_mem.m_dry (init_jmem n)), empty_map)))) 0 init_genv (juicy_mem.m_dry (init_jmem n)) init_point nil =
        Some ((init_U, init_tr, init_st), None) /\
        forall n' U',
          new_valid  (mk_nstate (U', init_tr, init_st)
                                (proj1_sig (init_mem CPROOF))) U' ->
       ksafe_new_step (globalenv prog) (U', init_tr, init_st)
         (proj1_sig (init_mem CPROOF)) n'.
    Proof.
      intros.
      pose proof (Initial_dry_Csafety_stronger U n).
      destruct H as [init_U [init_tr [init_st [INIT_ok SAFE] ]]].
      do 3 eexists; split; eauto.
      pose proof (init_schedule _ _ _ _ _ _ _ _ _ INIT_ok);
      pose proof (init_trace _ _ _ _ _ _ _ _ _ INIT_ok);
        simpl in *;
        subst.
      pose proof Clight_csafe2ksafe.
      unfold mk_nstate; simpl.
      intros; eapply H; eauto.
    Qed.

End Ksafety_Clight.















(*The following variables represent a program satisfying some CSL*)

(*
Section Clight_safety.
  Variable CPROOF: CSL_proof.
  Definition CS :=   CPROOF.(CSL_CS).
  Definition V :=   CPROOF.(CSL_V).
  Definition G :=   CPROOF.(CSL_G).
  Definition ext_link :=   CPROOF.(CSL_ext_link).
  Definition ext_link_inj :=   CPROOF.(CSL_ext_link_inj).
  Definition prog :=   CPROOF.(CSL_prog).
  Definition all_safe :=   CPROOF.(CSL_all_safe).
  Definition init_mem_not_none :=   CPROOF.(CSL_init_mem_not_none).

    Variables
      (x: block)
      (block: (Genv.find_symbol (globalenv prog) (prog_main (Ctypes.program_of_program prog)) = Some x)).

    Notation init_jmem n:= (initial_jm CPROOF n).
    Notation init_rmap n:=(Some (juicy_mem.m_phi (init_jmem n) )).
    Notation init_genv:=(globalenv prog).
    Notation init_point:=(Vptr (projT1 ((spr CPROOF))) Integers.Int.zero).


    Section Csafety_Clight.
    (** The initial Juicy Machine *)
    Definition js_initial n := initial_machine_state CPROOF n.

    Definition Juicy_safety:=
      safety_initial_state CPROOF.

    Import JuicyMachineModule.THE_JUICY_MACHINE.JuicyMachine.
    (*Import JuicyMachineModule.THE_JUICY_MACHINE.SCH.*)


        Lemma initial_equivalence_trivial:
          forall CPROOF n,
            JuicyMachineModule.THE_JUICY_MACHINE.JSEM.initial_machine
              (juicy_mem.m_phi
                 (initial_jm CPROOF n))
              (initial_corestate CPROOF) =
            initial_machine_state CPROOF n.
        Proof.
          intros; simpl.
          unfold initial_machine_state, JuicyMachineModule.THE_JUICY_MACHINE.JSEM.initial_machine; simpl.
          f_equal.
        Qed.
        
    (*this is showing the similarity between JM's initial machine and CoreSemantics initial machine*)
    Definition CoreInitial U r := (semantics.initial_core (MachineSemantics U r)).
    Lemma initial_equivalence: forall u r n
             (g:JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.G)
             b,
          genv_genv g = Genv.globalenv (Ctypes.program_of_program prog) ->
          b =  projT1 ((spr CPROOF)) ->
          r = Some (juicy_mem.m_phi (initial_jm CPROOF  n)) ->
          CoreInitial u r 0 g
                      (juicy_mem.m_dry (initial_jm CPROOF  n)) (Vptr b Integers.Int.zero) nil =
          Some (u, nil, initial_machine_state CPROOF n, None).
        intros.
        unfold CoreInitial; simpl.
        unfold init_machine, JuicyMachineModule.THE_JUICY_MACHINE.JSEM.init_mach.
        unfold semantics.initial_core.
        unfold ErasureSafety.ErasureProof.JMS.the_sem.
        unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.Sem.
        rewrite JuicyMachineModule.THE_JUICY_MACHINE.SEM.CLN_msem.
        simpl.
        
        rewrite <- initial_equivalence_trivial.
        subst r; simpl.
        unfold initial_corestate.
        unfold prog in *.
        destruct spr as (b' & c' & e & SPR); simpl in *.
        change semax_to_juicy_machine.prog with CSL_prog in *.
        subst b'.
        specialize (SPR n). destruct SPR as [jm [? [? [? _]]]].
        unfold juicy_extspec.j_initial_core in H2.
        unfold semantics.initial_core in H2. simpl in H2.
        rewrite <- H in *.
        destruct (Genv.find_funct_ptr g b) eqn:?H; [ | congruence].
        inversion H3; clear H3; subst.
        f_equal. f_equal. f_equal. f_equal. congruence.
   Qed.
    
    Lemma initial_equivalence': forall U n
             (g:JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.G),
          genv_genv g = Genv.globalenv (Ctypes.program_of_program prog) ->
          (semantics.initial_core (MachineSemantics U (Some (juicy_mem.m_phi (initial_jm CPROOF n)))))
            0 g (proj1_sig (init_mem CPROOF))
            (Vptr (projT1 ((spr CPROOF))) Integers.Int.zero) nil =
                  Some ((U, nil, initial_machine_state CPROOF n), None).
    Proof.
        intros.
        erewrite <- initial_equivalence; eauto.
        unfold CoreInitial. f_equal.
        unfold init_jmem.
        clear.
        destruct spr; simpl. destruct s. destruct p. simpl. destruct s. simpl. destruct a. rewrite H. auto.
    Qed.

    Lemma CoreInitial_juicy_safety:
      forall (U : semax_invariant.schedule) (n : nat),
      exists init_st,
        (semantics.initial_core (MachineSemantics U (init_rmap n))) 
                0 init_genv (proj1_sig (init_mem CPROOF)) init_point nil =
        Some ((U, nil, init_st), None) /\
       forall U',
       csafe (globalenv prog) (U', nil, init_st)
         (proj1_sig (init_mem CPROOF)) n.
    Proof.
      eexists; split.
      rewrite initial_equivalence'; eauto.
      intros U'; eapply Juicy_safety.
    Qed.

    (** *Safety for Clight_new*)
    Import DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryConc.
    Lemma Initial_dry_csafety:
      forall (U : semax_invariant.schedule) (n : nat),
      exists init_U init_tr init_st,
        (semantics.initial_core (MachineSemantics U (Some ( getCurPerm (juicy_mem.m_dry (init_jmem n)), empty_map)))) 0 init_genv (juicy_mem.m_dry (init_jmem n)) init_point nil =
        Some ((init_U, init_tr, init_st), None) /\
        forall U' ,
       csafe (globalenv prog) (U', init_tr, init_st)
         (proj1_sig (init_mem CPROOF)) n.
    Proof.
      intros U n.
      pose proof (CoreInitial_juicy_safety U n).
      destruct H as (init_jmach & INIT_ok & CSAFE).
      eapply ErasureSafety.initial_safety in INIT_ok; eauto.
      - destruct INIT_ok as (ds & INIT_ok & INV & MATCH).
         exists U, nil, ds.
         split.
         rewrite <- INIT_ok. f_equal.
         clear.
         unfold init_jmem. destruct spr; simpl. destruct s; simpl. destruct p; simpl. destruct (s n); simpl.
         destruct a; simpl. auto.
        intros U'.
        eapply ErasureSafety.erasure_safety; eauto; simpl.
        econstructor; eauto.
      - simpl; unfold ErasureSafety.ErasureProof.match_rmap_perm; intros.
        split; auto; simpl.
        rewrite getCurPerm_correct.
        
        admit. (* quite true *)
      - unfold ErasureSafety.ErasureProof.no_locks_perm.
         intros.
         admit. (* quite true *)
 Admitted.


    Lemma dry_initial_state_equality:
    forall (U : semax_invariant.schedule) (n1 n2 : nat),
      (semantics.initial_core (MachineSemantics U (Some ( getCurPerm (juicy_mem.m_dry (init_jmem n1)), empty_map)))) 0 init_genv (juicy_mem.m_dry (init_jmem n1)) init_point nil =
      (semantics.initial_core (MachineSemantics U (Some ( getCurPerm (juicy_mem.m_dry (init_jmem n2)), empty_map)))) 0 init_genv (juicy_mem.m_dry (init_jmem n2)) init_point nil.
    Proof.
      intros; simpl.
      replace (juicy_mem.m_dry (init_jmem n2)) with (juicy_mem.m_dry (init_jmem n1))
       by (unfold init_jmem; simpl;
            destruct spr as (b' & q & Hge & jm ); simpl in *;
            destruct (jm n1) as [? [? ?]], (jm n2) as [? [? ?]]; simpl; congruence).
      unfold init_machine, DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryMachine.init_mach.
      match goal with
      | [  |- context[semantics.initial_core ?a ?b ?c ?d ?e ?f] ] =>
        destruct (semantics.initial_core a b c d e f)
      end; f_equal; f_equal; simpl. destruct p.
      f_equal; f_equal.
    Qed.
    
    Lemma Initial_dry_Csafety_stronger:
      forall (U : semax_invariant.schedule) (n : nat),
      exists init_U init_tr init_st,
        (semantics.initial_core (MachineSemantics U (Some ( getCurPerm (juicy_mem.m_dry (init_jmem n)), empty_map)))) 0 init_genv (juicy_mem.m_dry (init_jmem n)) init_point nil =
        Some ((init_U, init_tr, init_st), None) /\
        forall U' n',
       csafe (globalenv prog) (U', init_tr, init_st)
         (proj1_sig (init_mem CPROOF)) n'.
    Proof.
      intros U n.
      pose proof (Initial_dry_csafety U n) as [init_U [ init_tr [init_st [HH ?]]]].
      do 3 eexists; split; eauto.
      intros U' n'.
      pose proof (Initial_dry_csafety U n') as [init_U' [ init_tr' [init_st' [HH' ?]]]].
      erewrite dry_initial_state_equality in HH'.
      erewrite HH' in HH. inversion HH; subst; auto.
    Qed.
      
End Csafety_Clight. *)

(*Infinite safety*)
Section safety_Clight.
  Import DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryConc.
  Import DryMachineSource.THE_DRY_MACHINE_SOURCE.SCH.
  Import DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryMachine.

  (*First we change validty to preserve bounded memory*)
  Lemma ksafe_new_step_ksafe_new_step_bounded: forall ge ds m,
        (forall (n : nat) (sch : Sch),
            new_valid  (mk_nstate (sch, nil, ds) m) sch ->
          ksafe_new_step ge
                                    (sch, nil, ds) m n) ->
      forall (n : nat) sch,
        new_valid_bound (mk_nstate (sch, nil, ds) m) sch ->
        safety.ksafe new_state Sch
                     (new_step ge) new_valid_bound (*Notice the stronger validity*)
                     (mk_nstate (sch, nil, ds) m) sch n.
    Proof.
      intros ge ds m KSAFE n.
      specialize (KSAFE n).
      generalize ds m KSAFE; clear ds m KSAFE.
      induction n.
      - intros ds m KSAFE sch.
        specialize (KSAFE sch).
        constructor 1.

      - intros ds m KSAFE sch [ VAL BOUND].
        specialize (KSAFE sch VAL).
        inversion KSAFE.
        econstructor ; eauto.
        intros U'' [ VAL'' BOUND''].
        unfold mk_nstate in IHn; simpl in IHn.
        destruct st' as [[tr' ds'] m'].
        cut (tr' = (@nil Events.machine_event)).
        + intros HH; subst tr'.
          eapply IHn; eauto.
          split; eauto.
        + inversion H0.
          * auto.
          * simpl in *; subst.
            inversion H2; simpl in *; auto.
    Qed.

  (* we prove safety that preserves bounded memory*)
  Lemma Initial_bounded_dry_safety:
      forall (U : semax_invariant.schedule) (n : nat),
      exists init_U init_tr init_st,
        (semantics.initial_core (MachineSemantics U (Some ( getCurPerm (juicy_mem.m_dry (init_jmem n)), empty_map)))) 0 init_genv (juicy_mem.m_dry (init_jmem n)) init_point nil =
        Some ((init_U, init_tr, init_st), None) /\
        forall U',
          new_valid_bound (mk_nstate (U', init_tr, init_st) (proj1_sig (init_mem CPROOF))) U' ->
       safe_new_step_bound (globalenv prog) (U', init_tr, init_st)
         (proj1_sig (init_mem CPROOF)).
  Proof.
    intros.
    destruct (Initial_dry_ksafety U n) as (INIT_U & INIT_tr & INIT_st & INIT_ok & SAFE).
    do 3 eexists; split; eauto.
    pose proof (init_schedule _ _ _ _ _ _ _ _ _ INIT_ok);
      pose proof (init_trace _ _ _ _ _ _ _ _ _ INIT_ok);
      simpl in *; subst.
    unfold safe_new_step.
    intros.
    eapply ksafe_safe'; eauto.
    - eapply classic.
    - intros; eapply DryMachineSource.THE_DRY_MACHINE_SOURCE.FiniteBranching.finite_branching.
    -  intros.
       unfold mk_nstate; simpl.
       unfold ksafe_new_step, mk_nstate in SAFE; simpl in SAFE.
       eapply ksafe_new_step_ksafe_new_step_bounded; eauto.
       intros; eapply SAFE.
  Qed.

  (*Facts aboud bounded memory, show it's preserved...*)
  Lemma bounded_mem_step:
            forall ge sm m sm' m',
          MachStep ge sm m sm' m' ->
          bounded_mem m ->
          bounded_mem m'.
    Proof.
      intros.
      inversion H; eauto; simpl in *; subst; eauto.
      -  (* initial *)
         inversion Htstep. subst. apply ClightSemanticsForMachines.ClightSEM.initial_core_nomem in Hinitial; subst om.
         simpl. auto.
      - (*thread step *)
        clear - H0 Htstep .
        inversion Htstep; subst.
        generalize Hcorestep; eauto;  simpl.
        unfold ThreadPool.SEM.Sem,
              DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.SEM.Sem,
              DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.SEM.CLN_evsem.
        intros HH.
        eapply event_semantics.ev_step_ax1 in HH.
        simpl in HH.
        unfold semantics.corestep in HH; simpl in HH.
        unfold semantics.csem in HH; simpl in HH.
        rewrite ClightSemanticsForMachines.ClightSEM.CLN_msem in HH.
        simpl in HH.
        eapply Clight_bounds.CLight_step_mem_bound in HH; eauto.
        eapply Clight_bounds.bounded_getMaxPerm in H0; eauto.
      - (* sync step *)
        inversion Htstep; eauto; simpl in *; subst; auto;
        eapply Clight_bounds.store_bounded; try eapply Hstore;
        eapply Clight_bounds.bounded_getMaxPerm; eauto.      
    Qed.

    Lemma safe_new_step_bound_safe_new_step: forall sch ds m,
        new_valid_bound (nil, ds, m) sch ->
        safe_new_step_bound  (globalenv prog) (sch, nil, ds) m ->
            safe_new_step  (globalenv prog) (sch, nil, ds) m.
    Proof.
      unfold safe_new_step,
              safe_new_step_bound,
              mk_nstate ; simpl; eauto.
      cofix.
      intros sch ds m [ VAL BOUND] SAFE.
      inversion SAFE.
      econstructor; eauto.
      intros.
      assert (new_valid_bound st' U'').
      { split; eauto.
        destruct st' as [[? ?] m']; simpl in *.
        inversion H.
        - simpl in *; subst; auto.
        - simpl in *; subst.
          unfold mk_ostate in H2; simpl in *.
          eapply bounded_mem_step; eauto. }

      destruct st' as [[tr' ds'] m']; simpl in *.

      assert (tr' = nil).
      { inversion H; auto.
        simpl in *; subst.
        inversion H3; simpl in *; subst; auto.
      }

      subst tr'.
      eapply safe_new_step_bound_safe_new_step; eauto.
      Guarded.
    Qed.

    Lemma bounded_empty_mem:
           bounded_mem Mem.empty.
        Proof. intros b0 f.
               intros HH.
               exists 0%Z. exists 0%Z.
               split.
               - intros.
                 unfold getMaxPerm, PMap.map in HH.
                 simpl in HH.
                 rewrite PTree.gleaf in HH; inversion HH.
               - intros.
                 unfold getMaxPerm, PMap.map in HH.
                 simpl in HH.
                 rewrite PTree.gleaf in HH; inversion HH.
        Qed.
    Lemma bounded_initial_mem:
      bounded_mem (proj1_sig (init_mem CPROOF)).
      unfold bounded_mem, bounded_maps.bounded_map, init_mem, init_m.
      destruct CPROOF; simpl in *.
      destruct (Genv.init_mem (Ctypes.program_of_program CSL_prog)) eqn:HH;
          [ | congruence].
      generalize HH; eauto; clear HH. simpl.
      pose (K:= (prog_defs (Ctypes.program_of_program CSL_prog))).
      pose (m':= Mem.empty).
      unfold Genv.init_mem.
      assert ( bounded_mem m').
      { subst; apply bounded_empty_mem. }
      generalize (H); clear H.
      fold K m'.
      generalize (m'); clear m'.
      induction K.
      - intros ? ? HH; inversion HH.
        simpl.
        subst; eauto.
        
      - intros M BM; simpl.
        destruct (Genv.alloc_global (Genv.globalenv (Ctypes.program_of_program CSL_prog)) M a) eqn: AA;
            try solve[intros HH; inversion HH].
          intros HH.
          pose (@Clight_bounds.alloc_global_bounded
                  _ _
                  (Genv.globalenv (Ctypes.program_of_program CSL_prog))
               M m0 a).
          eapply b in BM; eauto.
    Qed.

    Lemma Initial_dry_safety:
      forall (U : semax_invariant.schedule) (n : nat),
      exists init_U init_tr init_st,
        (semantics.initial_core (MachineSemantics U (Some ( getCurPerm (juicy_mem.m_dry (init_jmem n)), empty_map)))) 0 init_genv (juicy_mem.m_dry (init_jmem n)) init_point nil =
        Some ((init_U, init_tr, init_st), None) /\
        forall U',
          new_valid (mk_nstate (U', init_tr, init_st) (proj1_sig (init_mem CPROOF))) U' ->
       safe_new_step_bound (globalenv prog) (U', init_tr, init_st)
         (proj1_sig (init_mem CPROOF)).
  Proof.
    intros.
    destruct (Initial_bounded_dry_safety U n) as
        (INIT_U & INIT_tr & INIT_st & INIT_ok & SAFE).
    do 3 eexists; split; eauto.
    intros; eapply SAFE.
    split; eauto.
    unfold mk_nstate; simpl.
    eapply bounded_initial_mem.
  Qed.
  
  Lemma Initial_dry_safety_concur:
      forall (U : semax_invariant.schedule) (n : nat),
      exists init_st,
        (machine_semantics.initial_machine (new_MachineSemantics U (Some ( getCurPerm (juicy_mem.m_dry (init_jmem n)), empty_map)))) init_genv (juicy_mem.m_dry (init_jmem n)) init_point nil =
        Some (init_st, None) /\
        forall U',
          new_valid (mk_nstate (U', nil, init_st) (proj1_sig (init_mem CPROOF))) U' ->
       safe_new_step_bound (globalenv prog) (U', nil, init_st)
         (proj1_sig (init_mem CPROOF)).
  Proof.
    intros.
    destruct (Initial_dry_safety U n) as
        (INIT_U & INIT_tr & INIT_st & INIT_ok & SAFE).
    exists INIT_st; split; eauto.
    - simpl; unfold init_machine'; simpl.
      simpl in INIT_ok. unfold init_machine in INIT_ok.
      match goal with
      | [ H: context[init_mach ?a ?b ?c ?d ?e] |- _ ] =>
        destruct (init_mach a b c d e) as [[? ?]|] eqn:HH;
          inversion INIT_ok; subst; eauto
      end.
    - eapply init_trace in INIT_ok.
      simpl in INIT_ok; subst.
      eauto.
  Qed.


End safety_Clight.

End Clight_safety.

*)
