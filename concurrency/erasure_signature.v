Require Import compcert.common.Memory.

(* The concurrent machinery*)
Require Import VST.concurrency.threadPool.
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.TheSchedule.
Require Import VST.concurrency.HybridMachineSig.
Require Import VST.concurrency.semantics.
Require Import VST.concurrency.juicy_machine. Import Concur.
Require Import VST.concurrency.HybridMachine. Import Concur.

(*The simulations*)
Require Import VST.sepcomp.wholeprog_simulations.

Definition init_inj_ok (j: Values.Val.meminj) m:=
  forall b b' ofs, j b = Some (b', ofs) ->
              b = b' /\
              Mem.valid_block m b.

Module Type ErasureSig.

(*  Module SCH: Scheduler with Module TID:=NatTID:= THESCH.
  Import SCH.*)

  Import HybridMachineSig.

  Declare Instance Sem : Semantics.

  Declare Instance JR : Resources.
  Declare Instance JTP : ThreadPool.ThreadPool.
  Declare Instance JMS : MachineSig.
  Declare Instance JuicyMachine : HybridMachine.
  Notation JMachineSem := (MachineSemantics(HybridMachine := JuicyMachine)).
  Notation jres := (@res JR).
  Notation jstate := (@ThreadPool.t _ _ JTP).
  Notation jmachine_state := (@MachState _ _ JTP).
  Declare Instance DR : Resources.
  Declare Instance DTP : ThreadPool.ThreadPool.
  Declare Instance DMS : MachineSig.
  Declare Instance DryMachine : HybridMachine.
  Notation DMachineSem := (MachineSemantics(HybridMachine := DryMachine)).
  Notation dres := (@res DR).
  Notation dstate := (@ThreadPool.t _ _ DTP).
  Notation dmachine_state := (@MachState _ _ DTP).

  (*Parameter parch_state : jstate ->  dstate.*)
  Parameter match_st : jstate ->  dstate -> Prop.

  (*match axioms*)
  Axiom MTCH_cnt: forall {js tid ds},
           match_st js ds ->
           ThreadPool.containsThread js tid -> ThreadPool.containsThread ds tid.
  Axiom MTCH_cnt': forall {js tid ds},
           match_st js ds ->
           ThreadPool.containsThread ds tid -> ThreadPool.containsThread js tid.

       Axiom  MTCH_getThreadC: forall js ds tid c,
           forall (cnt: ThreadPool.containsThread js tid)
             (cnt': ThreadPool.containsThread ds tid)
             (M: match_st js ds),
             ThreadPool.getThreadC cnt =  c ->
             ThreadPool.getThreadC cnt'  =  c.

       Axiom MTCH_compat: forall js ds m,
           match_st js ds ->
         mem_compatible js m ->
         mem_compatible ds m.

       Axiom MTCH_updt:
           forall js ds tid c
             (H0:match_st js ds)
             (cnt: ThreadPool.containsThread js tid)
             (cnt': ThreadPool.containsThread ds tid),
             match_st (ThreadPool.updThreadC cnt c)
                       (ThreadPool.updThreadC cnt' c).

  (*Variable genv: G.
  Variable main: Values.val.*)
       Variable match_rmap_perm: jres -> dres -> Prop.
       Variable no_locks_perm: jres ->  Prop.


Axiom init_diagram:
    forall (j : Values.Val.meminj) (U:_) (js : jstate)
      (vals : list Values.val) (m : mem)
      (rmap: jres)
      (pmap: dres)
      main genv h,
      init_inj_ok j m ->
      match_rmap_perm rmap pmap ->
      no_locks_perm rmap ->
   initial_core (JMachineSem U (Some rmap)) h genv m main vals = Some ((U, nil, js),None) ->
   exists (ds : dstate),
     initial_core (DMachineSem U (Some pmap)) h genv m main vals = Some ((U, nil, ds),None) /\
     invariant ds /\
     match_st js ds.

  Axiom core_diagram:
    forall (m : mem)  (U0 U U': _) rmap pmap
     (ds : dstate) dtr (js js': jstate) jtr jtr'
     (m' : mem) genv,
   corestep (JMachineSem U0 rmap) genv (U, jtr, js) m (U', jtr', js') m' ->
   match_st js ds ->
   invariant ds ->
   exists (ds' : dstate),
     invariant ds' /\
     match_st js' ds' /\
     exists dtr', corestep (DMachineSem U0 pmap) genv (U, dtr, ds) m (U', dtr', ds') m'.

  Axiom halted_diagram:
    forall U (ds : dmachine_state) (js : jmachine_state)  rmap pmap,
      fst (fst js) = fst (fst ds) ->
      halted (JMachineSem U rmap) js = halted (DMachineSem U pmap) ds.

End ErasureSig.

Module ErasureFnctr (PC:ErasureSig).
  Import HybridMachineSig PC.

  Section ErasureFnctr.

  Notation jres := (@res JR).
  Notation jstate := (@ThreadPool.t _ _ JTP).
  Notation jmachine_state := (@MachState _ _ JTP).
  Notation dres := (@res DR).
  Notation dstate := (@ThreadPool.t _ _ DTP).
  Notation dmachine_state := (@MachState _ _ DTP).
  Existing Instance DMS.


  (*Parameter halt_inv: SM_Injection ->
                      G -> Values.val -> M ->
                      G -> Values.val -> M -> Prop.
  Parameter init_inv: Values.Val.meminj ->
                      G ->  list Values.val -> M ->
                      G ->  list Values.val -> M ->  Prop.*)
  (*Erasure is about drying memory. So the invariants are trivial. *)
    Inductive init_inv:  Values.Val.meminj ->
                       semG -> list Values.val -> mem ->
                       semG -> list Values.val -> mem -> Prop:=
    |InitEq: forall j g1 args1 m1 g2 args2 m2,
        g1 = g2 ->
        args1 = args2 ->
        m1 = m2 ->
        init_inj_ok j m1 ->
        init_inv j g1 args1 m1 g2 args2 m2.

    Inductive halt_inv:  Values.Val.meminj ->
                         semG -> Values.val -> mem ->
                         semG -> Values.val -> mem -> Prop:=
    |HaltEq: forall j g1 args1 m1 g2 args2 m2,
        g1 = g2 ->
        args1 = args2 ->
        m1 = m2 ->
        halt_inv j g1 args1 m1 g2 args2 m2.

  Definition ge_inv: semG -> semG -> Prop:= @eq semG.
  Definition core_data:= unit.
  Definition core_ord: unit-> unit -> Prop := fun _ _ => False.

  (*States match if the dry part satisfies the invariant and the substates match.*)
  Inductive match_state :
    core_data ->  Values.Val.meminj -> jmachine_state ->  mem -> dmachine_state -> mem -> Prop:=
    MATCH: forall d j js ds U m,
      invariant ds -> (*This could better go inside the state... but it's fine here. *)
      match_st js ds ->
      match_state d j  (U, nil, js) m (U, nil, ds) m.



  Lemma core_ord_wf:  well_founded core_ord.
  Proof. constructor; intros y H; inversion H. Qed.

  (*Wholeprog simulation depends on structured injections... temp-remove*)
  (*Theorem erasure: forall U rmap pmap main genv,
      PC.match_rmap_perm rmap pmap ->
      PC.no_locks_perm rmap ->
      Wholeprog_sim.Wholeprog_sim
        (JMachineSem U (Some rmap)) (DMachineSem U (Some pmap))
        genv genv
        main
        ge_inv init_inv halt_inv.
  Proof. intros U rmap pmap main genv init_OK no_locks.
         apply (Wholeprog_sim.Build_Wholeprog_sim
                  (JMachineSem U (Some rmap)) (DMachineSem U (Some pmap))
                  genv genv
                  main
                  ge_inv init_inv halt_inv
                  core_data match_state core_ord core_ord_wf).
    - reflexivity.
    - intros until m2; intros h H H0.
      inversion H0; subst. clear - H4 H init_OK no_locks.
      destruct c1 as [[U0 tr0] js].
      assert (HH:=JuicyMachine.initial_schedule _ _ _ _ _ _ _ tr0 h H).
      destruct HH. subst U0 tr0.
      destruct (init_diagram j U js vals2 m2 rmap pmap main genv h H4 init_OK no_locks H) as [mu [dms [injeq [IC [DINV MS] ]]]].
      exists tt, (U,nil,dms); intuition.
      constructor; assumption.
    - intros until m2; intros MTCH.
      inversion MTCH; subst; clear MTCH.
      destruct st1' as [[U' tr1'] js'].
      assert (H' := H).
      apply jstep_empty_trace in H'. destruct H'; subst.
      destruct (core_diagram m2 U U0 U' (Some rmap) (Some pmap) ds js js' m1' genv H H1 H0) as
          [ds' [DINV [MTCH CORE]]].
      exists (U', nil, ds'), m1', tt, mu. split.
      + constructor; assumption.
      + left; apply semantics_lemmas.corestep_plus_one; assumption.
    - intros until v1; intros MTCH.
      inversion MTCH; subst.
      intros. exists mu, v1.
      split; auto.
      constructor; reflexivity.
      rewrite <- H1; symmetry. (apply halted_diagram); reflexivity.
  Qed.*)

  End ErasureFnctr.

End ErasureFnctr.
