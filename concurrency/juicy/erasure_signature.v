
(** Erasure Signature  *)

(** Describes the specification of the erasure in two parts:
    1. Signature: Describes the axioms required to prove an erasure.
    2. Functor: Using the axioms, sets up the erasure theorem/results

    NOTE: Seems like the Functor is not used. TODO, remove the functor or
    rewrite it as a simulation (come back after erasure_proof / erasure_safety).
 *)

Require Import compcert.common.Memory.

(* The concurrent machinery*)
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.juicy.juicy_machine. Import Concur.
Require Import VST.concurrency.common.HybridMachine.

(*The simulations*)
Definition init_inj_ok (j: Values.Val.meminj) m:=
  forall b b' ofs, j b = Some (b', ofs) ->
              b = b' /\
              Mem.valid_block m b.

Module Type ErasureSig.

  (*  Module SCH: Scheduler with Module TID:=NatTID:= THESCH.
  Import SCH.*)

  Import HybridMachineSig.

  Declare Instance Sem (ge : Clight.genv) : Semantics.

  Declare Instance JR : Resources.
  Declare Instance JTP (ge : Clight.genv) : ThreadPool.ThreadPool(Sem := Sem ge).
  Declare Instance JMS (ge : Clight.genv) : MachineSig(ThreadPool := JTP ge).
  Declare Instance DilMem : DiluteMem.
  Declare Instance scheduler : Scheduler.
  Declare Instance JuicyMachine (ge : Clight.genv) : HybridMachine(machineSig:=JMS ge).
  Notation JMachineSem ge := (MachineSemantics(HybridMachine := JuicyMachine ge)).
  Notation jres := (@res JR).
  Notation jstate ge := (@ThreadPool.t _ _ (JTP ge)).
  Notation jmachine_state ge := (@MachState _ _ (JTP ge)).
  Declare Instance DR : Resources.
  Declare Instance DTP (ge : Clight.genv) : ThreadPool.ThreadPool(Sem := Sem ge).
  Declare Instance DMS (ge : Clight.genv) : MachineSig(ThreadPool := DTP ge).
  Declare Instance DryMachine (ge : Clight.genv) : HybridMachine(machineSig := DMS ge).
  Notation DMachineSem ge := (MachineSemantics(HybridMachine := DryMachine ge)).
  Notation dres := (@res DR).
  Notation dstate ge := (@ThreadPool.t _ _ (DTP ge)).
  Notation dmachine_state ge := (@MachState _ _ (DTP ge)).

  (*Parameter parch_state : jstate ->  dstate.*)
  Parameter match_st : forall (ge : Clight.genv), jstate ge -> dstate ge -> Prop.

  (*match axioms*)
  Axiom MTCH_cnt: forall {ge js tid ds},
      match_st ge js ds ->
      ThreadPool.containsThread js tid -> ThreadPool.containsThread ds tid.
  Axiom MTCH_cnt': forall {ge js tid ds},
      match_st ge js ds ->
      ThreadPool.containsThread ds tid -> ThreadPool.containsThread js tid.

  Axiom  MTCH_getThreadC: forall ge js ds tid c,
      forall (cnt: ThreadPool.containsThread js tid)
        (cnt': ThreadPool.containsThread ds tid)
        (M: match_st ge js ds),
        ThreadPool.getThreadC cnt =  c ->
        ThreadPool.getThreadC cnt'  =  c.

  Axiom MTCH_compat: forall ge js ds m,
      match_st ge js ds ->
      mem_compatible js m ->
      mem_compatible ds m.

  Axiom MTCH_updt:
    forall ge js ds tid c
      (H0:match_st ge js ds)
      (cnt: ThreadPool.containsThread js tid)
      (cnt': ThreadPool.containsThread ds tid),
      match_st ge (ThreadPool.updThreadC cnt c)
               (ThreadPool.updThreadC cnt' c).

  (*Variable genv: G.
  Variable main: Values.val.*)
(*  Variable match_rmap_perm: jres -> dres -> Prop.
  Variable no_locks_perm: jres ->  Prop.


  Axiom init_diagram:
    forall ge (j : Values.Val.meminj) (U:_) (js : jstate ge)
      (vals : list Values.val) (m m' : mem)
      (rmap: jres) (pmap: dres) main h,
      init_inj_ok j m ->
      match_rmap_perm rmap pmap ->
      no_locks_perm rmap ->
      initial_core (JMachineSem ge U (Some rmap)) h m (U, nil, js) m' main vals ->
      exists (ds : dstate ge),
        initial_core (DMachineSem ge U (Some pmap)) h m (U, nil, ds) m' main vals /\
        invariant ds /\
        match_st ge js ds.*)
(* There's no good generic way to describe the actual initial state, since it depends on the
   relationship between initial rmap/pmap and memory. *)

  Axiom core_diagram:
    forall ge (m : mem)  (U0 U U': _) rmap pmap
      (ds : dstate ge) dtr (js js': jstate ge) jtr jtr'
      (m' : mem),
      corestep (JMachineSem ge U0 rmap) (U, jtr, js) m (U', jtr', js') m' ->
      match_st ge js ds ->
      invariant ds ->
      exists (ds' : dstate ge),
        invariant ds' /\
        match_st ge js' ds' /\
        exists dtr', corestep (DMachineSem ge U0 pmap) (U, dtr, ds) m (U', app dtr dtr', ds') m'.

  Axiom halted_diagram:
    forall ge U (ds : dmachine_state ge) (js : jmachine_state ge)  rmap pmap,
      fst (fst js) = fst (fst ds) ->
      halted (JMachineSem ge U rmap) js = halted (DMachineSem ge U pmap) ds.

End ErasureSig.

Module ErasureFnctr (PC:ErasureSig).
  Import HybridMachineSig PC.

  Section ErasureFnctr.

    Context (ge : Clight.genv).
    Notation jres := (@res JR).
    Notation jstate := (@ThreadPool.t _ _ (JTP ge)).
    Notation jmachine_state := (@MachState _ _ (JTP ge)).
    Notation dres := (@res DR).
    Notation dstate := (@ThreadPool.t _ _ (DTP ge)).
    Notation dmachine_state := (@MachState _ _ (DTP ge)).
    Instance DMS : MachineSig(ThreadPool := DTP ge) := DMS ge.
    Instance Sem : Semantics := Sem ge.
    Notation match_st := (match_st ge).

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

    (*Wholeprog comes from compcomp. Should remove?*) 
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
