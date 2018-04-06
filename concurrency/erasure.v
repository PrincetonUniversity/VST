(** *This FILE IS DEPRICATED                 *)
(** *I'm moving some lemmas before erasing it*)
(** * Please see: erasure_signature.v        *)





















Require Import compcert.common.Memory.

(* The concurrent machinery*)
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.HybridMachineSig.
Require Import VST.concurrency.juicy_machine. Import Concur.
Require Import VST.concurrency.HybridMachine. Import Concur.

(*The simulations*)
Require Import VST.sepcomp.wholeprog_simulations.

Definition init_inj_ok (j: Values.Val.meminj) m:=
  forall b b' ofs, j b = Some (b', ofs) ->
              b = b' /\
              Mem.valid_block m b.

Module Type ErasureSig.

  Declare Module SCH: Scheduler with Module TID:=NatTID.
  Declare Module SEM: Semantics.
  Import SCH SEM.

  Declare Module JSIG: ConcurrentMachineSig
      with Module ThreadPool.TID:= NatTID
      with Module ThreadPool.SEM:= SEM.
  Declare Module JuicyMachine: ConcurrentMachine
      with Module SCH:=SCH
      with Module SIG:= JSEM.
  Notation JMachineSem:= JuicyMachine.MachineSemantics.
  Notation jstate:= JSEM.ThreadPool.t.
  Notation jmachine_state:= JuicyMachine.MachState.


  Declare Module DSIG: ConcurrentMachineSig
      with Module ThreadPool.TID:= NatTID
      with Module ThreadPool.SEM:= SEM.
  Declare Module DryMachine: ConcurrentMachine
      with Module SCH:=SCH
      with Module SIG:= DSEM.
  Notation DMachineSem:= DryMachine.MachineSemantics.
  Notation dstate:= DSEM.ThreadPool.t.
  Notation dmachine_state:= DryMachine.MachState.

  (*Parameter parch_state : jstate ->  dstate.*)
  Parameter match_st : jstate ->  dstate -> Prop.

  (*match axioms*)
  Axiom MTCH_cnt: forall {js tid ds},
           match_st js ds ->
           JSEM.ThreadPool.containsThread js tid -> DSEM.ThreadPool.containsThread ds tid.
  Axiom MTCH_cnt': forall {js tid ds},
           match_st js ds ->
           DSEM.ThreadPool.containsThread ds tid -> JSEM.ThreadPool.containsThread js tid.

       Axiom  MTCH_getThreadC: forall js ds tid c,
           forall (cnt: JSEM.ThreadPool.containsThread js tid)
             (cnt': DSEM.ThreadPool.containsThread ds tid)
             (M: match_st js ds),
             JSEM.ThreadPool.getThreadC cnt =  c ->
             DSEM.ThreadPool.getThreadC cnt'  =  c.

       Axiom MTCH_compat: forall js ds m,
           match_st js ds ->
         JSEM.mem_compatible js m ->
         DSEM.mem_compatible ds m.

       Axiom MTCH_updt:
           forall js ds tid c
             (H0:match_st js ds)
             (cnt: JSEM.ThreadPool.containsThread js tid)
             (cnt': DSEM.ThreadPool.containsThread ds tid),
             match_st (JSEM.ThreadPool.updThreadC cnt c)
                       (DSEM.ThreadPool.updThreadC cnt' c).

  Variable genv: G.
  Variable main: Values.val.
  Variable match_rmap_perm: JuicyMachine.SIG.ThreadPool.RES.res -> DryMachine.SIG.ThreadPool.RES.res -> Prop.
  Axiom init_diagram:
    forall (j : Values.Val.meminj) (U:schedule) (js : jstate)
      (vals : list Values.val) (m : mem) rmap pmap,
      init_inj_ok j m ->
      match_rmap_perm rmap pmap ->
   initial_core (JMachineSem U (Some rmap)) genv main vals = Some (U, js) ->
   exists (mu : SM_Injection) (ds : dstate),
     as_inj mu = j /\
     initial_core (DMachineSem U (Some pmap)) genv main vals = Some (U, ds) /\
     DSEM.invariant ds /\
     match_st js ds.

  Axiom core_diagram:
    forall (m : mem)  (U0 U U': schedule) rmap pmap
     (ds : dstate) (js js': jstate)
     (m' : mem),
   corestep (JMachineSem U0 rmap) genv (U, js) m (U', js') m' ->
   match_st js ds ->
   DSEM.invariant ds ->
   exists (ds' : dstate),
     DSEM.invariant ds' /\
     match_st js' ds' /\
     corestep (DMachineSem U0 pmap) genv (U, ds) m (U', ds') m'.

  Axiom halted_diagram:
    forall U ds js  rmap pmap,
      fst js = fst ds ->
      halted (JMachineSem U rmap) js = halted (DMachineSem U pmap) ds.

End ErasureSig.

Module ErasureFnctr (PC:ErasureSig).
  Module SEM:=PC.SEM.
  Import PC SEM DryMachine.SCH.

  (* remove all of this Parameter halt_inv: SM_Injection ->
                      G -> Values.val -> M ->
                      G -> Values.val -> M -> Prop.
  remove all of thisParameter init_inv: Values.Val.meminj ->
                      G ->  list Values.val -> M ->
                      G ->  list Values.val -> M ->  Prop.*)
  (*remove all of this Erasure is about drying memory. So the invariants are trivial. *)
    Inductive init_inv:  Values.Val.meminj ->
                       G -> list Values.val -> mem ->
                       G -> list Values.val -> mem -> Prop:=
    |InitEq: forall j g1 args1 m1 g2 args2 m2,
        g1 = g2 ->
        args1 = args2 ->
        m1 = m2 ->
        init_inj_ok j m1 ->
        init_inv j g1 args1 m1 g2 args2 m2.

    Inductive halt_inv:  Values.Val.meminj ->
                         G -> Values.val -> mem ->
                         G -> Values.val -> mem -> Prop:=
    |HaltEq: forall j g1 args1 m1 g2 args2 m2,
        g1 = g2 ->
        args1 = args2 ->
        m1 = m2 ->
        halt_inv j g1 args1 m1 g2 args2 m2.

  Definition ge_inv: G -> G -> Prop:= @eq G.
  Definition core_data:= unit.
  Definition core_ord: unit-> unit -> Prop := fun _ _ => False.

  (*States match if the dry part satisfies the invariant and the substates match.*)
  Inductive match_state :
    core_data ->  Values.Val.meminj -> jmachine_state ->  mem -> dmachine_state -> mem -> Prop:=
    MATCH: forall d j js ds U m,
      DSEM.invariant ds -> (*This could better go inside the state... but it's fine here. *)
      match_st js ds ->
      match_state d j  (U, js) m (U, ds) m.



  Lemma core_ord_wf:  well_founded core_ord.
  Proof. constructor; intros y H; inversion H. Qed.

  Theorem erasure: forall U rmap pmap,
      PC.match_rmap_perm rmap pmap ->
      Wholeprog_sim.Wholeprog_sim
        (JMachineSem U (Some rmap)) (DMachineSem U (Some pmap))
        PC.genv PC.genv
        PC.main
        ge_inv init_inv halt_inv.
  Proof.
    intros U rmap pmap init_OK.
    apply (Wholeprog_sim.Build_Wholeprog_sim
             (JMachineSem U (Some rmap)) (DMachineSem U (Some pmap))
             PC.genv PC.genv
             PC.main
             ge_inv init_inv halt_inv
             core_data match_state core_ord core_ord_wf).
    - reflexivity.
    - intros until m2; intros H H0.
      inversion H0; subst. clear - H4 H init_OK.
      destruct c1 as [U0 js].
      assert (HH:=JuicyMachine.initial_schedule _ _ _ _ _ _ _ H); subst U0.
      destruct (init_diagram j U js vals2 m2 rmap pmap H4 init_OK H) as [mu [dms [injeq [IC [DINV MS] ]]]].
      exists tt, (U,dms); intuition.
      constructor; assumption.
    - intros until m2; intros MTCH.
      inversion MTCH; subst; clear MTCH.
      destruct st1' as [U' js'].
      destruct (core_diagram m2 U U0 U' (Some rmap) (Some pmap) ds js js' m1' H H1 H0) as
          [ds' [DINV [MTCH CORE]]].
      exists (U', ds'), m1', tt, mu. split.
      + constructor; assumption.
      + left; apply semantics_lemmas.corestep_plus_one; assumption.
    - intros until v1; intros MTCH.
      inversion MTCH; subst.
      intros. exists mu, v1.
      split; auto.
      constructor; reflexivity.
      rewrite <- H1; symmetry. (apply halted_diagram); reflexivity.
  Qed.

End ErasureFnctr.
