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
Require Import VST.concurrency.compiler.Asm_lemmas.
Require Import VST.concurrency.compiler.synchronisation_symulations.
Require Import VST.concurrency.compiler.single_thread_simulation_proof.



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
Require Import VST.concurrency.common.mem_equiv.
Require Import VST.concurrency.lib.pair.
Require Import VST.concurrency.compiler.inject_virtue.
Require Import VST.concurrency.compiler.concur_match.
Require Import VST.concurrency.lib.Coqlib3.

Require Import VST.concurrency.compiler.Lift.


Set Nested Proofs Allowed.
Set Bullet Behavior "Strict Subproofs".

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_definitions.
Import bounded_maps.


Import HybridMachineSig.HybridMachineSig.


(* The self simulation of the CPM 
   allows us to show 
 *)

Section CPM_SelfSimulation.
  Context {CC_correct: CompCert_correctness}
          {Args: ThreadSimulationArguments}.

  Definition self_simulates:
    forall n, ThreadPool (Some n) -> mem -> Prop:=
    fun _ _ _ => True.

  Lemma self_simulates_match:
    forall hb1 (st:ThreadPool (Some hb1)) m,
      (ThreadPool_num_threads st < hb1)%nat ->  
      self_simulates hb1 st m ->
      concur_match hb1 None (Mem.flat_inj (Mem.nextblock m)) st m (lift_state' st) m.
  Proof.
  Admitted.

  Lemma lift_self_simulates:
    forall hb1 hb2 st m, 
      self_simulates hb1 st m ->
      (ThreadPool_num_threads st < hb1)%nat -> 
      (hb1 <= hb2)%nat ->
      self_simulates hb2 (lift_state' st) m.
  Admitted.
  Lemma machine_step_preserves_self_simulates:
    forall n m0 ge U tr st m U' tr' st' m',
      self_simulates n st m ->
      machine_semantics.machine_step (HybConcSem (Some n) m0)
                                     ge U tr st m U' tr' st' m' ->
      self_simulates n st' m'.
  Proof.
  Admitted.


  Lemma thread_step_preserves_self_simulates:
    forall n m0 ge U st m st' m',
      self_simulates n st m ->
      machine_semantics.thread_step (HybConcSem (Some n) m0)
                                    ge U st m st' m' ->
      self_simulates n st' m'.
  Proof.
    
  Admitted.


  Lemma thread_step_star_preserves_self_simulates:
    forall n m0 ge U st m st' m',
      self_simulates n st m ->
      machine_semantics_lemmas.thread_step_star (HybConcSem (Some n) m0)
                                                ge U st m st' m' ->
      self_simulates n st' m'.
  Proof.
    intros. inv H0.
    revert dependent m.
    revert U st st' m'.
    induction x.
    - simpl. intros. inv H1; assumption.
    - simpl; intros. normal_hyp.
      eapply IHx; try eapply H1.
      eapply thread_step_preserves_self_simulates; eauto.
      simpl; eassumption.

      Unshelve.
      all: eauto.
  Qed.
  Lemma thread_step_plus_preserves_self_simulates:
    forall n m0 ge U st m st' m',
      self_simulates n st m ->
      machine_semantics_lemmas.thread_step_plus (HybConcSem (Some n) m0)
                                                ge U st m st' m' ->
      self_simulates n st' m'.
  Proof.
    intros. eapply thread_step_star_preserves_self_simulates; eauto.
    apply machine_semantics_lemmas.thread_step_plus_star; eassumption.
  Qed.

  Lemma self_simulates_initial: 
    forall hb m x4 x2 (x1:ThreadPool (Some hb)) x3 main main_args,
      (hb > 0)%nat ->
      @init_machine'' dryResources
                      (@HybridSem CC_correct Args (@Some nat hb)) 
                      (TP (Some hb))
                      (@DryHybridMachineSig
                         (@HybridSem CC_correct Args (@Some nat hb))
                         (TP (@Some nat hb)))
                      m x4 x2 x1 x3 main main_args ->
      self_simulates hb x1 x3.
  Proof.
    intros * Hpos **.
    inv H. match_case in H1; subst.
    simpl in H1. unfold DryHybridMachine.init_mach in *.
    normal_hyp.
    simpl in *. unfold initial_core_sum in *.
    match_case in H; normal_hyp.
    { contradict H; simpl; omega. }
    subst. simpl.          
  Admitted.

End CPM_SelfSimulation.