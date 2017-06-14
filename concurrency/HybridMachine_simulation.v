From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrfun.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.

Require Import msl.Axioms.
Require Import Coq.ZArith.ZArith.
Require Import sepcomp.semantics.
Require Import sepcomp.event_semantics.
Require Export concurrency.semantics.
Require Export concurrency.lksize.
Require Import concurrency.threadPool. Export threadPool.

Require Import concurrency.machine_semantics.
Require Import concurrency.permissions.
Require Import concurrency.bounded_maps.
Require Import concurrency.addressFiniteMap.

Require Import concurrency.scheduler.
Require Import Coq.Program.Program.

Require Import concurrency.safety.

Require Import concurrency.coinductive_safety.


Require Import concurrency.concurrent_machine_rec.

Require Import veric.res_predicates.
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import ccc26x86.Asm_coop.
Require Import ccc26x86.Asm_event.

Require Import concurrency.HybridMachineSig.
Require Import concurrency.HybridMachine.

Require Import concurrency.CoreSemantics_sum.

Require Import compcert.common.Smallstep.

Require Import concurrency.machine_semantics_lemmas.


Section HybridSimulation.

  Variable (Sems Semt : Semantics_rec).
  Variable (hb1 hb2: option nat).

  Definition Resources : Resources_rec:=
    Build_Resources_rec (access_map * access_map)%type (access_map * access_map)%type.
  
  Definition HM1:=HybridMachine hb1 Sems Semt.
  Definition HM2:=HybridMachine hb2 Sems Semt.

  Variable U: seq.seq nat.

  (*I use none, but it should be the initial memory. FIX. *)
  Definition Sem1:=(ConcurMachineSemantics _ _ _ HM1 U None).
  Definition Sem2:=(ConcurMachineSemantics _ _ _ HM2 U None) .
  
  Notation C1:= (t_ (ThreadPool hb1 Sems Semt)).
  Notation C2:= (t_ (ThreadPool hb2 Sems Semt)).
  Definition G:= (semG Sems * semG Semt)%type.
  Variable ge:G.
  Variable (ge_inv: G -> G -> Prop).

  
  Variable init_inv : meminj -> G -> list val -> mem -> G -> list val -> mem -> Prop.

  Variable halt_inv : (*SM_Injection*)meminj -> G -> val -> mem -> G -> val -> mem -> Prop.

  Variable core_data: Type.
  Variable core_ord : core_data -> core_data -> Prop.
  Variable core_ord_wf : well_founded core_ord.
  Variable thread_match : core_data -> (*SM_Injection*)meminj -> (semC Sems) -> mem -> (semC Semt) -> mem -> Prop.
  Variable source_match : (*SM_Injection*)meminj -> (semC Sems) -> mem -> (semC Sems) -> mem -> Prop.
  Variable target_match : (*SM_Injection*)meminj -> (semC Semt) -> mem -> (semC Semt) -> mem -> Prop.


Definition order_option (d1 d2: (option core_data)):=
  match d1, d2 with
  | None, None => True
  | None, _ => True
  | Some d1', Some d2' => core_ord d1' d2'
  | _, _ => False
  end.
Fixpoint core_ord_list (ls1 ls2: list (option core_data)): Prop:=
    match ls1, ls2 with
    | nil, nil => True
    | d1::ls1',d2::ls2' => order_option d1 d2 /\ core_ord_list ls1' ls2' 
    | _, _ => False
    end.

(*This will probably need reworking*)
Record concur_match
           (data: list (option core_data)) (j:meminj) (cstate1: C1) (m1: mem) (cstate2: C2) (m2: mem):=
  { same_length: num_threads cstate1 = num_threads cstate2
    ; mtch_source:
        forall (i:nat) (cnti1: containsThread cstate1 i) (cnti2: containsThread cstate2 i)
          (memcompat1: mem_compatible _ _ _ cstate1 m1)
          (memcompat2: mem_compatible _ _ _ cstate2 m2),
        forall code1 res1 code2 res2,
        getThreadC cnti1 = Krun (SState _ _ code1) ->
        getThreadR cnti1 = res1 ->
        getThreadC cnti2 = Krun (SState _ _ code2) ->
        getThreadR cnti2 = res2 ->
        source_match j code1 (restrPermMap (memcompat1 i cnti1).1) code2 (restrPermMap (memcompat2 i cnti2).1)
    ; mtch_target:
        forall (i:nat) (cnti1: containsThread cstate1 i) (cnti2: containsThread cstate2 i)
          (memcompat1: mem_compatible _ _ _ cstate1 m1)
          (memcompat2: mem_compatible _ _ _ cstate2 m2),
        forall code1 res1 code2 res2,
        getThreadC cnti1 = Krun (TState _ _ code1) ->
        getThreadR cnti1 = res1 ->
        getThreadC cnti2 = Krun (TState _ _ code2) ->
        getThreadR cnti2 = res2 ->
        target_match j code1 (restrPermMap (memcompat1 i cnti1).1) code2 (restrPermMap (memcompat2 i cnti2).1)
    ; mtch_hybrid:
        forall (i:nat) (cnti1: containsThread cstate1 i) (cnti2: containsThread cstate2 i)
          (memcompat1: mem_compatible _ _ _ cstate1 m1)
          (memcompat2: mem_compatible _ _ _ cstate2 m2),
        forall code1 res1 code2 res2 d,
        getThreadC cnti1 = Krun (SState _ _ code1) ->
        getThreadR cnti1 = res1 ->
        getThreadC cnti2 = Krun (TState _ _ code2) ->
        getThreadR cnti2 = res2 ->
        nth i data None = Some d -> 
        thread_match d j code1 (restrPermMap (memcompat1 i cnti1).1) code2 (restrPermMap (memcompat2 i cnti2).1)
    ; correct_type_source1:
        forall (i:nat) (cnti1: containsThread cstate1 i) c x,
          lt_op i hb1 ->
          getThreadC cnti1 = Krun c \/
          getThreadC cnti1 = Kblocked c \/
          getThreadC cnti1 = Kresume c x ->
          exists c', c = SState _ _ c' 
    ; correct_type_target1:
        forall (i:nat) (cnti1: containsThread cstate1 i) c x,
          ~ lt_op i hb1 ->
          getThreadC cnti1 = Krun c \/
          getThreadC cnti1 = Kblocked c \/
          getThreadC cnti1 = Kresume c x ->
          exists c', c = TState _ _ c' 
    ; correct_type_source2:
        forall (i:nat) (cnti1: containsThread cstate1 i) c x,
          lt_op i hb2 ->
          getThreadC cnti1 = Krun c \/
          getThreadC cnti1 = Kblocked c \/
          getThreadC cnti1 = Kresume c x ->
          exists c', c = SState _ _ c' 
    ; correct_type_target2:
        forall (i:nat) (cnti1: containsThread cstate1 i) c x,
          ~ lt_op i hb2 ->
          getThreadC cnti1 = Krun c \/
          getThreadC cnti1 = Kblocked c \/
          getThreadC cnti1 = Kresume c x ->
          exists c', c = TState _ _ c' 
        
  } .
  
  Record HybridMachine_simulation main:=
    { genv_inv : ge_inv ge ge
      ; core_initial :
          forall j c1 vals1 m1 vals2 m2,
            machine_semantics.initial_machine Sem1 ge main vals1 = Some c1 ->
            init_inv j ge vals1 m1 ge vals2 m2 ->
    exists (*mu*) cd c2,
      (*as_inj mu = j*
      /\*) machine_semantics.initial_machine Sem2 ge main vals2 = Some c2
           /\ concur_match cd j c1 m1 c2 m2
      ; thread_diagram :
          forall U st1 m1 st1' m1',
            machine_semantics.thread_step Sem1 ge U st1 m1 st1' m1' ->
            forall cd st2 mu m2,
              concur_match cd mu st1 m1 st2 m2 ->
              exists st2', exists m2', exists cd', exists mu',
                      concur_match cd' mu' st1' m1' st2' m2'
                      /\ (thread_step_plus Sem2 ge U st2 m2 st2' m2'
               \/ (thread_step_star Sem2 ge U st2 m2 st2' m2' /\ core_ord_list cd' cd))
      ; machine_diagram :
          forall U tr st1 m1 U' tr' st1' m1',
            machine_semantics.machine_step Sem1 ge U tr st1 m1 U' tr' st1' m1' ->
            forall cd st2 mu m2,
              concur_match cd mu st1 m1 st2 m2 ->
              exists st2', exists m2', exists cd', exists mu',
                      concur_match cd' mu' st1' m1' st2' m2'
                      /\ machine_semantics.machine_step Sem2 ge U tr st2 m2 U' tr' st2' m2'
      ; thread_halted :
          forall cd mu U c1 m1 c2 m2 v1,
            concur_match cd mu c1 m1 c2 m2 ->
            conc_halted Sem1 U c1 = Some v1 ->
            exists j v2,
              halt_inv j ge v1 m1 ge v2 m2
              /\ conc_halted Sem2 U c2 = Some v2
      ; thread_running:
          forall cd mu c1 m1 c2 m2 ,
            concur_match cd mu c1 m1 c2 m2 ->
            forall i, runing_thread Sem1 c1 i <-> runing_thread Sem2 c2 i
            (* runing_thread Sem1 c1 = runing_thread Sem2 c2 *)
 }.



  End HybridSimulation.