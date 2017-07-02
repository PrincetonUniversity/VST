Require Import Coq.Bool.Bool.

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.structured_injections.
Require Import sepcomp.reach.
Require Import sepcomp.mem_wd.

Require Import concurrency.machine_semantics.
Require Import concurrency.machine_semantics_lemmas.

Section Machine_sim.

Context {G1 TID SCH TR C1 G2 C2 : Type}

(Sem1 : @ConcurSemantics G1 TID SCH TR C1 mem)
(Sem2 : @ConcurSemantics G2 TID SCH TR C2 mem)

(ge1 : G1)
(ge2 : G2)

(main : val).

(*
Variable ge_inv : G1 -> G2 -> Prop.

Variable init_inv : meminj -> G1 -> list val -> M1 -> G2 -> list val -> M2 -> Prop.

Variable halt_inv : (*SM_Injection*)meminj -> G1 -> val -> M1 -> G2 -> val -> M2 -> Prop.
*)

Definition smthng_about_globals {G} (g:G) (j:meminj):= True.
Record Machine_sim: Type :=
  { MSdata : Type ;
    MSmatch_states : MSdata -> (*SM_Injection*)meminj -> C1 -> mem -> C2 -> mem -> Prop ;
    MSorder : MSdata -> MSdata -> Prop;
    
 MSord_wf : well_founded MSorder
; core_initial :
    forall j c1 vals1 m1 m1' vals2 m2 m2',
    initial_machine Sem1 ge1 m1 main vals1 = Some (c1, m1') ->
      Mem.inject j m1 m2 ->
      Forall2 (val_inject j) vals1 vals2 ->
      (*
      meminj_preserves_globals ge1 j ->
      globalfunction_ptr_inject ge1 j ->*)
      smthng_about_globals ge1 j ->
    exists (*mu*) cd c2,
      (*as_inj mu = j*
      /\*) initial_machine Sem2 ge2 m2 main vals2 = Some (c2, m2')
      /\ MSmatch_states cd j c1 (option_proj m1 m1') c2 (option_proj m2 m2')
; MSthread_diagram :
    forall U st1 m1 st1' m1',
    thread_step Sem1 ge1 U st1 m1 st1' m1' ->
    forall cd st2 mu m2,
    MSmatch_states cd mu st1 m1 st2 m2 ->
    exists st2', exists m2', exists cd', exists mu',
    MSmatch_states cd' mu' st1' m1' st2' m2'
    /\ (thread_step_plus Sem2 ge2 U st2 m2 st2' m2'
       \/ (thread_step_star Sem2 ge2 U st2 m2 st2' m2' /\ MSorder cd' cd))
;MSmachine_diagram :
    forall U tr st1 m1 U' tr' st1' m1',
    machine_step Sem1 ge1 U tr st1 m1 U' tr' st1' m1' ->
    forall cd st2 mu m2,
    MSmatch_states cd mu st1 m1 st2 m2 ->
    exists st2', exists m2', exists cd', exists mu',
    MSmatch_states cd' mu' st1' m1' st2' m2'
    /\ machine_step Sem2 ge2 U tr st2 m2 U' tr' st2' m2'

; MSthread_halted :
    forall cd mu U c1 m1 c2 m2 v1,
    MSmatch_states cd mu c1 m1 c2 m2 ->
    conc_halted Sem1 U c1 = Some v1 ->
    exists v2,
       conc_halted Sem2 U c2 = Some v2
; MSthread_running:
    forall cd mu c1 m1 c2 m2 ,
      MSmatch_states cd mu c1 m1 c2 m2 ->
      forall i, runing_thread Sem1 c1 i <-> runing_thread Sem2 c2 i
      (* runing_thread Sem1 c1 = runing_thread Sem2 c2 *)
 }.

End Machine_sim.

Arguments MSdata {G1 TID SCH TR C1 G2 C2 Sem1 Sem2 ge1 ge2}.
Arguments MSorder {G1 TID SCH TR C1 G2 C2 Sem1 Sem2 ge1 ge2}.
Arguments MSmatch_states {G1 TID SCH TR C1 G2 C2 Sem1 Sem2 ge1 ge2}.
Arguments MSthread_diagram {G1 TID SCH TR C1 G2 C2 Sem1 Sem2 ge1 ge2}.
Arguments MSmachine_diagram {G1 TID SCH TR C1 G2 C2 Sem1 Sem2 ge1 ge2}.
Arguments MSthread_halted {G1 TID SCH TR C1 G2 C2 Sem1 Sem2 ge1 ge2}.
Arguments MSthread_running {G1 TID SCH TR C1 G2 C2 Sem1 Sem2 ge1 ge2}.

