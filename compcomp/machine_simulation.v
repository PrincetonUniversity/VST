Require Import compcert_threads.
Require Import simulations.
Import ssreflect fintype.
Require Import ProofIrrelevance.

Import Forward_simulation_inj.

Module Type SimParameters.
  Parameters F V C: Type.
  Definition G:= (Genv.t F V).
  Parameter ge: G.
  Parameter Sem:  CoreSemantics G C mem.
  Parameter lp_code: C.
  Parameter compute_init_perm: G -> permissions.access_map.
End SimParameters.

Module Type Simulation.
  Parameter simulation: forall (F1 F2 V1 V2 C1 C2: Type),
    CoreSemantics (Genv.t F1 V1) C1 mem ->
    CoreSemantics (Genv.t F2 V2) C2 mem ->
    Genv.t F1 V1 ->
    Genv.t F2 V2 -> list (val * val * signature) -> Type.
End Simulation.
  

Module Type MachineSimulation (SIM:Simulation)(SP1 SP2: SimParameters).
  (*Declare Module Sim : Simulation.*)
  Import SIM.
  Import Concur.


  Notation F1:= SP1.F.
  Notation V1:= SP1.V.
  Notation C1:= SP1.C.
  Notation F2:= SP2.F.
  Notation V2:= SP2.V.
  Notation C2:= SP2.C.

  Notation simple_sim:= (simulation F1 F2 V1 V2 C1 C2).
  Notation cm_sim:= (simulation F1 F2 V1 V2 (list nat * pool C1) (list nat * pool C2)).
  
  Notation Sem1:= SP1.Sem. 
  Notation G1:= SP1.G.
  Notation ge1:= SP1.ge.
  Notation lp_code1:= SP1.lp_code.
  Notation compute_init_perm1:= SP1.compute_init_perm.
  
  Notation Sem2:= SP2.Sem. 
  Notation G2:= SP2.G.
  Notation ge2:= SP2.ge.
  Notation lp_code2:= SP2.lp_code.
  Notation compute_init_perm2:= SP2.compute_init_perm.

  Parameter angel: nat -> permissions.access_map.
  Parameter sched: list nat.
  Parameter entry_points : list (val * val * signature).

  Definition SemM1:= @coarse_semantics C1 _ Sem1 compute_init_perm1 sched lp_code1 angel.
  Definition SemM2:= @coarse_semantics C2 _ Sem2 compute_init_perm2 sched lp_code2 angel.
  
  Axiom MachineSimProof:
     simple_sim Sem1 Sem2 ge1 ge2 entry_points ->
      cm_sim SemM1 SemM2 ge1 ge2 entry_points .
     
End MachineSimulation.

Module ESOP_SIM <: Simulation.
  Definition simulation :=
    fun (F1 F2 V1 V2 C1 C2: Type) => @Forward_simulation_inject F1 V1 F2 V2 C1 C2.
End ESOP_SIM.


Module ESOP_MachineSimulation (SP1 SP2 : SimParameters):  MachineSimulation ESOP_SIM SP1 SP2.
  Import ESOP_SIM.
  Import Concur.


  Notation F1:= SP1.F.
  Notation V1:= SP1.V.
  Notation C1:= SP1.C.
  Notation F2:= SP2.F.
  Notation V2:= SP2.V.
  Notation C2:= SP2.C.

  Notation simple_sim:= (simulation F1 F2 V1 V2 C1 C2).
  Notation cm_sim:= (simulation F1 F2 V1 V2 (list nat * pool C1) (list nat * pool C2)).
  
  Notation Sem1:= SP1.Sem. 
  Notation G1:= SP1.G.
  Notation ge1:= SP1.ge.
  Notation lp_code1:= SP1.lp_code.
  Notation compute_init_perm1:= SP1.compute_init_perm.
  
  Notation Sem2:= SP2.Sem. 
  Notation G2:= SP2.G.
  Notation ge2:= SP2.ge.
  Notation lp_code2:= SP2.lp_code.
  Notation compute_init_perm2:= SP2.compute_init_perm.

  Parameter angel: nat -> permissions.access_map.
  Parameter sched: list nat.
  Parameter entry_points : list (val * val * signature).


  Section TheTheorem.
    Variable Sim1: simple_sim Sem1 Sem2 ge1 ge2 entry_points .
    
    Notation num_threads := ThreadPool.num_threads.
    Notation match_s:= (match_state Sim1).
    Notation thread_ord:= (core_ord Sim1).
    Notation thread_diagram:= (core_diagram Sim1).

    
    Definition CM1:= (list nat * pool C1)%type.
    Definition CM2:= (list nat * pool C2)%type.
    Definition SemM1:= @coarse_semantics C1 _ Sem1 compute_init_perm1 sched lp_code1 angel.
    Definition SemM2:= @coarse_semantics C2 _ Sem2 compute_init_perm2 sched lp_code2 angel.
    
    Record machine_data:=
      {
        d_size: nat;
        datum: 'I_(d_size) -> core_data Sim1
       }.

    Lemma leq_eq: forall {m n}, 'I_m -> m = n -> 'I_n.
      intros ? ? H H0; rewrite <- H0; exact H.
    Qed.              
    Inductive md_ord: machine_data -> machine_data -> Prop:=
    | MD_LT: forall md md' (Hsize: d_size md = d_size md'),
        (forall tid: 'I_(d_size md),
            let d:= datum md tid in
            let d':= datum md' (leq_eq tid Hsize) in
            d = d' \/ thread_ord d d') ->
        (exists tid: 'I_(d_size md),
            let d:= datum md tid in
            let d':= datum md' (leq_eq tid Hsize) in
            thread_ord d d') ->
        md_ord md md'.
        
    Definition md_ord_wf: well_founded md_ord.
      unfold well_founded; intros.
      admit.
    Defined.
    Lemma le_eq: (forall a b c, a < b -> b = c -> a < c)%nat.
                   intros ? ? ? H H0; rewrite <- H0; exact H.
    Qed.
    Inductive match_ms: machine_data -> meminj -> CM1 -> mem -> CM2 -> mem -> Prop:=
      MATCH: forall md j ms1 m1 ms2 m2,
        forall sched tp1 tp2,
          ms1 = (sched, tp1) -> ms2  = (sched, tp2) ->
          forall (Hsize : pos.n (num_threads tp1) = pos.n (num_threads tp2))
            (Hdata_ok : pos.n (num_threads tp1) = d_size md) 
          (Hcompat1: mem_compatible tp1 m1)
          (Hcompat2: mem_compatible tp2 m2)
          (Hmatch: forall (tid: 'I_(pos.n (num_threads tp1))),
             let m1:= restrPermMap (permMapsInv_lt (perm_comp Hcompat1) tid) in 
             let m2:= restrPermMap (permMapsInv_lt (perm_comp Hcompat2) (leq_eq tid Hsize)) in
             let c1:= ThreadPool.pool tp1 tid in
             let c2:= ThreadPool.pool tp2 (leq_eq tid Hsize) in
             match_s (datum md (leq_eq tid Hdata_ok)) j c1 m1 c2 m2),
            match_ms md j ms1 m1 ms2 m2.

    (*This can be proven, it probably is somewhere. *)
    Parameter thread_diagramN:
      (forall (st3 : C1) (m3 : mem) (st1'0 : C1) (m1'0 : mem) n,
    corestepN Sem1 ge1 (S n) st3 m3 st1'0 m1'0 ->
    forall (cd0 : core_data Sim1) (st4 : C2) (j0 : meminj) (m4 : mem),
    match_s cd0 j0 st3 m3 st4 m4 ->
    exists (st2' : C2) (m2' : mem) (cd' : core_data Sim1) 
    (j' : meminj),
      inject_incr j0 j' /\
      inject_separated j0 j' m3 m4 /\
      match_s cd' j' st1'0 m1'0 st2' m2' /\
      (corestep_plus Sem2 ge2 st4 m4 st2' m2' \/
       corestep_star Sem2 ge2 st4 m4 st2' m2' /\ thread_ord cd' cd0)).

    Theorem core_diagram: forall (st1 : CM1) (m1 : mem) (st1' : CM1) (m1' : mem),
        corestep SemM1 ge1 st1 m1 st1' m1' ->
        forall (cd : machine_data) (st2 : CM2) 
          (j : meminj) (m2 : mem),
          match_ms cd j st1 m1 st2 m2 ->
        exists (st2' : CM2) (m2' : mem) (cd' : machine_data) 
          (j' : meminj),
          inject_incr j j' /\
          inject_separated j j' m1 m2 /\
          match_ms cd' j' st1' m1' st2' m2' /\
          (corestep_plus SemM2 ge2 st2 m2 st2' m2' \/
           corestep_star SemM2 ge2 st2 m2 st2' m2' /\
           md_ord cd' cd).
        intros. 
        inv H.

        (*CORE STEP*)
        { inv Ht_step.
          inv H0.
          pose (tid1:= (Ordinal (n:=pos.n (num_threads tp1))(m:=tid) Htid0_lt_pf)).
          pose (c2:= getThreadC tp2 (leq_eq tid1 Hsize)).
          (*rename m1 into my.*)
          pose (tm2:= restrPermMap
                       (permMapsInv_lt (perm_comp Hcompat2) (leq_eq tid1 Hsize) )).
          pose (d:= datum cd (leq_eq tid1 Hdata_ok)).
          pose (c1:= (getThreadC tp1) tid1).
          pose (tm1:= (restrPermMap
                    (permMapsInv_lt (perm_comp Hcompatible) tid1))).
          rename m1' into tm1'.
          
          assert (MATCH: match_s d j c1 tm1 c2 tm2).
          { simpl in Hmatch.
            unfold d, c1, tm1, c2, tm2.
            specialize (Hmatch tid1).
            simpl in Htid0_lt_pf.
            unfold getThreadC.
            replace Hcompatible with Hcompat1  by apply proof_irrelevance.
            apply Hmatch. }

          destruct (thread_diagramN c1 tm1 c' tm1' n0 HcorestepN d c2 j tm2 MATCH) as
              [st2' [m2' [cd' [j' HH]]] ].
          
  (*HALT STEP*)
  exists (sched0, snd st2), m2, cd, j.
  assert (ST1:st1' = (sched0, snd st1)).
  destruct st1', st1; inversion H4; inversion H6; reflexivity.
  repeat match goal with
         | [ _ : _  |- _ /\ _] => split; auto
         end.
  apply inject_separated_same_meminj.
  rewrite <- H5, ST1.
  admit.
  left. exists O, (sched0, snd st2), m2; simpl.
  split; [ | reflexivity].
  unfold cstep. simpl.
  assert (HH: fst st2 = fst st1) by admit.
  rewrite HH, <- H2.
  (*eapply step_halted.*) admit.

  (*EXTERNAL STEP*)
  inversion Hext_step.
  

  
  
  Theorem MachineSimProof:
    let CM1:= @coarse_semantics C1 _ Sem1 compute_init_perm1 sched lp_code1 angel in
    let CM2:= @coarse_semantics C2 _ Sem2 compute_init_perm2 sched lp_code2 angel in
     simple_sim Sem1 Sem2 ge1 ge2 entry_points ->
     cm_sim CM1 CM2 ge1 ge2 entry_points .
  Admitted.
End ESOP_MachineSimulation.
