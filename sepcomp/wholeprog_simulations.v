Require Import Bool.

Require Import Events.
Require Import Memory.
Require Import compcert.lib.Coqlib.
Require Import Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import compcert.lib.Axioms.

Require Import mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import core_semantics.
Require Import core_semantics_lemmas.
Require Import StructuredInjections.
Require Import reach.
Require Import mem_wd.

Require Import effect_semantics. (*for specialization below*)

Module Wholeprog_sim. Section Wholeprog_sim.

Context {G1 C1 M1 G2 C2 M2 : Type}

(Sem1 : @CoreSemantics G1 C1 M1)
(Sem2 : @CoreSemantics G2 C2 M2)

(ge1 : G1)
(ge2 : G2)

(main : val).

Variable ge_inv : G1 -> G2 -> Prop.

Variable init_inv : meminj -> G1 -> list val -> M1 -> G2 -> list val -> M2 -> Prop.

Variable halt_inv : SM_Injection -> G1 -> val -> M1 -> G2 -> val -> M2 -> Prop.

Record Wholeprog_sim := 
{ core_data : Type
; match_state : core_data -> SM_Injection -> C1 -> M1 -> C2 -> M2 -> Prop
; core_ord : core_data -> core_data -> Prop
; core_ord_wf : well_founded core_ord
; genv_inv : ge_inv ge1 ge2
; core_initial : 
    forall j c1 vals1 m1 vals2 m2,
    initial_core Sem1 ge1 main vals1 = Some c1 ->
    init_inv j ge1 vals1 m1 ge2 vals2 m2 ->
    exists mu cd c2,
      as_inj mu = j 
      /\ initial_core Sem2 ge2 main vals2 = Some c2 
      /\ match_state cd mu c1 m1 c2 m2
; core_diagram : 
    forall st1 m1 st1' m1', 
    corestep Sem1 ge1 st1 m1 st1' m1' ->
    forall cd st2 mu m2,
    match_state cd mu st1 m1 st2 m2 ->
    exists st2', exists m2', exists cd', exists mu',
    match_state cd' mu' st1' m1' st2' m2' 
    /\ (corestep_plus Sem2 ge2 st2 m2 st2' m2' 
        \/ (corestep_star Sem2 ge2 st2 m2 st2' m2' /\ core_ord cd' cd))
; core_halted : 
    forall cd mu c1 m1 c2 m2 v1,
    match_state cd mu c1 m1 c2 m2 ->
    halted Sem1 c1 = Some v1 ->
    exists j v2, 
       halt_inv j ge1 v1 m1 ge2 v2 m2 
    /\ halted Sem2 c2 = Some v2 }.

End Wholeprog_sim.

End Wholeprog_sim.

Section CompCert_wholeprog_sim.

Context {F1 V1 C1 F2 V2 C2 : Type}

(Sem1 : @EffectSem (Genv.t F1 V1) C1)
(Sem2 : @EffectSem (Genv.t F2 V2) C2)

(ge1 : Genv.t F1 V1)
(ge2 : Genv.t F2 V2)

(main : val).

Definition cc_init_inv j (ge1 : Genv.t F1 V1) vals1 m1 (ge2 : Genv.t F2 V2) vals2 m2 :=
  Mem.inject j m1 m2 
  /\ Forall2 (val_inject j) vals1 vals2 
  /\ meminj_preserves_globals ge1 j 
    (* TODO REACH redundant with val_valid and mem_wd, should be removed *)
  /\ (forall b, 
      REACH m2 (fun b0 => isGlobalBlock ge1 b0 || getBlocks vals2 b0) b=true ->
      Mem.valid_block m2 b)
  /\ mem_wd m2 
  /\ valid_genv ge2 m2 
  /\ Forall (fun v2 => val_valid v2 m2) vals2.
  
Definition cc_halt_inv j (ge1 : Genv.t F1 V1) v1 m1 (ge2 : Genv.t F2 V2) v2 m2 :=
  meminj_preserves_globals ge1 (as_inj j)
  /\ val_inject (as_inj j) v1 v2
  /\ Mem.inject (as_inj j) m1 m2.

Definition CompCert_wholeprog_sim :=
  @Wholeprog_sim.Wholeprog_sim _ _ _ _ _ _ 
    Sem1 Sem2
    ge1 ge2
    main
    genvs_domain_eq
    cc_init_inv
    cc_halt_inv.

End CompCert_wholeprog_sim.