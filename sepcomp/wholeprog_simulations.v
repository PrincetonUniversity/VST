Require Import Bool.

Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.

Require Import compcert.common.Globalenvs.

Require Import compcert.lib.Axioms.

Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.StructuredInjections.
Require Import sepcomp.reach.

Definition is_vundef (v : val) : bool :=
  match v with 
    | Vundef => true
    | _ => false
  end.

Definition vals_def (vs : list val) := 
  List.forallb (fun v => negb (is_vundef v)) vs.

Module Wholeprog_simulation. Section Wholeprog_simulation_inject. 

Context 
  {F1 V1 C1 F2 V2 C2 : Type}
  (Sem1 : @EffectSem (Genv.t F1 V1) C1)
  (Sem2 : @EffectSem (Genv.t F2 V2) C2)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2)
  (main : val).

Record Wholeprog_simulation_inject := 
{ core_data : Type
; match_state : core_data -> SM_Injection -> C1 -> mem -> C2 -> mem -> Prop
; core_ord : core_data -> core_data -> Prop
; core_ord_wf : well_founded core_ord


; match_sm_wd : 
    forall d mu c1 m1 c2 m2, 
    match_state d mu c1 m1 c2 m2 -> SM_wd mu

; genvs_dom_eq : genvs_domain_eq ge1 ge2

; match_genv : 
    forall d mu c1 m1 c2 m2 (MC : match_state d mu c1 m1 c2 m2),
    meminj_preserves_globals ge1 (extern_of mu) /\
    (forall b, isGlobalBlock ge1 b = true -> frgnBlocksSrc mu b = true)

; match_visible : 
    forall d mu c1 m1 c2 m2, 
    match_state d mu c1 m1 c2 m2 -> 
    REACH_closed m1 (vis mu)

; match_restrict : 
    forall d mu c1 m1 c2 m2 X, 
    match_state d mu c1 m1 c2 m2 -> 
    (forall b, vis mu b = true -> X b = true) ->
    REACH_closed m1 X ->
    match_state d (restrict_sm mu X) c1 m1 c2 m2

; match_validblocks : 
    forall d mu c1 m1 c2 m2, 
    match_state d mu c1 m1 c2 m2 ->
    sm_valid mu m1 m2


; core_initial : 
    forall j c1 vals1 m1 vals2 m2,
    initial_core Sem1 ge1 main vals1 = Some c1 ->
    Mem.inject j m1 m2 -> 
    Forall2 (val_inject j) vals1 vals2 ->
    meminj_preserves_globals ge1 j ->
    (forall b, 
     REACH m2 (fun b0 => isGlobalBlock ge1 b0 || getBlocks vals2 b0) b=true ->
     Mem.valid_block m2 b) -> 
    exists mu cd c2,
      as_inj mu = j 
      /\ initial_core Sem2 ge2 main vals2 = Some c2 
      /\ match_state cd mu c1 m1 c2 m2


; effcore_diagram : 
    forall st1 m1 st1' m1' U1, 
    effstep Sem1 ge1 U1 st1 m1 st1' m1' ->

    forall cd st2 mu m2
           (UHyp: forall b1 z, U1 b1 z = true -> vis mu b1 = true),
    match_state cd mu st1 m1 st2 m2 ->
    exists st2', exists m2', exists cd', exists mu',
    intern_incr mu mu' 
    /\ sm_inject_separated mu mu' m1 m2 
    /\ sm_locally_allocated mu mu' m1 m2 m1' m2' 
    /\ match_state cd' mu' st1' m1' st2' m2' 
    /\ exists U2,              
       ((effstep_plus Sem2 ge2 U2 st2 m2 st2' m2' 
        \/ (effstep_star Sem2 ge2 U2 st2 m2 st2' m2' /\ core_ord cd' cd))
       /\ forall b ofs, 
          U2 b ofs = true -> 
          visTgt mu b = true
          /\ (locBlocksTgt mu b = false ->
              exists b1 delta1, 
              foreign_of mu b1 = Some(b,delta1)
              /\ U1 b1 (ofs-delta1) = true 
              /\ Mem.perm m1 b1 (ofs-delta1) Max Nonempty))

      
; core_halted : 
    forall cd mu c1 m1 c2 m2 v1,
    match_state cd mu c1 m1 c2 m2 ->
    halted Sem1 c1 = Some v1 ->
    exists j v2, 
    meminj_preserves_globals ge1 j
    /\ val_inject j v1 v2
    /\ Mem.inject j m1 m2
    /\ halted Sem2 c2 = Some v2 }.

End Wholeprog_simulation_inject. 

End Wholeprog_simulation. 
