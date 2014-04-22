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

Module SM_simulation. Section SharedMemory_simulation_inject. 

Context 
  {F1 V1 C1 F2 V2 C2 : Type}
  (Sem1 : @EffectSem (Genv.t F1 V1) C1)
  (Sem2 : @EffectSem (Genv.t F2 V2) C2)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2).

Record SM_simulation_inject := 
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
    forall v vals1 c1 m1 j vals2 m2 DomS DomT,
    initial_core Sem1 ge1 v vals1 = Some c1 ->
    Mem.inject j m1 m2 -> 
    Forall2 (val_inject j) vals1 vals2 ->
    meminj_preserves_globals ge1 j ->

    (*the next two conditions are required to guarantee intialSM_wd*)
    (forall b1 b2 d, j b1 = Some (b2, d) -> 
      DomS b1 = true /\ DomT b2 = true) ->
    (forall b, 
      REACH m2 (fun b' => isGlobalBlock ge2 b' || getBlocks vals2 b') b=true -> 
      DomT b = true) ->

    (*the next two conditions ensure the initialSM satisfies sm_valid*)
    (forall b, DomS b = true -> Mem.valid_block m1 b) ->
    (forall b, DomT b = true -> Mem.valid_block m2 b) ->

    exists cd, exists c2, 
    initial_core Sem2 ge2 v vals2 = Some c2 
    (*Lemma StructuredInjections.initial_SM_as_inj implies 
      that Mem.inject (initial_SM DomS DomT 
            (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b)) 
            (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j)
            m1 m2 
     holds*)
    /\ match_state cd 
         (initial_SM DomS DomT 
           (REACH m1 (fun b => isGlobalBlock ge1 b || getBlocks vals1 b)) 
           (REACH m2 (fun b => isGlobalBlock ge2 b || getBlocks vals2 b)) j)
         c1 m1 c2 m2


(* ; core_diagram : 
    forall st1 m1 st1' m1', 
    corestep Sem1 ge1 st1 m1 st1' m1' ->
    forall cd st2 mu m2,
    match_state cd mu st1 m1 st2 m2 ->
    exists st2', exists m2', exists cd', exists mu',
      intern_incr mu mu' 
      /\ sm_inject_separated mu mu' m1 m2 
      /\ sm_locally_allocated mu mu' m1 m2 m1' m2' 
      /\ match_state cd' mu' st1' m1' st2' m2'
      /\ ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
           corestep_star Sem2 ge2 st2 m2 st2' m2' /\
           core_ord cd' cd) *)


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
    exists v2, 
    Mem.inject (as_inj mu) m1 m2 
    /\ val_inject (restrict (as_inj mu) (vis mu)) v1 v2 
    /\ halted Sem2 c2 = Some v2 


; core_at_external : 
    forall cd mu c1 m1 c2 m2 e vals1 ef_sig,
    match_state cd mu c1 m1 c2 m2 ->
    at_external Sem1 c1 = Some (e,ef_sig,vals1) ->
    Mem.inject (as_inj mu) m1 m2 
    /\ exists vals2, 
       Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 
       /\ at_external Sem2 c2 = Some (e,ef_sig,vals2)

    /\ forall
       (pubSrc' pubTgt' : block -> bool)
       (pubSrcHyp : pubSrc' =
                  (fun b : block =>
                  locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
       (pubTgtHyp: pubTgt' =
                  (fun b : block =>
                  locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
       nu (Hnu: nu = (replace_locals mu pubSrc' pubTgt')),
       match_state cd nu c1 m1 c2 m2 
       /\ Mem.inject (shared_of nu) m1 m2



; eff_after_external : 
  forall cd mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
  (MemInjMu: Mem.inject (as_inj mu) m1 m2)
  (MatchMu: match_state cd mu st1 m1 st2 m2)
  (AtExtSrc: at_external Sem1 st1 = Some (e,ef_sig,vals1))

  (* We include the clause AtExtTgt to ensure that vals2 is
     uniquely determined. We have e=e' and ef_sig=ef_sig' by the
     at_external clause, but omitting the hypothesis AtExtTgt
     would result in in 2 not necesssarily equal target argument
     lists in language 3 in the transitivity, as val_inject is not
     functional in the case where the left value is Vundef. (And
     we need to keep ValInjMu since vals2 occurs in pubTgtHyp) *)

  (AtExtTgt: at_external Sem2 st2 = Some (e',ef_sig',vals2)) 

  (ValInjMu: Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)  

  pubSrc' 
  (pubSrcHyp : 
    pubSrc' = fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b)
        
  pubTgt' 
  (pubTgtHyp : 
    pubTgt' = fun b => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b)

  nu (NuHyp: nu = replace_locals mu pubSrc' pubTgt'),

  forall nu' ret1 m1' ret2 m2'
  (INC: extern_incr nu nu')  
  (SEP: sm_inject_separated nu nu' m1 m2)
    
  (WDnu': SM_wd nu') (SMvalNu': sm_valid nu' m1' m2')

  (MemInjNu': Mem.inject (as_inj nu') m1' m2')
  (RValInjNu': val_inject (as_inj nu') ret1 ret2)

  (FwdSrc: mem_forward m1 m1') (FwdTgt: mem_forward m2 m2')

  frgnSrc' 
  (frgnSrcHyp: 
    frgnSrc' 
    = fun b => DomSrc nu' b 
               && (negb (locBlocksSrc nu' b) 
                   && REACH m1' (exportedSrc nu' (ret1::nil)) b))
  frgnTgt' 
  (frgnTgtHyp: 
    frgnTgt' 
    = fun b => DomTgt nu' b 
               && (negb (locBlocksTgt nu' b) 
                   && REACH m2' (exportedTgt nu' (ret2::nil)) b))

  mu' (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')

  (UnchPrivSrc: 
    Mem.unchanged_on (fun b ofs => 
      locBlocksSrc nu b = true /\ 
      pubBlocksSrc nu b = false) m1 m1') 

  (UnchLOOR: Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),

  exists cd', exists st1', exists st2',
  after_external Sem1 (Some ret1) st1 = Some st1'
  /\ after_external Sem2 (Some ret2) st2 = Some st2' 
  /\ match_state cd' mu' st1' m1' st2' m2' }.

End SharedMemory_simulation_inject. 

End SM_simulation.
