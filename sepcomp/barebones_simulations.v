Require Import compcert. Import CompcertCommon.
Require Import core_semantics.
Require Import core_semantics_lemmas.

Require Import mem_lemmas.

(* Minimal whole program simulations *)

Module Barebones_simulation. Section Barebones_simulation.

Context 
  {F1 V1 C1 F2 V2 C2 : Type}
  (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem)
  (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem)
  (ge1 : Genv.t F1 V1)
  (ge2 : Genv.t F2 V2)
  (main : val).

Record Barebones_simulation := 
{ match_state : C1 -> C2 -> Prop

; genvs_agree : genvs_domain_eq ge1 ge2

; core_initial : 
    forall c1 vals,
    initial_core Sem1 ge1 main vals = Some c1 ->
    exists c2,
         initial_core Sem2 ge2 main vals = Some c2 
      /\ match_state c1 c2 

; core_diagram :
    forall c1 c2 m c1' m',
    match_state c1 c2 -> 
    corestep Sem1 ge1 c1 m c1' m' -> 
    exists c2', 
       corestep_plus Sem2 ge2 c2 m c2' m' 
    /\ match_state c1' c2' 

; core_halted :
    forall c1 c2 rv,
    match_state c1 c2 -> 
    halted Sem1 c1 = Some rv ->
    halted Sem2 c2 = Some rv }.

End Barebones_simulation.

End Barebones_simulation.
