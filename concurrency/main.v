
(*Require Import semax_to_juicy_machine.*)
Require Import erasure_signature.
Require Import erasure_proof.
Require Import erasure_safety.


Module MainSafety (DecayingSEM: DecayingSemantics).

  Module ErasureProof := erasure_proof.Parching DecayingSEM.
  Module Erasure := ErasureFnctr ErasureProof.
  Import ErasureProof.
  Import Erasure.

  Module ErasureSafety := ErasureSafety DecayingSEM.
  Import ErasureSafety.

  Parameters initU: DryMachine.Sch.
  Parameter init_rmap : JuicyMachine.SIG.ThreadPool.RES.res.
  Parameter init_pmap : DSEM.perm_map.
  Parameter init_rmap_perm:  match_rmap_perm init_rmap init_pmap.

  Definition local_erasure:= erasure initU init_rmap init_pmap init_rmap_perm.
  Definition step_diagram:= ErasureProof.core_diagram.

  
(*From semax_to_juicy_machine*)
(*Lemma juicy_safety: forall U rmap0 genv main vals js,
  semantics.initial_core (JMachineSem U (Some rmap0)) genv
         main vals = Some (U, nil, js) -> False.

(*Theorem safety_initial_state (sch : schedule) (n : nat) :
  JuicyMachine.csafe (globalenv prog) (sch, nil, initial_machine_state n) (proj1_sig init_mem) n.
Proof.
  apply jmsafe_csafe, jmsafe_initial_state.
Qed.
*)
