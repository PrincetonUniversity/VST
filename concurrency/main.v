
(*Require Import semax_to_juicy_machine.*)
Require Import erasure_safety.

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
