Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VSTlib.threads.
Require Import VSTlib.spec_threads.

Section mpred.
Context `{!VSTGS OK_ty Σ}.

Definition Threads_internal_specs: funspecs := ThreadsASI.

Axiom body_spawn: semax_body Vprog Threads_internal_specs f_spawn (_spawn, spawn_spec).
Axiom body_exit_thread: semax_body Vprog Threads_internal_specs f_exit_thread exit_thread_spec.

Definition Threads_imported_specs: @funspecs Σ :=  nil.


Definition ThreadsVprog : varspecs. mk_varspecs prog. Defined.
Definition ThreadsGprog: funspecs := Threads_imported_specs ++ Threads_internal_specs.

Definition Threads_E : @funspecs Σ := nil.

Definition ThreadsVSU `{Espec: ext_spec OK_ty}: VSU Threads_E Threads_imported_specs ltac:(QPprog prog) ThreadsASI (fun _ => emp).
  Proof. 
    mkVSU prog Threads_internal_specs.
    - solve_SF_internal body_spawn.
    - solve_SF_internal body_exit_thread.
  Qed.

End mpred.

