Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VSTlib.threads.
Require Import VSTlib.spec_threads.

Definition Threads_internal_specs: funspecs := ThreadsASI.

Axiom body_spawn: semax_body Vprog Threads_internal_specs f_spawn (_spawn, spawn_spec).
Axiom body_exit_thread: semax_body Vprog Threads_internal_specs f_exit_thread exit_thread_spec.

Definition Threads_imported_specs:funspecs :=  nil.


Definition ThreadsVprog : varspecs. mk_varspecs prog. Defined.
Definition ThreadsGprog: funspecs := Threads_imported_specs ++ Threads_internal_specs.

Definition Threads_E : funspecs := nil.

Ltac check_mpreds2 R ::= (* Patch for https://github.com/PrincetonUniversity/VST/issues/638 *)
 lazymatch R with
 | @sepcon mpred _ _ ?a ?b => check_mpreds2 a; check_mpreds2 b
 | _ => match type of R with ?t =>
                          first [constr_eq t mpred
                                 | fail 4 "The conjunct" R "has type" t "but should have type mpred; these two types may be convertible but they are not identical"]
                     end
 | nil => idtac
 end.

#[local] Existing Instance NullExtension.Espec.   (* FIXME *)

Definition ThreadsVSU: VSU Threads_E Threads_imported_specs ltac:(QPprog prog) ThreadsASI emp.
  Proof. 
    mkVSU prog Threads_internal_specs.
    - solve_SF_internal body_spawn.
    - solve_SF_internal body_exit_thread.
  Qed.

