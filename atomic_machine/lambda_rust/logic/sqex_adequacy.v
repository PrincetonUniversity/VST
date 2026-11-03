(** Adequacy of the lifted sequential logic for the atomic machine semantics
    of lambda-Rust. *)

From stdpp Require Import relations.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.logic.sq_adequacy.
(* Imported last, so that [to_val] and the other lambda-Rust names it
   re-exports win over the homonyms of [iris.program_logic]. *)
Require Export VST.atomic_machine.lambda_rust.logic.sqex_logic.

Import ListNotations.

(** With no access in flight, every allocated location is unreserved. *)
Definition sq_mu (m : lr_mem) : rw_map := (fun _ => Rst 0) <$> m.

(** Machine steps that spawn no thread: the pool keeps its domain. *)
Definition at_nofork_step (q q' : am_cfg) : Prop :=
  at_step q q' /\
  (forall i, is_Some (am_threads q' !! i) <-> is_Some (am_threads q !! i)).

(** The machine pool of a thread list. *)
Definition sqex_pool (tp : list sq_expr) : tpool :=
  map_seq 0%nat ((fun e => Running e []) <$> tp).

(** Machine executions of [tp] from [m] are safe, and a terminated thread's
    value satisfies its postcondition. *)
Definition at_sem_adequate (tp : list sq_expr) (φs : list (sq_val -> Prop)) (m : lr_mem) : Prop :=
  forall tp' m' mu',
    rtc at_nofork_step (AMCfg (sqex_pool tp) m (sq_mu m)) (AMCfg tp' m' mu') ->
    (forall i t, tp' !! i = Some t -> am_not_stuck t m' mu') /\
    (forall i e v φ, tp' !! i = Some (Running e []) -> to_val e = Some v ->
       φs !! i = Some φ -> φ v).

(** TODO do iLob here, figure out IH *)
Theorem sqex_adequacy Σ `{!lrSqGpreS Σ} (e : sq_expr) (φ : sq_val -> Prop) (m : lr_mem) :
  (forall `{!lrSqGS Σ} 
  (*`{!satisy_conc_triples ExtCallSems} *)
  , ⊢ EXWP e {{ v, ⌜φ v⌝ }}) ->
   at_sem_adequate [e] [φ] m.
Admitted.
