From VST.lithium Require Import type.

(** This file collects options for files with type definitions.

    WARNING: Never export this file and don't import this file in
 files that use the automation! *)

(** These definitions are opaque by default to improve typeclass
search for the automation. We make them transparent for type
definitions such that iDestruct and friends work when proving lemmas. *)
#[export] Typeclasses Transparent ty_own ty_own_val with_refinement.

(* TODO: move this somewhere else? *)
#[export] Set Default Proof Using "Type".
