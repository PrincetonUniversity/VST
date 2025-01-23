From lithium Require Import hooks.
From refinedc.typing Require Import type.
(* Ke: TODO this one needs rework *)
Ltac unfold_aligned_to :=
  unfold aligned_to in *;
  try rewrite ->caesium_config.enforce_alignment_value in *;
  cbv [selected_config.enforce_alignment] in *.

Ltac unfold_common_defs :=
  unfold
  (* Unfold [aligned_to] and [Z.divide] as lia can work with the underlying multiplication. *)
    aligned_to, Z.divide,
  (* Unfold [addr] since [lia] may get stuck due to [addr]/[Z] mismatches. *)
    addr,
  (* Layout *)
    ly_size, ly_with_align, ly_align_log,
  (* Integer bounds *)
    max_int, min_int, int_half_modulus, int_modulus,
    it_layout, bits_per_int, bytes_per_int,
  (* Address bounds *)
    max_alloc_end, min_alloc_start, bytes_per_addr,
  (* Other byte-level definitions *)
    bits_per_byte in *.

(** * [solve_goal] without cleaning of the context  *)
Ltac solve_goal_normalized_prepare_hook ::=
  unfold_common_defs;
  try rewrite ->caesium_config.enforce_alignment_value in *;
  simpl in *;
  rewrite /ly_size/ly_align_log //=.
