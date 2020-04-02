Require Import VST.floyd.base2.
Require Export VST.floyd.Zlength_solver_base.

(** This file provides a almost-complete solver for list with concatenation.
  Its core symbols include:
    Zlength
    Znth
    Zrepeat
    app
    sublist
    map.
  And it also interprets these symbols by convernting to core symbols:
    list_repeat (Z.to_nat _)
    nil
    cons
    upd_Znth. *)

Ltac Zlength_solve := autorewrite with Zlength; pose_Zlength_nonneg; omega.
Hint Rewrite Zlength_cons : Zlength.
Hint Rewrite Zlength_nil : Zlength.
Hint Rewrite Zlength_app : Zlength.
Hint Rewrite Zlength_map : Zlength.
Hint Rewrite Zlength_Zrepeat using Zlength_solve : Zlength.
Hint Rewrite @Zlength_list_repeat using Zlength_solve : Zlength.
Hint Rewrite @upd_Znth_Zlength using Zlength_solve : Zlength.
Hint Rewrite @Zlength_sublist using Zlength_solve : Zlength.

(** * Zlength_solve_complete *)
(** Zlength_solve_complete intends to provide a more complete solver than Zlength_solve. *)

Ltac Zlength_solve_complete :=
  pose_Zlength_nonneg; autorewrite with Zlength in *; Zlength_solve.

Ltac Zlength_solve2 := Zlength_solve_complete.