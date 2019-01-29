(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Require Import FCF.DistTacs.
Require Import FCF.ProgTacs.
Require Import FCF.ProgramLogic.

Ltac inline_first :=
  repeat (dist_inline_first; prog_inline_first).

Ltac comp_skip :=
  dist_skip || prog_skip.

Ltac comp_irr_l :=
  dist_irr_l || prog_irr_l.

Ltac comp_irr_r :=
  dist_irr_r || prog_irr_r.

Ltac comp_swap s :=
  dist_swap s || prog_swap s.

Ltac comp_swap_r :=
  dist_swap_r || prog_swap_r.

Ltac comp_swap_l :=
  dist_swap_l || prog_swap_l.

Ltac comp_inline s :=
  dist_inline s || prog_inline s.

Ltac comp_inline_r :=
  dist_inline_r || prog_inline_r.

Ltac comp_inline_l :=
  dist_inline_l || prog_inline_l.

Ltac comp_ret_l :=
  dist_ret_l || prog_ret_l.

Ltac comp_ret_r :=
  dist_ret_r || prog_ret_r.

Ltac comp_ret s :=
  dist_ret s || prog_ret s.

Ltac comp_simp :=
  repeat (dist_simp; prog_simp).

Ltac comp_at t s l :=
  match goal with
    | [|- comp_spec _ _ _ ] => idtac
    | _ => dist_at t s l
  end.