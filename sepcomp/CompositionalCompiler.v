(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** * The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Globalenvs.
Require Import Smallstep.

Require Import compcert.cfrontend.Clight.
(*WE NEED THIS: Require Import VST.sepcomp.Clight_eff.*)

Require Import VST.ccc26x86.Asm.
Require Import VST.ccc26x86.Asm_eff.

Require Import VST.sepcomp.simulations.
Require Import VST.sepcomp.effect_semantics.

Axiom transf_clight_program : Clight.program -> res Asm.program.

(*WE NEED THIS:*) Axiom CL_core : Type.
(*WE NEED THIS:*) Axiom CL_eff_sem1 : @EffectSem (Genv.t Clight.fundef cfrontend.Ctypes.type) CL_core.

(* Axiomatization of Theorem 18, Compiler Correctness: *)
Axiom transf_clight_program_correct:
  forall p tp (LNR: list_norepet (map fst (prog_defs p))),
  transf_clight_program p = OK tp ->
  SM_simulation.SM_simulation_inject
    CL_eff_sem1 Asm_eff_sem (Genv.globalenv p) (Genv.globalenv tp).
