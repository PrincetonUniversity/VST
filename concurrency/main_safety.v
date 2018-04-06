Require Import veric.tycontext.
Require Import compcert.common.AST.
Require Import Coq.Strings.String.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import VST.concurrency.semax_conc.
Require Import compcert.cfrontend.Clight.
Require Import VST.concurrency.Clight_safety.


Section MainSafety.

Variables
      (CS : compspecs)
      (V :  varspecs)
      (G :  funspecs)
      (ext_link : string -> ident)
      (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2)
      (prog : Ctypes.program _)
      (all_safe : semax_prog.semax_prog (Concurrent_Espec unit CS ext_link) prog V G)
      (init_mem_not_none : Genv.init_mem (Ctypes.program_of_program prog) <> None)
      (x: block)
      (block: (Genv.find_symbol (globalenv prog) (prog_main (Ctypes.program_of_program prog)) = Some x)).

Notation Clight_new_dry_safety:=
  (Initial_dry_safety CS V G ext_link ext_link_inj prog all_safe init_mem_not_none x block). 

(*
Lemma 

Require Import concurency.Clight_new2core.
 *)
End MainSafety.
