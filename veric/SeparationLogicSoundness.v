Load loadpath.
Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.res_predicates.
Require Import veric.seplog.
Require Import veric.assert_lemmas.
Require Import veric.Clight_new.
Require Import veric.extspec.
Require Import veric.step_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.expr.
Require Import veric.semax.
Require Import veric.semax_lemmas.
Require Import veric.Clight_lemmas.
Require Import veric.initial_world.
Require Import msl.normalize.
Require Import veric.semax_call.
Require Import veric.semax_straight.
Require Import veric.semax_loop.
Require Import veric.semax_prog.
Require Import veric.SeparationLogic.
Require Import veric.sim.

Module Type SEPARATION_LOGIC_SOUNDNESS.

Declare Module CSL: CLIGHT_SEPARATION_LOGIC.

Import CSL.

Axiom semax_prog_rule :
  forall z V G prog m,
     semax_prog prog V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q, 
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       make_initial_core (juicy_core_sem cl_core_sem)
                    (Genv.globalenv prog) (Vptr b Int.zero) nil = Some q /\
       forall n, exists jm, 
       m_dry jm = m /\ level jm = n /\ 
       jsafeN ExtSpec.Hspec (Genv.globalenv prog) n z q jm.

End SEPARATION_LOGIC_SOUNDNESS.

Module MakeSeparationLogic (EXT_SPEC: EXTERNAL_SPEC) :
  SEPARATION_LOGIC_SOUNDNESS with Module CSL.ExtSpec := EXT_SPEC.

Module EXT_SPEC := EXT_SPEC.
Import EXT_SPEC.

Module CSL <: CLIGHT_SEPARATION_LOGIC.
Module ExtSpec := EXT_SPEC.

Definition semax := semax Hspec.
Definition extract_exists := extract_exists Hspec.
Definition initblocksize := initblocksize.
Definition semax_body_params_ok := semax_body_params_ok.
Definition semax_body := semax_body Hspec.
Definition semax_func := semax_func Hspec.
Definition semax_ext := semax_ext Hspec.
Definition main_pre := main_pre.
Definition main_post := main_post.
Definition match_globvars := match_globvars.
Definition semax_prog := semax_prog Hspec.
Definition semax_func_nil := semax_func_nil Hspec.
Definition semax_func_cons := semax_func_cons Hspec.
Definition semax_func_cons_ext := semax_func_cons_ext Hspec.
Definition main_params := main_params.
Definition semax_seq := semax_seq Hspec.
Definition semax_for := semax_for Hspec.
Definition semax_while := semax_while Hspec.
Definition seq_assoc := seq_assoc Hspec.
Definition semax_call := semax_call Hspec.
Definition semax_fun_id := semax_fun_id Hspec.
Definition semax_call_ext := semax_call_ext Hspec.
Definition semax_set := semax_set Hspec.
Definition semax_set_forward := semax_set_forward Hspec.
Definition semax_ifthenelse := semax_ifthenelse Hspec.
Definition semax_return := semax_return Hspec.
Definition semax_store := semax_store Hspec.
Definition semax_load := semax_load Hspec.
Definition semax_Sskip := semax_Sskip Hspec.
Definition frame_left := frame_left Hspec.
Definition exit_tycon := exit_tycon.
Definition semax_pre_post := semax_pre_post Hspec.
Definition derives_skip := derives_skip Hspec.
Definition semax_ff := semax_ff Hspec.
Definition semax_extract_prop := semax_extract_prop Hspec.
Definition fn_funsig := fn_funsig.
Definition arglist := arglist.
Definition semax_external ef A P Q := forall n, semax_ext ef A P Q n.
Definition Cnot := Cnot.
Definition bool_type := bool_type.
Definition get_result := get_result.
Definition closed_wrt_modvars := closed_wrt_modvars.
Definition make_args := make_args.
End CSL.

Definition semax_prog_rule := semax_prog_rule Hspec.

End MakeSeparationLogic.
