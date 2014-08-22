Require Import sepcomp.core_semantics.

Require Import veric.base.
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
Require Import sepcomp.extspec.
Require Import sepcomp.step_lemmas.
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
Require Import veric.semax_ext.
Require Import veric.SeparationLogic.
Require Import veric.expr_rel.

Module Type SEPARATION_LOGIC_SOUNDNESS.

(*Declare Module ExtSpec: EXTERNAL_SPEC. *)
Declare Module CSL: CLIGHT_SEPARATION_LOGIC.

Import CSL.

Axiom semax_prog_rule :
  forall {Espec: OracleKind},
  forall z V G prog m,
     @semax_prog Espec prog V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q, 
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       core_semantics.initial_core (juicy_core_sem cl_core_sem)
                    (Genv.globalenv prog) (Vptr b Int.zero) nil = Some q /\
       forall n, exists jm, 
       m_dry jm = m /\ level jm = n /\ 
       jsafeN (@OK_spec Espec) (Genv.globalenv prog) n z q jm.

End SEPARATION_LOGIC_SOUNDNESS.

Module SoundSeparationLogic : SEPARATION_LOGIC_SOUNDNESS.

Module CSL <: CLIGHT_SEPARATION_LOGIC.
Definition func_ptr (f: funspec) : val -> mpred := 
 match f with mk_funspec fsig A P Q => res_predicates.fun_assert fsig A P Q end.

Transparent mpred Nveric Sveric Cveric Iveric Rveric Sveric SIveric SRveric.
Lemma corable_func_ptr: forall f v, corable (func_ptr f v).
Proof.
intros. destruct f;  unfold func_ptr, corable.
intros.
apply log_normalize.corable_andp_sepcon1.
unfold corable.
intros.
simpl.
apply normalize.corable_andp_sepcon1.
apply corable_fun_assert.
Qed.
Opaque mpred Nveric Sveric Cveric Iveric Rveric Sveric SIveric SRveric.

Definition semax := @semax.
Definition extract_exists := @extract_exists.
Definition semax_body_params_ok := semax_body_params_ok.
Definition semax_body := @semax_body.
Definition semax_func := @semax_func.
Definition semax_prog := @semax_prog.
Definition semax_func_nil := @semax_func_nil.
Definition semax_func_cons := @semax_func_cons.
Definition semax_func_skip := @semax_func_skip.
Definition semax_func_cons_ext := @semax_func_cons_ext.
Definition semax_seq := @semax_seq.
Definition semax_break := @semax_break.
Definition semax_continue := @semax_continue.
Definition semax_loop := @semax_loop.
Definition seq_assoc := @seq_assoc.
Definition semax_seq_skip := @semax_seq_skip.
Definition semax_skip_seq := @semax_skip_seq.
Definition semax_call := @semax_call.
Definition semax_fun_id := @semax_fun_id_alt.
(* Definition semax_call_ext := @semax_call_ext. *)
Definition semax_set := @semax_set.
Definition semax_set_forward := @semax_set_forward.
Definition semax_ifthenelse := @semax_ifthenelse.
Definition semax_return := @semax_return.
Definition semax_store := @semax_store.
Definition semax_load := @semax_load.
Definition semax_set_forward_nl := @semax_set_forward_nl.
Definition semax_loadstore := @semax_loadstore.
Definition semax_cast_load := @semax_cast_load.
Definition semax_skip := @semax_skip.
Definition semax_frame := @semax_frame.
Definition semax_pre_post := @semax_pre_post.
Definition semax_extensionality_Delta := @semax_extensionality_Delta.
Definition semax_extract_prop := @semax_extract_prop.
Definition semax_ptr_compare := @semax_ptr_compare.

Definition semax_external {Espec: OracleKind} ef A P Q := 
  forall n, semax_external Espec ef A P Q n.

Definition juicy_ext_spec := juicy_ext_spec.

Definition wf_funspec := veric.semax_ext.wf_funspec.
Definition wf_funspecs := veric.semax_ext.wf_funspecs.
Definition in_funspecs := veric.semax_ext.in_funspecs.
Definition local_funspec := veric.semax_ext.local_funspec.
Definition funspecs_norepeat := veric.semax_ext.funspecs_norepeat.
Definition add_funspecs := veric.semax_ext.add_funspecs.
Definition funsig2signature := veric.semax_ext.funsig2signature.

Definition semax_ext := @semax_ext.

End CSL.

Definition semax_prog_rule := @semax_prog_rule.

End SoundSeparationLogic.
