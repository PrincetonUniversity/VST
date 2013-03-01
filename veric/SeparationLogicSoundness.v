Load loadpath.
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
Require Import veric.SeparationLogic.

Module Type SEPARATION_LOGIC_SOUNDNESS.

Declare Module ExtSpec: EXTERNAL_SPEC.
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

Module MakeSeparationLogic (ExtSpec: EXTERNAL_SPEC) :
  SEPARATION_LOGIC_SOUNDNESS with Module ExtSpec := ExtSpec.

Module ExtSpec := ExtSpec.
Import ExtSpec.

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

Definition semax := semax Hspec.
Definition extract_exists := extract_exists Hspec.
Definition semax_body_params_ok := semax_body_params_ok.
Definition semax_body := semax_body Hspec.
Definition semax_func := semax_func Hspec.
Definition semax_prog := semax_prog Hspec.
Definition semax_func_nil := semax_func_nil Hspec.
Definition semax_func_cons := semax_func_cons Hspec.
Definition semax_func_cons_ext := semax_func_cons_ext Hspec.
Definition semax_seq := semax_seq Hspec.
Definition semax_break := semax_break Hspec.
Definition semax_continue := semax_continue Hspec.
Definition semax_loop := semax_loop Hspec.
Definition seq_assoc := seq_assoc Hspec.
Definition semax_call := semax_call Hspec.
Definition semax_fun_id := semax_fun_id_alt Hspec.
Definition semax_call_ext := semax_call_ext Hspec.
Definition semax_set := semax_set Hspec.
Definition semax_set_forward := semax_set_forward Hspec.
Definition semax_ifthenelse := semax_ifthenelse Hspec.
Definition semax_return := semax_return Hspec.
Definition semax_store := semax_store Hspec.
Definition semax_load := semax_load Hspec.
Definition semax_skip := semax_skip Hspec.
Definition semax_frame := semax_frame Hspec.
Definition semax_pre_post := semax_pre_post Hspec.
Definition semax_extensionality_Delta := semax_extensionality_Delta Hspec.
Definition semax_extract_prop := semax_extract_prop Hspec.

Definition semax_external ef A P Q := forall n, semax_ext Hspec ef A P Q n.

Lemma semax_external_FF:
  forall ef A Q n,
     semax_ext Hspec ef A (fun _ _ => FF) Q n.
Proof.
repeat intro.  destruct H2 as [? [? [? [? ?]]]]. contradiction.
Qed.

End CSL.

Definition semax_prog_rule := semax_prog_rule Hspec.

End MakeSeparationLogic.
