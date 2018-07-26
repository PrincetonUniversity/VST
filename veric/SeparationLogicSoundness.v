Require Import VST.sepcomp.semantics.

Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.seplog.
Require Import VST.veric.assert_lemmas.
Require Import VST.veric.Clight_new.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.semax_congruence.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.initial_world.
Require Import VST.veric.semax_call.
Require Import VST.veric.semax_straight.
Require Import VST.veric.semax_loop.
Require Import VST.veric.semax_switch.
Require Import VST.veric.semax_prog.
Require Import VST.veric.semax_ext.
Require Import VST.veric.SeparationLogic.
Require Import VST.veric.expr_rel.

Module Type SEPARATION_LOGIC_SOUNDNESS.

(*Declare Module ExtSpec: EXTERNAL_SPEC. *)
Declare Module CSL: CLIGHT_SEPARATION_LOGIC.

Import CSL.

Axiom semax_prog_rule :
  forall {Espec: OracleKind}{CS: compspecs},
  OK_ty = unit -> 
  forall V G prog m h,
     @semax_prog Espec CS prog V G ->
     Genv.init_mem prog = Some m ->
     { b : block & { q : corestate &
       (Genv.find_symbol (globalenv prog) (prog_main prog) = Some b) *
       (forall jm, m_dry jm = m -> exists jm', semantics.initial_core (juicy_core_sem (cl_core_sem (globalenv prog))) h
                    jm q jm' (Vptr b Ptrofs.zero) nil) *
       forall n,
         { jm |
           m_dry jm = m /\ level jm = n /\
           (forall z, jsafeN (@OK_spec Espec) (globalenv prog) n z q jm) /\
           no_locks (m_phi jm) /\
           matchfunspecs (globalenv prog) G (m_phi jm) /\
           app_pred (funassert (nofunc_tycontext V G) (empty_environ (globalenv prog))) (m_phi jm)
     } } }%type.

(* This version lets the user choose the external state instead of quantifying over it. *)
Axiom semax_prog_rule' :
  forall {Espec: OracleKind}{CS: compspecs},
  forall V G prog m h,
     @semax_prog Espec CS prog V G ->
     Genv.init_mem prog = Some m ->
     { b : block & { q : corestate &
       (Genv.find_symbol (globalenv prog) (prog_main prog) = Some b) *
       (forall jm, m_dry jm = m -> exists jm', semantics.initial_core (juicy_core_sem (cl_core_sem (globalenv prog))) h
                    jm q jm' (Vptr b Ptrofs.zero) nil) *
       forall n z,
         { jm |
           m_dry jm = m /\ level jm = n /\
           nth_error (ghost_of (m_phi jm)) 0 = Some (Some (ext_ghost z, NoneP)) /\
           jsafeN (@OK_spec Espec) (globalenv prog) n z q jm /\
           no_locks (m_phi jm) /\
           matchfunspecs (globalenv prog) G (m_phi jm) /\
           app_pred (funassert (nofunc_tycontext V G) (empty_environ (globalenv prog))) (m_phi jm)
     } } }%type.


End SEPARATION_LOGIC_SOUNDNESS.

Module SoundSeparationLogic : SEPARATION_LOGIC_SOUNDNESS.

Module CSL <: CLIGHT_SEPARATION_LOGIC.

Definition func_ptr (f: funspec) (v: val): mpred :=
  exp (fun b: block => andp (prop (v = Vptr b Ptrofs.zero)) (func_at f (b, 0))).

Transparent mpred Nveric Sveric Cveric Iveric Rveric Sveric SIveric SRveric.

Definition corable_func_ptr: forall f v, corable (func_ptr f v) :=
  assert_lemmas.corable_func_ptr.

Lemma func_ptr_isptr:
  forall spec f, (func_ptr spec f |-- !! isptr f)%logic.
Proof.
  intros.
  unfold func_ptr.
  destruct spec.
  normalize.
Qed.

Definition approx_func_ptr := approx_func_ptr.
Definition func_ptr_def := eq_refl func_ptr.

Opaque mpred Nveric Sveric Cveric Iveric Rveric Sveric SIveric SRveric.

Definition semax := @semax.
Definition unfold_Ssequence := unfold_Ssequence.
Definition extract_exists := @extract_exists.
Definition semax_body := @semax_body.
Definition semax_func := @semax_func.
Definition semax_prog := @semax_prog.
Definition semax_prog_ext := @semax_prog_ext.
Definition semax_func_nil := @semax_func_nil.
Definition semax_func_cons := @semax_func_cons.
(* Definition semax_func_skip := @semax_func_skip. *)
Definition make_ext_rval := veric.semax.make_ext_rval.
Definition tc_option_val := veric.semax.tc_option_val.
Definition semax_func_cons_ext := @semax_func_cons_ext.
Definition semax_seq := @semax_seq.
Definition semax_break := @semax_break.
Definition semax_continue := @semax_continue.
Definition semax_loop := @semax_loop.
Definition semax_loop_nocontinue := @semax_loop_nocontinue.
Definition semax_if_seq := @semax_if_seq.
Definition semax_switch := @semax_switch.
Definition semax_Slabel := @semax_Slabel.
Definition semax_seq_Slabel := @semax_seq_Slabel.
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
Definition semax_pre_post_bupd := @semax_pre_post_bupd.
Definition semax_extensionality_Delta := @semax_extensionality_Delta.
Definition semax_extract_prop := @semax_extract_prop.
Definition semax_extract_later_prop := @semax_extract_later_prop.
Definition semax_ptr_compare := @semax_ptr_compare.
Definition semax_unfold_Ssequence := @semax_unfold_Ssequence.
Definition semax_external {Espec: OracleKind} ids ef A P Q :=
  forall n, semax_external Espec ids ef A P Q n.
Definition semax_external_FF := @semax_external_FF.

Definition juicy_ext_spec := juicy_ext_spec.

Definition semax_ext := @semax_ext.
Definition semax_ext_void := @semax_ext_void.

End CSL.

Definition semax_prog_rule := @semax_prog_rule.
Definition semax_prog_rule' := @semax_prog_rule'.

End SoundSeparationLogic.
