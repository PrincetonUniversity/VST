Require Import VST.sepcomp.semantics.

Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_new.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.semax_conseq.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.Clight_initial_world.
Require Import VST.veric.semax_call.
Require Import VST.veric.semax_straight.
Require Import VST.veric.semax_loop.
Require Import VST.veric.semax_switch.
Require Import VST.veric.semax_prog.
Require Import VST.veric.semax_ext.
Require Import VST.veric.SeparationLogic.
Require Import VST.veric.expr_rel.

Require Import VST.veric.ghost_PCM.

Module Type SEPARATION_HOARE_LOGIC_SOUNDNESS.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Module CSHL_Defs := DerivedDefs(CSHL_Def).

Import CSHL_Def.
Import CSHL_Defs.

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


End SEPARATION_HOARE_LOGIC_SOUNDNESS.

Module Type MAIN_THEOREM_STATEMENT.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Declare Module CSHL_MinimumLogic: MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC with Module CSHL_Def := CSHL_Def.
(*
Definition corable_func_ptr: forall f v, corable (func_ptr f v) :=
  general_assert_lemmas.corable_func_ptr.*)
Declare Module CSHL_PracticalLogic: PRACTICAL_CLIGHT_SEPARATION_HOARE_LOGIC with Module CSHL_MinimumLogic := CSHL_MinimumLogic.

Declare Module CSHL_Sound: SEPARATION_HOARE_LOGIC_SOUNDNESS with Module CSHL_Def := CSHL_Def.

End MAIN_THEOREM_STATEMENT.

Module VericDef <: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Definition semax := @semax.

Definition semax_func := @semax_func.

Definition semax_external {Espec: OracleKind} ids ef A P Q :=
  forall n, semax_external Espec ids ef A P Q n.

End VericDef.

Module VericMinimumSeparationLogic: MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC with Module CSHL_Def := VericDef.

Module CSHL_Def := VericDef.
Module CSHL_Defs := DerivedDefs (VericDef).
  
Definition semax_extract_exists := @extract_exists_pre.
Definition semax_body := @semax_body.
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
Definition semax_switch := @semax_switch.
Definition semax_Slabel := @semax_Slabel.
Definition semax_call := @semax_call.
(* Definition semax_call_ext := @semax_call_ext. *)
Definition semax_set_forward := @semax_set_forward.
Definition semax_ifthenelse := @semax_ifthenelse.
Definition semax_return := @semax_return.

Lemma semax_store:forall (CS : compspecs) (Espec : OracleKind) 
         (Delta : tycontext) (e1 e2 : expr) (sh : share)
         (P : environ -> pred rmap),
       writable_share sh ->
       semax Espec Delta
         (fun rho : environ =>
          (|> (extend_tc.tc_lvalue Delta e1 rho &&
               extend_tc.tc_expr Delta (Ecast e2 (typeof e1)) rho &&
               (mapsto_memory_block.mapsto_ sh 
                  (typeof e1) (eval_lvalue e1 rho) * 
                P rho)))%pred) (Sassign e1 e2)
         (Clight_seplog.normal_ret_assert
            (fun rho : environ =>
             (mapsto_memory_block.mapsto sh (typeof e1)
                (eval_lvalue e1 rho)
                (force_val
                   (sem_cast (typeof e2) (typeof e1) (eval_expr e2 rho))) *
              P rho)%pred)).
Proof.
intros; apply semax_store; auto.
Qed.

(*Definition semax_store := @semax_store. *)

Definition semax_load := @semax_load.
Definition semax_cast_load := @semax_cast_load.
Definition semax_skip := @semax_skip.
Definition semax_frame := @semax_frame.
Definition semax_conseq := @semax_conseq.
Definition semax_ptr_compare := @semax_ptr_compare.
Definition semax_external_FF := @semax_external_FF.

Definition juicy_ext_spec := juicy_ext_spec.

Definition semax_ext := @semax_ext.
Definition semax_ext_void := @semax_ext_void.

End VericMinimumSeparationLogic.

Module VericSound : SEPARATION_HOARE_LOGIC_SOUNDNESS with Module CSHL_Def := VericDef.

Module CSHL_Def := VericDef.
Module CSHL_Defs := DerivedDefs (VericDef).

Definition semax_prog_rule := @semax_prog_rule.
Definition semax_prog_rule' := @semax_prog_rule'.

End VericSound.

