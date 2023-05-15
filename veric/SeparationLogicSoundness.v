Require Import VST.sepcomp.semantics.

Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas.
Require Import VST.veric.external_state.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_core.
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

Module Type SEPARATION_HOARE_LOGIC_SOUNDNESS.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Module CSHL_Defs := DerivedDefs(CSHL_Def).

Import CSHL_Def.
Import CSHL_Defs.

Axiom semax_prog_sound :
  forall `{H : heapGS Σ}{Espec: OracleKind}{HE : externalGS OK_ty Σ}{CS: compspecs} prog z Vspec Gspec,
  @semax_prog Σ H Espec HE CS prog z Vspec Gspec ->
  @semax_prog.semax_prog Σ H Espec HE CS prog z Vspec Gspec.

Axiom semax_prog_rule :
  forall `{H : heapGS Σ}{Espec: OracleKind}{HE : externalGS OK_ty Σ}{CS: compspecs},
  forall V G prog m h z,
     @postcondition_allows_exit _ Espec tint ->
     @semax_prog Σ H Espec HE CS prog z V G ->
     Genv.init_mem prog = Some m ->
     { b : block & { q : CC_core &
       (exists m', semantics.initial_core (cl_core_sem (globalenv prog)) h
                       m q m' (Vptr b Ptrofs.zero) nil) *
       (state_interp Mem.empty z ∗ has_ext z ⊢ |==> state_interp m z ∗ jsafeN Espec (globalenv prog) ⊤ z q ∗
           (*no_locks ∧ □ matchfunspecs (globalenv prog) G ⊤ ∗*) funassert (nofunc_tycontext V G) (empty_environ (globalenv prog)))
     } }%type.

End SEPARATION_HOARE_LOGIC_SOUNDNESS.

Module Type MAIN_THEOREM_STATEMENT.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Declare Module CSHL_MinimumLogic: MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC with Module CSHL_Def := CSHL_Def.

Declare Module CSHL_PracticalLogic: PRACTICAL_CLIGHT_SEPARATION_HOARE_LOGIC with Module CSHL_MinimumLogic := CSHL_MinimumLogic.

Declare Module CSHL_Sound: SEPARATION_HOARE_LOGIC_SOUNDNESS with Module CSHL_Def := CSHL_Def.

End MAIN_THEOREM_STATEMENT.

Module VericDef <: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Definition semax := @semax.

Definition semax_func := @semax_func.

Definition semax_external := @semax_external.

End VericDef.

Module VericMinimumSeparationLogic: MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC with Module CSHL_Def := VericDef.

Module CSHL_Def := VericDef.
Module CSHL_Defs := DerivedDefs (VericDef).

Lemma semax_extract_exists: forall `{!heapGS Σ} Espec `{!externalGS OK_ty Σ} {CS: compspecs} E (A : Type) (P : A -> assert) c (Delta: tycontext) (R: ret_assert),
  (forall x, semax Espec E Delta (P x) c R) ->
   semax Espec E Delta (∃ x:A, P x) c R.
Proof.
  intros; eapply semax_pre, extract_exists_pre, H.
  intros; rewrite bi.and_elim_r; monPred.unseal; done.
Qed.

Definition semax_body := @semax_body.
Definition semax_prog := @semax_prog.
Definition semax_func_nil := @semax_func_nil.
Definition semax_func_cons := @semax_func_cons.
Definition make_ext_rval := veric.semax.make_ext_rval.
Definition tc_option_val := veric.semax.tc_option_val.

Lemma semax_func_cons_ext: forall `{HH: heapGS Σ}{Espec:OracleKind}{HE: externalGS OK_ty Σ} (V: varspecs) (G: funspecs)
     {C: compspecs} ge E fs id ef argsig retsig A P Q argsig'
      (G': funspecs) cc b,
  argsig' = typelist2list argsig ->
  ef_sig ef = mksignature (typlist_of_typelist argsig) (rettype_of_type retsig) cc ->
  id_in_list id (map (@fst _ _) fs) = false ->
  (ef_inline ef = false \/ withtype_empty A) ->
  (forall gx x (ret : option val),
      Q x (make_ext_rval gx (rettype_of_type retsig) ret) ∧
      ⌜Builtins0.val_opt_has_rettype ret (rettype_of_type retsig)⌝ ⊢
      ⌜tc_option_val retsig ret⌝) ->
  Genv.find_symbol ge id = Some b ->
  Genv.find_funct_ptr ge b = Some (Ctypes.External ef argsig retsig cc) ->
  (⊢ @CSHL_Def.semax_external _ HH Espec HE E ef A P Q) ->
  CSHL_Def.semax_func _ HH Espec HE V G C ge E fs G' ->
  CSHL_Def.semax_func _ HH Espec HE V G C ge E ((id, Ctypes.External ef argsig retsig cc)::fs)
             ((id, mk_funspec (argsig', retsig) cc A P Q)  :: G').
Proof. intros. eapply semax_func_cons_ext; eauto. Qed.

Definition semax_Delta_subsumption := @semax_lemmas.semax_Delta_subsumption.

(*Lemma semax_external_binaryintersection: forall
 {Espec ef A1 P1 Q1 P1ne Q1ne A2 P2 Q2 P2ne Q2ne A P Q P_ne Q_ne sig cc}
  (EXT1: @CSHL_Def.semax_external Espec ef A1 P1 Q1)
  (EXT2: @CSHL_Def.semax_external Espec ef A2 P2 Q2)
  (BI: binary_intersection (mk_funspec sig cc A1 P1 Q1 P1ne Q1ne) 
                      (mk_funspec sig cc A2 P2 Q2 P2ne Q2ne) =
     Some (mk_funspec sig cc A P Q P_ne Q_ne))
  (LEN: length (fst sig) = length (sig_args (ef_sig ef))),
  @CSHL_Def.semax_external Espec ef A P Q. 
Proof. intros. intros n. eapply semax_external_binaryintersection. apply EXT1. apply EXT2. apply BI. trivial. Qed.*)

Lemma semax_external_funspec_sub: forall `{HH : heapGS Σ}
  {Espec HE E argtypes rtype cc ef A1 P1 Q1 A P Q}
  (Hsub: funspec_sub E (mk_funspec (argtypes, rtype) cc A1 P1 Q1)
                   (mk_funspec (argtypes, rtype) cc A P Q))
  (HSIG: ef_sig ef =
         mksignature (map typ_of_type argtypes)
                     (rettype_of_type rtype) cc),
  @CSHL_Def.semax_external _ HH Espec HE E ef A1 P1 Q1 ⊢
  @CSHL_Def.semax_external _ HH Espec HE E ef A P Q.
Proof.
  intros. eapply semax_external_funspec_sub; eauto.
Qed.

(*Definition semax_body_binaryintersection := @semax_body_binaryintersection.*)

Definition semax_func_mono := @semax_func_mono.
Definition semax_func_app := @semax_func_app.
Definition semax_func_subsumption := @semax_func_subsumption.
Definition semax_func_join  := @semax_func_join.
Definition semax_func_firstn := @semax_func_firstn.
Definition semax_func_skipn := @semax_func_skipn.
Definition semax_body_subsumption := @semax_body_subsumption.
Definition semax_body_cenv_sub := @semax_body_cenv_sub.

Lemma semax_body_funspec_sub:
  forall `{!heapGS Σ} {Espec : OracleKind} `{!externalGS OK_ty Σ} (V : varspecs) (G : funspecs) (cs : compspecs) E (f : function) 
   (i : ident) (phi phi' : funspec),
 CSHL_Defs.semax_body V G E f (i, phi) ->
 funspec_sub E phi phi' ->
 list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)) ->
 CSHL_Defs.semax_body V G E f (i, phi').
Proof.
  intros. eapply semax_body_funspec_sub; eauto.
Qed.

Definition semax_seq := @semax_seq.
Definition semax_break := @semax_break.
Definition semax_continue := @semax_continue.
Definition semax_loop := @semax_loop.

Lemma semax_switch : forall `{HH: heapGS Σ}{Espec:OracleKind}{HE: externalGS OK_ty Σ}{CS: compspecs}
  E Delta (Q: assert) a sl R,
     is_int_type (typeof a) = true ->
     (forall rho, Q rho ⊢ tc_expr Delta a rho) ->
     (forall n,
     semax Espec E Delta 
               (local (liftx eq (eval_expr a) (liftx (Vint n))) ∧ Q)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) ->
     semax Espec E Delta Q (Sswitch a sl) R.
Proof.
  intros; eapply semax_switch; try done.
  intros; eapply semax_pre, H1.
  intros; rewrite bi.and_elim_r; monPred.unseal; done.
Qed.

Definition semax_Slabel := @semax_Slabel.
Definition semax_set_forward := @semax_set_forward.
Definition semax_ifthenelse := @semax_ifthenelse.

Lemma semax_return `{HH : !heapGS Σ} {Espec} `{HE : !externalGS OK_ty Σ} {CS}:
   forall E Delta (R: ret_assert) ret,
      semax Espec E Delta
                (tc_expropt Delta ret (ret_type Delta) ∧
                (assert_of (liftx (RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ))))
                (Sreturn ret)
                R.
Proof.
  intros; eapply semax_pre, semax_return.
  intros; rewrite bi.and_elim_r; monPred.unseal; done.
Qed.

(* Why are the implicits so inconsistent here? *)
Lemma semax_call `{HH : !heapGS Σ} {Espec} `{HE : !externalGS OK_ty Σ} {CS}:
  forall E Delta (A: Type)
  (P : A -> argsEnviron -> mpred)
  (Q : A -> environ -> mpred)
  (x : A)
   F ret id argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
            (retsig = Ctypes.Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax _ HH Espec HE CS E Delta
       ((tc_expr Delta a ∧ tc_exprlist Delta argsig bl) ∧
         (assert_of (fun rho => func_ptr (ge_of rho) E id (mk_funspec (argsig,retsig) cc A P Q) (eval_expr a rho)) ∗
          (▷(F ∗ assert_of (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho))))))
         (Scall ret a bl)
         (normal_ret_assert (∃ old:val, assert_of (substopt ret (liftx old) F) ∗ maybe_retval (Q x) retsig ret)).
Proof.
  intros. eapply semax_pre_post, semax_call_si; try done; [| by intros; rewrite bi.and_elim_r; monPred.unseal..].
  intros; rewrite bi.and_elim_r; monPred.unseal; apply bi.and_mono; [apply bi.later_intro | done].
Qed.

Lemma semax_store: forall `{HH : !heapGS Σ} (CS : compspecs) (Espec : OracleKind) `{HE : !externalGS OK_ty Σ}
         E (Delta : tycontext) (e1 e2 : expr) (sh : share)
         (P : environ -> mpred),
       writable_share sh ->
       semax Espec E Delta
         (fun rho : environ =>
          (▷ (tc_lvalue Delta e1 rho ∧
              tc_expr Delta (Ecast e2 (typeof e1)) rho ∧
               (mapsto_ sh (typeof e1) (eval_lvalue e1 rho) ∗
                P rho)))) (Sassign e1 e2)
         (normal_ret_assert
            (fun rho : environ =>
             (mapsto_memory_block.mapsto sh (typeof e1)
                (eval_lvalue e1 rho)
                (force_val
                   (sem_cast (typeof e2) (typeof e1) (eval_expr e2 rho))) ∗
              P rho))).
Proof.
intros; apply semax_store; auto.
Qed.

Definition semax_store_union_hack := @semax_store_union_hack.

Definition semax_load := @semax_load.
Definition semax_cast_load := @semax_cast_load.
Definition semax_skip := @semax_skip.
Definition semax_frame := @semax_frame.
Definition semax_conseq := @semax_conseq.
Definition semax_ptr_compare := @semax_ptr_compare.
Definition semax_external_FF := @semax_external_FF.

Definition juicy_ext_spec := @juicy_ext_spec.

Definition semax_ext := @semax_ext.

End VericMinimumSeparationLogic.

Module VericSound : SEPARATION_HOARE_LOGIC_SOUNDNESS with Module CSHL_Def := VericDef.

Module CSHL_Def := VericDef.
Module CSHL_Defs := DerivedDefs (VericDef).

Lemma semax_prog_sound :
  forall `{HH : heapGS Σ}{Espec}{HE : externalGS OK_ty Σ}{CS} prog z Vspec Gspec,
  @CSHL_Defs.semax_prog _ HH Espec HE CS prog z Vspec Gspec ->
  @semax_prog.semax_prog _ HH Espec HE CS prog z Vspec Gspec.
Proof.
  intros; apply H.
Qed.

Definition semax_prog_rule := @semax_prog_rule.

End VericSound.

