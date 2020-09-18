Require Import VST.sepcomp.semantics.

Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
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

Require Import VST.veric.ghost_PCM.

Module Type SEPARATION_HOARE_LOGIC_SOUNDNESS.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Module CSHL_Defs := DerivedDefs(CSHL_Def).

Import CSHL_Def.
Import CSHL_Defs.

Axiom semax_prog_sound :
  forall {Espec: OracleKind}{CS: compspecs} prog z Vspec Gspec,
  @semax_prog Espec CS prog z Vspec Gspec ->
  @semax_prog.semax_prog Espec CS prog z Vspec Gspec.

Axiom semax_prog_rule :
  forall {Espec: OracleKind}{CS: compspecs},
  forall V G prog m h z,
     postcondition_allows_exit Espec tint ->
     @semax_prog Espec CS prog z V G ->
     Genv.init_mem prog = Some m ->
     { b : block & { q : CC_core &
       (Genv.find_symbol (globalenv prog) (prog_main prog) = Some b) *
       (forall jm, m_dry jm = m -> exists jm',
                    semantics.initial_core (juicy_core_sem (cl_core_sem (globalenv prog))) h
                       jm q jm' (Vptr b Ptrofs.zero) nil) *
       forall n,
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

Definition semax_external {Espec: OracleKind} (*ids*) ef A P Q :=
  forall n, semax_external Espec (*ids*) ef A P Q n.

(*
Definition semax_cssub := @semax_cssub.
  *)
End VericDef.

Module VericMinimumSeparationLogic: MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC with Module CSHL_Def := VericDef.

Module CSHL_Def := VericDef.
Module CSHL_Defs := DerivedDefs (VericDef).
  
Definition semax_extract_exists := @extract_exists_pre.
Definition semax_body := @semax_body.
Definition semax_prog := @semax_prog.
Definition semax_func_nil := @semax_func_nil.
Definition semax_func_cons := @semax_func_cons.
(* Definition semax_func_skip := @semax_func_skip. *)
Definition make_ext_rval := veric.semax.make_ext_rval.
Definition tc_option_val := veric.semax.tc_option_val.
Definition semax_func_cons_ext := @semax_func_cons_ext.
Definition semax_Delta_subsumption := @semax_lemmas.semax_Delta_subsumption.

Lemma semax_external_binaryintersection: forall
 {Espec ef A1 P1 Q1 P1ne Q1ne A2 P2 Q2 P2ne Q2ne A P Q P_ne Q_ne sig cc (*ids*)}
  (EXT1: @CSHL_Def.semax_external Espec (*ids*) ef A1 P1 Q1)
  (EXT2: @CSHL_Def.semax_external Espec (*ids*) ef A2 P2 Q2)
  (BI: binary_intersection (mk_funspec sig cc A1 P1 Q1 P1ne Q1ne) 
                      (mk_funspec sig cc A2 P2 Q2 P2ne Q2ne) =
     Some (mk_funspec sig cc A P Q P_ne Q_ne))
  (*(IDS: ids = map fst (fst sig))*)
  (LEN: length (fst sig) = length (sig_args (ef_sig ef))),
  @CSHL_Def.semax_external Espec (*ids*) ef A P Q. 
Proof. intros. intros n. eapply semax_external_binaryintersection. apply EXT1. apply EXT2. apply BI. trivial. Qed.

Lemma semax_external_funspec_sub: forall {Espec argtypes rtype cc ef A1 P1 Q1 P1ne Q1ne A P Q Pne Qne}
  (Hsub: funspec_sub (mk_funspec (argtypes, rtype) cc A1 P1 Q1 P1ne Q1ne) 
                   (mk_funspec (argtypes, rtype) cc A P Q Pne Qne))
  (HSIG: ef_sig ef = 
         mksignature (map typ_of_type argtypes)
                     (rettype_of_type rtype) cc)
  (SE: @CSHL_Def.semax_external Espec ef A1 P1 Q1),
  @CSHL_Def.semax_external Espec ef A P Q.
Proof. intros. intros n. eapply semax_external_funspec_sub. apply Hsub. trivial. trivial. Qed.

Definition semax_body_binaryintersection := @semax_body_binaryintersection.

Definition semax_func_mono := semax_func_mono.
Definition semax_func_app := semax_func_app.
Definition semax_func_subsumption := semax_func_subsumption.
Definition semax_func_join  := semax_func_join.
Definition semax_func_firstn := semax_func_firstn.
Definition semax_func_skipn := semax_func_skipn.
Definition semax_body_subsumption:= semax_body_subsumption.
Definition semax_body_cenv_sub:= @semax_body_cenv_sub.
Definition semax_body_funspec_sub:= @semax_body_funspec_sub.

Definition semax_seq := @semax_seq.
Definition semax_break := @semax_break.
Definition semax_continue := @semax_continue.
Definition semax_loop := @semax_loop.
Definition semax_switch := @semax_switch.
Definition semax_Slabel := @semax_Slabel.

(*See below
Definition semax_call := @semax_call_si.*)
(* Definition semax_call_ext := @semax_call_ext. *)

Definition semax_set_forward := @semax_set_forward.
Definition semax_ifthenelse := @semax_ifthenelse.
Definition semax_return := @semax_return.

Import VST.msl.seplog VST.veric.lift.

Lemma semax_call {CS Espec}:
  forall Delta (A: TypeTree)
  (P : forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
  (Q : forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
  (NEP: args_super_non_expansive P) (NEQ: super_non_expansive Q)
  (ts: list Type) (x : dependent_type_functor_rec ts A mpred)
   F ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
            (retsig = Ctypes.Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
       (fun rho => ((*|>*)(tc_expr Delta a rho && tc_exprlist Delta argsig bl rho))  &&
           (func_ptr (mk_funspec (argsig,retsig) cc A P Q NEP NEQ) (eval_expr a rho) &&
          (|>(F rho * P ts x (ge_of rho, eval_exprlist argsig bl rho)))))%pred
         (Scall ret a bl)
         (normal_ret_assert
            (@exp
               (forall _ : environ,
                functors.MixVariantFunctor._functor functors.MixVariantFunctorGenerator.fidentity
                  mpred)
               (@LiftNatDed'
                  (functors.MixVariantFunctor._functor
                     functors.MixVariantFunctorGenerator.fidentity mpred) Nveric) val
               (fun old : val =>
                @sepcon
                  (forall _ : environ,
                   functors.MixVariantFunctor._functor
                     functors.MixVariantFunctorGenerator.fidentity mpred)
                  (@LiftNatDed'
                     (functors.MixVariantFunctor._functor
                        functors.MixVariantFunctorGenerator.fidentity mpred) Nveric)
                  (@LiftSepLog'
                     (functors.MixVariantFunctor._functor
                        functors.MixVariantFunctorGenerator.fidentity mpred) Nveric Sveric)
                  (@substopt
                     (functors.MixVariantFunctor._functor
                        functors.MixVariantFunctorGenerator.fidentity mpred) ret
                     (@liftx (LiftEnviron val) old) F) (maybe_retval (Q ts x) retsig ret)))).
Proof.
  intros. specialize (@semax_call_si CS Espec Delta A P Q NEP NEQ ts x F ret argsig retsig cc a bl H H0 H1); intros X.
  eapply semax_pre; [| apply X].
  intros. simpl. intros w [TC [W1 W2]]; split; trivial.
  eapply predicates_hered.now_later. rewrite <- tc_expr_eq; apply W1.
Qed. 

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

Definition semax_store_union_hack := @semax_store_union_hack.
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

Lemma semax_prog_sound :
  forall {Espec}{CS} prog z Vspec Gspec,
  @CSHL_Defs.semax_prog Espec CS prog z Vspec Gspec ->
  @semax_prog.semax_prog Espec CS prog z Vspec Gspec.
Proof.
  intros; apply H.
Qed.

Definition semax_prog_rule := @semax_prog_rule.

End VericSound.

