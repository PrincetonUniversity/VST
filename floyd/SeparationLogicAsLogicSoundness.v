From compcert Require Export Clightdefs.
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
Require Import VST.floyd.SeparationLogicFacts.
Require Import VST.floyd.SeparationLogicAsLogic.
Require Import VST.veric.SeparationLogicSoundness.
Local Open Scope logic.
Require Import VST.veric.ghost_PCM.

Module DeepEmbeddedSoundness
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (MinimumLogic: MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC with Module CSHL_Def := Def)
       (Sound: SEPARATION_HOARE_LOGIC_SOUNDNESS with Module CSHL_Def := Def)
       <: SEPARATION_HOARE_LOGIC_SOUNDNESS.

Module DeepEmbedded := DeepEmbedded (Def) (MinimumLogic).

Module CSHL_Def := DeepEmbedded.DeepEmbeddedDef.

Module CSHL_Defs := DeepEmbedded.DeepEmbeddedDefs.

Arguments CSHL_Def.semax {_} {_} _ _ _ _.

Module Conseq := GenConseq (Def) (MinimumLogic).

Module ExtrFacts := GenExtrFacts (Def) (Conseq) (MinimumLogic).

Import Conseq ExtrFacts.

Module CallF: CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
  
Definition semax_call_forward := @MinimumLogic.semax_call.

End CallF.

Module CallB := CallF2B (Def) (Conseq) (MinimumLogic) (CallF).

Module SetF: CLIGHT_SEPARATION_HOARE_LOGIC_SET_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
  
Definition semax_set_forward := @MinimumLogic.semax_set_forward.

End SetF.

Module SetB := SetF2B (Def) (Conseq) (MinimumLogic) (SetF).

Module PtrCmpF: CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
  
Definition semax_ptr_compare_forward := @MinimumLogic.semax_ptr_compare.

End PtrCmpF.

Module PtrCmpB := PtrCmpF2B (Def) (Conseq) (MinimumLogic) (PtrCmpF).

Module LoadF: CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
  
Definition semax_load_forward := @MinimumLogic.semax_load.

End LoadF.

Module LoadB := LoadF2B (Def) (Conseq) (MinimumLogic) (LoadF).

Module CastLoadF: CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
  
Definition semax_cast_load_forward := @MinimumLogic.semax_cast_load.

End CastLoadF.

Module CastLoadB := CastLoadF2B (Def) (Conseq) (MinimumLogic) (CastLoadF).

Module StoreF: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
  
Definition semax_store_forward := @MinimumLogic.semax_store.

End StoreF.

Module StoreB := StoreF2B (Def) (Conseq) (MinimumLogic) (StoreF).

Module Extr : CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def := MinimumLogic.

Module Sset := ToSset (Def) (Conseq) (Extr) (SetB) (PtrCmpB) (LoadB) (CastLoadB).

Theorem semax_sound: forall Espec CS Delta P c Q,
  @DeepEmbedded.DeepEmbeddedDef.semax Espec CS Delta P c Q ->
  @Def.semax Espec CS Delta P c Q.
Proof.
  intros.
  induction H.
  + rewrite andp_assoc.
    apply semax_extract_prop.
    intros.
    apply MinimumLogic.semax_ifthenelse; auto.
  + eapply MinimumLogic.semax_seq; eauto.
  + apply MinimumLogic.semax_break.
  + apply MinimumLogic.semax_continue.
  + eapply MinimumLogic.semax_loop; eauto.
  + apply semax_extract_prop.
    intros.
    apply MinimumLogic.semax_switch; auto.
  + apply CallB.semax_call_backward.
  + apply MinimumLogic.semax_return.
  + apply Sset.semax_set_ptr_compare_load_cast_load_backward.
  + apply StoreB.semax_store_backward.
  + apply MinimumLogic.semax_skip.
  + rewrite <- (andp_dup FF).
    unfold FF at 1.
    apply semax_extract_prop.
    tauto.
  + apply MinimumLogic.semax_Slabel; auto.
  + rewrite <- (andp_dup FF).
    unfold FF at 1.
    apply semax_extract_prop.
    tauto.
  + eapply MinimumLogic.semax_conseq; eauto.
Qed.

Theorem semax_body_sound: forall Vspec Gspec CS f id,
  @DeepEmbedded.DeepEmbeddedDefs.semax_body Vspec Gspec CS f id ->
  @MinimumLogic.CSHL_Defs.semax_body Vspec Gspec CS f id.
Proof.
  intros.
  unfold MinimumLogic.CSHL_Defs.semax_body, CSHL_Defs.semax_body in H |- *.
  destruct id.
  destruct f0.
  intros.
  apply semax_sound.
  apply H.
Qed.

Theorem semax_func_sound: forall Espec Vspec Gspec CS ge ids fs,
  @DeepEmbedded.DeepEmbeddedDef.semax_func Espec Vspec Gspec CS ge ids fs ->
  @Def.semax_func Espec Vspec Gspec CS ge ids fs.
Proof.
  intros.
  induction H.
  + apply MinimumLogic.semax_func_nil.
  + eapply MinimumLogic.semax_func_cons; eauto.
    apply semax_body_sound; auto.
  + eapply MinimumLogic.semax_func_cons_ext; eauto.
  + apply (@MinimumLogic.semax_func_mono Espec _ _ CSUB ge ge' Gfs Gffp); auto.
  + apply MinimumLogic.semax_func_app; auto.
  + eapply MinimumLogic.semax_func_subsumption; eauto.
  + eapply MinimumLogic.semax_func_join; eauto.
  + eapply MinimumLogic.semax_func_firstn; eauto.
  + eapply MinimumLogic.semax_func_skipn; eauto.
Qed.

Theorem semax_prog_sound': forall 
     (Espec: OracleKind) (CS: compspecs)
     (prog: program)  (V: varspecs) (G: funspecs),
  @DeepEmbedded.DeepEmbeddedDefs.semax_prog Espec CS prog V G ->
  @MinimumLogic.CSHL_Defs.semax_prog Espec CS prog V G.
Proof.
  intros.
  hnf in H |- *.
  pose proof (@semax_func_sound Espec V G CS (Genv.globalenv prog) (prog_funct prog) G).
  tauto.
Qed.

Theorem semax_prog_ext_sound': forall Espec CS prog z Vspec Gspec,
  @DeepEmbedded.DeepEmbeddedDefs.semax_prog_ext Espec CS prog z Vspec Gspec ->
  @MinimumLogic.CSHL_Defs.semax_prog_ext Espec CS prog z Vspec Gspec.
Proof.
  intros.
  hnf in H |- *.
  pose proof semax_func_sound Espec Vspec Gspec CS (Genv.globalenv prog) (prog_funct prog) Gspec.
  tauto.
Qed.

Theorem semax_prog_sound: forall Espec CS prog Vspec Gspec,
  @DeepEmbedded.DeepEmbeddedDefs.semax_prog Espec CS prog Vspec Gspec ->
  @semax_prog.semax_prog Espec CS prog Vspec Gspec.
Proof.
  intros.
  apply Sound.semax_prog_sound, semax_prog_sound'; auto.
Qed.

Theorem semax_prog_ext_sound: forall Espec CS prog z Vspec Gspec,
  @DeepEmbedded.DeepEmbeddedDefs.semax_prog_ext Espec CS prog z Vspec Gspec ->
  @semax_prog.semax_prog_ext Espec CS prog z Vspec Gspec.
Proof.
  intros.
  apply Sound.semax_prog_ext_sound, semax_prog_ext_sound'; auto.
Qed.

Theorem semax_prog_rule :
  forall {Espec: OracleKind}{CS: compspecs},
  OK_ty = unit -> 
  forall V G prog m h,
     @DeepEmbedded.DeepEmbeddedDefs.semax_prog Espec CS prog V G ->
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
Proof.
  intros.
  apply Sound.semax_prog_rule; auto.
  apply semax_prog_sound'; auto.
Qed.

Theorem semax_prog_rule' :
  forall {Espec: OracleKind}{CS: compspecs},
  forall V G prog m h,
     @DeepEmbedded.DeepEmbeddedDefs.semax_prog Espec CS prog V G ->
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
Proof.
  intros.
  apply Sound.semax_prog_rule'; auto.
  apply semax_prog_sound'; auto.
Qed.

Theorem semax_prog_rule_ext :
  forall {Espec: OracleKind}{CS: compspecs},
  forall V G prog m h z,
     @DeepEmbedded.DeepEmbeddedDefs.semax_prog_ext Espec CS prog z V G ->
     Genv.init_mem prog = Some m ->
     { b : block & { q : corestate &
       (Genv.find_symbol (globalenv prog) (prog_main prog) = Some b) *
       (forall jm, m_dry jm = m -> exists jm', semantics.initial_core (juicy_core_sem (cl_core_sem (globalenv prog))) h
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
Proof.
  intros.
  apply Sound.semax_prog_rule_ext; auto.
  apply semax_prog_ext_sound'; auto.
Qed.

End DeepEmbeddedSoundness.

(********************************************************)
(*                                                      *)
(*            Main Theorem of Verifiable C              *)
(*                                                      *)
(********************************************************)

Module MainTheorem: MAIN_THEOREM_STATEMENT.

Module DeepEmbedded := DeepEmbedded (VericDef) (VericMinimumSeparationLogic).

Import DeepEmbedded.

Module CSHL_Def := DeepEmbeddedDef.

Module CSHL_Defs := DeepEmbeddedDefs.

Module CSHL_MinimumLogic := DeepEmbeddedMinimumSeparationLogic.

Module CSHL_PracticalLogic := DeepEmbeddedPracticalLogic.

Module CSHL_Sound := DeepEmbeddedSoundness (VericDef) (VericMinimumSeparationLogic) (VericSound).

End MainTheorem.
