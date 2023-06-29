Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.base.
Require Import VST.veric.Clight_language.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.mpred.
Require Import VST.veric.external_state.
Require Import VST.veric.compspecs.
Require Import VST.veric.semax_prog.
Require Import VST.veric.SequentialClight.
Require Import VST.veric.NullExtension.

Definition null_extension_extspec : external_specification mem external_function unit
  := Build_external_specification mem external_function unit
     (*ext_spec_type*)
     (fun ef => False)
     (*ext_spec_pre*)
     (fun ef Hef ge tys vl m z => False)
     (*ext_spec_post*)
     (fun ef Hef ge ty vl m z => False)
     (*ext_spec_exit*)
     (fun rv m z => True).

Theorem VST_sound: 
  {Espec : OracleKind 
  | JMeq.JMeq (@OK_spec Espec) null_extension_extspec /\
  forall (CS: compspecs) `(!VSTGpreS OK_ty Σ)
     (prog: Clight.program) (initial_oracle: OK_ty)
     (V : mpred.varspecs) (G : mpred.funspecs) (m: mem),
     (forall {HH : heapGS Σ} {HE : externalGS OK_ty Σ}, @semax_prog _ HH Espec HE CS prog initial_oracle V G) ->
     Genv.init_mem prog = Some m ->
     exists b, exists q, exists m',
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       semantics.initial_core  (Clight_core.cl_core_sem (Clight.globalenv prog))
           0 m q m' (Vptr b Ptrofs.zero) nil /\
       forall n,
        @dry_safeN _ _ _ unit (genv_symb_injective)
          (Clight_core.cl_core_sem (Clight.globalenv prog)) null_extension_extspec
           (Clight.genv_genv 
            (Clight.Build_genv (Genv.globalenv prog) (Ctypes.prog_comp_env prog)) )
             n tt q m'}.
Proof.
intros.
exists NullExtension.Espec.
split.
reflexivity.
intros.
destruct initial_oracle.
eapply NullExtension_whole_program_sequential_safety; eassumption.
Qed.

Print Assumptions VST_sound.
