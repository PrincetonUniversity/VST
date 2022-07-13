Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.base.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.compspecs.
Require Import VST.veric.semax_prog.
Require Import VST.veric.SequentialClight2.
Require Import VST.veric.NullExtension.

Definition null_extension_juicyspec : external_specification juicy_mem external_function unit
  := Build_external_specification juicy_mem external_function unit
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
  | JMeq.JMeq (JE_spec _ (@OK_spec Espec)) null_extension_juicyspec /\
  let dryspec :=  juicy_dry_ext_spec_make _ null_extension_juicyspec in 
  forall (CS: compspecs)
     (prog: Clight.program) (initial_oracle: OK_ty)
     (V : mpred.varspecs) (G : mpred.funspecs) (m: mem),
     @semax_prog Espec CS prog initial_oracle V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q, exists m',
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       semantics.initial_core  (Clight_core.cl_core_sem (Clight.globalenv prog))
           0 m q m' (Vptr b Ptrofs.zero) nil /\
       forall n,
        @dry_safeN _ _ _ unit (semax.genv_symb_injective)
          (Clight_core.cl_core_sem (Clight.globalenv prog)) dryspec
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
