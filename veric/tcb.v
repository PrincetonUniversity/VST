Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.base.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.mpred.
Require Import VST.veric.external_state.
Require Import VST.veric.compspecs.
Require Import VST.veric.semax_prog.
Require Import VST.veric.SequentialClight.
Require Import VST.veric.NullExtension.

Theorem VST_sound: 
  forall (CS: compspecs) `(!VSTGpreS unit Σ)
     (prog: Clight.program) (initial_oracle: unit)
     (V : mpred.varspecs) (G : mpred.funspecs) (m: mem),
     (forall `{semax.VSTGS unit Σ}, semax_prog extspec prog initial_oracle V G) ->
     Genv.init_mem prog = Some m ->
     exists b, exists q, exists m',
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       semantics.initial_core  (Clight_core.cl_core_sem (Clight.globalenv prog))
           0 m q m' (Vptr b Ptrofs.zero) nil /\
       forall n,
        @dry_safeN _ _ _ unit (semax.genv_symb_injective)
          (Clight_core.cl_core_sem (Clight.globalenv prog)) extspec
           (Clight.genv_genv 
            (Clight.Build_genv (Genv.globalenv prog) (Ctypes.prog_comp_env prog)) )
             n tt q m'.
Proof.
intros.
destruct initial_oracle.
eapply NullExtension_whole_program_sequential_safety; eassumption.
Qed.

Print Assumptions VST_sound.
