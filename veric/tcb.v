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

(* If an inline external call can run on a memory m, then it should produce the same return value
   and perform the same memory operations when run on a memory m1 that has more permissions than m
   but is otherwise identical. c.f. Events.ec_mem_extends *)
Definition ec_mem_sub := forall ef se lv m t v m' (EFI : ef_inline ef = true) m1
  (EFC : Events.external_call ef se lv m t v m'), mem_sub m m1 ->
  exists m1' (EFC1 : Events.external_call ef se lv m1 t v m1'),
    mem_sub m' m1' /\ proj1_sig (Clight_core.inline_external_call_mem_events _ _ _ _ _ _ _ EFI EFC1) =
    proj1_sig (Clight_core.inline_external_call_mem_events _ _ _ _ _ _ _ EFI EFC).

Theorem VST_sound: 
  {Espec : OracleKind 
  | JMeq.JMeq (JE_spec _ (@OK_spec Espec)) null_extension_juicyspec /\
  let dryspec :=  juicy_dry_ext_spec_make _ null_extension_juicyspec in 
  forall (CS: compspecs)
     (Jsub: ec_mem_sub)
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
