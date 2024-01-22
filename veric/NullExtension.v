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

#[export] Instance extspec : external_specification mem external_function unit
  := Build_external_specification mem external_function unit
     (*ext_spec_type*)
     (fun ef => False)
     (*ext_spec_pre*)
     (fun ef Hef ge tys vl m z => False)
     (*ext_spec_post*)
     (fun ef Hef ge ty vl m z => False)
     (*ext_spec_exit*)
     (fun rv m z => True).

Lemma NullExtension_whole_program_sequential_safety:
   forall {CS: compspecs} `{!VSTGpreS unit Σ}
     (prog: Clight.program) V G m,
     (forall {HH : semax.VSTGS unit Σ}, semax_prog extspec prog tt V G) ->
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
eapply whole_program_sequential_safety_ext in H as (? & ? & ?); eauto.
- intros ?????; apply I.
- intros; apply ext_spec_entails_refl.
Qed.

(*Lemma module_sequential_safety : (*TODO*)
   forall {CS: compspecs} `{!VSTGpreS unit Σ} (prog: Clight.program) (V: varspecs) 
      (G: funspecs) ora m f f_id f_b f_body args,
     let ge := Genv.globalenv prog in
     let ext_link := SeparationLogic.ext_link_prog prog in
     (* this requires the heapGS and externalGS to be set up already -- would we want to fix
        the same one for each module? *)
     let spec := semax_ext.add_funspecs_rec _ ext_link (@OK_spec Espec) G in
     let tys := sig_args (ef_sig f) in
     let rty := sig_res (ef_sig f) in
     let sem := Clight_core.cl_core_sem (Clight.globalenv prog) in
     (forall {HH : heapGS Σ} {HE : externalGS OK_ty Σ}, @semax_prog _ HH Espec HE CS prog tt V G) ->
     fun_id ext_link f = Some f_id ->
     Genv.find_symbol ge f_id = Some f_b ->
     Genv.find_funct  ge (Vptr f_b Ptrofs.zero) = Some f_body ->
     forall x : ext_spec_type spec f,
     ext_spec_pre spec f x (genv_symb_injective ge) tys args ora m ->
     exists q,
       semantics.initial_core sem 
         0 (*additional temporary argument - TODO (Santiago): FIXME*)
             m q m
              (Vptr f_b Ptrofs.zero) args /\
       forall n, safeN_(genv_symb := @genv_symb_injective _ _)(Hrel := fun _ _ _ => True)
            sem  (upd_exit spec _ x (genv_symb_injective ge)) 
           ge n ora q m.
Abort.*)
