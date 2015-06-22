Require Import sepcomp.core_semantics.

Require Import veric.base.
Require Import veric.Clight_new.
Require Import veric.Clight_lemmas.
Require Import sepcomp.step_lemmas.
Require Import veric.SeparationLogic.
Require Import veric.juicy_extspec.
Require Import veric.juicy_mem.
Require veric.NullExtension.
Require Import veric.Clight_sim.
Require Import veric.SeparationLogicSoundness.
Require Import sepcomp.extspec.
Require Import msl.msl_standard.

Import SoundSeparationLogic.
Import CSL.

Definition dryspec : ext_spec unit :=
 Build_external_specification mem external_function unit
     (*ext_spec_type*)
     (fun ef => False)
     (*ext_spec_pre*)
     (fun ef Hef ge tys vl m z => False) 
     (*ext_spec_post*)
     (fun ef Hef ge ty vl m z => False)
     (*ext_spec_exit*)
     (fun rv m z => False).

 Lemma whole_program_sequential_safety:
   forall prog V G m,
     @semax_prog NullExtension.Espec prog V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q,
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       initial_core cl_core_sem
           (Build_genv (Genv.globalenv prog) (prog_comp_env prog))
 (Vptr b Int.zero) nil = Some q /\
       forall n, 
        @dry_safeN _ _ _ _ (@Genv.genv_symb _ _) (coresem_extract_cenv cl_core_sem (prog_comp_env prog)) dryspec (Build_genv (Genv.globalenv prog) (prog_comp_env prog)) n tt q m.
Proof.
 intros.
 destruct (@semax_prog_rule NullExtension.Espec tt _ _ _ _ H H0) as [b [q [? [? ?]]]].
 exists b, q.
 split3; auto.
 intro n.
 specialize (H3 n).
 destruct H3 as [jm [? [? ?]]].
 unfold semax.jsafeN in H5.
 subst m.
 clear - H4 H5.
 revert jm q H4 H5; induction n; simpl; intros. constructor.
 inv H5.
 destruct H0 as (?&?&?).
 econstructor.
 red. red. fold (globalenv prog). eassumption.
 apply IHn; auto. 
 change (level (m_phi jm)) with (level jm) in H4. 
   rewrite H4 in H2; inv H2; auto.
 exfalso; auto.
 eapply safeN_halted; eauto.
Qed.

Require Import juicy_safety.

Definition fun_id (ef: external_function) : option ident :=
  match ef with EF_external id sig => Some id | _ => None end.

Axiom module_sequential_safety : (*TODO*)
   forall (prog: program) (V: varspecs) (G: funspecs) ora m f f_id f_b f_body args,
     let ge := Genv.globalenv prog in
     let spec := add_funspecs NullExtension.Espec G in
     let tys := sig_args (ef_sig f) in
     let rty := sig_res (ef_sig f) in
     let sem := juicy_core_sem cl_core_sem in
     @semax_prog spec prog V G ->
     fun_id f = Some f_id ->
     Genv.find_symbol ge f_id = Some f_b -> 
     Genv.find_funct  ge (Vptr f_b Int.zero) = Some f_body -> 
     forall x : ext_spec_type (@OK_spec spec) f,
     ext_spec_pre (@OK_spec spec) f x (Genv.genv_symb ge) tys args ora m -> 
     exists q,
       initial_core sem (Build_genv ge (prog_comp_env prog))
              (Vptr f_b Int.zero) args = Some q /\
       forall n, safeN (@Genv.genv_symb _ _) (coresem_extract_cenv sem (prog_comp_env prog))
(upd_exit (@OK_spec spec) x (Genv.genv_symb ge)) ge n ora q m.
