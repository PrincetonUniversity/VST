Require Import sepcomp.semantics.

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
   forall {CS: compspecs} prog V G m,
     @semax_prog NullExtension.Espec CS prog V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q,
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       forall n,
       initial_core cl_core_sem 
           0 (*additional temporary argument - TODO (Santiago): FIXME*)
           (Build_genv (Genv.globalenv prog) (prog_comp_env prog))
           m (Vptr b Int.zero) nil = Some (q, None) /\
        @dry_safeN _ _ _ _ (@Genv.genv_symb _ _) (coresem_extract_cenv cl_core_sem (prog_comp_env prog)) dryspec (Build_genv (Genv.globalenv prog) (prog_comp_env prog)) n tt q m.
Proof.
 intros.
 destruct (@semax_prog_rule NullExtension.Espec CS _ _ _ _ 
     0 (*additional temporary argument - TODO (Santiago): FIXME*)
     H H0) as [b [q [H1 H3]]].
 exists b, q.
 split; auto.
 intro n.
 specialize (H3 n).
 destruct H3 as [jm [? [? [? [? _]]]]].
 simpl in H4; unfold j_initial_core in H4.
 destruct (initial_core cl_core_sem 0 (globalenv prog) (m_dry jm)
         (Vptr b Int.zero) nil) eqn:?; inversion H4; clear H4.
 destruct p. destruct o; inversion H7; clear H7; subst c.
 split. apply Heqo.
 specialize (H5 tt).
 unfold semax.jsafeN in H5.
 rename Heqo into H4.
 subst m.
 clear - H3 H5.
 revert jm q H3 H5; induction n; intros. constructor.
 inv H5.
 - destruct H0 as (?&?&?).
   econstructor.
   + red. red. fold (globalenv prog). eassumption.
   + apply IHn; auto. congruence.
 - exfalso; auto.
 - eapply safeN_halted; eauto.
Qed.

Require Import veric.juicy_safety.

Definition fun_id (ext_link: Strings.String.string -> ident) (ef: external_function) : option ident :=
  match ef with EF_external id sig => Some (ext_link id) | _ => None end.

Axiom module_sequential_safety : (*TODO*)
   forall {CS: compspecs} (prog: program) (V: varspecs) (G: funspecs) ora m f f_id f_b f_body args,
     let ge := Genv.globalenv prog in
     let ext_link := ext_link_prog prog in
     let spec := add_funspecs NullExtension.Espec ext_link G in
     let tys := sig_args (ef_sig f) in
     let rty := sig_res (ef_sig f) in
     let sem := juicy_core_sem cl_core_sem in
     @semax_prog spec CS prog V G ->
     fun_id ext_link f = Some f_id ->
     Genv.find_symbol ge f_id = Some f_b ->
     Genv.find_funct  ge (Vptr f_b Int.zero) = Some f_body ->
     forall x : ext_spec_type (@OK_spec spec) f,
     ext_spec_pre (@OK_spec spec) f x (Genv.genv_symb ge) tys args ora m ->
     exists q,
         initial_core sem 
         0 (*additional temporary argument - TODO (Santiago): FIXME*)
         (Build_genv ge (prog_comp_env prog)) m
              (Vptr f_b Int.zero) args = Some (q, None) /\
       forall n, 
          safeN (@Genv.genv_symb _ _) (coresem_extract_cenv sem (prog_comp_env prog))
(upd_exit (@OK_spec spec) x (Genv.genv_symb ge)) ge n ora q m.
