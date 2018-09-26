Require Import VST.sepcomp.semantics.

Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clight_lemmas.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.SeparationLogic.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_mem.
Require VST.veric.NullExtension.
Require Import VST.veric.Clight_sim.
Require Import VST.veric.SeparationLogicSoundness.
Require Import VST.sepcomp.extspec.
Require Import VST.msl.msl_standard.

Import VericSound.
Import VericMinimumSeparationLogic.
Import VericMinimumSeparationLogic.CSHL_Def.
Import VericMinimumSeparationLogic.CSHL_Defs.

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
     exists b, exists q, exists m',
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       initial_core  (cl_core_sem (globalenv prog))
           0 m q m' (Vptr b Ptrofs.zero) nil /\
       forall n,
        @dry_safeN _ _ _ _ (genv_symb_injective) (coresem_extract_cenv  (cl_core_sem (globalenv prog)) (prog_comp_env prog)) dryspec (Build_genv (Genv.globalenv prog) (prog_comp_env prog)) n tt q m'.
Proof.
 intros.
 destruct (@semax_prog_rule' NullExtension.Espec CS _ _ _ _ 
     0 (*additional temporary argument - TODO (Santiago): FIXME*)
     H H0) as [b [q [[H1 H2] H3]]].
 destruct (H3 O tt) as [jmx [H4x [H5x [H6x [H7x _]]]]].
 destruct (H2 jmx H4x) as [jmx' [H8x H8y]].
 exists b, q, (m_dry jmx').
 split3; auto.
 rewrite H4x in H8y. auto.
 subst. simpl. clear H5x H6x H7x H8y.
 forget (m_dry jmx) as m. clear jmx.
 intro n.
 specialize (H3 n tt).
 destruct H3 as [jm [? [? [? [? _]]]]].
 unfold semax.jsafeN in H6.
 subst m.
 assert (joins (compcert_rmaps.RML.R.ghost_of (m_phi jm))
   (Some (ghost_PCM.ext_ref tt, compcert_rmaps.RML.R.NoneP) :: nil)) as J.
 { destruct (compcert_rmaps.RML.R.ghost_of (m_phi jm)); inv H5.
   eexists; constructor; constructor.
   instantiate (1 := (_, _)); constructor; simpl; constructor; auto.
   instantiate (1 := (Some _, _)); repeat constructor; simpl; auto. }
 clear - H4 J H6.
 revert jm q H4 J H6; induction n; simpl; intros. constructor.
 inv H6.
 - destruct H0 as (?&?&?&Hg).
   econstructor.
   + red. red. fold (globalenv prog). eassumption.
   + destruct (H1 (Some (ghost_PCM.ext_ref tt, compcert_rmaps.RML.R.NoneP) :: nil)) as (m'' & J'' & (? & ? & ?) & ?); auto.
     { eexists; apply join_comm, core_unit. }
     { rewrite Hg.
       destruct J; eexists; apply compcert_rmaps.RML.ghost_fmap_join; eauto. }
     replace (m_dry m') with (m_dry m'') by auto.
     apply IHn; auto.
     change (level (m_phi jm)) with (level jm) in H4.
     rewrite H4 in H2; inv H2; auto.
 - exfalso; auto.
 - eapply safeN_halted; eauto.
 Unshelve. simpl. split; [apply Share.nontrivial | hnf]. exists None; constructor.
  apply Int.zero.
Qed.

Require Import VST.veric.juicy_safety.

Definition fun_id (ext_link: Strings.String.string -> ident) (ef: external_function) : option ident :=
  match ef with EF_external id sig => Some (ext_link id) | _ => None end.

Print genv.

Axiom module_sequential_safety : (*TODO*)
   forall {CS: compspecs} (prog: program) (V: varspecs) (G: funspecs) ora m f f_id f_b f_body args,
     let ge := Genv.globalenv prog in
     let ext_link := ext_link_prog prog in
     let spec := add_funspecs NullExtension.Espec ext_link G in
     let tys := sig_args (ef_sig f) in
     let rty := sig_res (ef_sig f) in
     let sem := juicy_core_sem (cl_core_sem (Build_genv ge (prog_comp_env prog))) in
     @semax_prog spec CS prog V G ->
     fun_id ext_link f = Some f_id ->
     Genv.find_symbol ge f_id = Some f_b ->
     Genv.find_funct  ge (Vptr f_b Ptrofs.zero) = Some f_body ->
     forall x : ext_spec_type (@OK_spec spec) f,
     ext_spec_pre (@OK_spec spec) f x (genv_symb_injective ge) tys args ora m ->
     exists q,
       initial_core sem 
         0 (*additional temporary argument - TODO (Santiago): FIXME*)
             m q m
              (Vptr f_b Ptrofs.zero) args /\
       forall n, safeN_(genv_symb := @genv_symb_injective _ _)(Hrel := juicy_extspec.Hrel) (coresem_extract_cenv sem (prog_comp_env prog))
(upd_exit (@OK_spec spec) x (genv_symb_injective ge)) ge n ora q m.
