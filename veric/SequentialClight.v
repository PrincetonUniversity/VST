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

(*
Definition dryspec (oracle_ty: Type) : ext_spec oracle_ty :=
 Build_external_specification mem external_function oracle_ty
     (*ext_spec_type*)
     (fun ef => False)
     (*ext_spec_pre*)
     (fun ef Hef ge tys vl m z => False)
     (*ext_spec_post*)
     (fun ef Hef ge ty vl m z => False)
     (*ext_spec_exit*)
     (fun rv m z => False).
*)

Definition ignores_juice Z (J: external_specification juicy_mem external_function Z) : Prop :=
  (forall e t b tl vl x jm jm',
     m_dry jm = m_dry jm' ->
    ext_spec_pre J e t b tl vl x jm ->
    ext_spec_pre J e t b tl vl x jm') /\
 (forall ef t b ot v x jm jm',
     m_dry jm = m_dry jm' -> 
    ext_spec_post J ef t b ot v x jm ->
    ext_spec_post J ef t b ot v x jm') /\
 (forall v x jm jm',
     m_dry jm = m_dry jm' -> 
     ext_spec_exit J v x jm ->
     ext_spec_exit J v x jm').

Import VST.veric.compcert_rmaps.R.
Search (option permission -> option permission -> Prop).

Definition juicy_ext_spec_resource_decay (Z: Type) 
  (J: external_specification juicy_mem external_function Z) :=
 forall ef w b tl vl ot v z jm jm',
    ext_spec_pre J ef w b tl vl z jm ->
    ext_spec_post J ef w b ot v z jm' ->
    resource_decay (Mem.nextblock (m_dry jm)) (m_phi jm) (m_phi jm').

Definition juicy_dry_ext_spec (Z: Type)
   (J: external_specification juicy_mem external_function Z)
   (D: external_specification mem external_function Z) :=
   (ext_spec_type D = ext_spec_type J) /\
  (forall e t t' b tl vl x jm,
    JMeq.JMeq t t' ->
    (ext_spec_pre J e t b tl vl x jm <->
    ext_spec_pre D e t' b tl vl x (m_dry jm))) /\
 (forall ef t t' b ot v x jm,
    JMeq.JMeq t t' ->
    (ext_spec_post J ef t b ot v x jm <->
     ext_spec_post D ef t' b ot v x (m_dry jm))) /\
 (forall v x jm,
     ext_spec_exit J v x jm <->
     ext_spec_exit D v x (m_dry jm)).

Definition juicy_dry_ext_spec_make (Z: Type) 
   (J: external_specification juicy_mem external_function Z) :
   external_specification mem external_function Z.
destruct J.
apply Build_external_specification with ext_spec_type.
intros e t b tl vl x m.
apply (forall jm, m_dry jm = m -> (* external ghost matches x -> *) ext_spec_pre e t b tl vl x jm).
intros e t b ot v x m.
apply (forall jm, m_dry jm = m -> ext_spec_post e t b ot v x jm).
intros v x m.
apply (forall jm, m_dry jm = m -> ext_spec_exit v x jm).
Defined.

Lemma jdes_make_lemma:
  forall Z J, ignores_juice Z J ->
    juicy_dry_ext_spec Z J (juicy_dry_ext_spec_make Z J).
Proof.
intros.
destruct H as [? [? ?]], J; split; [ | split3]; simpl in *; intros; auto.
-
apply JMeq.JMeq_eq in H2. subst t'.
split; intros.
eapply H. symmetry; eassumption.  auto.
apply H2; auto.
-
apply JMeq.JMeq_eq in H2. subst t'.
split; intros.
eapply H0. symmetry; eassumption.  auto.
apply H2; auto.
-
split; intros.
eapply H1. symmetry; eassumption. auto.
apply H2; auto. 
Qed.

 Lemma whole_program_sequential_safety:
   forall {CS: compspecs} {Espec: OracleKind} (initial_oracle: OK_ty) 
     (dryspec: ext_spec OK_ty)
     (JDE: juicy_dry_ext_spec _ (@JE_spec OK_ty OK_spec) dryspec)
     (JRD: juicy_ext_spec_resource_decay _ (@JE_spec OK_ty OK_spec))
     prog V G m,
     @semax_prog Espec (*NullExtension.Espec*) CS prog V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q, exists m',
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       initial_core  (cl_core_sem (globalenv prog))
           0 m q m' (Vptr b Ptrofs.zero) nil /\
       forall n,
        @dry_safeN _ _ _ OK_ty (genv_symb_injective)
            (coresem_extract_cenv  (cl_core_sem (globalenv prog))
                (prog_comp_env prog)) 
            (*(dryspec  OK_ty)*) dryspec
            (Build_genv (Genv.globalenv prog) (prog_comp_env prog)) 
             n initial_oracle q m'.
Proof.
 intros.
 destruct (@semax_prog_rule' (*NullExtension.*)Espec CS _ _ _ _ 
     0 (*additional temporary argument - TODO (Santiago): FIXME*)
     H H0) as [b [q [[H1 H2] H3]]].
 destruct (H3 O initial_oracle) as [jmx [H4x [H5x [H6x [H7x _]]]]].
 destruct (H2 jmx H4x) as [jmx' [H8x H8y]].
 exists b, q, (m_dry jmx').
 split3; auto.
 rewrite H4x in H8y. auto.
 subst. simpl. clear H5x H6x H7x H8y.
 forget (m_dry jmx) as m. clear jmx.
 intro n.
 specialize (H3 n initial_oracle).
 destruct H3 as [jm [? [? [? [? _]]]]].
 unfold semax.jsafeN in H6.
 subst m.
 assert (joins (compcert_rmaps.RML.R.ghost_of (m_phi jm))
   (Some (ghost_PCM.ext_ref initial_oracle, compcert_rmaps.RML.R.NoneP) :: nil)) as J.
 { destruct (compcert_rmaps.RML.R.ghost_of (m_phi jm)); inv H5.
   eexists; constructor; constructor.
   instantiate (1 := (_, _)); constructor; simpl; constructor; auto.
   instantiate (1 := (Some _, _)); repeat constructor; simpl; auto. }
 clear - JDE JRD H4 J H6.
  rewrite <- H4 in H6|-*.
 assert (level jm <= n)%nat by omega.
 clear H4; rename H into H4.
 forget initial_oracle as ora.
 revert ora jm q H4 J H6; induction n; simpl; intros.
 assert (level (m_phi jm) = 0%nat) by omega. rewrite H; constructor.
 inv H6.
 - constructor.
 -
   rewrite <- level_juice_level_phi in H4.
   destruct H0 as (?&?&?&Hg).
   eapply safeN_step.
   + red. red. fold (globalenv prog). eassumption.
   + destruct (H1 (Some (ghost_PCM.ext_ref ora, compcert_rmaps.RML.R.NoneP) :: nil)) as (m'' & J'' & (? & ? & ?) & ?); auto.
     { eexists; apply join_comm, core_unit. }
     { rewrite Hg.
       destruct J; eexists; apply compcert_rmaps.RML.ghost_fmap_join; eauto. }
     replace (m_dry m') with (m_dry m'') by auto.
     change (level (m_phi jm)) with (level jm) in *.
     replace n0 with (level m'') by omega.
     apply IHn; auto. omega.
     replace (level m'') with n0 by omega. auto.
 -
   assert (JDE1': ext_spec_type dryspec = ext_spec_type OK_spec) by apply JDE.
(*   destruct JDE as [JDE1 [JDE2 [JDE3 JDE4]]]. *)
   destruct dryspec as [ty pre post exit]. simpl in *. subst ty.
   destruct JE_spec as [ty' pre' post' exit']. simpl in *.
   change (level (m_phi jm)) with (level jm) in *.
   apply safeN_external with (e0:=e)(args0:=args)(x0:=x).
   assumption.
   simpl. eapply JDE; try apply JMeq.JMeq_refl; eassumption.
   simpl. intros.
   assert (H20: exists jm', m_dry jm' = m' 
                      /\ (level jm' = n')%nat
                      /\ juicy_safety.pures_eq (m_phi jm) (m_phi jm')
                      /\ exists g', compcert_rmaps.RML.R.ghost_of (m_phi jm') = Some (ghost_PCM.ext_ghost z', compcert_rmaps.RML.R.NoneP) :: g'). {
     destruct (juicy_mem_lemmas.rebuild_juicy_mem_rmap jm m') 
            as [phi [? [? ?]]].
     pose (phi' := age_to.age_to n' phi).
     assert (contents_cohere m' phi') by admit.
     assert (access_cohere m' phi') by admit.
     assert (max_access_cohere m' phi') by admit.
     assert (alloc_cohere m' phi') by admit.
     pose (jm' := mkJuicyMem _ _ H10 H11 H12 H13).
     exists jm'.  (* NOT QUITE RIGHT: it should be jm' with the ghost updated *)
     split; [ | split3].
     subst jm'; simpl; auto.
     subst jm' phi'; simpl. apply age_to.level_age_to. omega.
     hnf. split. intro loc. subst jm' phi'. simpl.
     rewrite age_to_resource_at.age_to_resource_at.
     rewrite H8. unfold juicy_mem_lemmas.rebuild_juicy_mem_fmap.
     destruct (m_phi jm @ loc); auto. rewrite age_to.level_age_to by omega.
      reflexivity.
     intro loc. subst jm' phi'. simpl.
     rewrite age_to_resource_at.age_to_resource_at.
     rewrite H8. unfold juicy_mem_lemmas.rebuild_juicy_mem_fmap; simpl.
     destruct (m_phi jm @ loc); auto.
     if_tac; simpl; auto. destruct k; simpl; auto. simpl. eauto.
     subst jm' phi'. simpl m_phi.
     rewrite age_to_resource_at.age_to_ghost_of.
     rewrite H9.
     admit. (* William?  *)
   }
   destruct H20 as [jm'  [H26 [H27 [H28 [g' Hg']]]]].
   specialize (H2 ret jm' z' n' Hargsty Hretty).
   spec H2. omega.
    spec H2. hnf; split3; auto. omega.
  spec H2.
  apply <- (proj1 (proj2 (proj2 JDE))); try apply JMeq.JMeq_refl. subst m'. apply H6.
  destruct H2 as [c' [H2a H2b]]; exists c'; split; auto.
  hnf in H2b.
  specialize (H2b (Some (ghost_PCM.ext_ref z', compcert_rmaps.RML.R.NoneP) :: nil)).
  spec H2b. apply join_sub_refl.
  spec H2b.
  { rewrite Hg'.
    exists (Some (ghost_PCM.ext_both z', compcert_rmaps.RML.R.NoneP) :: g');
      repeat constructor.  }
  destruct H2b as [jm'' [? [? ?]]].
  destruct H7 as [? [? ?]].
  subst m'. rewrite <- H7.
  specialize (IHn  z' jm'' c').
  subst n'. rewrite <- H9.
  change (level (m_phi jm'')) with (level  jm'') in IHn.
  apply IHn. omega.
  auto.
  rewrite H9; auto.
 - eapply safeN_halted; eauto.
    apply JDE. auto.
 Unshelve. simpl. split; [apply Share.nontrivial | hnf]. exists None; constructor.
all: fail.
Admitted.

Require Import VST.veric.juicy_safety.

Definition fun_id (ext_link: Strings.String.string -> ident) (ef: external_function) : option ident :=
  match ef with EF_external id sig => Some (ext_link id) | _ => None end.

Print genv.

Lemma module_sequential_safety : (*TODO*)
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
Abort.