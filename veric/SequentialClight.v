Require Import VST.sepcomp.semantics.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clight_lemmas.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Set Warnings "-hiding-delimiting-key,-custom-entry-overridden,-notation-overridden".
Require Import VST.veric.Clight_evsem.
Require Import VST.veric.SeparationLogic.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.SeparationLogicSoundness.
Require Import iris_ora.logic.wsat.
Require Import iris_ora.logic.fancy_updates.
Set Warnings "hiding-delimiting-key,custom-entry-overridden,notation-overridden".
Require Import VST.sepcomp.extspec.

Import VericSound.
Import VericMinimumSeparationLogic.
Import VericMinimumSeparationLogic.CSHL_Def.
Import VericMinimumSeparationLogic.CSHL_Defs.
Import Clight.

Definition sig_of_funspec `{!heapGS Σ} (f : funspec) := typesig2signature (typesig_of_funspec f) (callingconvention_of_funspec f).

Lemma juicy_dry_spec : forall `{!VSTGS OK_ty Σ} ext_link fs es
  (Hspecs : forall s f, In (ext_link s, f) fs -> match f with mk_funspec ts cc E A P Q =>
     let e := EF_external s (typesig2signature ts cc) in
     forall w p tys args m z, exists x,
       state_interp m z ∗ P w (filter_genv (symb2genv p), args) ⊢ ⌜ext_spec_pre es e x p tys args z m⌝ ∧
         ∀ ty ret z' m', ⌜ext_spec_post es e x p ty ret z' m'⌝ → |==>
           state_interp m' z' ∗ Q w (make_ext_rval (filter_genv (symb2genv p)) ty ret)
   end)
  (Hexit : forall v z m, ext_spec_exit es v z m),
  ext_spec_entails (add_funspecs_rec OK_ty ext_link (void_spec OK_ty) fs) es.
Proof.
  intros; constructor; last done; clear Hexit.
  intros *; intros Hpre; induction fs; simpl; first done.
  destruct a as (i, [[]]); simpl in *.
  rewrite /funspec2pre in Hpre; rewrite /funspec2post; if_tac.
  - clear IHfs.
    destruct e; inv H.
    specialize (Hspecs _ _ ltac:(eauto)).
    destruct x1 as ((n, phi), w).
    specialize (Hspecs w); edestruct Hspecs as (x & Hspec).
    exists x.
    destruct Hpre as (Hvalid & Hty & HP).
    eapply Hspec in HP; last done.
    revert HP; ouPred.unseal; intros (Hpre & Hpost).
    split; first apply Hpre.
    intros ???? Hpost'; eapply Hpost; auto.
  - apply IHfs; auto.
    intros; apply Hspecs; auto.
Qed.

Lemma whole_program_sequential_safety_ext:
   forall Σ `{!VSTGpreS OK_ty Σ} {Espec : forall `{VSTGS OK_ty Σ}, ext_spec OK_ty} {dryspec : ext_spec OK_ty} (initial_oracle: OK_ty)
     (EXIT: forall `{!VSTGS OK_ty Σ}, semax_prog.postcondition_allows_exit Espec tint)
     (Hdry : forall `{!VSTGS OK_ty Σ}, ext_spec_entails Espec dryspec)
     prog V (G : forall `{VSTGS OK_ty Σ}, funspecs) m,
     (forall {HH : VSTGS OK_ty Σ}, exists CS: compspecs, semax_prog(OK_spec := Espec) prog initial_oracle V G) ->
     Genv.init_mem prog = Some m ->
     exists b, exists q,
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       semantics.initial_core (cl_core_sem (globalenv prog))
           0 m q m (Vptr b Ptrofs.zero) nil /\
       forall n,
        @dry_safeN _ _ _ OK_ty (genv_symb_injective)
            (cl_core_sem (globalenv prog))
            dryspec
            (Build_genv (Genv.globalenv prog) (prog_comp_env prog))
             n initial_oracle q m.
Proof.
  intros.
  assert (forall n, exists b, exists q,
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       semantics.initial_core (cl_core_sem (globalenv prog))
           0 m q m (Vptr b Ptrofs.zero) nil /\
        @dry_safeN _ _ _ OK_ty (genv_symb_injective)
            (cl_core_sem (globalenv prog))
            dryspec
            (Build_genv (Genv.globalenv prog) (prog_comp_env prog))
             n initial_oracle q m).
  2: { destruct (H1 O) as (b0 & q0 & ? & (? & _) & _); eexists _, _; split; first done; split; first done.
       intros n; destruct (H1 n) as (b & q & ? & (? & _) & Hsafe).
       assert (b0 = b) as -> by congruence.
       assert (q0 = q) as -> by congruence.
       done. }
  intros n; eapply ouPred.pure_soundness, (step_fupdN_soundness_no_lc' _ (S n) O); [apply _..|].
  simpl; intros; iIntros "_".
  iMod (@init_VST _ _ VSTGpreS0) as "H".
  iDestruct ("H" $! Hinv) as (?? HE) "(H & ?)".
  set (HH := Build_VSTGS _ _ (HeapGS _ _ _ _) HE).
  specialize (H HH); specialize (EXIT HH); destruct H.
  eapply (semax_prog_rule _ _ _ _ n) in H as (b & q & (? & ? & Hinit & ->) & Hsafe); [|done..].
  iMod (Hsafe with "H") as "Hsafe".
  rewrite bi.and_elim_l.
  iPoseProof (adequacy with "Hsafe") as "Hsafe".
  iApply step_fupd_intro; first done; iNext.
  iApply (step_fupdN_mono with "Hsafe"); apply bi.pure_mono; intros.
  eapply ext_spec_entails_safe in H; eauto 6.
Qed.

Definition fun_id (ext_link: Strings.String.string -> ident) (ef: external_function) : option ident :=
  match ef with EF_external id sig => Some (ext_link id) | _ => None end.
