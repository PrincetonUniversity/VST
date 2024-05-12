Require Import VST.sepcomp.semantics.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clight_lemmas.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.veric.Clight_evsem.
Require Import VST.veric.SeparationLogic.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.SeparationLogicSoundness.
Require Import iris_ora.logic.wsat.
Require Import iris_ora.logic.fancy_updates.
Require Import VST.sepcomp.extspec.

Import VericSound.
Import VericMinimumSeparationLogic.
Import VericMinimumSeparationLogic.CSHL_Def.
Import VericMinimumSeparationLogic.CSHL_Defs.
Import Clight.

Class VSTGpreS (Z : Type) Σ := {
  VSTGpreS_inv :: invGpreS Σ;
  VSTGpreS_heap :: gen_heapGpreS share address resource Σ;
  VSTGpreS_funspec :: inG Σ (gmap_view.gmap_viewR address (@funspecO' Σ));
  VSTGpreS_ext :: inG Σ (excl_authR (leibnizO Z))
}.

Definition VSTΣ Z : gFunctors :=
  #[invΣ; gen_heapΣ share address resource; GFunctor (gmap_view.gmap_viewRF address funspecOF');
    GFunctor (excl_authR (leibnizO Z)) ].
Global Instance subG_VSTGpreS {Z Σ} : subG (VSTΣ Z) Σ → VSTGpreS Z Σ.
Proof. solve_inG. Qed.

Lemma init_VST: forall Z `{!VSTGpreS Z Σ} (z : Z),
  ⊢ |==> ∀ _ : invGS_gen HasNoLc Σ, ∃ _ : gen_heapGS share address resource Σ, ∃ _ : funspecGS Σ, ∃ _ : externalGS Z Σ,
    let H : VSTGS Z Σ := Build_VSTGS _ _ (HeapGS _ _ _ _) _ in
    (state_interp Mem.empty z ∗ funspec_auth ∅ ∗ has_ext z) ∗ ghost_map.ghost_map_auth(H0 := gen_heapGpreS_meta) (gen_meta_name _) 1 ∅.
Proof.
  intros; iIntros.
  iMod gen_heap_init_names_empty as (??) "(? & ?)".
  iMod (own_alloc(A := gmap_view.gmap_viewR address (@funspecO' Σ)) (gmap_view.gmap_view_auth (DfracOwn 1) ∅)) as (γf) "?".
  { apply gmap_view.gmap_view_auth_valid. }
  iMod (ext_alloc z) as (?) "(? & ?)".
  iIntros "!>" (?); iExists (GenHeapGS _ _ _ _ γh γm), (FunspecG _ _ γf), _.
  rewrite /state_interp /mem_auth /funspec_auth /=; iFrame.
  iSplit; [|done]. iPureIntro. apply empty_coherent.
Qed.

Global Instance stepN_absorbing {PROP : bi} `{!BiFUpd PROP} n E1 E2 (P : PROP) `{!Absorbing P}: Absorbing (|={E1}[E2]▷=>^n P).
Proof.
  induction n; apply _.
Qed.

Lemma adequacy: forall `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} ge z q m n,
  state_interp m z ∗ jsafeN OK_spec ge ⊤ z q ⊢
  |={⊤}[∅]▷=>^n ⌜dry_safeN(genv_symb := genv_symb_injective) (cl_core_sem ge) OK_spec ge n z q m⌝.
Proof.
  intros.
  iIntros "(S & Hsafe)".
  iLöb as "IH" forall (m z q n).
  destruct n as [|n]; simpl.
  { iPureIntro. constructor. }
  rewrite [in (environments.Esnoc _ "Hsafe" _)]/jsafeN jsafe_unfold /jsafe_pre.
  iMod ("Hsafe" with "S") as "[Hsafe_halt | [Hsafe_core | Hsafe_ext]]".
  - iDestruct "Hsafe_halt" as %(ret & Hhalt & Hexit).
    iApply step_fupd_intro; first done; iApply step_fupdN_intro; first done.
    iPureIntro; eapply safeN_halted; eauto.
  - iDestruct "Hsafe_core" as ">(%c' & %m' & % & s_interp & ▷jsafe)".
    iApply fupd_mask_intro; first done.
    iIntros "Hclose !>"; iMod "Hclose" as "_".
    iSpecialize ("IH" with "[$] [$]").
    iModIntro; iApply (step_fupdN_mono with "IH").
    iPureIntro. eapply safeN_step; eauto.
  - iDestruct "Hsafe_ext" as (ef args w (at_external & Hpre)) "Hpost".
    iAssert (|={⊤}[∅]▷=>^(S n) ⌜(∀ (ret : option val) m' z' n',
      Val.has_type_list args (sig_args (ef_sig ef))
      → Builtins0.val_opt_has_rettype ret (sig_res (ef_sig ef))
        → n' ≤ n
            → ext_spec_post OK_spec ef w
                (genv_symb_injective ge) (sig_res (ef_sig ef)) ret z' m'
              → ∃ q',
                  (after_external (cl_core_sem ge) ret q m' = Some q'
                   ∧ dry_safeN(genv_symb := genv_symb_injective) (cl_core_sem ge) OK_spec ge n' z' q' m'))⌝) with "[-]" as "Hdry".
      2: { iApply (step_fupdN_mono with "Hdry"); iPureIntro; intros; eapply safeN_external; eauto. }
      iApply step_fupdN_mono; first by do 8 setoid_rewrite bi.pure_forall.
      repeat (setoid_rewrite step_fupdN_plain_forall; last done; [|apply _..]).
      iIntros (ret m' z' n' ????).
      iApply fupd_mask_intro; first done.
      iIntros "Hclose !>"; iMod "Hclose" as "_".
      iMod ("Hpost" with "[%] [%]") as (??) "(S & Hsafe)"; [done..|].
      iSpecialize ("IH" with "[$] [$]").
      iModIntro; iApply step_fupdN_le; [done..|].
      iApply (step_fupdN_mono with "IH"); eauto.
Qed.

Definition ext_spec_entails {M E Z} (es1 es2 : external_specification M E Z) :=
  (forall e x1 p tys args z m, ext_spec_pre es1 e x1 p tys args z m ->
     exists x2, ext_spec_pre es2 e x2 p tys args z m /\
       forall ty ret z' m', ext_spec_post es2 e x2 p ty ret z' m' ->
                            ext_spec_post es1 e x1 p ty ret z' m') /\
  (forall v z m, ext_spec_exit es1 v z m -> ext_spec_exit es2 v z m).

Lemma ext_spec_entails_refl : forall {M E Z} (es : external_specification M E Z), ext_spec_entails es es.
Proof.
  intros; split; eauto.
Qed.

Theorem ext_spec_entails_safe : forall {G C M Z} {genv_symb} Hcore es1 es2 ge n z c m
  (Hes : ext_spec_entails es1 es2),
  @step_lemmas.dry_safeN G C M Z genv_symb Hcore es1 ge n z c m -> @step_lemmas.dry_safeN G C M Z genv_symb Hcore es2 ge n z c m.
Proof.
  induction n as [n IHn] using lt_wf_ind; intros.
  inv H.
  - constructor.
  - eapply step_lemmas.safeN_step; eauto.
    eapply IHn; eauto.
  - destruct Hes as (Hes & ?).
    apply Hes in H1 as (x2 & ? & ?).
    eapply step_lemmas.safeN_external; eauto; intros.
    edestruct H2 as (c' & ? & ?); eauto.
    exists c'; split; auto.
    eapply IHn; eauto; [lia | by split].
  - destruct Hes.
    eapply step_lemmas.safeN_halted; eauto.
Qed.

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
