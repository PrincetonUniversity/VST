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
  VSTGpreS_inv :> invGpreS Σ;
  VSTGpreS_heap :> gen_heapGpreS address resource Σ;
  VSTGpreS_funspec :> inG Σ (gmap_view.gmap_viewR address (@funspecO' Σ));
  VSTGpreS_ext :> inG Σ (excl_authR (leibnizO Z))
}.

Definition VSTΣ Z : gFunctors :=
  #[invΣ; gen_heapΣ address resource; GFunctor (gmap_view.gmap_viewRF address funspecOF');
    GFunctor (excl_authR (leibnizO Z)) ].
Global Instance subG_VSTGpreS {Z Σ} : subG (VSTΣ Z) Σ → VSTGpreS Z Σ.
Proof. solve_inG. Qed.

Lemma init_VST: forall Z `{!VSTGpreS Z Σ} (z : Z),
  ⊢ |==> ∀ _ : invGS_gen HasNoLc Σ, ∃ _ : gen_heapGS address resource Σ, ∃ _ : funspecGS Σ, ∃ _ : externalGS Z Σ,
    let H : heapGS Σ := HeapGS _ _ _ _ in
    (state_interp Mem.empty z ∗ funspec_auth ∅ ∗ has_ext z) ∗ ghost_map.ghost_map_auth(H0 := gen_heapGpreS_meta) (gen_meta_name _) 1 ∅.
Proof.
  intros; iIntros.
  iMod gen_heap_init_names_empty as (??) "(? & ?)".
  iMod (own_alloc(A := gmap_view.gmap_viewR address (@funspecO' Σ)) (gmap_view.gmap_view_auth (DfracOwn 1) ∅)) as (γf) "?".
  { apply gmap_view.gmap_view_auth_valid. }
  iMod (ext_alloc z) as (?) "(? & ?)".
  iIntros "!>" (?); iExists (GenHeapGS _ _ _ γh γm), (FunspecG _ _ γf), _.
  rewrite /state_interp /mem_auth /funspec_auth /=; iFrame.
  iExists ∅; iFrame. iSplit; [|done]. iPureIntro. apply empty_coherent.
Qed.

Global Instance stepN_absorbing {PROP : bi} `{!BiFUpd PROP} n E1 E2 (P : PROP) `{!Absorbing P}: Absorbing (|={E1}[E2]▷=>^n P).
Proof.
  induction n; apply _.
Qed.

Lemma whole_program_sequential_safety_ext:
   forall Σ {CS: compspecs} {Espec: OracleKind} `{!VSTGpreS OK_ty Σ} (initial_oracle: OK_ty)
     (EXIT: semax_prog.postcondition_allows_exit tint)
     prog V G m,
     (forall {HH : heapGS Σ} {HE : externalGS OK_ty Σ}, @semax_prog _ HH Espec HE CS prog initial_oracle V G) ->
     Genv.init_mem prog = Some m ->
     exists b, exists q,
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       semantics.initial_core (cl_core_sem (globalenv prog))
           0 m q m (Vptr b Ptrofs.zero) nil /\
       forall n,
        @dry_safeN _ _ _ OK_ty (genv_symb_injective)
            (cl_core_sem (globalenv prog))
            OK_spec
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
            OK_spec
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
  specialize (H (HeapGS _ _ _ _) HE).
  eapply (semax_prog_rule _ _ _ _ n) in H as (b & q & (? & ? & Hinit & ->) & Hsafe); [| done..].
  iMod (Hsafe with "H") as "Hsafe".
  iAssert (|={⊤}[∅]▷=>^n ⌜@dry_safeN _ _ _ OK_ty (genv_symb_injective) (cl_core_sem (globalenv prog))
            OK_spec (Build_genv (Genv.globalenv prog) (prog_comp_env prog)) n initial_oracle q m⌝) with "[Hsafe]" as "Hdry".
  { clear H0 Hinit Hsafe.
    rewrite bi.and_elim_l.
    iLöb as "IH" forall (m initial_oracle q n).
    destruct n as [|n]; simpl.
    { iPureIntro. constructor. }
    rewrite [in (environments.Esnoc _ "Hsafe" _)]/jsafeN jsafe_unfold /jsafe_pre.
    iDestruct "Hsafe" as "(s_interp & >Hsafe)".
    iDestruct ("Hsafe" with "s_interp") as "[Hsafe_halt | [Hsafe_core | Hsafe_ext]]".
    - iDestruct "Hsafe_halt" as %(ret & Hhalt & Hexit).
      iApply step_fupd_intro; first done; iApply step_fupdN_intro; first done.
      iPureIntro; eapply safeN_halted; eauto.
    - iDestruct "Hsafe_core" as ">(%c' & %m' & %H & s_interp & ▷jsafe)".
      iApply fupd_mask_intro; first done.
      iIntros "Hclose !>"; iMod "Hclose" as "_".
      iSpecialize ("IH" with "[$]").
      iModIntro; iApply (step_fupdN_mono with "IH").
      iPureIntro. eapply safeN_step; eauto.
    - iDestruct "Hsafe_ext" as (ef args w (at_external & Hpre)) "Hpost".
      iAssert (|={⊤}[∅]▷=>^(S n) ⌜(∀ (ret : option val) m' z' n',
      Val.has_type_list args (sig_args (ef_sig ef))
      → Builtins0.val_opt_has_rettype ret (sig_res (ef_sig ef))
        → n' ≤ n
            → ext_spec_post OK_spec ef w
                (genv_symb_injective (globalenv prog)) (sig_res (ef_sig ef)) ret z' m'
              → ∃ q',
                  (after_external (cl_core_sem (globalenv prog)) ret q m' = Some q'
                   ∧ safeN_ (cl_core_sem (globalenv prog)) OK_spec (Genv.globalenv prog) n' z' q' m'))⌝) with "[-]" as "Hdry".
      2: { iApply (step_fupdN_mono with "Hdry"); iPureIntro; intros; eapply safeN_external; eauto. }
      iApply step_fupdN_mono; first by do 8 setoid_rewrite bi.pure_forall.
      repeat (setoid_rewrite step_fupdN_plain_forall; last done; [|apply _..]).
      iIntros (ret m' z' n' ????).
      simpl; iApply fupd_mask_intro; first done.
      iIntros "Hclose !>"; iMod "Hclose" as "_".
      iMod ("Hpost" with "[%] [%]") as (??) "H"; [done..|].
      iSpecialize ("IH" with "[$]").
      iModIntro; iApply step_fupdN_le; first done.
      iApply (step_fupdN_mono with "IH"); eauto. }
  iApply step_fupd_intro; first done.
  iNext; iApply (step_fupdN_mono with "Hdry").
  iPureIntro. intros.
  eexists. eexists. split3; eauto.
Qed.

Definition fun_id (ext_link: Strings.String.string -> ident) (ef: external_function) : option ident :=
  match ef with EF_external id sig => Some (ext_link id) | _ => None end.
