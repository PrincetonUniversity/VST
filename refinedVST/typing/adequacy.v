From iris.algebra Require Import csum excl auth cmra_big_op gmap.
(*From iris.base_logic.lib Require Import ghost_map.*)
From VST.sepcomp Require Import step_lemmas.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.veric Require Import Clight_core env external_state juicy_extspec.
From VST.typing Require Export type.
From VST.typing Require Import programs function bytes globals int fixpoint.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Set Default Proof Using "Type".

Definition main_type `{!typeG OK_ty Σ} {cs : compspecs} (P : iProp Σ) : unit → function.fn_params :=
  fn(∀ () : (); P) → ∃ () : (), int.int tint; True.

Global Instance VST_typeG `{!VSTGS OK_ty Σ} : typeG OK_ty Σ := TypeG _ _ _.

(*(* up *)
Lemma var_sizes_ok_sub : forall c1 c2 vars (Hsub : expr.cenv_sub c1 c2)
  (Hcomplete : Forall (fun it : ident * Ctypes.type => complete_type c1 (snd it) = true) vars),
  @var_sizes_ok c1 vars -> @var_sizes_ok c2 vars.
Proof.
  intros.
  pose proof (List.Forall_and Hcomplete H) as H1.
  eapply Forall_impl; first apply H1.
  simpl; intros ? (? & ?).
  rewrite (expr.cenv_sub_sizeof Hsub) //.
Qed.*)

(* wrapper around veric/lifting's adequacy theorem *)

Lemma refinedc_adequacy: forall `{!VSTGpreS OK_ty Σ} {Espec : forall `{VSTGS OK_ty Σ}, ext_spec OK_ty} {dryspec : ext_spec OK_ty}
  (Hdry : forall `{!VSTGS OK_ty Σ}, ext_spec_entails Espec dryspec) {CS: compspecs}
  (ge : Genv.t Clight.fundef Ctypes.type) m z s f (T : forall `{!typeG OK_ty Σ}, type_ret_assert) ve te (Hf : f.(fn_vars) = [])
  (EXIT: forall `{!VSTGS OK_ty Σ}, ⊢ exit_ret_assert Espec (typed_stmt_post_cond (fn_return f) T)),
  (∀ `{HH : invGS_gen HasNoLc Σ}, ⊢ |={⊤}=> ∃ _ : gen_heapGS share Address.address resource Σ, ∃ _ : funspecGS Σ, ∃ _ : envGS Σ, ∃ _ : externalGS OK_ty Σ,
    let H : VSTGS OK_ty Σ := Build_VSTGS _ _ (HeapGS _ _ _ _) _ _ in
    stack_level 0 ∗ ⎡state_interp m z⎤ ∗ ⌜typecheck_var_environ (make_env ve) (make_tycontext_v (fn_vars f))⌝ ∧ ⎡env_auth (init_stack (Build_genv ge cenv_cs) ve te)⎤ ∗
    typed_stmt Espec ge s f T) →
       (forall n,
        @dry_safeN _ _ _ OK_ty (genv_symb_injective) (cl_core_sem (Build_genv ge cenv_cs)) dryspec
            (Build_genv ge cenv_cs) n z (Clight_core.State f s Kstop ve te) m).
Proof.
  intros; apply wp_adequacy with (R := λ (H : VSTGS OK_ty Σ), typed_stmt_post_cond (fn_return f) (T _)); [try done..|].
  iIntros; iMod H as (????) "($ & $ & $ & $ & H)".
  iModIntro; eauto.
Qed.

(** * Tactics for solving conditions in an adequacy proof *)

Ltac adequacy_intro_parameter :=
  repeat lazymatch goal with
         | |- ∀ _ : (), _ => case
         | |- ∀ _ : (_ * _), _ => case
         | |- ∀ _ : _, _ => move => ?
         end.

Ltac adequacy_unfold_equiv :=
  lazymatch goal with
  | |- type_fixpoint _ _ ≡ type_fixpoint _ _ => apply: type_fixpoint_proper; [|move => ??]
  | |- ty_own_val _ _ ≡ ty_own_val _ _ => unfold ty_own_val => /=
(*   | |-  _ =@{struct_layout} _ => apply: struct_layout_eq *)
  end.

Ltac adequacy_solve_equiv unfold_tac :=
  first [ eassumption | fast_reflexivity | unfold_type_equiv | adequacy_unfold_equiv | f_contractive | f_equiv' | reflexivity | progress unfold_tac ].

Ltac adequacy_solve_typed_function lemma unfold_tac :=
  iApply typed_function_equiv; [
    done |
    adequacy_intro_parameter => /=; repeat (constructor; [done|]); by constructor |
    | iApply lemma => //; iExists _; repeat iSplit => //];
    adequacy_intro_parameter => /=; eexists eq_refl => /=; split_and!; [..|adequacy_intro_parameter => /=; split_and!];  repeat adequacy_solve_equiv unfold_tac.

(* export to base triples *)
Definition fn_params_pre `{!VSTGS OK_ty Σ} {cs : compspecs} {A} fn fp (x : @dtfr Σ A) lsa : assert :=
  ⎡([∗ list] v;'(cty, t) ∈ lsa;zip (map snd (fn_params fn)) (fp_atys (fp x)), v ◁ᵥₐₗ| cty | t) ∗ fp_Pa (fp x)⎤.

Definition fn_params_post `{!VSTGS OK_ty Σ} {cs : compspecs} {A} fn fp (x : @dtfr Σ A) v : assert :=
  ∃ y, ⎡opt_ty_own_val (fn_return fn) ((fp x).(fp_fr) y).(fr_rty) v⎤ ∗ ⎡((fp x).(fp_fr) y).(fr_R)⎤.

Lemma typed_function_triple : forall `{!VSTGS OK_ty Σ} {cs : compspecs} {A} Espec ge f fp
    (Hcomplete : Forall (λ it, composite_compute.complete_legal_cosu_type it.2 = true) (fn_vars f))
    (Halign : Forall (λ it, align_mem.LegalAlignasFacts.LegalAlignasDefs.is_aligned cenv_cs ha_env_cs la_env_cs it.2 0 = true) (fn_vars f))
    (Hvolatile : Forall (λ it, type_is_volatile it.2 = false) (fn_vars f)),
  ⎡typed_function Espec ge f fp⎤ ⊢ ∀ x : dtfr A, fun_triple Espec (Build_genv ge cenv_cs) (fn_params_pre f fp x) f (fn_params_post f fp x).
Proof.
  rewrite /fun_triple /fn_params_pre /=; intros.
  iIntros "#?" (?) "!> %% ? H0 ?"; rewrite (stackframe_of_typed(typeG0 := VST_typeG)) //.
  iApply wp_strong_mono.
  iSplitL "H0". 2: {
    iStopProof; split => n; monPred.unseal; rewrite monPred_at_intuitionistically.
    iIntros "(H & (Hargs & ?) & Hstack)".
    iDestruct ("H" $! x) as "(%Htys & #H)".
    pose proof (tc_vals_length _ _ H) as Hlen; rewrite map_length in Hlen.
    apply Forall2_length in Htys as ->; rewrite Hlen.
    iApply ("H" $! _ (Vector.of_list args)).
    rewrite vec_to_list_to_vec; iFrame. }
  rewrite /= /Clight_seplog.bind_ret; iSplit.
  - rewrite /fn_params_post /=.
    iIntros "($ & H) !>"; iFrame.
    iDestruct ("H" with "[//]") as "(% & $ & $ & $)".
  - do 2 (iSplit; first by iIntros "[]").
    rewrite /fn_params_post /=.
    iIntros (?) "(% & Hret & %Htc & H)".
    iDestruct ("H" with "Hret") as "(% & ? & ? & $)"; by iFrame.
Qed.

Lemma typed_fptr_triple : forall `{!VSTGS OK_ty Σ} {cs : compspecs} {A} Espec ge fp l cty,
  ⎡l ◁ᵥₐₗ|cty| function_ptr Espec ge fp⎤ ⊢ ∃ f, ⌜Genv.find_funct ge l = Some (Internal f)⌝ ∧ ∀ x : dtfr A, ▷ fun_triple Espec (Build_genv ge cenv_cs) (fn_params_pre f fp x) f (fn_params_post f fp x).
Proof.
  rewrite /ty_own_val_at /ty_own_val /= /ty_own_val /=.
  intros.
  iIntros "(%x & % & (% & %) & %Hfn & H)"; simpl in *; subst; simpl in *; subst.
  destruct x, Hfn as (? & ? & ? & ? & ? & ? & ? & ? & ?); subst; simpl.
  iExists _; iSplit; first by iPureIntro; apply Genv.find_funct_ptr_iff.
  rewrite -bi.later_forall embed_later; by iPoseProof (typed_function_triple with "H") as "H".
Qed.
