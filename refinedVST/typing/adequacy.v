From iris.algebra Require Import csum excl auth cmra_big_op gmap.
(*From iris.base_logic.lib Require Import ghost_map.*)
From VST.sepcomp Require Import step_lemmas.
From VST.veric Require Import Clight_core env external_state juicy_extspec.
From VST.typing Require Export type.
From VST.typing Require Import programs function bytes globals int fixpoint.
Set Default Proof Using "Type".

(* Class typePreG Σ := PreTypeG {
  type_invG                      :: invGpreS Σ;
  type_heap_heap_inG             :: heapGpreS Σ;
(*  type_heap_alloc_meta_map_inG  :: ghost_mapG Σ alloc_id (Z * nat * alloc_kind);
  type_heap_alloc_alive_map_inG  :: ghost_mapG Σ alloc_id bool;
  type_heap_fntbl_inG            :: ghost_mapG Σ addr function; *)
}.

Definition typeΣ : gFunctors :=
  #[invΣ;
   GFunctor (constRF (authR heapUR));
   ghost_mapΣ alloc_id (Z * nat * alloc_kind);
   ghost_mapΣ alloc_id bool;
   ghost_mapΣ addr function].
Global Instance subG_typePreG {Σ} : subG typeΣ Σ → typePreG Σ.
Proof. solve_inG. Qed. *)

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

(*(* see believe_internal *)
Definition typed_func `{!VSTGS OK_ty Σ} {Espec : ext_spec OK_ty} (V: varspecs) (G : funspecs) {C: compspecs}
  (A : TypeTree) (t : dtfr A → function.fn_params)
  (ge: Genv.t Clight.fundef Ctypes.type) (id: ident) :=
  exists f, semax_body_params_ok f = true /\
      Forall (fun it : ident * Ctypes.type =>
          complete_type cenv_cs (snd it) = true) (fn_vars f) /\
       list_norepet (map fst (fn_params f) ++ map fst (fn_temps f)) /\
       list_norepet (map fst (fn_vars f)) /\
       var_sizes_ok (f.(fn_vars)) /\
       ∃ b, Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some (Internal f) /\
      ⊢ Vptr b Ptrofs.zero ◁ᵥ|tptr (type_of_function f)| (b, 0%Z) @ function_ptr Espec (nofunc_tycontext V G) (Build_genv ge cenv_cs) t.*)

(* RefinedC assumes that typechecking main implicitly typechecks all functions it calls.
   Can we do that too, or do we need to say that each function meets its specified type
   (and convert G to a list of types for each function)? *)

(*(* just main *)
Definition typed_prog `{!VSTGS OK_ty Σ} {Espec : ext_spec OK_ty} {C : compspecs}
       (prog: Clight.program) (ora: OK_ty) (V: varspecs) G : Prop :=
compute_list_norepet (prog_defs_names prog) = true  /\
all_initializers_aligned prog /\
Maps.PTree.elements cenv_cs = Maps.PTree.elements (prog_comp_env prog) /\
(*typed_func V G (Genv.globalenv prog) (prog_funct prog) G /\*)
match_globvars (prog_vars prog) V = true /\
  typed_func V G (ConstType unit) (main_type emp) (Genv.globalenv (program_of_program prog)) prog.(prog_main).*)

(* Definition typed_prog `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} {C: compspecs}
       (prog: program) (ora: OK_ty) (V: varspecs) (G: funspecs) : Prop :=
compute_list_norepet (prog_defs_names prog) = true  /\
all_initializers_aligned prog /\
Maps.PTree.elements cenv_cs = Maps.PTree.elements (prog_comp_env prog) /\
typed_func V G (Genv.globalenv prog) (prog_funct prog) G /\
match_globvars (prog_vars prog) V = true /\
match find_id prog.(prog_main) G with
| Some s => exists post,
      s = main_spec_ext' prog ora post
| None => False
end. *)


(*[∗ list] main ∈ thread_mains, ∃ P, main ◁ᵥ main @ function_ptr (main_type P) ∗ P*)

(* wrapper around veric/lifting's adequacy theorem *)
Lemma refinedc_adequacy: forall `{!VSTGpreS OK_ty Σ} {Espec : forall `{VSTGS OK_ty Σ}, ext_spec OK_ty} {dryspec : ext_spec OK_ty}
  (Hdry : forall `{!VSTGS OK_ty Σ}, ext_spec_entails Espec dryspec) {CS: compspecs}
  (ge : Genv.t Clight.fundef Ctypes.type) m z s f (T : forall `{!typeG OK_ty Σ}, option val → type → assert) ve te (Hf : f.(fn_vars) = [])
  (EXIT: forall `{!VSTGS OK_ty Σ} v ty, ⊢ (T v ty O -∗ ∀ m z, state_interp m z -∗ ⌜∃ i, ext_spec_exit Espec (Some (Vint i)) z m⌝)),
  (∀ `{HH : invGS_gen HasNoLc Σ}, ⊢ |={⊤}=> ∃ _ : gen_heapGS share address resource Σ, ∃ _ : funspecGS Σ, ∃ _ : envGS Σ, ∃ _ : externalGS OK_ty Σ,
    let H : VSTGS OK_ty Σ := Build_VSTGS _ _ (HeapGS _ _ _ _) _ _ in
    stack_level 0 ∗ ⎡state_interp m z⎤ ∗ ⌜typecheck_var_environ (make_env ve) (make_tycontext_v (fn_vars f))⌝ ∧ ⎡env_auth (init_stack (programs.ge ge) ve te)⎤ ∗
    typed_stmt Espec ge s f T) →
       (forall n,
        @dry_safeN _ _ _ OK_ty (genv_symb_injective) (cl_core_sem (programs.ge ge)) dryspec
            (programs.ge ge) n z (Clight_core.State f s Kstop ve te) m).
Proof.
  intros; apply wp_adequacy with (R := λ _ : VSTGS OK_ty Σ, λ v,
    (<affine> ⌜v = None⌝ ∗ T _ v tytrue) ∨ (let v := force_val v in 
      ∃ ty, ⎡(valinject (fn_return f) v) ◁ᵥ|fn_return f| ty⎤ ∗ T _ (Some v) ty)); [try done..|].
  { monPred.unseal.
    iIntros (??) "[(_ & H) | (% & _ & H)]"; by iApply EXIT. }
  iIntros; iMod H as (????) "($ & $ & $ & $ & H)".
  iModIntro; iExists _.
  iApply @wp_conseq; last iApply "H"; auto; simpl.
  - iIntros "?"; iLeft; auto.
  - iIntros (?) "(% & ? & ?)"; iRight; eauto with iFrame.
Qed.

(*Lemma refinedc_adequacy Σ `{!typePreG Σ} (thread_mains : list loc) (fns : gmap addr function) (gls : list loc) (gvs : list val.val) n t2 σ2 κs hs σ:
  alloc_new_blocks initial_heap_state GlobalAlloc gls gvs hs →
  σ = {| st_heap := hs; st_fntbl := fns; |} →
  (∀ {HtypeG : typeG Σ}, ∃ gl gt,
  let Hglobals : globalG Σ := {| global_locs := gl; global_initialized_types := gt; |} in
    ([∗ list] l; v ∈ gls; gvs, l ↦ v) -∗
    ([∗ map] k↦qs∈fns, fntbl_entry (fn_loc k) qs) ={⊤}=∗
      [∗ list] main ∈ thread_mains, ∃ P, main ◁ᵥ main @ function_ptr (main_type P) ∗ P) →
  nsteps (Λ := c_lang) n (initial_prog <$> thread_mains, σ) κs (t2, σ2) →
  ∀ e2, e2 ∈ t2 → not_stuck e2 σ2.
Proof.
  move => Hnew -> Hwp. apply: wp_strong_adequacy. move => ?.
  set h := to_heapUR ∅.
  iMod (own_alloc (● h ⋅ ◯ h)) as (γh) "[Hh _]" => //.
  { apply auth_both_valid_discrete. split => //. }
  iMod (ghost_map_alloc fns) as (γf) "[Hf Hfm]".
  iMod (ghost_map_alloc_empty (V:=(Z * nat * alloc_kind))) as (γr) "Hr".
  iMod (ghost_map_alloc_empty (V:=bool)) as (γs) "Hs".
  set (HheapG := HeapG _ _ γh _ γr _ γs _ γf).
  set (HrefinedCG := RefinedCG _ _ HheapG).
  set (HtypeG := TypeG _ HrefinedCG).
  move: (Hwp HtypeG) => {Hwp} [gl [gt]].
  set (Hglobals := {| global_locs := gl; global_initialized_types := gt; |}).
  move => Hwp.
  iMod (heap_alloc_new_blocks_upd with "[Hh Hr Hs]") as "[Hctx Hmt]" => //. {
    rewrite /heap_state_ctx /alloc_meta_ctx /to_alloc_meta_map /alloc_alive_ctx /to_alloc_alive_map !fmap_empty.
    by iFrame.
  }
  rewrite big_sepL2_sep. iDestruct "Hmt" as "[Hmt Hfree]".
  iAssert (|==> [∗ map] k↦qs ∈ fns, fntbl_entry (fn_loc k) qs)%I with "[Hfm]" as ">Hfm". {
    iApply big_sepM_bupd. iApply (big_sepM_impl with "Hfm").
    iIntros "!>" (???) "Hm". rewrite fntbl_entry_eq.
    iExists _. iSplitR; [done|]. by iApply ghost_map_elem_persist.
  }
  iMod (Hwp with "Hmt Hfm") as "Hmains".

  iModIntro. iExists _, (replicate (length thread_mains) (λ _, True%I)), _, _.
  iSplitL "Hctx Hf"; last first. 1: iSplitL "Hmains".
  - rewrite big_sepL2_fmap_l. iApply big_sepL2_replicate_r; [done|]. iApply (big_sepL_impl with "Hmains").
    iIntros "!#" (? main ?); iDestruct 1 as (P) "[Hmain HP]".
    iApply (type_call with "[-]"). 2: { by iIntros (??) "??". }
    iApply type_val. iApply type_val_context.
    iExists (main @ function_ptr (main_type P))%I => /=. iFrame => /=.
    iApply type_call_fnptr. iIntros "_". iExists () => /=. iFrame. by iIntros (v []) "Hv" => /=.
  - iFrame. iIntros (?? _ _ ?) "_ _ _". iApply fupd_mask_intro_discard => //. iPureIntro. by eauto.
  - by iFrame.
Qed.

(** * Helper functions for using the adequacy lemma *)
Definition fn_lists_to_fns (addrs : list addr) (fns : list function) : gmap addr function :=
  list_to_map (zip addrs fns).

Lemma fn_lists_to_fns_cons `{!refinedcG Σ} addr fn addrs fns :
  length addrs = length fns →
  addr ∉ addrs →
  ([∗ map] k↦qs ∈ fn_lists_to_fns (addr :: addrs) (fn :: fns), fntbl_entry (fn_loc k) qs) -∗
  fntbl_entry (ProvFnPtr, addr) fn ∗ ([∗ map] k↦qs ∈ fn_lists_to_fns addrs fns, fntbl_entry (fn_loc k) qs).
Proof.
  move => Hnotin ?.
  rewrite /fn_lists_to_fns /= big_sepM_insert. { by iIntros "?". }
  apply not_elem_of_list_to_map_1. rewrite fst_zip => //; lia.
Qed.*)

(** * Tactics for solving conditions in an adequacy proof *)

Ltac adequacy_intro_parameter :=
  repeat lazymatch goal with
         | |- ∀ _ : (), _ => case
         | |- ∀ _ : (_ * _), _ => case
         | |- ∀ _ : _, _ => move => ?
         end.

(*Ltac adequacy_unfold_equiv :=
  lazymatch goal with
  | |- type_fixpoint _ _ ≡ type_fixpoint _ _ => apply: type_fixpoint_proper; [|move => ??]
  | |- ty_own_val _ _ ≡ ty_own_val _ _ => unfold ty_own_val => /=
  | |-  _ =@{struct_layout} _ => apply: struct_layout_eq
  end.

Ltac adequacy_solve_equiv unfold_tac :=
  first [ eassumption | fast_reflexivity | unfold_type_equiv | adequacy_unfold_equiv | f_contractive | f_equiv' | reflexivity | progress unfold_tac ].

Ltac adequacy_solve_typed_function lemma unfold_tac :=
  iApply typed_function_equiv; [
    done |
    adequacy_intro_parameter => /=; repeat (constructor; [done|]); by constructor |
    | iApply lemma => //; iExists _; repeat iSplit => //];
    adequacy_intro_parameter => /=; eexists eq_refl => /=; split_and!; [..|adequacy_intro_parameter => /=; split_and!];  repeat adequacy_solve_equiv unfold_tac.*)

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
    iDestruct ("H" with "Hret") as "(% & ? & ? & $)"; iFrame.
    destruct v; first by iFrame.
    by apply tc_val_Vundef in Htc.
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
