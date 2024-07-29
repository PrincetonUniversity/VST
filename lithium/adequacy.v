From iris.algebra Require Import csum excl auth cmra_big_op gmap.
(*From iris.base_logic.lib Require Import ghost_map.*)
From VST.veric Require Import SequentialClight.
From VST.lithium Require Export type.
From VST.lithium Require Import programs function bytes globals int fixpoint.
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

Definition main_type `{!typeG Σ} {cs : compspecs} (P : iProp Σ) : {A : TypeTree & (dtfr(Σ := Σ) A → function.fn_params)%type} :=
  existT (ConstType unit) (fn(∀ () : (); P) → ∃ () : (), int.int tint; True).

Global Instance VST_typeG `{!VSTGS OK_ty Σ} : typeG Σ := TypeG _ _.

Definition typed_func `{!VSTGS OK_ty Σ} (V: varspecs) {C: compspecs}
  (t : {A : TypeTree & (dtfr A → function.fn_params)%type})
  (ge: Genv.t Clight.fundef Ctypes.type) (id: ident) (f: function) :=
  semax_body_params_ok f = true /\
      Forall
         (fun it : ident * Ctypes.type =>
          complete_type cenv_cs (snd it) =
          true) (fn_vars f) /\
       var_sizes_ok (f.(fn_vars)) /\
       ∃ b, Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some (Internal f) /\
      ∀ OK_spec : ext_spec OK_ty,
      (* at least need function pointers *) ⊢ (Vptr b Ptrofs.zero) ◁ᵥ (b, 0%Z) @ function_ptr t.

(* RefinedC assumes that typechecking main implicitly typechecks all functions it calls.
   Can we do that too, or do we need to say that each function meets its specified type
   (and convert G to a list of types for each function)? *)

(* just main *)
Definition typed_prog `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} {C: compspecs}
       (prog: Clight.program) (ora: OK_ty) (V: varspecs) : Prop :=
compute_list_norepet (prog_defs_names prog) = true  /\
all_initializers_aligned prog /\
Maps.PTree.elements cenv_cs = Maps.PTree.elements (prog_comp_env prog) /\
(*typed_func V G (Genv.globalenv prog) (prog_funct prog) G /\*)
match_globvars (prog_vars prog) V = true /\
∃ f, typed_func V (main_type emp) (Genv.globalenv (program_of_program prog)) prog.(prog_main) f.

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

(** * The main adequacy lemma *)
Lemma refinedc_adequacy Σ `{!VSTGpreS OK_ty Σ} {Espec : forall `{VSTGS OK_ty Σ}, ext_spec OK_ty} {dryspec : ext_spec OK_ty} (initial_oracle: OK_ty)
     (EXIT: forall `{!VSTGS OK_ty Σ}, semax_prog.postcondition_allows_exit Espec tint)
     (Hdry : forall `{!VSTGS OK_ty Σ}, ext_spec_entails Espec dryspec)
     prog V m :
     (forall {HH : VSTGS OK_ty Σ}, exists CS: compspecs, typed_prog(OK_spec := Espec) prog initial_oracle V) ->
     Genv.init_mem prog = Some m ->
     exists b, exists q,
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       semantics.initial_core (Clight_core.cl_core_sem (globalenv prog))
           0 m q m (Vptr b Ptrofs.zero) nil /\
       forall n,
        @step_lemmas.dry_safeN _ _ _ OK_ty (genv_symb_injective)
            (Clight_core.cl_core_sem (globalenv prog))
            dryspec
            (Build_genv (Genv.globalenv prog) (prog_comp_env prog))
             n initial_oracle q m.
Proof.
  
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

Ltac adequacy_unfold_equiv :=
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
    adequacy_intro_parameter => /=; eexists eq_refl => /=; split_and!; [..|adequacy_intro_parameter => /=; split_and!];  repeat adequacy_solve_equiv unfold_tac.
