From iris.algebra Require Import csum excl auth cmra_big_op gmap.
(*From iris.base_logic.lib Require Import ghost_map.*)
From VST.veric Require Import Clight_core SequentialClight.
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

Definition main_type `{!typeG Σ} {cs : compspecs} (P : iProp Σ) : unit → function.fn_params :=
  fn(∀ () : (); P) → ∃ () : (), int.int tint; True.

Global Instance VST_typeG `{!VSTGS OK_ty Σ} : typeG Σ := TypeG _ _.

(* up *)
Lemma var_sizes_ok_sub : forall c1 c2 vars (Hsub : cenv_sub c1 c2)
  (Hcomplete : Forall (fun it : ident * Ctypes.type => complete_type c1 (snd it) = true) vars),
  @var_sizes_ok c1 vars -> @var_sizes_ok c2 vars.
Proof.
  intros.
  pose proof (List.Forall_and Hcomplete H) as H1.
  eapply Forall_impl; first apply H1.
  simpl; intros ? (? & ?).
  rewrite (cenv_sub_sizeof Hsub) //.
Qed.

(* see believe_internal *)
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
      ⊢ Vptr b Ptrofs.zero ◁ᵥ (b, 0%Z) @ function_ptr Espec (nofunc_tycontext V G) (Build_genv ge cenv_cs) t.

(* RefinedC assumes that typechecking main implicitly typechecks all functions it calls.
   Can we do that too, or do we need to say that each function meets its specified type
   (and convert G to a list of types for each function)? *)

(* just main *)
Definition typed_prog `{!VSTGS OK_ty Σ} {Espec : ext_spec OK_ty} {C : compspecs}
       (prog: Clight.program) (ora: OK_ty) (V: varspecs) G : Prop :=
compute_list_norepet (prog_defs_names prog) = true  /\
all_initializers_aligned prog /\
Maps.PTree.elements cenv_cs = Maps.PTree.elements (prog_comp_env prog) /\
(*typed_func V G (Genv.globalenv prog) (prog_funct prog) G /\*)
match_globvars (prog_vars prog) V = true /\
  typed_func V G (ConstType unit) (main_type emp) (Genv.globalenv (program_of_program prog)) prog.(prog_main).

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

(* mimicking semax_prog_rule for typed_prog *)

Lemma typed_func_entry_point `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} {CS: compspecs}
  V f G prog b id_fun args A t
(*    (E: dtfr (MaskTT A))
   (P: dtfr (ArgsTT A))
   (Q: dtfr (AssertTT A)) *)
  h z:
  let retty := tint in
  postcondition_allows_exit OK_spec retty ->
  Maps.PTree.elements cenv_cs = Maps.PTree.elements (prog_comp_env prog) ->
  typed_func V G A t (globalenv prog) id_fun ->
  Genv.find_symbol (globalenv prog) id_fun = Some b ->
  Genv.find_funct_ptr (globalenv prog) b = Some (Internal f) ->
(*   find_id id_fun G =
     Some (mk_funspec (params, retty) cc_default A E P Q) ->
 *)  tc_vals (map snd f.(fn_params)) args ->
  let gargs := (filter_genv (globalenv prog), args) in
  { q : CC_core |
   (forall m,
(*     Forall (fun v => Val.inject (Mem.flat_inj (nextblock m)) v v)  args->*)
(*     inject_neutral (nextblock m) m /\ *)
(*     Coqlib.Ple (Genv.genv_next (Genv.globalenv prog)) (nextblock m) ->*)
    exists m', semantics.initial_core (cl_core_sem (globalenv prog)) h
    m q m' (Vptr b Ptrofs.zero) args) /\

  forall (a: @dtfr Σ A),
    fp_Pa (t a) ∗ ([∗ list] v;ty∈args;fp_atys (t a), v ◁ᵥ ty)
    ⊢ jsafeN OK_spec (globalenv prog) ⊤ z q }.
Proof.
intro retty.
intros EXIT CSEQ SP Findb Findf arg_p.
assert (semax_body_params_ok f = true
     ∧ Forall (λ it : ident * Ctypes.type, complete_type cenv_cs it.2 = true)
         (fn_vars f)
       ∧ list_norepet (map fst (fn_params f) ++ map fst (fn_temps f))
       ∧ list_norepet (map fst (fn_vars f))
       ∧ var_sizes_ok (fn_vars f)
          ∧ (⊢ Vptr b Ptrofs.zero
                   ◁ᵥ (b, 0%Z) @
                      function_ptr OK_spec (nofunc_tycontext V G)
                        {| genv_genv := globalenv prog; genv_cenv := cenv_cs |} t))%type as Hf.
{ destruct SP as (? & ? & ? & ? & ? & ? & ? & Hb & Hf & ?).
  rewrite Hb in Findb; inv Findb; auto 6. }
clear SP; destruct Hf as (? & ? & Hparams & ? & Hsz & Hty).
exists (Clight_core.Callstate (Internal f) args Kstop).
split.
{ intros m; exists m.
  simpl.
  rewrite Findf //. }
intros.
iIntros "(P & args)".
iApply jsafe_step.
rewrite /jstep_ex.
iIntros (?) "(Hm & ?)".
change (prog_comp_env prog) with (genv_cenv (globalenv prog)) in *.
assert (HGG: cenv_sub (@cenv_cs CS) (globalenv prog)).
 { clear - CSEQ. forget (@cenv_cs CS) as cs1.
   forget (genv_cenv (globalenv prog)) as cs2.
   hnf; intros; hnf.
   destruct (cs1 !! i)%maps eqn:?H; auto.
   apply Maps.PTree.elements_correct in H.
   apply Maps.PTree.elements_complete. congruence.
 }
eapply var_sizes_ok_sub in Hsz; [|done..].
iMod (alloc_stackframe with "Hm") as (m' ve' (? & ?)) "(Hm & Hstack)"; [done..|].
iIntros "!>".
iExists _, _; iSplit.
{ iPureIntro; constructor.
  constructor; eauto.
  all: admit. }
iFrame.
(* This will be annoying to use because args are already values, not exprs. *)
iPoseProof (type_call_fnptr _ _ _ _ (Evar id_fun (Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f))) with "[Hstack]") as "Hty".
{ simpl.
  admit. (* use Hstack, args, Hty; also need an assumption that the input types are satisfied *) }
rewrite /typed_call /=.
admit.
Admitted.

Lemma typed_prog_rule `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} {CS: compspecs} :
  forall V G prog m h z,
     postcondition_allows_exit OK_spec tint ->
     typed_prog(C := CS) prog z V G ->
     Genv.init_mem prog = Some m ->
     { b & { q : CC_core &
       (Genv.find_symbol (globalenv prog) (prog_main prog) = Some b) *
       (exists m', semantics.initial_core (cl_core_sem (globalenv prog)) h
                       m q m' (Vptr b Ptrofs.zero) nil) *
       (state_interp Mem.empty z ∗ funspec_auth ∅ ∗ has_ext z ⊢ |==> state_interp m z ∗ jsafeN OK_spec (globalenv prog) ⊤ z q)
     } }%type.
Proof.
  intros until z. intro EXIT. intros ? H1.
  generalize H; intros [? [AL [HGG [GV Hty]]]].
  destruct (Genv.find_symbol (globalenv prog) (prog_main prog)) eqn: Hmain.
  2: { exfalso; destruct Hty as (? & ? & ? & ? & ? & ? & ? & Hmain' & ?). rewrite Hmain in Hmain'; done. }
  destruct (Genv.find_funct_ptr (globalenv prog) b) as [ [|] |] eqn: Hf;
    [|exfalso; destruct Hty as (? & ? & ? & ? & ? & ? & ? & Hmain' & Hf' & ?); rewrite Hmain in Hmain'; inv Hmain'; rewrite Hf in Hf'; done..].
  eapply typed_func_entry_point in Hty as (q & Hinit & Hsafe); eauto.
  2: { (* no args *) admit. }
  exists b, q; split; first auto.
  specialize (Hsafe tt).
  rewrite /main_type /= in Hsafe.
  iIntros "((Hm & $) & Hf & Hz)".
  apply compute_list_norepet_e in H0.
  (* need a version of this without funspec_auth *)
  iMod (initialize_mem' with "[$Hm $Hf]") as "($ & Hm & Hcore & Hmatch)"; [try done..|].
  { admit. }
  rewrite -Hsafe.
Admitted.

(* The G in typed_prog is pretty much arbitrary, and we could replace it with a
   dummy that has default funspecs for every function in prog_funct prog, or work
   around it entirely. *)

(** * The main adequacy lemma *)
Lemma refinedc_adequacy Σ `{!VSTGpreS OK_ty Σ} {Espec : forall `{VSTGS OK_ty Σ}, ext_spec OK_ty} {dryspec : ext_spec OK_ty} (initial_oracle: OK_ty)
     (EXIT: forall `{!VSTGS OK_ty Σ}, semax_prog.postcondition_allows_exit Espec tint)
     (Hdry : forall `{!VSTGS OK_ty Σ}, ext_spec_entails Espec dryspec)
     prog V m :
     (∃ (G : forall `{VSTGS OK_ty Σ}, funspecs), forall (HH : VSTGS OK_ty Σ), exists CS: compspecs,
        typed_prog(Espec := Espec) prog initial_oracle V G) ->
     Genv.init_mem prog = Some m ->
     exists b, exists q,
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       semantics.initial_core (cl_core_sem (globalenv prog))
           0 m q m (Vptr b Ptrofs.zero) nil /\
       forall n,
        @step_lemmas.dry_safeN _ _ _ OK_ty (genv_symb_injective)
            (cl_core_sem (globalenv prog))
            dryspec
            (Build_genv (Genv.globalenv prog) (prog_comp_env prog))
             n initial_oracle q m.
Proof.
  intros (G & H) Hm.
  assert (forall n, exists b, exists q,
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       semantics.initial_core (cl_core_sem (globalenv prog))
           0 m q m (Vptr b Ptrofs.zero) nil /\
        @step_lemmas.dry_safeN _ _ _ OK_ty (genv_symb_injective)
            (cl_core_sem (globalenv prog))
            dryspec
            (Build_genv (Genv.globalenv prog) (prog_comp_env prog))
             n initial_oracle q m).
  2: { destruct (H0 O) as (b0 & q0 & ? & (? & _) & _); eexists _, _; split; first done; split; first done.
       intros n; destruct (H0 n) as (b & q & ? & (? & _) & Hsafe).
       assert (b0 = b) as -> by congruence.
       assert (q0 = q) as -> by congruence.
       done. }
  intros n; eapply ouPred.pure_soundness, (step_fupdN_soundness_no_lc' _ (S n) O); [apply _..|].
  simpl; intros; iIntros "_".
  iMod (@init_VST _ _ VSTGpreS0) as "H".
  iDestruct ("H" $! Hinv) as (?? HE) "(H & ?)".
  set (HH := Build_VSTGS _ _ (HeapGS _ _ _ _) HE).
  specialize (H HH); specialize (EXIT HH); destruct H.
  eapply (typed_prog_rule _ _ _ _ n) in H as (b & q & (? & ? & Hinit & ->) & Hsafe); [|done..].
  iMod (Hsafe with "H") as "Hsafe".
  iPoseProof (adequacy with "Hsafe") as "Hsafe".
  iApply step_fupd_intro; first done; iNext.
  iApply (step_fupdN_mono with "Hsafe"); apply bi.pure_mono; intros.
  eapply ext_spec_entails_safe in H; eauto 6.
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
