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

Require Import compcert.common.Smallstep.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.step_lemmas.

Section CompCert.
  (* is this provable? *)
  Lemma safe_external_inv : forall {Z} (Hspec : external_specification _ _ Z) ge z q m ef args, cl_at_external q = Some (ef, args) ->
    (forall n, dry_safeN(genv_symb := genv_symb_injective) (cl_core_sem ge) Hspec ge n z q m) ->
    exists x, ext_spec_pre Hspec ef x (genv_symb_injective ge) (sig_args (ef_sig ef)) args z m /\
      forall ret m' z' n', Val.has_type_list args (sig_args (ef_sig ef)) ->
        Builtins0.val_opt_has_rettype ret (sig_res (ef_sig ef)) ->
        ext_spec_post Hspec ef x (genv_symb_injective ge) (sig_res (ef_sig ef)) ret z' m' ->
        exists c', cl_after_external ret q = Some c' /\ dry_safeN(genv_symb := genv_symb_injective) (cl_core_sem ge) Hspec ge n' z' c' m'.
  Proof.
  Admitted.

  (* We can't directly import CompCert's top-level correctness theorem for licensing reasons,
     but we can generalize over an analogous theorem. *)
  Variables (asm_prog : Type) (asm_state : Type) (asm_core_sem : asm_prog -> CoreSemantics asm_state mem)
    (asm_initial_state : asm_prog -> (asm_state * mem) -> Prop) (asm_final_state : asm_prog -> (asm_state * mem) -> int -> Prop)
    (ccomp : program -> option asm_prog).
  Hypothesis (asm_final_halted : forall prog s i, asm_final_state prog s i -> halted (asm_core_sem prog) s.1 i).

  (* backward simulation adapted from compcert.common.Smallstep *)
  Record bsim_properties prog1 prog2 (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> (CC_core * mem) -> (asm_state * mem) -> Prop) : Prop := {
    bsim_order_wf: well_founded order;
    bsim_match_initial_states:
      forall s1, Clight.initial_state prog1 s1 ->
        exists i s2, asm_initial_state prog2 s2 /\ match_states i (CC_state_to_CC_core s1) s2;
    bsim_match_final_states:
      forall i s1 s2 r,
      match_states i s1 s2 -> (*safe L1 s1 ->*) asm_final_state prog2 s2 r ->
      exists s1', corestep_star (cl_core_sem (Clight.globalenv prog1)) s1.1 s1.2 (CC_state_to_CC_core s1').1 (CC_state_to_CC_core s1').2 /\
        Clight.final_state s1' r;
    bsim_progress:
      forall i s1 s2,
      match_states i s1 s2 ->
      (exists r, asm_final_state prog2 s2 r) \/
      (exists s2' m', corestep (asm_core_sem prog2) s2.1 s2.2 s2' m') \/
      (exists ef args, at_external (asm_core_sem prog2)s2.1 s2.2 = Some (ef, args));
    bsim_simulation:
      forall s2 s2', corestep (asm_core_sem prog2) s2.1 s2.2 s2'.1 s2'.2 ->
      forall i s1, match_states i s1 s2 ->
      exists i', exists s1',
         (corestep_plus (cl_core_sem (Clight.globalenv prog1)) s1.1 s1.2 s1'.1 s1'.2 \/
         (corestep_star (cl_core_sem (Clight.globalenv prog1)) s1.1 s1.2 s1'.1 s1'.2 /\ order i' i))
      /\ match_states i' s1' s2';(*
    bsim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id*)
    bsim_external:
      forall s2 ef args, at_external (asm_core_sem prog2) s2.1 s2.2 = Some (ef, args) ->
      forall i s1, match_states i s1 s2 ->
      cl_at_external s1.1 = Some (ef, args) /\
      forall Z e x ge tys z, ext_spec_pre(Z := Z) e ef x ge tys args z s1.2 ->
        ext_spec_pre e ef x ge tys args z s2.2 /\
        forall ty ret z' m',
          ext_spec_post e ef x ge ty ret z' m' ->
          exists m1', ext_spec_post e ef x ge ty ret z' m1' /\
            (forall s1', cl_after_external ret s1.1 = Some s1' ->
             exists s2', match_states i (s1', m1') (s2', m') /\
             after_external (asm_core_sem prog2) ret s2.1 m' = Some s2')
  }.

  Inductive backward_simulation prog1 prog2 : Prop :=
    Backward_simulation index order match_states (props: bsim_properties prog1 prog2 index order match_states).

  Hypothesis ccomp_correct :
    forall p tp, ccomp p = Some tp -> backward_simulation p tp.

  Lemma cl_corestep_fun : forall ge, corestep_fun (cl_core_sem ge).
  Proof.
    intros ??.
    by apply cl_corestep_fun.
  Qed.

  Theorem whole_program_asm_safety:
    forall Σ {CS: compspecs} {Espec: OracleKind} `{!VSTGpreS OK_ty Σ} (initial_oracle: OK_ty)
     (EXIT: semax_prog.postcondition_allows_exit tint)
     (prog : Ctypes.program _) V G (Hmain_sig : forall b f, Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b ->
        Genv.find_funct_ptr (Genv.globalenv prog) b = Some f -> type_of_fundef f = Tfunction Ctypes.Tnil type_int32s cc_default) m prog',
     (forall {HH : heapGS Σ} {HE : externalGS OK_ty Σ}, @semax_prog _ HH Espec HE CS prog initial_oracle V G) ->
     Genv.init_mem prog = Some m -> ccomp prog = Some prog' ->
     exists s, asm_initial_state prog' s /\
       forall n,
        @dry_safeN _ _ _ OK_ty (genv_symb_injective)
            (asm_core_sem prog')
            OK_spec
            (Build_genv (Genv.globalenv prog) (prog_comp_env prog))
             n initial_oracle s.1 s.2.
  Proof.
    intros until prog'; intros Hproof Hm Hcomp.
    eapply whole_program_sequential_safety_ext in Hproof as (? & q & Hb & (Hinit & _) & Hsafe); eauto.
    simpl in Hinit.
    if_tac in Hinit; last done.
    destruct (Genv.find_funct_ptr _ _) eqn: Hmain; inversion Hinit.
    assert (Clight.initial_state prog (CC_core_to_CC_state q m)) as Hinit'.
    { subst; econstructor; eauto. }
    specialize (ccomp_correct _ _ Hcomp); inv ccomp_correct.
    eapply bsim_match_initial_states in Hinit' as (i & s & ? & Hmatch); last done.
    eexists; split; first done.
    clear - asm_final_halted EXIT props Hsafe Hmatch.
    simpl in Hmatch.
    set (qc := Clight_core.Callstate _ _ _) in Hsafe, Hmatch; clearbody qc.
    rename initial_oracle into z.
    set (ge := {| genv_genv := _; genv_cenv := _|} ) in *.
    intros n; revert qc m z Hsafe i s Hmatch; induction n; first constructor; intros.
    destruct (bsim_progress _ _ _ _ _ props _ _ _ Hmatch) as [(? & Hhalt) | [(s' & m' & Hstep) | (ef & args & Hext)]].
    - eapply safeN_halted; first by apply asm_final_halted.
      eapply bsim_match_final_states in Hmatch as (sc & (nc & Hsteps) & Hfinal); [|done..].
      specialize (Hsafe (1 + S nc)); eapply safe_corestepN_forward in Hsafe; [| apply cl_corestep_fun | apply Hsteps].
      inv Hfinal; inv Hsafe; try done.
      { inv H0. }
      { by apply EXIT. }
    - eapply safeN_step; first done.
      eapply (bsim_simulation _ _ _ _ _ props _ (_, _)) in Hstep as (? & (?, ?) & Hsteps & Hmatch'); last done.
      unshelve eapply (IHn _ _ _ _ _ (_, _)); last apply Hmatch'.
      intros n0.
      destruct Hsteps as [(nc & Hsteps) | ((nc & Hsteps) & Hord)];
        (eapply safe_corestepN_forward; [apply cl_corestep_fun | done | apply Hsafe]).
    - pose proof (bsim_external _ _ _ _ _ props _ _ _ Hext _ _ Hmatch) as (Hextc & Hpre).
      assert (exists x, ext_spec_pre OK_spec ef x (genv_symb_injective ge) (sig_args (ef_sig ef)) args z s.2 /\
        forall ret z' m' n', Val.has_type_list args (sig_args (ef_sig ef)) -> Builtins0.val_opt_has_rettype ret (sig_res (ef_sig ef)) ->
          n' <= n ->
          ext_spec_post OK_spec ef x (genv_symb_injective ge) (sig_res (ef_sig ef)) ret z' m' ->
          exists s2', after_external (asm_core_sem prog') ret s.1 m' = Some s2' /\
            dry_safeN(genv_symb := genv_symb_injective) (asm_core_sem prog') OK_spec ge n' z' s2' m') as (x & Hprea & Hposta).
      { eapply safe_external_inv in Hextc as (x & Hprec & Hpost_safe); last apply Hsafe.
        apply Hpre in Hprec as (? & Hpost').
        exists x; split; first done; intros ??????? Hposta.
        apply Hpost' in Hposta as (? & Hpostc & Hafter').
        unshelve edestruct Hpost_safe as (? & Hafterc & _); [done..|].
        destruct (Hafter' _ Hafterc) as (? & Hmatch' & ?).
        eexists; split; first done.
        eapply safe_downward; first done.
        unshelve eapply (IHn _ _ _ _ _ (_, _)); last apply Hmatch'.
        intros nc; unshelve edestruct Hpost_safe as (? & Hafterc' & Hsafe');
          [.. | apply Hpostc | rewrite Hafterc' in Hafterc; inv Hafterc; apply Hsafe']; done. }
      eapply safeN_external; [done.. | eauto].
  Qed.

End CompCert.
