(* A core wp-based separation logic for Clight, in the Iris style. Maybe VeriC can be built on top of this? *)
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax.
Require Import VST.veric.semax_straight.

Global Instance local_absorbing `{!heapGS Σ} l : Absorbing (local l).
Proof.
  rewrite /local; apply monPred_absorbing, _.
Qed.

Global Instance local_persistent `{!heapGS Σ} l : Persistent (local l).
Proof.
  rewrite /local; apply monPred_persistent, _.
Qed.

Section mpred.

Context `{!VSTGS OK_ty Σ} (OK_spec : ext_spec OK_ty).

Definition assert_safe
     (E: coPset) (f: function) (ctl: contx) rho : iProp Σ :=
       ∀ ora ge ve te,
       ⌜rho = construct_rho (filter_genv ge) ve te⌝ →
       match ctl with
       | Stuck => |={E}=> False
       | Cont (Kseq s ctl') => 
             jsafeN OK_spec ge E ora (State f s ctl' ve te)
       | Cont (Kloop1 body incr ctl') =>
             jsafeN OK_spec ge E ora (State f Sskip (Kloop1 body incr ctl') ve te)
       | Cont (Kloop2 body incr ctl') =>
             jsafeN OK_spec ge E ora (State f (Sloop body incr) ctl' ve te)
       | Cont (Kcall id' f' ve' te' k') => 
             jsafeN OK_spec ge E ora (State f (Sreturn None) (Kcall id' f' ve' te' k') ve te)
       | Cont Kstop =>
             jsafeN OK_spec ge E ora (State f (Sreturn None) Kstop ve te)
       | Cont _ => |={E}=> False
       | Ret None ctl' =>
                jsafeN OK_spec ge E ora (State f (Sreturn None) ctl' ve te)
       | Ret (Some v) ctl' => ∀ e, (∀ m, juicy_mem.mem_auth m -∗ ⌜∃ v', Clight.eval_expr ge ve te m e v' ∧ Cop.sem_cast v' (typeof e) (fn_return f) m = Some v⌝) →
              (* Could we replace these with eval_expr and lose the memory dependence?
                 Right now, the only difference is that e must only access pointers that are valid in the current rmap.
                 But typechecking will also guarantee that. *)
              jsafeN OK_spec ge E ora (State f (Sreturn (Some e)) ctl' ve te)
       end.

Definition wp E f s (Q : assert) : assert := assert_of (λ rho,
    ∀ k, ((* ▷ *) (∀ rho, Q rho -∗ assert_safe E f (Cont k) rho)) -∗ assert_safe E f (Cont (Kseq s k)) rho).
(* ▷ would make sense here, but removing Kseq isn't always a step: for instance, Sskip Kstop is a synonym
   for (Sreturn None) Kstop rather than stepping to it. *)

Definition wp_expr e Φ : assert :=
  ∀ m, ⎡juicy_mem.mem_auth m⎤ -∗
         ∃ v, local (λ rho, forall ge ve te,
            rho = construct_rho (filter_genv ge) ve te ->
            Clight.eval_expr ge ve te m e v (*/\ typeof e = t /\ tc_val t v*)) ∧
         ⎡juicy_mem.mem_auth m⎤ ∗ Φ v.

Definition wp_lvalue e Φ : assert :=
  ∀ m, ⎡juicy_mem.mem_auth m⎤ -∗
         ∃ b o, local (λ rho, forall ge ve te,
            rho = construct_rho (filter_genv ge) ve te ->
            Clight.eval_lvalue ge ve te m e b o Full (*/\ typeof e = t /\ tc_val t v*)) ∧
         ⎡juicy_mem.mem_auth m⎤ ∗ Φ (Vptr b o).

Lemma wp_seq : forall E f s1 s2 Q, wp E f s1 (wp E f s2 Q) ⊢ wp E f (Ssequence s1 s2) Q.
Proof.
  intros; rewrite /wp; split => rho.
  iIntros "H % Hk" (???? ->).
  iApply jsafe_local_step.
  { intros; constructor. }
  iApply ("H" with "[Hk]"); last done.
  by iIntros "% H"; iApply "H".
Qed.

Definition valid_val v :=
  match v with Vptr _ _ => expr.valid_pointer v | _ => True end.

Definition valid_val0 m v : Prop :=
  match v with Vptr b o => valid_pointer m b (Ptrofs.intval o) = true | _ => True end.

Lemma valid_val_mem : forall m v, juicy_mem.mem_auth m ∗ valid_val v ⊢ ⌜valid_val0 m v⌝.
Proof.
  iIntros (??) "(Hm & Hv)"; destruct v; try done.
  iApply expr_lemmas4.valid_pointer_dry0; iFrame.
Qed.

Lemma bool_val_valid : forall m v t b, valid_val0 m v -> Cop2.bool_val t v = Some b -> bool_val v t m = Some b.
Proof.
  rewrite /Cop2.bool_val /bool_val.
  intros; destruct t; try done; simpl.
  - destruct i; done.
  - destruct v; try done.
    simpl in *.
    simple_if_tac; try done.
    rewrite /weak_valid_pointer H //.
  - destruct f; done.
  - destruct (Cop2.eqb_type _ _); try done.
    rewrite /Cop2.bool_val_p in H0.
    simple_if_tac.
    + destruct v; try done.
      rewrite /weak_valid_pointer H //.
    + destruct v; try done.
      rewrite /weak_valid_pointer H //.
Qed.

Lemma wp_if: forall E f e s1 s2 R,
  wp_expr e (λ v, ⎡valid_val v⎤ ∧ ∃ b, ⌜Cop2.bool_val (typeof e) v = Some b⌝ ∧ if b then wp E f s1 R else wp E f s2 R)
  ⊢ wp E f (Sifthenelse e s1 s2) R.
Proof.
  intros; split => rho; rewrite /wp /=.
  iIntros "H % Hk" (???? ->).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iDestruct ("H" with "[%] Hm") as (??) "(Hm & H)"; first done.
  iDestruct (valid_val_mem with "[Hm H]") as %?.
  { rewrite bi.and_elim_l; iFrame. }
  rewrite bi.and_elim_r; iDestruct "H" as (b ?) "H".
  iIntros "!>"; iExists _, m.
  iSplit.
  { iPureIntro.
    econstructor; eauto.
    apply bool_val_valid; eauto. }
  iFrame.
  destruct b; simpl; iNext; iApply ("H" with "[-]"); done.
Qed.

(* see also semax_lemmas.derives_skip *)
Lemma safe_skip : forall E ora f k ge ve te,
  assert_safe E f (exit_cont EK_normal None k) (construct_rho (filter_genv ge) ve te) ⊢
  jsafeN OK_spec ge E ora (State f Sskip k ve te).
Proof.
  intros; iIntros "H".
  rewrite /assert_safe.
  iSpecialize ("H" with "[%]"); first done.
  destruct k as [ | s ctl' | | | |]; try done; try solve [iApply (jsafe_local_step with "H"); constructor].
  - iApply (convergent_controls_jsafe with "H"); simpl; try congruence.
    by inversion 1; constructor.
  - iMod "H" as "[]".
  - iApply (convergent_controls_jsafe with "H"); simpl; try congruence.
    by inversion 1; constructor.
Qed.

Lemma wp_skip: forall E f R, R ⊢ wp E f Sskip R.
Proof.
  intros; split => rho; rewrite /wp.
  iIntros "H % Hk" (???? ->).
  iSpecialize ("Hk" with "H").
  by iApply safe_skip.
Qed.

Lemma wp_set: forall E f i e (R : assert),
  wp_expr e (λ v, assert_of (subst i (liftx v) R)) ⊢ wp E f (Sset i e) R.
Proof.
  intros; split => rho; rewrite /wp.
  iIntros "H % Hk" (???? ->).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_expr.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iDestruct ("H" with "[%] Hm") as (??) "(Hm & H)"; first done.
  iIntros "!>".
  iExists _, _; iSplit.
  { iPureIntro; constructor; eauto. }
  iFrame.
  iNext.
  iApply safe_skip; iApply "Hk".
  rewrite /subst /env_set /construct_rho /= expr_lemmas.map_ptree_rel //.
Qed.

Lemma wp_store: forall E f e1 e2 R,
  wp_lvalue e1 (λ v1, ∃ sh, ⌜writable0_share sh⌝ ∧ ⎡mapsto_ sh (typeof e1) v1⎤ ∗
    wp_expr (Ecast e2 (typeof e1)) (λ v2,
      ⌜Cop2.tc_val' (typeof e1) v2⌝ ∧ (⎡mapsto sh (typeof e1) v1 v2⎤ ={E}=∗ R)))
  ⊢ wp E f (Sassign e1 e2) R.
Proof.
  intros; split => rho; rewrite /wp.
  iIntros "H % Hk" (???? ->).
  iApply jsafe_step.
  rewrite /jstep_ex /wp_lvalue /wp_expr.
  iIntros (?) "(Hm & Ho)".
  monPred.unseal.
  iDestruct ("H" with "[%] Hm") as (b o ?) "(Hm & H)"; first done.
  iDestruct "H" as (sh ?) "(Hp & H)".
  iDestruct ("H" with "[%] Hm") as (? He2) "(Hm & % & H)"; first done.
  iDestruct (mapsto_pure_facts with "Hp") as %((? & ?) & ?).
  iDestruct (mapsto_can_store with "[$Hm Hp]") as %(? & ?); [done.. |].
  iMod (mapsto_store with "[$Hm $Hp]") as "(Hm & Hp)"; [done.. |].
  iMod ("H" with "[%] Hp"); first done.
  iIntros "!>".
  specialize (He2 _ _ _ eq_refl); inv He2.
  iExists _, _; iSplit.
  { iPureIntro; econstructor; eauto.
    econstructor; eauto. }
  iFrame.
  iNext.
  iApply safe_skip; iApply "Hk"; done.
  { inv H5. }
Qed.

Lemma wp_loop: forall E f s1 s2 R,
  ▷ wp E f s1 (▷ wp E f s2 (wp E f (Sloop s1 s2) R)) ⊢ wp E f (Sloop s1 s2) R.
Proof.
  intros; split => rho; rewrite /wp /=.
  monPred.unseal.
  iIntros "H % Hk" (???? ->).
  iApply jsafe_local_step.
  { intros; constructor. }
  iNext.
  iApply ("H" with "[Hk]"); last done.
  iIntros "% H" (???? ->).
  iApply jsafe_local_step.
  { intros; constructor; auto. }
  iNext.
  iApply ("H" with "[Hk]"); last done.
  iIntros "% H" (???? ->).
  by iApply ("H" with "Hk").
Qed.

End mpred.

(* adequacy: copied from veric/SequentialClight *)
Require Import VST.veric.external_state.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.semantics.

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
  rewrite /state_interp /juicy_mem.mem_auth /funspec_auth /=; iFrame.
  iSplit; [|done]. iPureIntro. apply juicy_mem.empty_coherent.
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

Lemma wp_adequacy: forall `{!VSTGpreS OK_ty Σ} {Espec : forall `{VSTGS OK_ty Σ}, ext_spec OK_ty} {dryspec : ext_spec OK_ty}
  (Hdry : forall `{!VSTGS OK_ty Σ}, ext_spec_entails Espec dryspec)
  ge m z f s φ ve te,
  (∀ `{HH : invGS_gen HasNoLc Σ}, ⊢ |={⊤}=> ∃ _ : gen_heapGS share address resource Σ, ∃ _ : funspecGS Σ, ∃ _ : externalGS OK_ty Σ,
    let H : VSTGS OK_ty Σ := Build_VSTGS _ _ (HeapGS _ _ _ _) _ in
    local (λ rho, rho = construct_rho (filter_genv ge) ve te) ∧ ⎡state_interp m z⎤ ∗ wp Espec ⊤ f s ⌜φ⌝) →
       (forall n,
        @dry_safeN _ _ _ OK_ty (genv_symb_injective) (cl_core_sem ge) dryspec
            ge n z (State f s Kstop ve te) m) (*∧ φ if it terminates *).
Proof.
  intros.
(*  assert (forall n, @dry_safeN _ _ _ OK_ty (genv_symb_injective) (cl_core_sem ge) dryspec
            ge n z (State f s Kstop ve te) m ∧ φ) as H'; last (split; [eapply H' | apply (H' 0)]; eauto). *)
  (*intros n;*)
  eapply ouPred.pure_soundness, (step_fupdN_soundness_no_lc'(Σ := Σ) _ (S n) O); [apply _..|].
  simpl; intros. apply (embed_emp_valid_inj(PROP2 := monPred environ_index _)). iIntros "_".
  iMod (H Hinv) as (???) "?".
  iStopProof.
  rewrite /wp; split => rho; monPred.unseal.
  iIntros "(% & S & H)".
  iApply step_fupd_intro; first done.
  iNext.
  set (HH := Build_VSTGS _ _ _ _).
  iApply step_fupdN_mono.
  { apply bi.pure_mono, (ext_spec_entails_safe _ (Espec HH)); auto. }
  iApply (adequacy(VSTGS0 := HH)(OK_spec := Espec HH)).
  iFrame.
  iApply "H"; last done.
  iIntros (?) "?". (* should be able to prove φ now *)
  rewrite /assert_safe.
  iIntros.
  (* are we halted? *)
Admitted.
