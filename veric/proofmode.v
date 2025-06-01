(* adapted from iris_heap_lang/proofmode.v *)
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From compcert.common Require Import Values.
From VST.veric Require Import mpred juicy_base Clight_base Clight_core mapsto_memory_block env tycontext lifting_expr lifting.

Ltac reshape_seq :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ (Ssequence ?s _) ?Q) => iApply wp_seq; reshape_seq
  | _ => idtac
  end.

Lemma tac_wp_expr_eval `{!VSTGS OK_ty Σ} Δ OK_spec ge E f Q e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (wp OK_spec ge E f e' Q) →
  envs_entails Δ (wp OK_spec ge E f e Q).
Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?OK_spec ?ge ?E ?f ?e ?Q) =>
    notypeclasses refine (tac_wp_expr_eval _ _ _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "wp_expr_eval: not a 'wp'"
  end.
Ltac wp_expr_simpl := wp_expr_eval simpl.



Inductive pure_step_n ge : nat -> Clight.statement -> Clight.statement -> Prop :=
| pure_step_0 : forall s, pure_step_n ge O s s
| pure_step_step : forall s1 s2 s3 n (Hstep : forall f k ve te m, step ge (State f s1 k ve te) m (State f s2 k ve te) m)
    (Hsteps : pure_step_n ge n s2 s3), pure_step_n ge (S n) s1 s3.

Definition PureExec ge φ (n : nat) s1 s2 : Prop := φ → pure_step_n ge n s1 s2.

Lemma wp_pure_step_later `{!VSTGS OK_ty Σ} OK_spec ge E f s1 s2 φ n Q :
  PureExec ge φ n s1 s2 →
  φ →
  (bi_laterN(PROP := monpred.monPredI _ _) n (wp OK_spec ge E f s2 Q) ⊢ wp OK_spec ge E f s1 Q).
Proof.
  intros Hexec ?; induction Hexec; [done | | done].
  rewrite /= IHp /wp. (* simpl; rewrite IHp; unfold wp. *)
  iIntros "H" (???) "L Hk".
  rewrite /assert_safe /=.
  do 4 (iApply embed_forall; iIntros (?)).
  iIntros "Hρ %%".
  iApply juicy_extspec.jsafe_local_step.
  { apply Hstep. }
  iSpecialize ("H" with "[//]").
  rewrite !bi.later_wand.
  iSpecialize ("H" with "L Hk").
  iPoseProof (embed_later with "H") as "H".
  iApply ("H" with "[Hρ]"); try done.
  rewrite embed_later; iIntros "!>".
  iApply "Hρ".
Qed.

Lemma tac_wp_pure `{!VSTGS OK_ty Σ} Δ Δ' OK_spec ge E f e1 e2 φ n Q :
  PureExec ge φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (wp OK_spec ge E f e2 Q) →
  envs_entails Δ (wp OK_spec ge E f e1 Q).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ' wp_pure_step_later //.
Qed.

(* We'll probably need another wp_pure lemma for wp_expr. *)

Lemma tac_wp_consti_nofupd `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (Φ (Vint v)) → envs_entails Δ (wp_expr ge E f (Econst_int v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by apply wp_const_int. Qed.
Lemma tac_wp_constf_nofupd `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (Φ (Vfloat v)) → envs_entails Δ (wp_expr ge E f (Econst_float v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by apply wp_const_float. Qed.
Lemma tac_wp_consts_nofupd `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (Φ (Vsingle v)) → envs_entails Δ (wp_expr ge E f (Econst_single v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by apply wp_const_single. Qed.
Lemma tac_wp_constl_nofupd `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (Φ (Vlong v)) → envs_entails Δ (wp_expr ge E f (Econst_long v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by apply wp_const_long. Qed.

Lemma tac_wp_consti `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (|={E}=> Φ (Vint v)) → envs_entails Δ (wp_expr ge E f (Econst_int v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by rewrite wp_const_int_fupd. Qed.
Lemma tac_wp_constf `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (|={E}=> Φ (Vfloat v)) → envs_entails Δ (wp_expr ge E f (Econst_float v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by rewrite wp_const_float_fupd. Qed.
Lemma tac_wp_consts `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (|={E}=> Φ (Vsingle v)) → envs_entails Δ (wp_expr ge E f (Econst_single v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by rewrite wp_const_single_fupd. Qed.
Lemma tac_wp_constl `{!VSTGS OK_ty Σ} Δ ge E f Φ v t :
  envs_entails Δ (|={E}=> Φ (Vlong v)) → envs_entails Δ (wp_expr ge E f (Econst_long v t) Φ).
Proof. rewrite envs_entails_unseal=> ->. by rewrite wp_const_long_fupd. Qed.

Ltac wp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_int _ _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_consti_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_float _ _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_constf_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_single _ _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_consts_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_long _ _) (λ _, fupd ?E _ _ _)) =>
      eapply tac_wp_constl_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_int _ _) (λ _, wp_expr _ ?E _ _ _)) =>
      eapply tac_wp_consti_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_float _ _) (λ _, wp_expr _ ?E _ _ _)) =>
      eapply tac_wp_constf_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_single _ _) (λ _, wp_expr _ ?E _ _ _)) =>
      eapply tac_wp_consts_nofupd
  | |- envs_entails _ (wp_expr _ ?E _ (Econst_long _ _) (λ _, wp_expr _ ?E _ _ _)) =>
      eapply tac_wp_constl_nofupd
  | |- envs_entails _ (wp _ ?E _ (Econst_int _ _) _) =>
      eapply tac_wp_consti
  | |- envs_entails _ (wp _ ?E _ (Econst_float _ _) _) =>
      eapply tac_wp_constf
  | |- envs_entails _ (wp _ ?E _ (Econst_single _ _) _) =>
      eapply tac_wp_consts
  | |- envs_entails _ (wp _ ?E _ (Econst_long _ _) _) =>
      eapply tac_wp_constl
  end.

Definition ob_replace `{!VSTGS OK_ty Σ} (P P' Q : assert) := ▷ (P ∗ (P' -∗ Q)).

Ltac ob_replace_tac :=
  lazymatch goal with
  | |- envs_entails ?Δ (ob_replace ?P ?P' ?Q) =>
      iNext; let i := fresh "i" in evar (i : ident.ident);
        let H := fresh "H" in assert (envs_lookup i Δ = Some (false, P)) as H;
        [subst i; iAssumptionCore || fail "cannot find" P |
         clear H; lazymatch goal with i := ?s |- _ => clear i; iFrame s; iIntros s end]
  | _ => fail "no such ob"
  end.

Ltac wp_finish :=
  try wp_value_head;  (* in case we have reached a value, get rid of the WP *)
  try ob_replace_tac;
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ ?e ?Q) =>
    let e := eval simpl in e in
    unify e efoc;
      eapply (tac_wp_pure _ _ _ _ _ _ e);
      [tc_solve                       (* PureExec *)
      |try fast_done    (* The pure condition for PureExec --
         handles trivial goals *)
      |tc_solve                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ]
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.
Tactic Notation "wp_pure" :=
  wp_pure _.

Ltac wp_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (wp_pure _; [])
        | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
        ].

#[global] Opaque temp.

(* Not sure whether this will work, but we can't have pointer values as literals in
   our program syntax. *)
Lemma tac_wp_load `{!VSTGS OK_ty Σ} Δ Δ' ge E f i e b q v (Q : val → assert) :
  readable_share q →
  v ≠ Vundef →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ (wp_lvalue ge E f e (λ '(bl, o),
    ⌜envs_lookup i Δ' = Some (b, ⎡mapsto q (typeof e) (Vptr bl (Ptrofs.repr o)) v⎤)⌝ ∧ of_envs Δ ∧
    Q v))%I →
  envs_entails Δ (wp_expr ge E f e Q).
Proof.
  rewrite envs_entails_unseal=> ??? Hi.
  rewrite Hi -wp_expr_mapsto.
  apply wp_lvalue_mono.
  intros (?, ?); apply bi.pure_elim_l; intros H.
  iIntros "? !>".
  iExists q, v; iSplit; first done.
  iApply bi.and_mono; [|done..].
  rewrite into_laterN_env_sound /=.
  rewrite embed_later embed_absorbingly; apply bi.later_mono.
  eassert (envs_entails Δ' _) as He; last by rewrite envs_entails_unseal in He.
  by eapply tac_specialize_intuitionistic_helper_done.
Qed.

(* This might be more useful for tactics. *)
Lemma tac_wp_load_temp `{!VSTGS OK_ty Σ} Δ Δ' ge E f i1 i2 x t t' b2 l q v (Q : val → assert) :
  readable_share q →
  v ≠ Vundef →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i1 Δ = Some (false, temp x l) →
  envs_lookup i2 Δ' = Some (b2, ⎡mapsto q t' l v⎤) →
  envs_entails Δ (Q v) →
  envs_entails Δ (wp_expr ge E f (Ederef (Etempvar x t) t') Q).
Proof.
  rewrite envs_entails_unseal=> ??? H1 H2 Hi.
  trans (of_envs Δ ∧ ▷⌜∃ bl o, l = Vptr bl o⌝).
  { apply bi.and_intro; first done.
    rewrite into_laterN_env_sound /=; apply bi.later_mono.
    rewrite envs_lookup_split //.
    iIntros "(H & _)"; iStopProof.
    rewrite bi.intuitionistically_if_elim mapsto_pure_facts embed_pure; apply bi.pure_mono.
    intros (? & ?); destruct l; try done; eauto. }
  iIntros "(? & >(% & % & ->))"; iStopProof.
  rewrite -wp_expr_mapsto -wp_deref -wp_tempvar_local.
  rewrite (envs_lookup_split _ _ _ _ H1) /=.
  apply bi.sep_mono; first done; apply bi.wand_mono; first done.
  iIntros "H"; iExists _, _; iSplit; first done.
  iExists q, v; iSplit; first done.
  iSplit; iStopProof; last done.
  rewrite into_laterN_env_sound /= embed_later embed_absorbingly; apply bi.later_mono.
  eassert (envs_entails Δ' _) as He; last by rewrite envs_entails_unseal in He.
  eapply tac_specialize_intuitionistic_helper_done.
  rewrite Ptrofs.repr_unsigned //.
Qed.

Lemma tac_wp_store `{!VSTGS OK_ty Σ} Δ Δ' OK_spec ge E f i e1 e2 q v Q :
  writable0_share q →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ (wp_expr ge E f (Ecast e2 (typeof e1)) (λ v2,
    ⌜Cop2.tc_val' (typeof e1) v2⌝ ∧ wp_lvalue ge E f e1 (λ '(b, o), let v1 := Vptr b (Ptrofs.repr o) in
    ⌜envs_lookup i Δ' = Some (false, ⎡mapsto q (typeof e1) v1 v⎤)⌝ ∧ of_envs Δ ∧
    match envs_simple_replace i false (Esnoc Enil i ⎡mapsto q (typeof e1) v1 v2⎤) Δ' with
    | Some Δ'' => ⌜envs_entails Δ'' (RA_normal Q)⌝
    | None => False
    end))) →
  envs_entails Δ (wp OK_spec ge E f (Sassign e1 e2) Q).
Proof.
  rewrite envs_entails_unseal=> ?? Hi.
  rewrite Hi -wp_store.
  apply wp_expr_mono.
  intros ?; rewrite -fupd_intro; f_equiv.
  apply wp_lvalue_mono.
  intros (?, ?); apply bi.pure_elim_l; intros H.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | iIntros "(_ & [])" ].
  apply bi.pure_elim_r; intros HQ.
  iIntros "H !>".
  iExists q; iSplit; first done.
  rewrite into_laterN_env_sound envs_simple_replace_sound //; simpl.
  iNext; iDestruct "H" as "(Hold & H)"; iSplitL "Hold".
  { by iApply mapsto_mapsto_. }
  iIntros "Hnew !>"; iApply HQ; iApply "H"; iFrame.
Qed.

(* simpler version here too? or will wp_pures for expr make that unnecessary? *)

Lemma tac_wp_temp `{!VSTGS OK_ty Σ} Δ ge E f i x v t Q :
  envs_lookup i Δ = Some (false, temp x v) →
  envs_entails Δ (Q v) →
  envs_entails Δ (wp_expr ge E f (Etempvar x t) Q).
Proof.
  rewrite envs_entails_unseal=> ? Hi.
  rewrite -wp_tempvar_local.
  rewrite envs_lookup_split //; simpl.
  by rewrite Hi.
Qed.

(*Lemma tac_wp_set `{!VSTGS OK_ty Σ} Δ Δ' OK_spec ge E f i x e v0 Q :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, temp x v0) →
  envs_entails Δ (wp_expr ge E f e (λ v,
    of_envs Δ ∧
    match envs_simple_replace i false (Esnoc Enil i (temp x v)) Δ' with
    | Some Δ'' => ⌜envs_entails Δ'' (RA_normal Q)⌝
    | None => False
    end)) →
  envs_entails Δ (wp OK_spec ge E f (Sset x e) Q).
Proof.
  rewrite envs_entails_unseal=> ?? Hi.
  rewrite Hi -wp_set.
  apply wp_expr_mono.
  intros ?.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | iIntros "(_ & [])" ].
  apply bi.pure_elim_r; intros HQ.
  rewrite into_laterN_env_sound envs_simple_replace_sound //; simpl.
  iIntros "($ & H) !> !> ?".
  iApply HQ; iApply "H"; iFrame.
Qed.*)

Lemma tac_wp_set `{!VSTGS OK_ty Σ} Δ OK_spec ge E f x e v0 Q :
  envs_entails Δ (wp_expr ge E f e (λ v,
    ob_replace (temp x v0) (temp x v) (RA_normal Q))) →
  envs_entails Δ (wp OK_spec ge E f (Sset x e) Q).
Proof.
  rewrite envs_entails_unseal=> Hi.
  rewrite Hi -wp_set.
  apply wp_expr_mono.
  by iIntros (?) "($ & $)".
Qed.

Ltac wp_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (wp _ _ _ _ _ _) =>
            tac_suc H
     | _ => fail 1 "wp_apply: not a 'wp'"
     end)
  |tac_fail ltac:(fun _ => wp_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "wp_apply: cannot apply" lem ":" P ].

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => fail).
Tactic Notation "wp_smart_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => wp_pure _; []; cont ()).

Tactic Notation "wp_apply" open_constr(lem) "as" constr(pat) :=
  wp_apply lem; last iIntros pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) ")" constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 ) pat.
Tactic Notation "wp_apply" open_constr(lem) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) simple_intropattern(x9) simple_intropattern(x10) ")"
    constr(pat) :=
  wp_apply lem; last iIntros ( x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) pat.

(*Tactic Notation "wp_load" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, ⎡mapsto _ _ ?l _⎤) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ ?e ?Q) =>
    first
      [eapply tac_wp_load
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [try fast_done
    |try fast_done
    |tc_solve
    |solve_pointsto ()
    |wp_finish]
  | _ => fail "wp_load: not a 'wp'"
  end.*)

(*Tactic Notation "wp_store" :=
  let solve_pointsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_seq; eapply tac_wp_store
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [tc_solve
    |solve_pointsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.*)

Tactic Notation "wp_temp" :=
  let solve_temp _ :=
    let i := match goal with |- _ = Some (_, temp ?i _) => i end in
    iAssumptionCore || fail "wp_store: cannot find temp" i in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp_expr _ ?E _ ?e ?Q) =>
    first
      [eapply tac_wp_temp
      |fail 1 "wp_temp: cannot find 'Etempvar' in" e];
    [solve_temp ()
    |pm_reduce; wp_finish]
  | _ => fail "wp_temp: not a 'wp'"
  end.

Tactic Notation "wp_set" :=
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?E _ ?e ?Q) =>
    first
      [reshape_seq; eapply tac_wp_set
      |fail 1 "wp_set: cannot find 'Sset' in" e];
    [pm_reduce; wp_finish]
  | _ => fail "wp_set: not a 'wp'"
  end.
