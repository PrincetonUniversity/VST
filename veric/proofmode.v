From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From compcert.common Require Import Values.
From VST.veric Require Import mpred juicy_base Clight_base Clight_core mapsto_memory_block env lifting_expr lifting.

Notation envs_entails := (envs_entails(PROP := monpred.monPredI _ _)).

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
