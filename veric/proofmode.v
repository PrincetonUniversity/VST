From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
Require Import VST.veric.Clight_core.
Require Import VST.veric.lifting.

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

Definition PureExec ge φ (n : nat) s1 s2 := φ →
  forall f k ve te m, step ge (State f s1 k ve te) m (State f s2 k ve te) m.

Lemma tac_wp_pure `{!VSTGS OK_ty Σ} Δ Δ' OK_spec ge E f e1 e2 φ n Q :
  PureExec ge φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (wp OK_spec ge E f e2 Q) →
  envs_entails Δ (wp OK_spec ge E f e1 Q).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  rewrite HΔ' -lifting.wp_pure_step_later //.
  iIntros "Hwp !> _" => //.
Qed.

Lemma tac_wp_load Δ Δ' s E i K b l q v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (b, l ↦{q} v)%I →
  envs_entails Δ' (WP fill K (Val v) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Load (LitV l)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ?? Hi.
  rewrite -wp_bind. eapply wand_apply; first by apply wand_entails, wp_load.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  apply later_mono.
  destruct b; simpl.
  * iIntros "[#$ He]". iIntros "_". iApply Hi. iApply "He". iFrame "#".
  * by apply sep_mono_r, wand_mono.
Qed.
