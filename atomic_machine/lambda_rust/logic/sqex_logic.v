(**
  The sequential program logic of [sq_logic.v, lifted with a semantics for
  the atomic operations as external function calls.

  [EXWP] is the weakest precondition of [sq_lang] with one extra case: [e] is
  at an atomic operation and takes an [ext_step].  Unlike Iris's [WP], it has
  no later credits: each step takes exactly one later.  A [WP] proof may spend
  the credits its steps receive, so a [WP] is not in general an [EXWP]; the
  lifting lemmas are [exwp_lift_step] for a step of [sq_lang] and
  [exwp_extcall] for an atomic operation.

  For lambda-Rust, [sc_extcall] instantiates [extcall_sems] with the
  sequentially consistent semantics of the atomic machine's SC rules, and
  [sqex_step] is the resulting semantics of a thread pool: the two cases of
  [EXWP], interleaved.  The rules for the SC operations under this instance
  close the file, with the statements of lambda-Rust's [lifting.v]
  ([exwp_read_sc], [exwp_write_sc], and the [exwp_cas_*] family);
  [sqex_adequacy.v] proves the logic adequate.
*)

From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.logic.sq_logic.
(* only for [redex_shape] and [fill_redex_unique] *)
Require Import VST.atomic_machine.lambda_rust.equivalence.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".

(** * External call semantics *)

(** The semantics of the atomic operations of [L], axiomatized:
    [extcall_sems op m ov m'] means that [op], performed on the memory [m],
    can return [ov] and leave the memory [m']. *)
Class ExtCallSems `(L : @sqlang Loc Val LocEqDec LocCountable Mem Layout) :=
  extcall_sems : @atomic_op Loc Val Layout -> Mem -> option Val -> Mem -> Prop.

Section ext_step.
  Context `{L : !@sqlang Loc Val LocEqDec LocCountable Mem Layout, !ExtCallSems L}.

  Local Notation C := sqlang_thrd_st.

  (** A thread at an atomic operation performs it according to
      [extcall_sems], and continues with the returned value. *)
  Inductive ext_step : C -> Mem -> C -> Mem -> Prop :=
  | ExtStep c op K m ov m' c' :
      sqlang_at_external c op K ->
      extcall_sems op m ov m' ->
      sqlang_after_external c ov c' ->
      ext_step c m c' m'.

  Definition ext_reducible (c : C) (m : Mem) : Prop :=
    exists c' m', ext_step c m c' m'.
End ext_step.

(** * External steps of lambda-Rust *)

Lemma lr_head_external_not_val e op k : lr_head_external e op k -> to_val e = None.
Proof. by destruct 1. Qed.

Lemma lr_head_external_redex_shape e op k : lr_head_external e op k -> redex_shape e.
Proof. intros Hh Ki e1 ->. destruct Ki; inversion Hh; subst; rewrite ?to_of_val; eauto. Qed.

Lemma lr_external_not_val e op k : lr_external e op k -> to_val e = None.
Proof. destruct 1 as [K e op k Hh]. apply fill_not_val. by eapply lr_head_external_not_val. Qed.

(** A thread is at no more than one SC operation. *)
Lemma lr_external_det e op1 k1 op2 k2 :
  lr_external e op1 k1 -> lr_external e op2 k2 ->
  op2 = op1 /\ forall ov, k2 ov = k1 ov.
Proof.
  destruct 1 as [K1 e1 ? k1' Hh1]. inversion 1 as [K2 e2 ? k2' Hh2 Heq]; subst.
  destruct (fill_redex_unique K2 K1 e2 e1) as [-> ->];
    eauto using lr_head_external_redex_shape, lr_head_external_not_val.
  destruct Hh1; inversion Hh2; split; congruence.
Qed.

Lemma lr_external_fill K e op k :
  lr_external e op k ->
  exists k', lr_external (fill K e) op k' /\ forall ov, k' ov = fill K (k ov).
Proof.
  destruct 1 as [K' e op k Hh]. exists (fun ov => fill (K' ++ K) (k ov)). split.
  - rewrite -fill_app. by constructor.
  - intros ov. by rewrite fill_app.
Qed.

Lemma lr_after_external_fill K e ov e' :
  lr_after_external e ov e' -> lr_after_external (fill K e) ov (fill K e').
Proof.
  destruct 1 as [e op k ov Hext].
  destruct (lr_external_fill K _ _ _ Hext) as (k' & Hext' & Hk').
  rewrite -Hk'. by econstructor.
Qed.

Section lr_ext_step.
  Context `{!ExtCallSems lr_language}.

  (** The external step of a thread at a known SC operation. *)
  Lemma lr_ext_step_inv e op k m e' m' :
    lr_external e op k -> ext_step e m e' m' ->
    exists ov, extcall_sems op m ov m' /\ e' = k ov.
  Proof.
    intros Hext. destruct 1 as [? op1 k1 ? ov ? ? Hext1 Hsem Hafter].
    destruct Hafter as [? op2 k2 ? Hext2].
    destruct (lr_external_det _ _ _ _ _ Hext Hext1) as [-> _].
    destruct (lr_external_det _ _ _ _ _ Hext Hext2) as [_ Hk].
    eauto.
  Qed.

  Lemma lr_ext_step_fill K e m e' m' :
    ext_step e m e' m' -> ext_step (fill K e) m (fill K e') m'.
  Proof.
    destruct 1 as [? op k ? ov ? ? Hext Hsem Hafter].
    destruct (lr_external_fill K _ _ _ Hext) as (k' & Hext' & _).
    econstructor; [ exact Hext' | exact Hsem | by apply lr_after_external_fill ].
  Qed.

  Lemma lr_ext_step_fill_inv K e op k m e2 m2 :
    lr_external e op k -> ext_step (fill K e) m e2 m2 ->
    exists e2', e2 = fill K e2' /\ ext_step e m e2' m2.
  Proof.
    intros Hext Hstep. destruct (lr_external_fill K _ _ _ Hext) as (k' & Hext' & Hk').
    destruct (lr_ext_step_inv _ _ _ _ _ _ Hext' Hstep) as (ov & Hsem & ->).
    exists (k ov). split; [ done | ].
    econstructor; [ exact Hext | exact Hsem | by econstructor ].
  Qed.

  Lemma lr_ext_reducible_external e m :
    ext_reducible e m -> exists op k, lr_external e op k.
  Proof. intros (e' & m' & Hstep). destruct Hstep. eauto. Qed.
End lr_ext_step.

(** * The sequentially consistent external call semantics

    The semantics the atomic machine gives the atomic operations ([SC_Read],
    [SC_Write], [SC_Cas_Suc], [SC_Cas_Fail] of [at_step]), with the machine
    stripped away: an SC access is a load or store on the memory alone, with
    no thread pool and no reader/writer map.  (The machine's rules are only
    a syntactic template here; this does not depend on [at_step].) *)

Local Notation lr_atomic_op := (@atomic_op loc val lr_layout).

(* FIXME move this to adequacy.v, add spawn case := noop *)
Inductive sc_extcall : lr_atomic_op -> lr_mem -> option val -> lr_mem -> Prop :=
| ScLoad ly l v m :
    load m l ly = Some v ->
    sc_extcall (ALoad ly l) m (Some v) m
| ScStore ly l v m m' :
    store m l ly v = Some m' ->
    sc_extcall (AStore ly l v) m None m'
| ScCasSuc ly l v_exp v_new v_cur m m' :
    load m l ly = Some v_cur ->
    lr_val_eq m v_cur v_exp ->
    store m l ly v_new = Some m' ->
    sc_extcall (ACAS ly l v_exp v_new) m (Some (LitV (lit_of_bool true))) m'
| ScCasFail ly l v_exp v_new v_cur m :
    load m l ly = Some v_cur ->
    lr_val_neq m v_cur v_exp ->
    sc_extcall (ACAS ly l v_exp v_new) m (Some (LitV (lit_of_bool false))) m.

Global Instance sc_extcall_sems : ExtCallSems lr_language := sc_extcall.

(** The lambda-Rust store succeeds exactly on allocated locations. *)
Lemma lr_store_Some (m : lr_mem) l (ly : lr_layout) v m' :
  store m l ly v = Some m' -> is_Some (m !! l) /\ m' = <[l := v]> m.
Proof. simpl. destruct (m !! l) eqn:Hl; [ | done ]. intros [= <-]. eauto. Qed.

(** * Sequential steps and atomic operations exclude each other *)

Local Lemma lr_head_step_not_val e m T e' m' :
  lr_head_step e m T e' m' -> to_val e = None.
Proof. by destruct 1. Qed.

Local Lemma lr_head_step_redex_shape e m T e' m' :
  lr_head_step e m T e' m' -> redex_shape e.
Proof. intros Hh Ki e1 ->. by eapply (sq_base_ctx_step_val _ _ m T e' m' []), SqHeadStep. Qed.

Lemma lr_step_external_excl e m T e' m' op K :
  lr_step e m T e' m' -> lr_external e op K -> False.
Proof.
  destruct 1 as [K1 e1 m1 T1 e2 m2 Hh].
  inversion 1 as [K2 e3 op' k Hhe Heq]; subst.
  destruct (fill_redex_unique K2 K1 e3 e1) as [_ ->];
    eauto using lr_head_step_redex_shape, lr_head_external_redex_shape,
      lr_head_step_not_val, lr_head_external_not_val.
  destruct Hh; inversion Hhe.
Qed.

(** A sequential step is a primitive step of [sq_lang], observing its
    events; [sq_reducible] of [sq_adequacy.v] is the converse. *)
Lemma lr_step_prim_step e m T e' m' :
  lr_step e m T e' m' -> @language.prim_step sq_lang e m T e' m' [].
Proof.
  destruct 1 as [K e1 m1 T1 e2 m2 Hh].
  apply (Ectx_step' (Λ := sq_ectx_lang) K). by apply SqHeadStep.
Qed.

(** * The lifted sequential semantics

    A pool of threads, each taking sequential steps and atomic operations:
    the two cases of [EXWP].  This is the machine with [Core_Try] and
    [Core_Commit] fused into one step, so reservations never stay pending. *)

(* FIXME remove the thread pool
  ext_step should be parametrized, in a different layer  *)
Inductive sqex_step : list sq_expr * lr_mem -> list sq_expr * lr_mem -> Prop :=
| SqexSeqStep i tp m e T e' m' :
    tp !! i = Some e ->
    lr_step e m T e' m' ->
    sqex_step (tp, m) (<[i := e']> tp, m')
| SqexExtStep i tp m e e' m' :
    tp !! i = Some e ->
    ext_step (L := lr_language) e m e' m' ->
    sqex_step (tp, m) (<[i := e']> tp, m').

Definition sqex_not_stuck (e : sq_expr) (m : lr_mem) : Prop :=
  is_Some (to_val e) \/ reducible (Λ := sq_lang) e m \/ ext_reducible (L := lr_language) e m.


(* WP is on this instance *)
Definition sq_lang_instance {ExtCallSems} := Language sqex_step.

(** * The weakest precondition. 
  Iris's weakest_pre plus the extcall case. *)
Definition exwp_pre `{!irisGS_gen hlc sq_lang Σ, !ExtCallSems lr_language}
    (exwp : coPset -d> sq_expr -d> (sq_val -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> sq_expr -d> (sq_val -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ns κ κs nt,
     state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
       (* a step of [sq_lang] *)
       (⌜reducible (Λ := sq_lang) e1 σ1⌝ ∗
         ∀ e2 σ2 efs, ⌜@language.prim_step sq_lang e1 σ1 κ e2 σ2 efs⌝ ={∅}▷=∗ |={∅,E}=>
           state_interp σ2 (S ns) κs (length efs + nt) ∗
           exwp E e2 Φ ∗
           (* WP for forked threads. Not used for lambda-rust since thread spawn
           will be in external calls. Maybe should remove this, since sequential
           semantics should be sequential anyways. *)
           [∗ list] i ↦ ef ∈ efs, exwp ⊤ ef fork_post) ∨
       (* an atomic operation, emits no events and spawn no threads.
          FIXME spawn should also be an ext_call. *)
       (⌜ext_reducible (L := lr_language) e1 σ1⌝ ∗
         ∀ e2 σ2, ⌜ext_step (L := lr_language) e1 σ1 e2 σ2⌝ ={∅}▷=∗ |={∅,E}=>
           state_interp σ2 (S ns) (κ ++ κs) nt ∗
           exwp E e2 Φ)
  end%I.

Local Instance exwp_pre_contractive `{!irisGS_gen hlc sq_lang Σ, !ExtCallSems lr_language} :
  Contractive exwp_pre.
Proof.
  rewrite /exwp_pre /= => n exwp exwp' Hwp E e1 Φ.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Local Definition exwp_def `{!irisGS_gen hlc sq_lang Σ, !ExtCallSems lr_language} :
  coPset -> sq_expr -> (sq_val -> iProp Σ) -> iProp Σ := fixpoint exwp_pre.
Local Definition exwp_aux : seal (@exwp_def). Proof. by eexists. Qed.
Definition exwp := exwp_aux.(unseal).
Global Arguments exwp {hlc Σ _ _} E e%_E Φ%_I.
Local Lemma exwp_unseal `{!irisGS_gen hlc sq_lang Σ, !ExtCallSems lr_language} :
  exwp = @exwp_def hlc Σ _ _.
Proof. rewrite -exwp_aux.(seal_eq) //. Qed.

Notation "'EXWP' e @ E {{ Φ } }" := (exwp E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'EXWP' e {{ Φ } }" := (exwp ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'EXWP' e @ E {{ v , Q } }" := (exwp E e%E (λ v, Q))
  (at level 20, e, Q at level 200, v at level 200 as pattern,
   format "'[hv' 'EXWP'  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'EXWP' e {{ v , Q } }" := (exwp ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200, v at level 200 as pattern,
   format "'[hv' 'EXWP'  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Section exwp.
Context `{!irisGS_gen hlc sq_lang Σ, !ExtCallSems lr_language}.
Implicit Types P : iProp Σ.
Implicit Types Φ Ψ : sq_val -> iProp Σ.
Implicit Types v : sq_val.
Implicit Types e : sq_expr.

Lemma exwp_unfold E e Φ : EXWP e @ E {{ Φ }} ⊣⊢ exwp_pre exwp E e Φ.
Proof. rewrite exwp_unseal. apply (fixpoint_unfold exwp_pre). Qed.

Global Instance exwp_ne E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (exwp (hlc := hlc) (Σ := Σ) E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !exwp_unfold /exwp_pre /=.
  (* [f_equiv] would turn the recursive occurrences into [Φ = Ψ]. *)
  repeat (f_contractive || match goal with
                           | |- exwp _ _ _ ≡{_}≡ exwp _ _ _ => fail 1
                           | _ => f_equiv
                           end).
  all: apply IH; [ done | ]; intros v; eapply dist_lt; [ apply HΦ | done ].
Qed.

Global Instance exwp_proper E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (exwp (hlc := hlc) (Σ := Σ) E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply exwp_ne=>v; apply equiv_dist.
Qed.

Lemma exwp_value_fupd' E Φ v : EXWP of_val v @ E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. rewrite exwp_unfold /exwp_pre to_of_val. auto. Qed.

Lemma exwp_strong_mono E1 E2 e Φ Ψ :
  E1 ⊆ E2 ->
  EXWP e @ E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ EXWP e @ E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !exwp_unfold /exwp_pre /=.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 ns κ κs nt) "Hσ".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "[[% H] | [% H]]"; iModIntro; [ iLeft | iRight ].
  - iSplit; [ done | ]. iIntros (e2 σ2 efs Hstep).
    iMod ("H" with "[//]") as "H". iIntros "!> !>". iMod "H". iModIntro.
    iMod "H" as "($ & H & Hefs)". iMod "Hclose" as "_". iModIntro. iSplitR "Hefs".
    + iApply ("IH" with "[//] H HΦ").
    + iApply (big_sepL_impl with "Hefs"); iIntros "!>" (k ef _).
      iIntros "H". iApply ("IH" with "[] H"); auto.
  - iSplit; [ done | ]. iIntros (e2 σ2 Hstep).
    iMod ("H" with "[//]") as "H". iIntros "!> !>". iMod "H". iModIntro.
    iMod "H" as "($ & H)". iMod "Hclose" as "_". iModIntro.
    iApply ("IH" with "[//] H HΦ").
Qed.

Lemma fupd_exwp E e Φ : (|={E}=> EXWP e @ E {{ Φ }}) ⊢ EXWP e @ E {{ Φ }}.
Proof.
  rewrite exwp_unfold /exwp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 ns κ κs nt) "Hσ1". iMod "H". by iApply "H".
Qed.

Lemma exwp_fupd E e Φ : EXWP e @ E {{ v, |={E}=> Φ v }} ⊢ EXWP e @ E {{ Φ }}.
Proof. iIntros "H". iApply (exwp_strong_mono E with "H"); auto. Qed.

Lemma exwp_mono E e Φ Ψ :
  (∀ v, Φ v ⊢ Ψ v) -> EXWP e @ E {{ Φ }} ⊢ EXWP e @ E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (exwp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.

Lemma exwp_mask_mono E1 E2 e Φ :
  E1 ⊆ E2 -> EXWP e @ E1 {{ Φ }} ⊢ EXWP e @ E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (exwp_strong_mono with "H"); auto. Qed.

Lemma exwp_wand E e Φ Ψ :
  EXWP e @ E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ EXWP e @ E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (exwp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.

Lemma exwp_value_fupd E Φ e v : IntoVal e v -> EXWP e @ E {{ Φ }} ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply exwp_value_fupd'. Qed.

Lemma exwp_value E Φ e v : IntoVal e v -> Φ v ⊢ EXWP e @ E {{ Φ }}.
Proof. intros <-. rewrite exwp_value_fupd'. auto. Qed.

Lemma exwp_bind (K : list sq_ectx_item) E e Φ :
  EXWP e @ E {{ v, EXWP fill K (of_val v) @ E {{ Φ }} }} ⊢ EXWP fill K e @ E {{ Φ }}.
Proof.
  pose proof (ectx_lang_ctx (Λ := sq_ectx_lang) K : LanguageCtx (Λ := sq_lang) (fill K)).
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite exwp_unfold /exwp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_exwp. }
  assert (to_val (fill K e) = None) as HK
    by exact (ectxi_language.fill_not_val (Λ := sq_ectxi_lang) K e He).
  rewrite exwp_unfold /exwp_pre HK.
  iIntros (σ1 ns κ κs nt) "Hσ". iMod ("H" with "[$]") as "[[% H] | [%Hred H]]"; iModIntro.
  - iLeft. iSplit; [ eauto using reducible_fill | ].
    iIntros (e2 σ2 efs Hstep).
    destruct (fill_step_inv (K := fill K) e σ1 κ e2 σ2 efs) as (e2' & -> & ?); [ done.. | ].
    iMod ("H" $! e2' σ2 efs with "[//]") as "H". iIntros "!> !>".
    iMod "H". iModIntro. iMod "H" as "($ & H & $)". iModIntro. by iApply "IH".
  - iRight. destruct (lr_ext_reducible_external e σ1 Hred) as (op & k & Hext).
    iSplit.
    { iPureIntro. destruct Hred as (e' & σ' & Hstep).
      exists (fill K e'), σ'. by apply lr_ext_step_fill. }
    iIntros (e2 σ2 Hstep).
    destruct (lr_ext_step_fill_inv K e op k σ1 e2 σ2) as (e2' & -> & ?); [ done.. | ].
    iMod ("H" $! e2' σ2 with "[//]") as "H". iIntros "!> !>".
    iMod "H". iModIntro. iMod "H" as "($ & H)". iModIntro. by iApply "IH".
Qed.

(** * Lifting *)

Lemma exwp_lift_step E Φ e1 :
  to_val e1 = None ->
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
    ⌜reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅}=∗ ▷ |={∅,E}=>
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      EXWP e2 @ E {{ Φ }} ∗
      [∗ list] ef ∈ efs, EXWP ef @ ⊤ {{ fork_post }})
  ⊢ EXWP e1 @ E {{ Φ }}.
Proof.
  iIntros (He) "H". rewrite exwp_unfold /exwp_pre He.
  iIntros (σ1 ns κ κs nt) "Hσ". iMod ("H" with "Hσ") as "[% H]". iModIntro. iLeft.
  iSplit; [ done | ]. iIntros (e2 σ2 efs Hstep).
  iMod ("H" with "[//]") as "H". by iIntros "!> !> !>".
Qed.

Lemma exwp_lift_ext_step E Φ e1 :
  to_val e1 = None ->
  (∀ σ1 ns κs nt, state_interp σ1 ns κs nt ={E,∅}=∗
    ⌜ext_reducible e1 σ1⌝ ∗
    ∀ e2 σ2, ⌜ext_step e1 σ1 e2 σ2⌝ ={∅}=∗ ▷ |={∅,E}=>
      state_interp σ2 (S ns) κs nt ∗ EXWP e2 @ E {{ Φ }})
  ⊢ EXWP e1 @ E {{ Φ }}.
Proof.
  iIntros (He) "H". rewrite exwp_unfold /exwp_pre He.
  iIntros (σ1 ns κ κs nt) "Hσ". iMod ("H" with "Hσ") as "[% H]". iModIntro. iRight.
  iSplit; [ done | ]. iIntros (e2 σ2 Hstep).
  iMod ("H" with "[//]") as "H". by iIntros "!> !> !>".
Qed.

(** An SC operation [op]: for every way [extcall_sems] can perform it, the
    thread continues as [k] applied to the returned value. *)
Lemma exwp_extcall E Φ e op k :
  lr_external e op k ->
  (∀ σ1 ns κs nt, state_interp σ1 ns κs nt ={E,∅}=∗
    ⌜∃ ov σ2, extcall_sems op σ1 ov σ2⌝ ∗
    ∀ ov σ2, ⌜extcall_sems op σ1 ov σ2⌝ ={∅}=∗ ▷ |={∅,E}=>
      state_interp σ2 (S ns) κs nt ∗ EXWP k ov @ E {{ Φ }})
  ⊢ EXWP e @ E {{ Φ }}.
Proof.
  iIntros (Hext) "H". iApply exwp_lift_ext_step; [ exact (lr_external_not_val _ _ _ Hext) | ].
  iIntros (σ1 ns κs nt) "Hσ". iMod ("H" with "Hσ") as "[%Hred H]". iModIntro. iSplit.
  { iPureIntro. destruct Hred as (ov & σ2 & Hsem).
    exists (k ov), σ2. econstructor; [ exact Hext | exact Hsem | by econstructor ]. }
  iIntros (e2 σ2 Hstep).
  destruct (lr_ext_step_inv _ _ _ _ _ _ Hext Hstep) as (ov & Hsem & ->).
  by iApply "H".
Qed.

End exwp.

(** * Texan triples for [EXWP]

    As [sq_logic.v] gives [sq_lang] its own carrier alias so that its
    canonical structures do not take over lambda-Rust's, the carrier gets
    one more alias here: on an [sqex_expr], [WP] (and with it Iris's triple
    notation) is [EXWP], and [WP] on an [sq_expr] remains the one of
    [sq_logic.v]. *)

Definition sqex_expr : Type := sq_expr.
(* Keep typeclass resolution from unfolding the alias: [Wp] instance search
   must key on it, so that [sq_expr]'s [WP] stays with [sq_lang]. *)
Global Typeclasses Opaque sqex_expr.

Global Instance exwp_wp `{!irisGS_gen hlc sq_lang Σ, !ExtCallSems lr_language} :
  Wp (iProp Σ) sqex_expr sq_val stuckness := fun _ : stuckness => exwp.

Lemma exwp_as_wp `{!irisGS_gen hlc sq_lang Σ, !ExtCallSems lr_language}
    s E (e : sqex_expr) Φ :
  (WP e @ s; E {{ Φ }})%I = (EXWP e @ E {{ Φ }})%I.
Proof. reflexivity. Qed.

(** * Hoare rules for the atomic operations

    The rules of the SC operations under [sc_extcall], with the statements
    of lambda-Rust's [lifting.v] ([wp_read_sc], [wp_write_sc], and the
    [wp_cas_*] family): the same heap resources as the non-atomic rules of
    [sq_logic.v], but the access is one step. *)

Section sc_rules.
Context `{!lrSqGS Σ}.
Implicit Types Φ : sq_val -> iProp Σ.

(** Two allocated locations compare as equal only if they are equal. *)
Local Lemma sq_lit_eq_alloc (m : lr_mem) l1 l2 v1 v2 :
  m !! l1 = Some v1 -> m !! l2 = Some v2 ->
  sq_mem.lit_eq m (LitLoc l1) (LitLoc l2) -> l1 = l2.
Proof.
  unfold lr_mem. intros H1 H2 Heq. inversion Heq; subst; congruence.
Qed.

Lemma exwp_read_sc E l q v :
  {{{ ▷ l ↦{q} v }}} (Read ScOrd (Lit $ LitLoc l) : sqex_expr) @ E
  {{{ RET (v : sq_val); l ↦{q} v }}}.
Proof.
  iIntros (Φ) "Hl HΦ". rewrite exwp_as_wp.
  iApply (exwp_extcall _ _ _ _ _ (LREctxExternal [] _ _ _ (LRReadScE l))).
  iIntros (σ1 ns κs nt) "Hσ". iMod "Hl".
  iDestruct (heap_read with "Hσ Hl") as %[n Hl].
  apply lookup_sq_heap_Some in Hl as [_ Hl].
  iApply fupd_mask_intro; [ set_solver | ]. iIntros "Hclose". iSplit.
  { iPureIntro. exists (Some v), σ1. by apply ScLoad. }
  iIntros (ov σ2 Hsem). inversion Hsem; simplify_eq/=.
  iModIntro. iNext. iMod "Hclose" as "_". iModIntro.
  iSplitL "Hσ"; [ iExact "Hσ" | ].
  iApply (exwp_value _ _ _ v eq_refl). by iApply "HΦ".
Qed.

Lemma exwp_write_sc E l e v v' :
  IntoVal e v ->
  {{{ ▷ l ↦ v' }}} (Write ScOrd (Lit $ LitLoc l) e : sqex_expr) @ E
  {{{ RET (LitV LitPoison : sq_val); l ↦ v }}}.
Proof.
  iIntros (<- Φ) "Hl HΦ". rewrite exwp_as_wp.
  iApply (exwp_extcall _ _ _ _ _
    (LREctxExternal [] _ _ _ (LRWriteScE l (of_val v) v (to_of_val v)))).
  iIntros (σ1 ns κs nt) "Hσ". iMod "Hl".
  iDestruct (heap_read_1 with "Hσ Hl") as %Hl.
  apply lookup_sq_heap_Some in Hl as [_ Hl].
  iMod (heap_write _ _ _ v with "Hσ Hl") as "[Hσ Hl]".
  iApply fupd_mask_intro; [ set_solver | ]. iIntros "Hclose". iSplit.
  { iPureIntro. exists None, (<[l := v]> σ1). apply ScStore. by rewrite /= Hl. }
  iIntros (ov σ2 Hsem). inversion Hsem; simplify_eq.
  match goal with H : store _ _ _ _ = Some _ |- _ =>
    destruct (lr_store_Some _ _ _ _ _ H) as (_ & ->) end.
  iModIntro. iNext. iMod "Hclose" as "_". iModIntro.
  iSplitL "Hσ"; [ by rewrite /= sq_heap_insert | ].
  iApply (exwp_value _ _ _ (LitV LitPoison) eq_refl). by iApply "HΦ".
Qed.

Lemma exwp_cas_int_fail E l q z1 e2 lit2 zl :
  IntoVal e2 (LitV lit2) -> z1 ≠ zl ->
  {{{ ▷ l ↦{q} LitV (LitInt zl) }}}
    (CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 : sqex_expr) @ E
  {{{ RET (LitV $ LitInt 0 : sq_val); l ↦{q} LitV (LitInt zl) }}}.
Proof.
  iIntros (<- Hne Φ) "Hl HΦ". rewrite exwp_as_wp.
  iApply (exwp_extcall _ _ _ _ _
    (LREctxExternal [] _ _ _
      (LRCasE l (Lit (LitInt z1)) (LitInt z1) (of_val (LitV lit2)) lit2
         eq_refl (to_of_val _)))).
  iIntros (σ1 ns κs nt) "Hσ". iMod "Hl".
  iDestruct (heap_read with "Hσ Hl") as %[n Hl].
  apply lookup_sq_heap_Some in Hl as [_ Hl].
  iApply fupd_mask_intro; [ set_solver | ]. iIntros "Hclose". iSplit.
  { iPureIntro. exists (Some (LitV (lit_of_bool false))), σ1.
    eapply ScCasFail; [ exact Hl | ]. simpl. by apply IntNeq. }
  iIntros (ov σ2 Hsem).
  inversion Hsem; simplify_eq;
    match goal with H : load _ _ _ = Some _ |- _ => simpl in H; rewrite Hl in H end;
    simplify_eq.
  { (* success is impossible: the compared integers differ *)
    match goal with H : lr_val_eq _ _ _ |- _ => simpl in H; inversion H; congruence end. }
  iModIntro. iNext. iMod "Hclose" as "_". iModIntro.
  iSplitL "Hσ"; [ iExact "Hσ" | ].
  iApply (exwp_value _ _ _ (LitV (lit_of_bool false)) eq_refl). by iApply "HΦ".
Qed.

Lemma exwp_cas_suc E l lit1 e2 lit2 :
  IntoVal e2 (LitV lit2) -> lit1 ≠ LitPoison ->
  {{{ ▷ l ↦ LitV lit1 }}}
    (CAS (Lit $ LitLoc l) (Lit lit1) e2 : sqex_expr) @ E
  {{{ RET (LitV (LitInt 1) : sq_val); l ↦ LitV lit2 }}}.
Proof.
  iIntros (<- Hlit Φ) "Hl HΦ". rewrite exwp_as_wp.
  iApply (exwp_extcall _ _ _ _ _
    (LREctxExternal [] _ _ _
      (LRCasE l (Lit lit1) lit1 (of_val (LitV lit2)) lit2 eq_refl (to_of_val _)))).
  iIntros (σ1 ns κs nt) "Hσ". iMod "Hl".
  iDestruct (heap_read_1 with "Hσ Hl") as %Hl.
  apply lookup_sq_heap_Some in Hl as [_ Hl].
  iMod (heap_write _ _ _ (LitV lit2) with "Hσ Hl") as "[Hσ Hl]".
  iApply fupd_mask_intro; [ set_solver | ]. iIntros "Hclose". iSplit.
  { iPureIntro. exists (Some (LitV (lit_of_bool true))), (<[l := LitV lit2]> σ1).
    eapply ScCasSuc; [ exact Hl | | by rewrite /= Hl ].
    simpl. destruct lit1; by [ destruct (Hlit eq_refl) | constructor ]. }
  iIntros (ov σ2 Hsem).
  inversion Hsem; simplify_eq;
    match goal with H : load _ _ _ = Some _ |- _ => simpl in H; rewrite Hl in H end;
    simplify_eq.
  2: { (* failure is impossible: the compared literals are equal *)
    match goal with H : lr_val_neq _ _ _ |- _ => simpl in H; inversion H; congruence end. }
  match goal with H : store _ _ _ _ = Some _ |- _ =>
    destruct (lr_store_Some _ _ _ _ _ H) as (_ & ->) end.
  iModIntro. iNext. iMod "Hclose" as "_". iModIntro.
  iSplitL "Hσ"; [ by rewrite /= sq_heap_insert | ].
  iApply (exwp_value _ _ _ (LitV (lit_of_bool true)) eq_refl). by iApply "HΦ".
Qed.

Lemma exwp_cas_int_suc E l z1 e2 lit2 :
  IntoVal e2 (LitV lit2) ->
  {{{ ▷ l ↦ LitV (LitInt z1) }}}
    (CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 : sqex_expr) @ E
  {{{ RET (LitV (LitInt 1) : sq_val); l ↦ LitV lit2 }}}.
Proof. intros ?. by apply exwp_cas_suc. Qed.

Lemma exwp_cas_loc_suc E l l1 e2 lit2 :
  IntoVal e2 (LitV lit2) ->
  {{{ ▷ l ↦ LitV (LitLoc l1) }}}
    (CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 : sqex_expr) @ E
  {{{ RET (LitV (LitInt 1) : sq_val); l ↦ LitV lit2 }}}.
Proof. intros ?. by apply exwp_cas_suc. Qed.

Lemma exwp_cas_loc_fail E l q q' q1 l1 v1' e2 lit2 l' vl' :
  IntoVal e2 (LitV lit2) -> l1 ≠ l' ->
  {{{ ▷ l ↦{q} LitV (LitLoc l') ∗ ▷ l' ↦{q'} vl' ∗ ▷ l1 ↦{q1} v1' }}}
    (CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 : sqex_expr) @ E
  {{{ RET (LitV $ LitInt 0 : sq_val);
      l ↦{q} LitV (LitLoc l') ∗ l' ↦{q'} vl' ∗ l1 ↦{q1} v1' }}}.
Proof.
  iIntros (<- Hne Φ) "(Hl & Hl' & Hl1) HΦ". rewrite exwp_as_wp.
  iApply (exwp_extcall _ _ _ _ _
    (LREctxExternal [] _ _ _
      (LRCasE l (Lit (LitLoc l1)) (LitLoc l1) (of_val (LitV lit2)) lit2
         eq_refl (to_of_val _)))).
  iIntros (σ1 ns κs nt) "Hσ". iMod "Hl". iMod "Hl'". iMod "Hl1".
  iDestruct (heap_read with "Hσ Hl") as %[n0 Hl].
  apply lookup_sq_heap_Some in Hl as [_ Hl].
  iDestruct (heap_read with "Hσ Hl'") as %[n1 Hl'].
  apply lookup_sq_heap_Some in Hl' as [_ Hl'].
  iDestruct (heap_read with "Hσ Hl1") as %[n2 Hl1].
  apply lookup_sq_heap_Some in Hl1 as [_ Hl1].
  iApply fupd_mask_intro; [ set_solver | ]. iIntros "Hclose". iSplit.
  { iPureIntro. exists (Some (LitV (lit_of_bool false))), σ1.
    eapply ScCasFail; [ exact Hl | ]. simpl. by apply LocNeq. }
  iIntros (ov σ2 Hsem).
  inversion Hsem; simplify_eq;
    match goal with H : load _ _ _ = Some _ |- _ => simpl in H; rewrite Hl in H end;
    simplify_eq.
  { (* success is impossible: the locations differ and both are allocated *)
    exfalso. apply Hne. eapply sq_lit_eq_alloc; [ exact Hl1 | exact Hl' | ].
    match goal with H : lr_val_eq _ _ _ |- _ => simpl in H; exact H end. }
  iModIntro. iNext. iMod "Hclose" as "_". iModIntro.
  iSplitL "Hσ"; [ iExact "Hσ" | ].
  iApply (exwp_value _ _ _ (LitV (lit_of_bool false)) eq_refl).
  iApply "HΦ". iFrame.
Qed.

Lemma exwp_cas_loc_nondet E l l1 e2 l2 ll :
  IntoVal e2 (LitV $ LitLoc l2) ->
  {{{ ▷ l ↦ LitV (LitLoc ll) }}}
    (CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 : sqex_expr) @ E
  {{{ (b : bool), RET (LitV (lit_of_bool b) : sq_val);
      if b then l ↦ LitV (LitLoc l2)
      else ⌜l1 ≠ ll⌝ ∗ l ↦ LitV (LitLoc ll) }}}.
Proof.
  iIntros (<- Φ) "Hl HΦ". rewrite exwp_as_wp.
  iApply (exwp_extcall _ _ _ _ _
    (LREctxExternal [] _ _ _
      (LRCasE l (Lit (LitLoc l1)) (LitLoc l1) (of_val (LitV (LitLoc l2))) (LitLoc l2)
         eq_refl (to_of_val _)))).
  iIntros (σ1 ns κs nt) "Hσ". iMod "Hl".
  iDestruct (heap_read_1 with "Hσ Hl") as %Hl.
  apply lookup_sq_heap_Some in Hl as [_ Hl].
  iApply fupd_mask_intro; [ set_solver | ]. iIntros "Hclose". iSplit.
  { iPureIntro. destruct (decide (ll = l1)) as [-> | Hne].
    - exists (Some (LitV (lit_of_bool true))), (<[l := LitV (LitLoc l2)]> σ1).
      eapply ScCasSuc; [ exact Hl | simpl; apply sq_mem.LocRefl | by rewrite /= Hl ].
    - exists (Some (LitV (lit_of_bool false))), σ1.
      eapply ScCasFail; [ exact Hl | ]. simpl. by apply LocNeq. }
  iIntros (ov σ2 Hsem).
  inversion Hsem; simplify_eq;
    match goal with H : load _ _ _ = Some _ |- _ => simpl in H; rewrite Hl in H end;
    simplify_eq.
  - (* success, also for a nondeterministic comparison of dangling locations *)
    match goal with H : store _ _ _ _ = Some _ |- _ =>
      destruct (lr_store_Some _ _ _ _ _ H) as (_ & ->) end.
    iMod (heap_write _ _ _ (LitV (LitLoc l2)) with "Hσ Hl") as "[Hσ Hl]".
    iModIntro. iNext. iMod "Hclose" as "_". iModIntro.
    iSplitL "Hσ"; [ by rewrite /= sq_heap_insert | ].
    iApply (exwp_value _ _ _ (LitV (lit_of_bool true)) eq_refl).
    by iApply ("HΦ" $! true).
  - (* failure: the locations are distinct *)
    match goal with H : lr_val_neq _ _ _ |- _ =>
      simpl in H; inversion H; subst end.
    iModIntro. iNext. iMod "Hclose" as "_". iModIntro.
    iSplitL "Hσ"; [ iExact "Hσ" | ].
    iApply (exwp_value _ _ _ (LitV (lit_of_bool false)) eq_refl).
    iApply ("HΦ" $! false). by iFrame.
Qed.

End sc_rules.
