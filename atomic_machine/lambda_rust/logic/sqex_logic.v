(** Program logic of a sq_lang quantified over a specification of external 
   calls. The weakest pre definition is EXWP. *)

From iris.algebra Require Import auth gmap.
From iris.proofmode Require Import proofmode coq_tactics reduction.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import language ectx_language.
From lrust.lang Require Import tactics.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.logic.sq_logic.
Require Export VST.atomic_machine.lambda_rust.logic.lr_lemmas.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".

(** The specification of one external call: the type of its logical
    parameters, its precondition, and its postcondition on the returned
    value. The precondition may require the verification of spawned
    threads: EXWP supplies their WPs [W] under a later; the precondition
    itself is required now, inside the opening fancy update. *)
Record ExtSpec `(L : @sqlang Loc Val LocEqDec LocCountable Mem Layout Expr)
    (Σ : gFunctors) := {
  ext_args : Type;
  ext_pre : ext_args ->
    (* spawned threads' WP *)
    ((@sqlang_thrd_st _ _ _ _ _ _ _ L) -d> iPropO Σ) -n>
      iPropO Σ;
  ext_post : ext_args -> option Val -> iProp Σ
}.

Global Arguments ext_args {_ _ _ _ _ _ _ _ _} _.
Global Arguments ext_pre {_ _ _ _ _ _ _ _ _} _ _.
Global Arguments ext_post {_ _ _ _ _ _ _ _ _} _ _ _.

(** The specifications of all external calls: a specification for each. *)
Class ExtSpecs `(L : @sqlang Loc Val LocEqDec LocCountable Mem Layout Expr)
    (Σ : gFunctors) :=
  ext_spec : @atomic_op Loc Val Layout Expr -> ExtSpec L Σ.

Notation ext_spec_args op := (ext_args (ext_spec op)).
Notation ext_spec_pre op := (ext_pre (ext_spec op)).
Notation ext_spec_post op := (ext_post (ext_spec op)).

Local Existing Instance lrSqGS_invGS.

(** ** Footprints *)

Section footprints.
  Context `{!sq_heapGS Σ}.

  (** Ownership of a location: fractional to read it, full to modify (write &
      free) it. *)
  Definition fp_own (l : loc) (w : bool) : iProp Σ :=
    (if w then ∃ v, l ↦ v else ∃ q v, l ↦{q} v)%I.

  Lemma fp_own_full l v w : l ↦ v ⊢ fp_own l w.
  Proof. iIntros "Hl". destruct w; rewrite /fp_own; by iExists _; try iExists _. Qed.

  (** Two owners of a location, one of them writing, are incompatible. *)
  Lemma fp_own_excl l w1 w2 :
    w1 = true \/ w2 = true -> fp_own l w1 -∗ fp_own l w2 -∗ False.
  Proof.
    iIntros (Hw) "H1 H2". rewrite /fp_own.
    destruct w1, w2; [ | | | destruct Hw as [H|H]; discriminate ].
    - iDestruct "H1" as (v1) "H1". iDestruct "H2" as (v2) "H2".
      iDestruct (sq_pointsto_valid_2 with "H1 H2") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 1 Hq).
    - iDestruct "H1" as (v1) "H1". iDestruct "H2" as (q2 v2) "H2".
      iDestruct (sq_pointsto_valid_2 with "H1 H2") as %[Hq _].
      exfalso. exact (Qp.not_add_le_l 1 q2 Hq).
    - iDestruct "H1" as (q1 v1) "H1". iDestruct "H2" as (v2) "H2".
      iDestruct (sq_pointsto_valid_2 with "H1 H2") as %[Hq _].
      exfalso. exact (Qp.not_add_le_r q1 1 Hq).
  Qed.

  (** The ownership needed for one non-atomic event, before the step. *)
  Definition fp_event (ev : @mem_ev loc) : iProp Σ :=
    match ev_need_full_loc (NA ev) with
    | Some (l, w) => fp_own l w
    | None => True
    end.

  Definition fp_tokens (T : list (@mem_ev loc)) : iProp Σ :=
    [∗ list] ev ∈ T, fp_event ev.

  Lemma fp_tokens_nil : ⊢ fp_tokens [].
  Proof. by rewrite /fp_tokens. Qed.

  Lemma fp_tokens_elem T ev l w :
    ev ∈ T -> ev_need_full_loc (NA ev) = Some (l, w) -> fp_tokens T ⊢ fp_own l w.
  Proof.
    intros Hin Hacc. iIntros "Hfp".
    iDestruct (big_sepL_elem_of with "Hfp") as "Hev"; first exact Hin.
    by rewrite /fp_event Hacc.
  Qed.
End footprints.



(** A step of [sq_lang] is a sequential step of [sq_sem.v]. *)
Lemma sq_prim_step_lr_step (e : sq_expr) m κ e' m' efs :
  prim_step e m κ e' m' efs <-> lr_step e m κ e' m' /\ efs = [].
Proof.
  split.
  - intros [K e1 e2 -> -> Hs]. inversion Hs; subst. split; [ by apply LREctxStep | done ].
  - intros [[K e1 ? ? e2 ? Hh] ->]. apply (Ectx_step' (Λ := sq_ectx_lang) K). by apply SqHeadStep.
Qed.

(** ** Core steps

    [sq_step e Ψ] is the weakest precondition of one core (sequential) step
    of [e], whose successor satisfies [Ψ]. It is the conjunction of
    - the step clause: given [sq_heap m1], [e] can step, and every step
      yields [sq_heap m2] and [Ψ] of the successor;
    - the footprint clause: every step, from any memory, has its footprint
      in the thread's ownership before the step.
    The conjunction is non-separating: the footprint is only inspected to
    refute races, so the same resources justify both clauses. EXWP lifts
    every rule for a core step with the single rule [exwp_core_step], whose
    side condition is the class [CoreRedex]. *)

(** [e] is a core redex: not a value, and not an external call. The
    instances for the operations of [sq_logic.v] are in [sqex_lr_logic.v]. *)
Class CoreRedex (e : sq_expr) : Prop := {
  core_redex_not_val : to_val e = None;
  core_redex_not_external op k : ~ lr_external e op k;
}.

(** A pure step is a core step. *)
Lemma pure_step_core_redex e1 e2 : @pure_step sq_lang e1 e2 -> CoreRedex e1.
Proof.
  intros [Hsafe _]. destruct (Hsafe ∅) as (e' & m' & efs & Hs). split.
  - exact (language.val_stuck _ _ _ _ _ _ Hs).
  - apply sq_prim_step_lr_step in Hs as [Hs _].
    intros op k He. by eapply lr_step_external_disjoint.
Qed.

Section core_steps.
  Context `{!sq_heapGS Σ}.

  Definition sq_step (e : sq_expr) (Ψ : sq_expr -> iProp Σ) : iProp Σ :=
    (∀ m1, sq_heap m1 ==∗
      ⌜exists T e2 m2, lr_step e m1 T e2 m2⌝ ∗
      ∀ T e2 m2, ⌜lr_step e m1 T e2 m2⌝ -∗ ▷ |==> sq_heap m2 ∗ Ψ e2) ∧
    (∀ m1 T e2 m2, ⌜lr_step e m1 T e2 m2⌝ ==∗ fp_tokens T).

  Lemma sq_step_wand e Ψ Ψ' :
    sq_step e Ψ -∗ ▷ (∀ e', Ψ e' -∗ Ψ' e') -∗ sq_step e Ψ'.
  Proof.
    rewrite /sq_step. iIntros "H HΨ". iSplit.
    - iDestruct "H" as "[H _]". iIntros (m) "Hm".
      iMod ("H" with "Hm") as "[$ H]". iModIntro.
      iIntros (T e2 m2 Hs). iSpecialize ("H" $! T e2 m2 with "[//]").
      iNext. iMod "H" as "[$ H]". iModIntro. by iApply "HΨ".
    - by iDestruct "H" as "[_ H]".
  Qed.

  (** A step under an evaluation context is a step of the redex. *)
  Lemma sq_step_fill K e Ψ :
    to_val e = None ->
    sq_step e (λ e', Ψ (fill K e')) ⊢ sq_step (fill K e) Ψ.
  Proof.
    intros Hv. rewrite /sq_step. iIntros "H". iSplit.
    - iDestruct "H" as "[H _]". iIntros (m) "Hm".
      iMod ("H" with "Hm") as "[%Hr H]". iModIntro. iSplit.
      { iPureIntro. destruct Hr as (T & e2 & m2 & Hs).
        exists T, (fill K e2), m2. destruct Hs. rewrite -!fill_app. by constructor. }
      iIntros (T e2 m2 Hs).
      destruct (lr_step_fill_inv _ _ _ _ _ _ Hv Hs) as (e2' & -> & Hs').
      by iApply ("H" $! T e2' m2 with "[//]").
    - iDestruct "H" as "[_ H]". iIntros (m T e2 m2 Hs).
      destruct (lr_step_fill_inv _ _ _ _ _ _ Hv Hs) as (e2' & -> & Hs').
      by iApply ("H" $! m T e2' m2 with "[//]").
  Qed.

  Lemma sq_step_pure e1 e2 Ψ :
    @pure_step sq_lang e1 e2 -> ▷ Ψ e2 ⊢ sq_step e1 Ψ.
  Proof.
    intros [Hsafe Hdet]. rewrite /sq_step. iIntros "HΨ". iSplit.
    - iIntros (m) "Hm". iModIntro. iSplit.
      { iPureIntro. destruct (Hsafe m) as (e' & m' & efs & [Hs _]%sq_prim_step_lr_step).
        eauto. }
      iIntros (T e' m' Hs).
      destruct (Hdet m T e' m' []) as (-> & -> & -> & _).
      { by apply sq_prim_step_lr_step. }
      iNext. iModIntro. iFrame.
    - iIntros (m T e' m' Hs).
      destruct (Hdet m T e' m' []) as (-> & -> & -> & _).
      { by apply sq_prim_step_lr_step. }
      iModIntro. iApply fp_tokens_nil.
  Qed.
End core_steps.

(** ** The weakest precondition *)

Section exwp_pre.
  Context `{!lrSqGS Σ} (specs : ExtSpecs lr_language Σ).
  Local Existing Instance specs.

  Definition exwp_pre
      (exwp : coPset -d> sq_expr -d> (sq_val -d> iPropO Σ) -d> iPropO Σ) :
      coPset -d> sq_expr -d> (sq_val -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
    (|={E}=>
    match to_val e1 with
    | Some v => Φ v
    | None =>
        (* A core step: as in Iris's wp, except that a NA step needs to
           show that it has "enough" points-tos to emit its events. *)
        (⌜forall op k, ~ lr_external e1 op k⌝ ∗
          ((∀ m1, sq_heap m1 ==∗
             ⌜exists T e2 m2, lr_step e1 m1 T e2 m2⌝ ∗
             ∀ T e2 m2, ⌜lr_step e1 m1 T e2 m2⌝ -∗ ▷ |==> sq_heap m2 ∗ exwp E e2 Φ) ∧
           (∀ m1 T e2 m2, ⌜lr_step e1 m1 T e2 m2⌝ ==∗ fp_tokens T))) ∨
        (∃ op k, ⌜lr_external e1 op k⌝ ∗
          |={E,∅}=> ∃ x : ext_spec_args op,
            ext_spec_pre op x (λ ef, ▷ exwp ⊤ ef (λ _, True)) ∗
            ▷ (∀ ov, ext_spec_post op x ov -∗ |={∅,E}=> exwp E (k ov) Φ))
    end)%I.

  Global Instance exwp_pre_contractive : Contractive exwp_pre.
  Proof.
    rewrite /exwp_pre /= => n wp wp' Hwp E e1 Φ.
    repeat (f_contractive || f_equiv); first [apply Hwp | intros ef; f_contractive; apply Hwp].
  Qed.
End exwp_pre.

Definition exwp `{!lrSqGS Σ, !ExtSpecs lr_language Σ} :
    coPset -> sq_expr -> (sq_val -> iProp Σ) -> iProp Σ :=
  fixpoint (exwp_pre _).
Global Arguments exwp {Σ _ _} E e%_E Φ%_I.

Notation "'EXWP' e @ E {{ Φ } }" := (exwp E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'EXWP' e {{ Φ } }" := (exwp ⊤ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'EXWP' e @ E {{ v , Q } }" := (exwp E e%E (λ v, Q))
  (at level 20, e, Q at level 200, v at level 200 as pattern) : bi_scope.
Notation "'EXWP' e {{ v , Q } }" := (exwp ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200, v at level 200 as pattern) : bi_scope.

Notation "'{{{' P } } } 'EXWP' e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ EXWP e @ E {{ Φ }})%I
  (at level 20) : bi_scope.
Notation "'{{{' P } } } 'EXWP' e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, ⊢ P -∗ ▷ (Q -∗ Φ pat%V) -∗ EXWP e @ E {{ Φ }}) : stdpp_scope.

Section exwp.
  Context `{!lrSqGS Σ, !ExtSpecs lr_language Σ}.

  Lemma exwp_unfold E e Φ :
    EXWP e @ E {{ Φ }} ⊣⊢ exwp_pre _ exwp E e Φ.
  Proof. apply (fixpoint_unfold (exwp_pre _)). Qed.

  Lemma exwp_value_fupd E v Φ : EXWP of_val v @ E {{ Φ }} ⊣⊢ |={E}=> Φ v.
  Proof. by rewrite exwp_unfold /exwp_pre to_of_val. Qed.

  Lemma exwp_value E v Φ : Φ v ⊢ EXWP of_val v @ E {{ Φ }}.
  Proof. rewrite exwp_value_fupd. apply fupd_intro. Qed.

  (** A value given as an expression, e.g. a literal. *)
  Lemma exwp_value' E e v Φ `{!@IntoVal sq_lang e v} : Φ v ⊢ EXWP e @ E {{ Φ }}.
  Proof. rewrite -(@into_val sq_lang e v). apply exwp_value. Qed.

  Lemma fupd_exwp E e Φ : (|={E}=> EXWP e @ E {{ Φ }}) ⊢ EXWP e @ E {{ Φ }}.
  Proof. rewrite exwp_unfold /exwp_pre. apply fupd_trans. Qed.

  Lemma bupd_exwp E e Φ : (|==> EXWP e @ E {{ Φ }}) ⊢ EXWP e @ E {{ Φ }}.
  Proof. iIntros "H". iApply fupd_exwp. by iMod "H". Qed.

  Lemma exwp_seq_unfold E e Φ :
    to_val e = None -> (forall op k, ~ lr_external e op k) ->
    EXWP e @ E {{ Φ }} ⊣⊢
      |={E}=> ((∀ m1, sq_heap m1 ==∗
         ⌜exists T e2 m2, lr_step e m1 T e2 m2⌝ ∗
         ∀ T e2 m2, ⌜lr_step e m1 T e2 m2⌝ -∗ ▷ |==>
           sq_heap m2 ∗ EXWP e2 @ E {{ Φ }}) ∧
       (∀ m1 T e2 m2, ⌜lr_step e m1 T e2 m2⌝ ==∗ fp_tokens T)).
  Proof.
    intros Hv Hext. rewrite exwp_unfold /exwp_pre Hv.
    iSplit.
    - iIntros ">[[_ Hseq] | (%op & %k & %Hcall & _)]".
      + by iModIntro.
      + exfalso. by eapply Hext.
    - iIntros ">H !>". iLeft. iFrame. done.
  Qed.

  Lemma exwp_core_step E e Φ `{!CoreRedex e} :
    sq_step e (λ e2, EXWP e2 @ E {{ Φ }}) ⊢ EXWP e @ E {{ Φ }}.
  Proof.
    rewrite (exwp_seq_unfold _ _ _ core_redex_not_val core_redex_not_external) /sq_step.
    apply fupd_intro.
  Qed.

  Lemma exwp_lift_external E e op k Φ :
    lr_external e op k ->
    (|={E,∅}=> ∃ x : ext_spec_args op,
      ext_spec_pre op x (λ ef, ▷ EXWP ef {{ _, True }}) ∗
      ▷ (∀ ov, ext_spec_post op x ov -∗ |={∅,E}=> EXWP k ov @ E {{ Φ }})) ⊢
    EXWP e @ E {{ Φ }}.
  Proof.
    intros Hext. rewrite exwp_unfold /exwp_pre (lr_external_not_val _ _ _ Hext).
    iIntros "Hspec !>". iRight. iExists op, k. by iFrame.
  Qed.

  Lemma exwp_ext_unfold E e op k Φ :
    lr_external e op k ->
    EXWP e @ E {{ Φ }} ⊣⊢
      (|={E,∅}=> ∃ x : ext_spec_args op,
        ext_spec_pre op x (λ ef, ▷ EXWP ef {{ _, True }}) ∗
        ▷ (∀ ov, ext_spec_post op x ov -∗ |={∅,E}=> EXWP k ov @ E {{ Φ }})).
  Proof.
    intros He. iSplit; last by iApply (exwp_lift_external _ _ _ _ _ He).
    rewrite exwp_unfold /exwp_pre (lr_external_not_val _ _ _ He).
    iIntros ">[[%Hno _] | (%op' & %k' & %He' & Hspec)]".
    - exfalso. by eapply Hno.
    - destruct (lr_external_det _ _ _ _ _ He He') as [-> Hk].
      iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
      iNext. iIntros (ov) "Hpost". rewrite -(Hk ov). by iApply "Hcont".
  Qed.

  Lemma exwp_bind K E e Φ :
    EXWP e @ E {{ v, EXWP fill K (of_val v) @ E {{ Φ }} }} ⊢
    EXWP fill K e @ E {{ Φ }}.
  Proof.
    iLöb as "IH" forall (e). rewrite (exwp_unfold E e) /exwp_pre.
    destruct (to_val e) as [v|] eqn:Hv.
    { apply of_to_val in Hv. subst e. iApply fupd_exwp. }
    rewrite exwp_unfold /exwp_pre (fill_not_val _ _ Hv).
    iIntros ">[[%Hno Hseq] | (%op & %k & %He & Hspec)] !>".
    - iLeft. iSplit.
      { iPureIntro. intros op k He.
        destruct (lr_external_fill_inv _ _ _ _ Hv He) as (k' & He' & _).
        by eapply Hno. }
      iApply sq_step_fill; first done.
      iApply (sq_step_wand with "Hseq"). iIntros "!>" (e') "Hwp".
      by iApply "IH".
    - destruct (lr_external_fill K _ _ _ He) as (k' & He' & Hk).
      iRight. iExists op, k'. iSplit; first done.
      iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
      iNext. iIntros (ov) "Hpost". iMod ("Hcont" with "Hpost") as "Hwp".
      iModIntro. rewrite Hk. by iApply "IH".
  Qed.

  Lemma exwp_pure_step E e1 e2 Φ :
    @pure_step sq_lang e1 e2 -> ▷ EXWP e2 @ E {{ Φ }} ⊢ EXWP e1 @ E {{ Φ }}.
  Proof.
    intros Hpure. have ? := pure_step_core_redex _ _ Hpure.
    iIntros "Hwp". iApply exwp_core_step. by iApply sq_step_pure.
  Qed.

  Lemma exwp_pure_steps E e1 e2 Φ n :
    nsteps (@pure_step sq_lang) n e1 e2 ->
    ▷^n EXWP e2 @ E {{ Φ }} ⊢ EXWP e1 @ E {{ Φ }}.
  Proof.
    induction 1 as [e | n e1 e2 e3 Hs Hsteps IH]; first done.
    simpl. iIntros "H". iApply (exwp_pure_step _ _ _ _ Hs).
    iNext. by iApply IH.
  Qed.

  Lemma exwp_wand E e Φ Ψ :
    EXWP e @ E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ EXWP e @ E {{ Ψ }}.
  Proof.
    iLöb as "IH" forall (e). iIntros "Hwp HΦ".
    rewrite !(exwp_unfold E e) /exwp_pre.
    destruct (to_val e) as [v|].
    { iMod "Hwp". iModIntro. by iApply "HΦ". }
    iMod "Hwp" as "[[%Hno Hseq] | (%op & %k & %He & Hspec)]"; iModIntro.
    - iLeft. iSplit; first done.
      iApply (sq_step_wand with "Hseq"). iIntros "!>" (e') "Hwp".
      iApply ("IH" with "Hwp HΦ").
    - iRight. iExists op, k. iSplit; first done.
      iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
      iNext. iIntros (ov) "Hpost". iMod ("Hcont" with "Hpost") as "Hwp". iModIntro.
      iApply ("IH" with "Hwp HΦ").
  Qed.

  Lemma exwp_fupd E e Φ :
    EXWP e @ E {{ v, |={E}=> Φ v }} ⊢ EXWP e @ E {{ Φ }}.
  Proof.
    iLöb as "IH" forall (e). rewrite !(exwp_unfold E e) /exwp_pre.
    destruct (to_val e) as [v|].
    { iIntros ">H". by iMod "H". }
    iIntros ">[[%Hno Hseq] | (%op & %k & %He & Hspec)] !>".
    - iLeft. iSplit; first done.
      iApply (sq_step_wand with "Hseq"). iIntros "!>" (e') "Hwp".
      by iApply "IH".
    - iRight. iExists op, k. iSplit; first done.
      iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
      iNext. iIntros (ov) "Hpost". iMod ("Hcont" with "Hpost") as "Hwp".
      iModIntro. by iApply "IH".
  Qed.

  Lemma exwp_atomic_ext E1 E2 e op k Φ :
    lr_external e op k ->
    (forall x ov, ext_spec_post op x ov ⊢ ⌜is_Some (to_val (k ov))⌝) ->
    (|={E1,E2}=> EXWP e @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢
      EXWP e @ E1 {{ Φ }}.
  Proof.
    intros He Ha. iIntros "Hwp".
    iApply (exwp_lift_external _ _ _ _ _ He).
    iMod "Hwp" as "Hwp".
    iEval (rewrite (exwp_ext_unfold _ _ _ _ _ He)) in "Hwp".
    iMod "Hwp" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
    iNext. iIntros (ov) "Hpost".
    iDestruct (Ha with "Hpost") as %[v Hv].
    iMod ("Hcont" with "Hpost") as "Hwp".
    apply of_to_val in Hv as <-. rewrite !exwp_value_fupd.
    iMod "Hwp" as ">HΦ". by iModIntro.
  Qed.
End exwp.

Lemma tac_exwp_bind `{!lrSqGS Σ, !ExtSpecs lr_language Σ} K Δ E Φ e :
  envs_entails Δ (EXWP e @ E {{ v, EXWP fill K (of_val v) @ E {{ Φ }} }})%I ->
  envs_entails Δ (EXWP fill K e @ E {{ Φ }}).
Proof. rewrite envs_entails_unseal => ->. apply exwp_bind. Qed.

Lemma tac_exwp_pure `{!lrSqGS Σ, !ExtSpecs lr_language Σ} K Δ Δ' E e1 e2 φ n Φ :
  @PureExec sq_lang φ n e1 e2 -> φ ->
  MaybeIntoLaterNEnvs n Δ Δ' ->
  envs_entails Δ' (EXWP fill K e2 @ E {{ Φ }}) ->
  envs_entails Δ (EXWP fill K e1 @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal => Hexec Hφ ? HΔ.
  rewrite into_laterN_env_sound HΔ. apply exwp_pure_steps.
  exact (@pure_step_nsteps_ctx sq_lang (@ectx_language.fill sq_ectx_lang K)
    (@ectx_lang_ctx sq_ectx_lang K) n e1 e2 (Hexec Hφ)).
Qed.

Tactic Notation "exwp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (exwp ?E ?e ?Φ) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc; apply (tac_exwp_bind K); simpl)
  end.

Tactic Notation "exwp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (exwp ?E ?e ?Φ) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc; eapply (tac_exwp_pure K);
    [simpl; tc_solve | try done | tc_solve | simpl_subst])
  end.

(** The contracts used by the SC examples. CAS compares integer values and
    requires full ownership, whether the comparison succeeds or fails. *)
Section ext_specs.
  Context `{!lrSqGS Σ}.

  (** An SC read of [l]: a fraction [q] of [l ↦ v], returned with [v]. *)
  Definition sc_load_spec (l : loc) : ExtSpec lr_language Σ := {|
    ext_args := Qp * val;
    ext_pre qv := cconst (l ↦{qv.1} qv.2)%I;
    ext_post qv ov := (⌜ov = Some qv.2⌝ ∗ l ↦{qv.1} qv.2)%I |}.

  (** An SC write of [v] to [l]: full ownership of [l]. *)
  Definition sc_store_spec (l : loc) (v : val) : ExtSpec lr_language Σ := {|
    ext_args := val;
    ext_pre v' := cconst (l ↦ v')%I;
    ext_post _ ov := (⌜ov = None⌝ ∗ l ↦ v)%I |}.

  (** A CAS on an integer cell: full ownership, whether it succeeds or not. *)
  Definition sc_cas_spec (l : loc) (v_exp v_new : val) : ExtSpec lr_language Σ := {|
    ext_args := Z * Z;
    ext_pre x := cconst (⌜v_exp = LitV (LitInt x.2)⌝ ∗ l ↦ LitV (LitInt x.1))%I;
    ext_post x ov :=
      (⌜ov = Some (LitV (lit_of_bool (bool_decide (x.1 = x.2))))⌝ ∗
       l ↦ (if decide (x.1 = x.2) then v_new else LitV (LitInt x.1)))%I |}.

  Local Instance sc_spawn_pre_ne (e : sq_expr) :
    NonExpansive (λ W : sq_expr -d> iPropO Σ, W e).
  Proof. intros n W W' HW. apply HW. Qed.

  (** Spawning [e]: the WP of [e]. *)
  Definition sc_spawn_spec (e : sq_expr) : ExtSpec lr_language Σ := {|
    ext_args := unit;
    ext_pre _ := OfeMor (λ W : sq_expr -d> iPropO Σ, W e);
    ext_post _ ov := ⌜ov = None⌝%I |}.

  Definition ext_specs : ExtSpecs lr_language Σ := λ op,
    match op with
    | ALoad _ l => sc_load_spec l
    | AStore _ l v => sc_store_spec l v
    | ACAS _ l v_exp v_new => sc_cas_spec l v_exp v_new
    | ASpawn e => sc_spawn_spec e
    end.
End ext_specs.

(** Proof rules. *)
Section concurrent_rules.
  Context `{!lrSqGS Σ}.
  Local Existing Instance ext_specs.

  Lemma conc_wp_read_sc E l q v :
    {{{ ▷ l ↦{q} v }}} EXWP (Read ScOrd (Lit $ LitLoc l) : sq_expr) @ E
    {{{ RET (v : sq_val); l ↦{q} v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    iApply (exwp_lift_external _ _ (ALoad tt l) lr_result_expr).
    { apply (LREctxExternal []). constructor. }
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
    iMod "Hl" as "Hl".
    iModIntro. iExists (q, v). simpl. iFrame "Hl".
    iNext. iIntros (ov) "[-> Hl]". iMod "Hclose" as "_".
    iModIntro. iApply exwp_value. by iApply "HΦ".
  Qed.

  Lemma conc_wp_write_sc E l (e : sq_expr) v v' :
    IntoVal e v ->
    {{{ ▷ l ↦ v' }}} EXWP (Write ScOrd (Lit $ LitLoc l) e : sq_expr) @ E
    {{{ RET (LitV LitPoison : sq_val); l ↦ v }}}.
  Proof.
    intros Hval Φ. iIntros "Hl HΦ".
    assert (Hv : to_val e = Some v).
    { rewrite -(@into_val sq_lang e v Hval). apply to_of_val. }
    iApply (exwp_lift_external _ _ (AStore tt l v) (fun _ => Lit LitPoison)).
    { apply (LREctxExternal []). by constructor. }
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
    iMod "Hl" as "Hl".
    iModIntro. iExists v'. simpl. iFrame "Hl".
    iNext. iIntros (ov) "[-> Hl]". iMod "Hclose" as "_".
    iModIntro. iApply (exwp_value _ (LitV LitPoison)). by iApply "HΦ".
  Qed.

  Lemma conc_wp_cas_int E l z_exp (e_new : sq_expr) lit_new z_cur :
    IntoVal e_new (LitV lit_new) ->
    {{{ ▷ l ↦ LitV (LitInt z_cur) }}}
      EXWP (CAS (Lit $ LitLoc l) (Lit $ LitInt z_exp) e_new : sq_expr) @ E
    {{{ RET (LitV (lit_of_bool (bool_decide (z_cur = z_exp))) : sq_val);
        l ↦ (if decide (z_cur = z_exp) then LitV lit_new else LitV (LitInt z_cur)) }}}.
  Proof.
    intros Hval Φ. iIntros "Hl HΦ".
    assert (Hv : to_val e_new = Some (LitV lit_new)).
    { rewrite -(@into_val sq_lang e_new (LitV lit_new) Hval). apply to_of_val. }
    iApply (exwp_lift_external _ _
      (ACAS tt l (LitV (LitInt z_exp)) (LitV lit_new)) lr_result_expr).
    { apply (LREctxExternal []). by constructor. }
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
    iMod "Hl" as "Hl".
    iModIntro. iExists (z_cur, z_exp). simpl. iFrame "Hl". iSplit; first done.
    iNext. iIntros (ov) "[-> Hl]". iMod "Hclose" as "_".
    iModIntro. iApply exwp_value. by iApply "HΦ".
  Qed.

  Lemma conc_wp_cas_int_suc E l z_exp (e_new : sq_expr) lit_new :
    IntoVal e_new (LitV lit_new) ->
    {{{ ▷ l ↦ LitV (LitInt z_exp) }}}
      EXWP (CAS (Lit $ LitLoc l) (Lit $ LitInt z_exp) e_new : sq_expr) @ E
    {{{ RET (LitV (LitInt 1) : sq_val); l ↦ LitV lit_new }}}.
  Proof.
    intros Hval Φ. iIntros "Hl HΦ".
    iApply (conc_wp_cas_int E l z_exp e_new lit_new z_exp Hval with "Hl").
    rewrite bool_decide_true; last done. rewrite decide_True; last done.
    done.
  Qed.

  Lemma conc_wp_cas_int_fail E l z_exp (e_new : sq_expr) lit_new z_cur :
    IntoVal e_new (LitV lit_new) -> z_exp ≠ z_cur ->
    {{{ ▷ l ↦ LitV (LitInt z_cur) }}}
      EXWP (CAS (Lit $ LitLoc l) (Lit $ LitInt z_exp) e_new : sq_expr) @ E
    {{{ RET (LitV (LitInt 0) : sq_val); l ↦ LitV (LitInt z_cur) }}}.
  Proof.
    intros Hval Hne Φ. iIntros "Hl HΦ".
    iApply (conc_wp_cas_int E l z_exp e_new lit_new z_cur Hval with "Hl").
    rewrite bool_decide_false; last congruence. rewrite decide_False; last congruence.
    done.
  Qed.

  Lemma conc_wp_fork E (e : sq_expr) :
    {{{ ▷ EXWP e {{ _, True }} }}} EXWP (Fork e : sq_expr) @ E
    {{{ RET (LitV LitPoison : sq_val); True }}}.
  Proof.
    iIntros (Φ) "He HΦ".
    iApply (exwp_lift_external _ _ (ASpawn e) (fun _ => Lit LitPoison)).
    { apply (LREctxExternal []). constructor. }
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
    iModIntro. iExists (). simpl. iFrame "He".
    iNext. iIntros (ov) "->". iMod "Hclose" as "_".
    iModIntro. iApply (exwp_value _ (LitV LitPoison)). iApply "HΦ". done.
  Qed.

  Lemma exwp_read_sc_atomic E1 E2 l Φ :
    (|={E1,E2}=> EXWP (Read ScOrd (Lit (LitLoc l))) @ E2
      {{ v, |={E2,E1}=> Φ v }}) ⊢
    EXWP (Read ScOrd (Lit (LitLoc l))) @ E1 {{ Φ }}.
  Proof.
    eapply (exwp_atomic_ext _ _ _ (ALoad tt l) lr_result_expr).
    - apply (LREctxExternal []). constructor.
    - intros [q v] ov. simpl. iIntros "[-> _]".
      iPureIntro. exists v. apply to_of_val.
  Qed.

  Lemma exwp_write_sc_atomic E1 E2 l v Φ :
    (|={E1,E2}=> EXWP (Write ScOrd (Lit (LitLoc l)) (of_val v)) @ E2
      {{ v, |={E2,E1}=> Φ v }}) ⊢
    EXWP (Write ScOrd (Lit (LitLoc l)) (of_val v)) @ E1 {{ Φ }}.
  Proof.
    eapply (exwp_atomic_ext _ _ _ (AStore tt l v) (fun _ => Lit LitPoison)).
    - apply (LREctxExternal []). constructor. apply to_of_val.
    - intros x ov. iIntros "_". eauto.
  Qed.

  Lemma exwp_cas_atomic E1 E2 l lit_exp lit_new Φ :
    (|={E1,E2}=> EXWP (CAS (Lit (LitLoc l)) (Lit lit_exp) (Lit lit_new)) @ E2
      {{ v, |={E2,E1}=> Φ v }}) ⊢
    EXWP (CAS (Lit (LitLoc l)) (Lit lit_exp) (Lit lit_new)) @ E1 {{ Φ }}.
  Proof.
    eapply (exwp_atomic_ext _ _ _
      (ACAS tt l (LitV lit_exp) (LitV lit_new)) lr_result_expr).
    - apply (LREctxExternal []). by constructor.
    - intros [z_cur z_exp] ov. simpl. iIntros "[-> _]".
      iPureIntro. eexists. apply to_of_val.
  Qed.
End concurrent_rules.
