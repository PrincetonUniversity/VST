(** Program logic of a sequential language, quantified over a specification of 
  external calls. The weakest pre definition is EXWP. *)

From iris.algebra Require Import gmap frac.
From iris.proofmode Require Import proofmode coq_tactics.
From iris.program_logic Require Export weakestpre.
Require Export VST.atomic_machine.atomic_machine.

Set Default Proof Using "Type".

(** Assume a generic sq_heap (the state_interp) that has some notion of points-to. *)
Class sqHeap `(L : @sqlang Loc Val LocEqDec LocCountable Mem Layout Expr)
    (Σ : gFunctors) := {
  sq_mem_inhabited :: Inhabited Mem;
  sq_heap : Mem -> iProp Σ;
  sq_pointsto : Loc -> Qp -> Val -> iProp Σ;
  sq_pointsto_valid_2 l q1 q2 v1 v2 :
    sq_pointsto l q1 v1 -∗ sq_pointsto l q2 v2 -∗ ⌜(q1 + q2 ≤ 1)%Qp⌝;
  (** Having a points-to contradicts with an allocation of the same location from the current memory. *)
  sq_pointsto_alloc_excl {e m T e' m' l} q v :
    sqlang_step e m T e' m' -> Alloc l ∈ T ->
    sq_heap m -∗ sq_pointsto l q v -∗ False
}.

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
    (Σ : gFunctors) := {
  ext_spec : @atomic_op Loc Val Layout Expr -> ExtSpec L Σ
}.

Notation ext_spec_args op := (ext_args (ext_spec op)).
Notation ext_spec_pre op := (ext_pre (ext_spec op)).
Notation ext_spec_post op := (ext_post (ext_spec op)).

Section language.
  Context `{L : !@sqlang Loc Val LocEqDec LocCountable Mem Layout Expr}.
  Local Notation C := (@sqlang_thrd_st _ _ _ _ _ _ _ L).

(** ** Footprints *)

Section footprints.
  Context `{!sqHeap L Σ}.

  (** For the event trace [T] in a *single* step, for each accessed
    location, records whether that location needs a full points-to in [T]. *)
  Fixpoint fp_requirements (T : list (@mem_ev Loc)) : gmap Loc bool :=
    match T with
    | [] => ∅
    | ev :: T =>
        let F := fp_requirements T in
        match mem_ev_need_full_loc ev with
        | Some (l, w) => <[l := w || default false (F !! l)]> F
        | None => F
        end
    end.

  Lemma fp_requirements_elem T ev l w :
    ev ∈ T -> mem_ev_need_full_loc ev = Some (l, w) ->
    exists w', fp_requirements T !! l = Some w' /\ (w = true -> w' = true).
  Proof.
    induction T as [|ev' T IH]; first by rewrite elem_of_nil.
    rewrite elem_of_cons. intros [-> | Hin] Hacc; cbn [fp_requirements].
    - rewrite Hacc lookup_insert_eq. eexists. split; first done.
      intros ->. done.
    - destruct (IH Hin Hacc) as (w' & Hl & Hw).
      destruct (mem_ev_need_full_loc ev') as [[l' w'']|]; last by eauto.
      destruct (decide (l' = l)) as [-> | Hne].
      + rewrite lookup_insert_eq Hl /=. eexists. split; first done.
        intros H. rewrite (Hw H). by destruct w''.
      + rewrite lookup_insert_ne //. by eauto.
  Qed.


  (** A footprint requirement's corresponding ownership. [w] is true for a write
     or free event. *)
  Definition fp_own (l : Loc) (w : bool) : iProp Σ :=
    (if w then ∃ v, sq_pointsto l 1 v else ∃ q v, sq_pointsto l q v)%I.

  Lemma fp_own_full l v w : sq_pointsto l 1 v ⊢ fp_own l w.
  Proof. iIntros "Hl". destruct w; rewrite /fp_own; by iExists _; try iExists _. Qed.

  Lemma fp_own_mono l w w' :
    (w = true -> w' = true) -> fp_own l w' ⊢ fp_own l w.
  Proof.
    intros Hw. destruct w, w'; try done.
    - by specialize (Hw eq_refl).
    - iDestruct 1 as (v) "Hl". by iApply fp_own_full.
  Qed.

  (** Two owners of a location, one of them writing, are incompatible. *)
  Lemma fp_own_excl l w1 w2 :
    w1 = true \/ w2 = true -> fp_own l w1 -∗ fp_own l w2 -∗ False.
  Proof.
    iIntros (Hw) "H1 H2". rewrite /fp_own.
    destruct w1, w2; [ | | | destruct Hw as [H|H]; discriminate ].
    - iDestruct "H1" as (v1) "H1". iDestruct "H2" as (v2) "H2".
      iDestruct (sq_pointsto_valid_2 with "H1 H2") as %Hq.
      exfalso. exact (Qp.not_add_le_l 1 1 Hq).
    - iDestruct "H1" as (v1) "H1". iDestruct "H2" as (q2 v2) "H2".
      iDestruct (sq_pointsto_valid_2 with "H1 H2") as %Hq.
      exfalso. exact (Qp.not_add_le_l 1 q2 Hq).
    - iDestruct "H1" as (q1 v1) "H1". iDestruct "H2" as (v2) "H2".
      iDestruct (sq_pointsto_valid_2 with "H1 H2") as %Hq.
      exfalso. exact (Qp.not_add_le_r q1 1 Hq).
  Qed.

  (** The ownership needed for one non-atomic event, before the step. *)
  Definition fp_event (ev : @mem_ev Loc) : iProp Σ :=
    match mem_ev_need_full_loc ev with
    | Some (l, w) => fp_own l w
    | None => True
    end.

  (** One points-to per accessed location, with full ownership exactly when
      at least one event at that location writes or frees it. *)
  Definition fp_tokens (T : list (@mem_ev Loc)) : iProp Σ :=
    [∗ map] l ↦ w ∈ fp_requirements T, fp_own l w.

  Lemma fp_tokens_nil : ⊢ fp_tokens [].
  Proof. by rewrite /fp_tokens /= big_sepM_empty. Qed.

  Lemma fp_tokens_singleton ev : fp_tokens [ev] ⊣⊢ fp_event ev.
  Proof.
    destruct ev; rewrite /fp_tokens /fp_event /= ?lookup_empty /=;
      by rewrite ?big_sepM_singleton ?big_sepM_empty.
  Qed.

  Lemma fp_tokens_cons ev T : fp_event ev ∗ fp_tokens T ⊢ fp_tokens (ev :: T).
  Proof.
    rewrite /fp_event /fp_tokens. cbn [fp_requirements].
    destruct (mem_ev_need_full_loc ev) as [[l w]|]; last by iIntros "[_ $]".
    iIntros "[Hev HT]".
    destruct (fp_requirements T !! l) as [w'|] eqn:Hl.
    - iDestruct (big_sepM_insert_acc with "HT") as "[Hl Hclose]"; first exact Hl.
      iApply "Hclose". simpl. destruct w; [iExact "Hev" | iExact "Hl"].
    - rewrite big_sepM_insert // /= Bool.orb_false_r. by iFrame.
  Qed.

  Lemma fp_tokens_elem T ev l w :
    ev ∈ T -> mem_ev_need_full_loc ev = Some (l, w) -> fp_tokens T ⊢ fp_own l w.
  Proof.
    intros Hin Hacc.
    destruct (fp_requirements_elem _ _ _ _ Hin Hacc) as (w' & Hl & Hw).
    rewrite /fp_tokens. iIntros "Hfp". iApply (fp_own_mono _ _ _ Hw).
    by iApply (big_sepM_lookup with "Hfp").
  Qed.
End footprints.

(** The logic is adequate for any external calls, as long as their specs satisfy
  the properties defined below. *)
Section ext_soundness.
  Context `{!sqHeap _ Σ} (spec : ExtSpec _ Σ)
    (op : @atomic_op Loc Val Layout Expr).

  (** PRE and SI imply that the call has a corr. at_step. *)
  Definition ext_enabled : Prop :=
    forall (e : C) k x (W : C -> iProp Σ) m,
      sqlang_at_external e op k ->
      ⊢ ext_pre spec x W -∗ sq_heap m -∗
        ⌜exists evs e' m' o, at_step e m evs e' m' o⌝.

  (** PRE and SI can be updated to POST, SI' and WP of the spawned thread (encoded as [W]). *)
  Definition ext_step : Prop :=
    forall (e : C) k x (W : C -> iProp Σ) m evs e' m' o,
      sqlang_at_external e op k -> at_step e m evs e' m' o ->
      ⊢ ext_pre spec x W -∗ sq_heap m ==∗
        ∃ ov, ⌜e' = k ov⌝ ∗ sq_heap m' ∗ ext_post spec x ov ∗ from_option W True o.

  (** At every location accessed in [evs], the precond owns the required points-to. *)
  Definition ext_footprint : Prop :=
    forall (e : C) k x (W : C -> iProp Σ) m evs e' m' o ev l w,
      sqlang_at_external e op k -> at_step e m evs e' m' o -> ev ∈ evs ->
      ev_access ev l w ->
      ⊢ ext_pre spec x W -∗ fp_own l w.
End ext_soundness.

(** Soundness of one external call. *)
Record ext_call_soundness `{!sqHeap L Σ} (spec : ExtSpec L Σ)
    (op : @atomic_op Loc Val Layout Expr) : Prop := {
  ext_enabled_pf : ext_enabled spec op;
  ext_step_pf : ext_step spec op;
  ext_footprint_pf : ext_footprint spec op;
}.

(** ** Core steps

  [sq_step e Ψ] is the weakest precondition of one core (sequential) step
  of [e], whose successor satisfies [Ψ]. It is the conjunction of
  - the step clause: given [sq_heap m1], [e] can step, and every step
    yields [sq_heap m2] and [Ψ] of the successor;
  - the footprint clause: every step, from any memory, has its footprint
    in the thread's ownership before the step.
  The conjunction is non-separating: the footprint is only inspected to
  refute races, so the same resources justify both clauses. *)
Definition sq_step `{!sqHeap L Σ} (e : C) (Ψ : C -> iProp Σ) : iProp Σ :=
  (* same as Iris wp, except a sequential step is not allowed a fupd in the
      middle of a step due to their non-atomic nature. *)
  (∀ m1, sq_heap m1 ==∗
    ⌜exists T e2 m2, sqlang_step e m1 T e2 m2⌝ ∗
    ∀ T e2 m2, ⌜sqlang_step e m1 T e2 m2⌝ -∗ ▷ |==> sq_heap m2 ∗ Ψ e2) ∧
  (* must demonstrate enough [fp_tokens] for all possible step from [e] *)
  (∀ m1 T e2 m2, ⌜sqlang_step e m1 T e2 m2⌝ ==∗ fp_tokens T).

Lemma sq_step_wand `{!sqHeap L Σ} e Ψ Ψ' :
  sq_step e Ψ -∗ ▷ (∀ e', Ψ e' -∗ Ψ' e') -∗ sq_step e Ψ'.
Proof.
  rewrite /sq_step. iIntros "H HΨ". iSplit.
  - iDestruct "H" as "[H _]". iIntros (m) "Hm".
    iMod ("H" with "Hm") as "[$ H]". iModIntro.
    iIntros (T e2 m2 Hs). iSpecialize ("H" $! T e2 m2 with "[//]").
    iNext. iMod "H" as "[$ H]". iModIntro. by iApply "HΨ".
  - by iDestruct "H" as "[_ H]".
Qed.

Definition exwp_pre `{!sqHeap L Σ, !invGS Σ, !ExtSpecs L Σ}
    (exwp : coPset -d> C -d> (Val -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> C -d> (Val -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  (|={E}=>
  match sqlang_is_final e1 with
  | Some v => Φ v
  | None =>
      (* A core step: as in Iris's wp, except that a NA step needs to
          show that it has "enough" points-tos to emit its events. *)
      (⌜forall op k, ~ sqlang_at_external e1 op k⌝ ∗
        sq_step e1 (λ e2, exwp E e2 Φ)) ∨
      (∃ op k, ⌜sqlang_at_external e1 op k⌝ ∗
        |={E,∅}=> ∃ x : ext_spec_args op,
          ext_spec_pre op x (λ ef, ▷ exwp ⊤ ef (λ _, True)) ∗
          ▷ (∀ ov, ext_spec_post op x ov -∗ |={∅,E}=> exwp E (k ov) Φ))
  end)%I.

Global Instance exwp_pre_contractive `{!sqHeap L Σ, !invGS Σ, !ExtSpecs L Σ} :
  Contractive exwp_pre.
Proof.
  rewrite /exwp_pre /sq_step /= => n wp wp' Hwp E e1 Φ.
  repeat (f_contractive || f_equiv); first [apply Hwp | intros ef; f_contractive; apply Hwp].
Qed.


Definition exwp `{!sqHeap L Σ, !invGS Σ, !ExtSpecs L Σ} :
    coPset -> C -> (Val -> iProp Σ) -> iProp Σ :=
  fixpoint exwp_pre.
Global Arguments exwp {Σ _ _ _} E e%_E Φ%_I.

End language.

(** Invert a step of an exposed operation. [Hk] identifies its continuation
    with the one supplied by the caller. *)
Ltac sqlang_ext_inv He Hst :=
  inversion Hst; subst;
  try (exfalso; by eapply sqlang_step_external_disjoint);
  match goal with H : sqlang_at_external _ _ _ |- _ =>
    destruct (sqlang_external_det _ _ _ _ _ He H) as [Hop Hk]; try discriminate Hop;
    injection Hop; intros; subst
  end.


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

Section language_rules.
  Context `{L : !@sqlang Loc Val LocEqDec LocCountable Mem Layout Expr}.
  Local Notation C := (@sqlang_thrd_st _ _ _ _ _ _ _ L).

(** Optional interfaces for syntax-directed proof rules. *)
Class sqOfVal := {
  sq_of_val : Val -> C;
  sq_to_of_val v : sqlang_is_final (sq_of_val v) = Some v;
  sq_of_to_val e v : sqlang_is_final e = Some v -> sq_of_val v = e
}.

Class SqIntoVal (e : C) (v : Val) : Prop :=
  sq_into_val : sqlang_is_final e = Some v.

Global Instance sq_of_val_into_val `{!sqOfVal} v : SqIntoVal (sq_of_val v) v.
Proof. apply sq_to_of_val. Qed.

Class SqAtExternal (e : C) (op : @atomic_op Loc Val Layout Expr)
    (k : option Val -> C) : Prop :=
  sq_at_external : sqlang_at_external e op k.

Class SqContext (K : C -> C) : Prop := {
  sq_ctx_not_final e :
    sqlang_is_final e = None -> sqlang_is_final (K e) = None;
  sq_ctx_step e m T e' m' :
    sqlang_step e m T e' m' -> sqlang_step (K e) m T (K e') m';
  sq_ctx_step_inv e m T e' m' :
    sqlang_is_final e = None -> sqlang_step (K e) m T e' m' ->
    exists e2, e' = K e2 /\ sqlang_step e m T e2 m';
  sq_ctx_external e op k :
    sqlang_at_external e op k ->
    exists k', sqlang_at_external (K e) op k' /\ forall ov, k' ov = K (k ov);
  sq_ctx_external_inv e op k :
    sqlang_is_final e = None -> sqlang_at_external (K e) op k ->
    exists k', sqlang_at_external e op k' /\ forall ov, k ov = K (k' ov)
}.

Record sq_pure_step (e1 e2 : C) : Prop := {
  sq_pure_step_safe m : sqlang_step e1 m [] e2 m;
  sq_pure_step_det m T e' m' :
    sqlang_step e1 m T e' m' -> T = [] /\ e' = e2 /\ m' = m
}.

Class SqPureExec (φ : Prop) (n : nat) (e1 e2 : C) : Prop :=
  sq_pure_exec : φ -> relations.nsteps sq_pure_step n e1 e2.

Class SqAtomicExternal `{!ExtSpecs L Σ} (op : @atomic_op Loc Val Layout Expr)
    (k : option Val -> C) : Prop :=
  sq_atomic_external_final x ov :
    ext_spec_post op x ov ⊢ ⌜is_Some (sqlang_is_final (k ov))⌝.

Section syntax_steps.
  Context `{!sqHeap L Σ}.

  Lemma sq_step_fill K e Ψ `{!SqContext K} :
    sqlang_is_final e = None ->
    sq_step e (λ e', Ψ (K e')) ⊢ sq_step (K e) Ψ.
  Proof.
    intros Hv. rewrite /sq_step. iIntros "H". iSplit.
    - iDestruct "H" as "[H _]". iIntros (m) "Hm".
      iMod ("H" with "Hm") as "[%Hr H]". iModIntro. iSplit.
      { iPureIntro. destruct Hr as (T & e2 & m2 & Hs).
        exists T, (K e2), m2. by apply sq_ctx_step. }
      iIntros (T e2 m2 Hs).
      destruct (sq_ctx_step_inv _ _ _ _ _ Hv Hs) as (e2' & -> & Hs').
      by iApply ("H" $! T e2' m2 with "[//]").
    - iDestruct "H" as "[_ H]". iIntros (m T e2 m2 Hs).
      destruct (sq_ctx_step_inv _ _ _ _ _ Hv Hs) as (e2' & -> & Hs').
      by iApply ("H" $! m T e2' m2 with "[//]").
  Qed.

  Lemma sq_step_pure e1 e2 Ψ : sq_pure_step e1 e2 -> ▷ Ψ e2 ⊢ sq_step e1 Ψ.
  Proof.
    intros [Hsafe Hdet]. rewrite /sq_step. iIntros "HΨ". iSplit.
    - iIntros (m) "Hm". iModIntro. iSplit.
      { iPureIntro. exists [], e2, m. apply Hsafe. }
      iIntros (T e' m' Hs).
      destruct (Hdet _ _ _ _ Hs) as (-> & -> & ->).
      iNext. iModIntro. iFrame.
    - iIntros (m T e' m' Hs).
      destruct (Hdet _ _ _ _ Hs) as (-> & -> & ->).
      iModIntro. iApply fp_tokens_nil.
  Qed.

  Lemma sq_pure_step_not_final e1 e2 :
    sq_pure_step e1 e2 -> sqlang_is_final e1 = None.
  Proof using Type*.
    intros Hpure. by apply (sqlang_step_not_final _ inhabitant [] e2 inhabitant), sq_pure_step_safe.
  Qed.

  Lemma sq_pure_step_ctx K e1 e2 `{!SqContext K} :
    sq_pure_step e1 e2 -> sq_pure_step (K e1) (K e2).
  Proof using Type*.
    intros Hpure. have Hv := sq_pure_step_not_final _ _ Hpure.
    destruct Hpure as [Hsafe Hdet]. split.
    - intros m. by apply sq_ctx_step, Hsafe.
    - intros m T e' m' Hs.
      destruct (sq_ctx_step_inv _ _ _ _ _ Hv Hs) as (e2' & -> & Hs').
      destruct (Hdet _ _ _ _ Hs') as (-> & -> & ->). done.
  Qed.
End syntax_steps.

Section exwp.
  Context `{!sqHeap L Σ, !invGS Σ, !ExtSpecs L Σ}.

  Lemma exwp_unfold E e Φ :
    EXWP e @ E {{ Φ }} ⊣⊢ exwp_pre exwp E e Φ.
  Proof. apply (fixpoint_unfold exwp_pre). Qed.

  Lemma exwp_value_fupd E e v Φ :
    sqlang_is_final e = Some v -> EXWP e @ E {{ Φ }} ⊣⊢ |={E}=> Φ v.
  Proof. intros Hv. by rewrite exwp_unfold /exwp_pre Hv. Qed.

  Lemma exwp_value E e v Φ :
    sqlang_is_final e = Some v -> Φ v ⊢ EXWP e @ E {{ Φ }}.
  Proof. intros Hv. rewrite (exwp_value_fupd _ _ _ _ Hv). apply fupd_intro. Qed.

  Lemma exwp_value' E e v Φ `{!SqIntoVal e v} : Φ v ⊢ EXWP e @ E {{ Φ }}.
  Proof. apply exwp_value, sq_into_val. Qed.

  Lemma fupd_exwp E e Φ : (|={E}=> EXWP e @ E {{ Φ }}) ⊢ EXWP e @ E {{ Φ }}.
  Proof. rewrite exwp_unfold /exwp_pre. apply fupd_trans. Qed.

  Lemma exwp_seq_unfold E e Φ :
    sqlang_is_final e = None -> (forall op k, ~ sqlang_at_external e op k) ->
    EXWP e @ E {{ Φ }} ⊣⊢
      |={E}=> sq_step e (λ e2, EXWP e2 @ E {{ Φ }}).
  Proof.
    intros Hv Hext. rewrite exwp_unfold /exwp_pre Hv.
    iSplit.
    - iIntros ">[[_ Hseq] | (%op & %k & %Hcall & _)]".
      + by iModIntro.
      + exfalso. by eapply Hext.
    - iIntros ">H !>". iLeft. iFrame. done.
  Qed.

  Lemma exwp_lift_external E e op k Φ :
    sqlang_at_external e op k ->
    (|={E,∅}=> ∃ x : ext_spec_args op,
      ext_spec_pre op x (λ ef, ▷ EXWP ef {{ _, True }}) ∗
      ▷ (∀ ov, ext_spec_post op x ov -∗ |={∅,E}=> EXWP k ov @ E {{ Φ }})) ⊢
    EXWP e @ E {{ Φ }}.
  Proof.
    intros Hext. rewrite exwp_unfold /exwp_pre
      (sqlang_external_not_final _ inhabitant _ _ Hext).
    iIntros "Hspec !>". iRight. iExists op, k. by iFrame.
  Qed.

  Lemma exwp_ext_unfold E e op k Φ :
    sqlang_at_external e op k ->
    EXWP e @ E {{ Φ }} ⊣⊢
      (|={E,∅}=> ∃ x : ext_spec_args op,
        ext_spec_pre op x (λ ef, ▷ EXWP ef {{ _, True }}) ∗
        ▷ (∀ ov, ext_spec_post op x ov -∗ |={∅,E}=> EXWP k ov @ E {{ Φ }})).
  Proof.
    intros He. iSplit; last by iApply (exwp_lift_external _ _ _ _ _ He).
    rewrite exwp_unfold /exwp_pre (sqlang_external_not_final _ inhabitant _ _ He).
    iIntros ">[[%Hno _] | (%op' & %k' & %He' & Hspec)]".
    - exfalso. by eapply Hno.
    - destruct (sqlang_external_det _ _ _ _ _ He He') as [-> Hk].
      iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
      iNext. iIntros (ov) "Hpost". rewrite -(Hk ov). by iApply "Hcont".
  Qed.

  (** Apply a selected external-call contract, restoring the caller's mask
      before invoking its continuation. *)
  Lemma exwp_ext_call_cont E e op k x Φ `{!SqAtExternal e op k} :
    (|={E}=> ext_spec_pre op x (λ ef, ▷ EXWP ef {{ _, True }})) -∗
    ▷ (∀ ov, ext_spec_post op x ov -∗ EXWP (k ov) @ E {{ Φ }}) -∗
    EXWP e @ E {{ Φ }}.
  Proof.
    iIntros "Hpre Hcont". iApply (exwp_lift_external _ _ _ _ _ sq_at_external).
    iMod "Hpre" as "Hpre".
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
    iModIntro. iExists x. iFrame "Hpre".
    iNext. iIntros (ov) "Hpost". iMod "Hclose" as "_".
    by iApply "Hcont".
  Qed.

  Lemma exwp_ext_call E e op k x v Q `{!SqAtExternal e op k} :
    (forall ov, ext_spec_post op x ov ⊢ ⌜sqlang_is_final (k ov) = Some v⌝ ∗ Q) ->
    {{{ |={E}=> ext_spec_pre op x (λ ef, ▷ EXWP ef {{ _, True }}) }}}
      EXWP e @ E {{{ RET v; Q }}}.
  Proof.
    intros Hpost Φ. iIntros "Hpre HΦ".
    iApply (exwp_ext_call_cont with "Hpre"). iNext. iIntros (ov) "Hpost".
    iDestruct (Hpost with "Hpost") as "[%Hv HQ]".
    iApply (exwp_value _ _ _ _ Hv). by iApply "HΦ".
  Qed.

  Lemma exwp_bind `{!sqOfVal} K E e Φ `{!SqContext K} :
    EXWP e @ E {{ v, EXWP K (sq_of_val v) @ E {{ Φ }} }} ⊢
    EXWP K e @ E {{ Φ }}.
  Proof.
    iLöb as "IH" forall (e). rewrite (exwp_unfold E e) /exwp_pre.
    destruct (sqlang_is_final e) as [v|] eqn:Hv.
    { rewrite -(sq_of_to_val _ _ Hv). iApply fupd_exwp. }
    rewrite exwp_unfold /exwp_pre (sq_ctx_not_final _ Hv).
    iIntros ">[[%Hno Hseq] | (%op & %k & %He & Hspec)] !>".
    - iLeft. iSplit.
      { iPureIntro. intros op k He.
        destruct (sq_ctx_external_inv _ _ _ Hv He) as (k' & He' & _).
        by eapply Hno. }
      iApply sq_step_fill; first done.
      iApply (sq_step_wand with "Hseq"). iIntros "!>" (e') "Hwp".
      by iApply "IH".
    - destruct (sq_ctx_external _ _ _ He) as (k' & He' & Hk).
      iRight. iExists op, k'. iSplit; first done.
      iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
      iNext. iIntros (ov) "Hpost". iMod ("Hcont" with "Hpost") as "Hwp".
      iModIntro. rewrite Hk. by iApply "IH".
  Qed.

  Lemma exwp_atomic_ext E1 E2 e op k Φ :
    sqlang_at_external e op k ->
    (forall x ov, ext_spec_post op x ov ⊢ ⌜is_Some (sqlang_is_final (k ov))⌝) ->
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
    rewrite !(exwp_value_fupd _ _ _ _ Hv).
    iMod "Hwp" as ">HΦ". by iModIntro.
  Qed.

  Lemma exwp_atomic E1 E2 {e op k} Φ `{!SqAtExternal e op k, !SqAtomicExternal op k} :
    (|={E1,E2}=> EXWP e @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢
      EXWP e @ E1 {{ Φ }}.
  Proof. apply (exwp_atomic_ext _ _ _ _ _ _ sq_at_external), sq_atomic_external_final. Qed.
End exwp.

Lemma tac_exwp_bind `{!sqHeap L Σ, !invGS Σ, !ExtSpecs L Σ, !sqOfVal}
    K Δ E Φ e `{!SqContext K} :
  envs_entails Δ (EXWP e @ E {{ v, EXWP K (sq_of_val v) @ E {{ Φ }} }})%I ->
  envs_entails Δ (EXWP K e @ E {{ Φ }}).
Proof. rewrite envs_entails_unseal => ->. apply (exwp_bind K). apply _. Qed.

(** ** Core-step lifting *)

(** Core rules handle expressions without an exposed external call,
    including final and stuck expressions. *)
Class NotAtExternal (e : C) : Prop :=
  not_at_external op k : ~ sqlang_at_external e op k.

Lemma not_at_external_of_step_or_value e m :
  is_Some (sqlang_is_final e) \/
    (exists T e' m', sqlang_step e m T e' m') -> NotAtExternal e.
Proof.
  intros [(v & Hv) | (T & e' & m' & Hstep)] op k Hext.
  - have Hnone := sqlang_external_not_final e m op k Hext. congruence.
  - by eapply sqlang_step_external_disjoint.
Qed.

Global Instance not_at_external_value `{!Inhabited Mem} e v `{!SqIntoVal e v} :
    NotAtExternal e | 100.
Proof.
  apply (not_at_external_of_step_or_value e inhabitant). left. exists v. apply sq_into_val.
Qed.

Section not_at_external_rules.
  Context `{!sqHeap L Σ, !invGS Σ, !ExtSpecs L Σ}.

  Lemma exwp_not_at_external_unfold E e Φ `{!NotAtExternal e} :
    EXWP e @ E {{ Φ }} ⊣⊢
    |={E}=> match sqlang_is_final e with
      | Some v => Φ v
      | None => sq_step e (λ e2, EXWP e2 @ E {{ Φ }})
      end.
  Proof.
    destruct (sqlang_is_final e) as [v|] eqn:Hv.
    - by apply (exwp_value_fupd _ _ _ _ Hv).
    - exact (exwp_seq_unfold _ _ _ Hv not_at_external).
  Qed.

  Lemma exwp_not_at_external E e Φ `{!NotAtExternal e} :
    (|={E}=> match sqlang_is_final e with
      | Some v => Φ v
      | None => sq_step e (λ e2, EXWP e2 @ E {{ Φ }})
      end) ⊢ EXWP e @ E {{ Φ }}.
  Proof.
    by rewrite (exwp_not_at_external_unfold E e Φ).
  Qed.

  Lemma exwp_pure_step E e1 e2 Φ :
    sq_pure_step e1 e2 -> ▷ EXWP e2 @ E {{ Φ }} ⊢ EXWP e1 @ E {{ Φ }}.
  Proof.
    intros Hpure. have Hstep : sqlang_step e1 inhabitant [] e2 inhabitant.
    { exact (sq_pure_step_safe _ _ Hpure _). }
    have ? : NotAtExternal e1.
    { apply (not_at_external_of_step_or_value e1 inhabitant). right. by do 3 eexists. }
    iIntros "Hwp". iApply exwp_not_at_external.
    rewrite (sqlang_step_not_final _ _ _ _ _ Hstep).
    iModIntro. by iApply sq_step_pure.
  Qed.

  Lemma exwp_pure_steps E e1 e2 Φ n :
    relations.nsteps sq_pure_step n e1 e2 ->
    ▷^n EXWP e2 @ E {{ Φ }} ⊢ EXWP e1 @ E {{ Φ }}.
  Proof.
    induction 1 as [e | n e1 e2 e3 Hs Hsteps IH]; first done.
    simpl. iIntros "H". iApply (exwp_pure_step _ _ _ _ Hs).
    iNext. by iApply IH.
  Qed.

  Lemma exwp_pure_exec E e1 e2 {φ n} Φ `{!SqPureExec φ n e1 e2} :
    φ -> ▷^n EXWP e2 @ E {{ Φ }} ⊢ EXWP e1 @ E {{ Φ }}.
  Proof. intros Hφ. apply exwp_pure_steps. by apply sq_pure_exec. Qed.

End not_at_external_rules.

Lemma tac_exwp_pure `{!sqHeap L Σ, !invGS Σ, !ExtSpecs L Σ}
    K Δ Δ' E e1 e2 φ n Φ `{!SqContext K} :
  SqPureExec φ n e1 e2 -> φ -> MaybeIntoLaterNEnvs n Δ Δ' ->
  envs_entails Δ' (EXWP K e2 @ E {{ Φ }}) ->
  envs_entails Δ (EXWP K e1 @ E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal => Hexec Hφ ? HΔ.
  rewrite into_laterN_env_sound HΔ. apply exwp_pure_steps.
  have Hmap : forall n' e e', relations.nsteps sq_pure_step n' e e' ->
      relations.nsteps sq_pure_step n' (K e) (K e').
  { intros n' e e' Hsteps. induction Hsteps as [e | n' e e' e'' Hs Hsteps IH];
      first constructor.
    econstructor; first by apply sq_pure_step_ctx. exact IH. }
  apply Hmap. by apply sq_pure_exec.
Qed.

End language_rules.
