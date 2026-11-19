(** Adequacy of generic EXWP for the atomic machine. *)
From stdpp Require Import relations.
From iris.proofmode Require Import proofmode.
Require Export VST.atomic_machine.sqex_logic.

Set Default Proof Using "Type*".

Section language.
  Context `{L : !@sqlang Loc Val LocEqDec LocCountable Mem Layout Expr}.
  Local Notation C := (@sqlang_thrd_st _ _ _ _ _ _ _ L).

(** Soundness of all external call specifications. *)
Class ExtSpecsSound {Σ : gFunctors}
    `{!ExtSpecs L Σ, !sqHeap L Σ} : Prop :=
  ext_specs_soundness : forall op, ext_call_soundness (ext_spec op) op.

(** ** The statement *)

Definition into_tpool (es : list C) : am_tpool := map_seq 0%nat es.

(** If thread [i] has returned a value [v], then [v] satisfies the
    postcondition of thread [i] in [φs] (if it has one). *)
Definition postcond_ok (φs : list (Val -> Prop)) (i : nat) (e : C) : Prop :=
  forall v φ, sqlang_is_final e = Some v -> φs !! i = Some φ -> φ v.

(* FIXME consolidate with am_safe *)
Definition at_sem_adequate (es : list C) (φs : list (Val -> Prop)) (m : Mem) : Prop :=
  forall tp' m',
    am_steps (AMCfg (into_tpool es) m) (AMCfg tp' m') ->
    ~ am_race (AMCfg tp' m') /\
    (forall i e, tp' !! i = Some e -> am_not_stuck e m') /\
    (forall i e, tp' !! i = Some e -> postcond_ok φs i e).

(** A step is sequential, or executes an exposed external call. *)
Lemma sqex_at_step_cases e m evs e' m' o :
  at_step e m evs e' m' o ->
  (exists T, sqlang_step e m T e' m' /\ evs = NA <$> T /\ o = None) \/
  (exists op K, sqlang_at_external e op K).
Proof. destruct 1; [left; by eexists | right; by do 2 eexists ..]. Qed.

(** ** Footprints of predicted steps *)

Section footprints.
  Context `{!sqHeap L Σ, !invGS Σ, !ExtSpecs L Σ, !ExtSpecsSound}.

  (** A sequential step's footprint is owned by the thread before the step. *)
  Lemma sqex_seq_own (e : C) Φ m T e' m' la wa ev :
    sqlang_step e m T e' m' -> ev ∈ T -> mem_ev_need_full_loc ev = Some (la, wa) ->
    EXWP e {{ Φ }} ={⊤}=∗ fp_own la wa.
  Proof.
    intros Hs Hin Hacc. iIntros "Hwp".
    have Hv := sqlang_step_not_final _ _ _ _ _ Hs.
    have Hno : forall op k, ~ sqlang_at_external e op k
      by intros op k Hext; eapply sqlang_step_external_disjoint.
    rewrite (exwp_seq_unfold _ _ _ Hv Hno). iMod "Hwp" as "[_ Hfp]".
    iMod ("Hfp" $! m T e' m' with "[//]") as "Hfp".
    iModIntro. by iApply (fp_tokens_elem with "Hfp").
  Qed.

  (** An atomic step's footprint is in the precondition of its call. *)
  Lemma sqex_atomic_own (e : C) Φ m evs e' m' o la wa ev :
    at_step e m evs e' m' o -> ev ∈ evs -> am_atomic ev = true ->
    ev_access ev la wa ->
    EXWP e {{ Φ }} ={⊤,∅}=∗ fp_own la wa.
  Proof.
    intros Hst Hin Ha Hacc. iIntros "Hwp".
    destruct (sqex_at_step_cases _ _ _ _ _ _ Hst) as [(T & _ & -> & _) | (op & k & Hext)].
    { apply list_elem_of_fmap in Hin as (ev' & -> & _). simpl in Ha. discriminate. }
    iEval (rewrite (exwp_ext_unfold _ _ _ _ _ Hext)) in "Hwp".
    iMod "Hwp" as "Hcall".
    iMod (ext_call_open _ _ _ _ with "Hcall") as (x) "[Hpre _]". iModIntro.
    by iApply (ext_footprint_pf _ op (ext_specs_soundness op) with "Hpre").
  Qed.

  (** The footprint of any step is owned by the thread before the step. *)
  Lemma sqex_step_own (e : C) Φ m evs e' m' o la wa ev :
    at_step e m evs e' m' o -> ev ∈ evs ->
    ev_access ev la wa ->
    EXWP e {{ Φ }} ={⊤,∅}=∗ fp_own la wa.
  Proof.
    intros Hst Hin Hacc. iIntros "Hwp".
    destruct (at_step_events _ _ _ _ _ _ Hst) as [(T & Hs & ->) | Hat].
    - apply list_elem_of_fmap in Hin as (ev' & -> & Hev').
      iMod (sqex_seq_own with "Hwp") as "$"; [exact Hs | exact Hev' | exact Hacc | ].
      by iApply fupd_mask_intro_discard.
    - have Ha : am_atomic ev = true by rewrite Forall_forall in Hat; apply Hat.
      by iApply (sqex_atomic_own with "Hwp").
  Qed.

  Local Lemma sqex_alloc_access {ei ej m evs1 evs2 ei' ej' m1 m2 o1 o2 l ev w Φ} :
    at_step ei m evs1 ei' m1 o1 -> NA (Alloc l) ∈ evs1 ->
    at_step ej m evs2 ej' m2 o2 -> ev ∈ evs2 -> ev_access ev l w ->
    sq_heap m -∗ EXWP ej {{ Φ }} ={⊤,∅}=∗ False.
  Proof.
    intros Halloc Hin Hstep Hev Hacc.
    destruct (at_step_events _ _ _ _ _ _ Halloc) as [(T & Hs & ->) | Hat].
    2: { rewrite Forall_forall in Hat. discriminate (Hat _ Hin). }
    apply list_elem_of_fmap in Hin as (a & Heq & Hin). injection Heq as <-.
    iIntros "Hm Hwp". iMod (sqex_step_own with "Hwp") as "Hl"; [exact Hstep | exact Hev | exact Hacc |].
    destruct w; [iDestruct "Hl" as (v) "Hl" | iDestruct "Hl" as (q v) "Hl"];
      by iDestruct (sq_pointsto_alloc_excl _ _ Hs Hin with "Hm Hl") as "[]".
  Qed.

  (** One step of a thread, with the WP of the thread it spawns (if any). *)
  Lemma sqex_thread_step (e : C) Ψ m evs e' m' o :
    at_step e m evs e' m' o ->
    EXWP e {{ Ψ }} -∗ sq_heap m ={⊤,∅}=∗ ▷ |={∅,⊤}=>
      sq_heap m' ∗ EXWP e' {{ Ψ }} ∗ from_option (λ ef, EXWP ef {{ _, True }}) True o.
  Proof.
    intros Hst. iIntros "Hwp Hm".
    destruct (sqex_at_step_cases _ _ _ _ _ _ Hst) as [(T & Hs & -> & ->) | (op & k & Hext)].
    - (* A core step. *)
      have Hv := sqlang_step_not_final _ _ _ _ _ Hs.
      have Hno : forall op k, ~ sqlang_at_external e op k
        by intros op k Hext; eapply sqlang_step_external_disjoint.
      rewrite (exwp_seq_unfold _ _ _ Hv Hno). iMod "Hwp" as "[Hwp _]".
      iMod ("Hwp" with "Hm") as "[_ Hwp]".
      iSpecialize ("Hwp" $! T e' m' with "[//]").
      iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iNext.
      iMod "Hwp" as "[$ $]". by iMod "Hclose" as "_".
    - (* An external call: its specification gives the step. *)
      iEval (rewrite (exwp_ext_unfold _ _ _ _ _ Hext)) in "Hwp".
      iMod "Hwp" as "Hcall".
      iMod (ext_call_open _ _ _ _ with "Hcall") as (x) "[Hpre Hcont]".
      iMod (ext_step_pf _ op (ext_specs_soundness op) with "Hpre Hm") as (ov) "(-> & Hm & Hpost & Ho)";
        [exact Hext | exact Hst | ].
      iModIntro. destruct o as [e_new|]; simpl; iNext;
        iMod ("Hcont" with "Hpost") as "Hwp"; iModIntro; iFrame.
  Qed.
End footprints.

(** ** The invariant *)

Section adequacy.
  Context `{!sqHeap L Σ, !invGS Σ, !ExtSpecs L Σ, !ExtSpecsSound}.
  Context (φ : Val -> Prop).

  (** Thread 0 is the initial thread; spawned threads have postcondition True. *)
  Definition sqex_post (i : nat) : Val -> iProp Σ :=
    if decide (i = 0%nat) then (λ v, ⌜φ v⌝)%I else (λ _, True)%I.

  Definition sqex_threads (tp : am_tpool) : iProp Σ :=
    [∗ map] i ↦ e ∈ tp, EXWP (e : C) {{ sqex_post i }}.

  Definition sqex_inv (tp : am_tpool) (m : Mem) : iProp Σ :=
    sq_heap m ∗ ⌜is_Some (tp !! 0%nat)⌝ ∗ sqex_threads tp.

  Lemma sqex_inv_zero (tp : am_tpool) (i : nat) (e : C) :
    is_Some (tp !! 0%nat) -> is_Some (<[i := e]> tp !! 0%nat).
  Proof. intros H0. rewrite lookup_insert_is_Some'. by right. Qed.

  Lemma am_step_preserves_sqex_inv tp m i evs tp' m' :
    am_step (AMCfg tp m) i evs (AMCfg tp' m') ->
    sqex_inv tp m ⊢ |={⊤,∅}=> ▷ |={∅,⊤}=> sqex_inv tp' m'.
  Proof.
    iIntros (Hmach) "(Hm & %H0 & Hts)". rewrite /sqex_threads.
    inversion Hmach; subst; rename Hstep into Htstep;
      iDestruct (big_sepM_delete _ _ i with "Hts") as "[Ht Hts]"; try done;
      iMod (sqex_thread_step with "Ht Hm") as "Hstep"; try done;
      iModIntro; iNext; iMod "Hstep" as "(Hm & Hwp & Ho)"; iModIntro; iFrame "Hm";
      simpl.
    - iSplit; first (iPureIntro; by apply sqex_inv_zero).
      iApply big_sepM_insert_delete. iFrame.
    - (* The spawned thread gets an unused index other than 0. *)
      have Hne : i ≠ j by intros ->; congruence.
      have Hj0 : j ≠ 0%nat.
      { intros ->. destruct H0 as [e0 He0]. rewrite Hfree in He0. discriminate. }
      iSplit; first (iPureIntro; by do 2 apply sqex_inv_zero).
      iApply big_sepM_insert; first by rewrite lookup_insert_ne.
      iSplitL "Ho".
      { rewrite /sqex_post decide_False //. }
      iApply big_sepM_insert_delete. iFrame.
  Qed.

  (** ** The invariant implies safety *)

  Lemma sqex_inv_thread_ok tp m i e :
    tp !! i = Some e ->
    sqex_inv tp m ⊢ |={⊤,∅}=> |={∅}▷=>
      ⌜am_not_stuck e m ∧ postcond_ok [φ] i e⌝.
  Proof.
    iIntros (Hi) "(Hm & _ & Hts)".
    iDestruct (big_sepM_lookup with "Hts") as "Ht"; first done.
    iEval (rewrite exwp_unfold /exwp_pre) in "Ht".
    destruct (sqlang_is_final e) as [v|] eqn:Hv.
    { iMod "Ht" as "Hpost".
      iAssert (⌜i = 0%nat -> φ v⌝)%I with "[Hpost]" as %Hφ.
      { destruct (decide (i = 0%nat)) as [->|Hne].
        - iEval (rewrite /sqex_post /=) in "Hpost". iDestruct "Hpost" as %Hφ.
          iPureIntro. by intros _.
        - iPureIntro. by intros ?. }
      iApply fupd_mask_intro_discard; first set_solver.
      iApply step_fupd_intro; first done. iNext. iPureIntro. split.
      - left. by exists v.
      - intros v0 φ0 Hv0 [-> <-]%list_lookup_singleton_Some.
        rewrite Hv in Hv0. injection Hv0 as <-. by apply Hφ. }
    iMod "Ht" as "[[%Hno [Hseq _]] | (%op & %k & %He & Hspec)]".
    - (* A core step. *)
      iMod ("Hseq" with "Hm") as "[%Hred _]".
      iApply fupd_mask_intro_discard; first set_solver.
      iApply step_fupd_intro; first done. iNext. iPureIntro. split.
      + right. destruct Hred as (T & e2 & m2 & Hs). do 4 eexists. by apply Core_Step.
      + intros v0 ? Hv0. congruence.
    - (* An external call: its precondition enables the machine step. *)
      iMod (ext_call_open _ _ _ _ with "Hspec") as (x) "[Hpre _]".
      iDestruct (ext_enabled_pf _ op (ext_specs_soundness op) with "Hpre Hm") as %Hen; first exact He.
      iModIntro. iApply step_fupd_intro; first done. iNext. iPureIntro.
      split; [by right | intros v0 ? Hv0; congruence].
  Qed.

  (** A race between a sequential step of [i] and any step of [j] would
      need incompatible ownership. *)
  Lemma sqex_threads_no_race_seq tp m i j ei ej T evs2 ei' ej' m1 m2 o2
      ev1 ev2 l w1 w2 :
    i ≠ j -> tp !! i = Some ei -> tp !! j = Some ej ->
    sqlang_step ei m T ei' m1 -> at_step ej m evs2 ej' m2 o2 ->
    ev1 ∈ (NA <$> T) -> ev2 ∈ evs2 ->
    ev_access ev1 l w1 -> ev_access ev2 l w2 -> w1 = true \/ w2 = true ->
    sqex_threads tp ⊢ |={⊤,∅}=> False.
  Proof.
    intros Hij Hi Hj Hs Hst He1 He2 Hacc1 Hacc2 Hw.
    apply list_elem_of_fmap in He1 as (ev & -> & Hev1).
    iIntros "Hts". rewrite /sqex_threads.
    iDestruct (big_sepM_delete _ _ i with "Hts") as "[Hi Hts]"; first done.
    iDestruct (big_sepM_lookup _ _ j with "Hts") as "Hj"; first by rewrite lookup_delete_ne.
    (* Extract [i]'s sequential footprint at [⊤] before [j]'s footprint
       potentially changes the mask to [∅] for an external call. *)
    iMod (sqex_seq_own with "Hi") as "Hown1"; [exact Hs | exact Hev1 | exact Hacc1 | ].
    iMod (sqex_step_own with "Hj") as "Hown2"; [exact Hst | exact He2 | exact Hacc2 | ].
    by iDestruct (fp_own_excl _ _ _ Hw with "Hown1 Hown2") as "[]".
  Qed.

  Lemma sqex_inv_no_race tp m i j ei ej evs1 evs2 ei' ej' m1 m2 o1 o2 :
    i ≠ j -> tp !! i = Some ei -> tp !! j = Some ej ->
    at_step ei m evs1 ei' m1 o1 -> at_step ej m evs2 ej' m2 o2 ->
    am_conflicts evs1 evs2 ->
    sqex_inv tp m ⊢ |={⊤,∅}=> |={∅}▷=> ⌜False⌝.
  Proof.
    intros Hij Hi Hj H1 H2 Hconf. iIntros "(Hm & _ & Hts)".
    have Hseq := am_conflicts_seq _ _ _ _ _ _ _ _ _ _ _ H1 H2 Hconf.
    destruct Hconf as (ev1 & ev2 & He1 & He2 & [(l & Hl1 & Hl2) Hkind]).
    destruct (am_event_access_or_alloc ev1 l Hl1) as [-> | (w1 & Hacc1)];
      destruct (am_event_access_or_alloc ev2 l Hl2) as [-> | (w2 & Hacc2)].
    - discriminate.
    - iDestruct (big_sepM_lookup with "Hts") as "Hj"; first exact Hj.
      by iMod (sqex_alloc_access H1 He1 H2 He2 Hacc2 with "Hm Hj") as "[]".
    - iDestruct (big_sepM_lookup with "Hts") as "Hi"; first exact Hi.
      by iMod (sqex_alloc_access H2 He2 H1 He1 Hacc1 with "Hm Hi") as "[]".
    - have Hw := am_conflicting_access_write _ _ _ _ _ Hkind Hacc1 Hacc2.
      destruct Hseq as [(T & Hs & ->) | (T & Hs & ->)].
      + by iMod (sqex_threads_no_race_seq with "Hts") as "[]".
      + iMod (sqex_threads_no_race_seq _ _ j i with "Hts") as "[]"; naive_solver.
  Qed.

  Lemma sqex_sound n tp m tp' m' (P : Prop) :
    relations.nsteps am_step_any n (AMCfg tp m) (AMCfg tp' m') ->
    (sqex_inv tp' m' ⊢ |={⊤,∅}=> |={∅}▷=> ⌜P⌝) ->
    sqex_inv tp m ⊢ |={⊤,∅}=> |={∅}▷=>^(S n) ⌜P⌝.
  Proof.
    intros Hsteps Hend. revert tp m Hsteps.
    induction n as [|n IH]; intros tp m Hsteps.
    - inversion Hsteps; subst. exact Hend.
    - inversion Hsteps as [|n0 cfg1 [tp2 m2] cfg3 (i & evs & Hfirst) Htail]; subst.
      iIntros "Hinv". iMod (am_step_preserves_sqex_inv with "Hinv") as "Hinv"; first done.
      iModIntro. rewrite Nat.iter_succ. iModIntro. iNext. iMod "Hinv".
      by iApply (IH with "Hinv").
  Qed.
End adequacy.

Class sqGS (Σ : gFunctors) := HeapGS {
  sqGS_heap :: sqHeap L Σ;
  sqGS_extspecs :: ExtSpecs L Σ;
  sqGS_extspecs_sound :: ExtSpecsSound
}.

Theorem sqex_adequacy_gen (Σ : gFunctors) `{!invGpreS Σ} (e : C) (φ : Val -> Prop) (m : Mem) :
  (forall `{!invGS Σ},
    (* if we have *some* sqGS and can prove wp.
       compare with wp_adequacy_gen *)
    ⊢ |={⊤}=> ∃ _ : sqGS Σ,
      sq_heap m ∗ exwp ⊤ e (λ v, ⌜φ v⌝)) ->
  at_sem_adequate [e] [φ] m.
Proof.
  intros Hinit tp' m' Hrtc.
  change (am_steps (AMCfg {[0%nat := e]} m) (AMCfg tp' m')) in Hrtc.
  destruct (rtc_nsteps_1 _ _ Hrtc) as [n Hsteps].
  assert (Hsound : forall P : Prop,
    (forall (Hinv : invGS Σ) (G : sqGS Σ),
      sqex_inv φ tp' m' ⊢ |={⊤,∅}=> |={∅}▷=> ⌜P⌝) -> P).
  { intros P HP. apply (pure_soundness (PROP := iPropI Σ)).
    apply (step_fupdN_soundness_lc (Σ := Σ) _ (S n) 0). intros Hinv. iIntros "_".
    iMod (Hinit Hinv) as (G) "[Hheap Hwp]".
    iApply (sqex_sound φ n with "[Hheap Hwp]");
      [exact Hsteps | exact (HP Hinv G) | ].
    iSplitL "Hheap"; first iExact "Hheap".
    iSplit; first (iPureIntro; by rewrite lookup_singleton_eq).
    rewrite /sqex_threads big_sepM_singleton /sqex_post /=. iExact "Hwp". }
  have Hend : forall i e0, tp' !! i = Some e0 ->
      am_not_stuck e0 m' /\ postcond_ok [φ] i e0.
  { intros i e0 Hi. apply Hsound. intros ? ?.
    by apply sqex_inv_thread_ok. }
  split; [|split].
  - intros (i & j & ei & ej & evs1 & evs2 & ei' & ej' & m1 & m2 & o1 & o2 &
      Hij & Hi & Hj & Hstep1 & Hstep2 & Hc).
    apply (Hsound False). intros ? ?.
    by eapply sqex_inv_no_race.
  - intros i e0 Hi. exact (proj1 (Hend i e0 Hi)).
  - intros i e0 Hi. exact (proj2 (Hend i e0 Hi)).
Qed.

End language.
