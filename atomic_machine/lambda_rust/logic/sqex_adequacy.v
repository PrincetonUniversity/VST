(** * Adequacy of EXWP for the atomic machine. *)
From stdpp Require Import relations.
From iris.algebra Require Import auth gmap frac.
From iris.proofmode Require Import proofmode.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_logic.

Set Default Proof Using "Type*".
#[local] Set Warnings "-redundant-canonical-projection".
Local Existing Instance lrSqGS_invGS.

Class lrSqGpreS Σ := LrSqGpreS {
  lrSqGpreS_inv :: invGpreS Σ;
  lrSqGpreS_heap :: inG Σ (authR sq_heapUR);
  lrSqGpreS_heap_freeable :: inG Σ (authR sq_freeableUR)
}.

Definition lrSqΣ : gFunctors :=
  #[invΣ;
    GFunctor (constRF (authR sq_heapUR));
    GFunctor (constRF (authR sq_freeableUR))].
Global Instance subG_lrSqGpreS {Σ} : subG lrSqΣ Σ -> lrSqGpreS Σ.
Proof. solve_inG. Qed.

(** ** The statement *)

Notation sqex_tpool := (am_tpool (L := lr_language)).

Definition sqex_pool (es : list sq_expr) : sqex_tpool := map_seq 0%nat es.

(** If thread [i] has returned a value [v], then [v] satisfies the
    postcondition of thread [i] in [φs] (if it has one). *)
Definition postcond_ok (φs : list (sq_val -> Prop)) (i : nat) (e : sq_expr) : Prop :=
  forall v φ, to_val e = Some v -> φs !! i = Some φ -> φ v.

Definition at_sem_adequate (es : list sq_expr) (φs : list (sq_val -> Prop)) (m : lr_mem) : Prop :=
  forall tp' m',
    am_steps (AMCfg (sqex_pool es) m) (AMCfg tp' m') ->
    ~ am_race (AMCfg tp' m') /\
    (forall i e, tp' !! i = Some e -> am_not_stuck e m') /\
    (forall i e, tp' !! i = Some e -> postcond_ok φs i e).

(** The adequacy works for any external calls, as long as their specs satisfy
  the properties defined below. *)
Section ext_sound.
  Context `{!lrSqGS Σ} (spec : ExtSpec lr_language Σ)
    (op : @atomic_op loc val lr_layout expr).

  (** PRE and SI imply that the call has a corr. at_step. *)
  Definition ext_enabled : Prop :=
    forall (e : sq_expr) k x (W : sq_expr -> iProp Σ) m,
      lr_external e op k ->
      ⊢ ext_pre spec x W -∗ sq_heap m -∗
        ⌜exists evs e' m' o, at_step e m evs e' m' o⌝.

  (** PRE and SI can be updated to POST, SI' and WP of the spawned thread (encoded as [W]). *)
  Definition ext_step : Prop :=
    forall (e : sq_expr) k x (W : sq_expr -> iProp Σ) m evs e' m' o,
      lr_external e op k -> at_step e m evs e' m' o ->
      ⊢ ext_pre spec x W -∗ sq_heap m ==∗
        ∃ ov, ⌜e' = k ov⌝ ∗ sq_heap m' ∗ ext_post spec x ov ∗ from_option W True o.

  (** For each emitted event, the precondition owns enough points-to to
      emit it. (FIXME: is this too strict?) *)
  Definition ext_footprint : Prop :=
    forall (e : sq_expr) k x (W : sq_expr -> iProp Σ) m evs e' m' o ev l w,
      lr_external e op k -> at_step e m evs e' m' o -> ev ∈ evs ->
      ev_need_full_loc ev = Some (l, w) ->
      ⊢ ext_pre spec x W -∗ fp_own l w.
End ext_sound.

(** Soundness of one external call. *)
Record ExtSound `{!lrSqGS Σ} (spec : ExtSpec lr_language Σ)
    (op : @atomic_op loc val lr_layout expr) : Prop := {
  ext_enabled_pf : ext_enabled spec op;
  ext_step_pf : ext_step spec op;
  ext_footprint_pf : ext_footprint spec op;
}.

(** Soundness of all external call specs. *)
Class ExtSpecsSound `{!lrSqGS Σ} (specs : ExtSpecs lr_language Σ) := {
  ext_specs_enabled op : ext_enabled (specs op) op;
  ext_specs_step op : ext_step (specs op) op;
  ext_specs_footprint op : ext_footprint (specs op) op;
}.

(** Inverts a machine step of an external call [op] whose continuation is
    [k]: the step is one for [op], with a continuation equal to [k] ([Hk]). *)
Local Ltac ext_inv He Hst :=
  inversion Hst; subst;
  try (exfalso; by eapply lr_step_external_disjoint);
  match goal with H : sqlang_at_external _ _ _ |- _ =>
    destruct (lr_external_det _ _ _ _ _ He H) as [Hop Hk]; try discriminate Hop;
    injection Hop; intros; subst
  end.

Section sc_ext_specs_sound.
  Context `{!lrSqGS Σ}.

  Lemma sc_load_sound ly l : ExtSound (sc_load_spec l) (ALoad ly l).
  Proof.
    split.
    - intros e k [q w] W m He. iIntros "Hpre Hm". simpl.
      iDestruct (sq_heap_read with "Hm Hpre") as %Hw. iPureIntro.
      do 4 eexists. eapply SC_Read; [exact He | exact Hw].
    - intros e k [q w] W m evs e' m' o He Hst. iIntros "Hpre Hm".
      ext_inv He Hst. simpl.
      iDestruct (sq_heap_read with "Hm Hpre") as %Hw.
      simpl in Hload. rewrite Hload in Hw. injection Hw as <-.
      iModIntro. iExists (Some v). iFrame. by rewrite Hk.
    - intros e k [q w] W m evs e' m' o ev l' w' He Hst Hin Hacc. iIntros "Hpre".
      ext_inv He Hst.
      simpl in Hin. apply list_elem_of_singleton in Hin as ->. injection Hacc as <- <-.
      rewrite /fp_own. by iExists q, w.
  Qed.

  Lemma sc_store_sound ly l v : ExtSound (sc_store_spec l v) (AStore ly l v).
  Proof.
    split.
    - intros e k w W m He. iIntros "Hpre Hm". simpl.
      iDestruct (sq_heap_read with "Hm Hpre") as %Hw. iPureIntro.
      do 4 eexists. eapply SC_Write; [exact He | by rewrite /= Hw].
    - intros e k w W m evs e' m' o He Hst. iIntros "Hpre Hm".
      ext_inv He Hst. simpl.
      iDestruct (sq_heap_read with "Hm Hpre") as %Hw.
      rewrite /= Hw in Hstore. injection Hstore as <-.
      iMod (sq_heap_write with "Hm Hpre") as "[Hm Hl]".
      iModIntro. iExists None. iFrame. by rewrite Hk.
    - intros e k w W m evs e' m' o ev l' w' He Hst Hin Hacc. iIntros "Hpre".
      ext_inv He Hst.
      simpl in Hin. apply list_elem_of_singleton in Hin as ->. injection Hacc as <- <-.
      by iApply fp_own_full.
  Qed.

  Lemma sc_cas_sound ly l v_exp v_new :
    ExtSound (sc_cas_spec l v_exp v_new) (ACAS ly l v_exp v_new).
  Proof.
    split.
    - intros e k [z_cur z_exp] W m He. iIntros "Hpre Hm". simpl.
      iDestruct "Hpre" as "[-> Hl]".
      iDestruct (sq_heap_read with "Hm Hl") as %Hw. iPureIntro.
      destruct (decide (z_cur = z_exp)) as [<-|Hne].
      + do 4 eexists. eapply (SC_Cas_Suc _ _ _ _ _ _ (LitV (LitInt z_cur)));
          [exact He | exact Hw | | by rewrite /= Hw].
        change (sq_mem.lit_eq m (LitInt z_cur) (LitInt z_cur)). constructor.
      + do 4 eexists. eapply (SC_Cas_Fail _ _ _ _ _ _ (LitV (LitInt z_cur)));
          [exact He | exact Hw | ].
        change (lit_neq (LitInt z_exp) (LitInt z_cur)). constructor. done.
    - intros e k [z_cur z_exp] W m evs e' m' o He Hst. iIntros "Hpre Hm".
      ext_inv He Hst; simpl; iDestruct "Hpre" as "[-> Hl]";
        iDestruct (sq_heap_read with "Hm Hl") as %Hw;
        simpl in Hload; rewrite Hload in Hw; injection Hw as ->.
      + (* Success *)
        apply lr_lit_eq_int in Heq. subst.
        rewrite /= Hload in Hstore. injection Hstore as <-.
        iMod (sq_heap_write with "Hm Hl") as "[Hm Hl]".
        iModIntro. iExists (Some (LitV (lit_of_bool true))). iFrame.
        rewrite bool_decide_true // decide_True //. iFrame. by rewrite Hk.
      + (* Failure *)
        apply lr_lit_neq_int in Hneq.
        have Hne : z_cur ≠ z_exp by intros ?; apply Hneq.
        iModIntro. iExists (Some (LitV (lit_of_bool false))). iFrame.
        rewrite bool_decide_false // decide_False //. iFrame. by rewrite Hk.
    - intros e k [z_cur z_exp] W m evs e' m' o ev l' w' He Hst Hin Hacc. iIntros "Hpre".
      ext_inv He Hst;
        simpl in Hin; apply list_elem_of_singleton in Hin as ->; injection Hacc as <- <-;
        iDestruct "Hpre" as "[_ Hl]"; by iApply fp_own_full.
  Qed.

  Lemma sc_spawn_sound e_new : ExtSound (sc_spawn_spec e_new) (ASpawn e_new).
  Proof.
    split.
    - intros e k [] W m He. iIntros "Hpre Hm". iPureIntro.
      do 4 eexists. by eapply Spawn.
    - (* The precondition is the spawned thread's [W]. *)
      intros e k [] W m evs e' m' o He Hst. iIntros "Hpre Hm".
      ext_inv He Hst. iModIntro. iExists None. iFrame. by rewrite Hk.
    - intros e k [] W m evs e' m' o ev l' w' He Hst Hin Hacc.
      ext_inv He Hst. by apply elem_of_nil in Hin.
  Qed.

  Lemma ext_sound op : ExtSound (ext_specs op) op.
  Proof.
    destruct op as [ly l|ly l v|ly l v_exp v_new|e];
      [apply sc_load_sound | apply sc_store_sound | apply sc_cas_sound | apply sc_spawn_sound].
  Qed.

  Global Instance ext_specs_sound : ExtSpecsSound ext_specs.
  Proof.
    split; intros op; [apply ext_enabled_pf | apply ext_step_pf | apply ext_footprint_pf];
      apply ext_sound.
  Qed.
End sc_ext_specs_sound.

(** ** Footprints of predicted steps *)

Section footprints.
  Context `{!lrSqGS Σ, specs : !ExtSpecs lr_language Σ, !ExtSpecsSound specs}.

  (** A sequential step's footprint is owned by the thread before the step. *)
  Lemma sqex_seq_own (e : sq_expr) Φ m T e' m' la wa ev :
    lr_step e m T e' m' -> ev ∈ T -> ev_need_full_loc (NA ev) = Some (la, wa) ->
    EXWP e {{ Φ }} ==∗ fp_own la wa.
  Proof.
    intros Hs Hin Hacc. iIntros "Hwp".
    have Hv := lr_step_not_val _ _ _ _ _ Hs.
    have Hno : forall op k, ~ lr_external e op k
      by intros op k Hext; eapply lr_step_external_disjoint.
    rewrite (exwp_seq_unfold _ _ _ Hv Hno). iDestruct "Hwp" as "[_ Hfp]".
    iMod ("Hfp" $! m T e' m' with "[//]") as "Hfp".
    iModIntro. by iApply (fp_tokens_elem with "Hfp").
  Qed.

  (** An atomic step's footprint is in the precondition of its call. *)
  Lemma sqex_atomic_own (e : sq_expr) Φ m evs e' m' o la wa ev :
    at_step e m evs e' m' o -> ev ∈ evs -> am_atomic ev = true ->
    ev_need_full_loc ev = Some (la, wa) ->
    EXWP e {{ Φ }} ={⊤,∅}=∗ fp_own la wa.
  Proof.
    intros Hst Hin Ha Hacc. iIntros "Hwp".
    destruct (at_step_cases _ _ _ _ _ _ Hst) as [(T & _ & -> & _) | (op & k & Hext)].
    { apply list_elem_of_fmap in Hin as (ev' & -> & _). simpl in Ha. discriminate. }
    iEval (rewrite (exwp_ext_unfold _ _ _ _ _ Hext)) in "Hwp".
    iMod "Hwp" as (x) "[Hpre _]". iModIntro.
    by iApply (ext_specs_footprint op with "Hpre").
  Qed.

  (** The footprint of any step is owned by the thread before the step. *)
  Lemma sqex_step_own (e : sq_expr) Φ m evs e' m' o la wa ev :
    at_step e m evs e' m' o -> ev ∈ evs ->
    ev_need_full_loc ev = Some (la, wa) ->
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

  (** One step of a thread, with the WP of the thread it spawns (if any). *)
  Lemma sqex_thread_step (c : sq_expr) Ψ m evs c' m' o :
    at_step c m evs c' m' o ->
    EXWP c {{ Ψ }} -∗ sq_heap m ={⊤,∅}=∗ ▷ |={∅,⊤}=>
      sq_heap m' ∗ EXWP c' {{ Ψ }} ∗ from_option (λ ef, EXWP ef {{ _, True }}) True o.
  Proof.
    intros Hst. iIntros "Hwp Hm".
    destruct (at_step_cases _ _ _ _ _ _ Hst) as [(T & Hs & -> & ->) | (op & k & Hext)].
    - (* A core step. *)
      have Hv := lr_step_not_val _ _ _ _ _ Hs.
      have Hno : forall op k, ~ lr_external c op k
        by intros op k Hext; eapply lr_step_external_disjoint.
      rewrite (exwp_seq_unfold _ _ _ Hv Hno). iDestruct "Hwp" as "[Hwp _]".
      iMod ("Hwp" with "Hm") as "[_ Hwp]".
      iSpecialize ("Hwp" $! T c' m' with "[//]").
      iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iNext.
      iMod "Hwp" as "[$ $]". by iMod "Hclose" as "_".
    - (* An external call: its specification gives the step. *)
      iEval (rewrite (exwp_ext_unfold _ _ _ _ _ Hext)) in "Hwp".
      iMod "Hwp" as (x) "[Hpre Hcont]".
      iMod (ext_specs_step op with "Hpre Hm") as (ov) "(-> & Hm & Hpost & Ho)";
        [exact Hext | exact Hst | ].
      iModIntro. destruct o as [c_new|]; simpl; iNext;
        iMod ("Hcont" with "Hpost") as "Hwp"; iModIntro; iFrame.
  Qed.
End footprints.

(** ** The invariant *)

Section adequacy.
  Context `{!lrSqGS Σ, specs : !ExtSpecs lr_language Σ, !ExtSpecsSound specs}.
  Context (φ : sq_val -> Prop).

  (** Thread 0 is the initial thread; spawned threads have postcondition True. *)
  Definition sqex_post (i : nat) : sq_val -> iProp Σ :=
    if decide (i = 0%nat) then (λ v, ⌜φ v⌝)%I else (λ _, True)%I.

  Definition sqex_threads (tp : sqex_tpool) : iProp Σ :=
    [∗ map] i ↦ e ∈ tp, EXWP (e : sq_expr) {{ sqex_post i }}.

  Definition sqex_inv (tp : sqex_tpool) (m : lr_mem) : iProp Σ :=
    sq_heap m ∗ ⌜is_Some (tp !! 0%nat)⌝ ∗ sqex_threads tp.

  Lemma sqex_inv_zero (tp : sqex_tpool) (i : nat) (e : sq_expr) :
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
      have Hj0 : j ≠ 0%nat by intros ->; destruct H0; congruence.
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
    destruct (to_val e) as [v|] eqn:Hv.
    { iMod "Ht" as "Hpost".
      iAssert (⌜i = 0%nat -> φ v⌝)%I with "[Hpost]" as %Hφ.
      { destruct (decide (i = 0%nat)) as [->|Hne].
        - iEval (rewrite /sqex_post /=) in "Hpost". iDestruct "Hpost" as %Hφ.
          iPureIntro. by intros _.
        - iPureIntro. by intros ?. }
      iApply fupd_mask_intro_discard; first set_solver.
      iApply step_fupd_intro; first done. iNext. iPureIntro. split.
      - left. change (lr_final e). rewrite /lr_final Hv. by eexists.
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
      iMod "Hspec" as (x) "[Hpre _]".
      iDestruct (ext_specs_enabled op with "Hpre Hm") as %Hen; first exact He.
      iModIntro. iApply step_fupd_intro; first done. iNext. iPureIntro.
      split; [by right | intros v0 ? Hv0; congruence].
  Qed.

  (** A race between a sequential step of [i] and any step of [j] would
      need incompatible ownership. *)
  Lemma sqex_threads_no_race_seq tp m i j ci cj T evs2 ci' cj' m1 m2 o2 :
    i ≠ j -> tp !! i = Some ci -> tp !! j = Some cj ->
    lr_step ci m T ci' m1 -> at_step cj m evs2 cj' m2 o2 ->
    am_conflicts (NA <$> T) evs2 ->
    sqex_threads tp ⊢ |={⊤,∅}=> False.
  Proof.
    intros Hij Hi Hj Hs Hst (e1 & e2 & He1 & He2 & Hc).
    apply list_elem_of_fmap in He1 as (ev1 & -> & Hev1).
    destruct (am_conflict_cases _ _ Hc) as (la & w1 & w2 & Hacc1 & Hacc2 & Hw).
    iIntros "Hts". rewrite /sqex_threads.
    iDestruct (big_sepM_delete _ _ i with "Hts") as "[Hi Hts]"; first done.
    iDestruct (big_sepM_lookup _ _ j with "Hts") as "Hj"; first by rewrite lookup_delete_ne.
    (* [i]'s step is sequential, so its footprint needs no mask change; [j]'s
       step may be an external call, whose footprint is in its precondition. *)
    iMod (sqex_seq_own with "Hi") as "Hown1"; [exact Hs | exact Hev1 | exact Hacc1 | ].
    iMod (sqex_step_own with "Hj") as "Hown2"; [exact Hst | exact He2 | exact Hacc2 | ].
    by iDestruct (fp_own_excl _ _ _ Hw with "Hown1 Hown2") as "[]".
  Qed.

  Lemma sqex_inv_no_race tp m i j ci cj evs1 evs2 ci' cj' m1 m2 o1 o2 :
    i ≠ j -> tp !! i = Some ci -> tp !! j = Some cj ->
    at_step ci m evs1 ci' m1 o1 -> at_step cj m evs2 cj' m2 o2 ->
    am_conflicts evs1 evs2 ->
    sqex_inv tp m ⊢ |={⊤,∅}=> |={∅}▷=> ⌜False⌝.
  Proof.
    intros Hij Hi Hj H1 H2 Hc. iIntros "(_ & _ & Hts)".
    destruct (am_conflicts_seq _ _ _ _ _ _ _ _ _ _ _ H1 H2 Hc)
      as [(T & Hs & ->) | (T & Hs & ->)].
    - by iMod (sqex_threads_no_race_seq with "Hts") as "[]".
    - iMod (sqex_threads_no_race_seq _ _ j i with "Hts") as "[]"; try done.
      by apply am_conflicts_sym.
  Qed.

  Lemma sqex_sound n tp m tp' m' (P : Prop) :
    nsteps am_step_any n (AMCfg tp m) (AMCfg tp' m') ->
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

(** ** Adequacy *)

(** For any sound specifications of the external calls. *)
Theorem sqex_adequacy_gen Σ `{!lrSqGpreS Σ}
    (specs : forall H : lrSqGS Σ, ExtSpecs lr_language Σ)
    (Hspecs : forall H : lrSqGS Σ, @ExtSpecsSound Σ H (specs H))
    (e : sq_expr) (φ : sq_val -> Prop) (m : lr_mem) :
  (forall H : lrSqGS Σ, ⊢ @exwp Σ H (specs H) ⊤ e (λ v, ⌜φ v⌝)) ->
  at_sem_adequate [e] [φ] m.
Proof.
  intros Hwp tp' m' Hrtc.
  change (am_steps (AMCfg {[0%nat := e]} m) (AMCfg tp' m')) in Hrtc.
  destruct (rtc_nsteps_1 _ _ Hrtc) as [n Hsteps].
  assert (Hsound : forall P : Prop,
    (forall Hgs : lrSqGS Σ, @sqex_inv Σ Hgs (specs Hgs) φ tp' m' ⊢ |={⊤,∅}=> |={∅}▷=> ⌜P⌝) -> P).
  { intros P HP. apply (pure_soundness (PROP := iPropI Σ)).
    apply (step_fupdN_soundness_lc (Σ := Σ) _ (S n) 0). intros Hinv. iIntros "_".
    iMod (sq_heap_init m) as (Hheap) "Hheap".
    set (Hgs := LrSqGS _ Hinv Hheap).
    iApply (@sqex_sound Σ Hgs (specs Hgs) (Hspecs Hgs) φ n with "[Hheap]");
      [exact Hsteps | apply HP | ].
    iSplitL "Hheap"; first iExact "Hheap".
    iSplit; first (iPureIntro; by rewrite lookup_singleton_eq).
    rewrite /sqex_threads big_sepM_singleton /sqex_post /=. iApply (Hwp Hgs). }
  have Hend : forall i e0, tp' !! i = Some e0 ->
      am_not_stuck e0 m' /\ postcond_ok [φ] i e0.
  { intros i e0 Hi. apply Hsound. intros Hgs.
    by apply (@sqex_inv_thread_ok Σ Hgs (specs Hgs) (Hspecs Hgs)). }
  split; [|split].
  - intros (i & j & ci & cj & evs1 & evs2 & ci' & cj' & m1 & m2 & o1 & o2 &
      Hij & Hi & Hj & H1 & H2 & Hc).
    apply (Hsound False). intros Hgs.
    by eapply (@sqex_inv_no_race Σ Hgs (specs Hgs) (Hspecs Hgs)).
  - intros i e0 Hi. exact (proj1 (Hend i e0 Hi)).
  - intros i e0 Hi. exact (proj2 (Hend i e0 Hi)).
Qed.

Local Existing Instance ext_specs.

(** For the contracts [ext_specs] of the SC operations and Fork. *)
Theorem sqex_adequacy Σ `{!lrSqGpreS Σ} (e : sq_expr) (φ : sq_val -> Prop) (m : lr_mem) :
  (forall `{!lrSqGS Σ}, ⊢ EXWP e {{ v, ⌜φ v⌝ }}) ->
  at_sem_adequate [e] [φ] m.
Proof.
  intros Hwp. apply (sqex_adequacy_gen Σ (fun H => @ext_specs Σ H)
    (fun H => @ext_specs_sound Σ H)).
  exact Hwp.
Qed.
