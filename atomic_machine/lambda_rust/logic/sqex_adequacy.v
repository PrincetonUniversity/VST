(** Adequacy of the lifted sequential logic over the atomic machine semantics
    of lambda-Rust. *)

From stdpp Require Import relations.
From iris.algebra Require Import auth gmap frac.
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Export VST.atomic_machine.lambda_rust.logic.sq_adequacy.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_external_steps.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_pool_rebuild.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_seq_step.

Import ListNotations.

Local Existing Instance lr_ext_specs.

(**  every allocated location is unreserved. *)
Definition sq_mu (m : lr_mem) : rw_map := (fun _ => Rst 0) <$> m.

Definition sqex_pool (tp : list sq_expr) : tpool :=
  map_seq 0%nat ((fun e => Running e []) <$> tp).

(** If thread [i] in state [t] has returned a value [v], then [v] satisfies
    the postcondition of thread [i] in [φs] (if it has one). *)
Definition postcond_ok (φs : list (sq_val -> Prop)) (i : nat) (t : tstate) : Prop :=
  forall e v φ, t = Running e [] -> to_val e = Some v -> φs !! i = Some φ -> φ v.

(** Every reachable thread is safe; returned values satisfy their
    postconditions. Initially allocated locations have no reservations. *)
Definition at_sem_adequate (tp : list sq_expr) (φs : list (sq_val -> Prop)) (m : lr_mem) : Prop :=
  forall tp' m' mu',
    am_steps (AMCfg (sqex_pool tp) m (sq_mu m)) (AMCfg tp' m' mu') ->
    (forall i t, tp' !! i = Some t -> am_not_stuck t m' mu') /\
    (forall i t, tp' !! i = Some t -> postcond_ok φs i t).

(** Allocate the shared heap authority and the initial thread's full fragment. *)
Lemma sqex_heap_init_full `{!lrSqGpreS Σ, !invGS Σ} m :
  ⊢ |==> ∃ Hheap : sq_heapGS Σ,
    ⌜@sq_heap_name Σ Hheap ≠ @sq_freeable_name Σ Hheap⌝ ∗
    @sq_heap_gen Σ Hheap m (sq_full_heap m) ∗
    @own Σ (authR sq_heapUR) (@sq_heap_inG Σ Hheap)
      (@sq_heap_name Σ Hheap) (◯ sq_heap_cells m (sq_full_heap m)).
Proof.
  iMod (own_alloc (● sq_heap_cells m (sq_full_heap m) ⋅
    ◯ sq_heap_cells m (sq_full_heap m))) as (vγ) "[Hvγ Hfrag]".
  { apply auth_both_valid. split; [done | apply sq_full_heap_valid]. }
  iMod (own_alloc_cofinite (● (∅ : sq_freeableUR)) {[vγ]}) as (fγ) "[%Hfresh Hfγ]";
    first by apply auth_auth_valid.
  iModIntro. iExists (SqHeapGS _ _ _ vγ fγ).
  iSplit; first (iPureIntro; simpl; set_solver).
  iFrame "Hfrag". iExists ∅. iFrame. iPureIntro.
  split; [apply sq_full_heap_rel | intros ?? Hnone; by rewrite lookup_empty in Hnone].
Qed.

(** The invariant at every machine step. Logical expressions already reflect
    Try; their physical threads may still carry the corresponding trace. *)
Definition sqex_pending_config_inv `{!lrSqGS Σ} (C : sqex_threads Σ)
    (tp : tpool) (m : lr_mem) (mu : rw_map) : iProp Σ :=
  (* FIXME upred *)
  ∃ p hF, uPred_ownM (sqex_state_resource m p hF) ∗
    ⌜sq_heap_name ≠ sq_freeable_name ∧ sqex_threads_coherent m p C ∧
      sq_freeable_rel m hF ∧ sqex_pool_matches C tp ∧
      sqex_pool_reservations tp m mu⌝ ∗
    (* FIXME avoid this *)
    sqex_exact_threads_inv m hF C.

Lemma sqex_pending_config_inv_init `{!lrSqGS Σ} i Φ e m :
  sq_heap_name ≠ sq_freeable_name ->
  EXWP e {{ v, Φ v }} -∗ sq_heap_gen m (sq_full_heap m) -∗
  own sq_heap_name (◯ sq_heap_cells m (sq_full_heap m)) -∗
  sqex_pending_config_inv {[i := SqexThread e (sq_full_heap m) Φ]}
    {[i := Running e []]} m (sq_mu m).
Proof.
  intros Hnames. iIntros "Hwp (%hF & Hm & HF & [%Hrel %HFrel]) Hfrag".
  iAssert (uPred_ownM (sqex_state_resource m (sq_full_heap m) hF))
    with "[Hm HF]" as "Hstate".
  { rewrite sqex_state_resource_own. by iFrame. }
  iDestruct (sqex_exact_thread_init _ _ _ _ _ Hnames
    with "Hstate Hfrag Hwp") as "[Hstate Hthread]".
  iExists (sq_full_heap m), hF. iFrame "Hstate". iSplit.
  - iPureIntro. split; first done. split.
    { apply sqex_threads_coherent_singleton; [exact Hrel | apply sq_full_heap_valid]. }
    split; first done. split.
    { replace {[i := Running e []]} with
        (sqex_threads_pool {[i := SqexThread e (sq_full_heap m) Φ]}).
      - apply sqex_pool_matches_ready.
      - by rewrite /sqex_threads_pool map_fmap_singleton. }
    apply sqex_pool_reservations_init. intros j t Ht.
    apply (lookup_singleton_Some (M := gmap nat)) in Ht as [-> <-]. done.
  - by rewrite /sqex_exact_threads_inv big_sepM_singleton.
Qed.

(** The original semantic adequacy statement. The asserted simulation uses
    logical postconditions for a whole collection of compatible threads.

    Pending traces account for arbitrary interleavings directly. Each physical
    step uses one guarded recursive call. Sequential updates retain the exact
    local fragment, while external calls may redistribute the executing
    thread's ownership. *)
Theorem sqex_adequacy Σ `{!lrSqGpreS Σ}
    (e : sq_expr) (φ : sq_val -> Prop) (m : lr_mem) :
  (forall `{!lrSqGS Σ}, ⊢ EXWP e {{ v, ⌜φ v⌝ }}) ->
  at_sem_adequate [e] [φ] m.
Proof.
  intros Hwp.
  assert (Hsound : forall (Σ : gFunctors) `{!lrSqGS Σ},
    forall (C : sqex_threads Σ) (tp0 : tpool) (m0 : lr_mem) (mu0 : rw_map),
    sqex_pending_config_inv C tp0 m0 mu0 -∗
    ∀ n tp' m' mu' i t',
      ⌜nsteps at_step n (AMCfg tp0 m0 mu0) (AMCfg tp' m' mu')⌝ -∗
      ⌜tp' !! i = Some t'⌝ -∗
      |={⊤,∅}=> |={∅}▷=>^(S n)
        (⌜am_not_stuck t' m' mu'⌝ ∗ sqex_result C i t')).
  2: {
    intros tp' m' mu' Hrtc.
    change (rtc at_step (AMCfg {[0%nat := Running e []]} m (sq_mu m))
      (AMCfg tp' m' mu')) in Hrtc.
    destruct (rtc_nsteps_1 _ _ Hrtc) as [n Hsteps].
    assert (Hendpoint : forall i t, tp' !! i = Some t ->
      am_not_stuck t m' mu' /\ postcond_ok [φ] i t).
    { intros i t Hi. apply (pure_soundness (PROP := iPropI Σ)).
      apply (step_fupdN_soundness_lc (Σ := Σ) _ (S n) 0).
      intros Hinv. iIntros "_".
      iMod (sqex_heap_init_full m) as (Hheap) "(%Hnames & Hheap & Hfrag)".
      set (Hgs := LrSqGS _ Hinv Hheap).
      iPoseProof (@Hsound Σ Hgs
        {[0%nat := SqexThread e (sq_full_heap m) (fun v => ⌜φ v⌝)%I]}
        {[0%nat := Running e []]} m (sq_mu m) with "[Hheap Hfrag]") as "Hrun".
      { iApply (sqex_pending_config_inv_init (lrSqGS0 := Hgs) 0%nat
          (fun v => ⌜φ v⌝)%I e m Hnames with "[] Hheap Hfrag"). iApply (Hwp Hgs). }
      iMod ("Hrun" $! n tp' m' mu' i t with "[] []") as "Hrun"; [done | done | ].
      iModIntro. iApply (step_fupdN_wand with "Hrun").
      iIntros "[%Hsafe Hpost]". iSplit; first done.
      iIntros (e0 v φ0 Heq Hv [-> <-]%list_lookup_singleton_Some).
      iApply ("Hpost" $! (SqexThread e (sq_full_heap m) (fun v => ⌜φ v⌝)%I)
        e0 v with "[] [] []"); done. }
    split; intros i t Hi.
    - exact (proj1 (Hendpoint i t Hi)).
    - exact (proj2 (Hendpoint i t Hi)).
  }
  clear dependent Σ.
  intros Σ Hgs C tp0 m0 mu0.
  iLöb as "IH" forall (C tp0 m0 mu0).
  iIntros "(%p & %hF & Hstate & %Hconfig & Hthreads)"
    (n tp' m' mu' i t Hsteps Hi).
  destruct Hconfig as (Hnames & Hcoherent & HFrel & Hmatch & Hres).
  have Hrel := proj1 Hcoherent.
  have Hvalid := proj1 (proj2 Hcoherent).
  destruct n as [|n].
  - inversion Hsteps; subst tp' m' mu'. simpl.
    destruct (sqex_pool_matches_lookup_inv _ _ _ _ Hmatch Hi)
      as (c & T & Hc & -> & Hbudget).
    destruct T as [|ev T].
    + destruct (to_val (sqex_thread_expr c)) as [v|] eqn:Hv.
      * iDestruct (big_sepM_lookup _ _ i c Hc with "Hthreads") as "Hthread".
        iDestruct (sqex_exact_thread_wp with "Hthread") as "Hwp".
        iEval (rewrite exwp_unfold /exwp_pre Hv) in "Hwp".
        iMod "Hwp" as "Hpost".
        iMod (fupd_mask_subseteq ∅) as "_"; first set_solver.
        iModIntro. iModIntro. iNext. iModIntro. iSplit.
        { iPureIntro. left. exists (sqex_thread_expr c). split; first done. by exists v. }
        iIntros (c0 e1 w Hc0 Heq Hw). rewrite Hc in Hc0. injection Hc0 as <-.
        inversion Heq; subst e1. rewrite Hv in Hw. injection Hw as <-. done.
      * iMod (sqex_ready_progress _ _ _ _ _ _ _ _
          Hnames Hcoherent HFrel Hmatch Hres Hc Hi with "Hstate Hthreads") as "Hsafe".
        iModIntro. iModIntro. iNext. iModIntro. iSplit; first done.
        iIntros (c0 e1 w Hc0 Heq Hw). inversion Heq; subst e1. congruence.
    + have Hsafe := sqex_pool_reservations_pending_safe _ _ _ _ _ _ Hres Hi ltac:(discriminate).
      iMod (fupd_mask_subseteq ∅) as "_"; first set_solver.
      iModIntro. iModIntro. iNext. iModIntro. iSplit; first done.
      iIntros (c0 e1 w Hc0 Heq Hw). discriminate.
  - inversion Hsteps as [|n0 cfg0 cfg1 cfg2 Hfirst Htail]; subst.
    inversion Hfirst; subst.
    + (* Try retains the exact local budget and frames every other thread. *)
      destruct (sqex_pool_matches_lookup_inv _ _ _ _ Hmatch Hget)
        as (c0 & U & Hc0 & Hthread_eq & _).
      inversion Hthread_eq; subst.
      iDestruct (big_sepM_delete _ _ _ _ Hc0 with "Hthreads") as "[Hthread Hothers]".
      iMod (sqex_exact_pool_seq_step _ _ _ _ _ _ _ _ _
        Hnames Hcoherent HFrel Hc0 Hstep with "Hstate Hthread Hothers") as "Hnext".
      iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
      iModIntro. simpl. iModIntro. iNext. iMod "Hclose" as "_".
      iMod "Hnext" as (p' local' hF') "(%Hnext & Hstate & Hthread & Hothers)".
      destruct Hnext as (Hglobal & Hlocal & HFrel' & Hcoherent').
      destruct (sqex_pool_seq_successor m0 p C tp0 mu0 i0 c0 T c' m'0 p' local' μ'
        Hcoherent Hmatch Hres Hc0 Hget Hstep Hglobal Hlocal Hreserve)
        as (_ & Hmatch' & Hres' & Hposts).
      iAssert (sqex_exact_threads_inv m'0 hF'
        (<[i0 := SqexThread c' local' (sqex_thread_post c0)]> C))
        with "[Hthread Hothers]" as "Hthreads".
      { rewrite /sqex_exact_threads_inv big_sepM_insert_delete. by iFrame. }
      iMod ("IH" with "[Hstate Hthreads] [] []") as "Hrun"; [ | done | done | ].
      { iExists p', hF'. iFrame. done. }
      iModIntro. iApply (step_fupdN_wand ∅ ∅ (S n) with "Hrun").
      iIntros "[Hsafe Hpost]". iFrame "Hsafe".
      by iApply (sqex_result_extend with "Hpost").
    + (* Commit consumes only reservation metadata; logical WPs are unchanged. *)
      destruct (sqex_pool_reservations_commit _ _ _ _ _ _ Hres Hget)
        as (mu_done & Hfin & Hres').
      rewrite Hcommit in Hfin. injection Hfin as <-.
      have Hmatch' := sqex_pool_matches_commit _ _ _ _ _ Hmatch Hget.
      iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
      iModIntro. simpl. iModIntro. iNext. iMod "Hclose" as "_".
      iApply ("IH" with "[Hstate Hthreads] [] []"); [ | done | done ].
      iExists p, hF. iFrame. done.
    + (* Atomic load: reconstruct only the executing ready thread. *)
      destruct (sqex_pool_matches_lookup_inv _ _ _ _ Hmatch Hget)
        as (c0 & T & Hc0 & Hthread_eq & _).
      inversion Hthread_eq; subst. destruct ly.
      iDestruct (big_sepM_delete _ _ _ _ Hc0 with "Hthreads") as "[Hthread Hothers]".
      iDestruct (sqex_exact_thread_wp with "Hthread") as "Hwp".
      iMod (sqex_external_read_pending ⊤ C tp0 m0 p hF mu0 i0
        (sqex_thread_expr c0) K l (sqex_thread_post c0)
        Hnames Hrel HFrel Hvalid Hmatch Hres Hget Hext
        with "Hstate Hwp Hothers") as (w) "[%Hread Hnext]".
      destruct Hread as [Hw _]. change (m0 !! l = Some v) in Hload.
      rewrite Hload in Hw. injection Hw as <-.
      iModIntro. simpl. iModIntro. iNext.
      iMod "Hnext" as "(Hstate & Hwp & Hothers)".
      have Hrels : forall j d, delete i0 C !! j = Some d -> sq_heap_rel m0 (sqex_thread_perm d).
      { intros j d Hd. apply (lookup_delete_Some (M := gmap nat)) in Hd as [_ Hd].
        by eapply (proj2 (proj2 (proj2 Hcoherent))). }
      iDestruct (sqex_ready_replace _ _ _ _ _ _ _ _ Hnames Hrel Hc0 Hrels Hmatch
        with "Hstate Hothers Hwp") as (pi) "(%Hnext & Hstate & Hthreads)".
      destruct Hnext as (Hcoherent' & Hmatch' & Hposts).
      have Hres' := sqex_pool_reservations_ready_update _ _ _ _ _ (K (Some v)) Hres Hget.
      iMod ("IH" with "[Hstate Hthreads] [] []") as "Hrun"; [ | done | done | ].
      { iExists p, hF. iFrame. done. }
      iModIntro. iApply (step_fupdN_wand ∅ ∅ (S n) with "Hrun").
      iIntros "[Hsafe Hpost]". iFrame "Hsafe".
      by iApply (sqex_result_extend with "Hpost").
    + (* Atomic store: retain other threads and reconstruct its continuation. *)
      destruct (sqex_pool_matches_lookup_inv _ _ _ _ Hmatch Hget)
        as (c0 & T & Hc0 & Hthread_eq & _).
      inversion Hthread_eq; subst. destruct ly.
      destruct (m0 !! l) as [old|] eqn:Hm;
        rewrite /= Hm in Hstore; inversion Hstore; subst.
      iDestruct (big_sepM_delete _ _ _ _ Hc0 with "Hthreads") as "[Hthread Hothers]".
      iDestruct (sqex_exact_thread_wp with "Hthread") as "Hwp".
      iMod (sqex_external_write_pending ⊤ C tp0 m0 p hF mu0 i0
        (sqex_thread_expr c0) K l v (sqex_thread_post c0)
        Hnames Hrel HFrel Hvalid Hmatch Hres Hget Hext
        with "Hstate Hwp Hothers") as "[%Hwrite Hnext]".
      destruct Hwrite as [Hallocated _].
      have Hrel' : sq_heap_rel (<[l := v]> m0) p.
      { unfold sq_heap_rel in *. rewrite dom_insert_L. set_solver. }
      have HFrel' : sq_freeable_rel (<[l := v]> m0) hF.
      { by eapply sq_freeable_rel_stable. }
      have Hrels : forall j d, delete i0 C !! j = Some d ->
          sq_heap_rel (<[l := v]> m0) (sqex_thread_perm d).
      { intros j d Hd. apply (lookup_delete_Some (M := gmap nat)) in Hd as [_ Hd].
        have Hdrel := proj2 (proj2 (proj2 Hcoherent)) _ _ Hd.
        unfold sq_heap_rel in *. rewrite dom_insert_L. set_solver. }
      iModIntro. simpl. iModIntro. iNext.
      iMod "Hnext" as "(Hstate & Hwp & Hothers)".
      iDestruct (sqex_ready_replace _ _ _ _ _ _ _ _ Hnames Hrel' Hc0 Hrels Hmatch
        with "Hstate Hothers Hwp") as (pi) "(%Hnext & Hstate & Hthreads)".
      destruct Hnext as (Hcoherent' & Hmatch' & Hposts).
      have Hres_mem := sqex_pool_reservations_store _ _ _ _ v Hres Hallocated.
      have Hres' := sqex_pool_reservations_ready_update _ _ _ _ _ (K None) Hres_mem Hget.
      iMod ("IH" with "[Hstate Hthreads] [] []") as "Hrun"; [ | done | done | ].
      { iExists p, hF. iFrame. done. }
      iModIntro. iApply (step_fupdN_wand ∅ ∅ (S n) with "Hrun").
      iIntros "[Hsafe Hpost]". iFrame "Hsafe".
      by iApply (sqex_result_extend with "Hpost").
    + (* Successful CAS updates the cell and reconstructs its continuation. *)
      destruct (sqex_pool_matches_lookup_inv _ _ _ _ Hmatch Hget)
        as (c0 & T & Hc0 & Hthread_eq & _).
      inversion Hthread_eq; subst. destruct ly.
      change (m0 !! l = Some v_cur) in Hload.
      rewrite /= Hload in Hstore. inversion Hstore; subst.
      iDestruct (big_sepM_delete _ _ _ _ Hc0 with "Hthreads") as "[Hthread Hothers]".
      iDestruct (sqex_exact_thread_wp with "Hthread") as "Hwp".
      iMod (sqex_external_cas_suc_pending ⊤ C tp0 m0 p hF mu0 i0
        (sqex_thread_expr c0) K l v_exp v_new v_cur (sqex_thread_post c0)
        Hnames Hrel HFrel Hvalid Hmatch Hres Hget Hext Hload Heq
        with "Hstate Hwp Hothers") as "Hnext".
      have Hallocated : is_Some (m0 !! l) by eexists.
      have Hrel' : sq_heap_rel (<[l := v_new]> m0) p.
      { unfold sq_heap_rel in *. rewrite dom_insert_L. set_solver. }
      have HFrel' : sq_freeable_rel (<[l := v_new]> m0) hF.
      { by eapply sq_freeable_rel_stable. }
      have Hrels : forall j d, delete i0 C !! j = Some d ->
          sq_heap_rel (<[l := v_new]> m0) (sqex_thread_perm d).
      { intros j d Hd. apply (lookup_delete_Some (M := gmap nat)) in Hd as [_ Hd].
        have Hdrel := proj2 (proj2 (proj2 Hcoherent)) _ _ Hd.
        unfold sq_heap_rel in *. rewrite dom_insert_L. set_solver. }
      iModIntro. simpl. iModIntro. iNext.
      iMod "Hnext" as "(Hstate & Hwp & Hothers)".
      iDestruct (sqex_ready_replace _ _ _ _ _ _ _ _ Hnames Hrel' Hc0 Hrels Hmatch
        with "Hstate Hothers Hwp") as (pi) "(%Hnext & Hstate & Hthreads)".
      destruct Hnext as (Hcoherent' & Hmatch' & Hposts).
      have Hres_mem := sqex_pool_reservations_store _ _ _ _ v_new Hres Hallocated.
      have Hres' := sqex_pool_reservations_ready_update _ _ _ _ _
        (K (Some (LitV (LitInt 1)))) Hres_mem Hget.
      iMod ("IH" with "[Hstate Hthreads] [] []") as "Hrun"; [ | done | done | ].
      { iExists p, hF. iFrame. done. }
      iModIntro. iApply (step_fupdN_wand ∅ ∅ (S n) with "Hrun").
      iIntros "[Hsafe Hpost]". iFrame "Hsafe".
      by iApply (sqex_result_extend with "Hpost").
    + (* Failed CAS retains the old heap and returns false. *)
      destruct (sqex_pool_matches_lookup_inv _ _ _ _ Hmatch Hget)
        as (c0 & T & Hc0 & Hthread_eq & _).
      inversion Hthread_eq; subst. destruct ly.
      change (m0 !! l = Some v_cur) in Hload.
      iDestruct (big_sepM_delete _ _ _ _ Hc0 with "Hthreads") as "[Hthread Hothers]".
      iDestruct (sqex_exact_thread_wp with "Hthread") as "Hwp".
      iMod (sqex_external_cas_fail_pending ⊤ C tp0 m0 p hF mu0 i0
        (sqex_thread_expr c0) K l v_exp v_new v_cur (sqex_thread_post c0)
        Hnames Hrel HFrel Hvalid Hmatch Hres Hget Hext Hload Hneq
        with "Hstate Hwp Hothers") as "Hnext".
      iModIntro. simpl. iModIntro. iNext.
      iMod "Hnext" as "(Hstate & Hwp & Hothers)".
      have Hrels : forall j d, delete i0 C !! j = Some d -> sq_heap_rel m0 (sqex_thread_perm d).
      { intros j d Hd. apply (lookup_delete_Some (M := gmap nat)) in Hd as [_ Hd].
        by eapply (proj2 (proj2 (proj2 Hcoherent))). }
      iDestruct (sqex_ready_replace _ _ _ _ _ _ _ _ Hnames Hrel Hc0 Hrels Hmatch
        with "Hstate Hothers Hwp") as (pi) "(%Hnext & Hstate & Hthreads)".
      destruct Hnext as (Hcoherent' & Hmatch' & Hposts).
      have Hres' := sqex_pool_reservations_ready_update _ _ _ _ _
        (K (Some (LitV (LitInt 0)))) Hres Hget.
      iMod ("IH" with "[Hstate Hthreads] [] []") as "Hrun"; [ | done | done | ].
      { iExists p, hF. iFrame. done. }
      iModIntro. iApply (step_fupdN_wand ∅ ∅ (S n) with "Hrun").
      iIntros "[Hsafe Hpost]". iFrame "Hsafe".
      by iApply (sqex_result_extend with "Hpost").
    + (* Full ownership excludes the reservation failure that causes CAS UB. *)
      destruct (sqex_pool_matches_lookup_inv _ _ _ _ Hmatch Hget)
        as (c0 & T & Hc0 & Hthread_eq & _).
      inversion Hthread_eq; subst. destruct ly.
      iDestruct (big_sepM_delete _ _ _ _ Hc0 with "Hthreads") as "[Hthread Hothers]".
      iDestruct (sqex_exact_thread_wp with "Hthread") as "Hwp".
      iMod (sqex_external_cas_writable ⊤ C tp0 m0 p hF mu0 i0
        (sqex_thread_expr c0) K l v_exp v_new (sqex_thread_post c0)
        Hnames Hrel HFrel Hvalid Hmatch Hres Hget Hext
        with "Hstate Hwp Hothers") as %Hwritable.
      exfalso. apply Ho. by apply Forall_singleton.
    + (* Spawn reconstructs parent and child while retaining all existing threads. *)
      destruct (sqex_pool_matches_lookup_inv _ _ _ _ Hmatch Hget)
        as (c0 & T & Hc0 & Hthread_eq & _).
      inversion Hthread_eq; subst.
      iDestruct (big_sepM_delete _ _ _ _ Hc0 with "Hthreads") as "[Hthread Hothers]".
      iDestruct (sqex_exact_thread_wp with "Hthread") as "Hwp".
      iMod (sqex_external_spawn_pending ⊤ C tp0 m0 p hF mu0 i0
        (sqex_thread_expr c0) K e_new j (sqex_thread_post c0)
        Hget Hspawn Hfree Hleast with "Hstate Hwp Hothers") as "[_ Hnext]".
      iModIntro. simpl. iModIntro. iNext.
      iMod "Hnext" as "(Hstate & Hwp & Hchild & Hothers)".
      have HfreshC : C !! j = None.
      { have Hj := Hmatch j. rewrite Hfree in Hj. by inversion Hj. }
      have Hrels : forall k d, delete i0 C !! k = Some d -> sq_heap_rel m0 (sqex_thread_perm d).
      { intros k d Hd. apply (lookup_delete_Some (M := gmap nat)) in Hd as [_ Hd].
        by eapply (proj2 (proj2 (proj2 Hcoherent))). }
      iDestruct (sqex_ready_spawn _ _ _ _ _ _ _ _ _ _
        Hnames Hrel Hc0 HfreshC Hrels Hmatch with "Hstate Hothers Hwp Hchild")
        as (pp pc) "(%Hnext & Hstate & Hthreads)".
      destruct Hnext as (Hcoherent' & Hmatch' & Hposts).
      have Hres_parent := sqex_pool_reservations_ready_update _ _ _ _ _ (K None) Hres Hget.
      have Hne : i0 ≠ j by intros ->; congruence.
      have Hfresh' : (<[i0 := Running (K None) []]> tp0) !! j = None by rewrite lookup_insert_ne.
      have Hres' := sqex_pool_reservations_spawn _ _ _ _ e_new Hres_parent Hfresh'.
      iMod ("IH" with "[Hstate Hthreads] [] []") as "Hrun"; [ | done | done | ].
      { iExists p, hF. iFrame. done. }
      iModIntro. iApply (step_fupdN_wand ∅ ∅ (S n) with "Hrun").
      iIntros "[Hsafe Hpost]". iFrame "Hsafe".
      by iApply (sqex_result_extend with "Hpost").
Qed.
