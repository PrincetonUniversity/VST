(** * Adequacy of EXWP for the atomic machine

    [at_sem_adequate] is safety of the atomic machine started from a list of
    threads: every reachable thread can step or has finished, and returned
    values satisfy their postconditions ([postcond_ok]).

    The proof is a standard Iris adequacy argument: an invariant holding the
    shared state interpretation [sq_heap m] and, for every thread, its EXWP
    (possibly waiting for the footprint of a pending trace) is preserved by
    each machine step and implies that every thread can step. Thread WPs are
    used only through [exwp_unfold]; the state interpretation only through
    the [sq_heap] lemmas.

    The reader/writer bookkeeping is the pure [sqex_pending] development. *)

From stdpp Require Import relations.
From iris.algebra Require Import auth gmap frac.
From iris.proofmode Require Import proofmode.
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.logic.at_logic.
Require Import VST.atomic_machine.lambda_rust.adequacy.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_pending.
Require Export VST.atomic_machine.lambda_rust.logic.sq_adequacy.
Require Export VST.atomic_machine.lambda_rust.logic.sqex_logic.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".
Local Existing Instance lrSqGS_invGS.
Local Existing Instance lr_ext_specs.

(** ** The statement *)

(** Every allocated location is unreserved. *)
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

(** ** Pure reservation facts *)

Lemma sqex_cell_readable v r f st :
  sqex_reservation_cell (Some v) r 0 f st -> exists n, st = Some (Rst n).
Proof. inversion 1; eauto. Qed.

Lemma sqex_cell_writable v f st :
  sqex_reservation_cell (Some v) 0 0 f st -> st = Some (Rst 0).
Proof. by inversion 1. Qed.

Lemma sqex_reservations_readable m D mu l :
  sqex_reservations m D mu -> is_Some (m !! l) -> lr_write_event l ∉ D ->
  exists n, mu !! l = Some (Rst n).
Proof.
  intros Hres [v Hv] Hw. specialize (Hres l). rewrite Hv in Hres.
  have Hw0 : sqex_trace_count SqexWrite l D = 0%nat by apply sqex_trace_count_zero.
  rewrite Hw0 in Hres. by eapply sqex_cell_readable.
Qed.

Lemma sqex_reservations_writable m D mu l :
  sqex_reservations m D mu -> is_Some (m !! l) ->
  lr_write_event l ∉ D -> lr_read_event l ∉ D -> mu !! l = Some (Rst 0).
Proof.
  intros Hres [v Hv] Hw Hr. specialize (Hres l). rewrite Hv in Hres.
  have Hw0 : sqex_trace_count SqexWrite l D = 0%nat by apply sqex_trace_count_zero.
  have Hr0 : sqex_trace_count SqexRead l D = 0%nat by apply sqex_trace_count_zero.
  rewrite Hw0 Hr0 in Hres. by eapply sqex_cell_writable.
Qed.

Lemma sqex_pending_ready tp i e :
  tp !! i = Some (Running e []) ->
  sqex_pending_events tp ≡ₚ sqex_pending_events (delete i tp).
Proof. intros Hi. by rewrite (sqex_pending_events_delete _ _ _ _ Hi). Qed.

Lemma sqex_step_free e m T e' m' l :
  lr_step e m T e' m' -> lr_free_event l ∈ T ->
  is_Some (m !! l) /\ m' !! l = None.
Proof.
  intros Hstep Hin. destruct (lr_step_mem_effect _ _ _ _ _ Hstep) as
    [m0|m0 k Hk|m0 k v Hk|m0 k n Hfresh|m0 k n Hall].
  - inversion Hin.
  - apply list_elem_of_singleton in Hin. discriminate.
  - apply list_elem_of_singleton in Hin. discriminate.
  - apply list_elem_of_fmap in Hin as (k' & Heq & _). discriminate.
  - apply list_elem_of_fmap in Hin as (k' & Heq & Hk').
    injection Heq as <-.
    destruct (sqex_locs_member_range _ _ _ Hk') as (z & Hz & ->).
    split; first by apply Hall.
    rewrite sq_mem_lookup_free_mem decide_True //.
    unfold loc_in_range, shift_loc. simpl. split; [done | lia].
Qed.

Lemma sqex_lit_eq_int (m : lr_mem) z1 z2 : sq_mem.lit_eq m (LitInt z1) (LitInt z2) -> z1 = z2.
Proof. by inversion 1. Qed.

Lemma sqex_lit_neq_int z1 z2 : lit_neq (LitInt z1) (LitInt z2) -> z1 ≠ z2.
Proof. by inversion 1. Qed.

Lemma sqex_singleton_lookup (t : tstate) : ({[0%nat := t]} : tpool) !! 0%nat = Some t.
Proof. apply (lookup_singleton_eq (M := gmap nat)). Qed.

Lemma sqex_singleton_lookup_1 (t : tstate) : ({[0%nat := t]} : tpool) !! 1%nat = None.
Proof. by apply (lookup_singleton_ne (M := gmap nat)). Qed.

(** ** The invariant *)

Section adequacy.
  Context `{!lrSqGS Σ} (φ : sq_val -> Prop).

  (** Thread 0 is the initial thread; spawned threads have postcondition True. *)
  Definition sqex_post (i : nat) : sq_val -> iProp Σ :=
    if decide (i = 0%nat) then (λ v, ⌜φ v⌝)%I else (λ _, True)%I.

  (** A thread with pending trace [T] has the points-tos corresponding to the pending events to justify the wp. *)
  Definition sqex_thread (i : nat) (t : tstate) : iProp Σ :=
    match t with
    | Running e T => ∃ ds, fp_tokens T ds ∗ (fp_tokens T ds -∗ EXWP e {{ sqex_post i }})
    | StuckState => False
    end.

  Definition sqex_inv (tp : tpool) (m : lr_mem) (mu : rw_map) : iProp Σ :=
    sq_heap m ∗ ⌜
      (* all pending events have been reserved (and can therefore can be
         commited later in an [at_step]) *)
      sqex_pool_reservations tp m mu ∧
      is_Some (tp !! 0%nat)⌝ ∗
    [∗ map] i ↦ t ∈ tp, sqex_thread i t.

  Lemma sqex_thread_ready i e :
    sqex_thread i (Running e []) ⊣⊢ EXWP e {{ sqex_post i }}.
  Proof.
    iSplit.
    - iIntros "(%ds & Htok & Hwp)". iDestruct (fp_tokens_nil_inv with "Htok") as %->.
      by iApply "Hwp".
    - iIntros "Hwp". iExists []. iSplit; first by iApply fp_tokens_nil. by iIntros "_".
  Qed.

  (** Pending footprints exclude conflicting fragments. *)
  Lemma sqex_threads_read_excl tp l q v :
    ([∗ map] i ↦ t ∈ tp, sqex_thread i t) -∗ l ↦{q} v -∗
    ⌜lr_write_event l ∉ sqex_pending_events tp⌝.
  Proof.
    iIntros "Hts Hl %Hin".
    apply sqex_pending_events_elem in Hin as (j & e & T & Hj & HinT).
    iDestruct (big_sepM_lookup with "Hts") as "Ht"; first exact Hj.
    iDestruct "Ht" as (ds) "[Htok _]".
    by iDestruct (fp_tokens_read_excl with "Htok Hl") as %?.
  Qed.

  Lemma sqex_threads_write_excl tp l v :
    ([∗ map] i ↦ t ∈ tp, sqex_thread i t) -∗ l ↦ v -∗
    ⌜lr_write_event l ∉ sqex_pending_events tp ∧
      lr_read_event l ∉ sqex_pending_events tp⌝.
  Proof.
    iIntros "Hts Hl". iSplit.
    - iApply (sqex_threads_read_excl with "Hts Hl").
    - iIntros (Hin). apply sqex_pending_events_elem in Hin as (j & e & T & Hj & HinT).
      iDestruct (big_sepM_lookup with "Hts") as "Ht"; first exact Hj.
      iDestruct "Ht" as (ds) "[Htok _]".
      iDestruct (fp_tokens_write_excl with "Htok Hl") as %[_ Hr]. done.
  Qed.

  Lemma sqex_threads_allocated tp m :
    sq_heap m -∗ ([∗ map] i ↦ t ∈ tp, sqex_thread i t) -∗
    ⌜forall l, lr_read_event l ∈ sqex_pending_events tp \/
      lr_write_event l ∈ sqex_pending_events tp -> is_Some (m !! l)⌝.
  Proof.
    iIntros "Hm Hts" (l Hin).
    have [j [e [T [Hj HinT]]]] : exists j e T, tp !! j = Some (Running e T) /\
        (lr_read_event l ∈ T \/ lr_write_event l ∈ T).
    { destruct Hin as [Hin|Hin]; apply sqex_pending_events_elem in Hin as (j & e & T & Hj & HinT);
        eauto 10. }
    iDestruct (big_sepM_lookup with "Hts") as "Ht"; first exact Hj.
    iDestruct "Ht" as (ds) "[Htok _]".
    iDestruct (fp_tokens_allocated with "Hm Htok") as %Halloc.
    iPureIntro. by apply Halloc.
  Qed.

  (** The reservation side conditions of a step of a ready thread, given its
      footprint, the state after the step, and the other threads. *)
  Lemma sqex_ready_conditions tp m mu i e T e' m' ds :
    sqex_pool_reservations tp m mu -> tp !! i = Some (Running e []) ->
    lr_step e m T e' m' ->
    sq_heap m' -∗ fp_tokens T ds -∗
    ([∗ map] k ↦ t ∈ delete i tp, sqex_thread k t) -∗
    ⌜(forall l, lr_read_event l ∈ T -> exists n, mu !! l = Some (Rst n)) /\
     (forall l, lr_write_event l ∈ T -> mu !! l = Some (Rst 0)) /\
     (forall l, lr_free_event l ∈ T -> mu !! l = Some (Rst 0))⌝.
  Proof.
    intros Hres Hi Hstep. iIntros "Hm Htok Hts".
    have Hres' : sqex_reservations m (sqex_pending_events (delete i tp)) mu.
    { unfold sqex_pool_reservations in Hres. by rewrite -(sqex_pending_ready _ _ _ Hi). }
    iDestruct (sqex_threads_allocated with "Hm Hts") as %Halloc.
    iSplit; [|iSplit].
    - iIntros (l Hin).
      iDestruct (fp_tokens_read with "Htok") as (q v) "[Hl _]"; first done.
      iDestruct (sqex_threads_read_excl with "Hts Hl") as %Hw.
      iPureIntro. eapply sqex_reservations_readable; [exact Hres' | | exact Hw].
      by destruct (lr_step_read_footprint _ _ _ _ _ _ Hstep Hin) as [Hm _].
    - iIntros (l Hin).
      iDestruct (fp_tokens_write with "Htok") as (v) "[Hl _]"; first done.
      iDestruct (sqex_threads_write_excl with "Hts Hl") as %[Hw Hr].
      iPureIntro. eapply sqex_reservations_writable; [exact Hres' | | exact Hw | exact Hr].
      destruct (lr_step_write_footprint _ _ _ _ _ _ Hstep Hin) as (old & _ & Hold & _).
      by eexists.
    - iPureIntro. intros l Hin.
      destruct (sqex_step_free _ _ _ _ _ _ Hstep Hin) as [Hm Hm'].
      apply (sqex_reservations_writable _ _ _ _ Hres' Hm).
      + intros Hw. have [w Hw'] := Halloc l (or_intror Hw). congruence.
      + intros Hr. have [w Hr'] := Halloc l (or_introl Hr). congruence.
  Qed.

  (** An external call's full points-to makes the location writable. *)
  Lemma sqex_external_writable tp m mu i e l v :
    sqex_pool_reservations tp m mu -> tp !! i = Some (Running e []) ->
    sq_heap m -∗ l ↦ v -∗ ([∗ map] k ↦ t ∈ delete i tp, sqex_thread k t) -∗
    ⌜m !! l = Some v ∧ mu !! l = Some (Rst 0)⌝.
  Proof.
    intros Hres Hi. iIntros "Hm Hl Hts".
    have Hres' : sqex_reservations m (sqex_pending_events (delete i tp)) mu.
    { unfold sqex_pool_reservations in Hres. by rewrite -(sqex_pending_ready _ _ _ Hi). }
    iDestruct (sq_heap_read with "Hm Hl") as %Hv.
    iDestruct (sqex_threads_write_excl with "Hts Hl") as %[Hw Hr].
    iPureIntro. split; first done.
    eapply sqex_reservations_writable; [exact Hres' | by eexists | exact Hw | exact Hr].
  Qed.

  Lemma sqex_external_readable tp m mu i e l q v :
    sqex_pool_reservations tp m mu -> tp !! i = Some (Running e []) ->
    sq_heap m -∗ l ↦{q} v -∗ ([∗ map] k ↦ t ∈ delete i tp, sqex_thread k t) -∗
    ⌜m !! l = Some v ∧ exists n, mu !! l = Some (Rst n)⌝.
  Proof.
    intros Hres Hi. iIntros "Hm Hl Hts".
    have Hres' : sqex_reservations m (sqex_pending_events (delete i tp)) mu.
    { unfold sqex_pool_reservations in Hres. by rewrite -(sqex_pending_ready _ _ _ Hi). }
    iDestruct (sq_heap_read with "Hm Hl") as %Hv.
    iDestruct (sqex_threads_read_excl with "Hts Hl") as %Hw.
    iPureIntro. split; first done.
    eapply sqex_reservations_readable; [exact Hres' | by eexists | exact Hw].
  Qed.

  Lemma sqex_inv_zero (tp : tpool) (i : nat) (t : tstate) :
    is_Some (tp !! 0%nat) -> is_Some (<[i := t]> tp !! 0%nat).
  Proof. intros H0. rewrite lookup_insert_is_Some'. by right. Qed.

  (** ** sqex_inv preserved *)

  Lemma at_step_preserves_sqex_inv tp m mu tp' m' mu' :
    at_step (AMCfg tp m mu) (AMCfg tp' m' mu') ->
    sqex_inv tp m mu ⊢ |={⊤,∅}=> ▷ |={∅,⊤}=> sqex_inv tp' m' mu'.
  Proof.
    iIntros (Hat) "(Hm & [%Hres %H0] & Hts)".
    inversion Hat; subst.
    - (* Core_Try: the thread hands over the footprint of its trace. *)
      iDestruct (big_sepM_delete _ _ i with "Hts") as "[Ht Hts]"; first done.
      iEval (rewrite sqex_thread_ready) in "Ht".
      have Hv := lr_step_not_val _ _ _ _ _ Hstep.
      have Hno : forall op k, ~ lr_external c op k
        by intros op k Hext; eapply lr_step_external_disjoint.
      rewrite (exwp_seq_unfold _ _ _ Hv Hno).
      iMod ("Ht" with "Hm") as "[_ Hwp]".
      iSpecialize ("Hwp" $! T c' m' with "[//]").
      iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iNext.
      iMod "Hwp" as "[Hm (%ds & Htok & Hwp)]".
      iDestruct (sqex_ready_conditions with "Hm Htok Hts") as %(_ & _ & Hfree);
        [done | done | done | ].
      have Hres' := sqex_pool_reservations_try _ _ _ _ _ _ _ _ _ Hres Hget Hstep Hfree Hreserve.
      iMod "Hclose" as "_". iModIntro. iFrame "Hm". iSplit.
      { iPureIntro. split; [done | by apply sqex_inv_zero]. }
      iApply big_sepM_insert_delete. iFrame "Hts". iExists ds. iFrame.
    - (* Core_Commit: the footprint is returned. *)
      destruct (sqex_pool_reservations_commit _ _ _ _ _ _ Hres Hget) as (mu2 & Hfin & Hres').
      rewrite Hcommit in Hfin. injection Hfin as <-.
      iDestruct (big_sepM_delete _ _ i with "Hts") as "[Ht Hts]"; first done.
      iDestruct "Ht" as (ds) "[Htok Hwp]". iSpecialize ("Hwp" with "Htok").
      iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iNext.
      iMod "Hclose" as "_". iModIntro. iFrame "Hm". iSplit.
      { iPureIntro. split; [done | by apply sqex_inv_zero]. }
      iApply big_sepM_insert_delete. iFrame "Hts". by iApply sqex_thread_ready.
    - (* SC_Read *)
      iDestruct (big_sepM_delete _ _ i with "Hts") as "[Ht Hts]"; first done.
      iEval (rewrite sqex_thread_ready (exwp_ext_unfold _ _ _ _ _ Hext)) in "Ht".
      iMod "Ht" as ([q w]) "[Hl Hcont]". simpl.
      iDestruct (sq_heap_read with "Hm Hl") as %Hw.
      change (m' !! l = Some v) in Hload. rewrite Hload in Hw. injection Hw as <-.
      iModIntro. iNext. iMod ("Hcont" $! (Some v) with "[Hl]") as "Hwp".
      { by iFrame. }
      iModIntro. iFrame "Hm". iSplit.
      { iPureIntro. split; last by apply sqex_inv_zero.
        by eapply sqex_pool_reservations_ready_update. }
      iApply big_sepM_insert_delete. iFrame "Hts". by iApply sqex_thread_ready.
    - (* SC_Write *)
      iDestruct (big_sepM_delete _ _ i with "Hts") as "[Ht Hts]"; first done.
      iEval (rewrite sqex_thread_ready (exwp_ext_unfold _ _ _ _ _ Hext)) in "Ht".
      iMod "Ht" as (w) "[Hl Hcont]". simpl.
      iDestruct (sq_heap_read with "Hm Hl") as %Hw.
      rewrite /= Hw in Hstore. injection Hstore as <-.
      iMod (sq_heap_write with "Hm Hl") as "[Hm Hl]".
      iModIntro. iNext. iMod ("Hcont" $! None with "[Hl]") as "Hwp".
      { by iFrame. }
      iModIntro. iFrame "Hm". iSplit.
      { iPureIntro. split; last by apply sqex_inv_zero.
        eapply sqex_pool_reservations_ready_update; last done.
        apply sqex_pool_reservations_store; [done | by eexists]. }
      iApply big_sepM_insert_delete. iFrame "Hts". by iApply sqex_thread_ready.
    - (* SC_Cas_Suc *)
      iDestruct (big_sepM_delete _ _ i with "Hts") as "[Ht Hts]"; first done.
      iEval (rewrite sqex_thread_ready (exwp_ext_unfold _ _ _ _ _ Hext)) in "Ht".
      iMod "Ht" as ([z_cur z_exp]) "[[-> Hl] Hcont]". simpl.
      iDestruct (sq_heap_read with "Hm Hl") as %Hw.
      change (m !! l = Some v_cur) in Hload. rewrite Hload in Hw. injection Hw as ->.
      apply sqex_lit_eq_int in Heq. subst.
      rewrite /= Hload in Hstore. injection Hstore as <-.
      iMod (sq_heap_write _ _ _ v_new with "Hm Hl") as "[Hm Hl]".
      iModIntro. iNext.
      iMod ("Hcont" $! (Some (LitV (lit_of_bool true))) with "[Hl]") as "Hwp".
      { rewrite bool_decide_true // decide_True //. by iFrame. }
      iModIntro. iFrame "Hm". iSplit.
      { iPureIntro. split; last by apply sqex_inv_zero.
        eapply sqex_pool_reservations_ready_update; last done.
        apply sqex_pool_reservations_store; [done | by eexists]. }
      iApply big_sepM_insert_delete. iFrame "Hts". by iApply sqex_thread_ready.
    - (* SC_Cas_Fail *)
      iDestruct (big_sepM_delete _ _ i with "Hts") as "[Ht Hts]"; first done.
      iEval (rewrite sqex_thread_ready (exwp_ext_unfold _ _ _ _ _ Hext)) in "Ht".
      iMod "Ht" as ([z_cur z_exp]) "[[-> Hl] Hcont]". simpl.
      iDestruct (sq_heap_read with "Hm Hl") as %Hw.
      change (m' !! l = Some v_cur) in Hload. rewrite Hload in Hw. injection Hw as ->.
      apply sqex_lit_neq_int in Hneq.
      iModIntro. iNext.
      iMod ("Hcont" $! (Some (LitV (lit_of_bool false))) with "[Hl]") as "Hwp".
      { have Hne : z_cur ≠ z_exp by intros ?; apply Hneq.
        rewrite bool_decide_false // decide_False //. by iFrame. }
      iModIntro. iFrame "Hm". iSplit.
      { iPureIntro. split; last by apply sqex_inv_zero.
        by eapply sqex_pool_reservations_ready_update. }
      iApply big_sepM_insert_delete. iFrame "Hts". by iApply sqex_thread_ready.
    - (* SC_Cas_Stuck is impossible: the full points-to makes [l] writable. *)
      iDestruct (big_sepM_delete _ _ i with "Hts") as "[Ht Hts]"; first done.
      iEval (rewrite sqex_thread_ready (exwp_ext_unfold _ _ _ _ _ Hext)) in "Ht".
      iMod "Ht" as ([z_cur z_exp]) "[[-> Hl] Hcont]". simpl.
      iDestruct (sqex_external_writable with "Hm Hl Hts") as %[_ Hw]; [done | done |].
      exfalso. apply Ho. by apply Forall_singleton.
    - (* Spawn *)
      iDestruct (big_sepM_delete _ _ i with "Hts") as "[Ht Hts]"; first done.
      iEval (rewrite sqex_thread_ready (exwp_ext_unfold _ _ _ _ _ Hspawn)) in "Ht".
      iMod "Ht" as (x) "[Hchild Hcont]". simpl.
      have Hne : i ≠ j by intros ->; congruence.
      have Hj0 : j ≠ 0%nat by intros ->; destruct H0; congruence.
      iModIntro. iNext.
      iMod ("Hcont" $! None with "[//]") as "Hwp".
      iModIntro. iFrame "Hm". iSplit.
      { iPureIntro. split; last by do 2 apply sqex_inv_zero.
        apply sqex_pool_reservations_spawn; last by rewrite lookup_insert_ne.
        by eapply sqex_pool_reservations_ready_update. }
      iApply big_sepM_insert; first by rewrite lookup_insert_ne.
      iSplitL "Hchild".
      { iApply sqex_thread_ready. rewrite /sqex_post decide_False //. }
      iApply big_sepM_insert_delete. iFrame "Hts". by iApply sqex_thread_ready.
  Qed.

  Lemma sqex_inv_implies_adequacy tp m mu i t :
    tp !! i = Some t ->
    sqex_inv tp m mu ⊢ |={⊤,∅}=> |={∅}▷=>
      ⌜am_not_stuck t m mu ∧ postcond_ok [φ] i t⌝.
  Proof.
    iIntros (Hi) "(Hm & [%Hres %H0] & Hts)".
    destruct t as [e T|]; last first.
    { iDestruct (big_sepM_lookup with "Hts") as "Ht"; first done. done. }
    destruct (decide (T = [])) as [->|HT]; last first.
    { iApply fupd_mask_intro_discard; first set_solver.
      iApply step_fupd_intro; first done. iNext. iPureIntro. split.
      - by eapply sqex_pool_reservations_pending_safe.
      - intros e0 v ? [= _ ->]. done. }
    iDestruct (big_sepM_delete _ _ i with "Hts") as "[Ht Hts]"; first done.
    iEval (rewrite sqex_thread_ready exwp_unfold /exwp_pre) in "Ht".
    destruct (to_val e) as [v|] eqn:Hv.
    { iMod "Ht" as "Hpost".
      iAssert (⌜i = 0%nat -> φ v⌝)%I with "[Hpost]" as %Hφ.
      { destruct (decide (i = 0%nat)) as [->|Hne].
        - iEval (rewrite /sqex_post /=) in "Hpost". iDestruct "Hpost" as %Hφ.
          iPureIntro. by intros _.
        - iPureIntro. by intros ?. }
      iApply fupd_mask_intro_discard; first set_solver.
      iApply step_fupd_intro; first done. iNext. iPureIntro. split.
      - left. exists e. split; first done. change (lr_final e). rewrite /lr_final Hv. by eexists.
      - intros e0 v0 φ0 [= <-] Hv0 [-> <-]%list_lookup_singleton_Some. rewrite Hv in Hv0. injection Hv0 as <-. by apply Hφ. }
    iMod "Ht" as "[[%Hno Hseq] | (%op & %k & %He & Hspec)]".
    - (* A sequential step that allocates outside the reservation map. *)
      iMod ("Hseq" with "Hm") as "[%Hred Hstep]".
      destruct Hred as (T0 & e0 & m0 & Hstep0).
      destruct (sqex_step_fresh_reservations _ _ _ _ _ mu Hstep0)
        as (T1 & e1 & m1 & Hstep1 & Hfresh).
      iSpecialize ("Hstep" $! T1 e1 m1 with "[//]").
      iApply fupd_mask_intro_discard; first set_solver.
      iModIntro. iNext. iMod "Hstep" as "[Hm1 (%ds & Htok & _)]".
      iDestruct (sqex_ready_conditions with "Hm1 Htok Hts") as %(Hread & Hwrite & _);
        [done | done | done | ].
      destruct (sqex_step_reservable _ _ _ _ _ mu Hstep1 Hread Hwrite Hfresh) as [mu1 Hrsv].
      iModIntro. iPureIntro. split.
      + right. eexists. eapply Core_Try; [apply sqex_singleton_lookup | exact Hstep1 | exact Hrsv].
      + intros e2 v2 ? [= <-] Hv2 ?. congruence.
    - (* An external call: its precondition enables the machine step. *)
      iMod "Hspec" as (x) "[Hpre _]".
      destruct op as [ly l|ly l w|ly l v_exp v_new|e_new]; simpl in x |- *.
      + destruct x as [q w]. simpl.
        iDestruct (sqex_external_readable with "Hm Hpre Hts") as %[Hw [n Hn]];
          [done | done | ].
        iModIntro. iApply step_fupd_intro; first done. iNext. iPureIntro.
        split; last (intros e2 v2 ? [= <-] Hv2 ?; congruence).
        right. eexists. eapply SC_Read; [apply sqex_singleton_lookup | exact He | | exact Hw].
        apply Forall_singleton. by rewrite Hn.
      + iDestruct (sqex_external_writable with "Hm Hpre Hts") as %[Hw Hn];
          [done | done | ].
        iModIntro. iApply step_fupd_intro; first done. iNext. iPureIntro.
        split; last (intros e2 v2 ? [= <-] Hv2 ?; congruence).
        right. eexists. eapply SC_Write; [apply sqex_singleton_lookup | exact He | | ].
        * by apply Forall_singleton.
        * by rewrite /= Hw.
      + destruct x as [z_cur z_exp]. simpl. iDestruct "Hpre" as "[-> Hl]".
        iDestruct (sqex_external_writable with "Hm Hl Hts") as %[Hw Hn];
          [done | done | ].
        iModIntro. iApply step_fupd_intro; first done. iNext. iPureIntro.
        split; last (intros e2 v2 ? [= <-] Hv2 ?; congruence).
        right. destruct (decide (z_cur = z_exp)) as [<-|Hne].
        * eexists. eapply (SC_Cas_Suc _ _ _ _ _ _ _ _ _ (LitV (LitInt z_cur)));
            [apply sqex_singleton_lookup | exact He | by apply Forall_singleton
            | exact Hw | | by rewrite /= Hw].
          change (sq_mem.lit_eq m (LitInt z_cur) (LitInt z_cur)). constructor.
        * eexists. eapply (SC_Cas_Fail _ _ _ _ _ _ _ _ _ (LitV (LitInt z_cur)));
            [apply sqex_singleton_lookup | exact He | | exact Hw | ].
          { apply Forall_singleton. by rewrite Hn. }
          change (lit_neq (LitInt z_exp) (LitInt z_cur)). constructor. done.
      + iModIntro. iApply step_fupd_intro; first done. iNext. iPureIntro.
        split; last (intros e2 v2 ? [= <-] Hv2 ?; congruence).
        right. eexists. eapply (Spawn _ _ _ _ _ _ _ 1%nat);
          [apply sqex_singleton_lookup | exact He | | ].
        * by rewrite sqex_singleton_lookup_1.
        * intros k0 Hk0. assert (k0 = 0%nat) as -> by lia. by rewrite sqex_singleton_lookup.
  Qed.

  Lemma sqex_sound n tp m mu tp' m' mu' i t :
    nsteps at_step n (AMCfg tp m mu) (AMCfg tp' m' mu') -> tp' !! i = Some t ->
    sqex_inv tp m mu ⊢ |={⊤,∅}=> |={∅}▷=>^(S n)
      ⌜am_not_stuck t m' mu' ∧ postcond_ok [φ] i t⌝.
  Proof.
    revert tp m mu. induction n as [|n IH]; intros tp m mu Hsteps Hi.
    - inversion Hsteps; subst. by iApply sqex_inv_implies_adequacy.
    - inversion Hsteps as [|n0 cfg1 [tp2 m2 mu2] cfg3 Hfirst Htail]; subst.
      iIntros "Hinv". iMod (at_step_preserves_sqex_inv with "Hinv") as "Hinv"; first done.
      iModIntro. rewrite Nat.iter_succ. iModIntro. iNext. iMod "Hinv".
      by iApply (IH with "Hinv").
  Qed.
End adequacy.

(** ** Adequacy *)

Theorem sqex_adequacy Σ `{!lrSqGpreS Σ} (e : sq_expr) (φ : sq_val -> Prop) (m : lr_mem) :
  (forall `{!lrSqGS Σ}, ⊢ EXWP e {{ v, ⌜φ v⌝ }}) ->
  at_sem_adequate [e] [φ] m.
Proof.
  intros Hwp tp' m' mu' Hrtc.
  change (rtc at_step (AMCfg {[0%nat := Running e []]} m (sq_mu m))
    (AMCfg tp' m' mu')) in Hrtc.
  destruct (rtc_nsteps_1 _ _ Hrtc) as [n Hsteps].
  assert (Hend : forall (i : nat) (t : tstate), tp' !! i = Some t ->
    am_not_stuck t m' mu' ∧ postcond_ok [φ] i t).
  { intros i t Hi. apply (pure_soundness (PROP := iPropI Σ)).
    apply (step_fupdN_soundness_lc (Σ := Σ) _ (S n) 0). intros Hinv. iIntros "_".
    iMod (sq_heap_init m) as (Hheap) "Hheap".
    set (Hgs := LrSqGS _ Hinv Hheap).
    iApply (@sqex_sound Σ Hgs φ n with "[Hheap]"); [exact Hsteps | exact Hi | ].
    iSplitL "Hheap"; first iExact "Hheap".
    iSplit.
    { iPureIntro. split; last by rewrite sqex_singleton_lookup.
      apply sqex_pool_reservations_init. intros j t' Ht'.
      apply (lookup_singleton_Some (M := gmap nat)) in Ht' as [_ <-]. done. }
    rewrite big_sepM_singleton. iApply sqex_thread_ready.
    rewrite /sqex_post /=. iApply (Hwp Hgs). }
  split; intros i t Hi.
  - exact (proj1 (Hend i t Hi)).
  - exact (proj2 (Hend i t Hi)).
Qed.
