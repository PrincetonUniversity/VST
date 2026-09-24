(** Safety of the atomic machine and the reference lambda-Rust semantics.

    The reference predicate below is the safety component of RustBelt/Iris
    adequacy (with a trivial result postcondition).  The current simulations
    prove reachability between stable configurations, not preservation of
    safety at all intermediate configurations.  Accordingly, the bridge
    proved here explicitly restricts its observations to stable states and
    its executions to the non-spawning fragment supported by the machine. *)

From Stdlib Require Import List Lia.
From stdpp Require Import gmap list.
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.event_semantics.
Require Import VST.atomic_machine.lambda_rust.reference.
Require Import VST.atomic_machine.lambda_rust.equivalence.

Import ListNotations.
Set Default Proof Using "Type".

Definition lr_final (e : expr) : Prop := is_Some (to_val e).

Definition lr_am_configuration (mc : lr_machine_configuration)
    : @am_configuration loc val _ _ lr_mem lr_layout lr_memory lr_language :=
  (lr_machine_threads mc, lr_machine_mem mc, lr_machine_rw mc).

Definition lr_am_safe (mc : lr_machine_configuration) : Prop :=
  am_safe lr_final (lr_am_configuration mc).

Definition lr_reference_not_stuck (e : expr) (sigma : state) : Prop :=
  lr_final e \/ reducible e sigma.

(** This uses the full reference [step], including thread creation. *)
Definition lr_reference_safe (rc : configuration) : Prop :=
  forall threads sigma,
    rtc step rc (threads, sigma) ->
    forall e, e ∈ threads -> lr_reference_not_stuck e sigma.

Lemma lr_am_steps mc mc' :
  lr_steps lr_machine_step mc mc' ->
  rtc am_step (lr_am_configuration mc) (lr_am_configuration mc').
Proof.
  induction 1; [ constructor | ].
  eapply rtc_l with (y := lr_am_configuration y);
    [ destruct x, y; exact H | exact IHlr_steps ].
Qed.

Lemma lr_am_safe_reachable mc mc' :
  lr_am_safe mc -> lr_steps lr_machine_step mc mc' -> lr_am_safe mc'.
Proof. intros Hsafe Hsteps. eapply am_safe_reachable; eauto using lr_am_steps. Qed.

Lemma lr_stable_backward_heaps sigma m mu :
  lr_stable_heaps_match sigma m mu -> lr_backward_heaps_match sigma m.
Proof.
  intros H l. specialize (H l).
  unfold lr_stable_heaps_match in H. unfold lr_backward_heaps_match.
  destruct (m !! l); naive_solver.
Qed.

(** At stable heaps, the ability of a particular machine thread to step
    implies that the same reference expression can step.  In contrast to
    the reachability simulations, this lemma cannot use zero reference
    steps to hide a machine step. *)
Lemma lr_stable_reducible e sigma m mu :
  lr_stable_heaps_match sigma m mu ->
  am_reducible (lr_running e []) m mu -> reducible e sigma.
Proof.
  intros Hstable (tp' & m' & mu' & Hstep).
  pose proof (lr_stable_backward_heaps _ _ _ Hstable) as Hheaps.
  pose proof (lr_backward_heaps_dom _ _ Hheaps) as Hdom.
  inversion Hstep; subst;
    unfold lr_tpool, tpool in *;
    apply lookup_singleton_Some in Hget as [Hi Hget];
    unfold lr_running in Hget; inversion Hget; subst.
  - change (lr_step c m T c' m') in Hstep0.
    inversion Hstep0 as [K e1 ? ? e2 ? Hhead]; subst.
    inversion Hhead; subst; unfold reducible.
    + do 3 eexists. apply EctxStep, BinOpS. by eapply bin_op_eval_dom.
    + do 3 eexists. apply EctxStep. by eapply BetaS.
    + do 3 eexists. apply EctxStep, (ReadNa1S l 0%nat).
      by eapply lr_backward_heaps_lookup.
    + do 3 eexists. apply EctxStep. eapply WriteNa1S; [ exact H | ].
      by eapply lr_backward_heaps_lookup.
    + do 3 eexists. apply EctxStep, AllocS; [ done | ].
      intros z. apply Hdom, H0.
    + do 3 eexists. apply EctxStep, FreeS; [ done | ].
      intros z. rewrite (lr_backward_heaps_is_Some _ _ _ Hheaps). apply H0.
    + do 3 eexists. apply EctxStep. by eapply CaseS.
  - contradiction.
  - inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst. simpl in Hload.
    do 3 eexists. apply EctxStep, (ReadScS l 0%nat).
    by eapply lr_backward_heaps_lookup.
  - inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst. simpl in Hstore.
    destruct (m !! l) as [v' | ] eqn:Hm; simplify_eq.
    do 3 eexists. apply EctxStep. eapply WriteScS; [ done | ].
    by eapply lr_backward_heaps_lookup.
  - inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst.
    simpl in Hload, Hstore. change (lr_val_eq m v_cur (LitV lit1)) in Heq.
    destruct v_cur as [litl | ]; [ | contradiction ]. simpl in Heq.
    do 3 eexists. apply EctxStep. eapply CasSucS; eauto.
    + by eapply lr_backward_heaps_lookup.
    + by eapply lit_eq_dom.
  - inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst.
    simpl in Hload. change (lr_val_neq m' v_cur (LitV lit1)) in Hneq.
    destruct v_cur as [litl | ]; [ | contradiction ]. simpl in Hneq.
    do 3 eexists. apply EctxStep. eapply (CasFailS l 0%nat); eauto.
    + by eapply lr_backward_heaps_lookup.
    + by eapply lit_neq_dom.
  - exfalso. apply Ho. destruct ly. simpl in Hload. simpl.
    apply Forall_singleton. specialize (Hstable l).
    unfold lr_stable_heaps_match in Hstable. rewrite Hload in Hstable.
    tauto.
Qed.

Lemma lr_stable_not_stuck e t sigma m mu :
  lr_stable_heaps_match sigma m mu ->
  lr_stable_thread_match e t ->
  am_not_stuck lr_final t m mu -> lr_reference_not_stuck e sigma.
Proof.
  intros Hheaps Hthread Hsafe. inversion Hthread; subst.
  destruct Hsafe as [(c & Hc & Hfinal) | Hred].
  - left. unfold lr_running in Hc. by inversion Hc; subst.
  - right. by eapply lr_stable_reducible.
Qed.

(** A consequence of full AM safety, using the existing stable reachability
    equivalence.  Both the stable endpoint and non-spawning execution
    restrictions are essential to the scope of this theorem. *)
Theorem lr_am_safe_reference_stable rc0 mc0 threads sigma mc :
  lr_stable_configuration_match rc0 mc0 ->
  lr_am_safe mc0 ->
  lr_steps lr_reference_step rc0 (threads, sigma) ->
  lr_stable_configuration_match (threads, sigma) mc ->
  forall e, e ∈ threads -> lr_reference_not_stuck e sigma.
Proof.
  intros Hinitial Hsafe Hsteps Hstable e He.
  pose proof (proj1 (lambda_rust_reachability_equivalence _ _ _ _ Hinitial Hstable)
    Hsteps) as Hmachine.
  pose proof (lr_am_safe_reachable _ _ Hsafe Hmachine) as Hsafe'.
  destruct mc as [tp m mu]. destruct Hstable as [Hpools Hheaps]. simpl in *.
  apply list_elem_of_lookup_1 in He as [i He].
  destruct (lr_pools_match_lookup_l _ _ _ _ _ Hpools He) as (t & Ht & Hthread).
  eapply lr_stable_not_stuck; [ exact Hheaps | exact Hthread | ].
  apply (Hsafe' tp m mu (rtc_refl _ _) i t Ht).
Qed.

(** Why the existing simulations cannot directly transport full safety.

    [LRForwardStuck] can relate a crashed reference thread to a terminated,
    safe machine thread.  This is not a counterexample to safety equivalence
    from corresponding stable initial states: the crashed reference state
    below is not stable.  It does rule out treating the existing forward
    relation as a progress-reflecting simulation. *)

Lemma lr_step_not_val e m T e' m' :
  lr_step e m T e' m' -> to_val e = None.
Proof.
  intros Hstep. inversion Hstep; subst. apply fill_not_val.
  by inversion H.
Qed.

Lemma lr_external_not_val e op k :
  lr_external e op k -> to_val e = None.
Proof.
  intros Hext. inversion Hext; subst. apply fill_not_val.
  by inversion H.
Qed.

Lemma lr_value_not_reducible v m mu :
  ~ am_reducible (lr_running (of_val v) []) m mu.
Proof.
  intros (tp' & m' & mu' & Hstep). inversion Hstep; subst;
    unfold lr_tpool, tpool in *;
    apply lookup_singleton_Some in Hget as [Hi Hget];
    unfold lr_running in Hget; inversion Hget; subst; try contradiction.
  all: try (apply lr_step_not_val in Hstep0; by rewrite to_of_val in Hstep0).
  all: apply lr_external_not_val in Hext; by rewrite to_of_val in Hext.
Qed.

Lemma lr_stuck_term_not_safe sigma :
  ~ lr_reference_not_stuck stuck_term sigma.
Proof.
  intros [[v Hv] | (e' & sigma' & spawned & Hstep)]; [ discriminate | ].
  exact (crashed_no_step [] sigma e' sigma' spawned Hstep).
Qed.

Theorem lr_forward_match_does_not_reflect_safety :
  exists rc mc,
    lr_forward_configuration_match rc mc /\
    lr_am_safe mc /\ ~ lr_reference_safe rc.
Proof.
  exists ([stuck_term], ∅),
    {| lr_machine_threads := {[0%nat := lr_running (of_val (LitV LitPoison)) []]};
       lr_machine_mem := ∅;
       lr_machine_rw := ∅ |}.
  split.
  - split.
    + intros [ | i]; unfold lr_tpool, tpool; simpl.
      * rewrite lookup_singleton_eq. apply (LRForwardStuck []).
      * rewrite lookup_singleton_ne; [ done | lia ].
    + intros l. unfold lr_mem, lr_rw_map, rw_map, state.
      by rewrite !lookup_empty.
  - split.
    + apply am_safe_final_singleton.
      * exists (LitV LitPoison). apply to_of_val.
      * apply lr_value_not_reducible.
    + intros Hsafe. apply (lr_stuck_term_not_safe ∅).
      apply (Hsafe [stuck_term] ∅ (rtc_refl _ _) stuck_term).
      by left.
Qed.
