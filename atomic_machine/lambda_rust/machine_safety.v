(** * Reference safety implies machine safety

    [lr_reference_safe] implies [am_safe] for the lambda-Rust instance of
    the atomic machine, from stably matched initial configurations.  This
    is the converse of [safety_reflection.v].

    The proof is a backward simulation (the machine drives) with the same
    shape of relation as in [safety_reflection.v]: a machine thread that
    has done [Core_Try] of a non-atomic access is matched by a reference
    thread that has done the first half ([Na1Ord]), and the reader/writer
    map mirrors the reference lock states.  Two machine-only states have no
    reference counterpart and are matched by the reference thread that has
    already finished the corresponding step:
    - a pending allocation, whose [Core_Commit] changes nothing;
    - a pending deallocation, whose [Core_Commit] deletes the reservations
      of the freed range.  Between [Core_Try] and [Core_Commit] such a
      range is unallocated in both memories but still present in the
      reader/writer map; [lr_frees_ok] records this, and that the ranges of
      distinct pending deallocations are disjoint.

    Reference safety is used throughout, not only at the end:
    - a pending access holds its lock, since otherwise the reference
      thread could not do its second half; so no other thread writes or
      frees its location, which keeps the value a pending read obtained on
      the machine side equal to the one the reference will read;
    - a machine step with no matching reference step (a racy [CAS]) is
      matched by a reference step to, or from, an unsafe configuration. *)

From Stdlib Require Import List Lia.
From stdpp Require Import gmap list.
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.event_semantics.
Require Import VST.atomic_machine.lambda_rust.reference.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Import VST.atomic_machine.lambda_rust.adequacy.
Require Import VST.atomic_machine.lambda_rust.safety_reflection.

Import ListNotations.
Open Scope lambda_rust_loc_scope.
Set Default Proof Using "Type".

(** * The relation *)

(** As [lr_tight_heaps_match], except that the reader/writer map is
    unconstrained at unallocated locations: a pending deallocation keeps
    its reservations until it commits. *)
Definition lr_back_heaps_match
    (sigma : state) (m : lr_mem) (mu : lr_rw_map) : Prop :=
  forall l,
    match m !! l with
    | Some v =>
        (exists st v0, sigma !! l = Some (st, v0) /\
           mu !! l = Some (lr_lock st) /\ (st = WSt \/ v0 = v)) /\
        na2_free (of_val v) = true
    | None => sigma !! l = None
    end.

Inductive lr_back_thread_match (m : lr_mem) : expr -> lr_tstate -> Prop :=
| LRBackSame e :
    na2_free e = true ->
    lr_back_thread_match m e (lr_running e [])
| LRBackRead K l v :
    na2_free (fill K (of_val v)) = true ->
    m !! l = Some v ->
    lr_back_thread_match m
      (fill K (Read Na2Ord (Lit (LitLoc l))))
      (lr_running (fill K (of_val v)) [lr_read_event l])
| LRBackWrite K l e v :
    to_val e = Some v ->
    na2_free (fill K (Lit LitPoison)) = true ->
    m !! l = Some v ->
    lr_back_thread_match m
      (fill K (Write Na2Ord (Lit (LitLoc l)) e))
      (lr_running (fill K (Lit LitPoison)) [lr_write_event l])
| LRBackAlloc e l n :
    (0 < n)%nat ->
    na2_free e = true ->
    lr_back_thread_match m e (lr_running e (lr_alloc_events l n))
| LRBackFree e l n :
    (0 < n)%nat ->
    na2_free e = true ->
    lr_back_thread_match m e (lr_running e (lr_free_events l n)).

(** Pending deallocations: their locations are unallocated but still
    reserved, and no location is being freed by two threads. *)
Definition lr_frees_ok (tp : lr_tpool) (m : lr_mem) (mu : lr_rw_map) : Prop :=
  (forall j c T l, tp !! j = Some (lr_running c T) -> lr_free_event l ∈ T ->
     m !! l = None /\ is_Some (mu !! l)) /\
  (forall j j' c c' T T' l, j <> j' ->
     tp !! j = Some (lr_running c T) -> tp !! j' = Some (lr_running c' T') ->
     lr_free_event l ∈ T -> lr_free_event l ∈ T' -> False).

Definition lr_back_configuration_match
    (rc : configuration) (mc : lr_machine_configuration) : Prop :=
  let '(threads, sigma) := rc in
  lr_pools_match (lr_back_thread_match (lr_machine_mem mc))
    threads (lr_machine_threads mc) /\
  lr_back_heaps_match sigma (lr_machine_mem mc) (lr_machine_rw mc) /\
  lr_frees_ok (lr_machine_threads mc) (lr_machine_mem mc) (lr_machine_rw mc).

Lemma lr_stable_back rc mc :
  lr_stable_configuration_match rc mc -> lr_back_configuration_match rc mc.
Proof.
  destruct rc as (threads, sigma). intros (Hpools & Hheaps). split; [ | split ].
  - eapply lr_pools_match_impl; [ | exact Hpools ]. intros ? ? []. by constructor.
  - intros l. specialize (Hheaps l). lr_unfold. destruct (_ !! l); [ | naive_solver ].
    destruct Hheaps as (Hs & Hmu & Hv). split; [ | done ].
    exists (RSt 0), v. auto.
  - split.
    + intros j c T l Hj Hl.
      destruct (lr_pools_match_lookup_r _ _ _ _ _ Hpools Hj) as (e & _ & Hthread).
      inversion Hthread; subst. unfold lr_running in *. simplify_eq.
      by apply not_elem_of_nil in Hl.
    + intros j j' c c' T T' l _ Hj _ Hl _.
      destruct (lr_pools_match_lookup_r _ _ _ _ _ Hpools Hj) as (e & _ & Hthread).
      inversion Hthread; subst. unfold lr_running in *. simplify_eq.
      by apply not_elem_of_nil in Hl.
Qed.

(** * Heaps *)

Lemma lr_back_heaps_lookup sigma m mu l st v0 :
  lr_back_heaps_match sigma m mu -> sigma !! l = Some (st, v0) ->
  exists v, m !! l = Some v /\ mu !! l = Some (lr_lock st) /\
    (st = WSt \/ v0 = v) /\ na2_free (of_val v) = true.
Proof.
  intros Hheaps Hs. specialize (Hheaps l). unfold lr_back_heaps_match in *.
  unfold lr_mem, lr_rw_map, rw_map, state in *.
  destruct (m !! l) as [v | ]; [ | congruence ].
  destruct Hheaps as ((st' & v0' & Hs' & Hmu & Hv) & Hna2).
  rewrite Hs in Hs'. simplify_eq. eauto.
Qed.

Lemma lr_back_heaps_lookup_m sigma m mu l v :
  lr_back_heaps_match sigma m mu -> m !! l = Some v ->
  exists st v0, sigma !! l = Some (st, v0) /\ mu !! l = Some (lr_lock st) /\
    (st = WSt \/ v0 = v) /\ na2_free (of_val v) = true.
Proof.
  intros Hheaps Hm. specialize (Hheaps l). unfold lr_back_heaps_match in *.
  unfold lr_mem, lr_rw_map, rw_map, state in *. rewrite Hm in Hheaps. naive_solver.
Qed.

Lemma lr_back_heaps_none sigma m mu l :
  lr_back_heaps_match sigma m mu -> (sigma !! l = None <-> m !! l = None).
Proof.
  intros Hheaps. specialize (Hheaps l). unfold lr_back_heaps_match in *.
  unfold lr_mem, lr_rw_map, rw_map, state in *.
  destruct (m !! l); [ | naive_solver ].
  destruct Hheaps as ((st & v0 & Hs & _) & _). rewrite Hs. naive_solver.
Qed.

Lemma lr_back_heaps_is_Some sigma m mu l :
  lr_back_heaps_match sigma m mu -> is_Some (sigma !! l) <-> is_Some (m !! l).
Proof.
  intros Hheaps. pose proof (lr_back_heaps_none _ _ _ l Hheaps) as Hiff.
  rewrite <- !not_eq_None_Some. naive_solver.
Qed.

Lemma lr_back_heaps_insert sigma m mu l st v0 v :
  lr_back_heaps_match sigma m mu ->
  (st = WSt \/ v0 = v) -> na2_free (of_val v) = true ->
  lr_back_heaps_match (<[l := (st, v0)]> sigma) (<[l := v]> m) (<[l := lr_lock st]> mu).
Proof.
  intros Hheaps Hv Hna2 l'. specialize (Hheaps l'). unfold lr_back_heaps_match in *.
  unfold lr_mem, lr_rw_map, rw_map, state in *.
  destruct (decide (l = l')) as [<- | ]; [ rewrite !lookup_insert_eq | by rewrite !lookup_insert_ne ].
  split; [ | done ]. eauto.
Qed.

Lemma lr_back_heaps_alloc sigma m mu l n :
  lr_back_heaps_match sigma m mu ->
  lr_back_heaps_match
    (init_mem (RSt 0, LitV LitPoison) l n sigma)
    (init_mem (LitV LitPoison) l n m)
    (init_mem (Rst 0) l n mu).
Proof.
  intros Hheaps l'. specialize (Hheaps l'). unfold lr_back_heaps_match in *.
  unfold lr_mem, lr_rw_map, rw_map, state in *. rewrite !lookup_init_mem.
  case_decide; [ | done ]. split; [ | done ]. exists (RSt 0), (LitV LitPoison). auto.
Qed.

(** Deallocation on the memories only; the reservations stay. *)
Lemma lr_back_heaps_free sigma m mu l n :
  lr_back_heaps_match sigma m mu ->
  lr_back_heaps_match (free_mem l n sigma) (free_mem l n m) mu.
Proof.
  intros Hheaps l'. specialize (Hheaps l'). unfold lr_back_heaps_match in *.
  unfold lr_mem, lr_rw_map, rw_map, state in *. rewrite !lookup_free_mem.
  by case_decide.
Qed.

(** Changing the reader/writer map at unallocated locations only. *)
Lemma lr_back_heaps_mu sigma m mu mu' :
  lr_back_heaps_match sigma m mu ->
  (forall l, is_Some (m !! l) -> mu' !! l = mu !! l) ->
  lr_back_heaps_match sigma m mu'.
Proof.
  intros Hheaps Hmu l. specialize (Hheaps l). unfold lr_back_heaps_match in *.
  destruct (m !! l) eqn:Hm; [ | done ]. rewrite Hmu; [ done | by eexists ].
Qed.

(** * Event lists *)

Lemma lr_free_event_elem_of l n l' :
  lr_free_event l' ∈ lr_free_events l n <-> loc_in_range l n l'.
Proof.
  revert l. induction n as [ | n IH ]; intros l.
  - unfold lr_free_events. simpl. rewrite elem_of_nil. unfold loc_in_range. lia.
  - unfold lr_free_events in *. simpl. rewrite elem_of_cons, IH.
    unfold lr_free_event. destruct l as [b o], l' as [b' o'].
    unfold loc_in_range, shift_loc. simpl. split.
    + intros [Heq | (-> & Hr)]; [ injection Heq as -> -> | ]; lia.
    + intros (-> & Hr). destruct (decide (o' = o)) as [-> | ]; [ by left | right ]. lia.
Qed.

Lemma lr_free_event_shift l n z :
  (0 <= z < Z.of_nat n)%Z -> lr_free_event (l +ₗ z)%L ∈ lr_free_events l n.
Proof.
  intros Hz. apply lr_free_event_elem_of. destruct l as [b o].
  unfold loc_in_range, shift_loc. simpl. lia.
Qed.

Lemma lr_free_event_not_alloc l n l' : lr_free_event l' ∉ lr_alloc_events l n.
Proof.
  revert l. induction n as [ | n IH ]; intros l; unfold lr_alloc_events in *; simpl;
    [ apply not_elem_of_nil | ].
  rewrite elem_of_cons. intros [Heq | Hin]; [ discriminate | by eapply IH ].
Qed.

Lemma lr_free_event_not_read l l' : lr_free_event l' ∉ [lr_read_event l].
Proof. rewrite list_elem_of_singleton. discriminate. Qed.

Lemma lr_free_event_not_write l l' : lr_free_event l' ∉ [lr_write_event l].
Proof. rewrite list_elem_of_singleton. discriminate. Qed.

(** Nonempty allocation/deallocation event lists are neither empty nor a
    single read or write. *)
Ltac lr_events_absurd :=
  match goal with
  | H : lr_alloc_events _ ?n = _ |- _ =>
      destruct n; [ lia | unfold lr_alloc_events in H; simpl in H;
                          first [ discriminate H | injection H as H; discriminate H ] ]
  | H : lr_free_events _ ?n = _ |- _ =>
      destruct n; [ lia | unfold lr_free_events in H; simpl in H;
                          first [ discriminate H | injection H as H; discriminate H ] ]
  end.

Lemma lr_rsv_alloc_events_inv (mu mu' : lr_rw_map) l n :
  rsv (lr_alloc_events l n) mu = Some mu' ->
  mu' = init_mem (Rst 0) l n mu /\
  (forall z, (0 <= z < Z.of_nat n)%Z -> mu !! (l +ₗ z)%L = None).
Proof.
  revert l mu'. induction n as [ | n IH ]; intros l mu' Hrsv.
  - unfold lr_alloc_events, rsv in Hrsv. simpl in Hrsv. injection Hrsv as <-. split; [ done | lia ].
  - unfold lr_alloc_events, rsv in *. simpl in Hrsv.
    destruct (foldr _ _ _) as [mu1 | ] eqn:Hrest; [ | discriminate ].
    destruct (IH _ _ Hrest) as (-> & Hrange). simpl in Hrsv. unfold rsv_Alloc in Hrsv.
    unfold lr_rw_map, rw_map in *.
    rewrite lookup_init_mem in Hrsv. case_decide as Hin.
    { destruct l. unfold loc_in_range, shift_loc in Hin. simpl in Hin. lia. }
    destruct (mu !! l) eqn:Hl; [ discriminate | ]. injection Hrsv as <-. split; [ done | ].
    intros z Hz. destruct (decide (z = 0%Z)) as [-> | ]; [ by rewrite shift_loc_0 | ].
    replace z with (1 + (z - 1))%Z by lia. rewrite <- shift_loc_assoc. apply Hrange. lia.
Qed.

(** * Freshness *)

Lemma lr_fresh_block (m : lr_mem) (mu : lr_rw_map) :
  exists l, forall z, m !! (l +ₗ z)%L = None /\ mu !! (l +ₗ z)%L = None.
Proof.
  unfold lr_mem, lr_rw_map, rw_map in *.
  set (B := (set_map fst (dom m) ∪ set_map fst (dom mu) : gset block)).
  exists (fresh B, 0%Z). intros z. unfold shift_loc. simpl.
  split; apply not_elem_of_dom_1; intros Hin; apply (is_fresh B);
    [ apply elem_of_union_l | apply elem_of_union_r ];
    change (fresh B) with (fst (fresh B, (0 + z)%Z)); by apply elem_of_map_2.
Qed.

(** * Reference facts *)

Lemma lr_reference_safe_now rc :
  lr_reference_safe rc -> forall e, e ∈ rc.1 -> lr_reference_not_stuck e rc.2.
Proof. destruct rc as (threads, sigma). intros Hsafe. exact (Hsafe _ _ (rtc_refl _ _)). Qed.

Lemma lr_reference_safe_step rc rc' :
  lr_reference_safe rc -> step rc rc' -> lr_reference_safe rc'.
Proof. intros Hsafe Hstep threads sigma Hsteps. apply Hsafe. by eapply rtc_l. Qed.

Lemma lr_steps_rtc rc rc' : lr_steps step rc rc' -> rtc step rc rc'.
Proof. induction 1; [ constructor | by eapply rtc_l ]. Qed.

Lemma lr_reference_safe_steps rc rc' :
  lr_reference_safe rc -> lr_steps step rc rc' -> lr_reference_safe rc'.
Proof.
  intros Hsafe Hsteps threads sigma Hsteps'. apply Hsafe.
  eapply rtc_trans; [ by apply lr_steps_rtc | exact Hsteps' ].
Qed.

Lemma lr_not_stuck_read_na2 K l sigma :
  lr_reference_not_stuck (fill K (Read Na2Ord (Lit (LitLoc l)))) sigma ->
  exists n v, sigma !! l = Some (RSt (S n), v).
Proof.
  intros [[v Hv] | (e' & sigma' & spawned & Hstep)].
  { by rewrite fill_not_val in Hv. }
  inversion Hstep as [K' e1' ? e2' ? ? Hhead HK]; subst.
  destruct (fill_redex_unique K' K e1' (Read Na2Ord (Lit (LitLoc l)))
              (head_step_redex_shape _ _ _ _ _ Hhead) (na2_read_redex_shape l)
              (head_step_not_val _ _ _ _ _ Hhead) eq_refl HK) as (-> & ->).
  inversion Hhead; subst. eauto.
Qed.

Lemma lr_not_stuck_write_na2 K l e v sigma :
  to_val e = Some v ->
  lr_reference_not_stuck (fill K (Write Na2Ord (Lit (LitLoc l)) e)) sigma ->
  exists v', sigma !! l = Some (WSt, v').
Proof.
  intros He [[w Hw] | (e' & sigma' & spawned & Hstep)].
  { by rewrite fill_not_val in Hw. }
  inversion Hstep as [K' e1' ? e2' ? ? Hhead HK]; subst.
  destruct (fill_redex_unique K' K e1' (Write Na2Ord (Lit (LitLoc l)) e)
              (head_step_redex_shape _ _ _ _ _ Hhead) (na2_write_redex_shape l e v He)
              (head_step_not_val _ _ _ _ _ Hhead) eq_refl HK) as (-> & ->).
  inversion Hhead; subst. eauto.
Qed.

(** A [CAS] on a location under a write lock has no reference step. *)
Lemma lr_not_stuck_cas_wst K l e1 e2 lit1 lit2 sigma v' :
  to_val e1 = Some (LitV lit1) -> to_val e2 = Some (LitV lit2) ->
  sigma !! l = Some (WSt, v') ->
  ~ lr_reference_not_stuck (fill K (CAS (Lit (LitLoc l)) e1 e2)) sigma.
Proof.
  intros He1 He2 Hs [[w Hw] | (e' & sigma' & spawned & Hstep)].
  { by rewrite fill_not_val in Hw. }
  assert (Hshape : redex_shape (CAS (Lit (LitLoc l)) e1 e2)).
  { intros Ki e'' Heq. destruct Ki; simplify_eq/=; eauto. }
  inversion Hstep as [K' e1' ? e2' ? ? Hhead HK]; subst.
  destruct (fill_redex_unique K' K e1' (CAS (Lit (LitLoc l)) e1 e2)
              (head_step_redex_shape _ _ _ _ _ Hhead) Hshape
              (head_step_not_val _ _ _ _ _ Hhead) eq_refl HK) as (-> & ->).
  inversion Hhead; subst; unfold state in *; congruence.
Qed.

(** * Pending accesses hold their locks *)

Definition lr_back_ref_ok (threads : list expr) (sigma : state) : Prop :=
  forall e, e ∈ threads -> lr_reference_not_stuck e sigma.

Lemma lr_back_pending_locked threads sigma tp m mu j t l :
  lr_pools_match (lr_back_thread_match m) threads tp ->
  lr_back_heaps_match sigma m mu ->
  lr_back_ref_ok threads sigma ->
  tp !! j = Some t -> lr_pending t l ->
  exists st, mu !! l = Some st /\ st <> Rst 0.
Proof.
  intros Hpools Hheaps Hok Hj (c & Ht).
  destruct (lr_pools_match_lookup_r _ _ _ _ _ Hpools Hj) as (e & He & Hthread).
  pose proof (Hok e (list_elem_of_lookup_2 _ _ _ He)) as Hns.
  destruct Ht as [-> | ->]; inversion Hthread; subst; unfold lr_running in *; simplify_eq;
    try lr_events_absurd.
  - destruct (lr_not_stuck_read_na2 _ _ _ Hns) as (n & v0 & Hs).
    destruct (lr_back_heaps_lookup _ _ _ _ _ _ Hheaps Hs) as (w & _ & Hmu & _).
    eexists. split; [ exact Hmu | discriminate ].
  - destruct (lr_not_stuck_write_na2 _ _ _ _ _ H1 Hns) as (v' & Hs).
    destruct (lr_back_heaps_lookup _ _ _ _ _ _ Hheaps Hs) as (w & _ & Hmu & _).
    eexists. split; [ exact Hmu | discriminate ].
Qed.

(** * Frames *)

Lemma lr_back_thread_frame m m' e t :
  lr_back_thread_match m e t ->
  (forall l, lr_pending t l -> m' !! l = m !! l) ->
  lr_back_thread_match m' e t.
Proof.
  intros Hthread Hframe. inversion Hthread; subst.
  - by constructor.
  - apply LRBackRead; [ done | ]. rewrite Hframe; [ done | ]. eexists. by left.
  - apply LRBackWrite with v; [ done | done | ]. rewrite Hframe; [ done | ]. eexists. by right.
  - by constructor.
  - by constructor.
Qed.

Lemma lr_back_pools_update m m' threads tp i e c :
  lr_pools_match (lr_back_thread_match m) threads tp ->
  lr_frame tp m m' ->
  is_Some (threads !! i) ->
  lr_back_thread_match m' e c ->
  lr_pools_match (lr_back_thread_match m') (<[i := e]> threads) (<[i := c]> tp).
Proof.
  intros Hpools Hframe Hi Hthread. apply lr_pools_match_insert; [ | done | done ].
  intros j. specialize (Hpools j). unfold lr_tpool, tpool in *.
  destruct (threads !! j), (tp !! j) as [t | ] eqn:Hj; try done.
  eapply lr_back_thread_frame; [ exact Hpools | ]. intros l. by eapply Hframe.
Qed.

(** Writing a location at [Rst 0]: no pending thread is there. *)
Lemma lr_back_frame_write threads sigma tp m mu l v :
  lr_pools_match (lr_back_thread_match m) threads tp ->
  lr_back_heaps_match sigma m mu ->
  lr_back_ref_ok threads sigma ->
  mu !! l = Some (Rst 0) ->
  lr_frame tp m (<[l := v]> m).
Proof.
  intros Hpools Hheaps Hok Hmu j t l' Hj Hpend.
  destruct (lr_back_pending_locked _ _ _ _ _ _ _ _ Hpools Hheaps Hok Hj Hpend) as (st & Hst & Hne).
  unfold lr_mem. rewrite lookup_insert_ne; [ done | ]. intros <-.
  unfold lr_rw_map, rw_map in *. rewrite Hmu in Hst. congruence.
Qed.

(** Allocating fresh locations: pending threads are at allocated ones. *)
Lemma lr_back_frame_alloc threads tp m l n (x : val) :
  lr_pools_match (lr_back_thread_match m) threads tp ->
  (forall z, m !! (l +ₗ z)%L = None) ->
  lr_frame tp m (init_mem x l n m).
Proof.
  intros Hpools Hfresh j t l' Hj Hpend.
  destruct (lr_pools_match_lookup_r _ _ _ _ _ Hpools Hj) as (e & _ & Hthread).
  assert (Hsome : is_Some (m !! l')).
  { destruct Hpend as (c & [-> | ->]); inversion Hthread; subst; unfold lr_running in *;
      simplify_eq; first [ by eexists | lr_events_absurd ]. }
  unfold lr_mem in *. rewrite lookup_init_mem. case_decide as Hin; [ | done ].
  destruct (loc_in_range_shift _ _ _ Hin) as (z & ->).
  rewrite Hfresh in Hsome. by destruct Hsome.
Qed.

(** * Single-thread machine reductions *)

Lemma lr_singleton_lookup (t : lr_tstate) : ({[0%nat := t]} : lr_tpool) !! 0%nat = Some t.
Proof. unfold lr_tpool, tpool. apply lookup_singleton_eq. Qed.

Lemma lr_red_try c m mu T c' m' mu' :
  lr_step c m T c' m' -> rsv T mu = Some mu' -> am_reducible (lr_running c []) m mu.
Proof.
  intros Hstep Hrsv. eexists _, _, _.
  exact (lr_machine_try _ m mu 0 c T c' m' mu' (lr_singleton_lookup _) Hstep Hrsv).
Qed.

Lemma lr_red_sc_read c m mu l v K :
  lr_external c (ALoad tt l) K -> mu !! l <> Some Wst -> m !! l = Some v ->
  am_reducible (lr_running c []) m mu.
Proof.
  intros Hext Hmu Hm. eexists _, _, _.
  exact (lr_machine_sc_read _ m mu 0 c l v K (lr_singleton_lookup _) Hext Hmu Hm).
Qed.

Lemma lr_red_sc_write c m mu l v v' K :
  lr_external c (AStore tt l v) K -> mu !! l = Some (Rst 0) -> m !! l = Some v' ->
  am_reducible (lr_running c []) m mu.
Proof.
  intros Hext Hmu Hm. eexists _, _, _.
  exact (lr_machine_sc_write _ m mu 0 c l v v' K (lr_singleton_lookup _) Hext Hmu Hm).
Qed.

Lemma lr_red_cas_suc c m mu l lit_exp lit_new lit_cur K :
  lr_external c (ACAS tt l (LitV lit_exp) (LitV lit_new)) K ->
  mu !! l = Some (Rst 0) -> m !! l = Some (LitV lit_cur) -> lit_eq m lit_exp lit_cur ->
  am_reducible (lr_running c []) m mu.
Proof.
  intros Hext Hmu Hm Heq. eexists _, _, _.
  exact (lr_machine_cas_suc _ m mu 0 c l lit_exp lit_new lit_cur K (lr_singleton_lookup _) Hext Hmu Hm Heq).
Qed.

Lemma lr_red_cas_fail c m mu l lit_exp lit_new lit_cur K :
  lr_external c (ACAS tt l (LitV lit_exp) (LitV lit_new)) K ->
  mu !! l <> Some Wst -> m !! l = Some (LitV lit_cur) -> lit_neq m lit_exp lit_cur ->
  am_reducible (lr_running c []) m mu.
Proof.
  intros Hext Hmu Hm Hneq. eexists _, _, _.
  exact (lr_machine_cas_fail _ m mu 0 c l lit_exp lit_new lit_cur K (lr_singleton_lookup _) Hext Hmu Hm Hneq).
Qed.

Lemma lr_red_cas_stuck c m mu l lit_exp lit_new lit_cur K :
  lr_external c (ACAS tt l (LitV lit_exp) (LitV lit_new)) K ->
  mu !! l <> Some (Rst 0) -> m !! l = Some (LitV lit_cur) -> lit_eq m lit_exp lit_cur ->
  am_reducible (lr_running c []) m mu.
Proof.
  intros Hext Hmu Hm Heq. eexists _, _, _.
  refine (SC_Cas_Stuck _ m mu 0 c tt l (LitV lit_exp) (LitV lit_new) (LitV lit_cur) K
            (lr_singleton_lookup _) Hext Hm _ _).
  - change (lr_val_eq m (LitV lit_cur) (LitV lit_exp)). exact Heq.
  - intros Hw. apply Forall_inv in Hw. by apply Hmu.
Qed.

Lemma lr_red_spawn K e m mu : am_reducible (lr_running (fill K (Fork e)) []) m mu.
Proof.
  eexists _, _, _. eapply (lr_machine_spawn _ m mu 0 K e 1); [ apply lr_singleton_lookup | | ].
  - reflexivity.
  - intros k Hk. assert (k = 0%nat) as -> by lia. by eexists.
Qed.

(** * Bookkeeping for the simulation step *)

Lemma loc_in_range_shift_range l n l' :
  loc_in_range l n l' -> exists z, (0 <= z < Z.of_nat n)%Z /\ l' = (l +ₗ z)%L.
Proof.
  destruct l as [b o], l' as [b' o']. unfold loc_in_range, shift_loc. simpl.
  intros (-> & Hr). exists (o' - o)%Z. split; [ lia | ]. f_equal. lia.
Qed.

Lemma lr_back_thread_idle m e c :
  lr_back_thread_match m e (lr_running c []) -> e = c /\ na2_free c = true.
Proof.
  intros Hthread. inversion Hthread; subst; unfold lr_running in *; simplify_eq; try lr_events_absurd.
  auto.
Qed.

(** Updating one thread.  The other threads' pending deallocations keep
    their memory and reservations; the updated thread's pending
    deallocations, if any, are unallocated, reserved, and nobody else's. *)
Lemma lr_frees_ok_update tp m mu m' mu' i t' :
  lr_frees_ok tp m mu ->
  (forall j c T l, j <> i -> tp !! j = Some (lr_running c T) -> lr_free_event l ∈ T ->
     m' !! l = m !! l /\ mu' !! l = mu !! l) ->
  (forall c T l, t' = lr_running c T -> lr_free_event l ∈ T ->
     m' !! l = None /\ is_Some (mu' !! l) /\
     forall j c'' T'', j <> i -> tp !! j = Some (lr_running c'' T'') -> lr_free_event l ∉ T'') ->
  lr_frees_ok (<[i := t']> tp) m' mu'.
Proof.
  intros (Hcov & Hdisj) Hothers Hnew. unfold lr_frees_ok, lr_tpool, tpool in *. split.
  - intros j c T l Hj Hl. destruct (decide (j = i)) as [-> | Hne].
    + rewrite lookup_insert_eq in Hj. injection Hj as ->.
      by destruct (Hnew c T l eq_refl Hl) as (? & ? & _).
    + rewrite lookup_insert_ne in Hj by done.
      destruct (Hothers j c T l Hne Hj Hl) as (-> & ->). by eapply Hcov.
  - intros j j' c c' T T' l Hne Hj Hj' Hl Hl'.
    destruct (decide (j = i)) as [-> | Hji]; destruct (decide (j' = i)) as [-> | Hj'i]; [ done | | | ].
    + rewrite lookup_insert_eq in Hj. injection Hj as ->.
      rewrite lookup_insert_ne in Hj' by done.
      destruct (Hnew c T l eq_refl Hl) as (_ & _ & Hno). by eapply Hno.
    + rewrite lookup_insert_eq in Hj'. injection Hj' as ->.
      rewrite lookup_insert_ne in Hj by done.
      destruct (Hnew c' T' l eq_refl Hl') as (_ & _ & Hno). by eapply Hno.
    + rewrite lookup_insert_ne in Hj by congruence. rewrite lookup_insert_ne in Hj' by congruence.
      exact (Hdisj j j' c c' T T' l Hne Hj Hj' Hl Hl').
Qed.

(** Updating one thread to a state with no pending deallocation. *)
Lemma lr_frees_ok_nofree tp m mu m' mu' i c' T' :
  lr_frees_ok tp m mu ->
  (forall l, lr_free_event l ∉ T') ->
  (forall l, m !! l = None -> is_Some (mu !! l) -> m' !! l = m !! l /\ mu' !! l = mu !! l) ->
  lr_frees_ok (<[i := lr_running c' T']> tp) m' mu'.
Proof.
  intros Hfrees HT' Hunch. apply lr_frees_ok_update with m mu; [ done | | ].
  - intros j c T l _ Hj Hl. apply Hunch; by eapply (proj1 Hfrees).
  - intros c T l Heq Hl. unfold lr_running in Heq. simplify_eq. by apply HT' in Hl.
Qed.

(** Changes at an allocated location leave pending deallocations alone. *)
Lemma lr_unchanged_insert (m : lr_mem) (mu : lr_rw_map) l v x :
  is_Some (m !! l) ->
  forall l', m !! l' = None -> is_Some (mu !! l') ->
    <[l := v]> m !! l' = m !! l' /\ <[l := x]> mu !! l' = mu !! l'.
Proof.
  intros [w Hl] l' Hl' _. unfold lr_mem, lr_rw_map, rw_map in *.
  assert (l <> l') by congruence. by rewrite !lookup_insert_ne.
Qed.

Lemma lr_back_pack threads sigma threads2 sigma2 tp2 m2 mu2 :
  lr_steps step (threads, sigma) (threads2, sigma2) ->
  lr_pools_match (lr_back_thread_match m2) threads2 tp2 ->
  lr_back_heaps_match sigma2 m2 mu2 ->
  lr_frees_ok tp2 m2 mu2 ->
  exists rc',
    lr_back_configuration_match rc'
      {| lr_machine_threads := tp2; lr_machine_mem := m2; lr_machine_rw := mu2 |} /\
    lr_steps step (threads, sigma) rc'.
Proof. intros. exists (threads2, sigma2). split; [ | done ]. by split; [ | split ]. Qed.

Lemma lr_not_stuck_crashed K sigma : ~ lr_reference_not_stuck (fill K stuck_term) sigma.
Proof.
  intros [[v Hv] | (e' & sigma' & spawned & Hstep)].
  - by rewrite fill_not_val in Hv.
  - exact (crashed_no_step _ _ _ _ _ Hstep).
Qed.

(** * The simulation step *)

Lemma lr_back_step rc mc mc' :
  lr_back_configuration_match rc mc ->
  lr_reference_safe rc ->
  lr_machine_step mc mc' ->
  exists rc', lr_back_configuration_match rc' mc' /\ lr_steps step rc rc'.
Proof.
  destruct rc as (threads, sigma). destruct mc as [tp m mu], mc' as [tp' m' mu'].
  intros (Hpools & Hheaps & Hfrees) Hsafe Hstep. simpl in Hpools, Hheaps, Hfrees.
  pose proof (lr_reference_safe_now _ Hsafe) as Hok. simpl in Hok.
  assert (Hdom : forall l, m !! l = None -> sigma !! l = None)
    by (intros l; apply (lr_back_heaps_none _ _ _ l Hheaps)).
  unfold lr_machine_step in Hstep. simpl in Hstep.
  inversion Hstep; subst;
    destruct (lr_pools_match_lookup_r _ _ _ _ _ Hpools Hget) as (e & He & Hthread);
    assert (Hsome : is_Some (threads !! i)) by (by eexists).
  - (* Core_Try *)
    apply lr_back_thread_idle in Hthread as (<- & Hna2c).
    change (lr_step e m T c' m') in Hstep0.
    inversion Hstep0 as [K e1 ? ? e2 ? Hhead]; subst.
    assert (Hna2 : na2_free e1 = true) by eauto using na2_free_fill_inv.
    inversion Hhead; subst.
    + (* BinOp *)
      injection Hreserve as <-.
      eapply lr_back_pack.
      * apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
        apply EctxStep, BinOpS. by eapply bin_op_eval_dom.
      * eapply lr_back_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
        constructor. by eapply na2_free_fill.
      * exact Hheaps.
      * eapply lr_frees_ok_nofree; [ exact Hfrees | intros ? [] % elem_of_nil | done ].
    + (* Beta *)
      injection Hreserve as <-. simpl in Hna2. na2_split.
      assert (Hna2' : na2_free e2 = true).
      { apply na2_free_subst_l with (f :: xl) (Rec f xl e :: el) e; [ | done | done ].
        by simpl; na2_split. }
      eapply lr_back_pack.
      * apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
        apply EctxStep. by eapply BetaS.
      * eapply lr_back_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
        constructor. by eapply na2_free_fill.
      * exact Hheaps.
      * eapply lr_frees_ok_nofree; [ exact Hfrees | intros ? [] % elem_of_nil | done ].
    + (* ReadNa: the reference does its first half. *)
      destruct (lr_rsv_read_inv _ _ _ Hreserve) as (n & Hmu).
      destruct (lr_back_heaps_lookup_m _ _ _ _ _ Hheaps H) as ([ | n' ] & v0 & Hs & Hmu' & Hv & Hvna2);
        unfold lr_rw_map, rw_map in *; rewrite Hmu in Hmu'; simpl in Hmu'; simplify_eq.
      destruct Hv as [ [=] | -> ].
      rewrite (lr_rsv_read mu l n' Hmu) in Hreserve. injection Hreserve as <-.
      eapply lr_back_pack.
      * apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
        apply EctxStep. by apply ReadNa1S.
      * eapply lr_back_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
        apply LRBackRead; [ by eapply na2_free_fill | done ].
      * unfold lr_mem in *. rewrite <- (insert_id m' l v) by done.
        by apply (lr_back_heaps_insert _ _ _ l (RSt (S n')) v v); [ | right | ].
      * eapply lr_frees_ok_nofree; [ exact Hfrees | apply lr_free_event_not_read | ].
        intros l' Hl' Hmu''. split; [ done | ].
        unfold lr_mem, lr_rw_map, rw_map in *. rewrite lookup_insert_ne; [ done | congruence ].
    + (* WriteNa: the reference does its first half; the machine already
         writes, at a location no pending access holds. *)
      apply lr_rsv_write_inv in Hreserve as Hmu.
      destruct (lr_back_heaps_lookup_m _ _ _ _ _ Hheaps H0) as ([ | n' ] & v0 & Hs & Hmu' & _ & _);
        unfold lr_rw_map, rw_map in *; rewrite Hmu in Hmu'; simpl in Hmu'; simplify_eq.
      rewrite (lr_rsv_write mu l Hmu) in Hreserve. injection Hreserve as <-.
      simpl in Hna2. rewrite <- (of_to_val e v H) in Hna2.
      eapply lr_back_pack.
      * apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
        apply EctxStep. by eapply WriteNa1S.
      * eapply lr_back_pools_update; [ exact Hpools | by eapply lr_back_frame_write | done | ].
        apply LRBackWrite with v; [ done | by eapply na2_free_fill | ].
        unfold lr_mem. apply lookup_insert_eq.
      * by apply (lr_back_heaps_insert _ _ _ l WSt v0 v); [ | left | ].
      * eapply lr_frees_ok_nofree; [ exact Hfrees | apply lr_free_event_not_write | ].
        intros l' Hl' Hmu''. unfold lr_mem, lr_rw_map, rw_map in *.
        rewrite !lookup_insert_ne; [ done | congruence | congruence ].
    + (* Alloc: the machine's fresh range is fresh for the reference too. *)
      destruct (lr_rsv_alloc_events_inv _ _ _ _ Hreserve) as (-> & Hmurange).
      eapply lr_back_pack.
      * apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
        apply EctxStep, AllocS; [ done | ]. intros z. apply Hdom, H0.
      * eapply lr_back_pools_update; [ exact Hpools | by eapply lr_back_frame_alloc | done | ].
        apply LRBackAlloc; [ lia | by eapply na2_free_fill ].
      * by apply lr_back_heaps_alloc.
      * eapply lr_frees_ok_nofree; [ exact Hfrees | apply lr_free_event_not_alloc | ].
        intros l' Hl' [st Hmu'']. unfold lr_mem, lr_rw_map, rw_map in *.
        rewrite !lookup_init_mem. case_decide as Hin; [ | done ].
        destruct (loc_in_range_shift_range _ _ _ Hin) as (z & Hz & ->).
        rewrite Hmurange in Hmu'' by done. discriminate.
    + (* Free: the reference frees at once; the machine keeps the
         reservations until it commits. *)
      rewrite lr_rsv_free_events in Hreserve. injection Hreserve as <-.
      set (n' := Z.to_nat n) in *.
      assert (Hrange : forall l0, loc_in_range l n' l0 -> is_Some (m !! l0)).
      { intros l0 Hin. destruct (loc_in_range_shift_range _ _ _ Hin) as (z & Hz & ->).
        apply H0. subst n'. rewrite Z2Nat.id in Hz by lia. lia. }
      assert (Hrs : step (threads, sigma) (<[i := fill K (Lit LitPoison)]> threads, free_mem l n' sigma)).
      { eapply lr_reference_step_at; [ exact He | ]. apply EctxStep, FreeS; [ done | ].
        intros z. rewrite (lr_back_heaps_is_Some _ _ _ _ Hheaps). apply H0. }
      pose proof (lr_reference_safe_now _ (lr_reference_safe_step _ _ Hsafe Hrs)) as Hok'. simpl in Hok'.
      (* A pending access at a freed location would leave its reference
         thread stuck. *)
      assert (Hframe : lr_frame tp m (free_mem l n' m)).
      { intros j t l0 Hj (c0 & Hpend). unfold lr_mem in *. rewrite lookup_free_mem.
        case_decide as Hin; [ exfalso | done ].
        destruct (lr_pools_match_lookup_r _ _ _ _ _ Hpools Hj) as (ej & Hej & Hthj).
        assert (Hji : j <> i).
        { intros ->. unfold lr_tpool, tpool, lr_running in *.
          assert (Heq : Some t = Some (Running (fill K (Free (Lit (LitInt n)) (Lit (LitLoc l)))) []))
            by (etransitivity; [ symmetry; exact Hj | exact Hget ]).
          injection Heq as ->. destruct Hpend; congruence. }
        assert (Hns : lr_reference_not_stuck ej (free_mem l n' sigma)).
        { apply Hok'. apply (list_elem_of_lookup_2 _ j). unfold thread_pool in *.
          rewrite list_lookup_insert_ne; [ exact Hej | done ]. }
        destruct Hpend as [-> | ->]; inversion Hthj; subst; unfold lr_running in *; simplify_eq;
          try lr_events_absurd.
        - destruct (lr_not_stuck_read_na2 _ _ _ Hns) as (k & v0 & Hs).
          unfold state in *. rewrite lookup_free_mem in Hs. case_decide; [ discriminate | done ].
        - destruct (lr_not_stuck_write_na2 _ _ _ _ _ ltac:(eassumption) Hns) as (v0 & Hs).
          unfold state in *. rewrite lookup_free_mem in Hs. case_decide; [ discriminate | done ]. }
      eapply lr_back_pack.
      * by apply lr_steps_one.
      * eapply lr_back_pools_update; [ exact Hpools | exact Hframe | done | ].
        apply LRBackFree; [ subst n'; lia | by eapply na2_free_fill ].
      * by apply lr_back_heaps_free.
      * apply lr_frees_ok_update with m mu; [ exact Hfrees | | ].
        -- intros j c T l0 _ Hj Hl0. split; [ | done ].
           unfold lr_mem in *. rewrite lookup_free_mem. case_decide as Hin; [ | done ].
           destruct (proj1 Hfrees j c T l0 Hj Hl0) as (Hm0 & _). symmetry. exact Hm0.
        -- intros c T l0 Heq Hl0. unfold lr_running in Heq. simplify_eq.
           apply lr_free_event_elem_of in Hl0 as Hin.
           destruct (Hrange l0 Hin) as [w Hw].
           split; [ unfold lr_mem in *; rewrite lookup_free_mem; by case_decide | split ].
           ++ destruct (lr_back_heaps_lookup_m _ _ _ _ _ Hheaps Hw) as (st & v0 & _ & Hmu & _). by eexists.
           ++ intros j c'' T'' _ Hj Hl0'. destruct (proj1 Hfrees j c'' T'' l0 Hj Hl0') as (Hm0 & _).
              assert (Some w = None) by (etransitivity; [ symmetry; exact Hw | exact Hm0 ]). discriminate.
    + (* Case *)
      injection Hreserve as <-. simpl in Hna2. na2_split.
      assert (Hna2' : na2_free e2 = true).
      { eapply forallb_forall; [ done | ]. apply list_elem_of_In. by eapply list_elem_of_lookup_2. }
      eapply lr_back_pack.
      * apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
        apply EctxStep. by eapply CaseS.
      * eapply lr_back_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
        constructor. by eapply na2_free_fill.
      * exact Hheaps.
      * eapply lr_frees_ok_nofree; [ exact Hfrees | intros ? [] % elem_of_nil | done ].
  - (* Core_Commit *)
    inversion Hthread as [ | K l v Hna2 Hmv | K l e0 v Hv Hna2 Hmv | e0 l n Hn Hna2 | e0 l n Hn Hna2 ];
      subst; unfold lr_running in *; [ done | | | | ].
    + (* Read: the reference does its second half, reading the value the
         machine already read. *)
      apply lr_fin_read_inv in Hcommit as Hmu. destruct Hmu as (n & Hmu).
      destruct (lr_back_heaps_lookup_m _ _ _ _ _ Hheaps Hmv) as ([ | n' ] & v0 & Hs & Hmu' & Hv & Hvna2);
        unfold lr_rw_map, rw_map in *; rewrite Hmu in Hmu'; simpl in Hmu'; simplify_eq.
      destruct Hv as [ [=] | -> ].
      rewrite (lr_fin_read mu l n Hmu) in Hcommit. injection Hcommit as <-.
      eapply lr_back_pack.
      * apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
        apply EctxStep. by apply ReadNa2S.
      * eapply lr_back_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
        by constructor.
      * unfold lr_mem in *. rewrite <- (insert_id m' l v) by done.
        by apply (lr_back_heaps_insert _ _ _ l (RSt n) v v); [ | right | ].
      * eapply lr_frees_ok_nofree; [ exact Hfrees | intros ? [] % elem_of_nil | ].
        intros l' Hl' _. split; [ done | ].
        unfold lr_mem, lr_rw_map, rw_map in *. rewrite lookup_insert_ne; [ done | congruence ].
    + (* Write: the reference does its second half. *)
      apply lr_fin_write_inv in Hcommit as Hmu.
      destruct (lr_back_heaps_lookup_m _ _ _ _ _ Hheaps Hmv) as ([ | n' ] & v0 & Hs & Hmu' & _ & Hvna2);
        unfold lr_rw_map, rw_map in *; rewrite Hmu in Hmu'; simpl in Hmu'; simplify_eq.
      rewrite (lr_fin_write mu l Hmu) in Hcommit. injection Hcommit as <-.
      eapply lr_back_pack.
      * apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
        apply EctxStep. by eapply WriteNa2S.
      * eapply lr_back_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
        by constructor.
      * unfold lr_mem in *. rewrite <- (insert_id m' l v) by done.
        by apply (lr_back_heaps_insert _ _ _ l (RSt 0) v v); [ | right | ].
      * eapply lr_frees_ok_nofree; [ exact Hfrees | intros ? [] % elem_of_nil | ].
        intros l' Hl' _. split; [ done | ].
        unfold lr_mem, lr_rw_map, rw_map in *. rewrite lookup_insert_ne; [ done | congruence ].
    + (* Alloc: nothing left to do on either side. *)
      rewrite lr_fin_alloc_events in Hcommit. injection Hcommit as <-.
      exists (threads, sigma). split; [ split; [ | split ] | apply LRStepsRefl ].
      * simpl. eapply lr_pools_match_insert_r; [ exact Hpools | exact He | by constructor ].
      * exact Hheaps.
      * eapply lr_frees_ok_nofree; [ exact Hfrees | intros ? [] % elem_of_nil | done ].
    + (* Free: the reservations of the (already freed) range go away. *)
      assert (Hres : forall z, (0 <= z < Z.of_nat n)%Z -> is_Some (mu !! (l +ₗ z)%L)).
      { intros z Hz. apply (proj1 Hfrees i c (lr_free_events l n) _ Hget). by apply lr_free_event_shift. }
      rewrite (lr_fin_free_events mu l n Hres) in Hcommit. injection Hcommit as <-.
      exists (threads, sigma). split; [ split; [ | split ] | apply LRStepsRefl ].
      * simpl. eapply lr_pools_match_insert_r; [ exact Hpools | exact He | by constructor ].
      * simpl. eapply lr_back_heaps_mu; [ exact Hheaps | ]. intros l' [w Hw].
        unfold lr_rw_map, rw_map in *. rewrite lookup_free_mem. case_decide as Hin; [ | done ].
        exfalso. apply lr_free_event_elem_of in Hin.
        destruct (proj1 Hfrees i c _ l' Hget Hin) as (Hm0 & _).
        assert (Some w = None) by (etransitivity; [ symmetry; exact Hw | exact Hm0 ]). discriminate.
      * simpl. apply lr_frees_ok_update with m' mu; [ exact Hfrees | | ].
        -- intros j c' T l' Hji Hj Hl'. split; [ done | ].
           unfold lr_rw_map, rw_map in *. rewrite lookup_free_mem. case_decide as Hin; [ | done ].
           exfalso. apply lr_free_event_elem_of in Hin.
           exact (proj2 Hfrees i j c c' _ T l' (not_eq_sym Hji) Hget Hj Hin Hl').
        -- intros c' T l' Heq Hl'. unfold lr_running in Heq. simplify_eq. by apply elem_of_nil in Hl'.
  - (* SC_Read *)
    apply lr_back_thread_idle in Hthread as (<- & Hna2c).
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst.
    simpl in Hload, Hmu. apply Forall_inv in Hmu.
    destruct (lr_back_heaps_lookup_m _ _ _ _ _ Hheaps Hload) as ([ | n' ] & v0 & Hs & Hmu' & Hv & Hvna2);
      unfold lr_rw_map, rw_map in *; rewrite Hmu' in Hmu; simpl in Hmu; [ done | ].
    destruct Hv as [ [=] | -> ].
    eapply lr_back_pack.
    + apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
      apply EctxStep. by eapply ReadScS.
    + eapply lr_back_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
      constructor. by eapply na2_free_fill.
    + exact Hheaps.
    + eapply lr_frees_ok_nofree; [ exact Hfrees | intros ? [] % elem_of_nil | done ].
  - (* SC_Write *)
    apply lr_back_thread_idle in Hthread as (<- & Hna2c).
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe as [ | l' e1 v1 Hv1 | ]; subst.
    simpl in Hstore, Hmu. apply Forall_inv in Hmu.
    destruct (m !! l) as [v' | ] eqn:Hm; simplify_eq.
    destruct (lr_back_heaps_lookup_m _ _ _ _ _ Hheaps Hm) as ([ | n' ] & v0 & Hs & Hmu' & _ & _);
      unfold lr_rw_map, rw_map in *; rewrite Hmu' in Hmu; simpl in Hmu; simplify_eq.
    assert (Hna2 : na2_free (Write ScOrd (Lit (LitLoc l)) e1) = true) by eauto using na2_free_fill_inv.
    simpl in Hna2. rewrite <- (of_to_val e1 v Hv1) in Hna2.
    eapply lr_back_pack.
    + apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
      apply EctxStep. by eapply WriteScS.
    + eapply lr_back_pools_update;
        [ exact Hpools | eapply lr_back_frame_write; [ exact Hpools | exact Hheaps | exact Hok | exact Hmu' ] | done | ].
      constructor. by eapply na2_free_fill.
    + rewrite <- (insert_id mu' l (Rst 0)) by exact Hmu'.
      by apply (lr_back_heaps_insert _ _ _ l (RSt 0) v v); [ | right | ].
    + eapply lr_frees_ok_nofree; [ exact Hfrees | intros ? [] % elem_of_nil | ].
      intros l'' Hl'' _. split; [ | done ]. unfold lr_mem in *. rewrite lookup_insert_ne; [ done | congruence ].
  - (* SC_Cas_Suc *)
    apply lr_back_thread_idle in Hthread as (<- & Hna2c).
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst.
    simpl in Hload, Hstore, Hmu. apply Forall_inv in Hmu.
    change (lr_val_eq m v_cur (LitV lit1)) in Heq.
    destruct v_cur as [litl | ]; [ | contradiction ]. simpl in Heq.
    destruct (lr_back_heaps_lookup_m _ _ _ _ _ Hheaps Hload) as ([ | n' ] & v0 & Hs & Hmu' & Hv & _);
      unfold lr_rw_map, rw_map in *; rewrite Hmu' in Hmu; simpl in Hmu; simplify_eq.
    destruct Hv as [ [=] | -> ].
    rewrite Hload in Hstore. injection Hstore as <-.
    eapply lr_back_pack.
    + apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
      apply EctxStep. eapply CasSucS; eauto. by eapply lit_eq_dom.
    + eapply lr_back_pools_update;
        [ exact Hpools | eapply lr_back_frame_write; [ exact Hpools | exact Hheaps | exact Hok | exact Hmu' ] | done | ].
      constructor. by eapply na2_free_fill.
    + rewrite <- (insert_id mu' l (Rst 0)) by exact Hmu'.
      by apply (lr_back_heaps_insert _ _ _ l (RSt 0) (LitV lit2) (LitV lit2)); [ | right | ].
    + eapply lr_frees_ok_nofree; [ exact Hfrees | intros ? [] % elem_of_nil | ].
      intros l' Hl' _. split; [ | done ]. unfold lr_mem in *. rewrite lookup_insert_ne; [ done | congruence ].
  - (* SC_Cas_Fail *)
    apply lr_back_thread_idle in Hthread as (<- & Hna2c).
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst.
    simpl in Hload, Hmu. apply Forall_inv in Hmu.
    change (lr_val_neq m' v_cur (LitV lit1)) in Hneq.
    destruct v_cur as [litl | ]; [ | contradiction ]. simpl in Hneq.
    destruct (lr_back_heaps_lookup_m _ _ _ _ _ Hheaps Hload) as ([ | n' ] & v0 & Hs & Hmu' & Hv & _);
      unfold lr_rw_map, rw_map in *; rewrite Hmu' in Hmu; simpl in Hmu; [ done | ].
    destruct Hv as [ [=] | -> ].
    eapply lr_back_pack.
    + apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
      apply EctxStep. eapply CasFailS; eauto. by eapply lit_neq_dom.
    + eapply lr_back_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
      constructor. by eapply na2_free_fill.
    + exact Hheaps.
    + eapply lr_frees_ok_nofree; [ exact Hfrees | intros ? [] % elem_of_nil | done ].
  - (* SC_Cas_Stuck: under reference safety this cannot happen. *)
    exfalso. apply lr_back_thread_idle in Hthread as (<- & Hna2c).
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe as [ | | l' e1 lit1' e2 lit2' He1 He2 ]; subst.
    simpl in Hload. change (lr_val_eq m' v_cur (LitV lit1')) in Heq.
    destruct v_cur as [litl | ]; [ | contradiction ]. simpl in Heq.
    destruct (lr_back_heaps_lookup_m _ _ _ _ _ Hheaps Hload) as ([ | [ | n' ] ] & v0 & Hs & Hmu' & Hv & _).
    + (* [WSt]: the reference [CAS] has no rule. *)
      apply (lr_not_stuck_cas_wst K0 l e1 e2 lit1' lit2' sigma v0 He1 He2 Hs).
      apply Hok. by eapply list_elem_of_lookup_2.
    + (* [RSt 0]: the machine [CAS] would have succeeded. *)
      apply Ho. simpl. apply Forall_singleton. exact Hmu'.
    + (* [RSt (S _)]: the reference crashes, which is unsafe. *)
      destruct Hv as [ [=] | -> ].
      assert (Hrs : step (threads, sigma) (<[i := fill K0 stuck_term]> threads, sigma)).
      { eapply lr_reference_step_at; [ exact He | ]. apply EctxStep.
        eapply CasStuckS; eauto; [ lia | by eapply lit_eq_dom ]. }
      eapply (lr_not_stuck_crashed K0 sigma).
      apply (lr_reference_safe_now _ (lr_reference_safe_step _ _ Hsafe Hrs)). simpl.
      eapply list_elem_of_lookup_2. unfold thread_pool. apply list_lookup_insert_eq.
      by eapply lookup_lt_Some.
  - (* Spawn: the reference forks, appending at the machine's new index. *)
    apply lr_back_thread_idle in Hthread as (<- & Hna2c).
    inversion Hspawn as [K e0 Hc0 Hc1 Hc2]; subst.
    assert (Hna2 : na2_free (Fork c_new) = true) by eauto using na2_free_fill_inv. simpl in Hna2.
    pose proof (lr_pools_match_least_free _ _ _ _ Hpools Hfree Hleast) as ->.
    eapply lr_back_pack.
    + apply lr_steps_one. eapply lr_reference_step_at_spawn; [ exact He | ]. apply EctxStep, ForkS.
    + rewrite <- (length_insert threads i (fill K (Lit LitPoison))).
      apply lr_pools_match_snoc; [ | by constructor ].
      eapply lr_back_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
      constructor. by eapply na2_free_fill.
    + exact Hheaps.
    + eapply lr_frees_ok_nofree; [ | intros ? [] % elem_of_nil | done ].
      eapply lr_frees_ok_nofree; [ exact Hfrees | intros ? [] % elem_of_nil | done ].
Qed.

(** * Progress reflection at a single configuration *)

Lemma lr_back_not_stuck rc mc :
  lr_back_configuration_match rc mc -> lr_reference_safe rc ->
  forall i t, lr_machine_threads mc !! i = Some t ->
  am_not_stuck t (lr_machine_mem mc) (lr_machine_rw mc).
Proof.
  destruct rc as (threads, sigma), mc as [tp m mu].
  intros (Hpools & Hheaps & Hfrees) Hsafe i t Hi. simpl in *.
  pose proof (lr_reference_safe_now _ Hsafe) as Hok. simpl in Hok.
  assert (Hdom : forall l, sigma !! l = None -> m !! l = None)
    by (intros l; apply (lr_back_heaps_none _ _ _ l Hheaps)).
  destruct (lr_pools_match_lookup_r _ _ _ _ _ Hpools Hi) as (e & He & Hthread).
  pose proof (Hok e (list_elem_of_lookup_2 _ _ _ He)) as Hns.
  inversion Hthread; subst.
  - (* Not pending: each reference step has a machine counterpart. *)
    destruct Hns as [Hfinal | (e' & sigma' & spawned & Hstep)].
    { left. by eexists. }
    right. inversion Hstep as [K e1 ? e2 ? ? Hhead]; subst.
    assert (Hna2 : na2_free e1 = true) by eauto using na2_free_fill_inv.
    inversion Hhead; subst.
    + eapply lr_red_try with (T := []); [ | done ]. apply LREctxStep, LRBinOpS. by eapply bin_op_eval_dom.
    + eapply lr_red_try with (T := []); [ | done ]. apply LREctxStep. by eapply LRBetaS.
    + destruct (lr_back_heaps_lookup _ _ _ _ _ _ Hheaps H0) as (v' & Hm & Hmu & [ [=] | <- ] & _).
      eapply lr_red_sc_read; [ by apply LREctxExternal, LRReadScE | | exact Hm ].
      unfold lr_rw_map, rw_map in *. by rewrite Hmu.
    + destruct (lr_back_heaps_lookup _ _ _ _ _ _ Hheaps H0) as (v' & Hm & Hmu & [ [=] | <- ] & _).
      eapply lr_red_try; [ apply LREctxStep; by apply LRReadNaS | by apply lr_rsv_read ].
    + by rewrite na2_free_read_na2 in H.
    + destruct (lr_back_heaps_lookup _ _ _ _ _ _ Hheaps H1) as (v'' & Hm & Hmu & _).
      eapply lr_red_sc_write; [ by apply LREctxExternal, LRWriteScE | exact Hmu | exact Hm ].
    + destruct (lr_back_heaps_lookup _ _ _ _ _ _ Hheaps H1) as (v'' & Hm & Hmu & _).
      eapply lr_red_try; [ apply LREctxStep; by eapply LRWriteNaS | by apply lr_rsv_write ].
    + by rewrite na2_free_write_na2 in H.
    + destruct (lr_back_heaps_lookup _ _ _ _ _ _ Hheaps H2) as (v' & Hm & Hmu & [ [=] | <- ] & _).
      eapply lr_red_cas_fail; [ by apply LREctxExternal, LRCasE | | exact Hm | by eapply lit_neq_dom ].
      unfold lr_rw_map, rw_map in *. by rewrite Hmu.
    + destruct (lr_back_heaps_lookup _ _ _ _ _ _ Hheaps H2) as (v' & Hm & Hmu & [ [=] | <- ] & _).
      eapply lr_red_cas_suc; [ by apply LREctxExternal, LRCasE | exact Hmu | exact Hm | by eapply lit_eq_dom ].
    + (* The reference crashes here; the machine can at least step (to a crash). *)
      destruct (lr_back_heaps_lookup _ _ _ _ _ _ Hheaps H2) as (v' & Hm & Hmu & [ [=] | <- ] & _).
      eapply lr_red_cas_stuck; [ by apply LREctxExternal, LRCasE | | exact Hm | by eapply lit_eq_dom ].
      unfold lr_rw_map, rw_map in *. rewrite Hmu. intros [=]. lia.
    + (* The reference's fresh block may still be reserved on the machine
         by a pending deallocation, so pick one fresh for both. *)
      destruct (lr_fresh_block m mu) as (l' & Hfresh).
      eapply lr_red_try; [ | apply lr_rsv_alloc_events, Hfresh ].
      apply LREctxStep, LRAllocS; [ done | apply Hfresh ].
    + eapply lr_red_try; [ | apply lr_rsv_free_events ].
      apply LREctxStep, LRFreeS; [ done | ].
      intros z. rewrite <- (lr_back_heaps_is_Some _ _ _ _ Hheaps). apply H1.
    + eapply lr_red_try with (T := []); [ | done ]. apply LREctxStep. by eapply LRCaseS.
    + apply lr_red_spawn.
  - (* Pending read: the reference lock is [RSt (S _)], so the commit succeeds. *)
    apply am_pending_not_stuck; [ discriminate | ].
    destruct (lr_not_stuck_read_na2 _ _ _ Hns) as (n & v0 & Hs).
    destruct (lr_back_heaps_lookup _ _ _ _ _ _ Hheaps Hs) as (w & _ & Hmu & _).
    eexists. by apply lr_fin_read.
  - (* Pending write: the reference lock is [WSt]. *)
    apply am_pending_not_stuck; [ discriminate | ].
    destruct (lr_not_stuck_write_na2 _ _ _ _ _ H Hns) as (v' & Hs).
    destruct (lr_back_heaps_lookup _ _ _ _ _ _ Hheaps Hs) as (w & _ & Hmu & _).
    eexists. by apply lr_fin_write.
  - apply am_pending_not_stuck; [ by apply lr_alloc_events_nonempty | ].
    eexists. apply lr_fin_alloc_events.
  - (* Pending free: its range is still reserved. *)
    apply am_pending_not_stuck; [ by apply lr_free_events_nonempty | ].
    eexists. apply lr_fin_free_events. intros z Hz.
    apply (proj1 Hfrees i e (lr_free_events l n) _ Hi). by apply lr_free_event_shift.
Qed.

(** * The theorem *)

Lemma lr_am_steps_inv mc q :
  rtc am_step (lr_am_configuration mc) q ->
  exists mc', q = lr_am_configuration mc' /\ lr_steps lr_machine_step mc mc'.
Proof.
  intros Hsteps. remember (lr_am_configuration mc) as q0 eqn:Hq0. revert mc Hq0.
  induction Hsteps as [ q | q1 q2 q3 Hstep _ IH ]; intros mc ->.
  - exists mc. split; [ done | constructor ].
  - destruct q2 as [[tp m] mu].
    destruct (IH {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |} eq_refl)
      as (mc' & -> & Hsteps').
    exists mc'. split; [ done | ]. eapply LRStepsStep; [ | exact Hsteps' ].
    destruct mc. exact Hstep.
Qed.

Lemma lr_back_steps rc mc mc' :
  lr_back_configuration_match rc mc ->
  lr_reference_safe rc ->
  lr_steps lr_machine_step mc mc' ->
  exists rc', lr_back_configuration_match rc' mc' /\ lr_reference_safe rc'.
Proof.
  intros Hmatch Hsafe Hsteps. revert rc Hmatch Hsafe.
  induction Hsteps as [ x | x y z Hxy Hyz IH ]; intros rc Hmatch Hsafe; [ eauto | ].
  destruct (lr_back_step _ _ _ Hmatch Hsafe Hxy) as (rc1 & Hmatch1 & Hsteps1).
  exact (IH rc1 Hmatch1 (lr_reference_safe_steps _ _ Hsafe Hsteps1)).
Qed.

Theorem lr_reference_safe_am_safe rc0 mc0 :
  lr_back_configuration_match rc0 mc0 ->
  lr_reference_safe rc0 ->
  lr_am_safe mc0.
Proof.
  intros Hmatch Hsafe tp m mu Hsteps i t Hi.
  destruct (lr_am_steps_inv _ _ Hsteps) as (mc & Hmc & Hsteps').
  destruct mc as [tp' m' mu']. unfold lr_am_configuration in Hmc. simpl in Hmc. simplify_eq.
  destruct (lr_back_steps _ _ _ Hmatch Hsafe Hsteps') as (rc & Hmatch' & Hsafe').
  exact (lr_back_not_stuck _ _ Hmatch' Hsafe' i t Hi).
Qed.

Corollary lr_reference_safe_am_safe_stable rc0 mc0 :
  lr_stable_configuration_match rc0 mc0 ->
  lr_reference_safe rc0 ->
  lr_am_safe mc0.
Proof. intros Hmatch. apply lr_reference_safe_am_safe, lr_stable_back, Hmatch. Qed.

(** Together with [safety_reflection.v]: from stably matched initial
    configurations, the machine is safe exactly when the reference is. *)
Theorem lr_safety_equivalence rc0 mc0 :
  lr_stable_configuration_match rc0 mc0 ->
  lr_am_safe mc0 <-> lr_reference_safe rc0.
Proof.
  intros Hmatch. split.
  - by apply lr_am_safe_reference_safe_stable.
  - by apply lr_reference_safe_am_safe_stable.
Qed.
