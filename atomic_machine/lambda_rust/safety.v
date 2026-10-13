(** Safety of the atomic machine and of the reference lambda-Rust
    semantics.

    The reference predicate is the safety component of RustBelt/Iris
    adequacy (with a trivial result postcondition).  [safety_reflection.v]
    and [machine_safety.v] prove that the two agree from stably matched
    initial configurations. *)

From Stdlib Require Import List Lia.
From stdpp Require Import gmap list.

Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.machine.

Import ListNotations.
Open Scope lambda_rust_loc_scope.
Set Default Proof Using "Type".

Definition lr_am_configuration (mc : lr_machine_configuration)
    : @am_configuration loc val _ _ lr_mem lr_layout lr_memory lr_language :=
  (lr_machine_threads mc, lr_machine_mem mc, lr_machine_rw mc).

Definition lr_am_safe (mc : lr_machine_configuration) : Prop :=
  am_safe (lr_am_configuration mc).

Definition lr_reference_not_stuck (e : expr) (sigma : state) : Prop :=
  lr_final e \/ reducible e sigma.

(** This uses the full reference [step], including thread creation. *)
Definition lr_reference_safe (rc : configuration) : Prop :=
  forall threads sigma,
    rtc step rc (threads, sigma) ->
    forall e, e ∈ threads -> lr_reference_not_stuck e sigma.

Lemma lr_am_steps mc mc' :
  rtc lr_machine_step mc mc' ->
  rtc am_step (lr_am_configuration mc) (lr_am_configuration mc').
Proof.
  induction 1; [ constructor | ].
  eapply rtc_l with (y := lr_am_configuration y);
    [ destruct x, y; exact H | exact IHrtc ].
Qed.

Lemma lr_am_steps_inv mc q :
  rtc am_step (lr_am_configuration mc) q ->
  exists mc', q = lr_am_configuration mc' /\ rtc lr_machine_step mc mc'.
Proof.
  intros Hsteps. remember (lr_am_configuration mc) as q0 eqn:Hq0. revert mc Hq0.
  induction Hsteps as [ q | q1 q2 q3 Hstep _ IH ]; intros mc ->.
  - exists mc. split; [ done | constructor ].
  - destruct q2 as [[tp m] mu].
    destruct (IH {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |} eq_refl)
      as (mc' & -> & Hsteps').
    exists mc'. split; [ done | ]. eapply rtc_l; [ | exact Hsteps' ].
    destruct mc. exact Hstep.
Qed.

Lemma lr_am_safe_reachable mc mc' :
  lr_am_safe mc -> rtc lr_machine_step mc mc' -> lr_am_safe mc'.
Proof. intros Hsafe Hsteps. eapply am_safe_reachable; eauto using lr_am_steps. Qed.

(** * The simulation relation

    Both safety proofs use the same relation, in which the two sides agree
    on which accesses are in flight:
    - a reference thread that has done the first half ([Na1Ord]) of a
      non-atomic access is matched by a machine thread that has done
      [Core_Try] and holds the corresponding pending event;
    - the reader/writer map mirrors the reference lock states at allocated
      locations;
    - the machine performs the memory effect at [Core_Try] and the
      reference at the second half, so the two memories differ exactly at
      locations the reference holds at [WSt].

    When the machine drives ([machine_safety.v]), two machine-only states
    have no reference counterpart and are matched by the reference thread
    that has already finished the step: a pending allocation and a pending
    deallocation.  A pending deallocation has already freed its range but
    keeps its reservations, so the reader/writer map is unconstrained at
    unallocated locations.  When the reference drives
    ([safety_reflection.v]), the machine performs allocation and
    deallocation in one go, so neither state arises and the reader/writer
    map is empty at unallocated locations. *)

Variant lr_driver := LRRefDrives | LRMachDrives.

Definition lr_lock (st : lock_state) : rw_state :=
  match st with
  | RSt n => Rst n
  | WSt => Wst
  end.

Definition lr_heaps_match (d : lr_driver)
    (sigma : state) (m : lr_mem) (mu : lr_rw_map) : Prop :=
  forall l,
    match m !! l with
    | Some v =>
        (exists st v0, sigma !! l = Some (st, v0) /\
           mu !! l = Some (lr_lock st) /\ (st = WSt \/ v0 = v)) /\
        na2_free (of_val v) = true
    | None =>
        sigma !! l = None /\
        match d with LRRefDrives => mu !! l = None | LRMachDrives => True end
    end.

(** A pending access holds the value it read (or is writing) in the
    machine memory; this is the only way the thread relation depends on
    the machine state. *)
Inductive lr_thread_match (m : lr_mem) : lr_driver -> expr -> lr_tstate -> Prop :=
| LRSame d e :
    na2_free e = true ->
    lr_thread_match m d e (lr_running e [])
| LRRead d K l v :
    na2_free (fill K (of_val v)) = true ->
    m !! l = Some v ->
    lr_thread_match m d
      (fill K (Read Na2Ord (Lit (LitLoc l))))
      (lr_running (fill K (of_val v)) [lr_read_event l])
| LRWrite d K l e v :
    to_val e = Some v ->
    na2_free (fill K (Lit LitPoison)) = true ->
    m !! l = Some v ->
    lr_thread_match m d
      (fill K (Write Na2Ord (Lit (LitLoc l)) e))
      (lr_running (fill K (Lit LitPoison)) [lr_write_event l])
| LRAlloc e l n :
    (0 < n)%nat ->
    na2_free e = true ->
    lr_thread_match m LRMachDrives e (lr_running e (lr_alloc_events l n))
| LRFree e l n :
    (0 < n)%nat ->
    na2_free e = true ->
    lr_thread_match m LRMachDrives e (lr_running e (lr_free_events l n)).

Ltac lr_heaps_unfold := unfold lr_heaps_match in *; lr_unfold.

(** * Heaps *)

Lemma lr_heaps_lookup d sigma m mu l st v0 :
  lr_heaps_match d sigma m mu -> sigma !! l = Some (st, v0) ->
  exists v, m !! l = Some v /\ mu !! l = Some (lr_lock st) /\
    (st = WSt \/ v0 = v) /\ na2_free (of_val v) = true.
Proof.
  intros Hheaps Hs. specialize (Hheaps l). lr_heaps_unfold.
  destruct (m !! l) as [v | ]; [ | naive_solver ].
  destruct Hheaps as ((st' & v0' & Hs' & Hmu & Hv) & Hna2).
  rewrite Hs in Hs'. simplify_eq. eauto.
Qed.

Lemma lr_heaps_lookup_m d sigma m mu l v :
  lr_heaps_match d sigma m mu -> m !! l = Some v ->
  exists st v0, sigma !! l = Some (st, v0) /\ mu !! l = Some (lr_lock st) /\
    (st = WSt \/ v0 = v) /\ na2_free (of_val v) = true.
Proof.
  intros Hheaps Hm. specialize (Hheaps l). lr_heaps_unfold. rewrite Hm in Hheaps. naive_solver.
Qed.

Lemma lr_heaps_none d sigma m mu l :
  lr_heaps_match d sigma m mu -> (sigma !! l = None <-> m !! l = None).
Proof.
  intros Hheaps. specialize (Hheaps l). lr_heaps_unfold.
  destruct (m !! l); [ | naive_solver ].
  destruct Hheaps as ((st & v0 & Hs & _) & _). rewrite Hs. naive_solver.
Qed.

Lemma lr_heaps_none_mu sigma m mu l :
  lr_heaps_match LRRefDrives sigma m mu -> m !! l = None -> mu !! l = None.
Proof. intros Hheaps Hm. specialize (Hheaps l). lr_heaps_unfold. rewrite Hm in Hheaps. naive_solver. Qed.

Lemma lr_heaps_is_Some d sigma m mu l :
  lr_heaps_match d sigma m mu -> is_Some (sigma !! l) <-> is_Some (m !! l).
Proof.
  intros Hheaps. pose proof (lr_heaps_none _ _ _ _ l Hheaps) as Hiff.
  rewrite <- !not_eq_None_Some. naive_solver.
Qed.

Lemma lr_heaps_insert d sigma m mu l st v0 v :
  lr_heaps_match d sigma m mu ->
  (st = WSt \/ v0 = v) -> na2_free (of_val v) = true ->
  lr_heaps_match d (<[l := (st, v0)]> sigma) (<[l := v]> m) (<[l := lr_lock st]> mu).
Proof.
  intros Hheaps Hv Hna2 l'. specialize (Hheaps l'). lr_heaps_unfold.
  destruct (decide (l = l')) as [<- | ]; [ rewrite !lookup_insert_eq | by rewrite !lookup_insert_ne ].
  split; [ | done ]. eauto.
Qed.

Lemma lr_heaps_alloc d sigma m mu l n :
  lr_heaps_match d sigma m mu ->
  lr_heaps_match d
    (init_mem (RSt 0, LitV LitPoison) l n sigma)
    (init_mem (LitV LitPoison) l n m)
    (init_mem (Rst 0) l n mu).
Proof.
  intros Hheaps l'. specialize (Hheaps l'). lr_heaps_unfold. rewrite !lookup_init_mem.
  case_decide; [ | done ]. split; [ | done ]. exists (RSt 0), (LitV LitPoison). auto.
Qed.

Lemma lr_heaps_free d sigma m mu l n :
  lr_heaps_match d sigma m mu ->
  lr_heaps_match d (free_mem l n sigma) (free_mem l n m) (free_mem l n mu).
Proof.
  intros Hheaps l'. specialize (Hheaps l'). lr_heaps_unfold. rewrite !lookup_free_mem.
  case_decide; [ by destruct d | done ].
Qed.

(** When the machine drives, deallocation acts on the memories only; the
    reservations stay until the deallocation commits. *)
Lemma lr_heaps_free_mem sigma m mu l n :
  lr_heaps_match LRMachDrives sigma m mu ->
  lr_heaps_match LRMachDrives (free_mem l n sigma) (free_mem l n m) mu.
Proof.
  intros Hheaps l'. specialize (Hheaps l'). lr_heaps_unfold. rewrite !lookup_free_mem.
  by case_decide.
Qed.

(** When the machine drives, the reader/writer map may change freely at
    unallocated locations. *)
Lemma lr_heaps_mu sigma m mu mu' :
  lr_heaps_match LRMachDrives sigma m mu ->
  (forall l, is_Some (m !! l) -> mu' !! l = mu !! l) ->
  lr_heaps_match LRMachDrives sigma m mu'.
Proof.
  intros Hheaps Hmu l. specialize (Hheaps l). lr_heaps_unfold.
  destruct (m !! l) eqn:Hm; [ | done ]. rewrite Hmu; [ done | by eexists ].
Qed.

(** * Pending accesses *)

Definition lr_pending (t : lr_tstate) (l : loc) : Prop :=
  exists c, t = lr_running c [lr_read_event l] \/ t = lr_running c [lr_write_event l].

Ltac lr_events_absurd :=
  match goal with
  | H : lr_alloc_events _ ?n = _ |- _ =>
      destruct n; [ lia | unfold lr_alloc_events in H; simpl in H;
                          first [ discriminate H | injection H as H; discriminate H ] ]
  | H : lr_free_events _ ?n = _ |- _ =>
      destruct n; [ lia | unfold lr_free_events in H; simpl in H;
                          first [ discriminate H | injection H as H; discriminate H ] ]
  end.

Lemma lr_thread_pending_some m d e t l :
  lr_thread_match m d e t -> lr_pending t l -> is_Some (m !! l).
Proof.
  intros Hthread (c & [Ht | Ht]); subst;
    inversion Hthread; subst; unfold lr_running in *; simplify_eq;
    first [ by eexists | lr_events_absurd ].
Qed.

(** A pending thread in a safe configuration can commit, so its location
    is locked. *)
Lemma lr_safe_pending_locked mc j t l :
  lr_am_safe mc -> lr_machine_threads mc !! j = Some t -> lr_pending t l ->
  exists st, lr_machine_rw mc !! l = Some st /\ st <> Rst 0.
Proof.
  intros Hsafe Hj (c & Ht).
  pose proof (Hsafe _ _ _ (rtc_refl _ _) j t Hj) as Hns.
  destruct Ht as [-> | ->].
  all: apply am_pending_not_stuck in Hns as (mu' & Hfin); [ | discriminate ].
  all: revert Hfin; destruct mc as [tp m mu]; simpl.
  all: unfold lr_rw_map, rw_map in *; unfold fin; simpl.
  all: unfold fin_Read, fin_Write; destruct (_ !! l) as [[[ | n] | ] | ] eqn:Hl; simpl;
    intros Hf; try discriminate Hf.
  all: eexists; split; [ reflexivity | discriminate ].
Qed.

(** * Frames *)

(** Memory [m'] agrees with [m] wherever some thread of [tp] is pending. *)
Definition lr_frame (tp : lr_tpool) (m m' : lr_mem) : Prop :=
  forall j t l, tp !! j = Some t -> lr_pending t l -> m' !! l = m !! l.

Lemma lr_frame_refl tp m : lr_frame tp m m.
Proof. by intros ????. Qed.

Lemma lr_thread_frame m m' d e t :
  lr_thread_match m d e t ->
  (forall l, lr_pending t l -> m' !! l = m !! l) ->
  lr_thread_match m' d e t.
Proof.
  intros Hthread Hframe. inversion Hthread; subst.
  - by constructor.
  - apply LRRead; [ done | ]. rewrite Hframe; [ done | ]. eexists. by left.
  - apply LRWrite with v; [ done | done | ]. rewrite Hframe; [ done | ]. eexists. by right.
  - by constructor.
  - by constructor.
Qed.

Lemma lr_pools_update m m' d threads tp i e c :
  lr_pools_match (lr_thread_match m d) threads tp ->
  lr_frame tp m m' ->
  is_Some (threads !! i) ->
  lr_thread_match m' d e c ->
  lr_pools_match (lr_thread_match m' d) (<[i := e]> threads) (<[i := c]> tp).
Proof.
  intros Hpools Hframe Hi Hthread. apply lr_pools_match_insert; [ | done | done ].
  intros j. specialize (Hpools j). unfold lr_tpool, tpool in *.
  destruct (threads !! j), (tp !! j) as [t | ] eqn:Hj; try done.
  eapply lr_thread_frame; [ exact Hpools | ]. intros l. by eapply Hframe.
Qed.

(** Allocating fresh locations: pending threads are at allocated ones. *)
Lemma lr_frame_alloc m d threads tp l n (x : val) :
  lr_pools_match (lr_thread_match m d) threads tp ->
  (forall z, m !! (l +ₗ z)%L = None) ->
  lr_frame tp m (init_mem x l n m).
Proof.
  intros Hpools Hfresh j t l' Hj Hpend.
  destruct (lr_pools_match_lookup_r _ _ _ _ _ Hpools Hj) as (e & _ & Hthread).
  pose proof (lr_thread_pending_some _ _ _ _ _ Hthread Hpend) as Hsome.
  unfold lr_mem in *. rewrite lookup_init_mem. case_decide as Hin; [ | done ].
  destruct (loc_in_range_shift _ _ _ Hin) as (z & _ & ->).
  rewrite Hfresh in Hsome. by destruct Hsome.
Qed.
