(** * Machine safety implies reference safety

    [am_safe] for the lambda-Rust instance of the atomic machine implies
    [lr_reference_safe] (with the full reference [step], including
    thread creation) from any pair of tightly matched initial
    configurations, in particular from stably matched ones.

    The proof is a forward simulation (the reference drives) with a
    relation in which the two sides agree on which accesses are in flight:
    a reference thread that has done the first half ([Na1Ord]) of a
    non-atomic access is matched by a machine thread that has done
    [Core_Try] and holds the corresponding pending event, and the machine's
    reader/writer map mirrors the reference's lock states exactly.  The
    machine performs the memory effect at [Core_Try] and the reference at
    the second half, so the two memories may differ exactly at locations
    the reference holds at [WSt], where no other thread can observe them.

    [am_safe] is used throughout, not only at the end:
    - a reference step with no matching machine step (a racy [CAS]) is
      a step to a machine configuration that is not safe;
    - a pending access never loses its lock (a [Free] of the location or
      an unmatched decrement would leave the pending machine thread unable
      to commit), which keeps the value a pending read has already
      obtained on the machine side equal to the one the reference will
      read. *)

From Stdlib Require Import List Lia.
From stdpp Require Import gmap list.
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.event_semantics.
Require Import VST.atomic_machine.lambda_rust.reference.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Import VST.atomic_machine.lambda_rust.adequacy.

Import ListNotations.
Open Scope lambda_rust_loc_scope.
Set Default Proof Using "Type".

(** * The relation *)

Definition lr_lock (st : lock_state) : rw_state :=
  match st with
  | RSt n => Rst n
  | WSt => Wst
  end.

(** The reader/writer map mirrors the lock states, and the values agree
    except under a write lock, where the machine already holds the value
    being written. *)
Definition lr_tight_heaps_match
    (sigma : state) (m : lr_mem) (mu : lr_rw_map) : Prop :=
  forall l,
    match m !! l with
    | Some v =>
        (exists st v0, sigma !! l = Some (st, v0) /\
           mu !! l = Some (lr_lock st) /\ (st = WSt \/ v0 = v)) /\
        na2_free (of_val v) = true
    | None => sigma !! l = None /\ mu !! l = None
    end.

(** A pending access holds the value it read (or is writing) in the
    machine memory; this is the only way the thread relation depends on
    the machine state. *)
Inductive lr_tight_thread_match (m : lr_mem) : expr -> lr_tstate -> Prop :=
| LRTightSame e :
    na2_free e = true ->
    lr_tight_thread_match m e (lr_running e [])
| LRTightRead K l v :
    na2_free (fill K (of_val v)) = true ->
    m !! l = Some v ->
    lr_tight_thread_match m
      (fill K (Read Na2Ord (Lit (LitLoc l))))
      (lr_running (fill K (of_val v)) [lr_read_event l])
| LRTightWrite K l e v :
    to_val e = Some v ->
    na2_free (fill K (Lit LitPoison)) = true ->
    m !! l = Some v ->
    lr_tight_thread_match m
      (fill K (Write Na2Ord (Lit (LitLoc l)) e))
      (lr_running (fill K (Lit LitPoison)) [lr_write_event l]).

Definition lr_tight_configuration_match
    (rc : configuration) (mc : lr_machine_configuration) : Prop :=
  let '(threads, sigma) := rc in
  lr_pools_match (lr_tight_thread_match (lr_machine_mem mc))
    threads (lr_machine_threads mc) /\
  lr_tight_heaps_match sigma (lr_machine_mem mc) (lr_machine_rw mc).

Lemma lr_stable_tight rc mc :
  lr_stable_configuration_match rc mc -> lr_tight_configuration_match rc mc.
Proof.
  destruct rc as (threads, sigma). intros (Hpools & Hheaps). split.
  - eapply lr_pools_match_impl; [ | exact Hpools ]. intros ? ? []. by constructor.
  - intros l. specialize (Hheaps l). lr_unfold. destruct (_ !! l); [ | done ].
    destruct Hheaps as (Hs & Hmu & Hv). split; [ | done ].
    exists (RSt 0), v. auto.
Qed.

Ltac lr_tight_unfold :=
  unfold lr_tight_configuration_match, lr_tight_heaps_match in *; lr_unfold.

(** * Heaps *)

Lemma lr_tight_heaps_lookup sigma m mu l st v0 :
  lr_tight_heaps_match sigma m mu -> sigma !! l = Some (st, v0) ->
  exists v, m !! l = Some v /\ mu !! l = Some (lr_lock st) /\
    (st = WSt \/ v0 = v) /\ na2_free (of_val v) = true.
Proof.
  intros Hheaps Hs. specialize (Hheaps l). lr_tight_unfold.
  destruct (m !! l) as [v | ]; [ | naive_solver ].
  destruct Hheaps as ((st' & v0' & Hs' & Hmu & Hv) & Hna2).
  rewrite Hs in Hs'. simplify_eq. eauto.
Qed.

Lemma lr_tight_heaps_lookup_m sigma m mu l v :
  lr_tight_heaps_match sigma m mu -> m !! l = Some v ->
  exists st v0, sigma !! l = Some (st, v0) /\ mu !! l = Some (lr_lock st) /\
    (st = WSt \/ v0 = v) /\ na2_free (of_val v) = true.
Proof.
  intros Hheaps Hm. specialize (Hheaps l). lr_tight_unfold. rewrite Hm in Hheaps. naive_solver.
Qed.

Lemma lr_tight_heaps_none sigma m mu l :
  lr_tight_heaps_match sigma m mu ->
  (sigma !! l = None <-> m !! l = None) /\ (m !! l = None -> mu !! l = None).
Proof.
  intros Hheaps. specialize (Hheaps l). lr_tight_unfold.
  destruct (m !! l); [ | naive_solver ].
  destruct Hheaps as ((st & v0 & Hs & _) & _). rewrite Hs. naive_solver.
Qed.

Lemma lr_tight_heaps_is_Some sigma m mu l :
  lr_tight_heaps_match sigma m mu -> is_Some (sigma !! l) <-> is_Some (m !! l).
Proof.
  intros Hheaps. destruct (lr_tight_heaps_none _ _ _ l Hheaps) as (Hiff & _).
  rewrite <- !not_eq_None_Some. naive_solver.
Qed.

Lemma lr_tight_heaps_insert sigma m mu l st v0 v :
  lr_tight_heaps_match sigma m mu ->
  (st = WSt \/ v0 = v) -> na2_free (of_val v) = true ->
  lr_tight_heaps_match (<[l := (st, v0)]> sigma) (<[l := v]> m) (<[l := lr_lock st]> mu).
Proof.
  intros Hheaps Hv Hna2 l'. specialize (Hheaps l'). lr_tight_unfold.
  destruct (decide (l = l')) as [<- | ]; [ rewrite !lookup_insert_eq | by rewrite !lookup_insert_ne ].
  split; [ | done ]. eauto.
Qed.

Lemma lr_tight_heaps_alloc sigma m mu l n :
  lr_tight_heaps_match sigma m mu ->
  lr_tight_heaps_match
    (init_mem (RSt 0, LitV LitPoison) l n sigma)
    (init_mem (LitV LitPoison) l n m)
    (init_mem (Rst 0) l n mu).
Proof.
  intros Hheaps l'. specialize (Hheaps l'). lr_tight_unfold. rewrite !lookup_init_mem.
  case_decide; [ | done ]. split; [ | done ]. exists (RSt 0), (LitV LitPoison). auto.
Qed.

Lemma lr_tight_heaps_free sigma m mu l n :
  lr_tight_heaps_match sigma m mu ->
  lr_tight_heaps_match (free_mem l n sigma) (free_mem l n m) (free_mem l n mu).
Proof.
  intros Hheaps l'. specialize (Hheaps l'). lr_tight_unfold. rewrite !lookup_free_mem.
  by case_decide.
Qed.

(** * Reserving and finishing single accesses *)

Lemma lr_rsv_read (mu : lr_rw_map) l n :
  mu !! l = Some (Rst n) ->
  rsv [lr_read_event l] mu = Some (<[l := Rst (S n)]> mu).
Proof. intros Hl. unfold lr_rw_map, rw_map in *. unfold rsv. simpl. unfold rsv_Read. by setoid_rewrite Hl. Qed.

Lemma lr_fin_read (mu : lr_rw_map) l n :
  mu !! l = Some (Rst (S n)) ->
  fin [lr_read_event l] mu = Some (<[l := Rst n]> mu).
Proof. intros Hl. unfold lr_rw_map, rw_map in *. unfold fin. simpl. unfold fin_Read. by setoid_rewrite Hl. Qed.

Lemma lr_rsv_write (mu : lr_rw_map) l :
  mu !! l = Some (Rst 0) ->
  rsv [lr_write_event l] mu = Some (<[l := Wst]> mu).
Proof. intros Hl. unfold lr_rw_map, rw_map in *. unfold rsv. simpl. unfold rsv_Write. by setoid_rewrite Hl. Qed.

Lemma lr_fin_write (mu : lr_rw_map) l :
  mu !! l = Some Wst ->
  fin [lr_write_event l] mu = Some (<[l := Rst 0]> mu).
Proof. intros Hl. unfold lr_rw_map, rw_map in *. unfold fin. simpl. unfold fin_Write. by setoid_rewrite Hl. Qed.

Lemma lr_rsv_read_inv (mu mu' : lr_rw_map) l :
  rsv [lr_read_event l] mu = Some mu' -> exists n, mu !! l = Some (Rst n).
Proof.
  unfold lr_rw_map, rw_map in *. unfold rsv. simpl. unfold rsv_Read.
  destruct (_ !! l) as [[n | ] | ] eqn:Hl; simpl; intros Hf; try discriminate Hf; eauto.
Qed.

Lemma lr_rsv_write_inv (mu mu' : lr_rw_map) l :
  rsv [lr_write_event l] mu = Some mu' -> mu !! l = Some (Rst 0).
Proof.
  unfold lr_rw_map, rw_map in *. unfold rsv. simpl. unfold rsv_Write.
  destruct (_ !! l) as [[[ | n] | ] | ] eqn:Hl; simpl; intros Hf; try discriminate Hf; reflexivity.
Qed.

(** * Pending accesses *)

Definition lr_pending (t : lr_tstate) (l : loc) : Prop :=
  exists c, t = lr_running c [lr_read_event l] \/ t = lr_running c [lr_write_event l].

Lemma lr_tight_thread_pending_some m e t l :
  lr_tight_thread_match m e t -> lr_pending t l -> is_Some (m !! l).
Proof.
  intros Hthread (c & [Ht | Ht]); subst;
    inversion Hthread; subst; unfold lr_running in *; simplify_eq; by eexists.
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

(** * Thread pools *)

Lemma lr_tight_thread_frame m m' e t :
  lr_tight_thread_match m e t ->
  (forall l, lr_pending t l -> m' !! l = m !! l) ->
  lr_tight_thread_match m' e t.
Proof.
  intros Hthread Hframe. inversion Hthread; subst.
  - by constructor.
  - apply LRTightRead; [ done | ]. rewrite Hframe; [ done | ]. eexists. by left.
  - apply LRTightWrite with v; [ done | done | ]. rewrite Hframe; [ done | ]. eexists. by right.
Qed.

(** Memory [m'] agrees with [m] wherever some thread of [tp] is pending. *)
Definition lr_frame (tp : lr_tpool) (m m' : lr_mem) : Prop :=
  forall j t l, tp !! j = Some t -> lr_pending t l -> m' !! l = m !! l.

Lemma lr_tight_pools_update m m' threads tp i e c :
  lr_pools_match (lr_tight_thread_match m) threads tp ->
  lr_frame tp m m' ->
  is_Some (threads !! i) ->
  lr_tight_thread_match m' e c ->
  lr_pools_match (lr_tight_thread_match m') (<[i := e]> threads) (<[i := c]> tp).
Proof.
  intros Hpools Hframe Hi Hthread. apply lr_pools_match_insert; [ | done | done ].
  intros j. specialize (Hpools j). unfold lr_tpool, tpool in *.
  destruct (threads !! j), (tp !! j) as [t | ] eqn:Hj; try done.
  eapply lr_tight_thread_frame; [ exact Hpools | ]. intros l. by eapply Hframe.
Qed.

Lemma lr_frame_refl tp m : lr_frame tp m m.
Proof. by intros ????. Qed.

(** Writing a location at [Rst 0]: no pending thread is there. *)
Lemma lr_frame_write tp m mu l v :
  lr_am_safe {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |} ->
  mu !! l = Some (Rst 0) ->
  lr_frame tp m (<[l := v]> m).
Proof.
  intros Hsafe Hmu j t l' Hj Hpend.
  destruct (lr_safe_pending_locked _ _ _ _ Hsafe Hj Hpend) as (st & Hst & Hne). simpl in Hst.
  unfold lr_mem. rewrite lookup_insert_ne; [ done | ]. intros <-.
  unfold lr_rw_map, rw_map in *. rewrite Hmu in Hst. congruence.
Qed.

Lemma loc_in_range_shift l n l' : loc_in_range l n l' -> exists z, l' = (l +ₗ z)%L.
Proof.
  destruct l as [b o], l' as [b' o']. unfold loc_in_range, shift_loc. simpl.
  intros (-> & _). exists (o' - o)%Z. f_equal. lia.
Qed.

(** Allocating fresh locations: pending threads are at allocated ones. *)
Lemma lr_frame_alloc threads tp m l n (x : val) :
  lr_pools_match (lr_tight_thread_match m) threads tp ->
  (forall z, m !! (l +ₗ z)%L = None) ->
  lr_frame tp m (init_mem x l n m).
Proof.
  intros Hpools Hfresh j t l' Hj Hpend.
  destruct (lr_pools_match_lookup_r _ _ _ _ _ Hpools Hj) as (e & _ & Hthread).
  pose proof (lr_tight_thread_pending_some _ _ _ _ Hthread Hpend) as Hsome.
  unfold lr_mem in *. rewrite lookup_init_mem. case_decide as Hin; [ | done ].
  destruct (loc_in_range_shift _ _ _ Hin) as (z & ->).
  rewrite Hfresh in Hsome. by destruct Hsome.
Qed.

(** Freeing: a pending thread at a freed location could no longer commit. *)
Lemma lr_frame_free tp tp' m mu l n :
  lr_am_safe {| lr_machine_threads := tp'; lr_machine_mem := free_mem l n m;
                lr_machine_rw := free_mem l n mu |} ->
  (forall j t l', tp !! j = Some t -> lr_pending t l' -> tp' !! j = Some t) ->
  lr_frame tp m (free_mem l n m).
Proof.
  intros Hsafe Htp j t l' Hj Hpend.
  destruct (lr_safe_pending_locked _ _ _ _ Hsafe (Htp _ _ _ Hj Hpend) Hpend) as (st & Hst & _).
  simpl in Hst. unfold lr_mem, lr_rw_map, rw_map in *. rewrite lookup_free_mem in Hst.
  rewrite lookup_free_mem. by case_decide.
Qed.

(** * Reference steps *)

(** A machine step to a configuration with a [StuckState] thread
    contradicts safety. *)
Lemma lr_safe_no_stuck_step mc tp' m' mu' i :
  lr_am_safe mc ->
  lr_machine_step mc {| lr_machine_threads := tp'; lr_machine_mem := m'; lr_machine_rw := mu' |} ->
  tp' !! i = Some lr_stuck -> False.
Proof.
  intros Hsafe Hstep Hi.
  pose proof (lr_am_safe_reachable _ _ Hsafe (lr_steps_one _ _ _ Hstep)) as Hsafe'.
  exact (am_stuck_not_safe _ _ _ _ _ (rtc_refl _ _) Hi Hsafe').
Qed.

Lemma lr_tight_pack threads tp m mu i e2 sigma2 tp2 m2 mu2 :
  lr_steps lr_machine_step
    {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |}
    {| lr_machine_threads := tp2; lr_machine_mem := m2; lr_machine_rw := mu2 |} ->
  lr_pools_match (lr_tight_thread_match m2) (<[i := e2]> threads) tp2 ->
  lr_tight_heaps_match sigma2 m2 mu2 ->
  exists mc',
    lr_tight_configuration_match (<[i := e2]> threads ++ [], sigma2) mc' /\
    lr_steps lr_machine_step
      {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |} mc'.
Proof. intros. eexists. rewrite app_nil_r. split; [ | eassumption ]. by split. Qed.

(** * The simulation step *)

Lemma lr_tight_step rc rc' mc :
  lr_tight_configuration_match rc mc ->
  lr_am_safe mc ->
  step rc rc' ->
  exists mc', lr_tight_configuration_match rc' mc' /\ lr_steps lr_machine_step mc mc'.
Proof.
  destruct rc as (threads, sigma). destruct mc as [tp m mu].
  intros (Hpools & Hheaps) Hsafe Hstep. simpl in Hpools, Hheaps.
  apply lr_reference_step_inv in Hstep as (i & e1 & e2 & sigma2 & spawned & Hi & Hprim & ->).
  destruct (lr_pools_match_lookup_l _ _ _ _ _ Hpools Hi) as (c & Hc & Hthread).
  assert (Hsome : is_Some (threads !! i)) by (by eexists).
  assert (Hdom : forall l, sigma !! l = None -> m !! l = None)
    by (intros l; apply (lr_tight_heaps_none _ _ _ l Hheaps)).
  assert (Hdom' : forall l, m !! l = None -> sigma !! l = None)
    by (intros l; apply (lr_tight_heaps_none _ _ _ l Hheaps)).
  inversion Hthread; subst.
  - (* [LRTightSame] *)
    inversion Hprim as [K e1' ? e2' ? ? Hhead HK]; subst.
    assert (Hna2 : na2_free e1' = true) by eauto using na2_free_fill_inv.
    inversion Hhead; subst.
    + (* BinOp *)
      eapply lr_tight_pack; [ | | exact Hheaps ].
      * eapply lr_machine_pure_steps; [ exact Hc | ]. apply LREctxStep, LRBinOpS.
        by eapply bin_op_eval_dom.
      * eapply lr_tight_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
        constructor. by eapply na2_free_fill.
    + (* Beta *)
      simpl in Hna2. na2_split.
      assert (Hna2' : na2_free e2' = true).
      { apply na2_free_subst_l with (f :: xl) (Rec f xl e :: el) e; [ | done | done ].
        by simpl; na2_split. }
      eapply lr_tight_pack; [ | | exact Hheaps ].
      * eapply lr_machine_pure_steps; [ exact Hc | ]. apply LREctxStep. by eapply LRBetaS.
      * eapply lr_tight_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
        constructor. by eapply na2_free_fill.
    + (* ReadSc *)
      destruct (lr_tight_heaps_lookup _ _ _ _ _ _ Hheaps H0) as (v' & Hm & Hmu & [ [=] | <- ] & Hv).
      eapply lr_tight_pack; [ | | exact Hheaps ].
      * apply lr_steps_one. eapply lr_machine_sc_read;
          [ exact Hc | by apply LREctxExternal, LRReadScE | | exact Hm ].
        unfold lr_rw_map, rw_map in *. by rewrite Hmu.
      * eapply lr_tight_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
        constructor. by eapply na2_free_fill.
    + (* ReadNa1: the machine tries now. *)
      destruct (lr_tight_heaps_lookup _ _ _ _ _ _ Hheaps H0) as (v' & Hm & Hmu & [ [=] | <- ] & Hv).
      eapply lr_tight_pack.
      * apply lr_steps_one. eapply lr_machine_try with (T := [lr_read_event l]);
          [ exact Hc | | by apply lr_rsv_read ].
        apply LREctxStep. by apply LRReadNaS.
      * eapply lr_tight_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
        constructor; [ by eapply na2_free_fill | exact Hm ].
      * unfold lr_mem in *. rewrite <- (insert_id m l v) by exact Hm.
        by apply (lr_tight_heaps_insert _ _ _ l (RSt (S n)) v v); [ | right | ].
    + (* ReadNa2: excluded by [na2_free]. *)
      discriminate.
    + (* WriteSc *)
      destruct (lr_tight_heaps_lookup _ _ _ _ _ _ Hheaps H1) as (v'' & Hm & Hmu & [ [=] | <- ] & _).
      simpl in Hna2. rewrite <- (of_to_val e v H0) in Hna2.
      eapply lr_tight_pack.
      * apply lr_steps_one. eapply lr_machine_sc_write;
          [ exact Hc | by apply LREctxExternal, LRWriteScE | exact Hmu | exact Hm ].
      * eapply lr_tight_pools_update; [ exact Hpools | by eapply lr_frame_write | done | ].
        constructor. by eapply na2_free_fill.
      * unfold lr_rw_map, rw_map in *. rewrite <- (insert_id mu l (Rst 0)) by exact Hmu.
        by apply (lr_tight_heaps_insert _ _ _ l (RSt 0) v v); [ | right | ].
    + (* WriteNa1: the machine tries now, writing already. *)
      destruct (lr_tight_heaps_lookup _ _ _ _ _ _ Hheaps H1) as (v'' & Hm & Hmu & [ [=] | <- ] & _).
      simpl in Hna2. rewrite <- (of_to_val e v H0) in Hna2.
      eapply lr_tight_pack.
      * apply lr_steps_one. eapply lr_machine_try with (T := [lr_write_event l]);
          [ exact Hc | | by apply lr_rsv_write ].
        apply LREctxStep. eapply LRWriteNaS; [ exact H0 | exact Hm ].
      * eapply lr_tight_pools_update; [ exact Hpools | by eapply lr_frame_write | done | ].
        apply LRTightWrite with v; [ exact H0 | by eapply na2_free_fill | ].
        unfold lr_mem. apply lookup_insert_eq.
      * by apply (lr_tight_heaps_insert _ _ _ l WSt v' v); [ | left | ].
    + (* WriteNa2: excluded by [na2_free]. *)
      discriminate.
    + (* CasFail *)
      destruct (lr_tight_heaps_lookup _ _ _ _ _ _ Hheaps H2) as (v' & Hm & Hmu & [ [=] | <- ] & _).
      eapply lr_tight_pack; [ | | exact Hheaps ].
      * apply lr_steps_one. eapply lr_machine_cas_fail;
          [ exact Hc | by apply LREctxExternal, LRCasE | | exact Hm | by eapply lit_neq_dom ].
        unfold lr_rw_map, rw_map in *. by rewrite Hmu.
      * eapply lr_tight_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
        constructor. by eapply na2_free_fill.
    + (* CasSuc *)
      destruct (lr_tight_heaps_lookup _ _ _ _ _ _ Hheaps H2) as (v' & Hm & Hmu & [ [=] | <- ] & _).
      eapply lr_tight_pack.
      * apply lr_steps_one. eapply lr_machine_cas_suc;
          [ exact Hc | by apply LREctxExternal, LRCasE | exact Hmu | exact Hm | by eapply lit_eq_dom ].
      * eapply lr_tight_pools_update; [ exact Hpools | by eapply lr_frame_write | done | ].
        constructor. by eapply na2_free_fill.
      * unfold lr_rw_map, rw_map in *. rewrite <- (insert_id mu l (Rst 0)) by exact Hmu.
        by apply (lr_tight_heaps_insert _ _ _ l (RSt 0) (LitV lit2) (LitV lit2)); [ | right | ].
    + (* CasStuck: the machine crashes too, contradicting safety. *)
      exfalso.
      destruct (lr_tight_heaps_lookup _ _ _ _ _ _ Hheaps H2) as (v' & Hm & Hmu & [ [=] | <- ] & _).
      eapply (lr_safe_no_stuck_step _ (<[i := lr_stuck]> tp) m mu i Hsafe).
      * refine (SC_Cas_Stuck tp m mu i _ tt l (LitV lit1) (LitV lit2) (LitV litl) _ Hc _ Hm _ _).
        -- by apply LREctxExternal, LRCasE.
        -- change (lr_val_eq m (LitV litl) (LitV lit1)). simpl. by eapply lit_eq_dom.
        -- intros Hw. apply Forall_inv in Hw. unfold lr_rw_map, rw_map in *.
           setoid_rewrite Hmu in Hw. injection Hw. lia.
      * unfold lr_tpool, tpool. apply lookup_insert_eq.
    + (* Alloc: try and commit together. *)
      assert (Hmfresh : forall z, m !! (l +ₗ z)%L = None) by (intros z; apply Hdom, H1).
      assert (Hmunone : forall z, mu !! (l +ₗ z)%L = None)
        by (intros z; apply (lr_tight_heaps_none _ _ _ _ Hheaps), Hmfresh).
      eapply lr_tight_pack.
      * eapply lr_machine_try_commit_steps with (T := lr_alloc_events l (Z.to_nat n));
          [ exact Hc | | apply lr_alloc_events_nonempty; lia
          | by apply lr_rsv_alloc_events | apply lr_fin_alloc_events ].
        apply LREctxStep, LRAllocS; auto.
      * eapply lr_tight_pools_update; [ exact Hpools | by eapply lr_frame_alloc | done | ].
        constructor. by eapply na2_free_fill.
      * by apply lr_tight_heaps_alloc.
    + (* Free: try and commit together; nothing may be pending there. *)
      assert (Hmurange : forall z, (0 <= z < Z.of_nat (Z.to_nat n))%Z -> is_Some (mu !! (l +ₗ z)%L)).
      { intros z Hz. rewrite Z2Nat.id in Hz by lia.
        destruct (proj2 (H1 z) Hz) as [[st v] Hs].
        destruct (lr_tight_heaps_lookup _ _ _ _ _ _ Hheaps Hs) as (_ & _ & Hmu & _). by eexists. }
      assert (Hsteps : lr_steps lr_machine_step
        {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |}
        {| lr_machine_threads := <[i := lr_running (fill K (Lit LitPoison)) []]> tp;
           lr_machine_mem := free_mem l (Z.to_nat n) m;
           lr_machine_rw := free_mem l (Z.to_nat n) mu |}).
      { eapply lr_machine_try_commit_steps with (T := lr_free_events l (Z.to_nat n));
          [ exact Hc | | apply lr_free_events_nonempty; lia
          | apply lr_rsv_free_events | by apply lr_fin_free_events ].
        apply LREctxStep, LRFreeS; [ done | ].
        intros z. rewrite <- (lr_tight_heaps_is_Some _ _ _ _ Hheaps). apply H1. }
      eapply lr_tight_pack; [ exact Hsteps | | by apply lr_tight_heaps_free ].
      eapply lr_tight_pools_update; [ exact Hpools | | done | ].
      * eapply lr_frame_free; [ exact (lr_am_safe_reachable _ _ Hsafe Hsteps) | ].
        intros j t l' Hj (c' & Hpend). unfold lr_tpool, tpool in *.
        rewrite lookup_insert_ne; [ done | ]. intros <-. rewrite Hc in Hj.
        unfold lr_running in *. destruct Hpend; simplify_eq.
      * constructor. by eapply na2_free_fill.
    + (* Case *)
      simpl in Hna2. na2_split.
      assert (Hna2' : na2_free e2' = true).
      { eapply forallb_forall; [ done | ]. apply list_elem_of_In. by eapply list_elem_of_lookup_2. }
      eapply lr_tight_pack; [ | | exact Hheaps ].
      * eapply lr_machine_pure_steps; [ exact Hc | ]. apply LREctxStep. by eapply LRCaseS.
      * eapply lr_tight_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
        constructor. by eapply na2_free_fill.
    + (* Fork: the machine spawns at the least unused index, which is
         where the reference appends. *)
      simpl in Hna2.
      destruct (tpool_least_free tp) as (j & Hj & Hleast).
      pose proof (lr_pools_match_least_free _ _ _ _ Hpools Hj Hleast) as ->.
      eexists. split; [ split | apply lr_steps_one; by eapply lr_machine_spawn ].
      * simpl. rewrite <- (length_insert threads i (fill K (Lit LitPoison))).
        apply lr_pools_match_snoc; [ | by constructor ].
        eapply lr_tight_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
        constructor. by eapply na2_free_fill.
      * exact Hheaps.
  - (* [LRTightRead]: the second half; the machine commits. *)
    inversion Hprim as [K' e1' ? e2' ? ? Hhead HK]; subst.
    destruct (fill_redex_unique K' K e1' (Read Na2Ord (Lit (LitLoc l)))
                (head_step_redex_shape _ _ _ _ _ Hhead) (na2_read_redex_shape l)
                (head_step_not_val _ _ _ _ _ Hhead) eq_refl HK) as (-> & ->).
    inversion Hhead; subst.
    match goal with Hs : sigma !! l = Some (RSt (S ?k), ?w) |- _ =>
      rename k into n; rename w into v0;
      destruct (lr_tight_heaps_lookup _ _ _ _ _ _ Hheaps Hs) as (v' & Hm & Hmu & [ [=] | <- ] & Hv) end.
    match goal with Hmv : m !! l = Some v |- _ => rewrite Hm in Hmv; injection Hmv as <- end.
    eapply lr_tight_pack.
    + apply lr_steps_one. eapply lr_machine_commit; [ exact Hc | done | by apply lr_fin_read ].
    + eapply lr_tight_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
      by constructor.
    + unfold lr_mem in *. rewrite <- (insert_id m l v0) by exact Hm.
      by apply (lr_tight_heaps_insert _ _ _ l (RSt n) v0 v0); [ | right | ].
  - (* [LRTightWrite] *)
    inversion Hprim as [K' e1' ? e2' ? ? Hhead HK]; subst.
    destruct (fill_redex_unique K' K e1' (Write Na2Ord (Lit (LitLoc l)) e)
                (head_step_redex_shape _ _ _ _ _ Hhead) (na2_write_redex_shape l e v H)
                (head_step_not_val _ _ _ _ _ Hhead) eq_refl HK) as (-> & ->).
    inversion Hhead; subst.
    (* The value being written is the one the machine already stored. *)
    match goal with Hv0 : to_val e = Some ?w |- _ =>
      rewrite H in Hv0; injection Hv0 as <- end.
    match goal with Hs : sigma !! l = Some (WSt, _) |- _ =>
      destruct (lr_tight_heaps_lookup _ _ _ _ _ _ Hheaps Hs) as (w & Hm & Hmu & _ & Hv) end.
    match goal with Hmv : m !! l = Some v |- _ => rewrite Hmv in Hm end.
    injection Hm as <-.
    eapply lr_tight_pack.
    + apply lr_steps_one. eapply lr_machine_commit; [ exact Hc | done | by apply lr_fin_write ].
    + eapply lr_tight_pools_update; [ exact Hpools | apply lr_frame_refl | done | ].
      by constructor.
    + unfold lr_mem in *. rewrite <- (insert_id m l v) by assumption.
      by apply (lr_tight_heaps_insert _ _ _ l (RSt 0) v v); [ | right | ].
Qed.

Lemma lr_tight_steps rc rc' mc :
  lr_tight_configuration_match rc mc ->
  lr_am_safe mc ->
  rtc step rc rc' ->
  exists mc', lr_tight_configuration_match rc' mc' /\ lr_am_safe mc'.
Proof.
  intros Hmatch Hsafe Hsteps. revert mc Hmatch Hsafe.
  induction Hsteps as [ x | x y z Hxy Hyz IH ]; intros mc Hmatch Hsafe; [ eauto | ].
  destruct (lr_tight_step _ _ _ Hmatch Hsafe Hxy) as (mc1 & Hmatch1 & Hsteps1).
  exact (IH mc1 Hmatch1 (lr_am_safe_reachable _ _ Hsafe Hsteps1)).
Qed.

(** * Progress reflection at a single configuration *)

Lemma lr_tight_same_not_stuck tp m mu sigma i e :
  lr_tight_heaps_match sigma m mu ->
  lr_am_safe {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |} ->
  tp !! i = Some (lr_running e []) ->
  lr_reference_not_stuck e sigma.
Proof.
  intros Hheaps Hsafe Hi.
  assert (Hdom' : forall l, m !! l = None -> sigma !! l = None)
    by (intros l; apply (lr_tight_heaps_none _ _ _ l Hheaps)).
  destruct (Hsafe _ _ _ (rtc_refl _ _) i _ Hi) as [(c & Hc & Hfinal) | (tp' & m' & mu' & Hstep)].
  { left. unfold lr_running in Hc. by simplify_eq. }
  right. unfold reducible.
  inversion Hstep; subst;
    unfold lr_tpool, tpool in *;
    apply lookup_singleton_Some in Hget as [_ Hget];
    unfold lr_running in Hget; inversion Hget; subst; try contradiction.
  all: simpl in *.
  - change (lr_step c m T c' m') in Hstep0.
    inversion Hstep0 as [K e1 ? ? e2 ? Hhead]; subst.
    inversion Hhead; subst.
    + do 3 eexists. apply EctxStep, BinOpS. by eapply bin_op_eval_dom.
    + do 3 eexists. apply EctxStep. by eapply BetaS.
    + destruct (lr_rsv_read_inv _ _ _ Hreserve) as (n & Hmu).
      destruct (lr_tight_heaps_lookup_m _ _ _ _ _ Hheaps H) as ([ | n' ] & v0 & Hs & Hmu' & Hv & _);
        unfold lr_rw_map, rw_map in *; rewrite Hmu in Hmu'; simpl in Hmu'; simplify_eq.
      destruct Hv as [ [=] | <- ].
      do 3 eexists. apply EctxStep. by eapply ReadNa1S.
    + apply lr_rsv_write_inv in Hreserve as Hmu.
      destruct (lr_tight_heaps_lookup_m _ _ _ _ _ Hheaps H0) as ([ | n' ] & v0 & Hs & Hmu' & Hv & _);
        unfold lr_rw_map, rw_map in *; rewrite Hmu in Hmu'; simpl in Hmu'; simplify_eq.
      do 3 eexists. apply EctxStep. by eapply WriteNa1S.
    + do 3 eexists. apply EctxStep, AllocS; [ done | ]. intros z. apply Hdom', H0.
    + do 3 eexists. apply EctxStep, FreeS; [ done | ].
      intros z. rewrite (lr_tight_heaps_is_Some _ _ _ _ Hheaps). apply H0.
    + do 3 eexists. apply EctxStep. by eapply CaseS.
  - (* SC_Read *)
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst. simpl in Hload, Hmu.
    apply Forall_inv in Hmu.
    destruct (lr_tight_heaps_lookup_m _ _ _ _ _ Hheaps Hload) as ([ | n' ] & v0 & Hs & Hmu' & Hv & _);
      unfold lr_rw_map, rw_map in *; rewrite Hmu' in Hmu; simpl in Hmu; [ done | ].
    destruct Hv as [ [=] | -> ].
    do 3 eexists. apply EctxStep. by eapply ReadScS.
  - (* SC_Write *)
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst. simpl in Hstore, Hmu.
    apply Forall_inv in Hmu.
    destruct (m !! l) as [v' | ] eqn:Hm; simplify_eq.
    destruct (lr_tight_heaps_lookup_m _ _ _ _ _ Hheaps Hm) as ([ | n' ] & v0 & Hs & Hmu' & _ & _);
      unfold lr_rw_map, rw_map in *; rewrite Hmu' in Hmu; simpl in Hmu; simplify_eq.
    do 3 eexists. apply EctxStep. by eapply WriteScS.
  - (* SC_Cas_Suc *)
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst.
    simpl in Hload, Hmu. apply Forall_inv in Hmu.
    change (lr_val_eq m v_cur (LitV lit1)) in Heq.
    destruct v_cur as [litl | ]; [ | contradiction ]. simpl in Heq.
    destruct (lr_tight_heaps_lookup_m _ _ _ _ _ Hheaps Hload) as ([ | n' ] & v0 & Hs & Hmu' & Hv & _);
      unfold lr_rw_map, rw_map in *; rewrite Hmu' in Hmu; simpl in Hmu; simplify_eq.
    destruct Hv as [ [=] | -> ].
    do 3 eexists. apply EctxStep. eapply CasSucS; eauto. by eapply lit_eq_dom.
  - (* SC_Cas_Fail *)
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst.
    simpl in Hload, Hmu. apply Forall_inv in Hmu.
    change (lr_val_neq m v_cur (LitV lit1)) in Hneq.
    destruct v_cur as [litl | ]; [ | contradiction ]. simpl in Hneq.
    destruct (lr_tight_heaps_lookup_m _ _ _ _ _ Hheaps Hload) as ([ | n' ] & v0 & Hs & Hmu' & Hv & _);
      unfold lr_rw_map, rw_map in *; rewrite Hmu' in Hmu; simpl in Hmu; [ done | ].
    destruct Hv as [ [=] | -> ].
    do 3 eexists. apply EctxStep. eapply CasFailS; eauto. by eapply lit_neq_dom.
  - (* SC_Cas_Stuck: reducible, but only to a crash; taking the step in
       the full pool contradicts safety. *)
    exfalso. eapply (lr_safe_no_stuck_step _ (<[i := lr_stuck]> tp) m mu i Hsafe).
    + exact (SC_Cas_Stuck tp m mu i _ ly l v_exp v_new v_cur K Hi Hext Hload Heq Ho).
    + unfold lr_tpool, tpool. apply lookup_insert_eq.
  - (* Spawn *)
    inversion Hspawn; subst. do 3 eexists. apply EctxStep, ForkS.
Qed.

Lemma lr_fin_read_inv (mu mu' : lr_rw_map) l :
  fin [lr_read_event l] mu = Some mu' -> exists n, mu !! l = Some (Rst (S n)).
Proof.
  unfold lr_rw_map, rw_map in *. unfold fin. simpl. unfold fin_Read.
  destruct (_ !! l) as [[[ | n] | ] | ] eqn:Hl; simpl; intros Hf; try discriminate Hf; eauto.
Qed.

Lemma lr_fin_write_inv (mu mu' : lr_rw_map) l :
  fin [lr_write_event l] mu = Some mu' -> mu !! l = Some Wst.
Proof.
  unfold lr_rw_map, rw_map in *. unfold fin. simpl. unfold fin_Write.
  destruct (_ !! l) as [[[ | n] | ] | ] eqn:Hl; simpl; intros Hf; try discriminate Hf; reflexivity.
Qed.

Lemma lr_safe_pending_fin tp m mu j c ev :
  lr_am_safe {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |} ->
  tp !! j = Some (lr_running c [ev]) ->
  exists mu', fin [ev] mu = Some mu'.
Proof.
  intros Hsafe Hj. pose proof (Hsafe _ _ _ (rtc_refl _ _) j _ Hj) as Hns.
  by apply am_pending_not_stuck in Hns.
Qed.

Lemma lr_tight_not_stuck rc mc :
  lr_tight_configuration_match rc mc -> lr_am_safe mc ->
  forall e, e ∈ rc.1 -> lr_reference_not_stuck e rc.2.
Proof.
  destruct rc as (threads, sigma), mc as [tp m mu].
  intros (Hpools & Hheaps) Hsafe e He. simpl in *.
  apply list_elem_of_lookup_1 in He as [i He].
  destruct (lr_pools_match_lookup_l _ _ _ _ _ Hpools He) as (t & Ht & Hthread).
  inversion Hthread; subst.
  - by eapply lr_tight_same_not_stuck.
  - (* A pending read can commit, so the reference lock is [RSt (S _)]. *)
    destruct (lr_safe_pending_fin _ _ _ _ _ _ Hsafe Ht) as (mu' & Hfin).
    apply lr_fin_read_inv in Hfin as (n & Hmu).
    destruct (lr_tight_heaps_lookup_m _ _ _ _ _ Hheaps H0) as ([ | n' ] & v0 & Hs & Hmu' & _ & _);
      unfold lr_rw_map, rw_map in *; rewrite Hmu in Hmu'; simpl in Hmu'; simplify_eq.
    right. do 3 eexists. apply EctxStep. by eapply ReadNa2S.
  - (* A pending write can commit, so the reference lock is [WSt]. *)
    destruct (lr_safe_pending_fin _ _ _ _ _ _ Hsafe Ht) as (mu' & Hfin).
    apply lr_fin_write_inv in Hfin as Hmu.
    destruct (lr_tight_heaps_lookup_m _ _ _ _ _ Hheaps H1) as ([ | n' ] & v0 & Hs & Hmu' & _ & _);
      unfold lr_rw_map, rw_map in *; rewrite Hmu in Hmu'; simpl in Hmu'; simplify_eq.
    right. do 3 eexists. apply EctxStep. by eapply WriteNa2S.
Qed.

(** * The theorem *)

Theorem lr_am_safe_reference_safe rc0 mc0 :
  lr_tight_configuration_match rc0 mc0 ->
  lr_am_safe mc0 ->
  lr_reference_safe rc0.
Proof.
  intros Hmatch Hsafe threads sigma Hsteps.
  destruct (lr_tight_steps _ _ _ Hmatch Hsafe Hsteps) as (mc & Hmatch' & Hsafe').
  exact (lr_tight_not_stuck _ _ Hmatch' Hsafe').
Qed.

Corollary lr_am_safe_reference_safe_stable rc0 mc0 :
  lr_stable_configuration_match rc0 mc0 ->
  lr_am_safe mc0 ->
  lr_reference_safe rc0.
Proof. intros Hmatch. apply lr_am_safe_reference_safe, lr_stable_tight, Hmatch. Qed.
