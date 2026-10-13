(**
  Statement of the equivalence between the lambda-Rust reference semantics
  and its atomic-machine implementation.

  The two systems expose different administrative states: the atomic machine
  reserves and commits events, while the reference semantics uses [Na2Ord].
  We therefore compare reflexive-transitive reachability between stable
  configurations, where neither representation has an access in flight.

  Thread creation is matched by the machine's [Spawn] rule: the reference
  appends the new thread to its list, and the machine gives it the least
  unused index, which is the same position.
*)

From Stdlib Require Import List Lia.
From stdpp Require Import gmap list.

Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.machine.

Import ListNotations.

Set Default Proof Using "Type".

Lemma lr_reference_two_steps threads sigma i e1 e2 e3 sigma2 sigma3 :
  threads !! i = Some e1 ->
  prim_step e1 sigma e2 sigma2 [] ->
  prim_step e2 sigma2 e3 sigma3 [] ->
  rtc step (threads, sigma) (<[i := e3]> threads, sigma3).
Proof.
  intros Hi H12 H23. rewrite <- (list_insert_insert_eq _ i e3 e2).
  eapply rtc_l; [ | apply rtc_once ]; eapply lr_reference_step_at; eauto.
  apply list_lookup_insert_eq, lookup_lt_is_Some_1. eauto.
Qed.

(** * Forward and backward relations

    The two directions of the proof use two different simulation
    relations, because the two systems read a non-atomic value at
    different moments: the reference reads at the second ([Na2Ord]) step,
    the machine at [Core_Try].

    - Forward (reference drives): the machine lags behind.  A reference
      thread that has done its first half is matched by the machine thread
      that has not started, and the machine performs [Core_Try] and
      [Core_Commit] together when the reference performs its second half.
      Every machine location is therefore always at [Rst 0].
    - Backward (machine drives): the reference runs ahead.  Whenever the
      machine performs [Core_Try] the reference performs both halves, so
      the reference heap is always at [RSt 0] and the reader/writer map
      is unconstrained.  A crashed machine thread matches anything. *)

Inductive lr_forward_thread_match : expr -> lr_tstate -> Prop :=
| LRForwardSame e :
    na2_free e = true ->
    lr_forward_thread_match e (lr_running e [])
| LRForwardReadNa2 K l :
    na2_free (fill K (Read Na1Ord (Lit (LitLoc l)))) = true ->
    lr_forward_thread_match
      (fill K (Read Na2Ord (Lit (LitLoc l))))
      (lr_running (fill K (Read Na1Ord (Lit (LitLoc l)))) [])
| LRForwardWriteNa2 K l e v :
    to_val e = Some v ->
    na2_free (fill K (Write Na1Ord (Lit (LitLoc l)) e)) = true ->
    lr_forward_thread_match
      (fill K (Write Na2Ord (Lit (LitLoc l)) e))
      (lr_running (fill K (Write Na1Ord (Lit (LitLoc l)) e)) [])
| LRForwardStuck K c :
    lr_forward_thread_match (fill K stuck_term) c.

Definition lr_forward_heaps_match
    (sigma : state) (m : lr_mem) (mu : lr_rw_map) : Prop :=
  forall l,
    match m !! l with
    | Some v =>
        (exists st, sigma !! l = Some (st, v)) /\
        mu !! l = Some (Rst 0) /\
        na2_free (of_val v) = true
    | None => sigma !! l = None /\ mu !! l = None
    end.

Definition lr_forward_configuration_match
    (rc : configuration) (mc : lr_machine_configuration) : Prop :=
  let '(threads, sigma) := rc in
  lr_pools_match lr_forward_thread_match threads (lr_machine_threads mc) /\
  lr_forward_heaps_match sigma (lr_machine_mem mc) (lr_machine_rw mc).

Definition lr_backward_thread_match (e : expr) (c : lr_tstate) : Prop :=
  match c with
  | Running e' _ => e = e'
  | StuckState => True
  end.

Definition lr_backward_heaps_match (sigma : state) (m : lr_mem) : Prop :=
  forall l,
    match m !! l with
    | Some v => sigma !! l = Some (RSt 0, v)
    | None => sigma !! l = None
    end.

Definition lr_backward_configuration_match
    (rc : configuration) (mc : lr_machine_configuration) : Prop :=
  let '(threads, sigma) := rc in
  lr_pools_match lr_backward_thread_match threads (lr_machine_threads mc) /\
  lr_backward_heaps_match sigma (lr_machine_mem mc).

Ltac lr_eq_unfold :=
  unfold lr_forward_configuration_match, lr_backward_configuration_match,
    lr_forward_heaps_match, lr_backward_heaps_match in *; lr_unfold.

(** Pointwise reasoning about a heap relation: specialize at the location
    under consideration, then split on the machine heap. *)

Ltac lr_heaps_at Hheaps l :=
  specialize (Hheaps l); lr_eq_unfold; destruct (_ !! l) eqn:?; naive_solver.

Lemma lr_stable_forward rc mc :
  lr_stable_configuration_match rc mc -> lr_forward_configuration_match rc mc.
Proof.
  destruct rc as (threads, sigma). intros (Hpools & Hheaps). split.
  - eapply lr_pools_match_impl; [ | exact Hpools ]. intros ? ? []. by constructor.
  - intros l. lr_heaps_at Hheaps l.
Qed.

Lemma lr_stable_backward rc mc :
  lr_stable_configuration_match rc mc -> lr_backward_configuration_match rc mc.
Proof.
  destruct rc as (threads, sigma). intros (Hpools & Hheaps). split.
  - eapply lr_pools_match_impl; [ | exact Hpools ]. by intros ? ? [].
  - intros l. lr_heaps_at Hheaps l.
Qed.

(** A forward-matched configuration that is also stably matched is at the
    stable machine configuration: pending accesses and crashed threads are
    excluded by stability. *)

Lemma lr_forward_thread_match_stable e c :
  na2_free e = true -> ~ lr_crashed e -> lr_forward_thread_match e c -> c = lr_running e [].
Proof.
  intros Hna2 Hcrash Hm. inversion Hm; subst;
    [ done | by rewrite na2_free_read_na2 in Hna2 | by rewrite na2_free_write_na2 in Hna2 | ].
  exfalso. apply Hcrash. by eexists.
Qed.

Lemma lr_forward_stable_unique rc mc mc' :
  lr_forward_configuration_match rc mc' ->
  lr_stable_configuration_match rc mc ->
  mc' = mc.
Proof.
  destruct rc as (threads, sigma). destruct mc as [tp m mu], mc' as [tp' m' mu'].
  intros (Hpools' & Hheaps') (Hpools & Hheaps). lr_eq_unfold. simpl in *.
  assert (m' = m) as ->.
  { apply map_eq. intros l. specialize (Hheaps l). specialize (Hheaps' l).
    destruct (m !! l), (m' !! l); naive_solver. }
  assert (mu' = mu) as ->.
  { apply map_eq. intros l. specialize (Hheaps l). specialize (Hheaps' l).
    destruct (m !! l); intuition congruence. }
  f_equal. apply (map_eq (M := gmap nat)). intros i.
  specialize (Hpools i). specialize (Hpools' i).
  destruct (threads !! i), (tp !! i), (tp' !! i); try done.
  inversion Hpools; subst. by rewrite (lr_forward_thread_match_stable _ _ H H0 Hpools').
Qed.

Lemma lr_backward_stable_unique rc rc' mc :
  lr_backward_configuration_match rc' mc ->
  lr_stable_configuration_match rc mc ->
  rc' = rc.
Proof.
  destruct rc as (threads, sigma), rc' as (threads', sigma'). destruct mc as [tp m mu].
  intros (Hpools' & Hheaps') (Hpools & Hheaps). lr_eq_unfold. simpl in *. f_equal.
  - apply list_eq. intros i. specialize (Hpools i). specialize (Hpools' i).
    destruct (tp !! i), (threads !! i), (threads' !! i); try done.
    inversion Hpools; subst. simpl in Hpools'. by subst.
  - apply map_eq. intros l. specialize (Hheaps l). specialize (Hheaps' l).
    destruct (m !! l); intuition congruence.
Qed.

(** ** Heap facts used by the forward direction *)

Lemma lr_forward_heaps_lookup sigma m mu l st v :
  lr_forward_heaps_match sigma m mu -> sigma !! l = Some (st, v) ->
  m !! l = Some v /\ mu !! l = Some (Rst 0) /\ na2_free (of_val v) = true.
Proof. intros Hheaps Hs. lr_heaps_at Hheaps l. Qed.

Lemma lr_forward_heaps_none sigma m mu l :
  lr_forward_heaps_match sigma m mu -> sigma !! l = None ->
  m !! l = None /\ mu !! l = None.
Proof. intros Hheaps Hs. lr_heaps_at Hheaps l. Qed.

Lemma lr_forward_heaps_is_Some sigma m mu l :
  lr_forward_heaps_match sigma m mu ->
  is_Some (m !! l) <-> is_Some (sigma !! l).
Proof.
  intros Hheaps. specialize (Hheaps l). lr_eq_unfold. destruct (m !! l).
  - destruct Hheaps as ((st & ->) & _). by split; eauto.
  - destruct Hheaps as (-> & _). by split; intros [].
Qed.

Lemma lr_forward_heaps_relock sigma m mu l st st' v :
  lr_forward_heaps_match sigma m mu -> sigma !! l = Some (st, v) ->
  lr_forward_heaps_match (<[l := (st', v)]> sigma) m mu.
Proof.
  intros Hheaps Hs l'. specialize (Hheaps l'). lr_eq_unfold.
  destruct (decide (l = l')) as [<- | ]; [ rewrite lookup_insert_eq | by rewrite lookup_insert_ne ].
  destruct (m !! l); naive_solver.
Qed.

Lemma lr_forward_heaps_write sigma m mu l st v' v :
  lr_forward_heaps_match sigma m mu -> m !! l = Some v' -> na2_free (of_val v) = true ->
  lr_forward_heaps_match (<[l := (st, v)]> sigma) (<[l := v]> m) mu.
Proof.
  intros Hheaps Hm Hna2 l'. specialize (Hheaps l'). lr_eq_unfold.
  destruct (decide (l = l')) as [<- | ]; [ rewrite !lookup_insert_eq | by rewrite !lookup_insert_ne ].
  rewrite Hm in Hheaps. naive_solver.
Qed.

Lemma lr_forward_heaps_alloc sigma m mu l n :
  lr_forward_heaps_match sigma m mu ->
  lr_forward_heaps_match
    (init_mem (RSt 0, LitV LitPoison) l n sigma)
    (init_mem (LitV LitPoison) l n m)
    (init_mem (Rst 0) l n mu).
Proof.
  intros Hheaps l'. specialize (Hheaps l'). lr_eq_unfold. rewrite !lookup_init_mem.
  case_decide; naive_solver.
Qed.

Lemma lr_forward_heaps_free sigma m mu l n :
  lr_forward_heaps_match sigma m mu ->
  lr_forward_heaps_match (free_mem l n sigma) (free_mem l n m) (free_mem l n mu).
Proof.
  intros Hheaps l'. specialize (Hheaps l'). lr_eq_unfold. rewrite !lookup_free_mem.
  case_decide; naive_solver.
Qed.

Lemma lr_forward_heaps_dom sigma m mu :
  lr_forward_heaps_match sigma m mu ->
  forall l, sigma !! l = None -> m !! l = None.
Proof. intros Hheaps l Hs. by apply (lr_forward_heaps_none _ _ _ _ Hheaps Hs). Qed.

(** * Forward simulation: reference steps are matched by machine steps *)

(** Packaging of a forward step: the machine steps come first so that
    they determine the target configuration before the matching goals. *)

Lemma lr_forward_pack threads tp m mu i e2 sigma2 tp2 m2 mu2 :
  rtc lr_machine_step
    {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |}
    {| lr_machine_threads := tp2; lr_machine_mem := m2; lr_machine_rw := mu2 |} ->
  lr_pools_match lr_forward_thread_match (<[i := e2]> threads) tp2 ->
  lr_forward_heaps_match sigma2 m2 mu2 ->
  exists mc',
    lr_forward_configuration_match (<[i := e2]> threads, sigma2) mc' /\
    rtc lr_machine_step
      {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |} mc'.
Proof. intros. eexists. split; [ | eassumption ]. by split. Qed.

(** The common case: both sides step in lockstep under the same context. *)

Lemma lr_forward_pools_same threads tp i K e1 e2 :
  lr_pools_match lr_forward_thread_match threads tp -> is_Some (threads !! i) ->
  na2_free (fill K e1) = true -> na2_free e2 = true ->
  lr_pools_match lr_forward_thread_match
    (<[i := fill K e2]> threads) (<[i := lr_running (fill K e2) []]> tp).
Proof. intros. apply lr_pools_match_insert; auto. constructor. eauto using na2_free_fill. Qed.

Lemma lr_forward_step rc rc' mc :
  lr_forward_configuration_match rc mc ->
  step rc rc' ->
  exists mc', lr_forward_configuration_match rc' mc' /\ rtc lr_machine_step mc mc'.
Proof.
  destruct rc as (threads, sigma). destruct mc as [tp m mu].
  intros (Hpools & Hheaps) Hstep. simpl in Hpools, Hheaps.
  apply lr_reference_step_inv in Hstep as (i & e1 & e2 & sigma2 & spawned & Hi & Hprim & ->).
  destruct (lr_pools_match_lookup_l _ _ _ _ _ Hpools Hi) as (c & Hc & Hthread).
  assert (Hsome : is_Some (threads !! i)) by (by eexists).
  pose proof (lr_forward_heaps_dom _ _ _ Hheaps) as Hdom.
  inversion Hthread; subst.
  - (* [LRForwardSame] *)
    inversion Hprim as [K e1' ? e2' ? ? Hhead HK]; subst.
    inversion Hhead; subst; rewrite ?app_nil_r.
    + (* BinOp *)
      eapply lr_forward_pack; [ | by eapply lr_forward_pools_same; eauto | exact Hheaps ].
      eapply lr_machine_pure_steps; [ exact Hc | ]. apply LREctxStep, LRBinOpS.
      by eapply bin_op_eval_dom.
    + (* Beta *)
      assert (Hna2 : na2_free (App (Rec f xl e) el) = true) by eauto using na2_free_fill_inv.
      simpl in Hna2. na2_split.
      assert (Hna2' : na2_free e2' = true).
      { apply na2_free_subst_l with (f :: xl) (Rec f xl e :: el) e; [ | done | done ].
        by simpl; na2_split. }
      eapply lr_forward_pack; [ | by eapply lr_forward_pools_same; eauto | exact Hheaps ].
      eapply lr_machine_pure_steps; [ exact Hc | ]. apply LREctxStep. by eapply LRBetaS.
    + (* ReadSc *)
      destruct (lr_forward_heaps_lookup _ _ _ _ _ _ Hheaps H0) as (Hm & Hmu & Hv).
      eapply lr_forward_pack;
        [ apply rtc_once; eapply lr_machine_sc_read; [ exact Hc | by apply LREctxExternal, LRReadScE | | exact Hm ]
        | by eapply lr_forward_pools_same; eauto | exact Hheaps ].
      intros Hw. setoid_rewrite Hmu in Hw. discriminate.
    + (* ReadNa1: the machine waits for the second half. *)
      eapply lr_forward_pack; [ apply rtc_refl | | by eapply lr_forward_heaps_relock ].
      eapply lr_pools_match_keep; [ exact Hpools | exact Hc | ]. by apply LRForwardReadNa2.
    + (* ReadNa2: excluded by [na2_free]. *)
      by rewrite na2_free_read_na2 in H.
    + (* WriteSc *)
      destruct (lr_forward_heaps_lookup _ _ _ _ _ _ Hheaps H1) as (Hm & Hmu & _).
      assert (Hna2 : na2_free (Write ScOrd (Lit (LitLoc l)) e) = true) by eauto using na2_free_fill_inv.
      simpl in Hna2. rewrite <- (of_to_val e v H0) in Hna2.
      eapply lr_forward_pack;
        [ apply rtc_once; eapply lr_machine_sc_write; [ exact Hc | by apply LREctxExternal, LRWriteScE | exact Hmu | exact Hm ]
        | by eapply lr_forward_pools_same; eauto | by eapply lr_forward_heaps_write ].
    + (* WriteNa1: the machine waits for the second half. *)
      eapply lr_forward_pack; [ apply rtc_refl | | by eapply lr_forward_heaps_relock ].
      eapply lr_pools_match_keep; [ exact Hpools | exact Hc | ]. by eapply LRForwardWriteNa2.
    + (* WriteNa2: excluded by [na2_free]. *)
      by rewrite na2_free_write_na2 in H.
    + (* CasFail *)
      destruct (lr_forward_heaps_lookup _ _ _ _ _ _ Hheaps H2) as (Hm & Hmu & _).
      eapply lr_forward_pack;
        [ apply rtc_once; eapply lr_machine_cas_fail;
            [ exact Hc | by apply LREctxExternal, LRCasE | | exact Hm | by eapply lit_neq_dom ]
        | by eapply lr_forward_pools_same; eauto | exact Hheaps ].
      intros Hw. setoid_rewrite Hmu in Hw. discriminate.
    + (* CasSuc *)
      destruct (lr_forward_heaps_lookup _ _ _ _ _ _ Hheaps H2) as (Hm & Hmu & _).
      eapply lr_forward_pack;
        [ apply rtc_once; eapply lr_machine_cas_suc;
            [ exact Hc | by apply LREctxExternal, LRCasE | exact Hmu | exact Hm | by eapply lit_eq_dom ]
        | by eapply lr_forward_pools_same; eauto | by eapply lr_forward_heaps_write ].
    + (* CasStuck: the reference thread crashes; the machine, which sees
         [Rst 0], would have succeeded, but crashed threads are outside
         the stable correspondence anyway. *)
      eapply lr_forward_pack; [ apply rtc_refl | | exact Hheaps ].
      eapply lr_pools_match_keep; [ exact Hpools | exact Hc | apply LRForwardStuck ].
    + (* Alloc: try and commit together. *)
      assert (Hmunone : forall z, mu !! (l +ₗ z)%L = None)
        by (intros z; apply (lr_forward_heaps_none _ _ _ _ Hheaps (H1 z))).
      eapply lr_forward_pack; [ | by eapply lr_forward_pools_same; eauto | by apply lr_forward_heaps_alloc ].
      eapply lr_machine_try_commit_steps with (T := lr_alloc_events l (Z.to_nat n));
        [ exact Hc | | apply lr_alloc_events_nonempty; lia | by apply lr_rsv_alloc_events | apply lr_fin_alloc_events ].
      apply LREctxStep, LRAllocS; auto.
    + (* Free: try and commit together. *)
      assert (Hmurange : forall z, (0 <= z < Z.of_nat (Z.to_nat n))%Z -> is_Some (mu !! (l +ₗ z)%L)).
      { intros z Hz. rewrite Z2Nat.id in Hz by lia.
        destruct (proj2 (H1 z) Hz) as [[st v] Hs].
        destruct (lr_forward_heaps_lookup _ _ _ _ _ _ Hheaps Hs) as (_ & Hmu & _). by eexists. }
      eapply lr_forward_pack; [ | by eapply lr_forward_pools_same; eauto | by apply lr_forward_heaps_free ].
      eapply lr_machine_try_commit_steps with (T := lr_free_events l (Z.to_nat n));
        [ exact Hc | | apply lr_free_events_nonempty; lia | apply lr_rsv_free_events | by apply lr_fin_free_events ].
      apply LREctxStep, LRFreeS; [ done | ].
      intros z. rewrite (lr_forward_heaps_is_Some _ _ _ _ Hheaps). apply H1.
    + (* Case *)
      assert (Hna2 : na2_free (Case (Lit (LitInt i0)) el) = true) by eauto using na2_free_fill_inv.
      simpl in Hna2. na2_split.
      assert (Hna2' : na2_free e2' = true).
      { eapply forallb_forall; [ done | ]. apply list_elem_of_In. by eapply list_elem_of_lookup_2. }
      eapply lr_forward_pack; [ | by eapply lr_forward_pools_same; eauto | exact Hheaps ].
      eapply lr_machine_pure_steps; [ exact Hc | ]. apply LREctxStep. by eapply LRCaseS.
    + (* Fork: the machine spawns at the least unused index, which is
         where the reference appends. *)
      assert (Hna2 : na2_free (Fork e) = true) by eauto using na2_free_fill_inv.
      simpl in Hna2.
      destruct (tpool_least_free tp) as (j & Hj & Hleast).
      pose proof (lr_pools_match_least_free _ _ _ _ Hpools Hj Hleast) as ->.
      eexists. split; [ split | apply rtc_once; by eapply lr_machine_spawn ].
      * simpl. rewrite <- (length_insert threads i (fill K (Lit LitPoison))).
        apply lr_pools_match_snoc; [ by eapply lr_forward_pools_same | by constructor ].
      * exact Hheaps.
  - (* [LRForwardReadNa2]: the second half; the machine now tries and commits. *)
    inversion Hprim as [K' e1' ? e2' ? ? Hhead HK]; subst.
    destruct (fill_redex_unique K' K e1' (Read Na2Ord (Lit (LitLoc l)))
                (head_step_redex_shape _ _ _ _ _ Hhead) (na2_read_redex_shape l)
                (head_step_not_val _ _ _ _ _ Hhead) eq_refl HK) as (-> & ->).
    inversion Hhead; subst; rewrite ?app_nil_r.
    match goal with Hs : sigma !! l = Some (RSt (S _), _) |- _ =>
      destruct (lr_forward_heaps_lookup _ _ _ _ _ _ Hheaps Hs) as (Hm & Hmu & Hv) end.
    destruct (rsv_fin_read mu l 0 Hmu) as (mu' & Hrsv & Hfin).
    eapply lr_forward_pack; [ | by eapply lr_forward_pools_same; eauto | by eapply lr_forward_heaps_relock ].
    eapply lr_machine_try_commit_steps with (T := [lr_read_event l]);
      [ exact Hc | | done | exact Hrsv | exact Hfin ].
    apply LREctxStep. by apply LRReadNaS.
  - (* [LRForwardWriteNa2] *)
    inversion Hprim as [K' e1' ? e2' ? ? Hhead HK]; subst.
    destruct (fill_redex_unique K' K e1' (Write Na2Ord (Lit (LitLoc l)) e)
                (head_step_redex_shape _ _ _ _ _ Hhead) (na2_write_redex_shape l e v H)
                (head_step_not_val _ _ _ _ _ Hhead) eq_refl HK) as (-> & ->).
    inversion Hhead; subst; rewrite ?app_nil_r.
    match goal with Hs : sigma !! l = Some (WSt, _) |- _ =>
      destruct (lr_forward_heaps_lookup _ _ _ _ _ _ Hheaps Hs) as (Hm & Hmu & _) end.
    destruct (rsv_fin_write mu l Hmu) as (mu' & Hrsv & Hfin).
    assert (Hna2 : na2_free (Write Na1Ord (Lit (LitLoc l)) e) = true) by eauto using na2_free_fill_inv.
    simpl in Hna2. rewrite <- (of_to_val e v H) in Hna2. simplify_eq.
    eapply lr_forward_pack; [ | by eapply lr_forward_pools_same; eauto | by eapply lr_forward_heaps_write ].
    eapply lr_machine_try_commit_steps with (T := [lr_write_event l]);
      [ exact Hc | | done | exact Hrsv | exact Hfin ].
    apply LREctxStep. by eapply LRWriteNaS.
  - (* [LRForwardStuck] *)
    exfalso. exact (crashed_no_step _ _ _ _ _ Hprim).
Qed.

(** * Backward simulation: machine steps are matched by reference steps *)

Lemma lr_backward_heaps_lookup sigma m l v :
  lr_backward_heaps_match sigma m -> m !! l = Some v -> sigma !! l = Some (RSt 0, v).
Proof. intros Hheaps Hm. lr_heaps_at Hheaps l. Qed.

Lemma lr_backward_heaps_dom sigma m :
  lr_backward_heaps_match sigma m ->
  forall l, m !! l = None -> sigma !! l = None.
Proof. intros Hheaps l Hm. lr_heaps_at Hheaps l. Qed.

Lemma lr_backward_heaps_is_Some sigma m l :
  lr_backward_heaps_match sigma m -> is_Some (sigma !! l) <-> is_Some (m !! l).
Proof.
  intros Hheaps. specialize (Hheaps l). lr_eq_unfold. destruct (m !! l); rewrite Hheaps.
  - by split; eauto.
  - by split; intros [].
Qed.

Lemma lr_backward_heaps_write sigma m l v :
  lr_backward_heaps_match sigma m ->
  lr_backward_heaps_match (<[l := (RSt 0, v)]> sigma) (<[l := v]> m).
Proof.
  intros Hheaps l'. specialize (Hheaps l'). lr_eq_unfold.
  destruct (decide (l = l')) as [<- | ]; [ by rewrite !lookup_insert_eq | by rewrite !lookup_insert_ne ].
Qed.

Lemma lr_backward_heaps_alloc sigma m l n :
  lr_backward_heaps_match sigma m ->
  lr_backward_heaps_match
    (init_mem (RSt 0, LitV LitPoison) l n sigma)
    (init_mem (LitV LitPoison) l n m).
Proof.
  intros Hheaps l'. specialize (Hheaps l'). lr_eq_unfold. rewrite !lookup_init_mem.
  case_decide; naive_solver.
Qed.

Lemma lr_backward_heaps_free sigma m l n :
  lr_backward_heaps_match sigma m ->
  lr_backward_heaps_match (free_mem l n sigma) (free_mem l n m).
Proof.
  intros Hheaps l'. specialize (Hheaps l'). lr_eq_unfold. rewrite !lookup_free_mem.
  case_decide; naive_solver.
Qed.

Lemma lr_backward_pack threads sigma tp' m' mu' i e2 sigma2 :
  rtc step (threads, sigma) (<[i := e2]> threads, sigma2) ->
  lr_pools_match lr_backward_thread_match (<[i := e2]> threads) tp' ->
  lr_backward_heaps_match sigma2 m' ->
  exists rc',
    lr_backward_configuration_match rc'
      {| lr_machine_threads := tp'; lr_machine_mem := m'; lr_machine_rw := mu' |} /\
    rtc step (threads, sigma) rc'.
Proof. intros. eexists. split; [ | eassumption ]. by split. Qed.

Lemma lr_backward_pack_refl threads sigma tp' m' mu' :
  lr_pools_match lr_backward_thread_match threads tp' ->
  lr_backward_heaps_match sigma m' ->
  exists rc',
    lr_backward_configuration_match rc'
      {| lr_machine_threads := tp'; lr_machine_mem := m'; lr_machine_rw := mu' |} /\
    rtc step (threads, sigma) rc'.
Proof. intros. exists (threads, sigma). split; [ by split | constructor ]. Qed.

(** The machine thread at [i] is running the reference thread at [i]. *)

Ltac lr_backward_thread Hpools Hget He :=
  let e := fresh "e" in let Hec := fresh "Hec" in
  destruct (lr_pools_match_lookup_r _ _ _ _ _ Hpools Hget) as (e & He & Hec);
  simpl in Hec; subst e.

Lemma lr_backward_step rc mc mc' :
  lr_backward_configuration_match rc mc ->
  lr_machine_step mc mc' ->
  exists rc', lr_backward_configuration_match rc' mc' /\ rtc step rc rc'.
Proof.
  destruct rc as (threads, sigma). destruct mc as [tp m mu], mc' as [tp' m' mu'].
  intros (Hpools & Hheaps) Hstep. simpl in Hpools, Hheaps.
  unfold lr_machine_step in Hstep. simpl in Hstep.
  pose proof (lr_backward_heaps_dom _ _ Hheaps) as Hdom.
  inversion Hstep; subst; lr_backward_thread Hpools Hget He;
    assert (Hsome : is_Some (threads !! i)) by (by eexists).
  - (* Core_Try *)
    change (lr_step c m T c' m') in Hstep0.
    inversion Hstep0 as [K e1 ? ? e2 ? Hhead]; subst.
    inversion Hhead; subst;
      (eapply lr_backward_pack; [ | by apply lr_pools_match_insert | ]).
    + (* BinOp *)
      apply rtc_once. eapply lr_reference_step_at; [ exact He | ].
      apply EctxStep, BinOpS. by eapply bin_op_eval_dom.
    + exact Hheaps.
    + (* Beta *)
      apply rtc_once. eapply lr_reference_step_at; [ exact He | ]. apply EctxStep. by eapply BetaS.
    + exact Hheaps.
    + (* ReadNa: the reference performs both halves at once. *)
      pose proof (lr_backward_heaps_lookup _ _ _ _ Hheaps H) as Hs.
      eapply lr_reference_two_steps; [ exact He | | ].
      * apply EctxStep. by apply ReadNa1S.
      * apply EctxStep. apply ReadNa2S. apply lookup_insert_eq.
    + pose proof (lr_backward_heaps_lookup _ _ _ _ Hheaps H) as Hs.
      lr_eq_unfold. by rewrite insert_insert_eq, insert_id.
    + (* WriteNa: both halves. *)
      pose proof (lr_backward_heaps_lookup _ _ _ _ Hheaps H0) as Hs.
      eapply lr_reference_two_steps; [ exact He | | ].
      * apply EctxStep. by eapply WriteNa1S.
      * apply EctxStep. eapply WriteNa2S; [ done | apply lookup_insert_eq ].
    + lr_eq_unfold. rewrite insert_insert_eq. by apply lr_backward_heaps_write.
    + (* Alloc *)
      apply rtc_once. eapply lr_reference_step_at; [ exact He | ].
      apply EctxStep, AllocS; [ done | intros z; apply Hdom, H0 ].
    + by apply lr_backward_heaps_alloc.
    + (* Free *)
      apply rtc_once. eapply lr_reference_step_at; [ exact He | ].
      apply EctxStep, FreeS; [ done | ].
      intros z. rewrite (lr_backward_heaps_is_Some _ _ _ Hheaps). apply H0.
    + by apply lr_backward_heaps_free.
    + (* Case *)
      apply rtc_once. eapply lr_reference_step_at; [ exact He | ]. apply EctxStep. by eapply CaseS.
    + exact Hheaps.
  - (* Core_Commit: nothing to do on the reference side. *)
    apply lr_backward_pack_refl; [ | exact Hheaps ]. by eapply lr_pools_match_insert_r.
  - (* SC_Read *)
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst. simpl in Hload.
    pose proof (lr_backward_heaps_lookup _ _ _ _ Hheaps Hload) as Hs.
    eapply lr_backward_pack; [ | by apply lr_pools_match_insert | exact Hheaps ].
    apply rtc_once. eapply lr_reference_step_at; [ exact He | ].
    apply EctxStep. by apply (ReadScS l 0%nat).
  - (* SC_Write *)
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst. simpl in Hstore.
    destruct (m !! l) as [v' | ] eqn:Hm; simplify_eq.
    pose proof (lr_backward_heaps_lookup _ _ _ _ Hheaps Hm) as Hs.
    eapply lr_backward_pack; [ | by apply lr_pools_match_insert | by apply lr_backward_heaps_write ].
    apply rtc_once. eapply lr_reference_step_at; [ exact He | ].
    apply EctxStep. by eapply WriteScS.
  - (* SC_Cas_Suc *)
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst.
    simpl in Hload, Hstore. change (lr_val_eq m v_cur (LitV lit1)) in Heq.
    destruct v_cur as [litl | ]; [ | contradiction ]. simpl in Heq.
    destruct (m !! l) as [v' | ] eqn:Hm; simplify_eq.
    pose proof (lr_backward_heaps_lookup _ _ _ _ Hheaps Hm) as Hs.
    eapply lr_backward_pack; [ | by apply lr_pools_match_insert | by apply lr_backward_heaps_write ].
    apply rtc_once. eapply lr_reference_step_at; [ exact He | ].
    apply EctxStep. eapply CasSucS; eauto. by eapply lit_eq_dom.
  - (* SC_Cas_Fail *)
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst.
    simpl in Hload. change (lr_val_neq m' v_cur (LitV lit1)) in Hneq.
    destruct v_cur as [litl | ]; [ | contradiction ]. simpl in Hneq.
    pose proof (lr_backward_heaps_lookup _ _ _ _ Hheaps Hload) as Hs.
    eapply lr_backward_pack; [ | by apply lr_pools_match_insert | exact Hheaps ].
    apply rtc_once. eapply lr_reference_step_at; [ exact He | ].
    apply EctxStep. eapply (CasFailS l 0%nat); eauto. by eapply lit_neq_dom.
  - (* SC_Cas_Stuck: the crashed thread matches anything. *)
    apply lr_backward_pack_refl; [ | exact Hheaps ]. by eapply lr_pools_match_insert_r.
  - (* Spawn: the reference forks, appending at the machine's new index. *)
    inversion Hspawn as [K e0 Hc0 Hc1 Hc2]; subst c c' c_new.
    pose proof (lr_pools_match_least_free _ _ _ _ Hpools Hfree Hleast) as ->.
    exists (<[i := fill K (Lit LitPoison)]> threads ++ [e0], sigma). split; [ split | ].
    + simpl. rewrite <- (length_insert threads i (fill K (Lit LitPoison))).
      apply lr_pools_match_snoc; [ by apply lr_pools_match_insert | done ].
    + exact Hheaps.
    + apply rtc_once. eapply lr_reference_step_at_spawn; [ exact He | ].
      apply EctxStep, ForkS.
Qed.

(** * Reachability *)

Lemma lr_forward_steps rc rc' mc :
  lr_forward_configuration_match rc mc ->
  rtc step rc rc' ->
  exists mc', lr_forward_configuration_match rc' mc' /\ rtc lr_machine_step mc mc'.
Proof.
  intros Hmatch Hsteps. revert mc Hmatch.
  induction Hsteps as [ x | x y z Hxy Hyz IH ]; intros mc Hmatch; [ eauto using rtc | ].
  destruct (lr_forward_step _ _ _ Hmatch Hxy) as (mc1 & Hmatch1 & Hsteps1).
  destruct (IH mc1 Hmatch1) as (mc2 & Hmatch2 & Hsteps2). eauto using rtc_trans.
Qed.

Lemma lr_backward_steps rc mc mc' :
  lr_backward_configuration_match rc mc ->
  rtc lr_machine_step mc mc' ->
  exists rc', lr_backward_configuration_match rc' mc' /\ rtc step rc rc'.
Proof.
  intros Hmatch Hsteps. revert rc Hmatch.
  induction Hsteps as [ x | x y z Hxy Hyz IH ]; intros rc Hmatch; [ eauto using rtc | ].
  destruct (lr_backward_step _ _ _ Hmatch Hxy) as (rc1 & Hmatch1 & Hsteps1).
  destruct (IH rc1 Hmatch1) as (rc2 & Hmatch2 & Hsteps2). eauto using rtc_trans.
Qed.

(**
  Reachability agrees between corresponding stable configurations.  A proof
  may pass through the administrative states omitted by
  [lr_stable_configuration_match].
*)
Theorem lambda_rust_reachability_equivalence rc1 mc1 rc2 mc2 :
  lr_stable_configuration_match rc1 mc1 ->
  lr_stable_configuration_match rc2 mc2 ->
  (rtc step rc1 rc2 <->
   rtc lr_machine_step mc1 mc2).
Proof.
  intros Hmatch1 Hmatch2. split; intros Hsteps.
  - destruct (lr_forward_steps _ _ _ (lr_stable_forward _ _ Hmatch1) Hsteps)
      as (mc' & Hmatch' & Hsteps').
    by rewrite <- (lr_forward_stable_unique _ _ _ Hmatch' Hmatch2).
  - destruct (lr_backward_steps _ _ _ (lr_stable_backward _ _ Hmatch1) Hsteps)
      as (rc' & Hmatch' & Hsteps').
    by rewrite <- (lr_backward_stable_unique _ _ _ Hmatch' Hmatch2).
Qed.
