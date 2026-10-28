(** The atomic machine instantiated with lambda-Rust, and the
    infrastructure shared by the proofs relating it to the reference
    semantics: matching of thread pools, reference steps at an index,
    machine steps on configurations, and stably matched configurations. *)

From Stdlib Require Import List Lia.
From stdpp Require Import gmap list.

Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.event_semantics.
Require Export VST.atomic_machine.lambda_rust.reference.
Require Export VST.atomic_machine.lambda_rust.lang_facts.

Import ListNotations.

Set Default Proof Using "Type".

(** The atomic machine specialized to lambda-Rust. *)

Definition lr_rw_map : Type := @rw_map loc _ _.

Definition lr_tstate : Type :=
  @tstate loc val _ _ lr_mem lr_layout lr_memory lr_language.

Definition lr_tpool : Type :=
  @tpool loc val _ _ lr_mem lr_layout lr_memory lr_language.

Definition lr_mem_ev : Type := @mem_ev loc.

(** Explicitly instantiated constructors: elaborating [Running] inside a
    record literal leaves its [sqlang] instance undetermined. *)

Definition lr_running (e : expr) (T : list lr_mem_ev) : lr_tstate :=
  @Running loc val _ _ lr_mem lr_layout lr_memory lr_language e T.

Definition lr_stuck : lr_tstate :=
  @StuckState loc val _ _ lr_mem lr_layout lr_memory lr_language.

Notation lr_machine_configuration :=
  (@am_configuration loc val _ _ lr_mem lr_layout lr_memory lr_language).
(** * Thread pools

    The reference pool is a list, the machine pool a finite map.  All
    index juggling is confined to the lemmas of this section. *)

Definition lr_pools_match (R : expr -> lr_tstate -> Prop)
    (threads : list expr) (tp : lr_tpool) : Prop :=
  forall i,
    match threads !! i, tp !! i with
    | Some e, Some c => R e c
    | None, None => True
    | _, _ => False
    end.

Lemma lr_pools_match_lookup_l R threads tp i e :
  lr_pools_match R threads tp -> threads !! i = Some e ->
  exists c, tp !! i = Some c /\ R e c.
Proof. intros H He. specialize (H i). rewrite He in H. destruct (tp !! i); naive_solver. Qed.

Lemma lr_pools_match_lookup_r R threads tp i c :
  lr_pools_match R threads tp -> tp !! i = Some c ->
  exists e, threads !! i = Some e /\ R e c.
Proof. intros H Hc. specialize (H i). rewrite Hc in H. destruct (threads !! i); naive_solver. Qed.

Lemma lr_pools_match_insert R threads tp i e c :
  lr_pools_match R threads tp -> is_Some (threads !! i) -> R e c ->
  lr_pools_match R (<[i := e]> threads) (<[i := c]> tp).
Proof.
  intros H Hi HR j. unfold lr_tpool, tpool in *. destruct (decide (i = j)) as [<- | Hne].
  - rewrite list_lookup_insert_eq, lookup_insert_eq; [ exact HR | by apply lookup_lt_is_Some_1 ].
  - rewrite list_lookup_insert_ne, lookup_insert_ne; auto. apply H.
Qed.

Lemma lr_pools_match_insert_r R threads tp i e c :
  lr_pools_match R threads tp -> threads !! i = Some e -> R e c ->
  lr_pools_match R threads (<[i := c]> tp).
Proof.
  intros H He HR j. unfold lr_tpool, tpool in *. destruct (decide (i = j)) as [<- | Hne].
  - by rewrite lookup_insert_eq, He.
  - rewrite lookup_insert_ne; auto. apply H.
Qed.

Lemma lr_pools_match_keep R threads tp i e c :
  lr_pools_match R threads tp -> tp !! i = Some c -> R e c ->
  lr_pools_match R (<[i := e]> threads) tp.
Proof.
  intros H Hc HR j. destruct (decide (i = j)) as [<- | Hne].
  - destruct (lr_pools_match_lookup_r _ _ _ _ _ H Hc) as (e0 & He0 & _).
    rewrite list_lookup_insert_eq, Hc; [ exact HR | by eapply lookup_lt_is_Some_1 ].
  - rewrite list_lookup_insert_ne; auto. apply H.
Qed.

Lemma lr_pools_match_impl R R' threads tp :
  (forall e c, R e c -> R' e c) ->
  lr_pools_match R threads tp -> lr_pools_match R' threads tp.
Proof. intros Himpl H i. specialize (H i). destruct (threads !! i), (tp !! i); auto. Qed.

(** Thread creation: the machine's least unused index is the position at
    which the reference appends. *)

Lemma lr_pools_match_is_Some R threads tp (k : nat) :
  lr_pools_match R threads tp -> is_Some (tp !! k) <-> (k < length threads)%nat.
Proof.
  intros H. specialize (H k). rewrite <- lookup_lt_is_Some.
  destruct (threads !! k), (tp !! k); naive_solver.
Qed.

Lemma lr_pools_match_least_free R threads tp (j : nat) :
  lr_pools_match R threads tp ->
  tp !! j = None -> (forall k, (k < j)%nat -> is_Some (tp !! k)) ->
  j = length threads.
Proof.
  intros H Hj Hleast.
  assert (~ (j < length threads)%nat).
  { intros Hlt. apply (lr_pools_match_is_Some _ _ _ j H) in Hlt. rewrite Hj in Hlt. by destruct Hlt. }
  destruct (decide (length threads < j)%nat) as [Hlt | ]; [ | lia ].
  apply Hleast, (lr_pools_match_is_Some _ _ _ _ H) in Hlt. lia.
Qed.

Lemma lr_pools_match_snoc R threads tp e c :
  lr_pools_match R threads tp -> R e c ->
  lr_pools_match R (threads ++ [e]) (<[length threads := c]> tp).
Proof.
  intros H HR k. unfold lr_tpool, tpool in *.
  destruct (decide (k = length threads)) as [-> | Hne].
  - rewrite lookup_insert_eq, lookup_app_r, Nat.sub_diag by lia. exact HR.
  - rewrite lookup_insert_ne by done. specialize (H k).
    destruct (decide (k < length threads)%nat).
    + by rewrite lookup_app_l.
    + rewrite lookup_app_r by lia. rewrite list_lookup_singleton.
      destruct (k - length threads)%nat eqn:?; [ lia | ].
      destruct (threads !! k) eqn:Hk; [ apply lookup_lt_Some in Hk; lia | ].
      by destruct (tp !! k).
Qed.

(** A reference step is a primitive step of the thread at some index,
    with the spawned threads appended. *)

Lemma lr_reference_step_at_spawn threads sigma i e1 e2 sigma2 spawned :
  threads !! i = Some e1 -> prim_step e1 sigma e2 sigma2 spawned ->
  step (threads, sigma) (<[i := e2]> threads ++ spawned, sigma2).
Proof.
  intros Hi Hstep.
  assert (Hlen : length (take i threads) = i)
    by (apply length_take_le, Nat.lt_le_incl, lookup_lt_is_Some_1; eauto).
  pose proof (take_drop_middle threads i e1 Hi) as Hsplit.
  assert (<[i := e2]> threads = take i threads ++ e2 :: drop (S i) threads) as ->.
  { rewrite <- Hsplit at 1. unfold thread_pool. by rewrite insert_app_r_alt, Hlen, Nat.sub_diag by lia. }
  rewrite <- Hsplit at 1. by constructor.
Qed.

Lemma lr_reference_step_at threads sigma i e1 e2 sigma2 :
  threads !! i = Some e1 -> prim_step e1 sigma e2 sigma2 [] ->
  step (threads, sigma) (<[i := e2]> threads, sigma2).
Proof.
  intros Hi Hstep. rewrite <- (app_nil_r (<[i := e2]> threads)).
  by eapply lr_reference_step_at_spawn.
Qed.

Lemma lr_reference_step_inv threads sigma rc' :
  step (threads, sigma) rc' ->
  exists i e1 e2 sigma2 spawned,
    threads !! i = Some e1 /\ prim_step e1 sigma e2 sigma2 spawned /\
    rc' = (<[i := e2]> threads ++ spawned, sigma2).
Proof.
  intros Hstep. inversion Hstep; subst. exists (length t1), e1, e2, sigma2, spawned.
  unfold thread_pool. rewrite insert_app_r_alt, Nat.sub_diag by lia.
  eauto using list_lookup_middle.
Qed.
(** Reserving and finishing the machine's allocation/deallocation events.
    [setoid_rewrite] rather than [rewrite]: the lookups elaborate at
    [lr_rw_map] and [gmap], which [rewrite] treats as distinct. *)

Lemma lr_rsv_alloc_events (mu : lr_rw_map) l n :
  (forall z, mu !! (l +ₗ z)%L = None) ->
  rsv (lr_alloc_events l n) mu = Some (init_mem (Rst 0) l n mu).
Proof.
  revert l. induction n as [ | n IH ]; intros l Hnone; [ done | ].
  unfold lr_alloc_events, rsv in *. simpl. rewrite IH.
  2: { intros z. rewrite shift_loc_assoc. apply Hnone. }
  simpl. unfold rsv_Alloc. setoid_rewrite lookup_init_mem. case_decide as Hin.
  { destruct l. unfold loc_in_range, shift_loc in Hin. simpl in Hin. lia. }
  pose proof (Hnone 0%Z) as H0. rewrite shift_loc_0 in H0. by setoid_rewrite H0.
Qed.

Lemma lr_fin_alloc_events (mu : lr_rw_map) l n :
  fin (lr_alloc_events l n) mu = Some mu.
Proof.
  revert l. induction n as [ | n IH ]; intros l; [ done | ].
  unfold lr_alloc_events, fin in *. simpl. by rewrite IH.
Qed.

Lemma lr_rsv_free_events (mu : lr_rw_map) l n :
  rsv (lr_free_events l n) mu = Some mu.
Proof.
  revert l. induction n as [ | n IH ]; intros l; [ done | ].
  unfold lr_free_events, rsv in *. simpl. by rewrite IH.
Qed.

Lemma lr_fin_free_events (mu : lr_rw_map) l n :
  (forall z, (0 <= z < Z.of_nat n)%Z -> is_Some (mu !! (l +ₗ z)%L)) ->
  fin (lr_free_events l n) mu = Some (free_mem l n mu).
Proof.
  revert l. induction n as [ | n IH ]; intros l Hsome; [ done | ].
  unfold lr_free_events, fin in *. simpl. rewrite IH.
  2: { intros z Hz. rewrite shift_loc_assoc. apply Hsome. lia. }
  simpl. unfold fin_Free. setoid_rewrite lookup_free_mem. case_decide as Hin.
  { destruct l. unfold loc_in_range, shift_loc in Hin. simpl in Hin. lia. }
  destruct (Hsome 0%Z ltac:(lia)) as [st H0]. rewrite shift_loc_0 in H0. by setoid_rewrite H0.
Qed.

Lemma lr_alloc_events_nonempty l n : (0 < n)%nat -> lr_alloc_events l n <> [].
Proof. destruct n; [ lia | discriminate ]. Qed.

Lemma lr_free_events_nonempty l n : (0 < n)%nat -> lr_free_events l n <> [].
Proof. destruct n; [ lia | discriminate ]. Qed.

(** * Stable configurations

    Corresponding configurations with no access in flight, no reserved
    events, no crashed thread, and no syntactic [Na2Ord].  All relations
    between the two semantics agree on stable configurations, so they are
    the starting points of the simulations.

    [Na2Ord] must be excluded: a program that writes it directly can
    decrement a reader count it never incremented, which the machine,
    having no rule for [Na2Ord], cannot mirror.  A reference thread that
    crashed on a racy CAS is [fill K stuck_term] forever while the
    machine's [StuckState] never returns to [Running], so crashed threads
    are excluded too. *)

Definition lr_crashed (e : expr) : Prop :=
  exists K, e = fill K stuck_term.

Inductive lr_stable_thread_match : expr -> lr_tstate -> Prop :=
| LRStableRunning e :
    na2_free e = true ->
    ~ lr_crashed e ->
    lr_stable_thread_match e (lr_running e []).

Definition lr_stable_pools_match : list expr -> lr_tpool -> Prop :=
  lr_pools_match lr_stable_thread_match.

Definition lr_stable_heaps_match
    (sigma : state) (m : lr_mem) (mu : lr_rw_map) : Prop :=
  forall l,
    match m !! l with
    | Some v =>
        sigma !! l = Some (RSt 0, v) /\
        mu !! l = Some (Rst 0) /\
        na2_free (of_val v) = true (** TODO: discharge *)
    | None => sigma !! l = None /\ mu !! l = None
    end.

Definition lr_stable_configuration_match
    (rc : configuration) (mc : lr_machine_configuration) : Prop :=
  let '(threads, sigma) := rc in
  lr_stable_pools_match threads (am_threads mc) /\
  lr_stable_heaps_match sigma (am_mem mc) (am_rw mc).

(** The type aliases ([lr_mem], [lr_tpool], ...) make stdpp's [rewrite]
    fail to recognise lookups elaborated at the alias; unfolding them
    first is the reliable fix. *)

Ltac lr_unfold :=
  unfold lr_stable_configuration_match, lr_stable_heaps_match,
    lr_stable_pools_match, lr_pools_match,
    lr_tpool, tpool, thread_pool, state, lr_tstate, lr_mem, lr_rw_map, rw_map in *.

(** ** Machine steps on configurations *)

Lemma lr_machine_try tp m mu i c T c' m' mu' :
  tp !! i = Some (lr_running c []) ->
  lr_step c m T c' m' ->
  rsv T mu = Some mu' ->
  am_step
    {| am_threads := tp; am_mem := m; am_rw := mu |}
    {| am_threads := <[i := lr_running c' T]> tp;
       am_mem := m'; am_rw := mu' |}.
Proof. intros. eapply Core_Try; eassumption. Qed.

Lemma lr_machine_commit tp m mu i c T mu' :
  tp !! i = Some (lr_running c T) ->
  T <> [] ->
  fin T mu = Some mu' ->
  am_step
    {| am_threads := tp; am_mem := m; am_rw := mu |}
    {| am_threads := <[i := lr_running c []]> tp;
       am_mem := m; am_rw := mu' |}.
Proof. intros. eapply Core_Commit; eassumption. Qed.

Lemma lr_machine_pure_steps tp m mu i c c' m' :
  tp !! i = Some (lr_running c []) ->
  lr_step c m [] c' m' ->
  rtc am_step
    {| am_threads := tp; am_mem := m; am_rw := mu |}
    {| am_threads := <[i := lr_running c' []]> tp;
       am_mem := m'; am_rw := mu |}.
Proof. intros. apply rtc_once. eapply lr_machine_try; eauto. Qed.

Lemma lr_machine_try_commit_steps tp m mu i c T c' m' mu' mu'' :
  tp !! i = Some (lr_running c []) ->
  lr_step c m T c' m' ->
  T <> [] ->
  rsv T mu = Some mu' ->
  fin T mu' = Some mu'' ->
  rtc am_step
    {| am_threads := tp; am_mem := m; am_rw := mu |}
    {| am_threads := <[i := lr_running c' []]> tp;
       am_mem := m'; am_rw := mu'' |}.
Proof.
  intros Hget Hstep HT Hrsv Hfin. unfold lr_tpool, tpool in *.
  rewrite <- (insert_insert_eq tp i (lr_running c' []) (lr_running c' T)).
  eapply rtc_l; [ eapply lr_machine_try; eauto | apply rtc_once ].
  eapply lr_machine_commit; eauto. unfold lr_tpool, tpool. apply lookup_insert_eq.
Qed.

Lemma lr_machine_sc_read tp m mu i c l v K :
  tp !! i = Some (lr_running c []) ->
  lr_external c (ALoad tt l) K ->
  mu !! l <> Some Wst ->
  m !! l = Some v ->
  am_step
    {| am_threads := tp; am_mem := m; am_rw := mu |}
    {| am_threads := <[i := lr_running (K (Some v)) []]> tp;
       am_mem := m; am_rw := mu |}.
Proof. intros. eapply SC_Read; eauto. by repeat constructor. Qed.

Lemma lr_machine_sc_write tp m mu i c l v v' K :
  tp !! i = Some (lr_running c []) ->
  lr_external c (AStore tt l v) K ->
  mu !! l = Some (Rst 0) ->
  m !! l = Some v' ->
  am_step
    {| am_threads := tp; am_mem := m; am_rw := mu |}
    {| am_threads := <[i := lr_running (K None) []]> tp;
       am_mem := <[l := v]> m; am_rw := mu |}.
Proof.
  intros ? ? Hmu Hm. eapply SC_Write; eauto; [ by repeat constructor | ].
  simpl. lr_unfold. by rewrite Hm.
Qed.

Lemma lr_machine_cas_suc tp m mu i c l lit_exp lit_new lit_cur K :
  tp !! i = Some (lr_running c []) ->
  lr_external c (ACAS tt l (LitV lit_exp) (LitV lit_new)) K ->
  mu !! l = Some (Rst 0) ->
  m !! l = Some (LitV lit_cur) ->
  lit_eq m lit_exp lit_cur ->
  am_step
    {| am_threads := tp; am_mem := m; am_rw := mu |}
    {| am_threads :=
         <[i := lr_running (K (Some (LitV (lit_of_bool true)))) []]> tp;
       am_mem := <[l := LitV lit_new]> m; am_rw := mu |}.
Proof.
  intros Hget Hext Hmu Hm Heq.
  refine (SC_Cas_Suc tp m mu i c tt l (LitV lit_exp) (LitV lit_new) (LitV lit_cur) _ K
            Hget Hext _ Hm Heq _); [ by repeat constructor | ].
  simpl. lr_unfold. by rewrite Hm.
Qed.

Lemma lr_machine_cas_fail tp m mu i c l lit_exp lit_new lit_cur K :
  tp !! i = Some (lr_running c []) ->
  lr_external c (ACAS tt l (LitV lit_exp) (LitV lit_new)) K ->
  mu !! l <> Some Wst ->
  m !! l = Some (LitV lit_cur) ->
  lit_neq m lit_exp lit_cur ->
  am_step
    {| am_threads := tp; am_mem := m; am_rw := mu |}
    {| am_threads :=
         <[i := lr_running (K (Some (LitV (lit_of_bool false)))) []]> tp;
       am_mem := m; am_rw := mu |}.
Proof.
  intros Hget Hext Hmu Hm Hneq.
  refine (SC_Cas_Fail tp m mu i c tt l (LitV lit_exp) (LitV lit_new) (LitV lit_cur) K
            Hget Hext _ Hm Hneq). by repeat constructor.
Qed.

Lemma lr_machine_spawn tp m mu i K e j :
  tp !! i = Some (lr_running (fill K (Fork e)) []) ->
  tp !! j = None -> (forall k, (k < j)%nat -> is_Some (tp !! k)) ->
  am_step
    {| am_threads := tp; am_mem := m; am_rw := mu |}
    {| am_threads :=
         <[j := lr_running e []]> (<[i := lr_running (fill K (Lit LitPoison)) []]> tp);
       am_mem := m; am_rw := mu |}.
Proof. intros. eapply Spawn; eauto. constructor. Qed.

