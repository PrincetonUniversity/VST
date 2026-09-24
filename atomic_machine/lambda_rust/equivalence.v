(**
  Statement of the equivalence between the lambda-Rust reference semantics
  and its atomic-machine implementation.

  The two systems expose different administrative states: the atomic machine
  reserves and commits events, while the reference semantics uses [Na2Ord].
  We therefore compare reflexive-transitive reachability between stable
  configurations, where neither representation has an access in flight.

  The atomic machine does not yet provide a thread-spawn rule, so the
  reference transition below is restricted to steps that spawn no threads.
*)

From Stdlib Require Import List Lia.
From stdpp Require Import gmap list.

Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.event_semantics.
Require Import VST.atomic_machine.lambda_rust.reference.

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

Set Primitive Projections.

Record lr_machine_configuration : Type := {
  lr_machine_threads : lr_tpool;
  lr_machine_mem : lr_mem;
  lr_machine_rw : lr_rw_map;
}.

Definition lr_machine_step
    (c1 c2 : lr_machine_configuration) : Prop :=
  @at_step loc val _ _ lr_mem lr_layout lr_memory lr_language
    (lr_machine_threads c1) (lr_machine_mem c1) (lr_machine_rw c1)
    (lr_machine_threads c2) (lr_machine_mem c2) (lr_machine_rw c2).

(** The non-spawning fragment of the reference transition relation. *)

Inductive lr_reference_step : configuration -> configuration -> Prop :=
| LRReferenceStep t1 e1 t2 sigma1 e2 sigma2 :
    prim_step e1 sigma1 e2 sigma2 [] ->
    lr_reference_step
      (t1 ++ e1 :: t2, sigma1)
      (t1 ++ e2 :: t2, sigma2).

(** Reflexive-transitive closure, used to hide administrative steps. *)

Inductive lr_steps {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| LRStepsRefl x : lr_steps R x x
| LRStepsStep x y z : R x y -> lr_steps R y z -> lr_steps R x z.

Lemma lr_steps_one {A : Type} (R : A -> A -> Prop) x y :
  R x y -> lr_steps R x y.
Proof. eauto using lr_steps. Qed.

Lemma lr_steps_two {A : Type} (R : A -> A -> Prop) x y z :
  R x y -> R y z -> lr_steps R x z.
Proof. eauto using lr_steps. Qed.

Lemma lr_steps_trans {A : Type} (R : A -> A -> Prop) x y z :
  lr_steps R x y -> lr_steps R y z -> lr_steps R x z.
Proof. induction 1; eauto using lr_steps. Qed.

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

(** A reference step is a primitive step of the thread at some index. *)

Lemma lr_reference_step_at threads sigma i e1 e2 sigma2 :
  threads !! i = Some e1 -> prim_step e1 sigma e2 sigma2 [] ->
  lr_reference_step (threads, sigma) (<[i := e2]> threads, sigma2).
Proof.
  intros Hi Hstep.
  assert (Hlen : length (take i threads) = i)
    by (apply length_take_le, Nat.lt_le_incl, lookup_lt_is_Some_1; eauto).
  pose proof (take_drop_middle threads i e1 Hi) as Hsplit.
  assert (<[i := e2]> threads = take i threads ++ e2 :: drop (S i) threads) as ->.
  { rewrite <- Hsplit at 1. unfold thread_pool. by rewrite insert_app_r_alt, Hlen, Nat.sub_diag by lia. }
  rewrite <- Hsplit at 1. by constructor.
Qed.

Lemma lr_reference_step_inv threads sigma rc' :
  lr_reference_step (threads, sigma) rc' ->
  exists i e1 e2 sigma2,
    threads !! i = Some e1 /\ prim_step e1 sigma e2 sigma2 [] /\
    rc' = (<[i := e2]> threads, sigma2).
Proof.
  intros Hstep. inversion Hstep; subst. exists (length t1), e1, e2, sigma2.
  unfold thread_pool. rewrite insert_app_r_alt, Nat.sub_diag by lia.
  eauto using list_lookup_middle.
Qed.

Lemma lr_reference_two_steps threads sigma i e1 e2 e3 sigma2 sigma3 :
  threads !! i = Some e1 ->
  prim_step e1 sigma e2 sigma2 [] ->
  prim_step e2 sigma2 e3 sigma3 [] ->
  lr_steps lr_reference_step (threads, sigma) (<[i := e3]> threads, sigma3).
Proof.
  intros Hi H12 H23. rewrite <- (list_insert_insert_eq _ i e3 e2).
  eapply lr_steps_two; eapply lr_reference_step_at; eauto.
  apply list_lookup_insert_eq, lookup_lt_is_Some_1. eauto.
Qed.

(** * Syntactic infrastructure

    Ported from the upstream lambda-Rust [lang.v]: evaluation contexts
    decompose uniquely around a head redex. *)

Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
Proof. destruct e; simpl; try case_decide; intros; by simplify_eq. Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros v1 v2 H%(f_equal to_val). rewrite !to_of_val in H. by simplify_eq. Qed.

Lemma fill_app K1 K2 e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof. revert e. induction K1; simpl; auto. Qed.

Lemma fill_item_not_val Ki e : to_val (fill_item Ki e) = None.
Proof. by destruct Ki. Qed.

Lemma fill_not_val K e : to_val e = None -> to_val (fill K e) = None.
Proof. revert e. induction K; simpl; eauto using fill_item_not_val. Qed.

Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
  to_val e1 = None -> to_val e2 = None ->
  map of_val vl1 ++ e1 :: el1 = map of_val vl2 ++ e2 :: el2 ->
  vl1 = vl2 /\ e1 = e2 /\ el1 = el2.
Proof.
  revert vl2. induction vl1 as [ | v1 vl1 IH ]; intros [ | v2 vl2 ] He1 He2 H; injection H as H1 H2;
    [ by subst | by rewrite H1, to_of_val in He1 | by rewrite <- H1, to_of_val in He2 | ].
  apply (inj of_val) in H1 as ->. by destruct (IH vl2 He1 He2 H2) as (-> & -> & ->).
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None -> to_val e2 = None ->
  fill_item Ki1 e1 = fill_item Ki2 e2 -> Ki1 = Ki2 /\ e1 = e2.
Proof.
  intros He1 He2 H. destruct Ki1, Ki2; simplify_eq/=; auto;
    repeat match goal with H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H end.
  match goal with H : map of_val _ ++ _ :: _ = map of_val _ ++ _ :: _ |- _ =>
    by destruct (list_expr_val_eq_inv _ _ _ _ _ _ He1 He2 H) as (-> & -> & ->) end.
Qed.

(** An expression has redex shape if it is not itself a strict context
    around a non-value.  Head redexes and the administrative [Na2Ord]
    accesses have this shape, so their evaluation context is unique. *)

Definition redex_shape (e : expr) : Prop :=
  forall Ki e', e = fill_item Ki e' -> is_Some (to_val e').

Lemma fill_redex_shape_inv K e e1 :
  redex_shape e1 -> to_val e = None -> fill K e = e1 -> K = [] /\ e = e1.
Proof.
  revert e. induction K as [ | Ki K IH ]; intros e Hshape He Hfill; simpl in Hfill; [ auto | ].
  destruct (IH _ Hshape (fill_item_not_val Ki e) Hfill) as (_ & Heq).
  destruct (Hshape Ki e (eq_sym Heq)) as [v Hv]. by rewrite He in Hv.
Qed.

Lemma fill_redex_unique K1 K2 e1 e2 :
  redex_shape e1 -> redex_shape e2 -> to_val e1 = None -> to_val e2 = None ->
  fill K1 e1 = fill K2 e2 -> K1 = K2 /\ e1 = e2.
Proof.
  intros Hs1 Hs2 Hv1 Hv2. revert K2.
  induction K1 as [ | Ki K1 IH ] using rev_ind; intros K2 Hfill.
  - by destruct (fill_redex_shape_inv K2 e2 e1 Hs1 Hv2 (eq_sym Hfill)) as (-> & ->).
  - destruct K2 as [ | Kj K2 _ ] using rev_ind.
    + destruct (fill_redex_shape_inv (K1 ++ [Ki]) e1 e2 Hs2 Hv1 Hfill) as (Hnil & _).
      by destruct K1.
    + rewrite !fill_app in Hfill. simpl in Hfill.
      destruct (fill_item_no_val_inj Ki Kj (fill K1 e1) (fill K2 e2)
                  (fill_not_val K1 e1 Hv1) (fill_not_val K2 e2 Hv2) Hfill) as (-> & Hfill').
      by destruct (IH K2 Hfill') as (-> & ->).
Qed.

Lemma head_step_not_val e1 sigma1 e2 sigma2 spawned :
  head_step e1 sigma1 e2 sigma2 spawned -> to_val e1 = None.
Proof. by destruct 1. Qed.

Lemma head_step_redex_shape e1 sigma1 e2 sigma2 spawned :
  head_step e1 sigma1 e2 sigma2 spawned -> redex_shape e1.
Proof.
  intros Hstep Ki e' Heq.
  destruct Hstep; destruct Ki; simplify_eq/=; rewrite ?to_of_val; eauto.
  - by case_decide.
  - by apply Forall_app, proj2, Forall_cons in H as [? _].
Qed.

Lemma na2_read_redex_shape l : redex_shape (Read Na2Ord (Lit (LitLoc l))).
Proof. intros Ki e' Heq. destruct Ki; simplify_eq/=; eauto. Qed.

Lemma na2_write_redex_shape l e v : to_val e = Some v -> redex_shape (Write Na2Ord (Lit (LitLoc l)) e).
Proof. intros He Ki e' Heq. destruct Ki; simplify_eq/=; eauto. Qed.

(** * Freedom from administrative accesses

    [Na2Ord] is an administrative state of the reference semantics, but it
    is also syntax, and a program that mentions it directly can decrement a
    reader count it never incremented.  Such a program is stuck on the
    machine (which has no rule for [Na2Ord]) yet may reach a "stable"
    reference configuration, so the correspondence excludes it. *)

Fixpoint na2_free (e : expr) : bool :=
  match e with
  | Var _ | Lit _ => true
  | Rec _ _ e | Alloc e | Fork e => na2_free e
  | BinOp _ e1 e2 | Free e1 e2 => na2_free e1 && na2_free e2
  | App e el | Case e el => na2_free e && forallb na2_free el
  | Read o e => match o with Na2Ord => false | _ => na2_free e end
  | Write o e1 e2 => match o with Na2Ord => false | _ => na2_free e1 && na2_free e2 end
  | CAS e0 e1 e2 => na2_free e0 && na2_free e1 && na2_free e2
  end.

Ltac na2_split :=
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  | |- (_ && _) = true => apply andb_true_iff; split
  end.

Lemma na2_free_fill_item_inv Ki e :
  na2_free (fill_item Ki e) = true -> na2_free e = true.
Proof. destruct Ki; simpl; try destruct o; rewrite ?forallb_app; simpl; intros; na2_split; auto; discriminate. Qed.

Lemma na2_free_fill_item Ki e e' :
  na2_free (fill_item Ki e) = true -> na2_free e' = true -> na2_free (fill_item Ki e') = true.
Proof. destruct Ki; simpl; try destruct o; rewrite ?forallb_app; simpl; intros; na2_split; auto; discriminate. Qed.

Lemma na2_free_fill_inv K e :
  na2_free (fill K e) = true -> na2_free e = true.
Proof. revert e. induction K; simpl; eauto using na2_free_fill_item_inv. Qed.

Lemma na2_free_fill K e e' :
  na2_free (fill K e) = true -> na2_free e' = true -> na2_free (fill K e') = true.
Proof.
  revert e e'. induction K as [ | Ki K IH ]; simpl; intros e e' H He'; [ done | ].
  eapply IH; [ exact H | ]. eapply na2_free_fill_item; eauto using na2_free_fill_inv.
Qed.

Lemma na2_free_subst x es e :
  na2_free es = true -> na2_free e = true -> na2_free (subst x es e) = true.
Proof.
  intros Hes. revert e. fix IH 1. intros e He.
  destruct e; simpl in *; repeat case_match; na2_split; auto;
    match goal with el : list expr |- _ => induction el; simpl in *; na2_split; auto end.
Qed.

Lemma na2_free_subst' mx es e :
  na2_free es = true -> na2_free e = true -> na2_free (subst' mx es e) = true.
Proof. destruct mx; simpl; auto using na2_free_subst. Qed.

Lemma na2_free_subst_l xl esl e e' :
  forallb na2_free esl = true -> na2_free e = true ->
  subst_l xl esl e = Some e' -> na2_free e' = true.
Proof.
  revert esl e'. induction xl as [ | mx xl IH ]; intros [ | es esl ] e' Hesl He Hsubst;
    simpl in *; na2_split; simplify_eq; [ done | ].
  destruct (subst_l xl esl e) eqn:Hsub; simplify_eq/=. eauto using na2_free_subst'.
Qed.

Lemma stuck_term_redex_shape : redex_shape stuck_term.
Proof.
  intros Ki e' Heq. destruct Ki; unfold stuck_term in Heq; simplify_eq/=; eauto. by destruct vl.
Qed.

Lemma crashed_no_step K sigma1 e2 sigma2 spawned :
  ~ prim_step (fill K stuck_term) sigma1 e2 sigma2 spawned.
Proof.
  intros Hstep. inversion Hstep as [K' e1 ? ? ? ? Hhead HK]; subst.
  destruct (fill_redex_unique K' K e1 stuck_term
              (head_step_redex_shape _ _ _ _ _ Hhead) stuck_term_redex_shape
              (head_step_not_val _ _ _ _ _ Hhead) eq_refl HK) as (_ & ->).
  inversion Hhead.
Qed.

(** * Heap ranges

    Allocation and deallocation act on a contiguous range of locations.
    [init_mem]/[free_mem] and the machine's event lists are all described
    through [loc_in_range]. *)

Definition loc_in_range (l : loc) (n : nat) (l' : loc) : Prop :=
  l'.1 = l.1 /\ (l.2 <= l'.2 < l.2 + Z.of_nat n)%Z.

Instance loc_in_range_dec l n l' : Decision (loc_in_range l n l').
Proof. unfold loc_in_range. apply _. Defined.

(** Shared proof of the two range lookups; [step] rewrites the head
    insertion/deletion at the looked-up location. *)

Ltac range_lookup_base :=
  case_decide; [ | done ]; unfold loc_in_range in *; simpl in *; lia.

Ltac range_lookup_step IH l l' :=
  destruct (decide (l = l')) as [-> | Hne];
  [ first [ rewrite lookup_insert_eq | rewrite lookup_delete_eq ];
    case_decide; [ done | ]; unfold loc_in_range in *; simpl in *; lia
  | first [ rewrite lookup_insert_ne | rewrite lookup_delete_ne ]; [ | done ]; rewrite IH;
    destruct l as [b o], l' as [b' o']; unfold loc_in_range, shift_loc in *; simpl in *;
    do 2 case_decide; try done; exfalso; [ lia | apply Hne; f_equal; lia ] ].

Lemma lookup_init_mem {A : Type} (x : A) (l : loc) (n : nat) (sigma : gmap loc A) (l' : loc) :
  init_mem x l n sigma !! l' =
    if decide (loc_in_range l n l') then Some x else sigma !! l'.
Proof.
  revert l. induction n as [ | n IH ]; intros l; simpl; [ range_lookup_base | range_lookup_step IH l l' ].
Qed.

Lemma lookup_free_mem {A : Type} (l : loc) (n : nat) (sigma : gmap loc A) (l' : loc) :
  free_mem l n sigma !! l' =
    if decide (loc_in_range l n l') then None else sigma !! l'.
Proof.
  revert l. induction n as [ | n IH ]; intros l; simpl; [ range_lookup_base | range_lookup_step IH l l' ].
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

(** Reserving and immediately finishing a single non-atomic access
    returns the reader/writer map to its starting point. *)

Lemma lr_rsv_fin_read (mu : lr_rw_map) l :
  mu !! l = Some (Rst 0) ->
  exists mu', rsv [lr_read_event l] mu = Some mu' /\ fin [lr_read_event l] mu' = Some mu.
Proof.
  intros Hl. unfold lr_rw_map, rw_map in *. eexists. split.
  - unfold rsv. simpl. unfold rsv_Read. by setoid_rewrite Hl.
  - unfold fin. simpl. unfold fin_Read, rw_map. rewrite lookup_insert_eq. simpl.
    by rewrite insert_insert_eq, insert_id.
Qed.

Lemma lr_rsv_fin_write (mu : lr_rw_map) l :
  mu !! l = Some (Rst 0) ->
  exists mu', rsv [lr_write_event l] mu = Some mu' /\ fin [lr_write_event l] mu' = Some mu.
Proof.
  intros Hl. unfold lr_rw_map, rw_map in *. eexists. split.
  - unfold rsv. simpl. unfold rsv_Write. by setoid_rewrite Hl.
  - unfold fin. simpl. unfold fin_Write, rw_map. rewrite lookup_insert_eq. simpl.
    by rewrite insert_insert_eq, insert_id.
Qed.

(** * Correspondence of configurations

    Three relations are used.  The theorem is stated for stable
    configurations: no access in flight, no reserved events, no crashed
    thread, and no syntactic [Na2Ord].  The two directions of the proof use
    two different simulation relations, because the two systems read a
    non-atomic value at different moments: the reference reads at the
    second ([Na2Ord]) step, the machine at [Core_Try].

    - Forward (reference drives): the machine lags behind.  A reference
      thread that has done its first half is matched by the machine thread
      that has not started, and the machine performs [Core_Try] and
      [Core_Commit] together when the reference performs its second half.
      Every machine location is therefore always at [Rst 0].
    - Backward (machine drives): the reference runs ahead.  Whenever the
      machine performs [Core_Try] the reference performs both halves, so
      the reference heap is always at [RSt 0] and the reader/writer map
      is unconstrained.  A crashed machine thread matches anything.

    [Na2Ord] must be excluded from stable configurations: a program that
    writes it directly can decrement a reader count it never incremented
    and thereby reach a reference configuration with [RSt 0] everywhere
    that the machine, which has no rule for [Na2Ord], cannot mirror.
    Similarly, a reference thread that crashed on a racy CAS is
    [fill K stuck_term] forever while the machine's [StuckState] never
    returns to [Running], so crashed threads are excluded too. *)

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
  lr_stable_pools_match threads (lr_machine_threads mc) /\
  lr_stable_heaps_match sigma (lr_machine_mem mc) (lr_machine_rw mc).

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

(** The type aliases ([lr_mem], [lr_tpool], ...) make stdpp's [rewrite]
    fail to recognise lookups elaborated at the alias; unfolding them
    first is the reliable fix. *)

Ltac lr_unfold :=
  unfold lr_stable_configuration_match, lr_forward_configuration_match,
    lr_backward_configuration_match,
    lr_stable_heaps_match, lr_forward_heaps_match, lr_backward_heaps_match,
    lr_stable_pools_match, lr_pools_match,
    lr_mem, lr_rw_map, rw_map, lr_tpool, tpool, thread_pool, state in *.

(** Pointwise reasoning about a heap relation: specialize at the location
    under consideration, then split on the machine heap. *)

Ltac lr_heaps_at Hheaps l :=
  specialize (Hheaps l); lr_unfold; destruct (_ !! l) eqn:?; naive_solver.

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

Lemma na2_free_read_na2 K l : na2_free (fill K (Read Na2Ord (Lit (LitLoc l)))) = false.
Proof. apply not_true_is_false. intros H%na2_free_fill_inv. discriminate. Qed.

Lemma na2_free_write_na2 K l e : na2_free (fill K (Write Na2Ord (Lit (LitLoc l)) e)) = false.
Proof. apply not_true_is_false. intros H%na2_free_fill_inv. discriminate. Qed.

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
  intros (Hpools' & Hheaps') (Hpools & Hheaps). lr_unfold. simpl in *.
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
  intros (Hpools' & Hheaps') (Hpools & Hheaps). lr_unfold. simpl in *. f_equal.
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
  intros Hheaps. specialize (Hheaps l). lr_unfold. destruct (m !! l).
  - destruct Hheaps as ((st & ->) & _). by split; eauto.
  - destruct Hheaps as (-> & _). by split; intros [].
Qed.

Lemma lr_forward_heaps_relock sigma m mu l st st' v :
  lr_forward_heaps_match sigma m mu -> sigma !! l = Some (st, v) ->
  lr_forward_heaps_match (<[l := (st', v)]> sigma) m mu.
Proof.
  intros Hheaps Hs l'. specialize (Hheaps l'). lr_unfold.
  destruct (decide (l = l')) as [<- | ]; [ rewrite lookup_insert_eq | by rewrite lookup_insert_ne ].
  destruct (m !! l); naive_solver.
Qed.

Lemma lr_forward_heaps_write sigma m mu l st v' v :
  lr_forward_heaps_match sigma m mu -> m !! l = Some v' -> na2_free (of_val v) = true ->
  lr_forward_heaps_match (<[l := (st, v)]> sigma) (<[l := v]> m) mu.
Proof.
  intros Hheaps Hm Hna2 l'. specialize (Hheaps l'). lr_unfold.
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
  intros Hheaps l'. specialize (Hheaps l'). lr_unfold. rewrite !lookup_init_mem.
  case_decide; naive_solver.
Qed.

Lemma lr_forward_heaps_free sigma m mu l n :
  lr_forward_heaps_match sigma m mu ->
  lr_forward_heaps_match (free_mem l n sigma) (free_mem l n m) (free_mem l n mu).
Proof.
  intros Hheaps l'. specialize (Hheaps l'). lr_unfold. rewrite !lookup_free_mem.
  case_decide; naive_solver.
Qed.

Lemma lr_forward_heaps_dom sigma m mu :
  lr_forward_heaps_match sigma m mu ->
  forall l, sigma !! l = None -> m !! l = None.
Proof. intros Hheaps l Hs. by apply (lr_forward_heaps_none _ _ _ _ Hheaps Hs). Qed.

(** [bin_op_eval] only consults the heap through [lit_eq]'s dangling-pointer
    cases, and those only observe the domain. *)

Lemma lit_eq_dom {A B : Type} (sigma : gmap loc A) (m : gmap loc B) lit1 lit2 :
  (forall l, sigma !! l = None -> m !! l = None) ->
  lit_eq sigma lit1 lit2 -> lit_eq m lit1 lit2.
Proof. destruct 2; eauto using lit_eq. Qed.

Lemma lit_neq_dom {A B : Type} (sigma : gmap loc A) (m : gmap loc B) lit1 lit2 :
  lit_neq sigma lit1 lit2 -> lit_neq m lit1 lit2.
Proof. destruct 1; constructor; auto. Qed.

Lemma bin_op_eval_dom {A B : Type} (sigma : gmap loc A) (m : gmap loc B) op lit1 lit2 lit' :
  (forall l, sigma !! l = None -> m !! l = None) ->
  bin_op_eval sigma op lit1 lit2 lit' -> bin_op_eval m op lit1 lit2 lit'.
Proof. destruct 2; constructor; eauto using lit_eq_dom, lit_neq_dom. Qed.

(** ** Machine steps on configurations *)

Lemma lr_machine_try tp m mu i c T c' m' mu' :
  tp !! i = Some (lr_running c []) ->
  lr_step c m T c' m' ->
  rsv T mu = Some mu' ->
  lr_machine_step
    {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |}
    {| lr_machine_threads := <[i := lr_running c' T]> tp;
       lr_machine_mem := m'; lr_machine_rw := mu' |}.
Proof. intros. eapply Core_Try; eassumption. Qed.

Lemma lr_machine_commit tp m mu i c T mu' :
  tp !! i = Some (lr_running c T) ->
  T <> [] ->
  fin T mu = Some mu' ->
  lr_machine_step
    {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |}
    {| lr_machine_threads := <[i := lr_running c []]> tp;
       lr_machine_mem := m; lr_machine_rw := mu' |}.
Proof. intros. eapply Core_Commit; eassumption. Qed.

Lemma lr_machine_pure_steps tp m mu i c c' m' :
  tp !! i = Some (lr_running c []) ->
  lr_step c m [] c' m' ->
  lr_steps lr_machine_step
    {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |}
    {| lr_machine_threads := <[i := lr_running c' []]> tp;
       lr_machine_mem := m'; lr_machine_rw := mu |}.
Proof. intros. apply lr_steps_one. eapply lr_machine_try; eauto. Qed.

Lemma lr_machine_try_commit_steps tp m mu i c T c' m' mu' mu'' :
  tp !! i = Some (lr_running c []) ->
  lr_step c m T c' m' ->
  T <> [] ->
  rsv T mu = Some mu' ->
  fin T mu' = Some mu'' ->
  lr_steps lr_machine_step
    {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |}
    {| lr_machine_threads := <[i := lr_running c' []]> tp;
       lr_machine_mem := m'; lr_machine_rw := mu'' |}.
Proof.
  intros Hget Hstep HT Hrsv Hfin. unfold lr_tpool, tpool in *.
  rewrite <- (insert_insert_eq tp i (lr_running c' []) (lr_running c' T)).
  eapply lr_steps_two; [ eapply lr_machine_try; eauto | ].
  eapply lr_machine_commit; eauto. unfold lr_tpool, tpool. apply lookup_insert_eq.
Qed.

Lemma lr_machine_sc_read tp m mu i c l v K :
  tp !! i = Some (lr_running c []) ->
  lr_external c (ALoad tt l) K ->
  mu !! l <> Some Wst ->
  m !! l = Some v ->
  lr_machine_step
    {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |}
    {| lr_machine_threads := <[i := lr_running (K (Some v)) []]> tp;
       lr_machine_mem := m; lr_machine_rw := mu |}.
Proof. intros. eapply SC_Read; eauto. by repeat constructor. Qed.

Lemma lr_machine_sc_write tp m mu i c l v v' K :
  tp !! i = Some (lr_running c []) ->
  lr_external c (AStore tt l v) K ->
  mu !! l = Some (Rst 0) ->
  m !! l = Some v' ->
  lr_machine_step
    {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |}
    {| lr_machine_threads := <[i := lr_running (K None) []]> tp;
       lr_machine_mem := <[l := v]> m; lr_machine_rw := mu |}.
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
  lr_machine_step
    {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |}
    {| lr_machine_threads :=
         <[i := lr_running (K (Some (LitV (lit_of_bool true)))) []]> tp;
       lr_machine_mem := <[l := LitV lit_new]> m; lr_machine_rw := mu |}.
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
  lr_machine_step
    {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |}
    {| lr_machine_threads :=
         <[i := lr_running (K (Some (LitV (lit_of_bool false)))) []]> tp;
       lr_machine_mem := m; lr_machine_rw := mu |}.
Proof.
  intros Hget Hext Hmu Hm Hneq.
  refine (SC_Cas_Fail tp m mu i c tt l (LitV lit_exp) (LitV lit_new) (LitV lit_cur) K
            Hget Hext _ Hm Hneq). by repeat constructor.
Qed.

(** * Forward simulation: reference steps are matched by machine steps *)

(** Packaging of a forward step: the machine steps come first so that
    they determine the target configuration before the matching goals. *)

Lemma lr_forward_pack threads tp m mu i e2 sigma2 tp2 m2 mu2 :
  lr_steps lr_machine_step
    {| lr_machine_threads := tp; lr_machine_mem := m; lr_machine_rw := mu |}
    {| lr_machine_threads := tp2; lr_machine_mem := m2; lr_machine_rw := mu2 |} ->
  lr_pools_match lr_forward_thread_match (<[i := e2]> threads) tp2 ->
  lr_forward_heaps_match sigma2 m2 mu2 ->
  exists mc',
    lr_forward_configuration_match (<[i := e2]> threads, sigma2) mc' /\
    lr_steps lr_machine_step
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
  lr_reference_step rc rc' ->
  exists mc', lr_forward_configuration_match rc' mc' /\ lr_steps lr_machine_step mc mc'.
Proof.
  destruct rc as (threads, sigma). destruct mc as [tp m mu].
  intros (Hpools & Hheaps) Hstep. simpl in Hpools, Hheaps.
  apply lr_reference_step_inv in Hstep as (i & e1 & e2 & sigma2 & Hi & Hprim & ->).
  destruct (lr_pools_match_lookup_l _ _ _ _ _ Hpools Hi) as (c & Hc & Hthread).
  assert (Hsome : is_Some (threads !! i)) by (by eexists).
  pose proof (lr_forward_heaps_dom _ _ _ Hheaps) as Hdom.
  inversion Hthread; subst.
  - (* [LRForwardSame] *)
    inversion Hprim as [K e1' ? e2' ? ? Hhead HK]; subst.
    inversion Hhead; subst.
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
        [ apply lr_steps_one; eapply lr_machine_sc_read; [ exact Hc | by apply LREctxExternal, LRReadScE | | exact Hm ]
        | by eapply lr_forward_pools_same; eauto | exact Hheaps ].
      intros Hw. setoid_rewrite Hmu in Hw. discriminate.
    + (* ReadNa1: the machine waits for the second half. *)
      eapply lr_forward_pack; [ apply LRStepsRefl | | by eapply lr_forward_heaps_relock ].
      eapply lr_pools_match_keep; [ exact Hpools | exact Hc | ]. by apply LRForwardReadNa2.
    + (* ReadNa2: excluded by [na2_free]. *)
      by rewrite na2_free_read_na2 in H.
    + (* WriteSc *)
      destruct (lr_forward_heaps_lookup _ _ _ _ _ _ Hheaps H1) as (Hm & Hmu & _).
      assert (Hna2 : na2_free (Write ScOrd (Lit (LitLoc l)) e) = true) by eauto using na2_free_fill_inv.
      simpl in Hna2. rewrite <- (of_to_val e v H0) in Hna2.
      eapply lr_forward_pack;
        [ apply lr_steps_one; eapply lr_machine_sc_write; [ exact Hc | by apply LREctxExternal, LRWriteScE | exact Hmu | exact Hm ]
        | by eapply lr_forward_pools_same; eauto | by eapply lr_forward_heaps_write ].
    + (* WriteNa1: the machine waits for the second half. *)
      eapply lr_forward_pack; [ apply LRStepsRefl | | by eapply lr_forward_heaps_relock ].
      eapply lr_pools_match_keep; [ exact Hpools | exact Hc | ]. by eapply LRForwardWriteNa2.
    + (* WriteNa2: excluded by [na2_free]. *)
      by rewrite na2_free_write_na2 in H.
    + (* CasFail *)
      destruct (lr_forward_heaps_lookup _ _ _ _ _ _ Hheaps H2) as (Hm & Hmu & _).
      eapply lr_forward_pack;
        [ apply lr_steps_one; eapply lr_machine_cas_fail;
            [ exact Hc | by apply LREctxExternal, LRCasE | | exact Hm | by eapply lit_neq_dom ]
        | by eapply lr_forward_pools_same; eauto | exact Hheaps ].
      intros Hw. setoid_rewrite Hmu in Hw. discriminate.
    + (* CasSuc *)
      destruct (lr_forward_heaps_lookup _ _ _ _ _ _ Hheaps H2) as (Hm & Hmu & _).
      eapply lr_forward_pack;
        [ apply lr_steps_one; eapply lr_machine_cas_suc;
            [ exact Hc | by apply LREctxExternal, LRCasE | exact Hmu | exact Hm | by eapply lit_eq_dom ]
        | by eapply lr_forward_pools_same; eauto | by eapply lr_forward_heaps_write ].
    + (* CasStuck: the reference thread crashes; the machine, which sees
         [Rst 0], would have succeeded, but crashed threads are outside
         the stable correspondence anyway. *)
      eapply lr_forward_pack; [ apply LRStepsRefl | | exact Hheaps ].
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
  - (* [LRForwardReadNa2]: the second half; the machine now tries and commits. *)
    inversion Hprim as [K' e1' ? e2' ? ? Hhead HK]; subst.
    destruct (fill_redex_unique K' K e1' (Read Na2Ord (Lit (LitLoc l)))
                (head_step_redex_shape _ _ _ _ _ Hhead) (na2_read_redex_shape l)
                (head_step_not_val _ _ _ _ _ Hhead) eq_refl HK) as (-> & ->).
    inversion Hhead; subst.
    match goal with Hs : sigma !! l = Some (RSt (S _), _) |- _ =>
      destruct (lr_forward_heaps_lookup _ _ _ _ _ _ Hheaps Hs) as (Hm & Hmu & Hv) end.
    destruct (lr_rsv_fin_read mu l Hmu) as (mu' & Hrsv & Hfin).
    eapply lr_forward_pack; [ | by eapply lr_forward_pools_same; eauto | by eapply lr_forward_heaps_relock ].
    eapply lr_machine_try_commit_steps with (T := [lr_read_event l]);
      [ exact Hc | | done | exact Hrsv | exact Hfin ].
    apply LREctxStep. by apply LRReadNaS.
  - (* [LRForwardWriteNa2] *)
    inversion Hprim as [K' e1' ? e2' ? ? Hhead HK]; subst.
    destruct (fill_redex_unique K' K e1' (Write Na2Ord (Lit (LitLoc l)) e)
                (head_step_redex_shape _ _ _ _ _ Hhead) (na2_write_redex_shape l e v H)
                (head_step_not_val _ _ _ _ _ Hhead) eq_refl HK) as (-> & ->).
    inversion Hhead; subst.
    match goal with Hs : sigma !! l = Some (WSt, _) |- _ =>
      destruct (lr_forward_heaps_lookup _ _ _ _ _ _ Hheaps Hs) as (Hm & Hmu & _) end.
    destruct (lr_rsv_fin_write mu l Hmu) as (mu' & Hrsv & Hfin).
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
  intros Hheaps. specialize (Hheaps l). lr_unfold. destruct (m !! l); rewrite Hheaps.
  - by split; eauto.
  - by split; intros [].
Qed.

Lemma lr_backward_heaps_write sigma m l v :
  lr_backward_heaps_match sigma m ->
  lr_backward_heaps_match (<[l := (RSt 0, v)]> sigma) (<[l := v]> m).
Proof.
  intros Hheaps l'. specialize (Hheaps l'). lr_unfold.
  destruct (decide (l = l')) as [<- | ]; [ by rewrite !lookup_insert_eq | by rewrite !lookup_insert_ne ].
Qed.

Lemma lr_backward_heaps_alloc sigma m l n :
  lr_backward_heaps_match sigma m ->
  lr_backward_heaps_match
    (init_mem (RSt 0, LitV LitPoison) l n sigma)
    (init_mem (LitV LitPoison) l n m).
Proof.
  intros Hheaps l'. specialize (Hheaps l'). lr_unfold. rewrite !lookup_init_mem.
  case_decide; naive_solver.
Qed.

Lemma lr_backward_heaps_free sigma m l n :
  lr_backward_heaps_match sigma m ->
  lr_backward_heaps_match (free_mem l n sigma) (free_mem l n m).
Proof.
  intros Hheaps l'. specialize (Hheaps l'). lr_unfold. rewrite !lookup_free_mem.
  case_decide; naive_solver.
Qed.

Lemma lr_backward_pack threads sigma tp' m' mu' i e2 sigma2 :
  lr_steps lr_reference_step (threads, sigma) (<[i := e2]> threads, sigma2) ->
  lr_pools_match lr_backward_thread_match (<[i := e2]> threads) tp' ->
  lr_backward_heaps_match sigma2 m' ->
  exists rc',
    lr_backward_configuration_match rc'
      {| lr_machine_threads := tp'; lr_machine_mem := m'; lr_machine_rw := mu' |} /\
    lr_steps lr_reference_step (threads, sigma) rc'.
Proof. intros. eexists. split; [ | eassumption ]. by split. Qed.

Lemma lr_backward_pack_refl threads sigma tp' m' mu' :
  lr_pools_match lr_backward_thread_match threads tp' ->
  lr_backward_heaps_match sigma m' ->
  exists rc',
    lr_backward_configuration_match rc'
      {| lr_machine_threads := tp'; lr_machine_mem := m'; lr_machine_rw := mu' |} /\
    lr_steps lr_reference_step (threads, sigma) rc'.
Proof. intros. exists (threads, sigma). split; [ by split | constructor ]. Qed.

(** The machine thread at [i] is running the reference thread at [i]. *)

Ltac lr_backward_thread Hpools Hget He :=
  let e := fresh "e" in let Hec := fresh "Hec" in
  destruct (lr_pools_match_lookup_r _ _ _ _ _ Hpools Hget) as (e & He & Hec);
  simpl in Hec; subst e.

Lemma lr_backward_step rc mc mc' :
  lr_backward_configuration_match rc mc ->
  lr_machine_step mc mc' ->
  exists rc', lr_backward_configuration_match rc' mc' /\ lr_steps lr_reference_step rc rc'.
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
      apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
      apply EctxStep, BinOpS. by eapply bin_op_eval_dom.
    + exact Hheaps.
    + (* Beta *)
      apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ]. apply EctxStep. by eapply BetaS.
    + exact Hheaps.
    + (* ReadNa: the reference performs both halves at once. *)
      pose proof (lr_backward_heaps_lookup _ _ _ _ Hheaps H) as Hs.
      eapply lr_reference_two_steps; [ exact He | | ].
      * apply EctxStep. by apply ReadNa1S.
      * apply EctxStep. apply ReadNa2S. apply lookup_insert_eq.
    + pose proof (lr_backward_heaps_lookup _ _ _ _ Hheaps H) as Hs.
      lr_unfold. by rewrite insert_insert_eq, insert_id.
    + (* WriteNa: both halves. *)
      pose proof (lr_backward_heaps_lookup _ _ _ _ Hheaps H0) as Hs.
      eapply lr_reference_two_steps; [ exact He | | ].
      * apply EctxStep. by eapply WriteNa1S.
      * apply EctxStep. eapply WriteNa2S; [ done | apply lookup_insert_eq ].
    + lr_unfold. rewrite insert_insert_eq. by apply lr_backward_heaps_write.
    + (* Alloc *)
      apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
      apply EctxStep, AllocS; [ done | intros z; apply Hdom, H0 ].
    + by apply lr_backward_heaps_alloc.
    + (* Free *)
      apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
      apply EctxStep, FreeS; [ done | ].
      intros z. rewrite (lr_backward_heaps_is_Some _ _ _ Hheaps). apply H0.
    + by apply lr_backward_heaps_free.
    + (* Case *)
      apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ]. apply EctxStep. by eapply CaseS.
    + exact Hheaps.
  - (* Core_Commit: nothing to do on the reference side. *)
    apply lr_backward_pack_refl; [ | exact Hheaps ]. by eapply lr_pools_match_insert_r.
  - (* SC_Read *)
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst. simpl in Hload.
    pose proof (lr_backward_heaps_lookup _ _ _ _ Hheaps Hload) as Hs.
    eapply lr_backward_pack; [ | by apply lr_pools_match_insert | exact Hheaps ].
    apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
    apply EctxStep. by apply (ReadScS l 0%nat).
  - (* SC_Write *)
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst. simpl in Hstore.
    destruct (m !! l) as [v' | ] eqn:Hm; simplify_eq.
    pose proof (lr_backward_heaps_lookup _ _ _ _ Hheaps Hm) as Hs.
    eapply lr_backward_pack; [ | by apply lr_pools_match_insert | by apply lr_backward_heaps_write ].
    apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
    apply EctxStep. by eapply WriteScS.
  - (* SC_Cas_Suc *)
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst.
    simpl in Hload, Hstore. change (lr_val_eq m v_cur (LitV lit1)) in Heq.
    destruct v_cur as [litl | ]; [ | contradiction ]. simpl in Heq.
    destruct (m !! l) as [v' | ] eqn:Hm; simplify_eq.
    pose proof (lr_backward_heaps_lookup _ _ _ _ Hheaps Hm) as Hs.
    eapply lr_backward_pack; [ | by apply lr_pools_match_insert | by apply lr_backward_heaps_write ].
    apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
    apply EctxStep. eapply CasSucS; eauto. by eapply lit_eq_dom.
  - (* SC_Cas_Fail *)
    inversion Hext as [K0 e0 op k Hhe]; subst. inversion Hhe; subst.
    simpl in Hload. change (lr_val_neq m' v_cur (LitV lit1)) in Hneq.
    destruct v_cur as [litl | ]; [ | contradiction ]. simpl in Hneq.
    pose proof (lr_backward_heaps_lookup _ _ _ _ Hheaps Hload) as Hs.
    eapply lr_backward_pack; [ | by apply lr_pools_match_insert | exact Hheaps ].
    apply lr_steps_one. eapply lr_reference_step_at; [ exact He | ].
    apply EctxStep. eapply (CasFailS l 0%nat); eauto. by eapply lit_neq_dom.
  - (* SC_Cas_Stuck: the crashed thread matches anything. *)
    apply lr_backward_pack_refl; [ | exact Hheaps ]. by eapply lr_pools_match_insert_r.
Qed.

(** * Reachability *)

Lemma lr_forward_steps rc rc' mc :
  lr_forward_configuration_match rc mc ->
  lr_steps lr_reference_step rc rc' ->
  exists mc', lr_forward_configuration_match rc' mc' /\ lr_steps lr_machine_step mc mc'.
Proof.
  intros Hmatch Hsteps. revert mc Hmatch.
  induction Hsteps as [ x | x y z Hxy Hyz IH ]; intros mc Hmatch; [ eauto using lr_steps | ].
  destruct (lr_forward_step _ _ _ Hmatch Hxy) as (mc1 & Hmatch1 & Hsteps1).
  destruct (IH mc1 Hmatch1) as (mc2 & Hmatch2 & Hsteps2). eauto using lr_steps_trans.
Qed.

Lemma lr_backward_steps rc mc mc' :
  lr_backward_configuration_match rc mc ->
  lr_steps lr_machine_step mc mc' ->
  exists rc', lr_backward_configuration_match rc' mc' /\ lr_steps lr_reference_step rc rc'.
Proof.
  intros Hmatch Hsteps. revert rc Hmatch.
  induction Hsteps as [ x | x y z Hxy Hyz IH ]; intros rc Hmatch; [ eauto using lr_steps | ].
  destruct (lr_backward_step _ _ _ Hmatch Hxy) as (rc1 & Hmatch1 & Hsteps1).
  destruct (IH rc1 Hmatch1) as (rc2 & Hmatch2 & Hsteps2). eauto using lr_steps_trans.
Qed.

(**
  Reachability agrees between corresponding stable configurations.  A proof
  may pass through the administrative states omitted by
  [lr_stable_configuration_match].
*)
Theorem lambda_rust_reachability_equivalence rc1 mc1 rc2 mc2 :
  lr_stable_configuration_match rc1 mc1 ->
  lr_stable_configuration_match rc2 mc2 ->
  (lr_steps lr_reference_step rc1 rc2 <->
   lr_steps lr_machine_step mc1 mc2).
Proof.
  intros Hmatch1 Hmatch2. split; intros Hsteps.
  - destruct (lr_forward_steps _ _ _ (lr_stable_forward _ _ Hmatch1) Hsteps)
      as (mc' & Hmatch' & Hsteps').
    by rewrite <- (lr_forward_stable_unique _ _ _ Hmatch' Hmatch2).
  - destruct (lr_backward_steps _ _ _ (lr_stable_backward _ _ Hmatch1) Hsteps)
      as (rc' & Hmatch' & Hsteps').
    by rewrite <- (lr_backward_stable_unique _ _ _ Hmatch' Hmatch2).
Qed.
