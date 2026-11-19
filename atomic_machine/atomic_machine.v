(** * The atomic machine

    This file defines the interface of a sequential language ([sqlang]) and
    lifts it to a sequentially consistent concurrent language with atomic read,
    write, CAS and fork. The concurrent language tracks memory events, and can
    potentially be racy. [race] is a predicate on program states defined on the
    potential events, not an explicit state, and a racy state does not get stuck
    in the concurrent language. Race freedom is restored by the program
    logic: a proof of [EXWP e Q] for some postcondition [Q] implies the
    execution of [e] is safe, i.e. it does not get stuck or reach a racy state.
     *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import List.
Import ListNotations.

Require Import stdpp.gmap stdpp.relations.


Class Location := location : Type.
Global Typeclasses Transparent Location.


(** ** Memory events of the sequential language *)
Section MemEvents.
  Context {Loc : Location}.

  Variant mem_ev : Type :=
  | Read (l : Loc)
  | Write (l : Loc)
  | Alloc (l : Loc)
  | Free (l : Loc).
End MemEvents.

Section Memory.
  Class Memory {Loc Val : Type} {LocEqDec : EqDecision Loc} {LocCountable : Countable Loc} {Mem : Type} {Layout : Type} : Type := {
    load : Mem -> Loc -> Layout -> option Val;
    store : Mem -> Loc -> Layout -> Val -> option Mem;
    layout_to_locs : Loc -> Layout -> list Loc
  }.

End Memory.

Inductive sqlang_state_kind :=
| SqValue | SqStep | SqExternal | SqStuck.

Section SeqLang.

  Context {Loc Val : Type} {LocEqDec : EqDecision Loc} {LocCountable : Countable Loc}
    {Mem Layout : Type} {expr : Type}.

  Local Notation mem_ev := (mem_ev(Loc:=Loc)).

  (* the kind of external functions. Should probably be just a general
     placeholder (maybe only expose a string?) and the supported external calls
     should be defined on a lifted layer that gives semantics to (a subset of
     supported) external calls. *)
  Inductive atomic_op : Type :=
  | ALoad : Layout -> Loc -> atomic_op
  | AStore : Layout -> Loc -> Val -> atomic_op
  | ACAS : Layout -> Loc -> Val (* expected val *) ->
          Val (* new val*) -> atomic_op
  | ASpawn : expr -> atomic_op.

  Class sqlang : Type := {
    (* the shared memory *)
    sqlang_memory :: @Memory Loc Val LocEqDec LocCountable Mem Layout;
    (* thread local state *)
    sqlang_thrd_st : Type;
    (* events emitted by the underlying sequential semantics *)
    sqlang_true_val : Val;
    sqlang_false_val : Val;
    sqlang_step :
      sqlang_thrd_st -> Mem -> list mem_ev -> sqlang_thrd_st -> Mem -> Prop;

    (* thread state that spawning an expression becomes *)
    sqlang_expr_to_thrd_st : expr -> sqlang_thrd_st;

    (* An exposed atomic operation and a continuation that takes its optional
       return value. *)
    sqlang_at_external :
      sqlang_thrd_st -> atomic_op ->
      (option Val -> sqlang_thrd_st) -> Prop;

    (** Returns [Some val] for terminated thread evaluating to [val], [None] for not terminated. *)
    sqlang_is_final : sqlang_thrd_st -> option Val;

    (** Value (in)equality for CAS *)
    sqlang_ValEq : Mem -> Val -> Val -> Prop;
    sqlang_ValNEq : Mem -> Val -> Val -> Prop;

    sqlang_stuck (e : sqlang_thrd_st) (m : Mem) : Prop :=
      sqlang_is_final e = None /\
      ~ (exists T e' m', sqlang_step e m T e' m') /\
      ~ (exists op k, sqlang_at_external e op k);

    sqlang_in_state e m kind : Prop :=
      match kind with
      | SqValue => is_Some (sqlang_is_final e)
      | SqStep => exists T e' m', sqlang_step e m T e' m'
      | SqExternal => exists op k, sqlang_at_external e op k
      | SqStuck => sqlang_stuck e m
      end;

    (** Every configuration is exactly one of: a value, can take a step,
        is at an external call, or is stuck. *)
    sqlang_state_classify e m : exists! kind, sqlang_in_state e m kind;

    (** External operations and continuations are determined by the thread. *)
    sqlang_external_det e op1 k1 op2 k2 :
      sqlang_at_external e op1 k1 -> sqlang_at_external e op2 k2 ->
      op2 = op1 /\ forall ov, k2 ov = k1 ov
  }.
End SeqLang.

Section StateClassification.
  Context `{L : !@sqlang Loc Val LocEqDec LocCountable Mem Layout Expr}.

  Lemma sqlang_state_exclusive e m kind1 kind2 :
    sqlang_in_state e m kind1 -> sqlang_in_state e m kind2 -> kind1 = kind2.
  Proof.
    destruct (sqlang_state_classify e m) as (kind & _ & Hunique).
    intros H1 H2. transitivity kind; [symmetry |]; by apply Hunique.
  Qed.

  Lemma sqlang_step_not_final e m T e' m' :
    sqlang_step e m T e' m' -> sqlang_is_final e = None.
  Proof.
    intros Hstep. destruct (sqlang_is_final e) as [v|] eqn:Hfinal; last done.
    exfalso. enough (SqValue = SqStep) by discriminate.
    eapply (sqlang_state_exclusive e m).
    - by exists v.
    - by exists T, e', m'.
  Qed.

  Lemma sqlang_external_not_final e (m : Mem) op k :
    sqlang_at_external e op k -> sqlang_is_final e = None.
  Proof.
    intros Hext. destruct (sqlang_is_final e) as [v|] eqn:Hfinal; last done.
    exfalso. enough (SqValue = SqExternal) by discriminate.
    eapply (sqlang_state_exclusive e m).
    - by exists v.
    - by exists op, k.
  Qed.

  Lemma sqlang_step_external_disjoint e m T e' m' op k :
    sqlang_step e m T e' m' -> sqlang_at_external e op k -> False.
  Proof.
    intros Hstep Hext. enough (SqStep = SqExternal) by discriminate.
    eapply (sqlang_state_exclusive e m).
    - by exists T, e', m'.
    - by exists op, k.
  Qed.

End StateClassification.

(** ** Machine events *)

Section Events.
  Context {Loc : Type}.

  (** (Sequentially consistent) atomic events. Each event contains the
      entire range of locations accessed by one atomic operation. *)
  Variant sc_event : Type :=
  | SCread (ls : list Loc)
  | SCwrite (ls : list Loc)
  (* for a successful CAS, does a read and a write at the same time.
     Failed CAS emits SCread. *)
  | SCrw (ls : list Loc).

  (** Events of the machine: the memory events of a sequential step are
      non-atomic ([NA]), those of atomic operations are [SC]. *)
  Variant am_event : Type :=
  | NA (ev : @mem_ev Loc)
  | SC (ev : sc_event).

  Definition mem_ev_loc (ev : @mem_ev Loc) : Loc :=
    match ev with Read l | Write l | Alloc l | Free l => l end.

  Definition sc_ev_locs (ev : sc_event) : list Loc :=
    match ev with SCread ls | SCwrite ls | SCrw ls => ls end.

  Definition am_ev_locs (e : am_event) : list Loc :=
    match e with NA ev => [mem_ev_loc ev] | SC ev => sc_ev_locs ev end.

  Definition am_atomic (e : am_event) : bool :=
    match e with NA _ => false | SC _ => true end.

  (** Check whether two event types conflict. There is a separate check for
      filtering events at the same location.

      Two event types conflict if their location ranges overlap, and
      - Two non-atomic events conflict as in CASCompCert's [FP.conflict].
        An Alloc event conflicts with every event except another Alloc.
      - Two SC events never conflict.
      - A non-atomic and an SC event conflict unless both are reads. *)
  Definition am_conflicting (e1 e2 : am_event) : bool :=
    match e1, e2 with
    | NA (Alloc _), NA (Alloc _) => false
    | NA (Read _), NA (Read _) => false
    | SC _, SC _ => false
    | NA (Read _), SC (SCread _) | SC (SCread _), NA (Read _) => false
    | _, _ => true
    end.

  (* Two events conflict if they access the same location and have conflicting
     event types. *)
  Definition am_conflict (e1 e2 : am_event) : Prop :=
    (exists l, l ∈ am_ev_locs e1 /\ l ∈ am_ev_locs e2) /\
      am_conflicting e1 e2 = true.

  (** Two event traces conflict if two of their events conflict. *)
  Definition am_conflicts (evs1 evs2 : list am_event) : Prop :=
    exists e1 e2, e1 ∈ evs1 /\ e2 ∈ evs2 /\ am_conflict e1 e2.

  Lemma am_conflict_sym e1 e2 : am_conflict e1 e2 -> am_conflict e2 e1.
  Proof.
    intros [(l & H1 & H2) Hc]. split; first by exists l.
    by destruct e1 as [[]|[]], e2 as [[]|[]].
  Qed.

  Lemma am_conflicts_sym evs1 evs2 : am_conflicts evs1 evs2 -> am_conflicts evs2 evs1.
  Proof.
    intros (e1 & e2 & H1 & H2 & Hc). exists e2, e1.
    split_and!; [done | done | by apply am_conflict_sym].
  Qed.

  (** Two atomic events never conflict. *)
  Lemma am_conflict_not_atomic e1 e2 :
    am_conflict e1 e2 -> am_atomic e1 = false \/ am_atomic e2 = false.
  Proof. intros [_ Hc]. destruct e1 as [[]|[]], e2 as [[]|[]]; naive_solver. Qed.

  (** The location a non-atomic access reads or writes, and whether it
      writes it. An allocation is not an access. *)
  Definition mem_ev_need_full_loc (e : @mem_ev Loc) : option (Loc * bool) :=
    match e with
    | Read l => Some (l, false)
    | Write l | Free l => Some (l, true)
    | Alloc _ => None
    end.

  (** For each event, the location it accesses and whether it needs full 
      points-to. *)
  Definition ev_access (e : am_event) (l : Loc) (w : bool) : Prop :=
    match e with
    | NA ev => mem_ev_need_full_loc ev = Some (l, w)
    | SC (SCread ls) => l ∈ ls /\ w = false
    | SC (SCwrite ls) | SC (SCrw ls) => l ∈ ls /\ w = true
    end.

  (** Every event at a location either allocates it or accesses it. *)
  Lemma am_event_access_or_alloc e l :
    l ∈ am_ev_locs e -> e = NA (Alloc l) \/ exists w, ev_access e l w.
  Proof.
    destruct e as [[l'|l'|l'|l']|[ls|ls|ls]]; simpl;
      try (intros Hl; apply list_elem_of_singleton in Hl; subst l');
      eauto.
  Qed.

  Lemma am_conflicting_access_write e1 e2 l w1 w2 :
    am_conflicting e1 e2 = true -> ev_access e1 l w1 -> ev_access e2 l w2 ->
    w1 = true \/ w2 = true.
  Proof.
    destruct e1 as [[]|[]], e2 as [[]|[]]; simpl;
      intros Hc H1 H2; naive_solver.
  Qed.

End Events.

Global Arguments am_event : clear implicits.

(** Every finite map over [nat] has a least unused index. *)
Lemma am_least_free {A : Type} (tp : gmap nat A) :
  exists j, tp !! j = None /\ forall k, k < j -> is_Some (tp !! k).
Proof.
  assert (Hdisj : forall N, (exists j, j <= N /\ tp !! j = None /\
                               forall k, k < j -> is_Some (tp !! k)) \/
                        (forall k, k <= N -> is_Some (tp !! k))).
  { induction N as [ | N IH ].
    - destruct (tp !! 0) eqn:H0; [ right | left ].
      + intros k Hk. assert (k = 0) as -> by lia. by rewrite H0.
      + exists 0. split; [ lia | ]. split; [ done | ]. lia.
    - destruct IH as [(j & Hj & Hfree & Hleast) | Hall].
      + left. exists j. split; [ lia | done ].
      + destruct (tp !! S N) eqn:HN; [ right | left ].
        * intros k Hk. destruct (decide (k = S N)) as [-> | ]; [ by rewrite HN | ].
          apply Hall. lia.
        * exists (S N). split; [ lia | ]. split; [ done | ].
          intros k Hk. apply Hall. lia. }
  destruct (Hdisj (fresh (dom tp))) as [(j & _ & Hj) | Hall]; [ by eexists | ].
  exfalso. apply (is_fresh (dom tp)), elem_of_dom, Hall. lia.
Qed.

Section AtomicMachine.

  Context `{L : !@sqlang Loc Val LocEqDec LocCountable Mem Layout expr}.

  Local Notation C := sqlang_thrd_st.
  Local Notation at_external := sqlang_at_external.
  Local Notation Vtrue := sqlang_true_val.
  Local Notation Vfalse := sqlang_false_val.
  Local Notation ValEq := sqlang_ValEq.
  Local Notation ValNEq := sqlang_ValNEq.
  Local Notation event := (am_event Loc).

  (** One step of one thread, with its events and optionally a new thread it spawns. *)
  Inductive at_step : C -> Mem -> list event -> C -> Mem -> option C -> Prop :=
  | Core_Step e m T e' m'
      (Hstep : sqlang_step e m T e' m') :
      at_step e m (NA <$> T) e' m' None
  | SC_Read e m ly l v K
      (Hext : at_external e (ALoad ly l) K)
      (Hload : load m l ly = Some v) :
      at_step e m [SC (SCread (layout_to_locs l ly))] (K (Some v)) m None
  | SC_Write e m ly l v m' K
      (Hext : at_external e (AStore ly l v) K)
      (Hstore : store m l ly v = Some m') :
      at_step e m [SC (SCwrite (layout_to_locs l ly))] (K None) m' None
  | SC_Cas_Suc e m ly l v_exp v_new v_cur m' K
      (Hext : at_external e (ACAS ly l v_exp v_new) K)
      (Hload : load m l ly = Some v_cur)
      (Heq : ValEq m v_cur v_exp)
      (Hstore : store m l ly v_new = Some m') :
      at_step e m [SC (SCrw (layout_to_locs l ly))]
        (K (Some Vtrue)) m' None
  | SC_Cas_Fail e m ly l v_exp v_new v_cur K
      (Hext : at_external e (ACAS ly l v_exp v_new) K)
      (Hload : load m l ly = Some v_cur)
      (Hneq : ValNEq m v_cur v_exp) :
      at_step e m [SC (SCread (layout_to_locs l ly))]
        (K (Some Vfalse)) m None
  | Spawn e m e_new K
      (Hspawn : at_external e (ASpawn e_new) K) :
      at_step e m [] (K None) m (Some (sqlang_expr_to_thrd_st e_new)).

  (** Optional semantic laws for allocation freshness and valid accesses. *)
  Class SqAllocLaws := {
    sq_loc_allocated : Mem -> Loc -> Prop;
    sq_alloc_step {e m evs e' m' o l} :
      at_step e m evs e' m' o -> NA (Alloc l) ∈ evs ->
      ~ sq_loc_allocated m l /\ sq_loc_allocated m' l;
    sq_access_step {e m evs e' m' o ev l w} :
      at_step e m evs e' m' o -> ev ∈ evs -> ev_access ev l w ->
      sq_loc_allocated m l \/ NA (Alloc l) ∈ evs
  }.

  Lemma am_successive_allocations_disjoint `{!SqAllocLaws}
      {e1 e2 m evs1 evs2 e1' e2' m1 m2 o1 o2 l} :
    at_step e1 m evs1 e1' m1 o1 -> at_step e2 m1 evs2 e2' m2 o2 ->
    NA (Alloc l) ∈ evs1 -> NA (Alloc l) ∉ evs2.
  Proof.
    intros Hstep1 Hstep2 Ha1 Ha2.
    destruct (sq_alloc_step Hstep1 Ha1) as [_ Hlive].
    destruct (sq_alloc_step Hstep2 Ha2) as [Hfresh _]. exact (Hfresh Hlive).
  Qed.

  Definition am_tpool := gmap nat C.
  #[projections(primitive)]
  Record am_cfg : Type := AMCfg {
    am_threads : am_tpool;
    am_mem : Mem;
  }.

  (** at_step lifted to thread pool, and we can talk about the thread ID of the
    executing thread. FIXME the spawn rule looks weird; do we need this at all,
    over the Iris step closure? *)
  Inductive am_step : am_cfg -> nat -> list event -> am_cfg -> Prop :=
  | AMStep tp m i e evs e' m'
      (Hget : tp !! i = Some e)
      (Hstep : at_step e m evs e' m' None) :
      am_step (AMCfg tp m) i evs (AMCfg (<[i := e']> tp) m')
  | AMStepSpawn tp m i e evs e' m' e_new j
      (Hget : tp !! i = Some e)
      (Hstep : at_step e m evs e' m' (Some e_new))
      (* picks least-unused index for the new thread *)
      (Hfree : tp !! j = None)
      (Hleast : forall k, k < j -> is_Some (tp !! k)) :
      am_step (AMCfg tp m) i evs (AMCfg (<[j := e_new]> (<[i := e']> tp)) m').

  Definition am_step_any (q q' : am_cfg) : Prop := exists i evs, am_step q i evs q'.

  Definition am_steps : relation am_cfg := rtc am_step_any.

  (** ** Races and safety *)

  Definition am_race (q : am_cfg) : Prop :=
    exists i j ei ej evs1 evs2 ei' ej' m1 m2 o1 o2,
      i <> j /\
      am_threads q !! i = Some ei /\ am_threads q !! j = Some ej /\
      at_step ei (am_mem q) evs1 ei' m1 o1 /\
      at_step ej (am_mem q) evs2 ej' m2 o2 /\
      am_conflicts evs1 evs2.

  (* TODO review the non_stuck condition when there are more external calls *)
  (** A thread is not stuck if it has finished or can step. *)
  Definition am_not_stuck (e : C) (m : Mem) : Prop :=
    is_Some (sqlang_is_final e) \/ exists evs e' m' oc, at_step e m evs e' m' oc.

  Definition am_safe (q : am_cfg) : Prop :=
    forall q', am_steps q q' ->
      ~ am_race q' /\
      forall i e, am_threads q' !! i = Some e -> am_not_stuck e (am_mem q').

  (** A thread that can step in isolation can step in every pool. *)
  Lemma at_step_in_pool tp m i e evs e' m' oc :
    tp !! i = Some e -> at_step e m evs e' m' oc ->
    exists q', am_step (AMCfg tp m) i evs q'.
  Proof.
    intros Hi Hstep. destruct oc as [e_new|].
    - destruct (am_least_free tp) as (j & Hj & Hleast).
      eexists. by eapply AMStepSpawn.
    - eexists. by eapply AMStep.
  Qed.

  (** The events of a sequential step are non-atomic; those of an external
      calls are atomic.
      TODO relax this, allow for non-atomic events (or even mixed?) *)
  Lemma at_step_events e m evs e' m' oc :
    at_step e m evs e' m' oc ->
    (exists T, sqlang_step e m T e' m' /\ evs = NA <$> T) \/
    Forall (fun e => am_atomic e = true) evs.
  Proof.
    destruct 1; [left; by eexists | right..].
    - repeat constructor.
    - repeat constructor.
    - repeat constructor.
    - repeat constructor.
    - constructor.
  Qed.

  (** A predicted data race includes a non-atomic step. **)
  Lemma am_conflicts_seq e1 e2 m evs1 evs2 e1' e2' m1 m2 o1 o2 :
    at_step e1 m evs1 e1' m1 o1 -> at_step e2 m evs2 e2' m2 o2 ->
    am_conflicts evs1 evs2 ->
    (exists T, sqlang_step e1 m T e1' m1 /\ evs1 = NA <$> T) \/
    (exists T, sqlang_step e2 m T e2' m2 /\ evs2 = NA <$> T).
  Proof.
    intros H1 H2 (ev1 & ev2 & Hev1 & Hev2 & Hc).
    destruct (at_step_events _ _ _ _ _ _ H1) as [?|Ha1]; first by left.
    destruct (at_step_events _ _ _ _ _ _ H2) as [?|Ha2]; first by right.
    exfalso. rewrite Forall_forall in Ha1. rewrite Forall_forall in Ha2.
    destruct (am_conflict_not_atomic _ _ Hc) as [Hn|Hn].
    - rewrite Ha1 in Hn; [discriminate | done].
    - rewrite Ha2 in Hn; [discriminate | done].
  Qed.

End AtomicMachine.
