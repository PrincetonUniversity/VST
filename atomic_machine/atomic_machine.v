(** * The atomic machine

    This file defines the interface of a sequential language ([sqlang]) and
    lifts it to a sequentially consistent concurrent machine that only tracks
    events. There is no reader/writer map and no Try/Commit split: a
    sequential step of a thread is one machine step, and so is an atomic
    operation.

    Every step emits events ([am_event]):
    - a sequential step emits its memory events as non-atomic events
      ([NA ev] for a [mem_ev] [ev]);
    - atomic loads and stores emit [SC (SCread l)] and [SC (SCwrite l)],
      a successful CAS emits the read-modify-write event [SC (SCrw l)], and
      a failed one [SC (SCread l)];
    - spawning emits no event.

    Data races are defined on the events, after CASCompCert's predicted
    races: a configuration is racy ([am_race]) if two different threads can
    each take a step from it whose events conflict ([am_conflict]). Events
    on different locations never conflict. On the same location:
    - an allocation conflicts with nothing (see [am_conflicting]);
    - two other non-atomic events conflict as in CASCompCert's
      [FP.conflict] (frees being permission changes), i.e. unless both are
      reads;
    - two SC events never conflict;
    - a non-atomic and an SC event conflict unless both are reads.
    Since every interleaving is a machine execution, a one-step prediction
    is enough: a later conflicting step of a thread is predicted from the
    configuration reached by scheduling that thread first. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import List.
Import ListNotations.

Require Import stdpp.gmap stdpp.relations.

(** ** Memory events of the sequential language *)

Class Location := location : Type.
Global Typeclasses Transparent Location.

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

    (** Terminal states: a thread in a final state with no pending events
        has finished, so being unable to step is not an error. *)
    sqlang_final : sqlang_thrd_st -> Prop;

    (** Value (in)equality for CAS *)
    sqlang_ValEq : Mem -> Val -> Val -> Prop;
    sqlang_ValNEq : Mem -> Val -> Val -> Prop;
  }.
End SeqLang.

(** ** Machine events *)

Section Events.
  Context {Loc : Type}.

  (** (Sequentially consistent) atomic events. *)
  Variant sc_event : Type :=
  | SCread (l : Loc)
  | SCwrite (l : Loc)
  (* for a successful CAS, does a read and a write at the same time.
     Failed CAS emits SCread. *)
  | SCrw (l : Loc).

  (** Events of the machine: the memory events of a sequential step are
      non-atomic ([NA]), those of atomic operations are [SC]. *)
  Variant am_event : Type :=
  | NA (ev : @mem_ev Loc)
  | SC (ev : sc_event).

  Definition mem_ev_loc (ev : @mem_ev Loc) : Loc :=
    match ev with Read l | Write l | Alloc l | Free l => l end.

  Definition sc_ev_loc (ev : sc_event) : Loc :=
    match ev with SCread l | SCwrite l | SCrw l => l end.

  Definition am_ev_loc (e : am_event) : Loc :=
    match e with NA ev => mem_ev_loc ev | SC ev => sc_ev_loc ev end.

  Definition am_atomic (e : am_event) : bool :=
    match e with NA _ => false | SC _ => true end.

  (** Two events conflict if they are on the same location, and
      - Two non-atomic events conflict as in CASCompCert's [FP.conflict].
        "conflicts" with Alloc is a memory safety property and not handled here.
      - Two SC events never conflict.
      - A non-atomic and an SC event conflict unless both are reads. *)
  Definition am_conflicting (e1 e2 : am_event) : bool :=
    match e1, e2 with
    | NA (Alloc _), _ | _, NA (Alloc _) => false
    | NA (Read _), NA (Read _) => false
    | SC _, SC _ => false
    | NA (Read _), SC (SCread _) | SC (SCread _), NA (Read _) => false
    | _, _ => true
    end.

  Definition am_conflict (e1 e2 : am_event) : Prop :=
    am_ev_loc e1 = am_ev_loc e2 /\ am_conflicting e1 e2 = true.

  (** Two event traces conflict if two of their events conflict. *)
  Definition am_conflicts (evs1 evs2 : list am_event) : Prop :=
    exists e1 e2, e1 ∈ evs1 /\ e2 ∈ evs2 /\ am_conflict e1 e2.

  Lemma am_conflict_sym e1 e2 : am_conflict e1 e2 -> am_conflict e2 e1.
  Proof. intros [Hl Hc]. split; first done. by destruct e1 as [[]|[]], e2 as [[]|[]]. Qed.

  Lemma am_conflicts_sym evs1 evs2 : am_conflicts evs1 evs2 -> am_conflicts evs2 evs1.
  Proof.
    intros (e1 & e2 & H1 & H2 & Hc). exists e2, e1.
    split_and!; [done | done | by apply am_conflict_sym].
  Qed.

  (** Two atomic events never conflict. *)
  Lemma am_conflict_not_atomic e1 e2 :
    am_conflict e1 e2 -> am_atomic e1 = false \/ am_atomic e2 = false.
  Proof. intros [_ Hc]. destruct e1 as [[]|[]], e2 as [[]|[]]; naive_solver. Qed.

  (** The location an access reads or writes, and whether it writes it. An
      allocation is not an access. *)
  Definition ev_need_full_loc (e : am_event) : option (Loc * bool) :=
    match e with
    | NA (Read l) | SC (SCread l) => Some (l, false)
    | NA (Write l) | NA (Free l) | SC (SCwrite l) | SC (SCrw l) => Some (l, true)
    | NA (Alloc _) => None
    end.

  (** A conflict is between two accesses of which one writes. *)
  Lemma am_conflict_cases e1 e2 :
    am_conflict e1 e2 ->
    exists l w1 w2, ev_need_full_loc e1 = Some (l, w1) /\ ev_need_full_loc e2 = Some (l, w2) /\
      (w1 = true \/ w2 = true).
  Proof.
    intros [Hl Hc]. destruct e1 as [[]|[]], e2 as [[]|[]]; simpl in *; subst; naive_solver.
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
  | Core_Step c m T c' m'
      (Hstep : sqlang_step c m T c' m') :
      at_step c m (NA <$> T) c' m' None
  | SC_Read c m ly l v K
      (Hext : at_external c (ALoad ly l) K)
      (Hload : load m l ly = Some v) :
      (* FIXME now it emits a list of SCread events, maybe it should be a single
         SCread event that contains a range? *)
      at_step c m ((fun l => SC (SCread l)) <$> layout_to_locs l ly) (K (Some v)) m None
  | SC_Write c m ly l v m' K
      (Hext : at_external c (AStore ly l v) K)
      (Hstore : store m l ly v = Some m') :
      at_step c m ((fun l => SC (SCwrite l)) <$> layout_to_locs l ly) (K None) m' None
  | SC_Cas_Suc c m ly l v_exp v_new v_cur m' K
      (Hext : at_external c (ACAS ly l v_exp v_new) K)
      (Hload : load m l ly = Some v_cur)
      (Heq : ValEq m v_cur v_exp)
      (Hstore : store m l ly v_new = Some m') :
      at_step c m ((fun l => SC (SCrw l)) <$> layout_to_locs l ly)
        (K (Some Vtrue)) m' None
  | SC_Cas_Fail c m ly l v_exp v_new v_cur K
      (Hext : at_external c (ACAS ly l v_exp v_new) K)
      (Hload : load m l ly = Some v_cur)
      (Hneq : ValNEq m v_cur v_exp) :
      at_step c m ((fun l => SC (SCread l)) <$> layout_to_locs l ly)
        (K (Some Vfalse)) m None
  | Spawn c m e_new K
      (Hspawn : at_external c (ASpawn e_new) K) :
      at_step c m [] (K None) m (Some (sqlang_expr_to_thrd_st e_new)).

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
  | AMStep tp m i c evs c' m'
      (Hget : tp !! i = Some c)
      (Hstep : at_step c m evs c' m' None) :
      am_step (AMCfg tp m) i evs (AMCfg (<[i := c']> tp) m')
  | AMStepSpawn tp m i c evs c' m' c_new j
      (Hget : tp !! i = Some c)
      (Hstep : at_step c m evs c' m' (Some c_new))
      (* picks least-unused index for the new thread *)
      (Hfree : tp !! j = None)
      (Hleast : forall k, k < j -> is_Some (tp !! k)) :
      am_step (AMCfg tp m) i evs (AMCfg (<[j := c_new]> (<[i := c']> tp)) m').

  Definition am_step_any (q q' : am_cfg) : Prop := exists i evs, am_step q i evs q'.

  Definition am_steps : relation am_cfg := rtc am_step_any.

  (** ** Races and safety *)

  (** Two different threads can step from [q] with conflicting events. *)
  Definition am_race (q : am_cfg) : Prop :=
    exists i j ci cj evs1 evs2 ci' cj' m1 m2 o1 o2,
      i <> j /\
      am_threads q !! i = Some ci /\ am_threads q !! j = Some cj /\
      at_step ci (am_mem q) evs1 ci' m1 o1 /\
      at_step cj (am_mem q) evs2 cj' m2 o2 /\
      am_conflicts evs1 evs2.

  (** A thread is not stuck if it has finished or can step. *)
  Definition am_not_stuck (c : C) (m : Mem) : Prop :=
    sqlang_final c \/ exists evs c' m' oc, at_step c m evs c' m' oc.

  Definition am_safe (q : am_cfg) : Prop :=
    forall q', am_steps q q' ->
      ~ am_race q' /\
      forall i c, am_threads q' !! i = Some c -> am_not_stuck c (am_mem q').

  (** A thread that can step in isolation can step in every pool. *)
  Lemma at_step_in_pool tp m i c evs c' m' oc :
    tp !! i = Some c -> at_step c m evs c' m' oc ->
    exists q', am_step (AMCfg tp m) i evs q'.
  Proof.
    intros Hi Hstep. destruct oc as [c_new|].
    - destruct (am_least_free tp) as (j & Hj & Hleast).
      eexists. by eapply AMStepSpawn.
    - eexists. by eapply AMStep.
  Qed.

  (** The events of a sequential step are non-atomic; those of an external
      calls are atomic.
      TODO relax this, allow for non-atomic events (or even mixed?) *)
  Lemma at_step_events c m evs c' m' oc :
    at_step c m evs c' m' oc ->
    (exists T, sqlang_step c m T c' m' /\ evs = NA <$> T) \/
    Forall (fun e => am_atomic e = true) evs.
  Proof.
    destruct 1; [left; by eexists | right..].
    - apply Forall_fmap, Forall_true. done.
    - apply Forall_fmap, Forall_true. done.
    - apply Forall_fmap, Forall_true. done.
    - apply Forall_fmap, Forall_true. done.
    - constructor.
  Qed.

  (** two event traces conflict if two of the events coming from each trace
    conflict. *)
  Lemma am_conflicts_seq c1 c2 m evs1 evs2 c1' c2' m1 m2 o1 o2 :
    at_step c1 m evs1 c1' m1 o1 -> at_step c2 m evs2 c2' m2 o2 ->
    am_conflicts evs1 evs2 ->
    (exists T, sqlang_step c1 m T c1' m1 /\ evs1 = NA <$> T) \/
    (exists T, sqlang_step c2 m T c2' m2 /\ evs2 = NA <$> T).
  Proof.
    intros H1 H2 (e1 & e2 & He1 & He2 & Hc).
    destruct (at_step_events _ _ _ _ _ _ H1) as [?|Ha1]; first by left.
    destruct (at_step_events _ _ _ _ _ _ H2) as [?|Ha2]; first by right.
    exfalso. rewrite Forall_forall in Ha1. rewrite Forall_forall in Ha2.
    destruct (am_conflict_not_atomic _ _ Hc) as [Hn|Hn].
    - rewrite Ha1 in Hn; [discriminate | done].
    - rewrite Ha2 in Hn; [discriminate | done].
  Qed.

End AtomicMachine.
