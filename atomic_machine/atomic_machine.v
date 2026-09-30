(** *

    This file implements a generic sequentially consistent concurrent semantics,
    lifting a sequential semantics to a sequentially consistent concurrent
    machine with a lambda-Rust-style reader/writer race detector (the `rw_map`)
    and SC atomic operations.

    A machine configuration is <<(tp, m, μ)>> where [tp] is a thread pool,
    [m] a CompCert memory, and [μ] a reader/writer state map.  A thread
    performs a sequential step in two phases: [Core_Try] runs a single thread
    step and "reserve permissions" by updating the "rw_map" and emits a trace of
    "on-going" memory events. If a thread has on-going events, it can only
    execute [Core_Commit] to finish the memory events, and release the reserve.
    Data-race is modeled by failure to reserve in [μ].

 *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import List.
Import ListNotations.

Require Import stdpp.gmap.

(** ** Reader/writer states

    The state of one memory byte, as in lambda-Rust: [Rst n] means [n]
    threads are between Try and Commit of a step that reads the byte;
    [Wst] means some thread is mid-step on a write to it. *)


Section RWMap.

  Context {Loc : Type}.
  Context {LocEqDec : EqDecision Loc}.
  Context {LocCountable : @Countable Loc _}.

  Inductive rw_state : Type :=
  | Rst (n : nat)
  | Wst.

  Variant mem_ev : Type :=
  | Read (l : Loc)
  | Write (l : Loc)
  | Alloc (l : Loc)
  | Free (l : Loc).

  Definition rw_map := gmap Loc rw_state.

  Implicit Types (μ : rw_map) (oμ : option rw_map) (l : Loc)
    (ev : mem_ev) (evs : list mem_ev).

  Definition initial_rw : rw_map := ∅.

  Definition rsv_Alloc μ l : option rw_map :=
    match μ !! l with
    | None => Some $ <[l := Rst 0]> μ
    | _ => None
    end.

  (* can't free right now because a subsequent fin_Read needs the location to be define *)
  Definition rsv_Free μ : option rw_map :=
    mret μ.

  Definition rsv_Write μ l : option rw_map :=
    st ← μ !! l;
    match st with
    | Rst O => Some $ <[l := Wst]> μ
    | _ => None
    end.

  Definition rsv_Read μ l : option rw_map :=
    st ← μ !! l;
    match st with
    | Rst n => Some $ <[l := Rst (S n)]> μ
    | _ => None
    end.

  Definition fin_Alloc μ : option rw_map := mret μ.

  Definition fin_Free μ l : option rw_map :=
    match μ !! l with
    | Some _ => Some $ delete l μ
    | _ => None
    end.

  Definition fin_Write μ l : option rw_map :=
    st ← μ !! l;
    match st with
    | Wst => Some $ <[l := Rst O]> μ
    | _ => None
    end.

  Definition fin_Read μ l : option rw_map :=
    st ← μ !! l;
    match st with
    | Rst (S n) => Some $ <[l := Rst n]> μ
    | _ => None
    end.

  Lemma rsv_Write_fin_Write μ l :
    (μ' ← rsv_Write μ l;
    fin_Write μ' l) = Some μ.
  Proof. Admitted.

  Lemma rsv_Read_fin_Read μ l :
    (μ' ← rsv_Read μ l;
    fin_Read μ' l) = Some μ.
  Proof. Admitted.

  Definition rsv_ev ev oμ : option rw_map :=
    μ ← oμ;
    match ev with
    | Read l => rsv_Read μ l
    | Write l => rsv_Write μ l
    | Alloc l => rsv_Alloc μ l
    | Free l => rsv_Free μ
    end.

  Definition fin_ev ev oμ : option rw_map :=
    μ ← oμ;
    match ev with
    | Read l => fin_Read μ l
    | Write l => fin_Write μ l
    | Alloc _ => fin_Alloc μ
    | Free l => fin_Free μ l
    end.

  (* for memory events, "reserve permission" by updating rw_map *)
  Definition rsv evs μ : option rw_map :=
    foldr rsv_ev (Some μ) evs.

  (* some memory events release permission after completion. *)
  Definition fin evs μ : option rw_map :=
    foldr fin_ev (Some μ) evs.

End RWMap.


Section Memory.
  Class Memory {Loc Val : Type} {LocEqDec : EqDecision Loc} {LocCountable : Countable Loc} {Mem : Type} {Layout : Type} : Type := {
    load : Mem -> Loc -> Layout -> option Val;
    store : Mem -> Loc -> Layout -> Val -> option Mem;
    layout_to_locs : Loc -> Layout -> list Loc
  }.

End Memory.

Section AtomicMachine.

  Context `{mem_inst: !@Memory Loc Val LocEqDec LocCountable Mem Layout}.

  Local Notation mem_ev := (mem_ev(Loc:=Loc)).
  Local Notation rw_map := (rw_map(Loc:=Loc)).

  Inductive atomic_op : Type :=
  | ALoad : Layout -> Loc -> atomic_op
  | AStore : Layout -> Loc -> Val -> atomic_op
  | ACAS : Layout -> Loc -> Val (* expected val *) ->
          Val (* new val*) -> atomic_op.

  Class sqlang {mem_inst : @Memory Loc Val LocEqDec LocCountable Mem Layout} : Type := {
    (* thread local state *)
    sqlang_thrd_st : Type;
    (* events emitted by the underlying sequential semantics *)
    sqlang_true_val : Val;
    sqlang_false_val : Val;
    sqlang_step :
      sqlang_thrd_st -> Mem -> list mem_ev -> sqlang_thrd_st -> Mem -> Prop;

    (* An exposed atomic operation and a continuation that takes its optional
       return value. *)
    sqlang_at_external :
      sqlang_thrd_st -> atomic_op ->
      (option Val -> sqlang_thrd_st) -> Prop;

    (** Thread creation: [sqlang_spawn c c' c_new] means that [c] is
        about to spawn a new thread starting at [c_new] and continue as
        [c']. *)
    sqlang_spawn :
      sqlang_thrd_st -> sqlang_thrd_st -> sqlang_thrd_st -> Prop;

    (** Terminal states: a thread in a final state with no pending events
        has finished, so being unable to step is not an error. *)
    sqlang_final : sqlang_thrd_st -> Prop;

    (** Value (in)equality for CAS *)
    sqlang_ValEq : Mem -> Val -> Val -> Prop;
    sqlang_ValNEq : Mem -> Val -> Val -> Prop;
  }.

  Context {L : sqlang}.

  Local Notation C := sqlang_thrd_st.
  Local Notation at_external := sqlang_at_external.
  Local Notation Vtrue := sqlang_true_val.
  Local Notation Vfalse := sqlang_false_val.
  Local Notation ValEq := sqlang_ValEq.
  Local Notation ValNEq := sqlang_ValNEq.

  Implicit Types (μ : rw_map) (oμ : option rw_map) (l : Loc)
    (ev : mem_ev) (evs : list mem_ev) (ly : Layout).

  Inductive tstate : Type :=
  | Running (c : C) (T : list mem_ev)
  | StuckState.

  Definition tpool := gmap nat tstate.

  (** No non-atomic write in progress anywhere in ls. *)
  Definition readable μ (ls : list Loc) : Prop :=
    Forall (fun l => μ !! l <> Some Wst) ls.

  (** No non-atomic access at all in ls. *)
  Definition writable μ (ls : list Loc) : Prop :=
    Forall (fun l => μ !! l = Some (Rst 0)) ls.

  Inductive at_step : tpool -> Mem -> rw_map -> tpool -> Mem -> rw_map -> Prop :=

  | Core_Try : forall tp m μ i c T c' m' μ'
      (Hget : tp !! i = Some (Running c []))
      (Hstep : sqlang_step c m T c' m')
      (Hreserve : rsv T μ = Some μ'),
      at_step tp m μ (<[i := Running c' T]> tp) m' μ'
    
  | Core_Commit : forall tp m μ i c T μ'
      (Hget : tp !! i = Some (Running c T))
      (Hne : T <> [])
      (Hcommit : fin T μ = Some μ'),
      at_step tp m μ (<[i := Running c []]> tp) m μ'

  | SC_Read : forall tp m μ i c ly l v K
      (Hget : tp !! i = Some (Running c []))
      (Hext : at_external c (ALoad ly l) K)
      (Hmu : readable μ (layout_to_locs l ly))
      (Hload : load m l ly = Some v),
      at_step tp m μ (<[i := Running (K $ Some v) []]> tp) m μ

  | SC_Write : forall tp m μ i c ly l v m' K
      (Hget : tp !! i = Some (Running c []))
      (Hext : at_external c (AStore ly l v) K)
      (Hmu : writable μ (layout_to_locs l ly))
      (Hstore : store m l ly v = Some m'),
      at_step tp m μ (<[i := Running (K None) []]> tp) m' μ

  | SC_Cas_Suc : forall tp m μ i c ly l v_exp v_new v_cur m' K
      (Hget : tp !! i = Some (Running c []))
      (Hext : at_external c (ACAS ly l v_exp v_new) K)
      (Hmu : writable μ (layout_to_locs l ly))
      (Hload : load m l ly = Some v_cur)
      (Heq : ValEq m v_cur v_exp)
      (Hstore : store m l ly v_new = Some m'),
      at_step tp m μ (<[i := Running (K $ Some Vtrue) []]> tp) m' μ

  | SC_Cas_Fail : forall tp m μ i c ly l v_exp v_new v_cur K
      (Hget : tp !! i = Some (Running c []))
      (Hext : at_external c (ACAS ly l v_exp v_new) K)
      (Hmu : readable μ (layout_to_locs l ly))
      (Hload : load m l ly = Some v_cur)
      (Hneq : ValNEq m v_cur v_exp),
      at_step tp m μ (<[i := Running (K $ Some Vfalse) []]> tp) m μ

  (** comparison succeeded, but can't write new value because reserve fails. *)
  | SC_Cas_Stuck : forall tp m μ i c ly l v_exp v_new v_cur K
      (Hget : tp !! i = Some (Running c []))
      (Hext : at_external c (ACAS ly l v_exp v_new) K)
      (Hload : load m l ly = Some v_cur)
      (Heq : ValEq m v_cur v_exp)
      (Ho : ~ writable μ (layout_to_locs l ly)),
      at_step tp m μ (<[i := StuckState]> tp) m μ

  (** Thread creation.  The new thread gets the least unused index, so
      a pool whose indices are an initial segment of [nat] stays one. *)
  | Spawn : forall tp m μ i c c' c_new j
      (Hget : tp !! i = Some (Running c []))
      (Hspawn : sqlang_spawn c c' c_new)
      (Hfree : tp !! j = None)
      (Hleast : forall k, k < j -> is_Some (tp !! k)),
      at_step tp m μ (<[j := Running c_new []]> (<[i := Running c' []]> tp)) m μ.

  (** ** Safety

      A singleton pool tests whether this particular thread can step with
      the current shared memory and reservations.  All [at_step] rules
      inspect only the selected thread, so this does not ask other threads
      to finish their pending accesses first. *)
  Definition am_reducible (t : tstate) (m : Mem) (μ : rw_map) : Prop :=
    exists tp' m' μ', at_step {[0 := t]} m μ tp' m' μ'.

  (** A singleton reduction really can be scheduled in any pool containing
      this thread, without changing the memory or reservations beforehand. *)
  (** Every pool has a least unused index. *)
  Lemma tpool_least_free (tp : tpool) :
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

  Lemma am_reducible_in_pool tp i t m μ :
    tp !! i = Some t -> am_reducible t m μ ->
    exists tp' m' μ', at_step tp m μ tp' m' μ'.
  Proof.
    intros Hlookup (tp' & m' & μ' & Hstep).
    destruct (tpool_least_free tp) as (j & Hfree & Hleast).
    inversion Hstep; subst;
      apply lookup_singleton_Some in Hget as [Hi Hget]; subst t;
      do 3 eexists; eauto using at_step.
  Qed.

  Definition am_configuration : Type := (tpool * Mem * rw_map)%type.

  Definition am_step (q q' : am_configuration) : Prop :=
    let '(tp, m, μ) := q in
    let '(tp', m', μ') := q' in
    at_step tp m μ tp' m' μ'.

  Definition am_not_stuck (t : tstate) (m : Mem) (μ : rw_map) : Prop :=
    (exists c, t = Running c [] /\ sqlang_final c) \/ am_reducible t m μ.

  (** Every thread has terminated or can step, in every reachable state.
      In particular, pending events must still be committed even when the
      underlying sequential state is final, and [StuckState] is an error. *)
  Definition am_safe (q : am_configuration) : Prop :=
    forall tp m μ,
      rtc am_step q (tp, m, μ) ->
      forall i t, tp !! i = Some t -> am_not_stuck t m μ.

  Lemma am_safe_reachable q q' :
    am_safe q -> rtc am_step q q' -> am_safe q'.
  Proof.
    intros Hsafe Hsteps tp m μ Hsteps' i t Hget.
    eapply Hsafe; [ eapply rtc_trans; eauto | exact Hget ].
  Qed.

  Lemma am_stuck_not_reducible m μ : ~ am_reducible StuckState m μ.
  Proof.
    intros (tp' & m' & μ' & Hstep). inversion Hstep; subst;
      apply lookup_singleton_Some in Hget as [Hi Hget]; discriminate.
  Qed.

  Lemma am_stuck_not_safe q tp m μ i :
    rtc am_step q (tp, m, μ) -> tp !! i = Some StuckState ->
    ~ am_safe q.
  Proof.
    intros Hsteps Hget Hsafe.
    destruct (Hsafe _ _ _ Hsteps _ _ Hget) as [(c & Hc & _) | Hred];
      [ discriminate | exact (am_stuck_not_reducible _ _ Hred) ].
  Qed.

  Lemma am_pending_not_stuck c T m μ :
    T <> [] ->
    (am_not_stuck (Running c T) m μ <-> exists μ', fin T μ = Some μ').
  Proof.
    intros Hne. split.
    - intros [(c' & Heq & _) | (tp' & m' & μ' & Hstep)]; [ congruence | ].
      inversion Hstep; subst;
        apply lookup_singleton_Some in Hget as [Hi Hget];
        inversion Hget; subst; try contradiction. by eexists.
    - intros (μ' & Hfin). right. do 3 eexists.
      eapply Core_Commit with (i := 0);
        [ apply lookup_singleton_eq | exact Hne | exact Hfin ].
  Qed.

  Lemma am_safe_final_singleton c m μ :
    sqlang_final c -> ~ am_reducible (Running c []) m μ ->
    am_safe ({[0 := Running c []]}, m, μ).
  Proof.
    intros Hfinal Hnormal tp m' μ' Hsteps i t Hget.
    inversion Hsteps; subst.
    - apply lookup_singleton_Some in Hget as [Hi Heq]. subst t.
      left. by eexists.
    - exfalso. apply Hnormal.
      match goal with H : am_step _ ?q |- _ =>
        destruct q as [[tp1 m1] μ1]; exists tp1, m1, μ1; exact H end.
  Qed.

End AtomicMachine.
