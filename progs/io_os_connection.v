Require Import List.
Require Import ZArith.
Require Import Psatz.
Require Import ITree.ITree.
Require Import ITree.Interp.Traces.
Require Import compcert.lib.Integers.
Require Import compcert.common.Memory.
Require Import VST.progs.io_specs.
Require Import VST.progs.io_dry.
Import ExtLib.Structures.Monad.

Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope Z.

(* Weaker pre condition using trace_incl instead of eutt. *)
Definition getchar_pre' (m : mem) (witness : int -> IO_itree) (z : IO_itree) :=
  let k := witness in trace_incl (r <- read;; k r) z.

(* getchar_pre' really is weaker. *)
Goal forall m w z,
  getchar_pre m w z -> getchar_pre' m w z.
Proof.
  unfold getchar_pre, getchar_pre', trace_incl; intros ? * Heq * Htrace.
  apply eutt_trace_eq in Heq.
  apply Heq; auto.
Qed.

(* CertiKOS specs must terminate. Could get blocking version back by
   wrapping getchar in a loop. *)
Definition getchar_post' (m0 m : mem) r (witness : (int -> IO_itree) * IO_itree) (z : IO_itree) :=
  m0 = m /\
    (* Success *)
    ((0 <= Int.signed r <= two_p 8 - 1 /\ let (k, _) := witness in z = k r) \/
    (* No character to read *)
    let (_, z0) := witness in z = z0 /\ Int.signed r = -1).

(** Traces *)
Inductive IO_trace_event :=
| ETRead (r : Z)
| ETWrite (c : Z).
Definition etrace := list IO_trace_event.

Definition trace_event_rtype (e : IO_trace_event) :=
  match e with
  | ETRead _ => int
  | ETWrite _ => unit
  end.

Definition io_event_of_io_tevent (e : IO_trace_event)
  : IO_event (trace_event_rtype e) * (trace_event_rtype e) :=
  match e with
  | ETRead r => (ERead, Int.repr r)
  | ETWrite c => (EWrite (Int.repr c), tt)
  end.

Fixpoint trace_of_etrace (t : etrace) : @trace IO_event unit :=
  match t with
  | nil => TEnd
  | e :: t' =>
      let (e', r) := io_event_of_io_tevent e in
      TEventResponse e' r (trace_of_etrace t')
  end.

Section SanityChecks.
  Variable k : int -> itree IO_event unit.
  Definition tree := (r <- read;; k r).

  Goal is_trace tree (@TEnd _ unit).
  Proof.
    hnf; cbn.
    constructor.
  Qed.

  Goal is_trace tree (@TEventEnd _ unit _ ERead).
  Proof.
    hnf; cbn.
    constructor.
  Qed.

  Goal is_trace tree (@TEventResponse _ unit _ ERead Int.zero TEnd).
  Proof.
    hnf; cbn.
    repeat constructor.
  Qed.

  Goal is_trace tree (trace_of_etrace nil).
  Proof.
    hnf; cbn.
    constructor.
  Qed.

  Goal is_trace tree (trace_of_etrace (ETRead 0 :: nil)).
  Proof.
    hnf; cbn.
    repeat constructor.
  Qed.
End SanityChecks.

(** CertiKOS Specs *)
Section Specs.

  Class ConsoleLen := {
    CONSOLE_MAX_LEN : Z;
    console_len_pos : 0 < CONSOLE_MAX_LEN
  }.
  Context {Hclen : ConsoleLen}.

  Class SerialOracle := {
    serial_oracle : etrace -> Z;
    serial_oracle_in_range : forall tr,
      0 <= serial_oracle tr <= 255
  }.
  Context {Horacle : SerialOracle}.

  Record state := mkSt {
    st_mem : mem;
    st_console : list Z;
    st_trace : etrace;
  }.

  (* Read a character from the serial device and place it in the console buffer.
     Triggered by an interrupt from the serial device. *)
  Definition serial_getc (st : state) : state :=
    let (mem, cons, tr) := st in
    let c := serial_oracle tr in
    let cons' := if Zlength cons <? CONSOLE_MAX_LEN then cons
                 else skipn 1 cons in
    mkSt mem (cons' ++ c :: nil) (tr ++ ETRead c :: nil).

  (* Take the first element from the console buffer or -1 if it is empty. *)
  Definition console_read (st : state) : state * Z :=
    let (mem, cons, tr) := st in
    match cons with
    | nil => (st, -1)
    | c :: rest =>
      let st' := mkSt mem rest tr in
      (st', c)
    end.

  (* Return the new state, the read character, and the section of the trace to
     be consumed. *)
  Definition getchar_spec (st : state) : state * Z * etrace :=
    let (st', r) := console_read st in
    (* Success *)
    if 0 <=? r then (st', r, ETRead r :: nil)
    (* Error *)
    else (st', -1, nil).

  (* Invariant that everything in the trace was put there by the serial
     device. *)
  Definition valid_trace st :=
    forall c,
      In (ETRead c) st.(st_trace) ->
      exists tr, serial_oracle tr = c.

  (* Invariant that everything in the console buffer is also in the trace. *)
  Definition valid_console st :=
    Zlength st.(st_console) <= CONSOLE_MAX_LEN /\
    forall c,
      In c st.(st_console) ->
      In (ETRead c) st.(st_trace).

  Definition valid_state st :=
    valid_trace st /\ valid_console st.

  Lemma serial_getc_preserve_valid_trace : forall st st',
    valid_trace st ->
    serial_getc st = st' ->
    valid_trace st'.
  Proof.
    unfold valid_trace, serial_getc; intros * Hvalid Hspec c Hin.
    destruct st as [? ? tr]; inv Hspec; cbn in *.
    rewrite in_app_iff in Hin; cbn in Hin.
    intuition.
    inv H0; eauto.
  Qed.

  Lemma serial_getc_preserve_valid_console : forall st st',
    valid_console st ->
    serial_getc st = st' ->
    valid_console st'.
  Proof.
    unfold valid_console, serial_getc; intros * (Hlen & Hvalid) Hspec.
    destruct st as [? cons ?]; inv Hspec; cbn in *.
    rewrite ?Zlength_correct in *.
    destruct (_ <? _) eqn:Hlt; [rewrite Z.ltb_lt in Hlt | rewrite Z.ltb_nlt in Hlt].
    + rewrite app_length; cbn.
      split; try lia.
      intros c; rewrite ?in_app_iff; cbn.
      intuition (subst; auto).
    + pose proof console_len_pos.
      rewrite app_length; cbn.
      split; [destruct cons; cbn in *; lia |].
      intros c; rewrite ?in_app_iff; cbn.
      destruct cons; intuition (subst; auto).
      intuition.
  Qed.

  Lemma getchar_spec_preserve_valid_trace : forall st st' c tr,
    valid_trace st ->
    getchar_spec st = (st', c, tr) ->
    valid_trace st'.
  Proof.
    unfold valid_trace, getchar_spec, console_read; intros * Hvalid Hspec c Hin.
    destruct st as [? [| c' cons] ?].
    - inv Hspec; eauto.
    - destruct (0 <=? c'); inv Hspec; cbn in *; eauto.
  Qed.

  Lemma getchar_spec_preserve_valid_console : forall st st' c tr,
    valid_console st ->
    getchar_spec st = (st', c, tr) ->
    valid_console st'.
  Proof.
    unfold valid_console, getchar_spec, console_read; intros * (Hlen & Hvalid) Hspec.
    destruct st as [? [| c' cons] ?].
    - inv Hspec; eauto.
    - rewrite ?Zlength_correct in *.
      destruct (0 <=? c'); inv Hspec; cbn in *; split; eauto; lia.
  Qed.

End Specs.

Section SpecsCorrect.

  Context `{SerialOracle} `{ConsoleLen}.

  (* For any trace that the new itree (z) allows, the old itree (z0) allowed it
     with the generated trace (t) as a prefix. *)
  Definition consume_trace (z0 z : IO_itree) (et : etrace) :=
    let t := trace_of_etrace et in
    forall t',
      is_trace z t' ->
      is_trace z0 (app_trace t t').

  Lemma getchar_correct k z m c t :
    (* Initial state is valid *)
    let st := mkSt m c t in
    valid_state st ->
    (* Pre condition holds *)
    getchar_pre' m k z ->
    exists st' r t',
      (* Spec with same initial memory returns some state and result *)
      getchar_spec st = (st', r, t') /\
      (* New itree is old k applied to result, or same as old itree if nothing
         to read *)
      let z' := if 0 <=? r then k (Int.repr r) else z in
      (* Post condition holds on new state, itree, and result *)
      getchar_post' m st'.(st_mem) (Int.repr r) (k, z) z' /\
      (* The new itree 'consumed' the generated trace *)
      consume_trace z z' t'.
  Proof.
    unfold getchar_pre'; intros Hval Hpre; cbn.
    unfold getchar_spec; cbn.
    destruct c as [| r c]; cbn.
    - (* Nothing to read *)
      do 4 esplit; eauto.
      split; hnf; cbn; auto.
    - (* Read r *)
      destruct Hval as (Hval_tr & (Hlen & Hval_cons)).
      specialize (Hval_cons _ ltac:(cbn; auto)).
      specialize (Hval_tr _ Hval_cons).
      destruct Hval_tr as (? & Hr).
      assert (0 <= r <= 255)
        by (subst; apply serial_oracle_in_range; auto).
      rewrite Zle_imp_le_bool by lia.
      do 4 esplit; eauto.
      rewrite Zle_imp_le_bool by lia.
      split; hnf; cbn.
      + rewrite Int.signed_repr; auto.
        cbn; lia.
      + intros * Htrace.
        apply Hpre.
        hnf; cbn.
        repeat constructor.
        apply Htrace.
  Qed.

End SpecsCorrect.
