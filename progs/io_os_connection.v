Require Import List.
Require Import ZArith.
Require Import Psatz.
Require Import ITree.ITree.
Require Import ITree.Interp.Traces.
Require Import compcert.lib.Integers.
Require Import compcert.common.Memory.
Require Import VST.progs.io_specs.
Require Import VST.progs.io_dry.
Require Import VST.floyd.sublist.
Import ExtLib.Structures.Monad.

Local Ltac inj :=
  repeat match goal with
  | H: _ = _ |- _ => assert_succeeds (injection H); inv H
  end.

(** Helper Lemmas *)
Section ListFacts.

  Context {A : Type}.
  Variable Aeq : forall (x y : A), {x = y} + {x <> y}.

  (** common_prefix/common_suffix *)
  Fixpoint common_prefix (xs ys : list A) : list A :=
    match xs, ys with
    | x :: xs', y :: ys' =>
      if Aeq x y then x :: common_prefix xs' ys' else nil
    | _, _ => nil
    end.

  Definition common_suffix (xs ys : list A) : list A :=
    rev (common_prefix (rev xs) (rev ys)).

  Definition split_at_common_suffix (xs ys : list A) : list A * list A :=
    let longer := if length xs <=? length ys then ys else xs in
    let i := length longer - length (common_suffix xs ys) in
    (firstn i longer, common_suffix xs ys).

  Lemma common_prefix_sym : forall xs ys,
    common_prefix xs ys = common_prefix ys xs.
  Proof.
    induction xs as [| x xs]; destruct ys as [| y ys]; cbn; auto.
    destruct (Aeq x y), (Aeq y x); congruence.
  Qed.

  Lemma common_suffix_sym : forall xs ys,
    common_suffix xs ys = common_suffix ys xs.
  Proof.
    unfold common_suffix; intros.
    rewrite common_prefix_sym; auto.
  Qed.

  Lemma common_prefix_correct : forall xs ys,
    let pre := common_prefix xs ys in
    pre = firstn (length pre) xs.
  Proof.
    induction xs as [| x xs]; destruct ys as [| y ys]; cbn; auto.
    destruct (Aeq x y); cbn; congruence.
  Qed.

  Lemma common_prefix_length : forall xs ys,
    length (common_prefix xs ys) <= length xs.
  Proof.
    induction xs as [| x xs]; destruct ys as [| y ys]; cbn; try lia.
    destruct (Aeq x y); cbn; try lia.
    specialize (IHxs ys); lia.
  Qed.

  Lemma common_suffix_length : forall xs ys,
    length (common_suffix xs ys) <= length xs.
  Proof.
    unfold common_suffix; intros.
    rewrite rev_length.
    etransitivity; [apply common_prefix_length |].
    rewrite rev_length; auto.
  Qed.

  Lemma common_suffix_correct : forall xs ys,
    let post := common_suffix xs ys in
    post = skipn (length xs - length post) xs.
  Proof.
    unfold common_suffix; intros; cbn.
    rewrite common_prefix_correct at 1.
    rewrite <- (rev_involutive (skipn _ _)).
    rewrite rev_skipn.
    repeat f_equal.
    generalize (common_suffix_length xs ys); unfold common_suffix.
    rewrite rev_length; lia.
  Qed.

  Lemma common_prefix_full : forall xs,
    common_prefix xs xs = xs.
  Proof.
    induction xs as [| x xs]; cbn; auto.
    destruct (Aeq x x); cbn; congruence.
  Qed.

  Lemma common_suffix_full : forall xs,
    common_suffix xs xs = xs.
  Proof.
    unfold common_suffix; intros.
    rewrite common_prefix_full.
    apply rev_involutive.
  Qed.

  Lemma common_prefix_app : forall xs x,
    common_prefix xs (xs ++ x :: nil) = xs.
  Proof.
    induction xs as [| x xs]; cbn; auto.
    destruct (Aeq x x); cbn; congruence.
  Qed.

  Lemma common_suffix_cons : forall xs x,
    common_suffix xs (x :: xs) = xs.
  Proof.
    unfold common_suffix; intros; cbn.
    rewrite common_prefix_app.
    apply rev_involutive.
  Qed.

  Lemma split_at_common_suffix_correct : forall xs ys,
    length xs <= length ys ->
    let (pre, post) := split_at_common_suffix xs ys in
    ys = pre ++ post.
  Proof.
    induction xs as [| x xs]; destruct ys as [| y ys]; cbn; intros; auto; try lia.
    - rewrite firstn_all, app_nil_r; auto.
    - rewrite leb_correct by lia.
      change (rev xs ++ x :: nil) with (rev (x :: xs)).
      change (rev ys ++ y :: nil) with (rev (y :: ys)).
      fold (common_suffix (x :: xs) (y :: ys)).
      rewrite common_suffix_sym.
      rewrite common_suffix_correct.
      rewrite <- common_suffix_correct at 1.
      rewrite firstn_skipn; auto.
  Qed.

  (** Misc tl/hd_error facts *)
  Lemma in_tail : forall (xs : list A) x,
    In x (tl xs) -> In x xs.
  Proof. destruct xs; intros *; cbn; auto. Qed.

  Lemma tail_not_nil_has_head : forall (xs ys : list A),
    ys <> nil ->
    tl xs = ys ->
    exists x, xs = x :: ys.
  Proof. destruct xs; cbn; intros; subst; eauto; easy. Qed.

  Lemma Zlength_tail : forall (xs : list A),
    (Zlength (tl xs) <= Zlength xs)%Z.
  Proof.
    destruct xs; [cbn; lia |].
    rewrite Zlength_cons; cbn; lia.
  Qed.

  Lemma Zlength_tail_strong : forall (xs : list A),
    xs <> nil ->
    (Zlength (tl xs) = Zlength xs - 1)%Z.
  Proof.
    destruct xs; [easy |].
    intros; cbn [tl].
    rewrite Zlength_cons; lia.
  Qed.

  Lemma hd_error_app : forall (xs ys : list A) x,
    hd_error xs = Some x ->
    hd_error (xs ++ ys) = Some x.
  Proof. destruct xs; cbn; easy. Qed.

  Lemma hd_error_app_case : forall (xs : list A) x,
    hd_error (xs ++ x :: nil) = hd_error xs \/ xs = nil.
  Proof. destruct xs; auto. Qed.

  Lemma hd_error_tl : forall (xs : list A) x,
    hd_error (tl xs) = Some x ->
    exists y, hd_error xs = Some y.
  Proof. destruct xs; cbn; eauto. Qed.

  Lemma hd_error_in : forall (xs : list A) x,
    hd_error xs = Some x ->
    In x xs.
  Proof. destruct xs; cbn; intros; inj; auto; easy. Qed.

  Lemma app_tail_case : forall (xs ys ys' : list A) x y,
    xs ++ x :: nil = ys ++ y :: ys' ->
    ys' = nil /\ x = y /\ xs = ys \/
    exists ys'', xs = ys ++ y :: ys'' /\ ys' = ys'' ++ x :: nil.
  Proof.
    intros * Heq.
    assert (Hcase: ys' = nil \/ exists ys'' y'', ys' = ys'' ++ y'' :: nil).
    { clear; induction ys'; auto.
      intuition (subst; eauto using app_nil_l).
      destruct H as (? & ? & ?); subst.
      eauto using app_comm_cons.
    }
    destruct Hcase as [? | (? & ? & ?)]; subst.
    - apply app_inj_tail in Heq; intuition auto.
    - rewrite app_comm_cons, app_assoc in Heq.
      apply app_inj_tail in Heq; intuition (subst; eauto).
  Qed.

End ListFacts.

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
  unfold getchar_pre, getchar_pre'; intros ? *.
  apply sutt_trace_incl.
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
| ETReadOS (ridx : nat) (r : Z)
| ETReadUser (ridx : nat) (r : Z)
| ETWrite (c : Z).
Definition etrace := list IO_trace_event.

Definition IO_trace_event_eq (e1 e2 : IO_trace_event) : {e1 = e2} + {e1 <> e2} :=
  ltac:(repeat decide equality).

Definition trace_event_rtype (e : IO_trace_event) :=
  match e with
  | ETReadOS _ _ => void
  | ETReadUser _ _ => int
  | ETWrite _ => unit
  end.

Definition io_event_of_io_tevent (e : IO_trace_event)
  : option (IO_event (trace_event_rtype e) * (trace_event_rtype e)) :=
  match e with
  | ETReadOS _ _ => None
  | ETReadUser _ r => Some (ERead, Int.repr r)
  | ETWrite c => Some (EWrite (Int.repr c), tt)
  end.

Fixpoint trace_of_etrace (t : etrace) : @trace IO_event unit :=
  match t with
  | nil => TEnd
  | e :: t' =>
      match io_event_of_io_tevent e with
      | Some (e', r) => TEventResponse e' r (trace_of_etrace t')
      | _ => trace_of_etrace t'
      end
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

  Goal is_trace tree (trace_of_etrace (ETReadUser O 0 :: ETReadOS O 0 :: nil)).
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
  Context `{ConsoleLen}.

  Class SerialOracle := {
    serial_oracle : etrace -> Z;
    serial_oracle_in_range : forall tr,
      0 <= serial_oracle tr <= 255
  }.
  Context `{SerialOracle}.

  Record state := mkSt {
    st_mem : mem;
    st_trace : etrace;
  }.

  Fixpoint compute_console (tr : etrace) : list (Z * nat) :=
    match tr with
    | nil => nil
    | ev :: tr' =>
        let cons := compute_console tr' in
        match ev with
        | ETReadOS ridx c =>
            let cons' := if Zlength cons <? CONSOLE_MAX_LEN then cons
                         else tl cons in
            cons' ++ (c, ridx) :: nil
        | ETReadUser _ _ => tl cons
        | _ => cons
        end
    end.

  (* Read a character from the serial device and place it in the console buffer.
     Triggered by an interrupt from the serial device. *)
  Definition serial_getc (st : state) : state :=
    let (mem, tr) := st in
    let c := serial_oracle tr in
    let ridx := length tr in
    mkSt mem (ETReadOS ridx c :: tr).

  (* Take the first element from the console buffer or -1 if it is empty. *)
  Definition console_read (st : state) : state * Z :=
    let (mem, tr) := st in
    match compute_console tr with
    | nil => (st, -1)
    | (c, ridx) :: _ =>
      let st' := mkSt mem (ETReadUser ridx c :: tr) in
      (st', c)
    end.

  (* Return the new state, the read character, and the section of the trace to
     be consumed. *)
  Definition getchar_spec (st : state) : state * Z :=
    let (st', r) := console_read st in
    (* Success *)
    if 0 <=? r then (st', r)
    (* Error *)
    else (st', -1).

End Specs.

(** Trace Invariants *)
Section Invariants.

  Context {Hclen : ConsoleLen} {Horacle : SerialOracle}.

  (* Everything in the trace was put there by the serial device. *)
  Definition valid_trace_serial tr :=
    forall ridx c pre post,
      tr = post ++ ETReadOS ridx c :: pre ->
      serial_oracle pre = c /\ length pre = ridx.

  (* Every user read has a matching OS read earlier in the trace. *)
  Definition valid_trace_user tr :=
    forall ridx c pre post,
      tr = post ++ ETReadUser ridx c :: pre ->
      In (ETReadOS ridx c) pre /\ hd_error (compute_console pre) = Some (c, ridx).

  (* Every event in the trace is unique. *)
  Definition valid_trace_unique (tr : etrace) := NoDup tr.

  (* All trace invariants hold. *)
  Record valid_trace st := {
    vt_trace_serial : valid_trace_serial st.(st_trace);
    vt_trace_user : valid_trace_user st.(st_trace);
    vt_trace_unique : valid_trace_unique st.(st_trace);
  }.

  (* Compute the newly added events in the trace. *)
  Definition new_trace (st st' : state) : etrace :=
    fst (split_at_common_suffix IO_trace_event_eq st.(st_trace) st'.(st_trace)).

  (* Invariants about the returned character and traces. *)
  Definition valid_ret (st st' : state) (c : Z) :=
    (* c is in the proper range. *)
    (c = -1 \/ 0 <= c <= 255) /\
    (* The memory is unchanged. *)
    st.(st_mem) = st'.(st_mem) /\
    let t := new_trace st st' in
    (* The new trace is the old one plus the newly added events. *)
    st'.(st_trace) = t ++ st.(st_trace) /\
    (* The newly added events are either nil or a single user read. *)
    (c = -1 -> t = nil) /\
    (0 <= c <= 255 -> exists ridx, t = ETReadUser ridx c :: nil).

  Lemma valid_trace_serial_cons : forall tr ev,
    valid_trace_serial (ev :: tr) ->
    valid_trace_serial tr.
  Proof.
    unfold valid_trace_serial.
    intros; subst; eauto using app_comm_cons.
  Qed.

  Lemma valid_trace_serial_app : forall tr' tr,
    valid_trace_serial (tr' ++ tr) ->
    valid_trace_serial tr.
  Proof.
    induction tr'; cbn; eauto using valid_trace_serial_cons.
  Qed.

  Local Hint Resolve valid_trace_serial_cons valid_trace_serial_app.

  Lemma read_os_ordered : forall mid pre ridx c ridx' c',
    valid_trace_serial (ETReadOS ridx' c' :: mid ++ ETReadOS ridx c :: pre) ->
    (ridx < ridx')%nat.
  Proof.
    intros * Hvalid.
    edestruct (Hvalid ridx); eauto using app_comm_cons.
    edestruct (Hvalid ridx'); eauto using app_nil_l.
    subst; rewrite app_length; cbn; lia.
  Qed.

  Lemma in_console_in_trace : forall tr ridx c,
    In (c, ridx) (compute_console tr) ->
    In (ETReadOS ridx c) tr.
  Proof.
    induction tr as [| ev tr]; cbn; intros * Hin; auto.
    destruct ev; cbn in Hin; auto using in_tail.
    rewrite in_app_iff in Hin; cbn in Hin.
    intuition (inj; auto).
    destruct (_ <? _); auto using in_tail.
  Qed.

  Lemma console_trace_same_order : forall tr pre mid post ridx c ridx' c',
    compute_console tr = pre ++ (c, ridx) :: mid ++ (c', ridx') :: post ->
    exists pre' mid' post',
      tr = post' ++ ETReadOS ridx' c' :: mid' ++ ETReadOS ridx c :: pre'.
  Proof.
    induction tr as [| ev tr]; cbn; intros * Hcons;
      [contradict Hcons; auto using app_cons_not_nil |].
    destruct ev; cbn in Hcons;
      try solve [edestruct IHtr as (? & ? & ? & ?); eauto; subst; eauto using app_comm_cons].
    - rewrite app_comm_cons, app_assoc in Hcons.
      destruct @app_tail_case with (1 := Hcons) as [(? & ? & Hcons') | (? & Hcons' & ?)]; inj; subst;
        destruct (_ <? _).
      + assert (Hin: In (c, ridx) (compute_console tr)).
        { rewrite Hcons', in_app_iff; cbn; auto. }
        apply in_console_in_trace in Hin.
        apply in_split in Hin; destruct Hin as (? & ? & ?); subst; eauto using app_nil_l.
      + apply tail_not_nil_has_head in Hcons'; auto using app_cons_not_nil.
        destruct Hcons' as (? & Hcons').
        rewrite app_comm_cons in Hcons'.
        assert (Hin: In (c, ridx) (compute_console tr)).
        { rewrite Hcons', in_app_iff; cbn; auto. }
        apply in_console_in_trace in Hin.
        apply in_split in Hin; destruct Hin as (? & ? & Heq); subst; eauto using app_nil_l.
      + rewrite <- app_assoc, <- app_comm_cons in Hcons'.
        edestruct IHtr as (? & ? & ? & Heq'); eauto; subst; eauto using app_comm_cons.
      + apply tail_not_nil_has_head in Hcons'; auto using app_cons_not_nil.
        destruct Hcons' as (? & Hcons').
        rewrite <- app_assoc, <- app_comm_cons in Hcons'.
        rewrite app_comm_cons in Hcons'.
        edestruct IHtr as (? & ? & ? & Heq); eauto; subst; eauto using app_comm_cons.
    - assert (Hcons': exists el,
        compute_console tr = el :: pre ++ (c, ridx) :: mid ++ (c', ridx') :: post).
      { destruct (compute_console tr); cbn in Hcons; subst; eauto.
        contradict Hcons; auto using app_cons_not_nil.
      }
      destruct Hcons' as (? & Hcons').
      rewrite app_comm_cons in Hcons'; eauto.
        edestruct IHtr as (? & ? & ? & Heq); eauto; subst; eauto using app_comm_cons.
  Qed.

  Corollary console_tl_trace_same_order : forall tr ridx c ridx' c',
    hd_error (compute_console tr) = Some (c, ridx) ->
    hd_error (tl (compute_console tr)) = Some (c', ridx') ->
    exists pre' mid' post',
      tr = post' ++ ETReadOS ridx' c' :: mid' ++ ETReadOS ridx c :: pre'.
  Proof.
    intros * Hcons Hcons'.
    destruct (compute_console tr) as [| ? cons] eqn:Heq; cbn in Hcons, Hcons'; [easy |]; inj.
    destruct cons as [| ? cons'] eqn:Heq'; cbn in Hcons'; [easy |]; inj.
    eapply console_trace_same_order.
    instantiate (1 := cons'); repeat instantiate (1 := nil); eauto.
  Qed.

  Lemma compute_console_ordered : forall tr ev ridx c ridx' c',
    let cons := compute_console tr in
    let cons' := compute_console (ev :: tr) in
    valid_trace_serial (ev :: tr) ->
    hd_error cons = Some (c, ridx) ->
    hd_error cons' = Some (c', ridx') ->
    match ev with
    | ETReadUser _ _ => (ridx < ridx')%nat
    | _ => (ridx <= ridx')%nat
    end.
  Proof.
    intros * Hserial Hcons Hcons'; subst cons cons'.
    destruct ev; cbn in Hcons'.
    - destruct (_ <? _).
      + erewrite hd_error_app in Hcons'; eauto; inj; auto.
      + destruct (hd_error_app_case (tl (compute_console tr)) (r, ridx0)) as [Heq | Heq];
          rewrite Heq in Hcons'; clear Heq.
        * edestruct console_tl_trace_same_order as (? & ? & ? & Heq); eauto; subst.
          rewrite app_comm_cons in Hserial.
          apply valid_trace_serial_app in Hserial.
          eapply read_os_ordered in Hserial; eauto; lia.
        * cbn in Hcons'; inj.
          apply hd_error_in in Hcons.
          apply in_console_in_trace in Hcons.
          apply in_split in Hcons; destruct Hcons as (? & ? & ?); subst.
          apply read_os_ordered in Hserial; lia.
    - edestruct console_tl_trace_same_order as (? & ? & ? & Heq); eauto; subst.
      eapply read_os_ordered; eauto.
    - rewrite Hcons in Hcons'; inj; auto.
  Qed.

  Lemma compute_console_user_ridx_increase : forall post pre ridx c ridx' c',
    let tr := post ++ ETReadUser ridx c :: pre in
    let cons := compute_console pre in
    let cons' := compute_console tr in
    valid_trace_serial tr ->
    hd_error cons = Some (c, ridx) ->
    hd_error cons' = Some (c', ridx') ->
    (ridx < ridx')%nat.
  Proof.
    induction post as [| ev post]; intros * Hserial Hcons Hcons'; subst tr cons cons'.
    - eapply compute_console_ordered in Hcons; eauto.
      cbn in Hcons; auto.
    - assert (Hcase:
        (exists ridx'' c'',
          hd_error (compute_console (post ++ ETReadUser ridx c :: pre)) = Some (c'', ridx'')) \/
        ev = ETReadOS ridx' c' /\ compute_console (post ++ ETReadUser ridx c :: pre) = nil).
      { cbn in Hcons'; destruct ev; eauto.
        - destruct (compute_console (post ++ _ :: pre)) as [| (? & ?) ?] eqn:?; cbn; eauto.
          right; destruct (_ <? _); cbn in Hcons'; inj; eauto.
        - eapply hd_error_tl in Hcons'.
          destruct Hcons' as ((? & ?) & ?); eauto.
      }
      destruct Hcase as [(ridx'' & c'' & Hcons'') | (? & Hcons'')]; subst.
      + enough (ridx < ridx'' <= ridx')%nat by lia.
        split; eauto.
        destruct ev; eapply compute_console_ordered in Hcons'; eauto; lia.
      + apply hd_error_in in Hcons.
        apply in_console_in_trace in Hcons.
        apply in_split in Hcons; destruct Hcons as (? & ? & ?); subst.
        rewrite <- app_comm_cons in Hserial.
        rewrite (app_comm_cons _ _ (ETReadUser _ _)) in Hserial.
        rewrite app_assoc in Hserial.
        eauto using read_os_ordered.
  Qed.

  Lemma console_len : forall tr,
    Zlength (compute_console tr) <= CONSOLE_MAX_LEN.
  Proof.
    pose proof console_len_pos.
    induction tr as [| ev tr]; cbn; try lia.
    destruct ev; cbn; auto.
    - destruct (_ <? _) eqn:Hlt; [rewrite Z.ltb_lt in Hlt | rewrite Z.ltb_nlt in Hlt];
        rewrite Zlength_app, Zlength_cons, Zlength_nil; try lia.
      rewrite Zlength_tail_strong; try lia.
      intros Hcons; rewrite Hcons in *; cbn in *; lia.
    - etransitivity; [apply Zlength_tail |]; auto.
  Qed.

  (** Trace Invariants Preserved *)
  Lemma serial_getc_preserve_valid_trace : forall st st',
    valid_trace st ->
    serial_getc st = st' ->
    valid_trace st'.
  Proof.
    unfold serial_getc; intros * Hvalid Hspec.
    destruct st as [? tr]; subst; destruct Hvalid; cbn in *.
    split; cbn; red; auto.
    - (* valid_trace_serial *)
      intros * Heq.
      destruct post; inj; eauto.
    - (* valid_trace_user *)
      intros * Heq.
      destruct post; inj; eauto.
    - (* valid_trace_unique *)
      constructor; auto; intros Hin.
      apply in_split in Hin.
      destruct Hin as (post & pre & Heq); subst.
      edestruct vt_trace_serial0 as (? & Hlen); eauto.
      rewrite Heq, app_length in Hlen.
      cbn in Hlen; lia.
  Qed.

  Lemma console_read_preserve_valid_trace : forall st st' c,
    valid_trace st ->
    console_read st = (st', c) ->
    valid_trace st'.
  Proof.
    unfold console_read; intros * Hvalid Hspec.
    destruct st as [? tr]; destruct Hvalid; cbn in *.
    destruct (compute_console tr) as [| (c' & ridx) cons] eqn:Hcons; inj.
    - repeat (split; auto).
    - split; cbn; red; auto using in_tail.
      + (* valid_trace_serial *)
        intros * Heq.
        destruct post; inj; eauto.
      + (* valid_trace_user *)
        intros * Heq.
        symmetry in Heq; destruct post; inj; cbn in *; eauto.
        assert (Hin: In (ETReadOS ridx c) tr).
        { apply in_console_in_trace.
          rewrite Hcons; cbn; auto.
        }
        apply in_split in Hin.
        destruct Hin as (post & pre & ?); subst.
        edestruct vt_trace_serial0; eauto; subst.
        rewrite in_app_iff, Hcons; cbn; auto.
      + (* valid_trace_unique *)
        constructor; auto; intros Hin.
        apply in_split in Hin.
        destruct Hin as (post & pre & ?); subst.
        edestruct vt_trace_user0 as (Hin & Hhd); eauto.
        enough (ridx < ridx)%nat by lia.
        eapply compute_console_user_ridx_increase; eauto.
        rewrite Hcons; cbn; auto.
  Qed.

  Lemma getchar_spec_preserve_valid_trace : forall st st' c,
    valid_trace st ->
    getchar_spec st = (st', c) ->
    valid_trace st'.
  Proof.
    unfold getchar_spec; intros * Hvalid Hspec.
    destruct (console_read st) eqn:Hread.
    eapply console_read_preserve_valid_trace in Hread; eauto.
    destruct (0 <=? _) eqn:Hle; inj; eauto.
  Qed.

  (** Return Invariants Preserved *)
  Lemma console_read_valid_ret : forall st st' c,
    valid_trace st ->
    console_read st = (st', c) ->
    valid_ret st st' c.
  Proof.
    unfold console_read; intros * Hvalid Hspec.
    destruct st as [? tr]; destruct Hvalid; cbn in *.
    destruct (compute_console tr) as [| (c' & ridx) cons] eqn:Hcons; inj.
    - repeat (split; eauto using common_suffix_full); cbn -[common_suffix]; try lia.
      all: rewrite Nat.leb_refl, common_suffix_full, Nat.sub_diag; cbn; auto.
    - repeat split.
      + (* c in range *)
        assert (Hin: In (ETReadOS ridx c) tr).
        { apply in_console_in_trace.
          rewrite Hcons; cbn; auto.
        }
        apply in_split in Hin.
        destruct Hin as (post & pre & ?); subst.
        edestruct vt_trace_serial0; eauto; subst.
        right; apply serial_oracle_in_range.
      + (* new event + old trace = new trace *)
        cbn -[common_suffix]; rewrite leb_correct by lia.
        rewrite common_suffix_cons.
        replace (length (_ :: _) - length _)%nat with 1%nat.
        { cbn; eauto. }
        clear; induction tr; auto.
      + (* empty trace *)
        assert (Hin: In (ETReadOS ridx c) tr).
        { apply in_console_in_trace.
          rewrite Hcons; cbn; auto.
        }
        apply in_split in Hin.
        destruct Hin as (post & pre & ?); subst.
        edestruct vt_trace_serial0; eauto; subst.
        pose proof (serial_oracle_in_range pre); lia.
      + (* singleton trace *)
        intros; cbn -[common_prefix]; rewrite leb_correct by lia.
        rewrite common_suffix_cons.
        replace (length (_ :: _) - length _)%nat with 1%nat.
        { cbn; eauto. }
        clear; induction tr; auto.
  Qed.

  Lemma getchar_spec_valid_ret : forall st st' c,
    valid_trace st ->
    getchar_spec st = (st', c) ->
    valid_ret st st' c.
  Proof.
    unfold getchar_spec; intros * Hvalid Hspec.
    destruct (console_read st) eqn:Hread.
    eapply console_read_valid_ret in Hread; eauto.
    destruct (0 <=? _) eqn:Hle; inj; eauto.
    rewrite Z.leb_nle in Hle.
    destruct Hread as ([? | ?] & ? & ? & ? & ?); subst; try lia.
    repeat (split; auto).
  Qed.

End Invariants.

Section SpecsCorrect.

  Context `{SerialOracle} `{ConsoleLen}.

  (* For any trace that the new itree (z) allows, the old itree (z0) allowed it
     with the generated trace (t) as a prefix. *)

  Definition consume_trace (z0 z : IO_itree) (et : etrace) :=
    let t := trace_of_etrace et in
    forall t',
      is_trace z t' ->
      is_trace z0 (app_trace t t').

  Lemma getchar_correct k z st :
    (* Initial trace is valid *)
    valid_trace st ->
    (* Pre condition holds *)
    getchar_pre' st.(st_mem) k z ->
    exists st' r,
      (* Spec with same initial memory returns some state and result *)
      getchar_spec st = (st', r) /\
      (* New itree is old k applied to result, or same as old itree if nothing
         to read *)
      let z' := if 0 <=? r then k (Int.repr r) else z in
      (* Post condition holds on new state, itree, and result *)
      getchar_post' st.(st_mem) st'.(st_mem) (Int.repr r) (k, z) z' /\
      (* Compute the newly added events *)
      let t := new_trace st st' in
      (* The new itree 'consumed' the generated trace *)
      consume_trace z z' t /\
      (* t is the correct prefix *)
      st'.(st_trace) = t ++ st.(st_trace) /\
      (* The new trace is valid *)
      valid_trace st'.
  Proof.
    unfold getchar_pre'; intros Hvalid Hpre; cbn -[new_trace].
    destruct (getchar_spec st) as (st' & r) eqn:Hinv.
    pose proof Hinv as Hret.
    eapply getchar_spec_preserve_valid_trace in Hinv; auto.
    eapply getchar_spec_valid_ret in Hret; auto.
    destruct Hret as (Hr & Hmem & Htr & Ht & Ht').
    exists st', r.
    repeat (split; auto); try congruence.
    - destruct Hr; subst; auto.
      rewrite Int.signed_repr by (cbn; lia).
      rewrite Zle_imp_le_bool by lia.
      auto.
    - hnf; intros * Htrace.
      destruct Hr; subst; cbn in *.
      + rewrite Ht; auto.
      + destruct Ht' as (? & ->); auto.
        apply Hpre.
        hnf; cbn.
        repeat constructor.
        rewrite Zle_imp_le_bool in Htrace by lia.
        apply Htrace.
  Qed.

End SpecsCorrect.
