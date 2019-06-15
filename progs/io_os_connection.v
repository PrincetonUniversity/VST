Require Import List.
Require Import ZArith.
Require Import Psatz.
Require Import ITree.ITree.
Require Import ITree.Interp.Traces.
Require Import compcert.lib.Integers.
Require Import compcert.common.Memory.
Require Import VST.progs.io_specs.
Require Import VST.progs.io_dry.
Require Import VST.progs.io_os_specs.
Require Import VST.floyd.sublist.
Import ExtLib.Structures.Monad.

Local Ltac inj :=
  repeat match goal with
  | H: _ = _ |- _ => assert_succeeds (injection H); inv H
  end.

Ltac prename' pat H name :=
  match type of H with
  | context[?pat'] => unify pat pat'; rename H into name
  end.

Tactic Notation "prename" open_constr(pat) "into" ident(name) :=
  lazymatch goal with
  | H: pat, H': pat |- _ =>
      fail 0 "Multiple possible matches for" pat ":" H "and" H'
  | H: pat |- _ => prename' pat H name
  | H: context[pat], H': context[pat] |- _ =>
      fail 0 "Multiple possible matches for" pat ":" H "and" H'
  | H: context[pat] |- _ => prename' pat H name
  | _ => fail 0 "No hypothesis matching" pat
  end.

Ltac simpl_rev :=
  repeat (rewrite rev_app_distr; cbn [rev app]);
  rewrite <- ?app_assoc; cbn [rev app];
  rewrite ?rev_involutive.

Ltac simpl_rev_in H :=
  repeat (rewrite rev_app_distr in H; cbn [rev app] in H);
  rewrite <- ?app_assoc in H; cbn [rev app] in H;
  rewrite ?rev_involutive in H.

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

  Lemma cons_app_single : forall (xs ys : list A) x,
    xs ++ x :: ys = (xs ++ x :: nil) ++ ys.
  Proof. intros; rewrite <- app_assoc; auto. Qed.

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
Definition ostrace := list IOEvent.

Definition IOEvent_eq (e1 e2 : IOEvent) : {e1 = e2} + {e1 <> e2} :=
  ltac:(repeat decide equality).

Definition trace_event_rtype (e : IOEvent) :=
  match e with
  | IOEvRecv _ _ _ => void
  | IOEvGetc _ _ _ => int
  end.

Definition io_event_of_io_tevent (e : IOEvent)
  : option (IO_event (trace_event_rtype e) * (trace_event_rtype e)) :=
  match e with
  | IOEvRecv _ _ _ => None
  | IOEvGetc _ _ r => Some (ERead, Int.repr r)
  end.

Fixpoint trace_of_ostrace (t : ostrace) : @trace IO_event unit :=
  match t with
  | nil => TEnd
  | e :: t' =>
      match io_event_of_io_tevent e with
      | Some (e', r) => TEventResponse e' r (trace_of_ostrace t')
      | _ => trace_of_ostrace t'
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

  Goal is_trace tree (trace_of_ostrace nil).
  Proof.
    hnf; cbn.
    constructor.
  Qed.

  Goal is_trace tree (trace_of_ostrace (IOEvGetc 0 O 0 :: IOEvRecv 0 O 0 :: nil)).
  Proof.
    hnf; cbn.
    repeat constructor.
  Qed.
End SanityChecks.

(** Trace Invariants *)
Section Invariants.

  Fixpoint compute_console' (tr : ostrace) : list (Z * Z * nat) :=
    match tr with
    | nil => nil
    | ev :: tr' =>
      let cons := compute_console' tr' in
      match ev with
      | IOEvRecv logIdx strIdx c =>
        let cons' := if Zlength cons <? CONS_BUFFER_MAX_CHARS then cons else tl cons in
        cons' ++ (c, logIdx, strIdx) :: nil
      | IOEvGetc _ _ _ => tl cons
      end
    end.
  Definition compute_console tr := compute_console' (rev tr).

  (* Everything in the trace was put there by the serial device. *)
  Definition valid_trace_serial tr :=
    forall logIdx strIdx c pre post,
      tr = pre ++ IOEvRecv logIdx strIdx c :: post ->
      Zlength pre = logIdx + Z.of_nat strIdx /\
      match SerialEnv logIdx with
      | SerialRecv str => nth_error str strIdx = Some c
      | _ => False
      end.

  (* Every user read has a matching OS read earlier in the trace. *)
  Definition valid_trace_user tr :=
    forall logIdx strIdx c pre post,
      tr = pre ++ IOEvGetc logIdx strIdx c :: post ->
      In (IOEvRecv logIdx strIdx c) pre /\ hd_error (compute_console pre) = Some (c, logIdx, strIdx).

  (* Every event in the trace is unique. *)
  Definition valid_trace_unique (tr : ostrace) := NoDup tr.

  (* The console matches compute_console. *)
  Definition valid_trace_console tr cons := cons = compute_console tr.

  (* All trace invariants hold. *)
  Record valid_trace (st : RData) := {
    vt_trace_serial : valid_trace_serial st.(io_log);
    vt_trace_user : valid_trace_user st.(io_log);
    vt_trace_unique : valid_trace_unique st.(io_log);
    vt_trace_console : valid_trace_console st.(io_log) st.(console).(cons_buf);
  }.

  (* Compute the newly added events in the trace. *)
  (* Definition new_trace (st st' : state) : ostrace := *)
  (*   fst (split_at_common_suffix IO_trace_event_eq st.(io_log) st'.(io_log)). *)

  (* Invariants about the returned character and traces. *)
  (* Definition valid_ret (st st' : state) (c : Z) := *)
  (*   (1* c is in the proper range. *1) *)
  (*   (c = -1 \/ 0 <= c <= 255) /\ *)
  (*   (1* The memory is unchanged. *1) *)
  (*   st.(st_mem) = st'.(st_mem) /\ *)
  (*   let t := new_trace st st' in *)
  (*   (1* The new trace is the old one plus the newly added events. *1) *)
  (*   st'.(io_log) = t ++ st.(io_log) /\ *)
  (*   (1* The newly added events are either nil or a single user read. *1) *)
  (*   (c = -1 -> t = nil) /\ *)
  (*   (0 <= c <= 255 -> exists logIdx, t = IOEvGetc logIdx c :: nil). *)

  Lemma valid_trace_serial_snoc : forall tr ev,
    valid_trace_serial (tr ++ ev :: nil) ->
    valid_trace_serial tr.
  Proof.
    unfold valid_trace_serial.
    intros * Hvalid * ->; eapply Hvalid.
    rewrite app_comm_cons, <- app_assoc; eauto.
  Qed.

  Lemma valid_trace_serial_app : forall tr' tr,
    valid_trace_serial (tr ++ tr') ->
    valid_trace_serial tr.
  Proof.
    induction tr'; cbn; intros *.
    - rewrite app_nil_r; auto.
    - rewrite cons_app_single.
      eauto using valid_trace_serial_snoc.
  Qed.

  Local Hint Resolve valid_trace_serial_snoc valid_trace_serial_app.

  Lemma read_os_ordered : forall post mid pre logIdx strIdx c logIdx' strIdx' c',
    valid_trace_serial (pre ++ IOEvRecv logIdx strIdx c :: mid ++ IOEvRecv logIdx' strIdx' c' :: post) ->
    logIdx + Z.of_nat strIdx < logIdx' + Z.of_nat strIdx'.
  Proof.
    intros * Hvalid.
    edestruct (Hvalid logIdx) as (Hlen & ?); eauto; intros.
    edestruct (Hvalid logIdx') as (Hlen' & ?); intros.
    { rewrite app_comm_cons, app_assoc; eauto. }
    pose proof (Zlength_nonneg mid).
    rewrite Zlength_app, Zlength_cons in Hlen'.
    lia.
  Qed.

  Lemma in_console_in_trace' : forall tr logIdx strIdx c,
    In (c, logIdx, strIdx) (compute_console' tr) ->
    In (IOEvRecv logIdx strIdx c) tr.
  Proof.
    induction tr as [| ev tr]; cbn; intros * Hin; eauto.
    destruct ev; auto using in_tail.
    rewrite in_app_iff in Hin; cbn in Hin.
    intuition (inj; auto); right.
    destruct (_ <? _); auto using in_tail.
  Qed.

  Corollary in_console_in_trace : forall tr logIdx strIdx c,
    In (c, logIdx, strIdx) (compute_console tr) ->
    In (IOEvRecv logIdx strIdx c) tr.
  Proof.
    unfold compute_console; intros * Hin.
    apply in_rev.
    apply in_console_in_trace'; auto.
  Qed.

  Lemma console_trace_same_order' : forall tr pre mid post logIdx strIdx c logIdx' strIdx' c',
    compute_console' tr = pre ++ (c, logIdx, strIdx) :: mid ++ (c', logIdx', strIdx') :: post ->
    exists pre' mid' post',
      tr = post' ++ IOEvRecv logIdx' strIdx' c' :: mid' ++ IOEvRecv logIdx strIdx c :: pre'.
  Proof.
    induction tr as [| ev tr]; cbn; intros * Hcons;
      [contradict Hcons; auto using app_cons_not_nil |].
    destruct ev; cbn in Hcons.
    - rewrite app_comm_cons, app_assoc in Hcons.
      destruct @app_tail_case with (1 := Hcons) as [(? & ? & Hcons') | (? & Hcons' & ?)]; inj; subst;
        destruct (_ <? _).
      + assert (Hin: In (c, logIdx, strIdx) (compute_console' tr)).
        { rewrite Hcons', in_app_iff; cbn; auto. }
        apply in_console_in_trace' in Hin.
        apply in_split in Hin; destruct Hin as (? & ? & ?); subst; eauto using app_nil_l.
      + apply tail_not_nil_has_head in Hcons'; auto using app_cons_not_nil.
        destruct Hcons' as (? & Hcons').
        rewrite app_comm_cons in Hcons'.
        assert (Hin: In (c, logIdx, strIdx) (compute_console' tr)).
        { rewrite Hcons', in_app_iff; cbn; auto. }
        apply in_console_in_trace' in Hin.
        apply in_split in Hin; destruct Hin as (? & ? & Heq); subst; eauto using app_nil_l.
      + rewrite <- app_assoc, <- app_comm_cons in Hcons'.
        edestruct IHtr as (? & ? & ? & Heq'); eauto; subst; eauto using app_comm_cons.
      + apply tail_not_nil_has_head in Hcons'; auto using app_cons_not_nil.
        destruct Hcons' as (? & Hcons').
        rewrite <- app_assoc, <- app_comm_cons in Hcons'.
        rewrite app_comm_cons in Hcons'.
        edestruct IHtr as (? & ? & ? & Heq); eauto; subst; eauto using app_comm_cons.
    - assert (Hcons': exists el,
        compute_console' tr = el :: pre ++ (c, logIdx, strIdx) :: mid ++ (c', logIdx', strIdx') :: post).
      { destruct (compute_console' tr); cbn in Hcons; subst; eauto.
        contradict Hcons; auto using app_cons_not_nil.
      }
      destruct Hcons' as (? & Hcons').
      rewrite app_comm_cons in Hcons'; eauto.
        edestruct IHtr as (? & ? & ? & Heq); eauto; subst; eauto using app_comm_cons.
  Qed.

  Corollary console_tl_trace_same_order' : forall tr logIdx strIdx c logIdx' strIdx' c',
    hd_error (compute_console' tr) = Some (c, logIdx, strIdx) ->
    hd_error (tl (compute_console' tr)) = Some (c', logIdx', strIdx') ->
    exists pre' mid' post',
      tr = post' ++ IOEvRecv logIdx' strIdx' c' :: mid' ++ IOEvRecv logIdx strIdx c :: pre'.
  Proof.
    intros * Hcons Hcons'.
    destruct (compute_console' tr) as [| ? cons] eqn:Heq; cbn in Hcons, Hcons'; [easy |]; inj.
    destruct cons as [| ? cons'] eqn:Heq'; cbn in Hcons'; [easy |]; inj.
    eapply console_trace_same_order'.
    instantiate (1 := cons'); repeat instantiate (1 := nil); eauto.
  Qed.

  Lemma compute_console_ordered' : forall tr ev logIdx strIdx c logIdx' strIdx' c',
    let cons := compute_console' tr in
    let cons' := compute_console' (ev :: tr) in
    valid_trace_serial (rev tr ++ ev :: nil) ->
    hd_error cons = Some (c, logIdx, strIdx) ->
    hd_error cons' = Some (c', logIdx', strIdx') ->
    match ev with
    | IOEvGetc _ _ _ => logIdx + Z.of_nat strIdx < logIdx' + Z.of_nat strIdx'
    | _ => logIdx + Z.of_nat strIdx <= logIdx' + Z.of_nat strIdx'
    end.
  Proof.
    intros * Hserial Hcons Hcons'; subst cons cons'.
    destruct ev; cbn in Hcons'.
    - destruct (_ <? _).
      + erewrite hd_error_app in Hcons'; eauto; inj; lia.
      + destruct (hd_error_app_case (tl (compute_console' tr)) (c0, logIdx0, strIdx0)) as [Heq | Heq];
          rewrite Heq in Hcons'; clear Heq.
        * edestruct console_tl_trace_same_order' as (? & ? & ? & Heq); eauto; subst.
          simpl_rev_in Hserial.
          eapply read_os_ordered in Hserial; lia.
        * cbn in Hcons'; inj.
          apply hd_error_in in Hcons.
          apply in_console_in_trace' in Hcons.
          apply in_split in Hcons; destruct Hcons as (? & ? & ?); subst.
          simpl_rev_in Hserial.
          apply read_os_ordered in Hserial; lia.
    - edestruct console_tl_trace_same_order' as (? & ? & ? & Heq); eauto; subst.
      simpl_rev_in Hserial.
      eapply read_os_ordered; eauto.
  Qed.

  Lemma compute_console_user_idx_increase' : forall post pre logIdx strIdx c logIdx' strIdx' c',
    let tr := post ++ IOEvGetc logIdx strIdx c :: pre in
    let cons := compute_console' pre in
    let cons' := compute_console' tr in
    valid_trace_serial (rev tr) ->
    hd_error cons = Some (c, logIdx, strIdx) ->
    hd_error cons' = Some (c', logIdx', strIdx') ->
    logIdx + Z.of_nat strIdx < logIdx' + Z.of_nat strIdx'.
  Proof.
    induction post as [| ev post]; intros * Hserial Hcons Hcons'; subst tr cons cons'; simpl_rev_in Hserial.
    - eapply compute_console_ordered' in Hcons; eauto.
      cbn in Hcons, Hcons'; auto.
    - assert (Hcase:
        (exists logIdx'' strIdx'' c'',
          hd_error (compute_console' (post ++ IOEvGetc logIdx strIdx c :: pre)) = Some (c'', logIdx'', strIdx'')) \/
        ev = IOEvRecv logIdx' strIdx' c' /\ compute_console' (post ++ IOEvGetc logIdx strIdx c :: pre) = nil).
      { cbn in Hcons'; destruct ev; eauto.
        - destruct (compute_console' (post ++ _ :: pre)) as [| ((? & ?) & ?) ?] eqn:?; cbn; eauto.
          right; destruct (_ <? _); cbn in Hcons'; inj; eauto.
        - eapply hd_error_tl in Hcons'.
          destruct Hcons' as (((? & ?) & ?) & ?); eauto.
      }
      destruct Hcase as [(logIdx'' & strIdx'' & c'' & Hcons'') | (? & Hcons'')]; subst.
      + enough (logIdx + Z.of_nat strIdx < logIdx'' + Z.of_nat strIdx'' <= logIdx' + Z.of_nat strIdx') by lia.
        split.
        * eapply IHpost with (pre := pre); simpl_rev; eauto.
          eapply valid_trace_serial_snoc.
          rewrite <- app_assoc, <- app_comm_cons; eauto.
        * rewrite <- app_comm_cons in Hcons'.
          eapply compute_console_ordered' in Hcons'; eauto; simpl_rev; eauto.
          destruct ev; lia.
      + apply hd_error_in in Hcons.
        apply in_console_in_trace' in Hcons.
        apply in_split in Hcons; destruct Hcons as (? & ? & ?); subst.
        simpl_rev_in Hserial.
        rewrite (app_comm_cons _ _ (IOEvGetc _ _ _)) in Hserial.
        rewrite app_assoc in Hserial.
        eauto using read_os_ordered.
  Qed.

  Corollary compute_console_user_idx_increase : forall pre post logIdx strIdx c logIdx' strIdx' c',
    let tr := pre ++ IOEvGetc logIdx strIdx c :: post in
    let cons := compute_console pre in
    let cons' := compute_console tr in
    valid_trace_serial tr ->
    hd_error cons = Some (c, logIdx, strIdx) ->
    hd_error cons' = Some (c', logIdx', strIdx') ->
    logIdx + Z.of_nat strIdx < logIdx' + Z.of_nat strIdx'.
  Proof.
    unfold compute_console; intros *; simpl_rev; intros Hserial Hcons Hcons'.
    eapply compute_console_user_idx_increase'; eauto.
    simpl_rev; auto.
  Qed.

  Lemma console_len' : forall tr,
    Zlength (compute_console' tr) <= CONS_BUFFER_MAX_CHARS.
  Proof.
    induction tr as [| ev tr]; cbn; try lia.
    destruct ev; cbn; auto.
    - destruct (_ <? _) eqn:Hlt; [rewrite Z.ltb_lt in Hlt | rewrite Z.ltb_nlt in Hlt];
        rewrite Zlength_app, Zlength_cons, Zlength_nil; try lia.
      rewrite Zlength_tail_strong; try lia.
      intros Hcons; rewrite Hcons in *; cbn in *; lia.
    - etransitivity; [apply Zlength_tail |]; auto.
  Qed.

  Corollary console_len : forall tr,
    Zlength (compute_console tr) <= CONS_BUFFER_MAX_CHARS.
  Proof. intros; apply console_len'. Qed.

  (** Trace Invariants Preserved *)
  (* Specs:
       serial_intr_enable_spec
       serial_intr_disable_spec
       thread_serial_intr_enable_spec
       thread_serial_intr_disable_spec
       uctx_arg2_spec
       uctx_set_retval1_spec
       uctx_set_errno_spec
       serial_putc_spec
       cons_buf_read_spec
       thread_cons_buf_read_spec
       thread_serial_putc_spec
       sys_getc_spec
       sys_putc_spec
  *)

  Context `{ThreadsConfigurationOps}.

  Ltac destruct_spec Hspec :=
    repeat match type of Hspec with
    | match ?x with _ => _ end = _ => destruct x eqn:?; subst; inj; try discriminate
    end.

  Lemma idxs_NoDup {A} : forall (xs : list A),
    NoDup (idxs xs).
  Proof.
    induction xs; cbn; constructor.
    - clear IHxs; induction (idxs xs); cbn in *; intuition (auto || easy).
    - apply FinFun.Injective_map_NoDup; try red; auto.
  Qed.

  Lemma combine_NoDup {A B} : forall (xs : list A) (ys : list B),
    NoDup xs -> NoDup (combine xs ys).
  Proof.
    induction xs; intros * Hnodup; cbn in *; [constructor | inv Hnodup].
    destruct ys; cbn; constructor; auto.
    intros Hin; apply in_combine_l in Hin; easy.
  Qed.

  Lemma mkRecvEvents_NoDup : forall logIdx cs,
    NoDup (mkRecvEvents logIdx cs).
  Proof.
    unfold mkRecvEvents, enumerate; intros.
    apply FinFun.Injective_map_NoDup; auto using combine_NoDup, idxs_NoDup.
    red; intros (? & ?) (? & ?); intros; inj; auto.
  Qed.

  Lemma cons_intr_aux_preserve_valid_trace : forall st st',
    valid_trace st ->
    cons_intr_aux st = Some st' ->
    valid_trace st'.
  Proof.
    unfold cons_intr_aux; intros * Hvalid Hspec; destruct_spec Hspec.
    - prename (Coqlib.zeq _ _ = _) into Htmp; clear Htmp.
      destruct st; inv Hvalid; constructor; cbn in *; subst; red.
      + (* valid_trace_serial *)
        intros * Heq.
        admit.
      + (* valid_trace_user *)
        intros * Heq.
        admit.
      + (* valid_trace_unique *)
        rewrite conclib.NoDup_app_iff; repeat split; auto using mkRecvEvents_NoDup.
        admit.
      + (* valid_trace_console *)
        destruct console; cbn in *.
        rewrite vt_trace_console0.
        admit.
    - prename (Coqlib.zeq _ _ = _) into Htmp; clear Htmp.
      destruct st; inv Hvalid; constructor; cbn in *; subst; red.
      + (* valid_trace_serial *)
        intros * Heq.
        admit.
      + (* valid_trace_user *)
        intros * Heq.
        admit.
      + (* valid_trace_unique *)
        rewrite conclib.NoDup_app_iff; repeat split; auto using mkRecvEvents_NoDup.
        admit.
      + (* valid_trace_console *)
        destruct console; cbn in *.
        rewrite vt_trace_console0.
        rewrite Zlength_app, Zlength_map.
        admit.
  Admitted.

  Lemma serial_intr_enable_aux_preserve_valid_trace : forall n st st',
    valid_trace st ->
    serial_intr_enable_aux n st = Some st' ->
    valid_trace st'.
  Proof.
    induction n; intros * Hvalid Hspec; cbn -[cons_intr_aux] in Hspec; inj; auto.
    destruct_spec Hspec; auto.
    eapply IHn; [| eauto].
    eapply cons_intr_aux_preserve_valid_trace; eauto.
  Qed.

  Lemma serial_intr_enable_preserve_valid_trace : forall st st',
    valid_trace st ->
    serial_intr_enable_spec st = Some st' ->
    valid_trace st'.
  Proof.
    unfold serial_intr_enable_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    prename serial_intr_enable_aux into Hspec.
    eapply serial_intr_enable_aux_preserve_valid_trace in Hspec.
    2: destruct st; inv Hvalid; constructor; auto.
    destruct r; inv Hspec; constructor; auto.
  Qed.

  Lemma serial_intr_disable_aux_preserve_valid_trace : forall n mask st st',
    valid_trace st ->
    serial_intr_disable_aux n mask st = Some st' ->
    valid_trace st'.
  Proof.
    induction n; intros * Hvalid Hspec; cbn -[cons_intr_aux] in Hspec; inj; auto.
    destruct_spec Hspec; auto.
    - eapply IHn; [| eauto].
      admit.
    - eapply IHn; [| eauto].
      eapply cons_intr_aux_preserve_valid_trace; [| eauto].
      admit.
  Admitted.

  Lemma serial_intr_disable_preserve_valid_trace : forall st st',
    valid_trace st ->
    serial_intr_disable_spec st = Some st' ->
    valid_trace st'.
  Proof.
    unfold serial_intr_disable_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    prename serial_intr_disable_aux into Hspec.
    eapply serial_intr_disable_aux_preserve_valid_trace in Hspec.
    2: destruct st; inv Hvalid; constructor; auto.
    destruct r; inv Hspec; constructor; auto.
  Qed.

  Lemma thread_serial_intr_enable_preserve_valid_trace : forall st st',
    valid_trace st ->
    thread_serial_intr_enable_spec st = Some st' ->
    valid_trace st'.
  Proof.
    unfold thread_serial_intr_enable_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    eapply serial_intr_enable_preserve_valid_trace; eauto.
  Qed.

  Lemma thread_serial_intr_disable_preserve_valid_trace : forall st st',
    valid_trace st ->
    thread_serial_intr_disable_spec st = Some st' ->
    valid_trace st'.
  Proof.
    unfold thread_serial_intr_disable_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    eapply serial_intr_disable_preserve_valid_trace; eauto.
  Qed.

  Lemma uctx_set_retval1_preserve_valid_trace : forall st v st',
    valid_trace st ->
    uctx_set_retval1_spec v st = Some st' ->
    valid_trace st'.
  Proof.
    unfold uctx_set_retval1_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    destruct st; inv Hvalid; constructor; cbn in *; auto.
  Qed.

  Lemma uctx_set_errno_preserve_valid_trace : forall st e st',
    valid_trace st ->
    uctx_set_errno_spec e st = Some st' ->
    valid_trace st'.
  Proof.
    unfold uctx_set_errno_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    destruct st; inv Hvalid; constructor; cbn in *; auto.
  Qed.

  Lemma serial_putc_preserve_valid_trace : forall st c st',
    valid_trace st ->
    serial_putc_spec c st = Some st' ->
    valid_trace st'.
  Proof.
    unfold serial_putc_spec; intros * Hvalid Hspec; destruct_spec Hspec; eauto.
    all: destruct st; inv Hvalid; constructor; cbn in *; subst; red; auto.
  Qed.

  Lemma cons_buf_read_preserve_valid_trace : forall st st' c,
    valid_trace st ->
    cons_buf_read_spec st = Some (st', c) ->
    valid_trace st'.
  Proof.
    unfold cons_buf_read_spec; intros * Hvalid Hspec; destruct_spec Hspec; eauto.
    prename (cons_buf _ = _) into Hcons.
    destruct st; inv Hvalid; constructor; cbn in *; subst; red.
    - (* valid_trace_serial *)
      intros * Heq.
      apply (f_equal (@rev _)) in Heq; simpl_rev_in Heq.
      destruct (rev post); cbn in Heq; inj; prename (rev _ = _) into Heq.
      apply (f_equal (@rev _)) in Heq; simpl_rev_in Heq; subst; eauto.
    - (* valid_trace_user *)
      intros * Heq.
      symmetry in Heq.
      apply (f_equal (@rev _)) in Heq; simpl_rev_in Heq.
      destruct (rev post); cbn in Heq; inj; prename (_ = rev _) into Heq;
        apply (f_equal (@rev _)) in Heq; simpl_rev_in Heq; subst; eauto.
      rewrite <- vt_trace_console0, Hcons; cbn; split; auto.
      apply in_console_in_trace.
      rewrite <- vt_trace_console0, Hcons; cbn; auto.
    - (* valid_trace_unique *)
      rewrite conclib.NoDup_app_swap; cbn.
      constructor; auto; intros Hin.
      apply in_split in Hin.
      destruct Hin as (post & pre & ?); subst.
      edestruct vt_trace_user0 as (Hin & Hhd); eauto.
      rewrite vt_trace_console0 in Hcons.
      apply (f_equal (@hd_error _)) in Hcons.
      eapply compute_console_user_idx_increase in Hcons; eauto; lia.
    - (* valid_trace_console *)
      destruct console; cbn in *; subst.
      red in vt_trace_console0.
      unfold compute_console in *; simpl_rev; cbn.
      rewrite <- vt_trace_console0; cbn; auto.
  Qed.

  Lemma thread_cons_buf_read_preserve_valid_trace : forall st st' c,
    valid_trace st ->
    thread_cons_buf_read_spec st = Some (st', c) ->
    valid_trace st'.
  Proof.
    unfold thread_cons_buf_read_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    eapply cons_buf_read_preserve_valid_trace; eauto.
  Qed.

  Lemma thread_serial_putc_preserve_valid_trace : forall st c st',
    valid_trace st ->
    thread_serial_putc_spec c st = Some st' ->
    valid_trace st'.
  Proof.
    unfold thread_serial_putc_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    eapply serial_putc_preserve_valid_trace; eauto.
  Qed.

  Lemma sys_getc_preserve_valid_trace : forall st st',
    valid_trace st ->
    sys_getc_spec st = Some st' ->
    valid_trace st'.
  Proof.
    unfold sys_getc_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    eapply uctx_set_errno_preserve_valid_trace; [| eauto].
    eapply uctx_set_retval1_preserve_valid_trace; [| eauto].
    eapply thread_serial_intr_enable_preserve_valid_trace; [| eauto].
    eapply thread_cons_buf_read_preserve_valid_trace; [| eauto].
    eapply thread_serial_intr_disable_preserve_valid_trace; [| eauto].
    eauto.
  Qed.

  Lemma sys_putc_preserve_valid_trace : forall st st',
    valid_trace st ->
    sys_putc_spec st = Some st' ->
    valid_trace st'.
  Proof.
    unfold sys_putc_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    eapply uctx_set_errno_preserve_valid_trace; [| eauto].
    eapply thread_serial_intr_enable_preserve_valid_trace; [| eauto].
    eapply thread_serial_putc_preserve_valid_trace; [| eauto].
    eapply thread_serial_intr_disable_preserve_valid_trace; [| eauto].
    eauto.
  Qed.

End Invariants.

Section SpecsCorrect.

  Context `{SerialOracle} `{ConsoleLen}.

  (* For any trace that the new itree (z) allows, the old itree (z0) allowed it
     with the generated trace (t) as a prefix. *)

  Definition consume_trace (z0 z : IO_itree) (et : ostrace) :=
    let t := trace_of_ostrace et in
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
      st'.(io_log) = t ++ st.(io_log) /\
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
