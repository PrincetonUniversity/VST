Require Import List.
Require Import ZArith.
Require Import Psatz.
Require Import ITree.ITree.
Require Import ITree.Interp.Traces.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import VST.progs.io_specs.
Require Import VST.progs.io_mem_specs.
Require Import VST.progs.io_dry.
Require Import VST.progs.io_mem_dry.
Require Import VST.progs.io_os_specs.
Require Import VST.floyd.sublist.
Require Import VST.progs.os_combine.
Import ExtLib.Structures.Monad.

Local Ltac inj :=
  repeat match goal with
  | H: _ = _ |- _ => assert_succeeds (injection H); inv H
  end.

Local Ltac prename' pat H name :=
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

Local Ltac simpl_rev :=
  repeat (rewrite rev_app_distr; cbn [rev app]);
  rewrite <- ?app_assoc; cbn [rev app];
  rewrite ?rev_involutive.

Local Ltac simpl_rev_in H :=
  repeat (rewrite rev_app_distr in H; cbn [rev app] in H);
  rewrite <- ?app_assoc in H; cbn [rev app] in H;
  rewrite ?rev_involutive in H.

Local Ltac destruct_spec Hspec :=
  repeat match type of Hspec with
  | match ?x with _ => _ end = _ => destruct x eqn:?; subst; inj; try discriminate
  end.

(** Helper Lemmas *)
Section ListFacts.

  Context {A : Type}.
  Variable Aeq : forall (x y : A), {x = y} + {x <> y}.

  (** common_prefix *)
  Fixpoint common_prefix (xs ys : list A) : list A :=
    match xs, ys with
    | x :: xs', y :: ys' =>
      if Aeq x y then x :: common_prefix xs' ys' else nil
    | _, _ => nil
    end.

  Definition strip_common_prefix (xs ys : list A) : list A :=
    let longer := if (length xs <=? length ys)%nat then ys else xs in
    skipn (length (common_prefix xs ys)) longer.

  Lemma common_prefix_sym : forall xs ys,
    common_prefix xs ys = common_prefix ys xs.
  Proof.
    induction xs as [| x xs]; destruct ys as [| y ys]; cbn; auto.
    destruct (Aeq x y), (Aeq y x); congruence.
  Qed.

  Lemma common_prefix_correct : forall xs ys pre,
    pre = common_prefix xs ys ->
    exists rest, ys = pre ++ rest.
  Proof.
    induction xs as [| x xs]; destruct ys as [| y ys]; intros; subst; cbn; eauto.
    destruct (Aeq x y); cbn; subst; eauto.
    edestruct (IHxs ys) as (? & Heq); eauto.
    esplit; rewrite <- Heq; eauto.
  Qed.

  Lemma common_prefix_firstn : forall xs ys,
    let pre := common_prefix xs ys in
    pre = firstn (length pre) xs.
  Proof.
    induction xs as [| x xs]; destruct ys as [| y ys]; cbn; auto.
    destruct (Aeq x y); cbn; congruence.
  Qed.

  Lemma common_prefix_length : forall xs ys,
    (length (common_prefix xs ys) <= length xs)%nat.
  Proof.
    induction xs as [| x xs]; destruct ys as [| y ys]; cbn; try lia.
    destruct (Aeq x y); cbn; try lia.
    specialize (IHxs ys); lia.
  Qed.

  Lemma common_prefix_full : forall xs,
    common_prefix xs xs = xs.
  Proof.
    induction xs as [| x xs]; cbn; auto.
    destruct (Aeq x x); cbn; congruence.
  Qed.

  Lemma common_prefix_app : forall xs ys,
    common_prefix xs (xs ++ ys) = xs.
  Proof.
    induction xs as [| x xs]; cbn; auto.
    destruct (Aeq x x); cbn; congruence.
  Qed.

  Lemma strip_common_prefix_correct : forall xs ys,
    (length xs <= length ys)%nat ->
    let post := strip_common_prefix xs ys in
    ys = common_prefix xs ys ++ post.
  Proof.
    induction xs as [| x xs]; destruct ys as [| y ys]; cbn; intros; auto; try lia.
    rewrite leb_correct by lia.
    destruct (Aeq _ _); subst; cbn; auto.
    rewrite common_prefix_sym.
    rewrite common_prefix_firstn at 1.
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

  Lemma skipn_tl : forall n (xs : list A),
    skipn (S n) xs = tl (skipn n xs).
  Proof. induction n; destruct xs; cbn in *; auto. Qed.

  Lemma tl_app : forall (xs ys : list A),
    xs <> nil ->
    tl (xs ++ ys) = tl xs ++ ys.
  Proof. induction xs; cbn; easy. Qed.

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

  Lemma in_app_case : forall (xs ys xs' ys' : list A) x,
    xs ++ ys = xs' ++ x :: ys' ->
    (In x ys /\ exists zs, ys = zs ++ x :: ys') \/ (In x xs /\ exists zs, xs = xs' ++ x :: zs).
  Proof.
    induction xs; cbn; intros * Heq; subst; eauto.
    - rewrite in_app_iff; cbn; intuition eauto.
    - destruct xs'; inj; cbn; eauto.
      edestruct IHxs as [(? & ? & ?) | (? & ? & ?)]; eauto; subst; eauto.
  Qed.

  Lemma cons_app_single : forall (xs ys : list A) x,
    xs ++ x :: ys = (xs ++ x :: nil) ++ ys.
  Proof. intros; rewrite <- app_assoc; auto. Qed.

  Lemma combine_map_fst {B C} : forall (xs : list A) (ys : list B) (f : A -> C),
    combine (map f xs) ys = map (fun '(x, y) => (f x, y)) (combine xs ys).
  Proof.
    induction xs; intros *; cbn; auto.
    destruct ys; cbn; auto.
    f_equal; auto.
  Qed.

End ListFacts.

Definition lex_lt (p1 p2 : Z * Z) : Prop :=
  let (x1, y1) := p1 in let (x2, y2) := p2 in
  (x1 < x2 \/ x1 = x2 /\ y1 < y2)%Z.
Local Infix "<l" := lex_lt (at level 70).

Definition lex_le (p1 p2 : Z * Z) : Prop :=
  p1 = p2 \/ p1 <l p2 .
Local Infix "<=l" := lex_le (at level 70).

Local Open Scope monad_scope.
Local Open Scope Z.

(* Weaker pre condition using trace_incl instead of eutt. *)
Definition getchar_pre' (m : mem) (witness : byte -> IO_itree) (z : IO_itree) :=
  let k := witness in trace_incl (r <- read stdin;; k r) z.

(* CertiKOS specs must terminate. Could get blocking version back by
   wrapping getchar in a loop. *)
Definition getchar_post' (m0 m : mem) r (witness : (byte -> IO_itree) * IO_itree) (z : @IO_itree (@IO_event nat)) :=
  m0 = m /\
    (* Success *)
    ((0 <= Int.signed r <= two_p 8 - 1 /\ let (k, _) := witness in z = k (Byte.repr (Int.signed r))) \/
    (* No character to read *)
    (Int.signed r = -1 /\ let (_, z0) := witness in z = z0)).

(** Traces *)
Definition ostrace := list IOEvent.

Definition IOEvent_eq (e1 e2 : IOEvent) : {e1 = e2} + {e1 <> e2} :=
  ltac:(repeat decide equality).

Definition trace_event_rtype (e : IOEvent) :=
  match e with
  | IOEvRecv _ _ _ => void
  | IOEvSend _ _ => void
  | IOEvGetc _ _ _ => byte
  | IOEvPutc _ _ => unit
  end.

Definition io_event_of_io_tevent (e : IOEvent)
  : option (IO_event (trace_event_rtype e) * (trace_event_rtype e)) :=
  match e with
  | IOEvRecv _ _ _ => None
  | IOEvSend _ _ => None
  | IOEvGetc _ _ r => Some (ERead stdin, Byte.repr r)
  | IOEvPutc _ r => Some (EWrite stdout (Byte.repr r), tt)
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

(** Trace Invariants *)
Section Invariants.

  Definition get_sys_ret (st : RData) :=
    let curid := ZMap.get st.(CPU_ID) st.(cid) in
    ZMap.get U_EBX (ZMap.get curid st.(uctxt)).

  Definition get_sys_arg1 (st : RData) :=
    let curid := ZMap.get st.(CPU_ID) st.(cid) in
    ZMap.get U_EBX (ZMap.get curid st.(uctxt)).

  Definition get_sys_arg2 (st : RData) :=
    let curid := ZMap.get st.(CPU_ID) st.(cid) in
    ZMap.get U_EBX (ZMap.get curid st.(uctxt)).

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
      | _ => cons
      end
    end.
  Definition compute_console tr := compute_console' (rev tr).

  (* Everything in the trace was put there by the serial device. *)
  Definition valid_trace_serial tr lrx :=
    forall logIdx strIdx c pre post,
      tr = pre ++ IOEvRecv logIdx strIdx c :: post ->
      logIdx < lrx - 1 /\
      match SerialEnv logIdx with
      | SerialRecv str => nth_error str strIdx = Some c
      | _ => False
      end.

  (* OS reads are ordered lexicographically by logIdx and strIdx. *)
  Definition valid_trace_ordered tr :=
    forall post mid pre logIdx strIdx c logIdx' strIdx' c',
      tr = pre ++ IOEvRecv logIdx strIdx c :: mid ++ IOEvRecv logIdx' strIdx' c' :: post ->
      (logIdx, Z.of_nat strIdx) <l (logIdx', Z.of_nat strIdx').

  (* Every user read has a matching OS read earlier in the trace. *)
  Definition valid_trace_user tr :=
    forall logIdx strIdx c pre post,
      tr = pre ++ IOEvGetc logIdx strIdx c :: post ->
      In (IOEvRecv logIdx strIdx c) pre /\ hd_error (compute_console pre) = Some (c, logIdx, strIdx).

  (* Every read event in the trace is unique. *)
  Definition valid_trace_unique (tr : ostrace) :=
    let tr' := filter (fun ev =>
      match ev with | IOEvRecv _ _ _ | IOEvGetc _ _ _ => true | _ => false end) tr in
    NoDup tr'.

  (* The console matches compute_console. *)
  Definition valid_trace_console tr cons := cons = compute_console tr.

  (* All trace invariants hold. *)
  Record valid_trace (st : RData) := {
    vt_trace_serial : valid_trace_serial st.(io_log) st.(com1).(l1);
    vt_trace_ordered : valid_trace_ordered st.(io_log);
    vt_trace_user : valid_trace_user st.(io_log);
    vt_trace_unique : valid_trace_unique st.(io_log);
    vt_trace_console : valid_trace_console st.(io_log) st.(console).(cons_buf);
  }.

  (* Console entries are ordered by logIdx and strIdx *)
  Lemma valid_trace_ordered_snoc : forall tr ev,
    valid_trace_ordered (tr ++ ev :: nil) ->
    valid_trace_ordered tr.
  Proof.
    unfold valid_trace_ordered.
    intros * Hvalid * ->; eapply Hvalid.
    do 2 (rewrite <- app_assoc, <- app_comm_cons); auto.
  Qed.

  Lemma valid_trace_ordered_app : forall tr' tr,
    valid_trace_ordered (tr ++ tr') ->
    valid_trace_ordered tr.
  Proof.
    induction tr'; cbn; intros *.
    - rewrite app_nil_r; auto.
    - rewrite cons_app_single.
      eauto using valid_trace_ordered_snoc.
  Qed.

  Local Hint Resolve valid_trace_ordered_snoc valid_trace_ordered_app : core.

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
    destruct ev; cbn in Hcons;
      try solve [edestruct IHtr as (? & ? & ? & ?); eauto; subst; eauto using app_comm_cons].
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
    valid_trace_ordered (rev tr ++ ev :: nil) ->
    hd_error cons = Some (c, logIdx, strIdx) ->
    hd_error cons' = Some (c', logIdx', strIdx') ->
    match ev with
    | IOEvGetc _ _ _ => (logIdx, Z.of_nat strIdx) <l (logIdx', Z.of_nat strIdx')
    | _ => (logIdx, Z.of_nat strIdx) <=l (logIdx', Z.of_nat strIdx')
    end.
  Proof.
    unfold lex_le, lex_lt; intros * Horder Hcons Hcons'.
    destruct ev; cbn in Hcons';
      try solve [rewrite Hcons in Hcons'; inj; auto].
    - destruct (_ <? _).
      + erewrite hd_error_app in Hcons'; eauto; inj; auto.
      + destruct (hd_error_app_case (tl (compute_console' tr)) (c0, logIdx0, strIdx0)) as [Heq | Heq];
          rewrite Heq in Hcons'; clear Heq.
        * edestruct console_tl_trace_same_order' as (? & ? & ? & Heq); eauto; subst.
          simpl_rev_in Horder.
          right; eapply Horder; eauto.
        * cbn in Hcons'; inj.
          apply hd_error_in in Hcons.
          apply in_console_in_trace' in Hcons.
          apply in_split in Hcons; destruct Hcons as (? & ? & ?); subst.
          simpl_rev_in Horder.
          right; eapply Horder; eauto.
    - edestruct console_tl_trace_same_order' as (? & ? & ? & Heq); eauto; subst.
      simpl_rev_in Horder.
      eapply Horder; eauto.
  Qed.

  Lemma compute_console_user_idx_increase' : forall post pre logIdx strIdx c logIdx' strIdx' c',
    let tr := post ++ IOEvGetc logIdx strIdx c :: pre in
    let cons := compute_console' pre in
    let cons' := compute_console' tr in
    valid_trace_ordered (rev tr) ->
    hd_error cons = Some (c, logIdx, strIdx) ->
    hd_error cons' = Some (c', logIdx', strIdx') ->
    (logIdx, Z.of_nat strIdx) <l (logIdx', Z.of_nat strIdx').
  Proof.
    unfold lex_le, lex_lt; induction post as [| ev post]; intros * Horder Hcons Hcons'; simpl_rev_in Horder.
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
      + enough ((logIdx, Z.of_nat strIdx) <l (logIdx'', Z.of_nat strIdx'')
                /\ (logIdx'', Z.of_nat strIdx'') <=l (logIdx', Z.of_nat strIdx')).
        { unfold lex_le, lex_lt in *. intuition (inj; auto; lia). }
        unfold lex_le, lex_lt; split.
        * eapply IHpost with (pre := pre); simpl_rev; eauto.
          eapply valid_trace_ordered_snoc.
          rewrite <- app_assoc, <- app_comm_cons; eauto.
        * rewrite <- app_comm_cons in Hcons'.
          eapply compute_console_ordered' in Hcons'; eauto; simpl_rev; eauto.
          destruct ev; auto.
      + apply hd_error_in in Hcons.
        apply in_console_in_trace' in Hcons.
        apply in_split in Hcons; destruct Hcons as (? & ? & ?); subst.
        simpl_rev_in Horder.
        rewrite (app_comm_cons _ _ (IOEvGetc _ _ _)) in Horder.
        rewrite app_assoc in Horder.
        eapply Horder; eauto.
  Qed.

  Corollary compute_console_user_idx_increase : forall pre post logIdx strIdx c logIdx' strIdx' c',
    let tr := pre ++ IOEvGetc logIdx strIdx c :: post in
    let cons := compute_console pre in
    let cons' := compute_console tr in
    valid_trace_ordered tr ->
    hd_error cons = Some (c, logIdx, strIdx) ->
    hd_error cons' = Some (c', logIdx', strIdx') ->
    (logIdx, Z.of_nat strIdx) <l (logIdx', Z.of_nat strIdx').
  Proof.
    unfold compute_console; intros *; simpl_rev; intros Horder Hcons Hcons'.
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

  (* mkRecvEvents Lemmas *)
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
    apply FinFun.Injective_map_NoDup; auto using combine_NoDup, seq_NoDup.
    red; intros (? & ?) (? & ?); intros; inj; auto.
  Qed.

  Lemma Zlength_enumerate {A} : forall (xs : list A),
    Zlength (enumerate xs) = Zlength xs.
  Proof.
    unfold enumerate; intros.
    rewrite conclib.Zlength_combine, !Zlength_correct, seq_length; lia.
  Qed.

  Lemma seq_nth_app : forall len start n pre post,
    seq start len = pre ++ n :: post ->
    n = (start + length pre)%nat.
  Proof.
    intros * Heq.
    enough (n = nth (length pre) (seq start len) O); subst.
    { rewrite Heq, app_nth2, Nat.sub_diag, seq_nth; auto; cbn.
      rewrite <- (seq_length len start), Heq, app_length; cbn; lia.
    }
    rewrite Heq, app_nth2, Nat.sub_diag; auto.
  Qed.

  Lemma enumerate_length {A} : forall (xs : list A) n x pre post,
    enumerate xs = pre ++ (n, x) :: post ->
    n = length pre.
  Proof.
    unfold enumerate; intros * Heq.
    apply (f_equal (map fst)) in Heq.
    rewrite conclib.combine_fst, map_app in Heq; cbn in Heq.
    apply seq_nth_app in Heq; subst; cbn; auto using map_length.
    rewrite <- Nat2Z.id, <- Zlength_length; rewrite <- Zlength_correct.
    - rewrite !Zlength_correct, seq_length; auto.
    - apply Zlength_nonneg.
  Qed.

  Lemma mkRecvEvents_strIdx : forall cs logIdx strIdx c pre post,
    mkRecvEvents logIdx cs = pre ++ IOEvRecv logIdx strIdx c :: post ->
    strIdx = length pre.
  Proof.
    unfold mkRecvEvents; intros * Heq.
    apply (f_equal (map (fun ev =>
      match ev with
      | IOEvRecv _ sidx c => (sidx, c)
      | _ => (O, 0) (* impossible *)
      end))) in Heq.
    rewrite List.map_map, map_app in Heq; cbn in Heq.
    assert (Henum: map
        (fun x : nat * Z =>
         match (let (i, c) := x in IOEvRecv logIdx i c) with
         | IOEvRecv _ sidx c => (sidx, c)
         | _ => (O, 0)
         end) (enumerate cs) = enumerate cs).
    { clear.
      induction (enumerate cs) as [| ev ?]; cbn; auto.
      destruct ev; cbn; f_equal; auto.
    }
    rewrite Henum in Heq.
    apply enumerate_length in Heq; subst; auto using map_length.
  Qed.

  Corollary mkRecvEvents_ordered : forall cs logIdx strIdx c strIdx' c' pre mid post,
    mkRecvEvents logIdx cs = pre ++ IOEvRecv logIdx strIdx c :: mid ++ IOEvRecv logIdx strIdx' c' :: post ->
    Z.of_nat strIdx < Z.of_nat strIdx'.
  Proof.
    intros * Heq.
    pose proof Heq as Heq'.
    rewrite app_comm_cons, app_assoc in Heq'.
    apply mkRecvEvents_strIdx in Heq; apply mkRecvEvents_strIdx in Heq'; subst.
    rewrite app_length; cbn; lia.
  Qed.

  Lemma mkRecvEvents_cons : forall cs c logIdx,
    mkRecvEvents logIdx (c :: cs) =
    IOEvRecv logIdx O c :: map (fun ev =>
      match ev with
      | IOEvRecv lidx sidx c' => IOEvRecv lidx (S sidx) c'
      | _ => IOEvRecv 0 O 0 (* impossible *)
      end) (mkRecvEvents logIdx cs).
  Proof.
    cbn; intros *; f_equal.
    unfold mkRecvEvents, enumerate.
    rewrite <- seq_shift.
    rewrite combine_map_fst, !List.map_map.
    induction (combine (seq _ _) cs) as [| ev ?]; cbn; auto.
    f_equal; auto.
    destruct ev; auto.
  Qed.

  Lemma in_mkRecvEvents : forall cs ev logIdx,
    In ev (mkRecvEvents logIdx cs) ->
    exists strIdx c,
      nth_error cs strIdx = Some c /\
      nth_error (mkRecvEvents logIdx cs) strIdx = Some ev /\
      ev = IOEvRecv logIdx strIdx c.
  Proof.
    induction cs; intros * Hin; try easy.
    rewrite mkRecvEvents_cons in Hin; cbn in Hin.
    destruct Hin as [? | Hin]; subst.
    - repeat (esplit; eauto); cbn; auto.
    - rewrite mkRecvEvents_cons.
      apply Coqlib.list_in_map_inv in Hin; destruct Hin as (? & ? & Hin); subst.
      eapply IHcs in Hin.
      destruct Hin as (? & ? & ? & ? & ?); subst.
      repeat (esplit; eauto); cbn; auto.
      prename (nth_error (mkRecvEvents _ _) _ = _) into Hnth.
      eapply map_nth_error in Hnth; rewrite Hnth; auto.
  Qed.

  Lemma compute_console_app_space' : forall evs tr,
    let cons := compute_console' tr in
    (forall ev, In ev evs -> exists logIdx strIdx c, ev = IOEvRecv logIdx strIdx c) ->
    Zlength cons + Zlength evs <= CONS_BUFFER_MAX_CHARS ->
    compute_console' (evs ++ tr) =
    cons ++ rev (map (fun ev =>
      match ev with
      | IOEvRecv logIdx strIdx c => (c, logIdx, strIdx)
      | _ => (0, 0, O) (* impossible *)
      end) evs).
  Proof.
    induction evs as [| ev evs]; cbn -[Zlength]; intros * Hall Hlen; auto using app_nil_r.
    rewrite Zlength_cons in Hlen.
    edestruct Hall as (? & ? & ? & ?); eauto; subst.
    destruct (_ <? _) eqn:Hlt; auto.
    - rewrite IHevs; auto using app_assoc; lia.
    - rewrite Z.ltb_nlt in Hlt.
      rewrite IHevs in Hlt; auto; try lia.
      rewrite Zlength_app, Zlength_rev, Zlength_map in Hlt; lia.
  Qed.

  Corollary compute_console_app_space : forall evs tr,
    let cons := compute_console tr in
    (forall ev, In ev evs -> exists logIdx strIdx c, ev = IOEvRecv logIdx strIdx c) ->
    Zlength cons + Zlength evs <= CONS_BUFFER_MAX_CHARS ->
    compute_console (tr ++ evs) =
    cons ++ (map (fun ev =>
      match ev with
      | IOEvRecv logIdx strIdx c => (c, logIdx, strIdx)
      | _ => (0, 0, O) (* impossible *)
      end) evs).
  Proof.
    unfold compute_console; intros.
    rewrite rev_app_distr, compute_console_app_space'.
    - rewrite map_rev, rev_involutive; auto.
    - intros * Hin; rewrite <- in_rev in Hin; auto.
    - rewrite Zlength_rev; auto.
  Qed.

  Lemma compute_console_app_no_space' : forall evs tr,
    let cons := compute_console' tr in
    let skip := Zlength cons + Zlength evs - CONS_BUFFER_MAX_CHARS in
    (forall ev, In ev evs -> exists logIdx strIdx c, ev = IOEvRecv logIdx strIdx c) ->
    Zlength cons <= CONS_BUFFER_MAX_CHARS ->
    Zlength cons + Zlength evs > CONS_BUFFER_MAX_CHARS ->
    compute_console' (evs ++ tr) =
    skipn (Z.to_nat skip) (cons ++ rev (map (fun ev =>
      match ev with
      | IOEvRecv logIdx strIdx c => (c, logIdx, strIdx)
      | _ => (0, 0, O) (* impossible *)
      end) evs)).
  Proof.
    induction evs as [| ev evs]; cbn -[Zlength]; intros * Hall Hmax Hlen.
    { cbn in *.
      replace (Zlength (compute_console' tr)) with CONS_BUFFER_MAX_CHARS by lia.
      cbn; auto using app_nil_r.
    }
    rewrite Zlength_cons in Hlen.
    edestruct Hall as (? & ? & ? & ?); eauto; subst.
    assert (Hcase:
      Zlength (compute_console' tr) + Zlength evs > CONS_BUFFER_MAX_CHARS
      \/ Zlength (compute_console' tr) + Zlength evs = CONS_BUFFER_MAX_CHARS) by lia.
    destruct Hcase as [? | Hlen'].
    - destruct (_ <? _) eqn:Hlt; auto.
      + rewrite Z.ltb_lt in Hlt.
        rewrite IHevs in Hlt; auto.
        rewrite Zlength_skipn, Zlength_app, Zlength_rev, Zlength_map in Hlt; lia.
      + rewrite Zlength_cons, IHevs; auto.
        assert (Hskip:
          Z.to_nat (Zlength (compute_console' tr) + Z.succ (Zlength evs) - CONS_BUFFER_MAX_CHARS)
          = S (Z.to_nat (Zlength (compute_console' tr) + Zlength evs - CONS_BUFFER_MAX_CHARS))).
        { rewrite <- Z2Nat.inj_succ by lia; f_equal; lia. }
        cbn in Hskip; rewrite Hskip, skipn_tl, <- tl_app; cbn.
        * rewrite <- Zskipn_app1 by (rewrite Zlength_app, Zlength_rev, Zlength_map; lia).
          rewrite app_assoc; auto.
        * intros Heq; apply (f_equal (@Zlength _)) in Heq; cbn in Heq.
          rewrite Zlength_skipn, Zlength_app, Zlength_rev, Zlength_map in Heq; lia.
    - rewrite compute_console_app_space'; auto; try lia.
      rewrite Zlength_app, Zlength_rev, Zlength_map.
      rewrite Hlen', Zlength_cons; cbn.
      assert (Hskip:
        Z.to_nat (Zlength (compute_console' tr) + Z.succ (Zlength evs) - CONS_BUFFER_MAX_CHARS)
        = S (Z.to_nat (Zlength (compute_console' tr) + Zlength evs - CONS_BUFFER_MAX_CHARS))).
      { rewrite <- Z2Nat.inj_succ by lia; f_equal; lia. }
      cbn in Hskip; rewrite Hskip, skipn_tl, Hlen', <- tl_app; cbn.
      + rewrite app_assoc; auto.
      + intros Heq; apply (f_equal (@Zlength _)) in Heq; cbn in Heq.
        rewrite Zlength_app, Zlength_rev, Zlength_map in Heq; lia.
  Qed.

  Corollary compute_console_app_no_space : forall evs tr,
    let cons := compute_console tr in
    let skip := Zlength cons + Zlength evs - CONS_BUFFER_MAX_CHARS in
    (forall ev, In ev evs -> exists logIdx strIdx c, ev = IOEvRecv logIdx strIdx c) ->
    Zlength cons <= CONS_BUFFER_MAX_CHARS ->
    Zlength cons + Zlength evs > CONS_BUFFER_MAX_CHARS ->
    compute_console (tr ++ evs) =
    skipn (Z.to_nat skip) (cons ++ (map (fun ev =>
      match ev with
      | IOEvRecv logIdx strIdx c => (c, logIdx, strIdx)
      | _ => (0, 0, O) (* impossible *)
      end) evs)).
  Proof.
    unfold compute_console; intros.
    rewrite rev_app_distr, compute_console_app_no_space'; auto.
    - rewrite map_rev, rev_involutive, Zlength_rev; auto.
    - intros * Hin; rewrite <- in_rev in Hin; auto.
    - rewrite Zlength_rev; auto.
  Qed.

  (** Trace Invariants Preserved *)
  (* Specs:
       serial_intr_enable_spec
       serial_intr_disable_spec
       thread_serial_intr_enable_spec
       thread_serial_intr_disable_spec
       uctx_set_retval1_spec
       uctx_set_errno_spec
       serial_putc_spec
       cons_buf_read_spec
       cons_buf_read_loop_spec
       thread_cons_buf_read_spec
       thread_serial_putc_spec
       thread_cons_buf_read_loop_spec
       sys_getc_spec
       sys_putc_spec
       sys_getcs_spec
  *)
  Context `{ThreadsConfigurationOps}.

  Lemma valid_trace_tx_event : forall st ev,
    match ev with
    | IOEvSend _ _ | IOEvPutc _ _ => True
    | _ => False
    end ->
    valid_trace st ->
    valid_trace (st {io_log : st.(io_log) ++ ev :: nil}).
  Proof.
    destruct ev; try easy; intros _ Hvalid; inv Hvalid; constructor; red; destruct st; cbn in *.
    - intros * Heq.
      apply in_app_case in Heq; cbn in Heq; intuition (try easy).
      all: destruct H2; subst; eapply vt_trace_serial0; eauto.
    - intros * Heq.
      rewrite app_comm_cons, app_assoc in Heq.
      apply in_app_case in Heq; cbn in Heq; intuition (try easy).
      destruct H2; subst; eauto. eapply vt_trace_ordered0; rewrite app_comm_cons, app_assoc; eauto.
    - intros * Heq.
      apply in_app_case in Heq; cbn in Heq; intuition (try easy).
      all: destruct H2; subst; eapply vt_trace_user0; eauto.
    - rewrite conclib.filter_app, app_nil_r; auto.
    - simpl_rev; cbn; auto.
    - intros * Heq.
      apply in_app_case in Heq; cbn in Heq; intuition (try easy).
      all: destruct H2; subst; eapply vt_trace_serial0; eauto.
    - intros * Heq.
      rewrite app_comm_cons, app_assoc in Heq.
      apply in_app_case in Heq; cbn in Heq; intuition (try easy).
      destruct H2; subst; eauto. eapply vt_trace_ordered0; rewrite app_comm_cons, app_assoc; eauto.
    - intros * Heq.
      apply in_app_case in Heq; cbn in Heq; intuition (try easy).
      all: destruct H2; subst; eapply vt_trace_user0; eauto.
    - rewrite conclib.filter_app, app_nil_r; auto.
    - simpl_rev; cbn; auto.
  Qed.

  Lemma cons_intr_aux_preserve_valid_trace : forall st st',
    valid_trace st ->
    cons_intr_aux st = Some st' ->
    valid_trace st'.
  Proof.
    unfold cons_intr_aux; intros * Hvalid Hspec; destruct_spec Hspec.
    - prename (Coqlib.zeq _ _ = _) into Htmp; clear Htmp.
      destruct st; inv Hvalid; constructor; cbn in *; subst; red; cbn in *.
      + (* valid_trace_serial *)
        intros * Heq.
        rewrite Zlength_map.
        pose proof (Zlength_nonneg (enumerate RxBuf)).
        apply in_app_case in Heq.
        destruct Heq as [(Hin & ? & ?) | (? & ? & ?)]; subst.
        * eapply in_mkRecvEvents in Hin.
          destruct Hin as (? & ? & ? & ? & ?); inj.
          prename (SerialEnv _ = _) into Henv.
          rewrite Henv; split; auto; lia.
        * edestruct vt_trace_serial0; eauto.
          split; auto; lia.
      + (* valid_trace_ordered *)
        intros * Heq.
        pose proof Heq as Hcase.
        rewrite app_comm_cons, app_assoc in Hcase.
        apply in_app_case in Hcase.
        destruct Hcase as [(Hin & ? & _) | (? & ? & ?)]; subst.
        * eapply in_mkRecvEvents in Hin.
          destruct Hin as (? & ? & ? & ? & ?); inj.
          apply in_app_case in Heq.
          destruct Heq as [(Hin' & ? & ?) | (? & ? & ?)]; subst.
          -- eapply in_mkRecvEvents in Hin'.
             destruct Hin' as (? & ? & ? & ? & ?); inj.
             prename (mkRecvEvents _ _ = _) into Heq'.
             apply mkRecvEvents_ordered in Heq'; auto.
          -- edestruct vt_trace_serial0; eauto.
        * edestruct vt_trace_ordered0; eauto.
          rewrite <- app_assoc, <- app_comm_cons; eauto.
      + (* valid_trace_user *)
        intros * Heq.
        apply in_app_case in Heq.
        destruct Heq as [(Hin & ? & ?) | (? & ? & ?)]; subst; eauto.
        eapply in_mkRecvEvents in Hin.
        destruct Hin as (? & ? & ? & ? & ?); inj; easy.
      + (* valid_trace_unique *)
        rewrite conclib.filter_app, conclib.NoDup_app_iff; repeat split;
          auto using mkRecvEvents_NoDup, conclib.NoDup_filter.
        intros *; rewrite !filter_In.
        intros (Hin & ?) (Hin' & ?).
        eapply in_mkRecvEvents in Hin'.
        destruct Hin' as (? & ? & ? & ? & ?); inj; subst.
        apply in_split in Hin; destruct Hin as (? & ? & ?); subst.
        edestruct vt_trace_serial0; eauto; lia.
      + (* valid_trace_console *)
        prename Coqlib.zle into Htmp; clear Htmp.
        prename (_ <= _) into Hle.
        destruct console; cbn in *.
        rewrite vt_trace_console0.
        rewrite vt_trace_console0, Zlength_app, Zlength_map in Hle.
        rewrite compute_console_app_space.
        * unfold mkRecvEvents; f_equal; rewrite List.map_map.
          clear; induction (enumerate _) as [| (? & ?) ?]; cbn; auto.
          rewrite IHl; auto.
        * intros * Hin.
          eapply in_mkRecvEvents in Hin.
          destruct Hin as (? & ? & ? & ? & ?); inj; subst; eauto.
        * unfold mkRecvEvents; rewrite Zlength_map; auto.
    - prename (Coqlib.zeq _ _ = _) into Htmp; clear Htmp.
      destruct st; inv Hvalid; constructor; cbn in *; subst; red; cbn in *.
      + (* valid_trace_serial *)
        intros * Heq.
        rewrite Zlength_map.
        pose proof (Zlength_nonneg (enumerate RxBuf)).
        apply in_app_case in Heq.
        destruct Heq as [(Hin & ? & ?) | (? & ? & ?)]; subst.
        * eapply in_mkRecvEvents in Hin.
          destruct Hin as (? & ? & ? & ? & ?); inj.
          prename (SerialEnv _ = _) into Henv.
          rewrite Henv; split; auto; lia.
        * edestruct vt_trace_serial0; eauto.
          split; auto; lia.
      + (* valid_trace_ordered *)
        intros * Heq.
        pose proof Heq as Hcase.
        rewrite app_comm_cons, app_assoc in Hcase.
        apply in_app_case in Hcase.
        destruct Hcase as [(Hin & ? & _) | (? & ? & ?)]; subst.
        * eapply in_mkRecvEvents in Hin.
          destruct Hin as (? & ? & ? & ? & ?); inj.
          apply in_app_case in Heq.
          destruct Heq as [(Hin' & ? & ?) | (? & ? & ?)]; subst.
          -- eapply in_mkRecvEvents in Hin'.
             destruct Hin' as (? & ? & ? & ? & ?); inj.
             prename (mkRecvEvents _ _ = _) into Heq'.
             apply mkRecvEvents_ordered in Heq'; auto.
          -- edestruct vt_trace_serial0; eauto.
        * edestruct vt_trace_ordered0; eauto.
          rewrite <- app_assoc, <- app_comm_cons; eauto.
      + (* valid_trace_user *)
        intros * Heq.
        apply in_app_case in Heq.
        destruct Heq as [(Hin & ? & ?) | (? & ? & ?)]; subst; eauto.
        eapply in_mkRecvEvents in Hin.
        destruct Hin as (? & ? & ? & ? & ?); inj; easy.
      + (* valid_trace_unique *)
        rewrite conclib.filter_app, conclib.NoDup_app_iff; repeat split;
          auto using mkRecvEvents_NoDup, conclib.NoDup_filter.
        intros *; rewrite !filter_In.
        intros (Hin & ?) (Hin' & ?).
        eapply in_mkRecvEvents in Hin'.
        destruct Hin' as (? & ? & ? & ? & ?); inj; subst.
        apply in_split in Hin; destruct Hin as (? & ? & ?); subst.
        edestruct vt_trace_serial0; eauto; lia.
      + (* valid_trace_console *)
        prename Coqlib.zle into Htmp; clear Htmp.
        prename (_ > _) into Hgt.
        destruct console; cbn in *.
        rewrite vt_trace_console0.
        rewrite Zlength_app, Zlength_map, Zlength_enumerate.
        rewrite vt_trace_console0, Zlength_app, Zlength_map in Hgt.
        rewrite compute_console_app_no_space; auto using console_len.
        * unfold mkRecvEvents.
          rewrite List.map_map, Zlength_map, Zlength_enumerate; do 2 f_equal.
          clear; induction (enumerate _) as [| (? & ?) ?]; cbn; auto.
          rewrite IHl; auto.
        * intros * Hin.
          eapply in_mkRecvEvents in Hin.
          destruct Hin as (? & ? & ? & ? & ?); inj; subst; eauto.
        * unfold mkRecvEvents; rewrite Zlength_map; auto.
  Qed.

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
      prename serial_intr into Hspec'; unfold serial_intr in Hspec'; destruct_spec Hspec'.
      destruct o.
      + enough (Hvalid': valid_trace (st {io_log : io_log st ++ IOEvSend 0 z :: nil}));
          auto using valid_trace_tx_event.
        destruct st; inv Hvalid'; constructor; cbn in *; auto.
        destruct com1; cbn in *; red; intros; subst; edestruct vt_trace_serial0; eauto.
        cbn; split; auto; lia.
      + rewrite app_nil_r; destruct st; inv Hvalid; constructor; cbn in *; auto.
        destruct com1; cbn in *; red; intros; subst; edestruct vt_trace_serial0; eauto.
        cbn; split; auto; lia.
    - eapply IHn; [| eauto].
      eapply cons_intr_aux_preserve_valid_trace; [| eauto].
      prename serial_intr into Hspec'; unfold serial_intr in Hspec'; destruct_spec Hspec'.
      destruct o.
      + enough (Hvalid': valid_trace (st {io_log : io_log st ++ IOEvSend 0 z :: nil}));
          auto using valid_trace_tx_event.
        destruct st; inv Hvalid'; constructor; cbn in *; auto.
        destruct com1; cbn in *; red; intros; subst; edestruct vt_trace_serial0; eauto.
        cbn; split; auto; lia.
      + rewrite app_nil_r; destruct st; inv Hvalid; constructor; cbn in *; auto.
        destruct com1; cbn in *; red; intros; subst; edestruct vt_trace_serial0; eauto.
        cbn; split; auto; lia.
  Qed.

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

  Lemma serial_putc_preserve_valid_trace : forall st c st' r,
    valid_trace st ->
    serial_putc_spec c st = Some (st', r) ->
    valid_trace st'.
  Proof.
    unfold serial_putc_spec; intros * Hvalid Hspec; destruct_spec Hspec; eauto.
    all: enough (Hvalid': valid_trace (st {io_log : io_log st ++ IOEvPutc l2 c :: nil}));
      auto using valid_trace_tx_event.
    all: destruct st; inv Hvalid'; constructor; cbn in *; subst; auto.
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
    - (* valid_trace_ordered *)
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
      rewrite conclib.filter_app, conclib.NoDup_app_swap; cbn.
      constructor; auto; intros Hin.
      rewrite filter_In in Hin; destruct Hin as (Hin & _).
      apply in_split in Hin.
      destruct Hin as (post & pre & ?); subst.
      edestruct vt_trace_user0 as (Hin & Hhd); eauto.
      rewrite vt_trace_console0 in Hcons.
      apply (f_equal (@hd_error _)) in Hcons.
      eapply compute_console_user_idx_increase in Hcons; eauto.
      unfold lex_lt in Hcons; lia.
    - (* valid_trace_console *)
      destruct console; cbn in *; subst.
      red in vt_trace_console0.
      unfold compute_console in *; simpl_rev; cbn.
      rewrite <- vt_trace_console0; cbn; auto.
  Qed.

  Lemma cons_buf_read_loop_preserve_valid_trace : forall n st st' read addr read',
    valid_trace st ->
    cons_buf_read_loop_spec n read addr st = Some (st', read') ->
    valid_trace st'.
  Proof.
    induction n; intros * Hvalid Hspec; cbn [cons_buf_read_loop_spec] in Hspec; inj; auto.
    destruct_spec Hspec; inj; auto.
    eapply IHn in Hspec; eauto.
    prename cons_buf_read_spec into Hspec'.
    eapply cons_buf_read_preserve_valid_trace in Hspec'; auto.
    inv Hspec'; destruct r; constructor; auto.
  Qed.

  Lemma thread_cons_buf_read_preserve_valid_trace : forall st st' c,
    valid_trace st ->
    thread_cons_buf_read_spec st = Some (st', c) ->
    valid_trace st'.
  Proof.
    unfold thread_cons_buf_read_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    eapply cons_buf_read_preserve_valid_trace; eauto.
  Qed.

  Lemma thread_serial_putc_preserve_valid_trace : forall st c st' r,
    valid_trace st ->
    thread_serial_putc_spec c st = Some (st', r) ->
    valid_trace st'.
  Proof.
    unfold thread_serial_putc_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    eapply serial_putc_preserve_valid_trace; eauto.
  Qed.

  Lemma thread_cons_buf_read_loop_preserve_valid_trace : forall st st' len addr read,
    valid_trace st ->
    thread_cons_buf_read_loop_spec len addr st = Some (st', read) ->
    valid_trace st'.
  Proof.
    unfold thread_cons_buf_read_loop_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    eapply cons_buf_read_loop_preserve_valid_trace; eauto.
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
    eapply uctx_set_retval1_preserve_valid_trace; [| eauto].
    eapply thread_serial_intr_enable_preserve_valid_trace; [| eauto].
    eapply thread_serial_putc_preserve_valid_trace; [| eauto].
    eapply thread_serial_intr_disable_preserve_valid_trace; [| eauto].
    eauto.
  Qed.

  Lemma sys_getcs_preserve_valid_trace : forall st st',
    valid_trace st ->
    sys_getcs_spec st = Some st' ->
    valid_trace st'.
  Proof.
    unfold sys_getcs_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    eapply uctx_set_errno_preserve_valid_trace; [| eauto].
    eapply uctx_set_retval1_preserve_valid_trace; [| eauto].
    eapply thread_serial_intr_enable_preserve_valid_trace; [| eauto].
    eapply thread_cons_buf_read_loop_preserve_valid_trace; [| eauto].
    eapply thread_serial_intr_disable_preserve_valid_trace; [| eauto].
    eauto.
  Qed.

  (* Memory is unchanged *)
  Lemma cons_intr_aux_mem_unchanged : forall st st',
    cons_intr_aux st = Some st' ->
    st.(HP) = st'.(HP).
  Proof.
    unfold cons_intr_aux; intros * Hspec; destruct_spec Hspec.
    all: destruct st; auto.
  Qed.

  Lemma serial_intr_enable_aux_mem_unchanged : forall n st st',
    serial_intr_enable_aux n st = Some st' ->
    st.(HP) = st'.(HP).
  Proof.
    induction n; intros * Hspec; cbn -[cons_intr_aux] in Hspec; inj; auto.
    destruct_spec Hspec; auto.
    etransitivity.
    eapply cons_intr_aux_mem_unchanged; eauto.
    eauto.
  Qed.

  Lemma serial_intr_enable_mem_unchanged : forall st st',
    serial_intr_enable_spec st = Some st' ->
    st.(HP) = st'.(HP).
  Proof.
    unfold serial_intr_enable_spec; intros * Hspec; destruct_spec Hspec.
    prename serial_intr_enable_aux into Hspec.
    eapply serial_intr_enable_aux_mem_unchanged in Hspec.
    destruct r, st; inv Hspec; auto.
  Qed.

  Lemma serial_intr_disable_aux_mem_unchanged : forall n mask st st',
    serial_intr_disable_aux n mask st = Some st' ->
    st.(HP) = st'.(HP).
  Proof.
    induction n; intros * Hspec; cbn -[cons_intr_aux] in Hspec; inj; auto.
    destruct_spec Hspec; auto.
    - etransitivity; [| eapply IHn; eauto].
      destruct st; auto.
    - etransitivity; [| eapply IHn; eauto].
      etransitivity; [| eapply cons_intr_aux_mem_unchanged; eauto].
      destruct st; auto.
  Qed.

  Lemma serial_intr_disable_mem_unchanged : forall st st',
    serial_intr_disable_spec st = Some st' ->
    st.(HP) = st'.(HP).
  Proof.
    unfold serial_intr_disable_spec; intros * Hspec; destruct_spec Hspec.
    prename serial_intr_disable_aux into Hspec.
    eapply serial_intr_disable_aux_mem_unchanged in Hspec.
    destruct r, st; inv Hspec; auto.
  Qed.

  Lemma thread_serial_intr_enable_mem_unchanged : forall st st',
    thread_serial_intr_enable_spec st = Some st' ->
    st.(HP) = st'.(HP).
  Proof.
    unfold thread_serial_intr_enable_spec; intros * Hspec; destruct_spec Hspec.
    eapply serial_intr_enable_mem_unchanged; eauto.
  Qed.

  Lemma thread_serial_intr_disable_mem_unchanged : forall st st',
    thread_serial_intr_disable_spec st = Some st' ->
    st.(HP) = st'.(HP).
  Proof.
    unfold thread_serial_intr_disable_spec; intros * Hspec; destruct_spec Hspec.
    eapply serial_intr_disable_mem_unchanged; eauto.
  Qed.

  Lemma uctx_set_retval1_mem_unchanged : forall st v st',
    uctx_set_retval1_spec v st = Some st' ->
    st.(HP) = st'.(HP).
  Proof.
    unfold uctx_set_retval1_spec; intros * Hspec; destruct_spec Hspec.
    destruct st; auto.
  Qed.

  Lemma uctx_set_errno_mem_unchanged : forall st e st',
    uctx_set_errno_spec e st = Some st' ->
    st.(HP) = st'.(HP).
  Proof.
    unfold uctx_set_errno_spec; intros * Hspec; destruct_spec Hspec.
    destruct st; auto.
  Qed.

  Lemma serial_putc_mem_unchanged : forall st c st' r,
    serial_putc_spec c st = Some (st', r) ->
    st.(HP) = st'.(HP).
  Proof.
    unfold serial_putc_spec; intros * Hspec; destruct_spec Hspec; eauto.
    all: destruct st; auto.
  Qed.

  Lemma cons_buf_read_mem_unchanged : forall st st' c,
    cons_buf_read_spec st = Some (st', c) ->
    st.(HP) = st'.(HP).
  Proof.
    unfold cons_buf_read_spec; intros * Hspec; destruct_spec Hspec; eauto.
    destruct st; auto.
  Qed.

  Lemma thread_cons_buf_read_mem_unchanged : forall st st' c,
    thread_cons_buf_read_spec st = Some (st', c) ->
    st.(HP) = st'.(HP).
  Proof.
    unfold thread_cons_buf_read_spec; intros * Hspec; destruct_spec Hspec.
    eapply cons_buf_read_mem_unchanged; eauto.
  Qed.

  Lemma thread_serial_putc_mem_unchanged : forall st c st' r,
    thread_serial_putc_spec c st = Some (st', r) ->
    st.(HP) = st'.(HP).
  Proof.
    unfold thread_serial_putc_spec; intros * Hspec; destruct_spec Hspec.
    eapply serial_putc_mem_unchanged; eauto.
  Qed.

  Lemma sys_getc_mem_unchanged : forall st st',
    sys_getc_spec st = Some st' ->
    st.(HP) = st'.(HP).
  Proof.
    unfold sys_getc_spec; intros * Hspec; destruct_spec Hspec.
    etransitivity; [| eapply uctx_set_errno_mem_unchanged; eauto].
    etransitivity; [| eapply uctx_set_retval1_mem_unchanged; eauto].
    etransitivity; [| eapply thread_serial_intr_enable_mem_unchanged; eauto].
    etransitivity; [| eapply thread_cons_buf_read_mem_unchanged; eauto].
    etransitivity; [| eapply thread_serial_intr_disable_mem_unchanged; eauto].
    eauto.
  Qed.

  Lemma sys_putc_mem_unchanged : forall st st',
    sys_putc_spec st = Some st' ->
    st.(HP) = st'.(HP).
  Proof.
    unfold sys_putc_spec; intros * Hspec; destruct_spec Hspec.
    etransitivity; [| eapply uctx_set_errno_mem_unchanged; eauto].
    etransitivity; [| eapply uctx_set_retval1_mem_unchanged; eauto].
    etransitivity; [| eapply thread_serial_intr_enable_mem_unchanged; eauto].
    etransitivity; [| eapply thread_serial_putc_mem_unchanged; eauto].
    etransitivity; [| eapply thread_serial_intr_disable_mem_unchanged; eauto].
    eauto.
  Qed.

  (** No user-visible events are generated. *)
  Definition nil_trace_case t t' :=
    let new := trace_of_ostrace (strip_common_prefix IOEvent_eq t t') in
    t = common_prefix IOEvent_eq t t' /\
    new = trace_of_ostrace nil.

  (** At most one user-visible read event is generated. *)
  Definition getc_trace_case t t' ret :=
    let new := trace_of_ostrace (strip_common_prefix IOEvent_eq t t') in
    t = common_prefix IOEvent_eq t t' /\
    ((ret = -1 /\ new = trace_of_ostrace nil) \/
     (0 <= ret <= 255 /\ forall logIdx strIdx,
        new = trace_of_ostrace (IOEvGetc logIdx strIdx ret :: nil))).

  (** At most one user-visible write event is generated. *)
  Definition putc_trace_case t t' c ret :=
    let new := trace_of_ostrace (strip_common_prefix IOEvent_eq t t') in
    t = common_prefix IOEvent_eq t t' /\
    ((ret = -1 /\ new = trace_of_ostrace nil) \/
     (ret = c mod 256 /\ forall logIdx,
        new = trace_of_ostrace (IOEvPutc logIdx c :: nil))).

  Lemma trace_of_ostrace_app : forall otr otr',
    let tr := trace_of_ostrace otr in
    let tr' := trace_of_ostrace otr' in
    trace_of_ostrace (otr ++ otr') = app_trace tr tr'.
  Proof.
    induction otr as [| ev otr]; cbn; intros *; auto.
    destruct ev; cbn; auto.
    all: rewrite IHotr; auto.
  Qed.

  Lemma IOEvRecvs_not_visible : forall tr,
    (forall ev, In ev tr -> exists logIdx strIdx c, ev = IOEvRecv logIdx strIdx c) ->
    trace_of_ostrace tr = TEnd.
  Proof.
    induction tr; cbn; intros Htr; auto.
    edestruct Htr as (? & ? & ? & ?); auto; subst; cbn; auto.
  Qed.

  Lemma mkRecvEvents_not_visible : forall cs logIdx,
    trace_of_ostrace (mkRecvEvents logIdx cs) = TEnd.
  Proof.
    intros; apply IOEvRecvs_not_visible; intros * Hin.
    apply in_mkRecvEvents in Hin.
    destruct Hin as (? & ? & ? & ? & ?); eauto.
  Qed.

  Lemma nil_trace_getc_trace : forall t t',
    nil_trace_case t t' <-> getc_trace_case t t' (-1).
  Proof.
    unfold nil_trace_case, getc_trace_case; intuition (auto; easy).
  Qed.

  Lemma nil_trace_putc_trace : forall t t' c,
    nil_trace_case t t' <-> putc_trace_case t t' c (-1).
  Proof.
    unfold nil_trace_case, putc_trace_case; intuition auto.
    pose proof (Z.mod_pos_bound c 256 ltac:(lia)); lia.
  Qed.

  Lemma nil_trace_case_refl : forall st, nil_trace_case st st.
  Proof.
    red; intros; unfold strip_common_prefix.
    rewrite common_prefix_full, leb_correct, skipn_exact_length; cbn; auto.
  Qed.

  Local Hint Resolve nil_trace_case_refl : core.

  Corollary getc_trace_case_refl : forall st, getc_trace_case st st (-1).
  Proof. intros; rewrite <- nil_trace_getc_trace; auto. Qed.

  Corollary putc_trace_case_refl : forall st c, putc_trace_case st st c (-1).
  Proof. intros; rewrite <- nil_trace_putc_trace; auto. Qed.

  Local Hint Resolve getc_trace_case_refl : core.
  Local Hint Resolve putc_trace_case_refl : core.

  Lemma getc_trace_case_trans : forall t t' t'' r,
    nil_trace_case t t' ->
    getc_trace_case t' t'' r ->
    getc_trace_case t t'' r.
  Proof.
    intros * Htr Htr'; red.
    destruct Htr as (Heq & Htr), Htr' as (Heq' & Htr'); subst.
    apply common_prefix_correct in Heq; apply common_prefix_correct in Heq'.
    destruct Heq, Heq'; subst.
    unfold strip_common_prefix in *.
    rewrite !app_length, leb_correct in * by lia.
    rewrite <- app_assoc.
    rewrite common_prefix_app, skipn_app1, skipn_exact_length in *;
      rewrite ?app_length; auto; cbn in *.
    rewrite trace_of_ostrace_app.
    rewrite Htr; destruct Htr' as [(? & ->) | ?]; subst; auto.
  Qed.

  Lemma getc_trace_case_trans' : forall t t' t'' r,
    getc_trace_case t t' r ->
    nil_trace_case t' t'' ->
    getc_trace_case t t'' r.
  Proof.
    intros * Htr Htr'; red.
    destruct Htr as (Heq & Htr), Htr' as (Heq' & Htr'); subst.
    apply common_prefix_correct in Heq; apply common_prefix_correct in Heq'.
    destruct Heq, Heq'; subst.
    unfold strip_common_prefix in *.
    rewrite !app_length, leb_correct in * by lia.
    rewrite <- app_assoc.
    rewrite common_prefix_app, skipn_app1, skipn_exact_length in *;
      rewrite ?app_length; auto; cbn in *.
    rewrite trace_of_ostrace_app.
    rewrite Htr'; destruct Htr as [(? & ->) | (? & ->)]; subst; auto; constructor.
  Qed.

  Corollary nil_trace_case_trans : forall t t' t'',
    nil_trace_case t t' ->
    nil_trace_case t' t'' ->
    nil_trace_case t t''.
  Proof.
    intros * ?; rewrite !nil_trace_getc_trace; eauto using getc_trace_case_trans.
  Qed.

  Lemma putc_trace_case_trans : forall t t' t'' c r,
    nil_trace_case t t' ->
    putc_trace_case t' t'' c r ->
    putc_trace_case t t'' c r.
  Proof.
    intros * Htr Htr'; red.
    destruct Htr as (Heq & Htr), Htr' as (Heq' & Htr'); subst.
    apply common_prefix_correct in Heq; apply common_prefix_correct in Heq'.
    destruct Heq, Heq'; subst.
    unfold strip_common_prefix in *.
    rewrite !app_length, leb_correct in * by lia.
    rewrite <- app_assoc.
    rewrite common_prefix_app, skipn_app1, skipn_exact_length in *;
      rewrite ?app_length; auto; cbn in *.
    rewrite trace_of_ostrace_app.
    pose proof (Z.mod_pos_bound c 256 ltac:(lia)).
    rewrite Htr; destruct Htr' as [(? & ->) | ?]; subst; auto.
  Qed.

  Lemma putc_trace_case_trans' : forall t t' t'' c r,
    putc_trace_case t t' c r ->
    nil_trace_case t' t'' ->
    putc_trace_case t t'' c r.
  Proof.
    intros * Htr Htr'; red.
    destruct Htr as (Heq & Htr), Htr' as (Heq' & Htr'); subst.
    apply common_prefix_correct in Heq; apply common_prefix_correct in Heq'.
    destruct Heq, Heq'; subst.
    unfold strip_common_prefix in *.
    rewrite !app_length, leb_correct in * by lia.
    rewrite <- app_assoc.
    rewrite common_prefix_app, skipn_app1, skipn_exact_length in *;
      rewrite ?app_length; auto; cbn in *.
    rewrite trace_of_ostrace_app.
    pose proof (Z.mod_pos_bound c 256 ltac:(lia)).
    rewrite Htr'; destruct Htr as [(? & ->) | (? & ->)]; subst; auto.
  Qed.

  Lemma cons_intr_aux_trace_case : forall st st',
    cons_intr_aux st = Some st' ->
    nil_trace_case st.(io_log) st'.(io_log).
  Proof.
    unfold cons_intr_aux, nil_trace_case; intros * Hspec; destruct_spec Hspec.
    - prename (Coqlib.zeq _ _ = _) into Htmp; clear Htmp.
      destruct st; cbn in *; subst; cbn in *.
      rewrite common_prefix_app, app_length, leb_correct by lia.
      rewrite skipn_app1, skipn_exact_length; cbn; auto using mkRecvEvents_not_visible.
    - prename (Coqlib.zeq _ _ = _) into Htmp; clear Htmp.
      destruct st; cbn in *; subst; cbn in *.
      rewrite common_prefix_app, app_length, leb_correct by lia.
      rewrite skipn_app1, skipn_exact_length; cbn; auto using mkRecvEvents_not_visible.
  Qed.

  Lemma serial_intr_enable_aux_trace_case : forall n st st',
    serial_intr_enable_aux n st = Some st' ->
    nil_trace_case st.(io_log) st'.(io_log).
  Proof.
    induction n; intros * Hspec; cbn -[cons_intr_aux] in Hspec; inj; auto.
    destruct_spec Hspec; auto.
    prename cons_intr_aux into Hspec'.
    eapply nil_trace_case_trans; [eapply cons_intr_aux_trace_case |]; eauto.
  Qed.

  Lemma serial_intr_enable_trace_case : forall st st',
    serial_intr_enable_spec st = Some st' ->
    nil_trace_case st.(io_log) st'.(io_log).
  Proof.
    unfold serial_intr_enable_spec; intros * Hspec; destruct_spec Hspec.
    prename serial_intr_enable_aux into Hspec.
    eapply serial_intr_enable_aux_trace_case in Hspec.
    destruct st, r; auto.
  Qed.

  Lemma serial_intr_disable_aux_trace_case : forall n mask st st',
    serial_intr_disable_aux n mask st = Some st' ->
    nil_trace_case st.(io_log) st'.(io_log).
  Proof.
    induction n; intros * Hspec; cbn -[cons_intr_aux] in Hspec; inj; auto.
    destruct_spec Hspec; auto.
    - eapply IHn in Hspec.
      destruct st, st'; cbn in *.
      prename serial_intr into Hspec'.
      unfold serial_intr in Hspec'; destruct_spec Hspec'.
      destruct o; [| rewrite app_nil_r in Hspec; auto].
      destruct Hspec as (Heq & Htr).
      apply common_prefix_correct in Heq.
      destruct Heq; subst; red.
      rewrite <- Htr; unfold strip_common_prefix.
      rewrite common_prefix_app, <- app_assoc, common_prefix_app.
      rewrite !app_length, !leb_correct by (cbn; lia).
      rewrite skipn_app1, skipn_exact_length; auto.
      rewrite (app_assoc io_log), <- app_length.
      rewrite skipn_app1, skipn_exact_length; cbn; auto.
    - prename cons_intr_aux into Hspec'.
      eapply cons_intr_aux_trace_case in Hspec'.
      eapply IHn in Hspec.
      eapply nil_trace_case_trans; [| eapply Hspec]; eauto.
      destruct st, r, st'; cbn in *.
      prename serial_intr into Hspec''.
      unfold serial_intr in Hspec''; destruct_spec Hspec''.
      destruct o; [| rewrite app_nil_r in Hspec'; auto].
      destruct Hspec' as (Heq & Htr).
      apply common_prefix_correct in Heq.
      destruct Heq; subst; red.
      rewrite <- Htr; unfold strip_common_prefix.
      rewrite common_prefix_app, <- app_assoc, common_prefix_app.
      rewrite !app_length, !leb_correct by (cbn; lia).
      rewrite skipn_app1, skipn_exact_length; auto.
      rewrite (app_assoc io_log), <- app_length.
      rewrite skipn_app1, skipn_exact_length; cbn; auto.
  Qed.

  Lemma serial_intr_disable_trace_case : forall st st',
    serial_intr_disable_spec st = Some st' ->
    nil_trace_case st.(io_log) st'.(io_log).
  Proof.
    unfold serial_intr_disable_spec; intros * Hspec; destruct_spec Hspec.
    prename serial_intr_disable_aux into Hspec.
    eapply serial_intr_disable_aux_trace_case in Hspec.
    destruct st, r; auto.
  Qed.

  Lemma thread_serial_intr_enable_trace_case : forall st st',
    thread_serial_intr_enable_spec st = Some st' ->
    nil_trace_case st.(io_log) st'.(io_log).
  Proof.
    unfold thread_serial_intr_enable_spec; intros * Hspec; destruct_spec Hspec.
    eapply serial_intr_enable_trace_case; eauto.
  Qed.

  Lemma thread_serial_intr_disable_trace_case : forall st st',
    thread_serial_intr_disable_spec st = Some st' ->
    nil_trace_case st.(io_log) st'.(io_log).
  Proof.
    unfold thread_serial_intr_disable_spec; intros * Hspec; destruct_spec Hspec.
    eapply serial_intr_disable_trace_case; eauto.
  Qed.

  Lemma uctx_set_retval1_trace_case : forall st v st',
    uctx_set_retval1_spec v st = Some st' ->
    nil_trace_case st.(io_log) st'.(io_log).
  Proof.
    unfold uctx_set_retval1_spec; intros * Hspec; destruct_spec Hspec.
    destruct st; auto.
  Qed.

  Lemma uctx_set_errno_trace_case : forall st e st',
    uctx_set_errno_spec e st = Some st' ->
    nil_trace_case st.(io_log) st'.(io_log).
  Proof.
    unfold uctx_set_errno_spec; intros * Hspec; destruct_spec Hspec.
    destruct st; auto.
  Qed.

  Lemma serial_putc_putc_trace_case : forall st c st' r,
    serial_putc_spec c st = Some (st', r) ->
    putc_trace_case st.(io_log) st'.(io_log) c r.
  Proof.
    unfold serial_putc_spec; intros * Hspec; destruct_spec Hspec; eauto.
    - prename (Coqlib.zeq _ _ = _) into Htmp; clear Htmp.
      destruct st; cbn in *; subst; red.
      unfold strip_common_prefix.
      rewrite !app_length, leb_correct by lia.
      rewrite common_prefix_app, skipn_app1, skipn_exact_length; auto.
    - prename (Coqlib.zeq _ _ = _) into Htmp; clear Htmp.
      destruct st; cbn in *; subst; red.
      unfold strip_common_prefix.
      rewrite !app_length, leb_correct by lia.
      rewrite common_prefix_app, skipn_app1, skipn_exact_length; auto.
  Qed.

  Lemma cons_buf_read_trace_case : forall st st' c,
    valid_trace st ->
    cons_buf_read_spec st = Some (st', c) ->
    getc_trace_case st.(io_log) st'.(io_log) c /\ -1 <= c <= 255.
  Proof.
    unfold cons_buf_read_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    { split; eauto; lia. }
    prename (cons_buf _ = _) into Hcons.
    destruct st; cbn in *; unfold getc_trace_case.
    unfold strip_common_prefix.
    rewrite common_prefix_app, app_length, leb_correct by lia.
    rewrite skipn_app1, skipn_exact_length; cbn; auto.
    inv Hvalid; cbn in *.
    rewrite vt_trace_console0 in Hcons.
    assert (Hin: In (c, z0, n) (compute_console io_log)) by (rewrite Hcons; cbn; auto).
    apply in_console_in_trace in Hin.
    apply in_split in Hin; destruct Hin as (? & ? & ?); subst.
    edestruct vt_trace_serial0 as (_ & Henv); eauto.
    destruct (SerialEnv z0) eqn:Hrange; try easy.
    apply SerialRecv_in_range in Hrange.
    rewrite Forall_forall in Hrange.
    apply nth_error_In in Henv.
    apply Hrange in Henv.
    split; auto; lia.
  Qed.

  Lemma thread_serial_putc_trace_case : forall st c st' r,
    thread_serial_putc_spec c st = Some (st', r) ->
    putc_trace_case st.(io_log) st'.(io_log) c r.
  Proof.
    unfold thread_serial_putc_spec; intros * Hspec; destruct_spec Hspec.
    eapply serial_putc_putc_trace_case; eauto.
  Qed.

  Lemma thread_cons_buf_read_trace_case : forall st st' c,
    valid_trace st ->
    thread_cons_buf_read_spec st = Some (st', c) ->
    getc_trace_case st.(io_log) st'.(io_log) c /\ -1 <= c <= 255.
  Proof.
    unfold thread_cons_buf_read_spec; intros * Hvalid Hspec; destruct_spec Hspec.
    eapply cons_buf_read_trace_case; eauto.
  Qed.

  Lemma sys_getc_trace_case : forall st st' ret,
    valid_trace st ->
    sys_getc_spec st = Some st' ->
    get_sys_ret st' = Vint ret ->
    getc_trace_case st.(io_log) st'.(io_log) (Int.signed ret).
  Proof.
    unfold sys_getc_spec, get_sys_ret; intros * Hvalid Hspec Hret; destruct_spec Hspec.
    prename thread_serial_intr_disable_spec into Hspec1.
    prename thread_cons_buf_read_spec into Hspec2.
    prename thread_serial_intr_enable_spec into Hspec3.
    prename uctx_set_retval1_spec into Hspec4.
    assert (valid_trace r) by eauto using thread_serial_intr_disable_preserve_valid_trace.
    assert (valid_trace r0) by eauto using thread_cons_buf_read_preserve_valid_trace.
    assert (valid_trace r1) by eauto using thread_serial_intr_enable_preserve_valid_trace.
    assert (valid_trace r2) by eauto using uctx_set_retval1_preserve_valid_trace.
    assert (valid_trace st') by eauto using uctx_set_errno_preserve_valid_trace.
    eapply thread_serial_intr_disable_trace_case in Hspec1 as Htr.
    eapply thread_cons_buf_read_trace_case in Hspec2 as (Htr1 & Hrange); auto.
    eapply thread_serial_intr_enable_trace_case in Hspec3 as Htr2.
    eapply uctx_set_retval1_trace_case in Hspec4 as Htr3.
    eapply uctx_set_errno_trace_case in Hspec as Htr4.
    eapply getc_trace_case_trans'; [| eapply Htr4].
    eapply getc_trace_case_trans'; [| eapply Htr3].
    eapply getc_trace_case_trans'; [| eapply Htr2].
    eapply getc_trace_case_trans; [eapply Htr |]; eauto.
    enough (z = Int.signed ret); subst; auto.
    clear -Hspec Hspec4 Hret Htr1 Hrange.
    unfold uctx_set_retval1_spec in Hspec4; destruct_spec Hspec4.
    unfold uctx_set_errno_spec in Hspec; destruct_spec Hspec.
    destruct r1; cbn in *; subst.
    repeat (rewrite ZMap.gss in Hret || rewrite ZMap.gso in Hret by easy); inj.
    rewrite Int.signed_repr; auto; cbn; lia.
  Qed.

  Lemma sys_putc_trace_case : forall st st' c ret,
    sys_putc_spec st = Some st' ->
    get_sys_arg1 st = Vint c ->
    get_sys_ret st' = Vint ret ->
    putc_trace_case st.(io_log) st'.(io_log) (Int.unsigned c) (Int.signed ret).
  Proof.
    unfold sys_putc_spec, get_sys_arg1, get_sys_ret; intros * Hspec Harg Hret; destruct_spec Hspec.
    prename thread_serial_intr_disable_spec into Hspec1.
    prename thread_serial_putc_spec into Hspec2.
    prename thread_serial_intr_enable_spec into Hspec3.
    prename uctx_set_retval1_spec into Hspec4.
    prename uctx_arg2_spec into Hspec5.
    eapply thread_serial_intr_disable_trace_case in Hspec1 as Htr.
    eapply thread_serial_putc_trace_case in Hspec2 as (Htr1 & Hrange); auto.
    eapply thread_serial_intr_enable_trace_case in Hspec3 as Htr2.
    eapply uctx_set_retval1_trace_case in Hspec4 as Htr3.
    eapply uctx_set_errno_trace_case in Hspec as Htr4.
    eapply putc_trace_case_trans'; [| eapply Htr4].
    eapply putc_trace_case_trans'; [| eapply Htr3].
    eapply putc_trace_case_trans'; [| eapply Htr2].
    eapply putc_trace_case_trans; [eapply Htr |]; eauto.
    enough (z0 = Int.signed ret /\ z = Int.unsigned c) as (? & ?); subst; [split; auto |].
    clear -Hspec Hspec4 Hspec5 Harg Hret Htr1 Hrange.
    unfold uctx_set_retval1_spec in Hspec4; destruct_spec Hspec4.
    unfold uctx_set_errno_spec in Hspec; destruct_spec Hspec.
    unfold uctx_arg2_spec in Hspec5; destruct_spec Hspec5.
    destruct r1; cbn in *; subst.
    repeat (rewrite ZMap.gss in Hret || rewrite ZMap.gso in Hret by easy); inj.
    rewrite Int.signed_repr; auto; cbn; try lia.
    pose proof (Z.mod_pos_bound (Int.unsigned c) 256 ltac:(lia)).
    destruct Hrange as [(? & ?) | (? & ?)]; lia.
  Qed.

End Invariants.

Section SpecsCorrect.

  Context `{ThreadsConfigurationOps}.

  Definition user_trace (ot ot' : ostrace) : trace :=
    trace_of_ostrace (strip_common_prefix IOEvent_eq ot ot').

  Definition trace_itree_match (z0 z : IO_itree) (ot ot' : ostrace) :=
    (* Compute the OS-generated trace of newly added events *)
    let ot_new := strip_common_prefix IOEvent_eq ot ot' in
    (* Filter out the user-invisible events *)
    let t := trace_of_ostrace ot_new in
    (* The new itree 'consumed' the OS-generated trace *)
    consume_trace z0 z t.

  Import Mem.
  Variable block_to_addr : block -> Z.

  Definition mem_to_flatmem (f : flatmem) (m : mem) (b : block) (ofs len : Z) : flatmem :=
    let contents := getN (Z.to_nat len) ofs (m.(mem_contents) !! b) in
    let addr := block_to_addr b + ofs in
    FlatMem.setN contents addr f.

  Program Definition flatmem_to_mem (f : flatmem) (m : mem) (b : block) (ofs len : Z) : mem :=
    let (cont, acc, nxt, amax, nxt_no, _) := m in
    let addr := block_to_addr b + ofs in
    let bytes := FlatMem.getN (Z.to_nat len) addr f in
    let contents := setN bytes ofs (cont !! b) in
    mkmem (PMap.set b contents cont) acc nxt amax nxt_no _.
  Next Obligation.
    cbn; intros; destruct (Pos.eq_dec b b0) eqn:?; subst.
    - rewrite PMap.gss, setN_default; auto.
    - rewrite PMap.gso; auto.
  Defined.

  Record R_sys_getc_correct k z m st st' ret := {
    (* New itree is old k applied to result, or same as old itree if nothing
       to read *)
    getc_z' := if 0 <=? Int.signed ret then k (Byte.repr (Int.signed ret)) else z;

    (* Post condition holds on new state, itree, and result *)
    getc_post_ok : getchar_post' m m ret (k, z) getc_z';
    (* The itrees and OS traces agree on the external events *)
    getc_itree_trace_ok : trace_itree_match z getc_z' st.(io_log) st'.(io_log);
    (* The new trace is valid *)
    getc_trace_ok : valid_trace st';
    (* The memory is unchanged *)
    getc_mem_ok : st.(HP) = st'.(HP)
  }.

  Lemma sys_getc_correct k z m st st' :
    (* Initial trace is valid *)
    valid_trace st ->
    (* Pre condition holds *)
    getchar_pre' m k z ->
    (* sys_getc returns some state *)
    sys_getc_spec st = Some st' ->
    exists ret,
      get_sys_ret st' = Vint ret /\
      R_sys_getc_correct k z m st st' ret.
  Proof.
    unfold getchar_pre', get_sys_ret; intros Hvalid Hpre Hspec.
    apply sys_getc_preserve_valid_trace in Hspec as Hvalid'; auto.
    apply sys_getc_mem_unchanged in Hspec as Hmem.
    pose proof Hspec as Htrace_case.
    unfold sys_getc_spec in Hspec; destruct_spec Hspec.
    prename (thread_cons_buf_read_spec) into Hread.
    apply thread_cons_buf_read_trace_case in Hread as (_ & ?).
    2: eapply (thread_serial_intr_disable_preserve_valid_trace st); eauto.
    unfold uctx_set_errno_spec in Hspec; destruct_spec Hspec.
    prename (uctx_set_retval1_spec) into Hspec.
    unfold uctx_set_retval1_spec in Hspec; destruct_spec Hspec.
    destruct r1; cbn in *.
    repeat (rewrite ZMap.gss in * || rewrite ZMap.gso in * by easy); subst; inj.
    do 2 esplit; eauto.
    eapply sys_getc_trace_case in Htrace_case; eauto.
    2: unfold get_sys_ret; cbn; repeat (rewrite ZMap.gss || rewrite ZMap.gso by easy); auto.
    constructor; eauto; hnf.
    - (* getchar_post *)
      split; auto; cbn in *.
      rewrite Int.signed_repr by (cbn; lia).
      destruct (Coqlib.zeq z0 (-1)); subst; auto.
      left; split; try lia.
      rewrite Zle_imp_le_bool by lia; auto.
    - (* trace_itree_match *)
      rewrite Int.signed_repr in * by (cbn; lia).
      cbn in *; destruct Htrace_case as (Htr & Hcase).
      intros * Htrace; cbn.
      destruct Hcase as [(? & ->) | (? & Heq)]; subst; auto.
      rewrite Zle_imp_le_bool in Htrace by lia.
      unshelve erewrite Heq; try solve [constructor].
      apply Hpre.
      hnf; cbn; repeat constructor; auto.
  Qed.

  Record R_sys_putc_correct c k z m st st' ret := {
    (* New itree is old k, or same as old itree if send failed *)
    putc_z' := if 0 <=? Int.signed ret then k else z;

    (* Post condition holds on new state, itree, and result *)
    putc_post_ok : putchar_post m m ret (c, k) putc_z';
    (* The itrees and OS traces agree on the external events *)
    putc_itree_trace_ok : trace_itree_match z putc_z' st.(io_log) st'.(io_log);
    (* The new trace is valid *)
    (* TODO: have to define valid trace condition for putc *)
    putc_trace_ok : valid_trace st';
    (* The memory is unchanged *)
    putc_mem_ok : st.(HP) = st'.(HP)
  }.

Import functional_base.

  Lemma sys_putc_correct c k z m st st' :
    (* Initial trace is valid *)
    valid_trace st ->
    (* Pre condition holds *)
    putchar_pre m (c, k) z ->
    (* c is passed as an argument *)
    get_sys_arg1 st = Vubyte c ->
    (* sys_putc returns some state *)
    sys_putc_spec st = Some st' ->
    exists ret,
      get_sys_ret st' = Vint ret /\
      R_sys_putc_correct c k z m st st' ret.
  Proof.
    unfold putchar_pre, get_sys_arg1, get_sys_ret; intros Hvalid Hpre Harg Hspec.
    apply sys_putc_mem_unchanged in Hspec as Hmem.
    pose proof (sys_putc_preserve_valid_trace _ _ Hvalid Hspec).
    pose proof Hspec as Htrace_case.
    unfold sys_putc_spec in Hspec; destruct_spec Hspec.
    prename (thread_serial_putc_spec) into Hput.
    apply thread_serial_putc_trace_case in Hput.
    assert (-1 <= z1 <= 255).
    { pose proof (Z.mod_pos_bound z0 256 ltac:(lia)).
      destruct Hput as (? & [(? & ?) | (? & ?)]); subst; lia.
    }
    unfold uctx_set_errno_spec in Hspec; destruct_spec Hspec.
    prename (uctx_set_retval1_spec) into Hspec.
    unfold uctx_set_retval1_spec in Hspec; destruct_spec Hspec.
    prename (uctx_arg2_spec) into Hspec.
    unfold uctx_arg2_spec in Hspec; destruct_spec Hspec.
    destruct r1; cbn in *.
    repeat (rewrite ZMap.gss in * || rewrite ZMap.gso in * by easy); subst; inj.
    do 2 esplit; eauto.
    eapply sys_putc_trace_case in Htrace_case; eauto.
    2: unfold get_sys_ret; cbn; repeat (rewrite ZMap.gss || rewrite ZMap.gso by easy); auto.
    pose proof (Byte.unsigned_range_2 c).
    rewrite Int.unsigned_repr in * by functional_base.rep_lia.
    constructor; eauto; hnf.
    - (* putchar_post *)
      split; auto; cbn in *.
      rewrite Int.signed_repr by (cbn; lia).
      destruct (Coqlib.zeq z1 (-1)); subst; auto.
      destruct (eq_dec.eq_dec _ _); try easy.
      rewrite Zle_imp_le_bool by lia.
      destruct Hput as (? & [(? & ?) | (? & ?)]); subst; auto; try lia.
      rewrite Zmod_small; auto; functional_base.rep_lia.
    - (* trace_itree_match *)
      rewrite Int.signed_repr in * by (cbn; lia).
      cbn in *; destruct Htrace_case as (Htr & Hcase).
      intros * Htrace; cbn.
      destruct Hcase as [(? & ->) | (? & Heq)]; subst; auto.
      pose proof (Z.mod_pos_bound (Byte.unsigned c) 256 ltac:(lia)).
      rewrite Zle_imp_le_bool in Htrace by lia.
      unshelve erewrite Heq; try solve [constructor].
      eapply Traces.sutt_trace_incl; eauto; cbn.
      rewrite Byte.repr_unsigned.
      hnf; cbn; repeat constructor; auto.
  Qed.

  (* TODO: memory *)
  Record R_sys_getcs_correct sh buf len k z m st st' ret := {
    vals := nil; (* TODO *)
    getcs_z' := if 0 <=? Int.signed ret then k vals else z;

    (* Post condition holds on new state, itree, and result *)
    getcs_post_ok : getchars_post m m ret (sh, buf, len, k) getcs_z';
    (* The itrees and OS traces agree on the external events *)
    getcs_itree_trace_ok : trace_itree_match z getcs_z' st.(io_log) st'.(io_log);
    (* The new trace is valid *)
    getcs_trace_ok : valid_trace st';
    (* The memory has changed *)
    (* TODO *)
    (* getcs_mem_ok : st.(HP) = st'.(HP) *)
  }.

  Lemma sys_getcs_correct sh buf ofs len k z m st st' :
    let addr := block_to_addr buf + Ptrofs.unsigned ofs in
    (* Initial trace is valid *)
    valid_trace st ->
    (* Pre condition holds *)
    getchars_pre m (sh, Vptr buf ofs, len, k) z ->
    (* addr and len are passed as arguments *)
    get_sys_arg1 st = Vint (Int.repr addr) ->
    get_sys_arg2 st = Vint (Int.repr len) ->
    (* sys_getcs returns some state *)
    sys_getcs_spec st = Some st' ->
    exists ret,
      get_sys_ret st' = Vint ret /\
      R_sys_getcs_correct sh (Vptr buf ofs) len k z m st st' ret.
  Proof.
    unfold getchars_pre, get_sys_ret; intros Hvalid Hpre Harg1 Harg2 Hspec.
    apply sys_getcs_preserve_valid_trace in Hspec as Hvalid'; auto.
    (* pose proof Hspec as Htrace_case. *)
    unfold sys_getcs_spec in Hspec; destruct_spec Hspec.
    prename (thread_cons_buf_read_loop_spec) into Hread.
    (* apply thread_cons_buf_read_getcs_trace_case in Hread as (_ & ?). *)
    (* 2: eapply (thread_serial_intr_disable_preserve_valid_trace st); eauto. *)
    unfold uctx_set_errno_spec in Hspec; destruct_spec Hspec.
    prename (uctx_set_retval1_spec) into Hspec.
    unfold uctx_set_retval1_spec in Hspec; destruct_spec Hspec.
    prename (uctx_arg2_spec) into Hspec.
    unfold uctx_arg2_spec in Hspec; destruct_spec Hspec.
    prename (uctx_arg3_spec) into Hspec.
    unfold uctx_arg3_spec in Hspec; destruct_spec Hspec.
    destruct r1; cbn in *.
    repeat (rewrite ZMap.gss in * || rewrite ZMap.gso in * by easy); subst; inj.
    do 2 esplit; eauto.
    (* eapply sys_putc_trace_case in Htrace_case; eauto. *)
    (* 2: unfold get_sys_ret; cbn; repeat (rewrite ZMap.gss || rewrite ZMap.gso by easy); auto. *)
    constructor; eauto; hnf.
    - (* getchars_post *)
      admit.
    - (* trace_itree_match *)
      admit.
  Admitted.

End SpecsCorrect.
