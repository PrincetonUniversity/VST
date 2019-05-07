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

Section CommonPrefix.

  Context {A: Type}.
  Variable Aeq : forall (x y : A), {x = y} + {x <> y}.

  Fixpoint common_prefix (xs ys : list A) : list A :=
    match xs, ys with
    | x :: xs', y :: ys' =>
      if Aeq x y then x :: common_prefix xs' ys' else nil
    | _, _ => nil
    end.

  Definition split_at_common_prefix (xs ys : list A) : list A * list A :=
    let i := length (common_prefix xs ys) in
    let pre := firstn i xs in
    let post := if length xs <=? length ys then skipn i ys else skipn i xs in
    (pre, post).

  Lemma common_prefix_sym : forall xs ys,
    common_prefix xs ys = common_prefix ys xs.
  Proof.
    induction xs as [| x xs]; destruct ys as [| y ys]; cbn; auto.
    destruct (Aeq x y), (Aeq y x); congruence.
  Qed.

  Lemma common_prefix_correct : forall xs ys,
    let pre := common_prefix xs ys in
    pre = firstn (length pre) xs.
  Proof.
    induction xs as [| x xs]; destruct ys as [| y ys]; cbn; auto.
    destruct (Aeq x y); cbn; congruence.
  Qed.

  Lemma split_at_common_prefix_correct : forall xs ys,
    length xs <= length ys ->
    let (pre, post) := split_at_common_prefix xs ys in
    ys = pre ++ post.
  Proof.
    induction xs as [| x xs]; destruct ys as [| y ys]; cbn; intros; auto; try lia.
    rewrite leb_correct by lia.
    destruct (Aeq x y); cbn; subst; auto.
    rewrite <- common_prefix_correct.
    rewrite common_prefix_sym.
    rewrite common_prefix_correct at 1.
    rewrite firstn_skipn.
    auto.
  Qed.

  Fact list_eq_in_or : forall (xs ys xs' ys' : list A) x y,
    xs ++ x :: xs' = ys ++ y :: ys' ->
    x <> y ->
    In y xs \/ In y xs'.
  Proof.
    induction xs; destruct ys; cbn; intros * Heq Hneq; inj; eauto.
    - rewrite in_app_iff; cbn; auto.
    - cut (In y xs \/ In y xs'); eauto.
      intuition auto.
  Qed.

  Fact list_eq_in_l : forall (xs ys ys' : list A) x y,
    xs ++ x :: nil = ys ++ y :: ys' ->
    x <> y ->
    In y xs.
  Proof.
    intros.
    cut (In y xs \/ In y nil); [intuition |].
    eapply list_eq_in_or; eauto.
  Qed.

  Fact list_eq_in_r : forall (xs' ys ys' : list A) x y,
    x :: xs' = ys ++ y :: ys' ->
    x <> y ->
    In y xs'.
  Proof.
    intros.
    cut (In y nil \/ In y xs'); [intuition |].
    eapply list_eq_in_or; eauto.
  Qed.

  Fact list_unique_match : forall (xs ys xs' ys': list A) x,
    xs ++ x :: xs' = ys ++ x :: ys' ->
    NoDup (xs ++ x :: xs') ->
    xs = ys /\ xs' = ys'.
  Proof.
    induction xs; destruct ys; cbn; intros * Heq Huniq; inj; inv Huniq; auto.
    - rewrite in_app_iff in *; cbn in *.
      intuition.
    - rewrite in_app_iff in *; cbn in *.
      intuition.
    - cut (xs = ys /\ xs' = ys'); eauto.
      intuition congruence.
  Qed.

End CommonPrefix.

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
  Context {Hclen : ConsoleLen}.

  Class SerialOracle := {
    serial_oracle : etrace -> Z;
    serial_oracle_in_range : forall tr,
      0 <= serial_oracle tr <= 255
  }.
  Context {Horacle : SerialOracle}.

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
                         else skipn 1 cons in
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

  (** Invariants *)
  (* Everything in the trace was put there by the serial device. *)
  Definition valid_trace_serial tr :=
    forall ridx c,
      In (ETReadOS ridx c) tr ->
      exists tr',
        serial_oracle tr' = c /\ length tr' = ridx /\
        Zlength tr' <= Zlength tr /\
        let lo := Z.max 0 (Zlength tr - (Zlength tr' + 1)) in
        sublist lo (Zlength tr) tr = ETReadOS ridx c :: tr'.

  (* Every user read has a matching OS read earlier in the trace. *)
  Definition valid_trace_user tr :=
    forall ridx c pre post,
      tr = post ++ (ETReadUser ridx c) :: pre ->
      In (ETReadOS ridx c) pre /\ hd_error (compute_console pre) = Some (c, ridx).

  (* Every event in the trace is unique. *)
  Definition valid_trace_unique (tr : etrace) := NoDup tr.

  (* Everything in the console buffer is also in the trace. *)
  Definition valid_console tr :=
    forall ridx c,
      In (c, ridx) (compute_console tr) ->
      In (ETReadOS ridx c) tr.

  (* The console buffer never overflows *)
  Definition valid_console_len tr :=
    Zlength (compute_console tr) <= CONSOLE_MAX_LEN.

  Record valid_state st := {
    valid_state_trace_serial : valid_trace_serial st.(st_trace);
    (* Every user read has a matching OS read earlier in the trace. *)
    valid_state_trace_user : valid_trace_user st.(st_trace);
    (* Every event in the trace is unique. *)
    valid_state_trace_unique : valid_trace_unique st.(st_trace);
    (* Everything in the console buffer is also in the trace. *)
    valid_state_console : valid_console st.(st_trace);
    (* The console buffer never overflows *)
    valid_state_console_len : valid_console_len st.(st_trace);
  }.

  Lemma hd_error_app {A} : forall (xs ys : list A) x,
    hd_error xs = Some x ->
    hd_error (xs ++ ys) = Some x.
  Proof.
    destruct xs; cbn; easy.
  Qed.

  Lemma compute_console_ridx_increase : forall tr ev ridx c ridx' c',
    let cons := compute_console tr in
    let cons' := compute_console (ev :: tr) in
    valid_console (ev :: tr) ->
    valid_trace_serial (ev :: tr) ->
    hd_error cons = Some (c, ridx) ->
    hd_error cons' = Some (c', ridx') ->
    (ridx <= ridx')%nat.
  Proof.
    destruct ev; intros * Hcons Htr Hhd Hhd'; red in Hcons, Htr; subst cons cons'; cbn in *.
    - destruct (_ <? _)eqn:Hlt; [rewrite Z.ltb_lt in Hlt | rewrite Z.ltb_nlt in Hlt].
      + erewrite hd_error_app in Hhd' by eauto; inj; auto.
      + pose proof console_len_pos.
        destruct (compute_console tr) eqn:Heq; cbn in *; inj; try lia.
        admit.
    - admit.
    - admit.
  Admitted.

  (* Lemma compute_console_ridx_increase : forall ridx c tr ridx' c', *)
  (*   let cons := compute_console tr in *)
  (*   let cons' := compute_console (ETReadUser ridx c :: tr) in *)
  (*   hd_error cons = Some (c', ridx') -> *)
  (*   (ridx' < ridx)%nat. *)
  (* Proof. *)
  (*   induction tr as [| ev tr]; cbn; intros * Hhd; [discriminate |]. *)
  (*   destruct ev; eauto. *)
  (*   - admit. *)
  (*   - eapply IHtr. *)
  (* Qed. *)

  Lemma serial_getc_preserve_trace_unique : forall st st',
    valid_state st ->
    serial_getc st = st' ->
    valid_trace_unique st'.(st_trace).
  Proof.
    unfold serial_getc; intros * Hvalid Hspec.
    destruct st as [? tr]; subst; destruct Hvalid; cbn in *.
    constructor; auto.
    intros * Hin.
    apply valid_state_trace_serial0 in Hin.
    destruct Hin as (? & ? & Hlen & ? & Hsub); cbn in Hsub.
    rewrite Z.max_l in Hsub
      by (rewrite !Zlength_correct, Hlen; lia).
    rewrite conclib.sublist_all in Hsub by easy.
    rewrite Hsub in Hlen; cbn in Hlen; lia.
  Qed.

  Lemma serial_getc_preserve_valid_state : forall st st',
    valid_state st ->
    serial_getc st = st' ->
    valid_state st'.
  Proof.
    unfold serial_getc; intros * Hvalid Hspec.
    pose proof Hvalid as Hvalid'.
    eapply serial_getc_preserve_trace_unique in Hvalid'; eauto.
    destruct st as [? tr]; subst; destruct Hvalid; cbn in *.
    split; cbn; red; auto.
    - (* valid_trace_serial *)
      rewrite !Zlength_cons.
      intros *; cbn.
      intuition eauto; inj.
      + repeat (esplit; eauto); try lia.
        rewrite Z.max_l by lia.
        rewrite conclib.sublist_all; auto.
        rewrite Zlength_cons; easy.
      + edestruct valid_state_trace_serial0 as (tr' & ? & ? & ? & Hsub); eauto; subst.
        repeat (esplit; eauto); try lia.
        rewrite <- Hsub.
        rewrite Z.max_r by lia.
        apply Z.max_case_strong; intros.
        * (* length tr <= length tr' + 1 *)
          rewrite Z.max_l in Hsub by lia; cbn in Hsub.
          rewrite conclib.sublist_all in Hsub by lia; subst.
          rewrite ?Zlength_cons in *.
          replace (Z.succ _ - (_ + 1)) with 1 by lia.
          rewrite conclib.sublist_S_cons by lia.
          f_equal; lia.
        * (* length tr' + 1 <= length tr *)
          rewrite Z.max_r in Hsub by lia; cbn in Hsub.
          rewrite conclib.sublist_S_cons by lia.
          f_equal; lia.
    - (* valid_trace_user *)
      intros * Heq.
      pose proof Heq as Heq'.
      apply list_eq_in_r in Heq'; try congruence.
      apply in_split in Heq'.
      destruct Heq' as (post' & pre' & ?); subst.
      rewrite app_comm_cons in Heq.
      apply list_unique_match in Heq; auto.
      destruct Heq as (? & ?); subst; eauto.
    - (* valid_console *)
      intros *; cbn.
      rewrite !in_app_iff, Zlength_correct; cbn.
      destruct (_ <? _) eqn:Hlt; [rewrite Z.ltb_lt in Hlt | rewrite Z.ltb_nlt in Hlt].
      + intuition (inj; auto).
      + red in valid_state_console0.
        destruct (compute_console tr); intuition (inj; auto; try easy).
        intuition.
    - (* valid_console_len *)
      red in valid_state_console_len0.
      repeat (rewrite ?Zlength_correct, ?app_length in *; cbn).
      pose proof console_len_pos.
      destruct (_ <? _) eqn:Hlt; [rewrite Z.ltb_lt in Hlt | rewrite Z.ltb_nlt in Hlt];
        try lia.
      destruct (compute_console tr); cbn in *; lia.
  Qed.

  Lemma console_read_preserve_trace_unique : forall st st' c,
    valid_state st ->
    console_read st = (st', c) ->
    valid_trace_unique st'.(st_trace).
  Proof.
    unfold console_read; intros * Hvalid Hspec.
    destruct st as [? tr]; destruct Hvalid; cbn in *.
    destruct (compute_console tr) as [| (c' & ridx) cons] eqn:Hcons; inj; red; cbn; auto.
    constructor; auto.
    intros Hin; apply in_split in Hin.
    destruct Hin as (post & pre & ?); subst.
    edestruct valid_state_trace_user0 as (Hin & Hhd); eauto.
    admit.
  Admitted.

  Definition new_trace (st st' : state) : etrace :=
    snd (split_at_common_prefix IO_trace_event_eq st.(st_trace) st'.(st_trace)).

  Definition valid_ret (st st' : state) (c : Z) :=
    (c = -1 \/ 0 <= c <= 255) /\ st.(st_mem) = st'.(st_mem) /\
    (c = -1 -> new_trace st st' = nil) /\
    (0 <= c <= 255 -> exists ridx, new_trace st st' = ETReadUser ridx c :: nil).

  Lemma console_read_preserve_valid_state : forall st st' c,
    valid_state st ->
    console_read st = (st', c) ->
    valid_state st' /\ valid_ret st st' c.
  Proof.
    admit.
  (*   unfold console_read; intros * Hvalid Hspec. *)
  (*   destruct st as [? [| (c' & ridx) cons] tr]; destruct Hvalid; inj; cbn in *. *)
  (*   { repeat (split; eauto). } *)
  (*   split; [split; red |]; rewrite ?Zlength_correct in *; cbn -[Z.of_nat] in *; *)
  (*     eauto; try lia. *)
  (*   - (1* valid_trace_serial *1) *)
  (*     intros *; rewrite in_app_iff; cbn. *)
  (*     intuition (try congruence). *)
  (*     edestruct valid_state_trace_serial0 as (tr' & ? & ? & Hsub); eauto; subst. *)
  (*     repeat (esplit; eauto). *)
  (*     rewrite sublist0_app1; auto. *)
  (*     replace (Zlength tr' + 1) *)
  (*       with (Zlength (tr' ++ ETReadOS (length tr') (serial_oracle tr') :: nil)) *)
  (*       by (rewrite Zlength_app; auto). *)
  (*     rewrite <- Hsub. *)
  (*     auto using conclib.sublist_max_length, Zlength_nonneg. *)
  (*   - (1* valid_trace_user *1) *)
  (*     intros ridx' c' * Heq. *)
  (*     assert (Hcase: ETReadUser ridx c = ETReadUser ridx' c' \/ *)
  (*                    ETReadUser ridx c <> ETReadUser ridx' c'). *)
  (*     { clear; repeat decide equality. } *)
  (*     destruct Hcase; inj. *)
  (*     + apply list_unique_match in Heq; auto. *)
  (*       { destruct Heq; subst; auto. *)
  (*         split. *)
  (*         - eapply valid_state_console0; cbn; auto. *)
  (*         - hnf in *. *)
  (*       } *)
  (*       apply conclib.NoDup_add; rewrite app_nil_r; auto. *)
  (*       intros Hin. *)
  (*       apply in_split in Hin. *)
  (*       destruct Hin as (pre' & post' & ?); subst. *)
  (*       assert (Hin: In (ETReadOS ridx' c') (pre' ++ ETReadUser ridx' c' :: post')). *)
  (*       { rewrite in_app_iff; left. *)
  (*         eapply valid_state_trace_user0; eauto. } *)
  (*       eapply valid_state_trace_serial0 in Hin. *)
  (*       destruct Hin as (? & ? & ? & ?); subst. *)
  (*       red in valid_state_console0. *)
  (*     + pose proof Heq as Heq'. *)
  (*       apply list_eq_in_l in Heq'; auto. *)
  (*       apply in_split in Heq'. *)
  (*       destruct Heq' as (pre' & post' & Heq''). *)
  (*       assert (In (ETReadOS ridx' c') pre'). *)
  (*       { apply valid_state_trace_user0 in Heq''; auto. } *)
  (*       subst. *)
  (*   - (1* valid_console *1) *)
  (*     intuition idtac. *)
  (*   - (1* c in range *1) *)
  (*     pose proof serial_oracle_in_range. *)
  (*     right; cut (exists tr, serial_oracle tr = c); eauto. *)
  (*     intros (? & ?); subst; eauto. *)
  Admitted.

  Lemma getchar_spec_preserve_valid_state : forall st st' c,
    valid_state st ->
    getchar_spec st = (st', c) ->
    valid_state st' /\ valid_ret st st' c.
  Proof.
    unfold getchar_spec; intros * Hvalid Hspec.
    destruct (console_read st) eqn:Hread.
    eapply console_read_preserve_valid_state in Hread; eauto.
    destruct (0 <=? _) eqn:Hle; inj; eauto.
    rewrite Z.leb_nle in Hle.
    destruct Hread as (? & ([? | ?] & ? & ? & ?)); subst; try lia.
    repeat (split; auto).
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

  Lemma getchar_correct k z st :
    (* Initial state is valid *)
    valid_state st ->
    (* Pre condition holds *)
    getchar_pre' st.(st_mem) k z ->
    exists st' r,
      (* Spec with same initial memory returns some state and result *)
      getchar_spec st = (st', r) /\
      (* Compute the newly added events *)
      let t' := new_trace st st' in
      (* New itree is old k applied to result, or same as old itree if nothing
         to read *)
      let z' := if 0 <=? r then k (Int.repr r) else z in
      (* Post condition holds on new state, itree, and result *)
      getchar_post' st.(st_mem) st'.(st_mem) (Int.repr r) (k, z) z' /\
      (* The new itree 'consumed' the generated trace *)
      consume_trace z z' t'.
  Proof.
    unfold getchar_pre'; intros Hval Hpre; cbn.
    destruct (getchar_spec st) as (st' & r) eqn:Hspec.
    eapply getchar_spec_preserve_valid_state in Hspec; auto.
    destruct Hspec as (Hval' & (Hr & Hmem & Htr & Htr')).
    exists st', r.
    repeat (split; auto).
    - destruct Hr; subst; auto.
      rewrite Int.signed_repr by (cbn; lia).
      rewrite Zle_imp_le_bool by lia.
      auto.
    - hnf; intros * Htrace.
      (* apply Hpre. *)
      destruct Hr; subst; cbn in *.
      + rewrite Htr; auto.
      + destruct Htr' as (? & ->); auto.
        apply Hpre.
        hnf; cbn.
        repeat constructor.
        rewrite Zle_imp_le_bool in Htrace by lia.
        apply Htrace.
  Qed.

End SpecsCorrect.
