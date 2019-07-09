Require Import VST.floyd.proofauto.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.initial_world.
Require Import VST.veric.ghost_PCM.
Require Import VST.veric.SequentialClight.
Require Import VST.veric.Clight_new.
Require Import VST.progs.conclib.
Require Import VST.sepcomp.semantics.
Require Import ITree.ITree.
(* Import ITreeNotations. *) (* one piece conflicts with subp notation *)
Notation "t1 >>= k2" := (ITree.bind t1 k2)
  (at level 50, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (ITree.bind t1 (fun x => t2))
  (at level 100, t1 at next level, right associativity) : itree_scope.
Notation "t1 ;; t2" := (ITree.bind t1 (fun _ => t2))
  (at level 100, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (ITree.bind t1 (fun x_ => match x_ with p => t2 end))
(at level 100, t1 at next level, p pattern, right associativity) : itree_scope.
Require Import ITree.Interp.Traces.
Require Import Ensembles.
Require Import VST.progs.io_dry.
Require Import VST.progs.io_os_connection.
Require Import VST.progs.io_os_specs.
Require Import VST.progs.os_combine.

Section IO_safety.

Context `{Config : ThreadsConfigurationOps}.
Variable (prog : Clight.program).

Definition ext_link := ext_link_prog prog.

Definition sys_getc_wrap_spec (abd : RData) : option (RData * val * trace) :=
  match sys_getc_spec abd with
  | Some abd' => Some (abd', get_sys_ret abd', trace_of_ostrace (strip_common_prefix IOEvent_eq abd.(io_log) abd'.(io_log)))
  | None => None
  end.

Definition sys_putc_wrap_spec (abd : RData) : option (RData * val * trace) :=
  match sys_putc_spec abd with
  | Some abd' => Some (abd', get_sys_ret abd', trace_of_ostrace (strip_common_prefix IOEvent_eq abd.(io_log) abd'.(io_log)))
  | None => None
  end.

Definition IO_ext_sem e (args : list val) s :=
  if oi_eq_dec (Some (ext_link "putchar"%string, funsig2signature ([(1%positive, tint)], tint) cc_default))
    (ef_id_sig ext_link e) then
    match sys_putc_wrap_spec s with
    | Some (s', ret, t') => Some (s', Some ret, t')
    | None => None
    end else
  if oi_eq_dec  (Some (ext_link "getchar"%string, funsig2signature ([], tint) cc_default))
    (ef_id_sig ext_link e) then
    match sys_getc_wrap_spec s with
    | Some (s', ret, t') => Some (s', Some ret, t')
    | None => None
    end
  else Some (s, None, TEnd).

Definition IO_inj_mem (m : mem) t s := valid_trace s /\ t = trace_of_ostrace s.(io_log). (* stub *)
Definition OS_mem (s : RData) : mem := Mem.empty. (* stub *)

Instance IO_Espec : OracleKind := io_specs.IO_Espec ext_link.

Definition lift_IO_event e := existT (fun X => option (io_specs.IO_event X * X)%type) (trace_event_rtype e) (io_event_of_io_tevent e).

Theorem IO_OS_soundness:
 forall {CS: compspecs} (initial_oracle: OK_ty) V G m,
   semax_prog_ext prog initial_oracle V G ->
   Genv.init_mem prog = Some m ->
   exists b, exists q, exists m',
     Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
     initial_core (cl_core_sem (globalenv prog))
         0 m q m' (Vptr b Ptrofs.zero) nil /\
   forall n, exists traces, ext_safeN_trace(J := OK_spec) prog IO_ext_sem IO_inj_mem OS_mem n TEnd traces initial_oracle q m' /\
     forall t, In _ traces t -> exists z', consume_trace initial_oracle z' t.
Proof.
  intros; eapply OS_soundness with (dryspec := io_dry_spec ext_link); eauto.
  - unfold IO_ext_sem; intros; simpl in *.
    destruct H2 as [Hvalid Htrace].
    if_tac; [|if_tac; [|contradiction]].
    + destruct w as (? & _ & ? & ?).
      destruct H1 as (? & ? & Hpre); subst.
      destruct s; simpl in *.
      unfold sys_putc_wrap_spec in *.
      destruct (sys_putc_spec) eqn:Hspec; inv H3.
      admit. (* need putc_correct *)
    + destruct w as (? & _ & ?).
      destruct H1 as (? & ? & Hpre); subst.
      destruct s; simpl in *.
      unfold sys_getc_wrap_spec in *.
      destruct (sys_getc_spec) eqn:Hspec; inv H3.
      eapply sys_getc_correct in Hspec as (? & -> & [? Hpost ? ?]); eauto.
      * do 2 eexists; eauto.
        unfold getchar_post, getchar_post' in *.
        destruct Hpost as [? Hpost]; split; auto.
        admit. (* memory not handled yet *)
        destruct Hpost as [[]|[-> ->]]; split; try (simpl in *; omega).
        -- rewrite if_false by omega; eauto.
        -- rewrite if_true; auto.
      * unfold getchar_pre, getchar_pre' in *.
        apply Traces.sutt_trace_incl; auto.
  - apply juicy_dry_specs.
  - apply dry_spec_mem.
Admitted.

(* relate to OS's external events *)
  Notation ge := (globalenv prog).

  Inductive OS_safeN_trace : nat -> @trace io_specs.IO_event unit -> Ensemble (@trace io_specs.IO_event unit * RData) -> OK_ty -> RData -> corestate -> mem -> Prop :=
  | OS_safeN_trace_0: forall t z s c m, OS_safeN_trace O t (Singleton _ (TEnd, s)) z s c m
  | OS_safeN_trace_step:
      forall n t traces z s c m c' m',
      cl_step ge c m c' m' ->
      OS_safeN_trace n t traces z s c' m' ->
      OS_safeN_trace (S n) t traces z s c m
  | OS_safeN_trace_external:
      forall n t traces z s0 c m e args,
      cl_at_external c = Some (e,args) ->
      (forall s s' ret m' t' n'
         (Hargsty : Val.has_type_list args (sig_args (ef_sig e)))
         (Hretty : step_lemmas.has_opttyp ret (sig_res (ef_sig e))),
         IO_inj_mem m t s ->
         IO_ext_sem e args s = Some (s', ret, t') ->
         m' = OS_mem s' ->
         (n' <= n)%nat ->
         exists traces' z' c', consume_trace z z' t' /\
           cl_after_external ret c = Some c' /\
           OS_safeN_trace n' (app_trace t t') traces' z' s' c' m' /\
           (forall t'' sf, In _ traces' (t'', sf) -> In _ traces (app_trace t' t'', sf))) ->
      (forall t1, In _ traces t1 ->
        exists s s' ret m' t' n', Val.has_type_list args (sig_args (ef_sig e)) /\
         step_lemmas.has_opttyp ret (sig_res (ef_sig e)) /\
         IO_inj_mem m t s /\ IO_ext_sem e args s = Some (s', ret, t') /\ m' = OS_mem s' /\
         (n' <= n)%nat /\ exists traces' z' c', consume_trace z z' t' /\
           cl_after_external ret c = Some c' /\ OS_safeN_trace n' (app_trace t t') traces' z' s' c' m' /\
        exists t'' sf, In _ traces' (t'', sf) /\ t1 = (app_trace t' t'', sf)) ->
      OS_safeN_trace (S n) t traces z s0 c m.

(*  Lemma IO_ext_sem_trace : forall e args s s' ret t, IO_ext_sem e args s = Some (s', ret, t) ->
    t = trace_of_ostrace (strip_common_prefix IOEvent_eq s.(io_log) s'.(io_log)).
  Proof.
    intros until t.
    unfold IO_ext_sem.*)

(*  Lemma OS_trace_correct' : forall n t traces z s0 c m
    (Hvalid : valid_trace s0),
    OS_safeN_trace n t traces z s0 c m ->
    forall t sf, In _ traces (t, sf) -> valid_trace sf /\ app_trace (trace_of_ostrace s0.(io_log)) t = trace_of_ostrace sf.(io_log).
  Proof.
    induction n as [n IHn] using lt_wf_ind; intros; inversion H; subst.
    - inversion H0; subst.
      split; auto.
      admit.
    - eauto.
    - destruct (H3 _ H0) as (? & ? & ? & ? & ? & ? & ? & ? & Htrace & ? & Hext & ? & ? & ? & ? & ? & ? & ? & Hsafe & ? & ? & ? & Heq).
      inversion Heq; subst.
      eapply IHn in Hsafe as [? Htrace']; eauto; try omega.
      split; auto.
      rewrite <- Htrace, <- Htrace'.
      admit.
      { admit. }
  Admitted.*)

(*  Lemma OS_trace_correct : forall n traces z s0 c m
    (Hinit : s0.(io_log) = []) (Hcon : s0.(console) = {| cons_buf := []; rpos := 0 |}),
    OS_safeN_trace n traces z s0 c m ->
    forall t sf, In _ traces (t, sf) -> valid_trace sf /\ t = trace_of_ostrace sf.(io_log).
  Proof.
    intros; eapply OS_trace_correct' in H as [? Htrace]; eauto.
    split; auto.
    rewrite Hinit in Htrace; auto.
    { constructor; rewrite Hinit; repeat intro; try (pose proof app_cons_not_nil; congruence).
      + constructor.
      + hnf.
        rewrite Hcon; auto. }
  Qed.*)

(*  Lemma OS_safe_ext_safe : forall n traces z s0 q m,
    OS_safeN_trace n traces z s0 q m ->
    exists traces', ext_safeN_trace(J := OK_spec) prog IO_ext_sem IO_inj_mem OS_mem n traces' z q m /\
      forall t, In _ traces' t <-> exists s, In _ traces (t, s).
  Proof.
    induction n as [n IHn] using lt_wf_ind; intros; inversion H; subst.
    - exists (Singleton _ TEnd); split; [constructor|].
      intros; split.
      + inversion 1; eexists; constructor.
      + intros (? & Hin); inversion Hin; constructor.
    - edestruct IHn as (traces' & ? & ?); eauto.
      do 2 eexists; eauto.
      eapply ext_safeN_trace_step; eauto.
    - exists (fun t1 => exists s s' ret m' t n', Val.has_type_list args (sig_args (ef_sig e)) /\
         step_lemmas.has_opttyp ret (sig_res (ef_sig e)) /\
         IO_inj_mem m s /\ IO_ext_sem e args s = Some (s', ret, t) /\ m' = OS_mem s' /\
         (n' <= n0)%nat /\ exists traces' z' c', consume_trace z z' t /\
           cl_after_external ret q = Some c' /\ ext_safeN_trace(J := @OK_spec IO_Espec) prog IO_ext_sem IO_inj_mem OS_mem n' traces' z' c' m' /\
        exists t', In _ traces' t' /\ t1 = app_trace t t'); split.
      + eapply ext_safeN_trace_external; eauto; intros.
        edestruct (H1 (update_console (update_io_log s (io_log s0)) (console s0))) as (? & ? & ? & ? & ? & Hsafe & ?); eauto.
        { destruct s; reflexivity. }
        { admit. }
        { admit. }
        eapply IHn in Hsafe as (? & ? & ?); [|omega].
        do 4 eexists; eauto; split; eauto; split; eauto.
        intros; unfold In; eauto 25.
      + unfold In in *; split.
        * intro Hin; destruct (H2 _ Hin) as (s & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hsafe & ? & ? & ?); subst.
          eapply IHn in Hsafe as (? & ? & ?); [|omega].
          eexists; exists (update_console (update_io_log s (io_log s0)) (console s0)); do 6 eexists; eauto; split; eauto; split.
          { destruct s; reflexivity. }
          split.
          { admit. }
          admit.
        * intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Heq).
          inversion Heq; subst.
          edestruct H1 as (? & ? & ? & ? & ? & Hsafe & Htrace); eauto; apply Htrace.*)

  Lemma IO_valid : forall e args s s' ret t, IO_ext_sem e args s = Some (s', ret, t) -> valid_trace s -> valid_trace s'.
  Admitted.

  Lemma ext_safe_OS_safe : forall n t traces z q m s0 (Hvalid : valid_trace s0),
    ext_safeN_trace(J := OK_spec) prog IO_ext_sem IO_inj_mem OS_mem n t traces z q m ->
    exists traces', OS_safeN_trace n t traces' z s0 q m /\ forall t, In _ traces t <-> exists s, In _ traces' (t, s).
  Proof.
    induction n as [n IHn] using lt_wf_ind; intros; inversion H; subst.
    - exists (Singleton _ (TEnd, s0)); split; [constructor|].
      intros; split.
      + inversion 1; eexists; constructor.
      + intros (? & Hin); inversion Hin; constructor.
    - edestruct IHn as (traces' & ? & ?); eauto.
      do 2 eexists; eauto.
      eapply OS_safeN_trace_step; eauto.
    - exists (fun t1 => exists s s' ret m' t' n', Val.has_type_list args (sig_args (ef_sig e)) /\
         step_lemmas.has_opttyp ret (sig_res (ef_sig e)) /\
         IO_inj_mem m t s /\ IO_ext_sem e args s = Some (s', ret, t') /\ m' = OS_mem s' /\
         (n' <= n0)%nat /\ exists traces' z' c', consume_trace z z' t' /\
           cl_after_external ret q = Some c' /\ OS_safeN_trace n' (app_trace t t') traces' z' s' c' m' /\
        exists t'' sf, In _ traces' (t'', sf) /\ t1 = (app_trace t' t'', sf)); split.
      + eapply OS_safeN_trace_external; eauto; intros.
        edestruct H1 as (? & ? & ? & ? & ? & Hsafe & ?); eauto.
        assert (valid_trace s') by (destruct H3; eapply IO_valid; eauto).
        eapply IHn with (s0 := s') in Hsafe as (? & ? & ?); eauto; try omega.
        do 4 eexists; eauto; split; eauto; split; eauto.
        intros; unfold In; eauto 25.
      + unfold In in *; split.
        * intro Hin; destruct (H2 _ Hin) as (s & s' & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hsafe & ? & Htrace & ?); subst.
          assert (valid_trace s') by (destruct H5; eapply IO_valid; eauto).
          eapply IHn in Hsafe as (? & ? & Htraces); eauto; try omega.
          apply Htraces in Htrace as []; eauto 25.
        * intros (? & ? & s' & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Heq).
          inversion Heq; subst.
          edestruct H1 as (? & ? & ? & ? & ? & Hsafe & Htrace); eauto; apply Htrace.
          assert (valid_trace s') by (destruct H5; eapply IO_valid; eauto).
          eapply IHn in Hsafe as (? & ? & ->); eauto; try omega.
          admit.
  Admitted.

Theorem IO_OS_ext: 
 forall {CS: compspecs} (initial_oracle: OK_ty) V G m,
   semax_prog_ext prog initial_oracle V G ->
   Genv.init_mem prog = Some m ->
   exists b, exists q, exists m',
     Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
     initial_core (cl_core_sem (globalenv prog))
         0 m q m' (Vptr b Ptrofs.zero) nil /\
   forall n s0, s0.(io_log) = [] -> s0.(console) = {| cons_buf := []; rpos := 0 |} ->
    exists traces, OS_safeN_trace n TEnd traces initial_oracle s0 q m' /\
     forall t s, In _ traces (t, s) -> exists z', consume_trace initial_oracle z' t /\ t = trace_of_ostrace s.(io_log) /\
      valid_trace_user s.(io_log).
Proof.
  intros; eapply IO_OS_soundness in H as (? & ? & ? & ? & ? & Hsafe); eauto.
  do 4 eexists; eauto; split; eauto; intros.
  destruct (Hsafe n) as (? & Hsafen & Htrace).
  eapply ext_safe_OS_safe in Hsafen as (? & Hsafen & Htrace').
  do 2 eexists; eauto; intros ?? Hin.
  eapply OS_trace_correct in Hsafen as [Hvalid]; eauto.
  destruct (Htrace t).
  { apply Htrace'; eauto. }
  inversion Hvalid; eauto.
Qed.

End IO_safety.
