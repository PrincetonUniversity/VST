Require Import VST.floyd.proofauto.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.initial_world.
Require Import VST.veric.ghost_PCM.
Require Import VST.veric.SequentialClight.
Require Import VST.veric.Clight_core.
Require Import VST.progs.conclib.
Require Import VST.sepcomp.semantics.
Require Import ITree.ITree.
Require Import ITree.Interp.Traces.
Require Import Ensembles.
Require Import VST.progs.io_specs.
Require Import VST.progs.io_dry.
Require Import VST.progs.io_os_specs.
Require Import VST.progs.io_os_connection.
Require Import VST.progs.os_combine.
Require Import VST.progs.dry_mem_lemmas.

Section IO_safety.

Context `{Config : ThreadsConfigurationOps}.
Variable (prog : Clight.program).

Definition ext_link := ext_link_prog prog.

Definition sys_getc_wrap_spec (abd : RData) : option (RData * val * trace) :=
  match sys_getc_spec abd with
  | Some abd' => Some (abd', get_sys_ret abd', trace_of_ostrace (strip_common_prefix IOEvent_eq abd.(io_log) abd'.(io_log)))
  | None => None
  end.

Definition sys_putc_wrap_spec (cv : val) (abd : RData) : option (RData * val * trace) :=
  (* Make sure argument is set *)
  match cv, get_sys_arg1 abd with
  | Vint c, Vint c' =>
    if eq_dec.eq_dec c c' then
      match sys_putc_spec abd with
      | Some abd' => Some (abd', get_sys_ret abd', trace_of_ostrace (strip_common_prefix IOEvent_eq abd.(io_log) abd'.(io_log)))
      | None => None
      end
    else None
  | _, _ => None
  end.

Definition IO_ext_sem e (args : list val) s :=
  if oi_eq_dec (Some (ext_link "putchar"%string, funsig2signature ([(1%positive, tint)], tint) cc_default))
    (ef_id_sig ext_link e) then
    match args with
    | c :: nil =>
      match sys_putc_wrap_spec c s with
      | Some (s', ret, t') => Some (s', Some ret, t')
      | None => None
      end
    | _ => None end else
  if oi_eq_dec  (Some (ext_link "getchar"%string, funsig2signature ([], tint) cc_default))
    (ef_id_sig ext_link e) then
    match sys_getc_wrap_spec s with
    | Some (s', ret, t') => Some (s', Some ret, t')
    | None => None
    end
  else Some (s, None, TEnd).

Variable (R_mem : block -> Z).

(* Because putchar and getchar don't use memory, these functions don't either. *)
Definition IO_inj_mem (e : external_function) (args : list val) (m : mem) t s :=
  valid_trace s /\ t = trace_of_ostrace s.(io_log).
Definition OS_mem (e : external_function) (args : list val) m (s : RData) : mem := m.
(* In general, this could look like:
  if oi_eq_dec (Some (ext_link "putchars"%string, ...) (ef_id_sig ext_link e) then
    match args with
    | (Vptr b ofs) :: len :: nil => flatmem_to_mem R_mem s.(HP) m b ofs (ofs + len)
    | _ => m end
  else ...
*)

Instance IO_Espec : OracleKind := IO_Espec ext_link.

Theorem IO_OS_soundness:
 forall {CS: compspecs} (initial_oracle: OK_ty) V G m,
   semax_prog prog initial_oracle V G ->
   Genv.init_mem prog = Some m ->
   exists b, exists q,
     Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
     initial_core (Clight_core.cl_core_sem (globalenv prog))
         0 m q m (Vptr b Ptrofs.zero) nil /\
   forall n, exists traces, ext_safeN_trace(J := OK_spec) prog IO_ext_sem IO_inj_mem OS_mem valid_trace n TEnd traces initial_oracle q m /\
     forall t, In _ traces t -> exists z', consume_trace initial_oracle z' t.
Proof.
  intros; eapply OS_soundness with (dryspec := io_dry_spec ext_link); eauto.
  - unfold IO_ext_sem; intros; simpl in *.
    destruct H2 as [Hvalid Htrace].
    if_tac; [|if_tac; [|contradiction]].
    + destruct w as (? & _ & ? & ?).
      destruct H1 as (? & ? & Hpre); subst.
      destruct s; simpl in *.
      rewrite if_true in H3 by auto.  
      destruct (get_sys_arg1 _) eqn:Harg; try discriminate.
      destruct (eq_dec _ _); subst; try discriminate.
      destruct (sys_putc_spec _) eqn:Hspec; inv H3.
      assert (sig_res (ef_sig e) <> AST.Tvoid).
      { destruct e; inv H2; discriminate. }
      eapply sys_putc_correct in Hspec as (? & -> & [? Hpost ?]); eauto.
    + destruct w as (? & _ & ?).
      destruct H1 as (? & ? & Hpre); subst.
      destruct s; simpl in *.
      rewrite if_false in H3 by auto.  
      rewrite if_true in H3 by auto.  
      unfold sys_getc_wrap_spec in *.
      destruct (sys_getc_spec) eqn:Hspec; inv H3.
      assert (sig_res (ef_sig e) <> AST.Tvoid).
      { destruct e; inv H4; discriminate. }
      eapply sys_getc_correct with (m1 := m) in Hspec as (? & -> & [? Hpost ? ?]); eauto.
      * split; auto; do 2 eexists; eauto.
        unfold getchar_post, getchar_post' in *.
        destruct Hpost as [? Hpost]; split; auto; split; auto.
        destruct Hpost as [[]|[-> ->]]; split; try (simpl in *; rep_lia).
        -- rewrite if_false by lia; eauto.
        -- rewrite if_true; auto.
      * unfold getchar_pre, getchar_pre' in *.
        apply Traces.sutt_trace_incl; auto.
  - constructor.
  - apply juicy_dry_specs.
  - apply dry_spec_mem.
Qed.

(* relate to OS's external events *)
Notation ge := (globalenv prog).

  Inductive OS_safeN_trace : nat -> @trace io_events.IO_event unit -> Ensemble (@trace io_events.IO_event unit * RData) -> OK_ty -> RData -> CC_core -> mem -> Prop :=
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
         (Hretty : Builtins0.val_opt_has_rettype  ret (sig_res (ef_sig e))),
         IO_inj_mem e args m t s ->
         IO_ext_sem e args s = Some (s', ret, t') ->
         m' = OS_mem e args m s' ->
         (n' <= n)%nat ->
         valid_trace s' /\ exists traces' z' c', consume_trace z z' t' /\
           cl_after_external ret c = Some c' /\
           OS_safeN_trace n' (app_trace t t') traces' z' s' c' m' /\
           (forall t'' sf, In _ traces' (t'', sf) -> In _ traces (app_trace t' t'', sf))) ->
      (forall t1, In _ traces t1 ->
        exists s s' ret m' t' n', Val.has_type_list args (sig_args (ef_sig e)) /\
         Builtins0.val_opt_has_rettype  ret (sig_res (ef_sig e)) /\
         IO_inj_mem e args m t s /\ IO_ext_sem e args s = Some (s', ret, t') /\ m' = OS_mem e args m s' /\
         (n' <= n)%nat /\ valid_trace s' /\ exists traces' z' c', consume_trace z z' t' /\
           cl_after_external ret c = Some c' /\ OS_safeN_trace n' (app_trace t t') traces' z' s' c' m' /\
        exists t'' sf, In _ traces' (t'', sf) /\ t1 = (app_trace t' t'', sf)) ->
      OS_safeN_trace (S n) t traces z s0 c m
  | OS_safeN_trace_halted:
      forall n z t s c m,
      cl_halted c <> None ->
      OS_safeN_trace n t (Singleton _ (TEnd, s)) z s c m.

Lemma strip_all : forall {A} (A_eq : forall x y : A, {x = y} + {x <> y}) t, strip_common_prefix A_eq t t = [].
Proof.
  intros; unfold strip_common_prefix.
  rewrite common_prefix_full, Nat.leb_refl, skipn_exact_length; auto.
Qed.

Local Ltac inj :=
  repeat match goal with
  | H: _ = _ |- _ => assert_succeeds (injection H); inv H
  end.

Local Ltac destruct_spec Hspec :=
  repeat match type of Hspec with
  | match ?x with _ => _ end = _ => destruct x eqn:?; subst; inj; try discriminate
  end.

  Lemma IO_ext_sem_trace : forall e args s s' ret t, valid_trace s -> IO_ext_sem e args s = Some (s', ret, t) ->
    s.(io_log) = common_prefix IOEvent_eq s.(io_log) s'.(io_log) /\
    t = trace_of_ostrace (strip_common_prefix IOEvent_eq s.(io_log) s'.(io_log)).
  Proof.
    intros until 1.
    unfold IO_ext_sem.
    if_tac; [|if_tac].
    - unfold sys_putc_wrap_spec.
      destruct args as [| [] [|]]; try discriminate.
      destruct get_sys_arg1 eqn: Harg; try discriminate.
      destruct (eq_dec _ _); try discriminate.
      destruct sys_putc_spec eqn: Hputc; inversion 1; subst; split; auto.
      pose proof Hputc as Hspec.
      unfold sys_putc_spec in Hputc; destruct_spec Hputc.
      unfold uctx_set_errno_spec in Hputc; destruct_spec Hputc.
      unfold uctx_set_retval1_spec in Heqo3; destruct_spec Heqo3.
      destruct r1; cbn in *.
      eapply sys_putc_trace_case in Hspec as []; eauto.
      unfold get_sys_ret; cbn.
      repeat (rewrite ZMap.gss in * || rewrite ZMap.gso in * by easy); subst; inj; reflexivity.
    - unfold sys_getc_wrap_spec.
      destruct sys_getc_spec eqn: Hgetc; inversion 1; subst; split; auto.
      pose proof Hgetc as Hspec.
      unfold sys_getc_spec in Hgetc; destruct_spec Hgetc.
      unfold uctx_set_errno_spec in Hgetc; destruct_spec Hgetc.
      unfold uctx_set_retval1_spec in Heqo2; destruct_spec Heqo2.
      destruct r1; cbn in *.
      eapply sys_getc_trace_case in Hspec as []; auto.
      unfold get_sys_ret; cbn.
      repeat (rewrite ZMap.gss in * || rewrite ZMap.gso in * by easy); subst; inj; reflexivity.
    - inversion 1.
      rewrite common_prefix_full, strip_all; auto.
  Qed.

  Lemma app_trace_end : forall t, app_trace (trace_of_ostrace t) TEnd = trace_of_ostrace t.
  Proof.
    induction t; auto; simpl.
    destruct io_event_of_io_tevent as [[]|]; auto; simpl.
    rewrite IHt; auto.
  Qed.

  Lemma app_trace_strip : forall t1 t2, common_prefix IOEvent_eq t1 t2 = t1 ->
    app_trace (trace_of_ostrace t1) (trace_of_ostrace (strip_common_prefix IOEvent_eq t1 t2)) = trace_of_ostrace t2.
  Proof.
    intros; rewrite (strip_common_prefix_correct IOEvent_eq t1 t2) at 2.
    rewrite trace_of_ostrace_app, H; auto.
    { rewrite <- H, common_prefix_sym; apply common_prefix_length. }
  Qed.

  Lemma OS_trace_correct' : forall n t traces z s0 c m
    (Hvalid : valid_trace s0) (Ht : t = trace_of_ostrace s0.(io_log)),
    OS_safeN_trace n t traces z s0 c m ->
    forall t' sf, In _ traces (t', sf) -> valid_trace sf /\ app_trace (trace_of_ostrace s0.(io_log)) t' = trace_of_ostrace sf.(io_log).
  Proof.
    induction n as [n IHn] using lt_wf_ind; intros; inv H.
    - inv H0.
      rewrite app_trace_end; auto.
    - eauto.
    - destruct (H3 _ H0) as (? & s' & ? & ? & ? & ? & ? & ? & Hinj & Hcall & ? & ? & ? & ? & ? & ? & ? & ? & Hsafe & ? & ? & ? & Heq).
      inv Heq.
      destruct Hinj as [? Htrace].
      apply IO_ext_sem_trace in Hcall as [Hprefix]; auto; subst.
      eapply IHn in Hsafe as [? Htrace']; eauto; try lia.
      split; auto.
      rewrite Htrace, <- Htrace', <- app_trace_assoc, app_trace_strip; auto.
      { rewrite Htrace, app_trace_strip; auto. }
    - inv H0.
      rewrite app_trace_end; auto.
  Qed.

  Lemma init_log_valid : forall s, io_log s = [] -> console s = {| cons_buf := []; rpos := 0 |} -> valid_trace s.
  Proof.
    intros s Hinit Hcon.
    constructor; rewrite Hinit; repeat intro; try (pose proof app_cons_not_nil; congruence).
    + constructor.
    + hnf.
      rewrite Hcon; auto.
  Qed.

  Lemma OS_trace_correct : forall n traces z s0 c m
    (Hinit : s0.(io_log) = []) (Hcon : s0.(console) = {| cons_buf := []; rpos := 0 |}),
    OS_safeN_trace n TEnd traces z s0 c m ->
    forall t sf, In _ traces (t, sf) -> valid_trace sf /\ t = trace_of_ostrace sf.(io_log).
  Proof.
    intros; eapply OS_trace_correct' in H as [? Htrace]; eauto.
    split; auto.
    rewrite Hinit in Htrace; auto.
    { apply init_log_valid; auto. }
    { rewrite Hinit; auto. }
  Qed.

  Lemma cl_at_external_not_halted : forall q a, cl_at_external q = Some a -> ~cl_halted q <> None.
  Proof.
    destruct q; try discriminate; simpl; congruence.
  Qed.

  Lemma OS_traces_det : forall n t traces traces' z z' s q m,
    OS_safeN_trace n t traces z s q m -> OS_safeN_trace n t traces' z' s q m ->
    traces = traces'.
  Proof.
    induction n as [n IHn] using lt_wf_ind; inversion 1; inversion 1; subst; auto.
    - eapply semax_lemmas.cl_corestep_fun in H0; eauto; inv H0; eauto.
    - apply cl_corestep_not_at_external in H0; congruence.
    - apply (cl_corestep_not_halted _ _ _ _ _ Int.zero) in H0; contradiction.
    - erewrite cl_corestep_not_at_external in H0 by eauto; congruence.
    - rewrite H0 in H12; inv H12.
      apply Extensionality_Ensembles; split; intros ? Hin.
      + destruct (H2 _ Hin) as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hafter & Hsafe & ? & ? & ? & ?); subst.
        edestruct H13 as (? & ? & ? & ? & ? & Hafter' & Hsafe' & Htraces); eauto.
        rewrite Hafter in Hafter'; inv Hafter'.
        apply Htraces.
        eapply IHn in Hsafe; eauto; try lia.
        subst; auto.
      + destruct (H14 _ Hin) as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hafter & Hsafe & ? & ? & ? & ?); subst.
        edestruct H1 as (? & ? & ? & ? & ? & Hafter' & Hsafe' & Htraces); eauto.
        rewrite Hafter in Hafter'; inv Hafter'.
        apply Htraces.
        eapply IHn in Hsafe; eauto; try lia.
        subst; auto.
    - apply cl_at_external_not_halted in H0; auto; contradiction.
    - apply (cl_corestep_not_halted _ _ _ _ _ Int.zero) in H9; contradiction.
    - apply cl_at_external_not_halted in H9; auto; contradiction.
  Qed.

  Lemma ext_safe_OS_safe : forall n t traces z q m s0 (Hvalid : valid_trace s0),
    ext_safeN_trace(J := OK_spec) prog IO_ext_sem IO_inj_mem OS_mem valid_trace n t traces z q m ->
    exists traces', OS_safeN_trace n t traces' z s0 q m /\ forall t, In _ traces t <-> exists s, In _ traces' (t, s).
  Proof.
    induction n as [n IHn] using lt_wf_ind; intros; inv H.
    - exists (Singleton _ (TEnd, s0)); split; [constructor|].
      intros; split.
      + inversion 1; eexists; constructor.
      + intros (? & Hin); inversion Hin; constructor.
    - edestruct IHn as (traces' & ? & ?); eauto.
      do 2 eexists; eauto.
      eapply OS_safeN_trace_step; eauto.
    - exists (fun t1 => exists s s' ret m' t' n', Val.has_type_list args (sig_args (ef_sig e)) /\
         Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e)) /\
         IO_inj_mem e args m t s /\ IO_ext_sem e args s = Some (s', ret, t') /\ m' = OS_mem e args m s' /\
         (n' <= n0)%nat /\ valid_trace s' /\ exists traces' z' c', consume_trace z z' t' /\
           cl_after_external ret q = Some c' /\ OS_safeN_trace n' (app_trace t t') traces' z' s' c' m' /\
        exists t'' sf, In _ traces' (t'', sf) /\ t1 = (app_trace t' t'', sf)); split.
      + eapply OS_safeN_trace_external; eauto; intros.
        edestruct H1 as (? & ? & ? & ? & ? & ? & Hsafe & ?); eauto.
        eapply IHn with (s0 := s') in Hsafe as (? & ? & ?); eauto; try lia.
        split; auto; do 4 eexists; eauto; split; eauto; split; eauto.
        intros; unfold In; eauto 25.
      + unfold In in *; split.
        * intro Hin; destruct (H2 _ Hin) as (s & s' & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hsafe & ? & Htrace & ?); subst.
          eapply IHn in Hsafe as (? & ? & Htraces); eauto; try lia.
          apply Htraces in Htrace; destruct Htrace; eauto 25.
        * intros (? & ? & s' & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hafter & Hsafe' & ? & ? & ? & Heq).
          inv Heq.
          edestruct H1 as (? & ? & ? & ? & ? & Hafter' & Hsafe & Htrace); eauto; apply Htrace.
          eapply IHn in Hsafe as (? & ? & ->); eauto; try lia.
          rewrite Hafter in Hafter'; inv Hafter'.
          eapply OS_traces_det in Hsafe'; eauto; subst; eauto.
    - exists (Singleton _ (TEnd, s0)); split; [constructor; auto|].
      intros; split.
      + inversion 1; eexists; constructor.
      + intros (? & Hin); inversion Hin; constructor.
  Qed.

Theorem IO_OS_ext:
 forall {CS: compspecs} (initial_oracle: OK_ty) V G m,
   semax_prog prog initial_oracle V G ->
   Genv.init_mem prog = Some m ->
   exists b, exists q, 
     Genv.find_symbol (Genv.globalenv prog) (AST.prog_main prog) = Some b /\
     initial_core (cl_core_sem (globalenv prog))
         0 m q m (Vptr b Ptrofs.zero) nil /\
   forall n s0, s0.(io_log) = [] -> s0.(console) = {| cons_buf := []; rpos := 0 |} ->
    exists traces, OS_safeN_trace n TEnd traces initial_oracle s0 q m /\
     forall t s, In _ traces (t, s) -> exists z', consume_trace initial_oracle z' t /\ t = trace_of_ostrace s.(io_log) /\
      valid_trace_user s.(io_log).
Proof.
  intros.
  eapply IO_OS_soundness in H as (? & ? & ? & ? & Hsafe); eauto.
  do 3 eexists; eauto; split; eauto; intros.
  destruct (Hsafe n) as (? & Hsafen & Htrace).
  eapply ext_safe_OS_safe in Hsafen as (? & Hsafen & Htrace').
  do 2 eexists; eauto; intros ?? Hin.
  eapply OS_trace_correct in Hsafen as [Hvalid]; eauto.
  destruct (Htrace t).
  { apply Htrace'; eauto. }
  inversion Hvalid; eauto.
  { apply init_log_valid; auto. }
Qed.

End IO_safety.
