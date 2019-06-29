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

(*Section ext_safe.

  Context {Espec : OracleKind} {OS_state : Type} {etrace : Type}.
  Variable prog : Clight.program.
  Variable ext_sem : external_function -> list val -> OS_state -> OS_state * option val * etrace.
  Variable consume_trace : OK_ty -> OK_ty -> etrace -> Prop.
  Variable inj_mem : mem -> OS_state -> Prop.
  Variable extr_mem : OS_state -> mem.
  Notation ge := (globalenv prog).

  Inductive ext_safeN : nat -> OK_ty -> corestate -> mem -> Prop :=
  | ext_safeN_0: forall z c m, ext_safeN O z c m
  | ext_safeN_step:
      forall n z c m c' m',
      cl_step ge c m c' m' ->
      ext_safeN n z c' m' ->
      ext_safeN (S n) z c m
  | ext_safeN_external:
      forall n z c m e args,
      cl_at_external c = Some (e,args) ->
      (forall s s' ret m' t' n'
         (Hargsty : Val.has_type_list args (sig_args (ef_sig e)))
         (Hretty : step_lemmas.has_opttyp ret (sig_res (ef_sig e))),
         inj_mem m s ->
         ext_sem e args s = (s', ret, t') ->
         m' = extr_mem s' ->
         (n' <= n)%nat ->
         exists z' c', consume_trace z z' t' /\
           cl_after_external ret c = Some c' /\
           ext_safeN n' z' c' m') ->
      ext_safeN (S n) z c m.

  Variable dryspec : ext_spec OK_ty.
  Hypothesis extcalls_correct : forall e w b tl args z m s, ext_spec_pre dryspec e w b tl args z m ->
    inj_mem m s ->
    let '(s', ret, t') := ext_sem e args s in
    exists z', consume_trace z z' t' /\
    ext_spec_post dryspec e w b (sig_res (ef_sig e)) ret z' (extr_mem s').

  Lemma dry_safe_ext_safe : forall n z q m,
    step_lemmas.dry_safeN(genv_symb := Clight_sim.genv_symb_injective)
     (Clight_sim.coresem_extract_cenv (cl_core_sem (globalenv prog)) (prog_comp_env prog)) dryspec
     (Build_genv (Genv.globalenv prog) (prog_comp_env prog)) n z q m ->
    ext_safeN n z q m.
  Proof.
    induction n as [n IHn] using lt_wf_ind; intros; inversion H; subst; try contradiction.
    - constructor.
    - econstructor; eauto.
    - eapply ext_safeN_external; eauto; intros.
      eapply extcalls_correct in H1; eauto.
      rewrite H4 in H1; destruct H1 as (z' & ? & ?).
      edestruct H2 as (? & ? & ?); eauto.
      do 3 eexists; eauto; split; eauto.
      subst; apply IHn; auto; omega.
  Qed.

  Theorem OS_safety:
   forall {CS: compspecs} (initial_oracle: OK_ty)
     (dessicate : forall (ef : external_function) jm,
               ext_spec_type OK_spec ef ->
               ext_spec_type dryspec ef)
     (JDE: juicy_dry_ext_spec _ (@JE_spec OK_ty OK_spec) dryspec dessicate)
     (DME: ext_spec_mem_evolve _ dryspec)
     V G m,
     @semax_prog_ext Espec CS prog initial_oracle V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q, exists m',
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       initial_core  (cl_core_sem (globalenv prog))
           0 m q m' (Vptr b Ptrofs.zero) nil /\
       forall n, ext_safeN n initial_oracle q m'.
  Proof.
    intros.
    eapply CSHL_Sound.semax_prog_ext_sound, whole_program_sequential_safety_ext in H as (b & q & m' & ? & ? & Hsafe); eauto.
    do 4 eexists; eauto; split; eauto; intro n.
    eapply dry_safe_ext_safe; eauto.
  Qed.

End ext_safe.*)

Require Import ITree.Interp.Traces.
Require Import Ensembles.

Section ext_trace.

  Context {cevent : Type -> Type} {J : juicy_ext_spec (itree cevent unit)} {OS_state : Type} {event : Type}.
  Variable prog : Clight.program.
  Variable ext_sem : external_function -> list val -> OS_state -> option (OS_state * option val * list event).
  Variable inj_mem : mem -> OS_state -> Prop.
  Variable extr_mem : OS_state -> mem.
  Notation ge := (globalenv prog).

  Instance Espec : OracleKind := Build_OracleKind (itree cevent unit) J.

  Variable lift_event : event -> {X & option (cevent X * X)%type}.

  Fixpoint trace_of_events (t : list event) : @trace cevent unit :=
    match t with
    | nil => TEnd
    | e :: t' =>
        match projT2 (lift_event e) with
        | Some (e', r) => TEventResponse e' r (trace_of_events t')
        | None => trace_of_events t'
        end
    end.

  Definition consume_trace (z z' : itree cevent unit) le := let t := trace_of_events le in
    forall t', is_trace z' t' -> is_trace z (app_trace t t').

(*  Inductive ext_traceN : nat -> list event -> OK_ty -> corestate -> mem -> Prop :=
  | ext_traceN_0: forall z c m, ext_traceN O [] z c m
  | ext_traceN_step:
      forall n t z c m c' m',
      cl_step ge c m c' m' ->
      ext_traceN n t z c' m' ->
      ext_traceN (S n) t z c m
  | ext_traceN_external:
      forall n z c m e args,
      cl_at_external c = Some (e,args) ->
      forall s s' ret m' t t' n'
       (Hargsty : Val.has_type_list args (sig_args (ef_sig e)))
       (Hretty : step_lemmas.has_opttyp ret (sig_res (ef_sig e))),
       inj_mem m s ->
       ext_sem e args s = (s', ret, t) ->
       m' = extr_mem s' ->
       (n' <= n)%nat ->
       forall z' c', consume_trace z z' t ->
       cl_after_external ret c = Some c' ->
       ext_traceN n' t' z' c' m' ->
      ext_traceN (S n) (t ++ t') z c m.*)

  Lemma consume_trace_nil : forall z, consume_trace z z nil.
  Proof.
    repeat intro; auto.
  Qed.

  Lemma trace_of_events_app : forall t t', trace_of_events (t ++ t') = app_trace (trace_of_events t) (trace_of_events t').
  Proof.
    induction t; auto; simpl; intros.
    destruct (lift_event a) as (? & [(? & ?) |]); simpl; auto.
    rewrite IHt; auto.
  Qed.

  Lemma app_trace_assoc : forall {E : Type -> Type} {R : Type} (t t' t'' : @trace E R),
    app_trace (app_trace t t') t'' = app_trace t (app_trace t' t'').
  Proof.
    induction t; auto; simpl; intros.
    rewrite IHt; auto.
  Qed.

  Lemma consume_trace_app : forall z z' z'' t t', consume_trace z z' t -> consume_trace z' z'' t' ->
    consume_trace z z'' (t ++ t').
  Proof.
    unfold consume_trace; intros.
    rewrite trace_of_events_app, app_trace_assoc; auto.
  Qed.

(*  Theorem ext_trace_correct:
   forall (initial_oracle: OK_ty) q m n t,
    ext_traceN n t initial_oracle q m ->
    exists z', consume_trace initial_oracle z' t.
  Proof.
    induction 1.
    - exists z; repeat intro; auto.
    - auto.
    - destruct IHext_traceN as [z'' ?].
      exists z''.
      eapply consume_trace_app; eauto.
  Qed.*)

  Inductive ext_safeN_trace : nat -> Ensemble (list event) -> OK_ty -> corestate -> mem -> Prop :=
  | ext_safeN_trace_0: forall z c m, ext_safeN_trace O (Empty_set _) z c m
  | ext_safeN_trace_step:
      forall n traces z c m c' m',
      cl_step ge c m c' m' ->
      ext_safeN_trace n traces z c' m' ->
      ext_safeN_trace (S n) traces z c m
  | ext_safeN_trace_external:
      forall n traces z c m e args,
      cl_at_external c = Some (e,args) ->
      (forall s s' ret m' t n'
         (Hargsty : Val.has_type_list args (sig_args (ef_sig e)))
         (Hretty : step_lemmas.has_opttyp ret (sig_res (ef_sig e))),
         inj_mem m s ->
         ext_sem e args s = Some (s', ret, t) ->
         m' = extr_mem s' ->
         (n' <= n)%nat ->
         exists traces' z' c', consume_trace z z' t /\
           cl_after_external ret c = Some c' /\
           ext_safeN_trace n' traces' z' c' m' /\
           (forall t', In _ traces' t' -> In _ traces (t ++ t'))) ->
      (forall t1, In _ traces t1 ->
        exists s s' ret m' t n', Val.has_type_list args (sig_args (ef_sig e)) /\
         step_lemmas.has_opttyp ret (sig_res (ef_sig e)) /\
         inj_mem m s /\ ext_sem e args s = Some (s', ret, t) /\ m' = extr_mem s' /\
         (n' <= n)%nat /\ exists traces' z' c', consume_trace z z' t /\
           cl_after_external ret c = Some c' /\ ext_safeN_trace n' traces' z' c' m' /\
        exists t', In _ traces' t' /\ t1 = t ++ t') ->
      ext_safeN_trace (S n) traces z c m.

  Variable dryspec : ext_spec OK_ty.
  Hypothesis extcalls_correct : forall e w b tl args z m s, ext_spec_pre dryspec e w b tl args z m ->
    inj_mem m s ->
    forall s' ret t', Some (s', ret, t') = ext_sem e args s ->
    exists z', consume_trace z z' t' /\
    ext_spec_post dryspec e w b (sig_res (ef_sig e)) ret z' (extr_mem s').

  Lemma dry_safe_ext_trace_safe : forall n z q m,
    step_lemmas.dry_safeN(genv_symb := Clight_sim.genv_symb_injective)
     (Clight_sim.coresem_extract_cenv (cl_core_sem (globalenv prog)) (prog_comp_env prog)) dryspec
     (Build_genv (Genv.globalenv prog) (prog_comp_env prog)) n z q m ->
    exists traces, ext_safeN_trace n traces z q m.
  Proof.
    induction n as [n IHn] using lt_wf_ind; intros; inversion H; subst; try contradiction.
    - eexists; constructor.
    - edestruct IHn as [traces ?]; eauto; exists traces; econstructor; eauto.
    - exists (fun t1 => exists s s' ret m' t n', Val.has_type_list args (sig_args (ef_sig e)) /\
         step_lemmas.has_opttyp ret (sig_res (ef_sig e)) /\
         inj_mem m s /\ ext_sem e args s = Some (s', ret, t) /\ m' = extr_mem s' /\
         (n' <= n0)%nat /\ exists traces' z' c', consume_trace z z' t /\
           cl_after_external ret q = Some c' /\ ext_safeN_trace n' traces' z' c' m' /\
        exists t', In _ traces' t' /\ t1 = t ++ t').
      eapply ext_safeN_trace_external; eauto; intros.
      eapply extcalls_correct in H1; eauto.
      destruct H1 as (z' & ? & ?).
      edestruct H2 as (? & ? & Hsafe); eauto.
      apply IHn in Hsafe as [traces ?]; [|omega].
      subst; do 4 eexists; eauto; split; eauto; split; eauto.
      intros; unfold In.
      do 7 eexists; eauto; split; eauto; split; eauto; split; eauto; split; eauto; split; eauto.
      do 4 eexists; eauto.
  Qed.

  Lemma safety_trace:
   forall {CS: compspecs} (initial_oracle: OK_ty)
     (dessicate : forall (ef : external_function) jm,
               ext_spec_type OK_spec ef ->
               ext_spec_type dryspec ef)
     (JDE: juicy_dry_ext_spec _ (@JE_spec OK_ty OK_spec) dryspec dessicate)
     (DME: ext_spec_mem_evolve _ dryspec)
     V G m,
     @semax_prog_ext Espec CS prog initial_oracle V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q, exists m',
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       initial_core  (cl_core_sem (globalenv prog))
           0 m q m' (Vptr b Ptrofs.zero) nil /\
       forall n, exists traces, ext_safeN_trace n traces initial_oracle q m'.
  Proof.
    intros.
    eapply CSHL_Sound.semax_prog_ext_sound, whole_program_sequential_safety_ext in H as (b & q & m' & ? & ? & Hsafe); eauto.
    do 4 eexists; eauto; split; eauto; intro n.
    eapply dry_safe_ext_trace_safe; eauto.
  Qed.

  Lemma trace_correct:
   forall n (z: OK_ty) q m traces t,
    ext_safeN_trace n traces z q m ->
    In _ traces t ->
    exists z', consume_trace z z' t.
  Proof.
    induction n as [n IHn] using lt_wf_ind; intros; inversion H; subst.
    - inversion H0.
    - eauto.
    - destruct (H3 _ H0) as (s & s' & ret & m' & t1 & n' & ? & ? & ? & ? & ? & ? & traces' & z' & c' & ? & ? & ? & ? & ? & ?).
      edestruct (IHn n') as [z'' ?]; eauto; [omega|].
      subst; eexists; eapply consume_trace_app; eauto.
  Qed.

  Theorem OS_soundness:
   forall {CS: compspecs} (initial_oracle: OK_ty)
     (dessicate : forall (ef : external_function) jm,
               ext_spec_type OK_spec ef ->
               ext_spec_type dryspec ef)
     (JDE: juicy_dry_ext_spec _ (@JE_spec OK_ty OK_spec) dryspec dessicate)
     (DME: ext_spec_mem_evolve _ dryspec)
     V G m,
     @semax_prog_ext Espec CS prog initial_oracle V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q, exists m',
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       initial_core  (cl_core_sem (globalenv prog))
           0 m q m' (Vptr b Ptrofs.zero) nil /\
       forall n, exists traces, ext_safeN_trace n traces initial_oracle q m' /\
         forall t, In _ traces t -> exists z', consume_trace initial_oracle z' t.
  Proof.
    intros.
    eapply safety_trace in H as (b & q & m' & ? & ? & Hsafe); eauto.
    exists b, q, m'; split; auto; split; auto.
    intro n; destruct (Hsafe n) as [traces Hsafen].
    exists traces; split; auto.
    intros; eapply trace_correct; eauto.
  Qed.

End ext_trace.

Require Import VST.progs.io_dry.
Require Import VST.progs.io_os_connection.
Require Import VST.progs.io_os_specs.

Section IO_safety.

Context `{ThreadsConfigurationOps}.
Variable (prog : Clight.program).

Definition ext_link := ext_link_prog prog.

Definition sys_getc_wrap_spec (abd : RData) : option (RData * val * ostrace) :=
  match sys_getc_spec abd with
  | Some abd' => Some (abd', get_sys_ret abd', strip_common_prefix IOEvent_eq abd.(io_log) abd'.(io_log))
  | None => None
  end.

Definition IO_ext_sem e (args : list val) s :=
  if oi_eq_dec (Some (ext_link "putchar"%string, funsig2signature ([(1%positive, tint)], tint) cc_default))
    (ef_id_sig ext_link e) then
    (* putchar_spec (Znth 0 args) s *) Some (s, None, []) else
  if oi_eq_dec  (Some (ext_link "getchar"%string, funsig2signature ([], tint) cc_default))
    (ef_id_sig ext_link e) then
    match sys_getc_wrap_spec s with
    | Some (s', ret, t') => Some (s', Some ret, t')
    | None => None
    end
  else Some (s, None, []).

Definition IO_inj_mem (m : mem) s := valid_trace s. (* stub *)
Definition OS_mem (s : RData) : mem := Mem.empty. (* stub *)

Instance IO_Espec : OracleKind := io_specs.IO_Espec ext_link.

Definition lift_IO_event e := existT (fun X => option (io_specs.IO_event X * X)%type) (trace_event_rtype e) (io_event_of_io_tevent e).

Theorem IO_OS_soundness:
 forall {CS: compspecs} (initial_oracle: OK_ty) V G m,
   semax_prog_ext prog initial_oracle V G ->
   Genv.init_mem prog = Some m ->
   exists b, exists q, exists m',
     Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
     initial_core  (cl_core_sem (globalenv prog))
         0 m q m' (Vptr b Ptrofs.zero) nil /\
   forall n, exists traces, ext_safeN_trace(J := OK_spec) prog IO_ext_sem IO_inj_mem OS_mem lift_IO_event n traces initial_oracle q m' /\
     forall t, In _ traces t -> exists z', consume_trace lift_IO_event initial_oracle z' t.
Proof.
  intros; eapply OS_soundness with (dryspec := io_dry_spec ext_link); eauto.
  - unfold IO_ext_sem; intros; simpl in *.
    if_tac; [|if_tac; [|contradiction]].
    + destruct w as (? & _ & ? & ?).
      admit. (* need putchar_spec *)
    + destruct w as (? & _ & ?).
      destruct H2 as (? & ? & Hpre); subst.
      destruct s; simpl in *.
      unfold sys_getc_wrap_spec in *.
      destruct (sys_getc_spec) eqn:Hspec; inv H4.
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

End IO_safety.
