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

Section ext_trace.

  Context {event : Type -> Type} {J : juicy_ext_spec (itree event unit)} {OS_state : Type}.
  Variable prog : Clight.program.
  Variable ext_sem : external_function -> list val -> OS_state -> option (OS_state * option val * @trace event unit).
  Variable inj_mem : external_function -> list val -> mem -> @trace event unit -> OS_state -> Prop.
  Variable extr_mem : external_function -> list val -> mem -> OS_state -> mem.
  Variable OS_valid : OS_state -> Prop.
  Notation ge := (globalenv prog).

  Instance Espec : OracleKind := Build_OracleKind (itree event unit) J.

  (* For any trace that the new itree (z) allows, that trace prefixed with the
     OS-generated trace (t) is allowed by the old itree (z0). *)
  Definition consume_trace (z z' : itree event unit) (t : @trace event unit) :=
    forall t', is_trace z' t' -> is_trace z (app_trace t t').

  Lemma consume_trace_nil : forall z, consume_trace z z TEnd.
  Proof.
    repeat intro; auto.
  Qed.

  Lemma app_trace_assoc : forall {E : Type -> Type} {R : Type} (t t' t'' : @trace E R),
    app_trace (app_trace t t') t'' = app_trace t (app_trace t' t'').
  Proof.
    induction t; auto; simpl; intros.
    rewrite IHt; auto.
  Qed.

  Lemma consume_trace_app : forall z z' z'' t t', consume_trace z z' t -> consume_trace z' z'' t' ->
    consume_trace z z'' (app_trace t t').
  Proof.
    unfold consume_trace; intros.
    rewrite app_trace_assoc; auto.
  Qed.

  Inductive ext_safeN_trace : nat -> @trace event unit -> Ensemble (@trace event unit) -> OK_ty -> CC_core -> mem -> Prop :=
  | ext_safeN_trace_0: forall z t c m, ext_safeN_trace O t (Singleton _ TEnd) z c m
  | ext_safeN_trace_step:
      forall n t traces z c m c' m',
      cl_step ge c m c' m' ->
      ext_safeN_trace n t traces z c' m' ->
      ext_safeN_trace (S n) t traces z c m
  | ext_safeN_trace_external:
      forall n t traces z c m e args,
      cl_at_external c = Some (e,args) ->
      (forall s s' ret m' t' n'
         (Hargsty : Val.has_type_list args (sig_args (ef_sig e)))
         (Hretty : Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))),
         inj_mem e args m t s ->
         ext_sem e args s = Some (s', ret, t') ->
         m' = extr_mem e args m s' ->
         (n' <= n)%nat ->
         OS_valid s' /\ exists traces' z' c', consume_trace z z' t' /\
           cl_after_external ret c = Some c' /\
           ext_safeN_trace n' (app_trace t t') traces' z' c' m' /\
           (forall t'', In _ traces' t'' -> In _ traces (app_trace t' t''))) ->
      (forall t1, In _ traces t1 ->
        exists s s' ret m' t' n', Val.has_type_list args (sig_args (ef_sig e)) /\
         Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e)) /\
         inj_mem e args m t s /\ ext_sem e args s = Some (s', ret, t') /\ m' = extr_mem e args m s' /\
         (n' <= n)%nat /\ OS_valid s' /\ exists traces' z' c', consume_trace z z' t' /\
           cl_after_external ret c = Some c' /\ ext_safeN_trace n' (app_trace t t') traces' z' c' m' /\
        exists t'', In _ traces' t'' /\ t1 = app_trace t' t'') ->
      ext_safeN_trace (S n) t traces z c m
  | ext_safeN_trace_halted: forall n z t c m i,
      halted (cl_core_sem ge) c i ->
      ext_safeN_trace n t (Singleton _ TEnd) z c m.

  Variable dryspec : ext_spec OK_ty.
  Hypothesis extcalls_correct : forall e w b tl args z m t s, ext_spec_pre dryspec e w b tl args z m ->
    inj_mem e args m t s ->
    forall s' ret t', Some (s', ret, t') = ext_sem e args s ->
    OS_valid s' /\ exists z', consume_trace z z' t' /\
    ext_spec_post dryspec e w b (sig_res (ef_sig e)) ret z' (extr_mem e args m s').

  Lemma dry_safe_ext_trace_safe : forall n t z q m,
    step_lemmas.dry_safeN(genv_symb := semax.genv_symb_injective)
     (cl_core_sem (globalenv prog)) dryspec
     (Build_genv (Genv.globalenv prog) (prog_comp_env prog)) n z q m ->
    exists traces, ext_safeN_trace n t traces z q m.
  Proof.
    induction n as [n IHn] using lt_wf_ind; intros; inversion H; subst.
    - eexists; constructor.
    - edestruct IHn as [traces ?]; eauto; exists traces; econstructor; eauto.
    - exists (fun t1 => exists s s' ret m' t' n', Val.has_type_list args (sig_args (ef_sig e)) /\
         Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e)) /\
         inj_mem e args m t s /\ ext_sem e args s = Some (s', ret, t') /\ m' = extr_mem e args m s' /\
         (n' <= n0)%nat /\ OS_valid s' /\ exists traces' z' c', consume_trace z z' t' /\
           cl_after_external ret q = Some c' /\ ext_safeN_trace n' (app_trace t t') traces' z' c' m' /\
        exists t'', In _ traces' t'' /\ t1 = app_trace t' t'').
      eapply ext_safeN_trace_external; eauto; intros.
      eapply extcalls_correct in H1 as (z' & ? & ? & ?); eauto.
      split; auto.
      edestruct H2 as (? & ? & Hsafe); eauto.
      eapply IHn in Hsafe as [traces ?]; [|lia].
      subst; do 4 eexists; eauto; split; eauto; split; eauto.
      intros; unfold In; eauto 25.
    - eexists; econstructor; eauto.
  Qed.

  Lemma safety_trace:
   forall {CS: compspecs} (initial_oracle: OK_ty)
     (EXIT: semax_prog.postcondition_allows_exit Espec tint)
     (dessicate : forall (ef : external_function) jm,
               ext_spec_type OK_spec ef ->
               ext_spec_type dryspec ef)
     (JDE: juicy_dry_ext_spec _ (@JE_spec OK_ty OK_spec) dryspec dessicate)
     (DME: ext_spec_mem_evolve _ dryspec)
     V G m,
     @semax_prog Espec CS prog initial_oracle V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q,
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       initial_core  (cl_core_sem (globalenv prog))
           0 m q m (Vptr b Ptrofs.zero) nil /\
       forall n, exists traces, ext_safeN_trace n TEnd traces initial_oracle q m.
  Proof.
    intros.
    eapply CSHL_Sound.semax_prog_sound, whole_program_sequential_safety_ext in H as (b & q & ? & ? & Hsafe); eauto.
    do 3 eexists; eauto; split; eauto; intros n.
    eapply dry_safe_ext_trace_safe; eauto.
  Qed.

  Lemma trace_correct:
   forall n (z: OK_ty) q m t traces t',
    ext_safeN_trace n t traces z q m ->
    In _ traces t' ->
    exists z', consume_trace z z' t'.
  Proof.
    induction n as [n IHn] using lt_wf_ind; intros; inversion H; subst.
    - inversion H0.
      exists z; apply consume_trace_nil.
    - eauto.
    - destruct (H3 _ H0) as (s & s' & ret & m' & t1 & n' & ? & ? & ? & ? & ? & ? & ? & traces' & z' & c' & ? & ? & ? & ? & ? & ?).
      edestruct (IHn n') as [z'' ?]; eauto; [lia|].
      subst; eexists; eapply consume_trace_app; eauto.
    - inversion H0.
      exists z; apply consume_trace_nil.
  Qed.

  Theorem OS_soundness:
   forall {CS: compspecs} (initial_oracle: OK_ty)
     (EXIT: semax_prog.postcondition_allows_exit Espec tint)
     (dessicate : forall (ef : external_function) jm,
               ext_spec_type OK_spec ef ->
               ext_spec_type dryspec ef)
     (JDE: juicy_dry_ext_spec _ (@JE_spec OK_ty OK_spec) dryspec dessicate)
     (DME: ext_spec_mem_evolve _ dryspec)
     V G m,
     @semax_prog Espec CS prog initial_oracle V G ->
     Genv.init_mem prog = Some m ->
     exists b, exists q,
       Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
       initial_core  (cl_core_sem (globalenv prog))
           0 m q m (Vptr b Ptrofs.zero) nil /\
       forall n, exists traces, ext_safeN_trace n TEnd traces initial_oracle q m /\
         forall t, In _ traces t -> exists z', consume_trace initial_oracle z' t.
  Proof.
    intros.
    eapply safety_trace in H as (b & q & ? & ? & Hsafe); eauto.
    exists b, q; split; auto; split; auto.
    intros n; destruct (Hsafe n) as [traces Hsafen].
    exists traces; split; auto.
    intros; eapply trace_correct; eauto.
  Qed.

End ext_trace.
