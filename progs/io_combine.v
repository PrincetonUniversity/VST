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

Section ext_safe.

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
       forall n,
        ext_safeN
             n initial_oracle q m'.
  Proof.
    intros.
    eapply CSHL_Sound.semax_prog_ext_sound, whole_program_sequential_safety_ext in H as (b & q & m' & ? & ? & Hsafe); eauto.
    do 4 eexists; eauto; split; eauto; intro n.
    eapply dry_safe_ext_safe; eauto.
  Qed.

End ext_safe.

Require Import VST.progs.io_dry.
Require Import VST.progs.io_os_connection.

Section IO_safety.

Variable (prog : Clight.program).

Definition ext_link := ext_link_prog prog.

Definition IO_ext_sem e (args : list val) s :=
  if oi_eq_dec (Some (ext_link "putchar"%string, funsig2signature ([(1%positive, tint)], tint) cc_default))
    (ef_id_sig ext_link e) then
    (* putchar_spec (Znth 0 args) s *) (s, None, []) else
  if oi_eq_dec  (Some (ext_link "getchar"%string, funsig2signature ([], tint) cc_default))
    (ef_id_sig ext_link e) then
    let '(s', ret, t') := getchar_spec s in (s', Some (Vint (Int.repr ret)), t')
  else (s, None, []).

Context {Hclen : ConsoleLen} {Horacle : SerialOracle}.

Definition IO_inj_mem m s := st_mem s = m /\ valid_state s. (* stub *)

Instance Espec : OracleKind := io_specs.IO_Espec ext_link.

Theorem IO_OS_safety:
 forall {CS: compspecs} (initial_oracle: OK_ty) V G m,
   semax_prog_ext prog initial_oracle V G ->
   Genv.init_mem prog = Some m ->
   exists b, exists q, exists m',
     Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
     initial_core  (cl_core_sem (globalenv prog))
         0 m q m' (Vptr b Ptrofs.zero) nil /\
     forall n,
      ext_safeN prog IO_ext_sem consume_trace IO_inj_mem st_mem
           n initial_oracle q m'.
Proof.
  intros; eapply OS_safety with (dryspec := io_dry_spec ext_link); eauto.
  - unfold IO_ext_sem; intros; simpl in *.
    destruct H2 as [? Hvalid]; subst.
    if_tac; [|if_tac; [|contradiction]].
    + destruct w as (? & _ & ? & ?).
      admit. (* need putchar_spec *)
    + destruct w as (? & _ & ?).
      destruct H1 as (? & ? & Hpre); subst.
      destruct s; simpl in *.
      eapply getchar_correct in Hvalid as (? & r & ? & -> & Hpost & ?).
      * do 2 eexists; eauto.
        unfold getchar_post, getchar_post' in *.
        destruct Hpost as [? Hpost]; split; auto.
        destruct Hpost as [[]|[-> ->]]; split; try (simpl in *; omega).
        -- rewrite if_false by omega; eauto.
        -- rewrite if_true; auto.
      * unfold getchar_pre, getchar_pre' in *.
        apply Traces.sutt_trace_incl; auto.
  - apply juicy_dry_specs.
  - apply dry_spec_mem.
Admitted.

End IO_safety.
