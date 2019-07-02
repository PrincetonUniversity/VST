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

Context `{ThreadsConfigurationOps}.
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
     initial_core (cl_core_sem (globalenv prog))
         0 m q m' (Vptr b Ptrofs.zero) nil /\
   forall n, exists traces, ext_safeN_trace(J := OK_spec) prog IO_ext_sem IO_inj_mem OS_mem n traces initial_oracle q m' /\
     forall t, In _ traces t -> exists z', consume_trace initial_oracle z' t.
Proof.
  intros; eapply OS_soundness with (dryspec := io_dry_spec ext_link); eauto.
  - unfold IO_ext_sem; intros; simpl in *.
    if_tac; [|if_tac; [|contradiction]].
    + destruct w as (? & _ & ? & ?).
      destruct H2 as (? & ? & Hpre); subst.
      destruct s; simpl in *.
      unfold sys_putc_wrap_spec in *.
      destruct (sys_putc_spec) eqn:Hspec; inv H4.
      admit. (* need putc_correct *)
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
