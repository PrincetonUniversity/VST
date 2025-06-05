Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clight_lemmas.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.external_state.
Require Import VST.veric.Clight_assert_lemmas.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Export VST.veric.lifting.
Require Export VST.veric.env_pred.

Import Ctypes Clight_core.

Local Open Scope nat_scope.
Open Scope maps.

Section mpred.

Context `{!VSTGS OK_ty Σ} (OK_spec : ext_spec OK_ty).

Definition closed_wrt_modvars c (F: environ -> mpred) : Prop :=
    closed_wrt_vars (modifiedvars c) F.

Record semaxArg : Type := SemaxArg {
 sa_cs: compspecs;
 sa_E: coPset;
 sa_Delta: tycontext;
 sa_P: assert;
 sa_c: statement;
 sa_R: ret_assert
}.

Definition make_ext_rval t (v : option val) := match t with Xvoid => None | _ => v end.

Definition semax_external
  ef
  (A: TypeTree)
  (E: dtfr (MaskTT A))
  (P: dtfr (ArgsTT A))
  (Q: dtfr (AssertTT A)) :=
 ∀ gx: genv,
 ∀ x: dtfr A,
   ▷ ∀ F (ts: list typ),
   ∀ args: list val,
   ■ (⌜Val.has_type_list args (map proj_xtype (sig_args (ef_sig ef)))⌝ ∧
     (P x (make_env (Genv.genv_symb gx), args) ∗ F) ={E x}=∗
   ∀ m z, state_interp m z -∗ ∃ x': ext_spec_type OK_spec ef,
    ⌜ext_spec_pre OK_spec ef x' (genv_symb_injective gx) ts args z m⌝ ∧
     (*□*) ∀ tret: xtype, ∀ ret: option val, ∀ m': mem, ∀ z': OK_ty,
      ⌜ext_spec_post OK_spec ef x' (genv_symb_injective gx) tret ret z' m'⌝ → |={E x}=>
          state_interp m' z' ∗ Q x (make_ext_rval tret ret) ∗ F).

Lemma Forall2_implication {A B} (P Q:A -> B -> Prop) (PQ:forall a b, P a b -> Q a b):
  forall l t, Forall2 P l t -> Forall2 Q l t.
Proof. intros; eapply Forall2_impl; eauto. Qed.
Lemma has_type_list_Forall2: forall vals ts, Val.has_type_list vals ts <-> Forall2 Val.has_type vals ts.
Proof.
  induction vals; destruct ts; simpl; split; intros; trivial; try contradiction.
  inv H. inv H.
  destruct H. apply IHvals in H0. constructor; trivial. 
  inv H. apply IHvals in H5. split; trivial.
Qed.

Lemma proj_xtype_argtype: 
  forall a, proj_xtype (argtype_of_type a) = typ_of_type a.
Proof.
destruct a; simpl; auto. destruct i,s; auto. destruct f; auto.
Qed.

Lemma map_proj_xtype_argtype: 
  forall a, map proj_xtype (map argtype_of_type a) = map typ_of_type a.
Proof.
induction a; auto.
simpl; f_equal; auto.
apply proj_xtype_argtype.
Qed.

Lemma semax_external_funspec_sub
  {argtypes rtype cc ef A1 E1 P1 Q1 A E P Q}
  (Hsub: funspec_sub (mk_funspec (argtypes, rtype) cc A1 E1 P1 Q1)
                     (mk_funspec (argtypes, rtype) cc A E P Q))
  (HSIG: ef_sig ef =
         mksignature
                     (map argtype_of_type argtypes)
                     (rettype_of_type rtype) cc):
  semax_external ef A1 E1 P1 Q1 ⊢ semax_external ef A E P Q.
Proof.
  apply bi.forall_mono; intros g.
  iIntros "#H" (x). iIntros "!>" (F ts args) "!> (%HT & P & F)".
  destruct Hsub as [(? & ?) Hsub]; subst.
  iMod (Hsub with "[$P]") as (x1 F1 HE1) "((F1 & P1) & %HQ)".
  { iPureIntro; split; auto.
    rewrite HSIG map_proj_xtype_argtype in HT; apply has_type_list_Forall2 in HT.
    eapply Forall2_implication; [ | apply HT]; auto. }
  iMod (fupd_mask_subseteq (E1 x1)) as "Hmask"; first done.
  iMod ("H" $! _ (F ∗ F1) with "[$P1 $F $F1]") as "H1"; first done.
  iMod "Hmask" as "_".
  iIntros "!>" (??) "s".
  iDestruct ("H1" with "s") as (x') "[? H']".
  iExists x'; iFrame; iIntros (????) "Hpost".
  iMod (fupd_mask_subseteq (E1 x1)) as "Hmask"; first done.
  iMod ("H'" with "Hpost") as "($ & Q1 & $ & F1)".
  iMod "Hmask" as "_".
  iIntros "!>".
  iApply HQ; iFrame.
Qed.

Definition tc_option_val (sig: type) (ret: option val) :=
  match sig, ret with
    | Tvoid, _ => True%type
    | ty, Some v => tc_val ty v
    | _, _ => False%type
  end.

Notation dtfr := (@dtfr Σ).

Definition withtype_empty (A: TypeTree) : Prop := forall (x : dtfr A), False.
Definition believe_external (gx: genv) (v: val) (fsig: typesig) cc
  (A: TypeTree)
  (E: dtfr (MaskTT A))
  (P: dtfr (ArgsTT A))
  (Q: dtfr (AssertTT A)) :=
  match Genv.find_funct gx v with
  | Some (External ef sigargs sigret cc') =>
        ⌜fsig = (sigargs, sigret) /\ cc'=cc
           /\ ef_sig ef = mksignature
                           (map argtype_of_type (fst fsig))
                           (rettype_of_type (snd fsig)) cc
           /\ (ef_inline ef = false \/ withtype_empty A)⌝
        ∧ semax_external ef A E P Q
        ∧ ■ (∀ x: dtfr A,
              ∀ ret:option val,
                Q x (make_ext_rval (rettype_of_type (snd fsig)) ret)
                  ∧ ⌜Builtins0.val_opt_has_rettype ret (rettype_of_type (snd fsig))⌝
                  -∗ ⌜tc_option_val sigret ret⌝)
  | _ => False
  end.

Lemma believe_external_funspec_sub {gx v sig cc A E P Q A' E' P' Q'}
      (Hsub: funspec_sub (mk_funspec sig cc A E P Q) (mk_funspec sig cc A' E' P' Q'))
      (WTE: withtype_empty A -> withtype_empty A'):
      believe_external gx v sig cc A E P Q ⊢ believe_external gx v sig cc A' E' P' Q'.
Proof.
  unfold believe_external.
  destruct (Genv.find_funct gx v); trivial.
  destruct f; trivial. destruct sig as [argtypes rtype].
  iIntros "((% & % & %He & %) & H & #Htc)".
  rewrite semax_external_funspec_sub; [iFrame | eauto..].
  iSplit.
  - iPureIntro; repeat split; auto; tauto.
  - iSplit; first done.
    iIntros "!>" (??) "[Q %]".
    destruct Hsub as [_ Hsub].
    iApply "Htc"; iSplit; last done.
    simpl in *; inv H.
Abort.

Definition fn_typesig (f: function) : typesig := (map snd (fn_params f), fn_return f).

(* the version of this in lifting includes the args, while this believe_internal
   uses close_precondition for the args instead *)
(*Definition stackframe_of' (cenv: composite_env) (f: Clight.function) : mpred.assert :=
  ([∗ list] idt ∈ fn_vars f, var_block' Share.top cenv idt) ∗
  ([∗ list] idt;v ∈ (fn_temps f);(repeat Vundef (length (fn_temps f))), temp (fst idt) v).*)
(* But if we do it this way, then we somehow need to reclaim the param temps in the
   postcondition as well, so maybe we should just use lifting.stackframe_of' instead. *)

Definition claims (ge: genv) (Delta: tycontext) v fsig cc A E P Q : Prop :=
  exists id, (glob_specs Delta) !! id = Some (mk_funspec fsig cc A E P Q) /\
    exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Ptrofs.zero.

Definition believe_internal_ {CS}
  (semax:semaxArg -> mpred.assert)
  (gx: genv) (Delta: tycontext) v (fsig: typesig) cc (A: TypeTree)
  (E: dtfr (MaskTT A))
  (P: dtfr (ArgsTT A))
  (Q: dtfr (AssertTT A)) : mpred.assert :=
  let ce := (@cenv_cs CS) in
  (∃ b: Values.block, ∃ f: function,
   let fparams := fn_params f in
   ⌜v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ Forall (fun it => complete_type ce (snd it) = true) (fn_vars f)
                 /\ list_norepet (map fst fparams ++ map fst f.(fn_temps))
                 /\ list_norepet (map fst f.(fn_vars)) /\ var_sizes_ok ce (f.(fn_vars))
                 /\ fn_typesig f = fsig
                 /\ f.(fn_callconv) = cc⌝
  ∧ ∀ Delta':tycontext, ∀ CS':compspecs,
   ⌜forall f, tycontext_sub (func_tycontext' f Delta) (func_tycontext' f Delta')⌝ →
     ⌜cenv_sub (@cenv_cs CS) (@cenv_cs CS')⌝ →
      (∀ x : dtfr A,
        ▷ semax (SemaxArg CS' (E x) (func_tycontext' f Delta')
                         ((bind_args (f.(fn_params)) (P x) ∗ stackframe_of(cs := CS') f))
                          (f.(fn_body))
           (frame_ret_assert (function_body_ret_assert (fn_return f) (Q x))
              (stackframe_of(cs := CS') f))))).

Definition believepred {CS} (semax:semaxArg -> mpred.assert)
              (Delta: tycontext) (gx: genv) Delta' :=
  ∀ v:val, ∀ fsig: typesig, ∀ cc: calling_convention,
  ∀ A: TypeTree,
  ∀ E: dtfr (MaskTT A),
  ∀ P: dtfr (ArgsTT A),
  ∀ Q: dtfr (AssertTT A),
     ⌜claims gx Delta' v fsig cc A E P Q⌝ →
        (⎡believe_external gx v fsig cc A E P Q⎤
         ∨ @believe_internal_ CS semax gx Delta v fsig cc A E P Q).

Global Instance believe_external_plain gx v fsig cc A E P Q : Plain (believe_external gx v fsig cc A E P Q).
Proof.
  rewrite /believe_external.
  destruct (Genv.find_funct _ _) as [[|]|]; apply _.
Qed.

Definition guard_environ (Delta: tycontext) (f: function) (rho: environ) : Prop :=
   typecheck_environ Delta rho /\ (forall i v, (te_of rho !! i)%stdpp = Some v -> exists t, temp_types Delta !! i = Some t) /\ ret_type Delta = fn_return f.

Definition env_ret_assert Delta ge f (R : ret_assert) : tycontext.ret_assert :=
  Clight_seplog.existential_ret_assert (λ rho, Clight_seplog.frame_ret_assert
    {| tycontext.RA_normal := ⎡RA_normal R rho⎤;
       tycontext.RA_break := ⎡RA_break R rho⎤;
       tycontext.RA_continue := ⎡RA_continue R rho⎤;
       tycontext.RA_return := λ vl, ⎡RA_return R vl rho⎤
    |} (<affine> ⌜guard_environ Delta f rho⌝ ∗ curr_env ge f rho)).

(* semax must be plain (or at least persistent) so we can reuse believe for as many
   functions as we need. *)
Definition semax_
       (semax: semaxArg -d> mpred.assert) : semaxArg -d> mpred.assert := fun a =>
 match a with SemaxArg CS E Delta P c R =>
  ∀ ge Delta' CS', ⌜tycontext_sub Delta Delta' ∧
      cenv_sub (@cenv_cs CS) (@cenv_cs CS') ∧
      cenv_sub (@cenv_cs CS') (genv_cenv ge)⌝ →
    ■ (⎡funassert Delta' ge⎤ -∗
       @believepred CS' semax Delta' ge Delta' -∗
       ∀ f rho, <affine> ⌜guard_environ Delta' f rho⌝ -∗ curr_env ge f rho -∗
       ⎡P rho⎤ -∗ wp OK_spec ge E f c
    (Clight_seplog.frame_ret_assert (env_ret_assert Delta' ge f R) ⎡funassert Delta' ge⎤))
 end.

Local Instance semax_contractive : Contractive semax_.
Proof.
  rewrite /semax_ => n semax semax' Hsemax [??????].
  do 10 f_equiv.
  rewrite /believepred.
  do 15 f_equiv.
  rewrite /believe_internal_.
  do 14 f_equiv.
  f_contractive.
  solve_proper.
Qed.

Definition semax' {CS: compspecs} E Delta P c R : mpred.assert :=
  (fixpoint semax_) (SemaxArg CS E Delta P c R).

Definition believe_internal {CS}
  (gx: genv) (Delta: tycontext) v (fsig: typesig) cc (A: TypeTree)
  (E: dtfr (MaskTT A))
  (P: dtfr (ArgsTT A))
  (Q: dtfr (AssertTT A)) : mpred.assert :=
  let ce := (@cenv_cs CS) in
  (∃ b: Values.block, ∃ f: function,
   let fparams := fn_params f in
   ⌜v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ Forall (fun it => complete_type ce (snd it) = true) (fn_vars f)
                 /\ list_norepet (map fst fparams ++ map fst f.(fn_temps))
                 /\ list_norepet (map fst f.(fn_vars)) /\ var_sizes_ok ce (f.(fn_vars))
                 /\ fn_typesig f = fsig
                 /\ f.(fn_callconv) = cc⌝
  ∧ ∀ Delta':tycontext, ∀ CS':compspecs,
   ⌜forall f, tycontext_sub (func_tycontext' f Delta) (func_tycontext' f Delta')⌝ →
     ⌜cenv_sub (@cenv_cs CS) (@cenv_cs CS')⌝ →
      (∀ x : dtfr A,
        ▷ @semax' CS' (E x) (func_tycontext' f Delta')
                         ((bind_args (f.(fn_params)) (P x) ∗ stackframe_of(cs := CS') f))
                          (f.(fn_body))
           (frame_ret_assert (function_body_ret_assert (fn_return f) (Q x))
              (stackframe_of(cs := CS') f)))).

Definition believe {CS}
              (Delta: tycontext) (gx: genv) Delta' :=
  ∀ v:val, ∀ fsig: typesig, ∀ cc: calling_convention,
  ∀ A: TypeTree,
  ∀ E: dtfr (MaskTT A),
  ∀ P: dtfr (ArgsTT A),
  ∀ Q: dtfr (AssertTT A),
     ⌜claims gx Delta' v fsig cc A E P Q⌝ →
        (⎡believe_external gx v fsig cc A E P Q⎤
         ∨ @believe_internal CS gx Delta v fsig cc A E P Q).

Lemma semax_fold_unfold : forall {CS: compspecs} E Delta P c R,
  semax' E Delta P c R ⊣⊢
  ∀ ge Delta' CS', ⌜tycontext_sub Delta Delta' ∧
      cenv_sub (@cenv_cs CS) (@cenv_cs CS') ∧
      cenv_sub (@cenv_cs CS') (genv_cenv ge)⌝ →
  ■ (⎡funassert Delta' ge⎤ -∗
    @believe CS' Delta' ge Delta' -∗
    ∀ f rho, <affine> ⌜guard_environ Delta' f rho⌝ -∗ curr_env ge f rho -∗
      ⎡P rho⎤ -∗ wp OK_spec ge E f c
    (Clight_seplog.frame_ret_assert (env_ret_assert Delta' ge f R) ⎡funassert Delta' ge⎤)).
Proof.
intros.
unfold semax'.
by rewrite (fixpoint_unfold semax_ _).
Qed.

Lemma semax'_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) E Delta P c R:
      @semax' CS E Delta P c R ⊢ @semax' CS' E Delta P c R.
Proof.
  rewrite !semax_fold_unfold.
  iIntros "H" (??? (? & ? & ?)); iApply ("H" with "[%]").
  split3; auto; apply (cenv_sub_trans CSUB); auto.
Qed.
Lemma semax'_cssub {CS CS'} (CSUB: cspecs_sub CS CS') E Delta P c R:
      @semax' CS E Delta P c R ⊢ @semax' CS' E Delta P c R.
Proof.
  destruct CSUB as [CSUB _].
  apply (@semax'_cenv_sub _ _ CSUB).
Qed.

Definition semax {CS: compspecs} E (Delta: tycontext) P c Q : Prop :=
  ⊢ @semax' CS E Delta P c Q.

Section believe_monotonicity.
Context {CS: compspecs}.

Lemma claims_antimono gx Gamma v sig cc E A P Q Gamma' 
  (SUB: forall id spec, (glob_specs Gamma') !! id = Some spec ->
                        (glob_specs Gamma) !! id = Some spec)
  (CL: claims gx Gamma' v sig cc E A P Q):
  claims gx Gamma v sig cc E A P Q.
Proof. destruct CL as [id [Hid X]]; exists id; split; auto. Qed.

Lemma believe_antimonoR gx Delta Gamma Gamma'
  (DG1: forall id spec, (glob_specs Gamma') !! id = Some spec ->
                        (glob_specs Gamma) !! id = Some spec):
  @believe CS Delta gx Gamma ⊢ @believe CS Delta gx Gamma'.
Proof. rewrite /believe. iIntros "H" (????????); iApply "H". iPureIntro; eapply claims_antimono; eauto. Qed.

Lemma cenv_sub_complete_legal_cosu_type cenv1 cenv2 (CSUB: cenv_sub cenv1 cenv2): forall t,
    @composite_compute.complete_legal_cosu_type cenv1 t = true ->
    @composite_compute.complete_legal_cosu_type cenv2 t = true.
Proof.
  induction t; simpl; intros; auto. 
  + specialize (CSUB i). red in CSUB.
    destruct (Maps.PTree.get i cenv1); [rewrite CSUB; trivial | inv H].
  + specialize (CSUB i). red in CSUB.
    destruct (Maps.PTree.get i cenv1); [rewrite CSUB; trivial | inv H].
Qed.

Lemma complete_type_cenv_sub {ce ce'} (C: cenv_sub ce ce') t (T:complete_type ce t = true):
  complete_type ce' t = true.
Proof. apply (complete_type_stable ce ce'); trivial. intros. specialize (C id). setoid_rewrite H in C; apply C.
Qed.
Lemma complete_type_cspecs_sub {cs cs'} (C: cspecs_sub cs cs') t (T:complete_type (@cenv_cs cs) t = true):
  complete_type (@cenv_cs cs') t = true.
Proof. destruct C. apply (complete_type_cenv_sub H _ T). Qed.

Lemma believe_internal_cenv_sub {CS'} gx Delta Delta' v sig cc A E P Q
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta'))
  (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) :
  @believe_internal CS gx Delta v sig cc A E P Q ⊢
  @believe_internal CS' gx Delta' v sig cc A E P Q.
Proof.
  rewrite /believe_internal.
  iIntros "H"; iDestruct "H" as (b f Hv) "H".
  iExists b, f; iSplit.
  - iPureIntro; intuition.
    + eapply List.Forall_impl, H0. simpl; intros.
      apply (complete_type_cenv_sub CSUB); auto.
    + rewrite /var_sizes_ok !Forall_forall in H0 H4 |- *; intros.
      rewrite (cenv_sub_sizeof CSUB); eauto.
  - iIntros (?????); iApply ("H" with "[%] [%]").
    + simpl; intros. eapply tycontext_sub_trans; eauto.
    + apply (cenv_sub_trans CSUB); auto.
Qed.
Lemma believe_internal_mono {CS'} gx Delta Delta' v sig cc A E P Q
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta'))
  (CSUB: cspecs_sub  CS CS') :
  @believe_internal CS gx Delta v sig cc A E P Q ⊢
  @believe_internal CS' gx Delta' v sig cc A E P Q.
Proof.
  destruct CSUB as [CSUB _].
  eapply (@believe_internal_cenv_sub CS'). apply SUB. apply CSUB.
Qed. 

Lemma believe_cenv_sub_L {CS'} gx Delta Delta' Gamma
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta'))
  (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')):
  @believe CS Delta gx Gamma ⊢ @believe CS' Delta' gx Gamma.
Proof.
  rewrite /believe.
  iIntros "H" (????????); iDestruct ("H" with "[%]") as "[?|?]"; eauto.
  iRight; by iApply (believe_internal_cenv_sub with "[$]").
Qed.
Lemma believe_monoL {CS'} gx Delta Delta' Gamma
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta'))
  (CSUB: cspecs_sub CS CS'):
  @believe CS Delta gx Gamma ⊢ @believe CS' Delta' gx Gamma.
Proof.
  destruct CSUB as [CSUB _].
  eapply (@believe_cenv_sub_L CS'). apply SUB. apply CSUB.
Qed.

Lemma believe_internal__mono sem gx Delta Delta' v sig cc A E P Q
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta')) :
  @believe_internal_ CS sem gx Delta v sig cc A E P Q ⊢
  @believe_internal_ CS sem gx Delta' v sig cc A E P Q.
Proof.
  rewrite /believe_internal_.
  iIntros "H"; iDestruct "H" as (b f Hv) "H".
  iExists b, f; iSplit; first trivial.
  iIntros (?????); iApply ("H" with "[%] [%]"); last done.
  simpl; intros. eapply tycontext_sub_trans; eauto.
Qed.

End believe_monotonicity.

 Lemma semax__mono {CS} E Delta Delta'
  (SUB: tycontext_sub Delta Delta') sem P c R:
  @semax_ sem {| sa_cs := CS; sa_E := E; sa_Delta := Delta; sa_P := P; sa_c := c; sa_R := R |} ⊢
  @semax_ sem {| sa_cs := CS; sa_E := E; sa_Delta := Delta'; sa_P := P; sa_c := c; sa_R := R |}.
Proof.
  unfold semax_.
  iIntros "H" (??? (? & ? & ?)).
  iApply "H"; iPureIntro; split; auto.
  eapply tycontext_sub_trans; eauto.
Qed.

Lemma semax_mono {CS} E Delta Delta' P Q
  (SUB: tycontext_sub Delta Delta') c:
  @semax' CS E Delta P c Q ⊢
  @semax' CS E Delta' P c Q.
Proof.
  rewrite !semax_fold_unfold.
  do 9 f_equiv.
  rewrite /impl.
  by apply tycontext_sub_trans.
Qed.

Lemma semax_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) E Delta P c R:
      @semax CS E Delta P c R -> @semax CS' E Delta P c R.
Proof.
  by rewrite /semax -(semax'_cenv_sub CSUB).
Qed.
Lemma semax_cssub {CS CS'} (CSUB: cspecs_sub  CS CS') E Delta P c R:
      @semax CS E Delta P c R -> @semax CS' E Delta P c R.
Proof.
  by rewrite /semax -(semax'_cssub CSUB).
Qed.

Lemma semax_mask_mono {CS} E E' Delta P Q
  (SUB: E ⊆ E') c:
  @semax' CS E Delta P c Q ⊢
  @semax' CS E' Delta P c Q.
Proof.
  rewrite !semax_fold_unfold.
  do 17 f_equiv.
  by apply wp_mask_mono.
Qed.

Lemma believe_internal_mask_mono {CS} gx Delta v sig cc A (E E' : dtfr (MaskTT A)) P Q
  (SUB: forall x, E x ⊆ E' x) :
  @believe_internal CS gx Delta v sig cc A E P Q ⊢
  @believe_internal CS gx Delta v sig cc A E' P Q.
Proof.
  rewrite /believe_internal.
  do 14 f_equiv.
  by apply semax_mask_mono.
Qed.

End mpred.
