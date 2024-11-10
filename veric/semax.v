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
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Export VST.veric.lifting.

Import Ctypes Clight_core.

Local Open Scope nat_scope.
Open Scope maps.

Section mpred.

Context `{!VSTGS OK_ty Σ} (OK_spec : ext_spec OK_ty).

Definition closed_wrt_modvars c (F: assert) : Prop :=
    closed_wrt_vars (modifiedvars c) F.

(*Inductive contx :=
| Stuck
| Cont: cont -> contx
| Ret: option val -> cont -> contx.

Definition assert_safe
     (ge: genv) (E: coPset) (f: function) (ve: env) (te: temp_env) (ctl: contx) : assert :=
      assert_of (fun rho =>
       ∀ ora, (* ext_compat ora -> *)
       ⌜rho = construct_rho (filter_genv ge) ve te⌝ →
       match ctl with
       | Stuck => |={E}=> False
       | Cont (Kseq s ctl') => 
             jsafeN OK_spec ge E ora (State f s ctl' ve te)
       | Cont (Kloop1 body incr ctl') =>
             jsafeN OK_spec ge E ora (State f Sskip (Kloop1 body incr ctl') ve te)
       | Cont (Kloop2 body incr ctl') =>
             jsafeN OK_spec ge E ora (State f (Sloop body incr) ctl' ve te)
       | Cont (Kcall id' f' ve' te' k') => 
             jsafeN OK_spec ge E ora (State f (Sreturn None) (Kcall id' f' ve' te' k') ve te)
       | Cont Kstop =>
             jsafeN OK_spec ge E ora (State f (Sreturn None) Kstop ve te)
       | Cont _ => |={E}=> False
       | Ret None ctl' =>
                jsafeN OK_spec ge E ora (State f (Sreturn None) ctl' ve te)
       | Ret (Some v) ctl' => ∀ e, (∀ m, mem_auth m -∗ ⌜∃ v', Clight.eval_expr ge ve te m e v' ∧ Cop.sem_cast v' (typeof e) (fn_return f) m = Some v⌝) →
              (* Could we replace these with eval_expr and lose the memory dependence?
                 Right now, the only difference is that e must only access pointers that are valid in the current rmap.
                 But typechecking will also guarantee that. *)
              jsafeN OK_spec ge E ora (State f (Sreturn (Some e)) ctl' ve te)
       end).

Lemma assert_safe_mono ge E1 E2 f ve te ctl: E1 ⊆ E2 ->
  assert_safe ge E1 f ve te ctl ⊢ assert_safe ge E2 f ve te ctl.
Proof.
  rewrite /assert_safe; split => ? /=.
  iIntros "H" (? ->); iSpecialize ("H" $! _ eq_refl).
  destruct ctl.
  - iMod (fupd_mask_subseteq E1); first done; iMod "H" as "[]".
  - destruct c; try by iApply jsafe_mask_mono.
    iMod (fupd_mask_subseteq E1); first done; iMod "H" as "[]".
  - destruct o; last by iApply jsafe_mask_mono.
    iIntros (e); iSpecialize ("H" $! e).
    iApply (bi.impl_intro_r with "H").
    iIntros "H".
    iPoseProof (bi.impl_elim_l with "H") as "?".
    by iApply jsafe_mask_mono.
Qed.*)

Definition list2opt {T: Type} (vl: list T) : option T :=
 match vl with nil => None | x::_ => Some x end.

Definition guard_environ (Delta: tycontext) (f: function) (rho: environ) : Prop :=
   typecheck_environ Delta rho /\
    match_venv (ve_of rho) (fn_vars f)
   /\ ret_type Delta = fn_return f.

Lemma guard_environ_e1:
   forall Delta f rho, guard_environ Delta f rho ->
     typecheck_environ Delta rho.
Proof. intros. destruct H; auto. Qed.

(* Definition _guard
    (gx: genv) E (Delta: tycontext) (f: function) (P : assert) (ctl: contx) : mpred :=
     ∀ tx : Clight.temp_env, ∀ vx : env,
          let rho := construct_rho (filter_genv gx) vx tx in
          ■ (⌜guard_environ Delta f rho⌝
                  ∧ P rho ∗ funassert Delta rho
             -∗ assert_safe gx E f vx tx ctl rho).

Definition guard'
    (gx: genv) E (Delta: tycontext) f P  (ctl: cont) :=
  _guard gx E Delta f P (Cont ctl).

Definition exit_cont (ek: exitkind) (vl: option val) (k: cont) : contx :=
  match ek with
  | EK_normal => match vl with None => Cont k | Some _ => Stuck end
  | EK_break => break_cont k
  | EK_continue => continue_cont k
  | EK_return => Ret vl (call_cont k)
  end.

Definition rguard
    (gx: genv) E (Delta: tycontext) (f: function) (R : ret_assert) (ctl: cont) : mpred :=
  ∀ ek: exitkind, ∀ vl: option val,
    _guard gx E Delta f (proj_ret_assert R ek vl) (exit_cont ek vl ctl). *)

Record semaxArg :Type := SemaxArg {
 sa_cs: compspecs;
 sa_E: coPset;
 sa_Delta: tycontext;
 sa_P: assert;
 sa_c: statement;
 sa_R: ret_assert
}.

Definition make_ext_rval  (gx: genviron) (tret: rettype) (v: option val):=
  match tret with AST.Tvoid => mkEnviron gx (Map.empty _) (Map.empty _) 
 | _ => 
  match v with
  | Some v' =>  mkEnviron gx (Map.empty _)
                              (Map.set 1%positive v' (Map.empty _))
  | None => mkEnviron gx (Map.empty _) (Map.empty _)
  end end.

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
   ■ (⌜Val.has_type_list args (sig_args (ef_sig ef))⌝ ∧
     (P x (filter_genv gx, args) ∗ F) ={E x}=∗
   ∀ m z, state_interp m z -∗ ∃ x': ext_spec_type OK_spec ef,
    ⌜ext_spec_pre OK_spec ef x' (genv_symb_injective gx) ts args z m⌝ ∧
     (*□*) ∀ tret: rettype, ∀ ret: option val, ∀ m': mem, ∀ z': OK_ty,
      ⌜ext_spec_post OK_spec ef x' (genv_symb_injective gx) tret ret z' m'⌝ → |={E x}=>
          state_interp m' z' ∗ Q x (make_ext_rval (filter_genv gx) tret ret) ∗ F).

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

Lemma semax_external_funspec_sub
  {argtypes rtype cc ef A1 E1 P1 Q1 A E P Q}
  (Hsub: funspec_sub (mk_funspec (argtypes, rtype) cc A1 E1 P1 Q1)
                     (mk_funspec (argtypes, rtype) cc A E P Q))
  (HSIG: ef_sig ef =
         mksignature
                     (map typ_of_type argtypes)
                     (rettype_of_type rtype) cc):
  semax_external ef A1 E1 P1 Q1 ⊢ semax_external ef A E P Q.
Proof.
  apply bi.forall_mono; intros g.
  iIntros "#H" (x). iIntros "!>" (F ts args) "!> (%HT & P & F)".
  destruct Hsub as [(? & ?) Hsub]; subst.
  iMod (Hsub with "[$P]") as (x1 F1 HE1) "((F1 & P1) & %HQ)".
  { iPureIntro; split; auto.
    rewrite HSIG in HT; apply has_type_list_Forall2 in HT.
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
  iApply (HQ with "[$F1 $Q1]"); iPureIntro; split; auto.
  destruct tret, ret; auto.
Qed.

Definition tc_option_val (sig: type) (ret: option val) :=
  match sig, ret with
    | Tvoid, _ => True%type
    | ty, Some v => tc_val ty v
    | _, _ => False%type
  end.

Fixpoint zip_with_tl {A : Type} (l1 : list A) (l2 : typelist) : list (A*type) :=
  match l1, l2 with
    | a::l1', Tcons b l2' => (a,b)::zip_with_tl l1' l2'
    | _, _ => nil
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
        ⌜fsig = (typelist2list sigargs, sigret) /\ cc'=cc
           /\ ef_sig ef = mksignature
                           (typlist_of_typelist (typelist_of_type_list (fst fsig)))
                           (rettype_of_type (snd fsig)) cc
           /\ (ef_inline ef = false \/ withtype_empty A)⌝
        ∧ semax_external ef A E P Q
        ∧ ■ (∀ x: dtfr A,
              ∀ ret:option val,
                Q x (make_ext_rval (filter_genv gx) (rettype_of_type (snd fsig)) ret)
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
  rewrite TTL2 in He |- *.
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

Definition var_sizes_ok (cenv: composite_env) (vars: list (ident*type)) :=
   Forall (fun var : ident * type => @sizeof cenv (snd var) <= Ptrofs.max_unsigned)%Z vars.

Definition var_block' (sh: Share.t) (cenv: composite_env) (idt: ident * type): assert :=
  ⌜(sizeof (snd idt) <= Ptrofs.max_unsigned)%Z⌝ ∧
  assert_of (fun rho => (memory_block sh (sizeof (snd idt))) (eval_lvar (fst idt) (snd idt) rho)).

Definition stackframe_of' (cenv: composite_env) (f: Clight.function) : assert :=
  fold_right bi_sep emp
     (map (fun idt => var_block' Share.top cenv idt) (Clight.fn_vars f)).

Definition claims (ge: genv) (Delta: tycontext) v fsig cc A E P Q : Prop :=
  exists id, (glob_specs Delta) !! id = Some (mk_funspec fsig cc A E P Q) /\
    exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Ptrofs.zero.

Definition believe_internal {CS}
  (gx: genv) v (fsig: typesig) cc (A: TypeTree)
  (E: dtfr (MaskTT A))
  (P: dtfr (ArgsTT A))
  (Q: dtfr (AssertTT A)) : assert :=
  let ce := (@cenv_cs CS) in
  (∃ b: Values.block, ∃ f: function,
   let fparams := fn_params f in
   ⌜v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ Forall (fun it => complete_type ce (snd it) = true) (fn_vars f)
                 /\ list_norepet (map fst fparams ++ map fst f.(fn_temps))
                 /\ list_norepet (map fst f.(fn_vars)) /\ var_sizes_ok ce (f.(fn_vars))
                 /\ fn_typesig f = fsig
                 /\ f.(fn_callconv) = cc⌝
  ∧ ∀ CS', ⌜cenv_sub (@cenv_cs CS) (@cenv_cs CS')⌝ →
■ ∀ x : dtfr A, ▷ ((bind_args f.(fn_params) (argsassert_of (P x)) ∗ stackframe_of' (@cenv_cs CS') f) -∗
         wp OK_spec gx (E x) f f.(fn_body)
           (frame_ret_assert (function_body_ret_assert f.(fn_return) (assert_of (Q x))) (stackframe_of' (@cenv_cs CS') f)))).
(* might need the recursive construction after all, so that we can use believe in
   proving all the funspecs *)

Definition believe {CS}
              (Delta: tycontext) (gx: genv) :=
  ∀ v:val, ∀ fsig: typesig, ∀ cc: calling_convention,
  ∀ A: TypeTree,
  ∀ E: dtfr (MaskTT A),
  ∀ P: dtfr (ArgsTT A),
  ∀ Q: dtfr (AssertTT A),
       ⌜claims gx Delta v fsig cc A E P Q⌝ →
      (⎡believe_external gx v fsig cc A E P Q⎤
        ∨ @believe_internal CS gx v fsig cc A E P Q).

Global Instance believe_external_plain gx v fsig cc A E P Q : Plain (believe_external gx v fsig cc A E P Q).
Proof.
  rewrite /believe_external.
  destruct (Genv.find_funct _ _) as [[|]|]; apply _.
Qed.

Definition semax' {CS} E Delta P c R :=
  ∀ ge Delta' CS', ⌜tycontext_sub Delta Delta' ∧
      cenv_sub (@cenv_cs CS) (@cenv_cs CS') ∧
      cenv_sub (@cenv_cs CS') (genv_cenv ge)⌝ →
  <affine> local (typecheck_environ Delta') -∗
  funassert Delta' -∗
  <affine> @believe CS' Delta' ge -∗
  ∀ f, P -∗ wp OK_spec ge E f c
    (frame_ret_assert R (<affine> local (typecheck_environ Delta') ∗ funassert Delta')).

Lemma semax'_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) E Delta P c R:
      @semax' CS E Delta P c R ⊢ @semax' CS' E Delta P c R.
Proof.
  rewrite /semax'.
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

 Lemma believe_antimonoR gx Gamma Gamma'
  (DG1: forall id spec, (glob_specs Gamma') !! id = Some spec ->
                        (glob_specs Gamma) !! id = Some spec):
  @believe CS Gamma gx ⊢ @believe CS Gamma' gx.
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

Lemma believe_internal_cenv_sub {CS'} gx v sig cc A E P Q
  (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) :
  @believe_internal CS gx v sig cc A E P Q ⊢
  @believe_internal CS' gx v sig cc A E P Q.
Proof.
  rewrite /believe_internal.
  do 7 f_equiv.
  - rewrite /impl; intuition.
    + eapply Forall_impl. apply H. simpl; intros.
      apply (complete_type_cenv_sub CSUB); auto.
    + rewrite /var_sizes_ok !Forall_forall in H H3 |- *; intros.
      rewrite (cenv_sub_sizeof CSUB); eauto.
  - do 2 f_equiv.
(*     + simpl; intros. eapply tycontext_sub_trans; eauto. *)
    + rewrite /impl; apply (cenv_sub_trans CSUB).
Qed.
Lemma believe_internal_mono {CS'} gx v sig cc A E P Q
  (CSUB: cspecs_sub  CS CS') :
  @believe_internal CS gx v sig cc A E P Q ⊢
  @believe_internal CS' gx v sig cc A E P Q.
Proof.
  destruct CSUB as [CSUB _].
  eapply (@believe_internal_cenv_sub CS'). apply CSUB.
Qed. 

(* Lemma believe_cenv_sub_L {CS'} gx Delta Delta'
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta'))
  (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')):
  @believe CS Delta gx ⊢ @believe CS' Delta' gx.
Proof.
  rewrite /believe.
  iIntros "H" (????????); iDestruct ("H" with "[%]") as "[?|?]"; eauto.
  + eapply claims_antimono, H.
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
Qed. *)

(* Lemma believe_internal__mono gx Delta Delta' v sig cc A E P Q
  (SUB: forall f, tycontext_sub (func_tycontext' f Delta)
                                (func_tycontext' f Delta')) :
  believe_internal CS gx Delta v sig cc A E P Q ⊢
  believe_internal CS gx Delta' v sig cc A E P Q.
Proof.
  rewrite /believe_internal.
  iIntros "H"; iDestruct "H" as (b f Hv) "H".
  iExists b, f; iSplit; first trivial.
  iIntros (??); iApply ("H" with "[%]"); last done.
Qed. *)

End believe_monotonicity.

(* Lemma semax__mono {CS} E Delta Delta'
  (SUB: tycontext_sub Delta Delta') sem P c R:
  @semax_ sem {| sa_cs := CS; sa_E := E; sa_Delta := Delta; sa_P := P; sa_c := c; sa_R := R |} ⊢
  @semax_ sem {| sa_cs := CS; sa_E := E; sa_Delta := Delta'; sa_P := P; sa_c := c; sa_R := R |}.
Proof.
  unfold semax_.
  iIntros "H" (??? (? & ? & ?)).
  iApply "H"; iPureIntro; split; auto.
  eapply tycontext_sub_trans; eauto.
Qed. *)

Lemma semax_mono {CS} E Delta Delta' P Q
  (SUB: tycontext_sub Delta Delta') c:
  @semax' CS E Delta P c Q ⊢
  @semax' CS E Delta' P c Q.
Proof.
  rewrite /semax'.
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
  rewrite /semax'.
  do 13 f_equiv.
  by apply wp_mask_mono.
Qed.

Lemma believe_internal_mask_mono {CS} gx v sig cc A (E E' : dtfr (MaskTT A)) P Q
  (SUB: forall x, E x ⊆ E' x) :
  @believe_internal CS gx v sig cc A E P Q ⊢
  @believe_internal CS gx v sig cc A E' P Q.
Proof.
  rewrite /believe_internal.
  do 13 f_equiv.
  by apply wp_mask_mono.
Qed.

End mpred.
