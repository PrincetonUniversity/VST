Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clight_lemmas.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.external_state.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.

Import Ctypes Clight_core.

Local Open Scope nat_scope.
Open Scope maps.

Definition genv_symb_injective {F V} (ge: Genv.t F V) : extspec.injective_PTree Values.block.
Proof.
exists (Genv.genv_symb ge).
hnf; intros.
eapply Genv.genv_vars_inj; eauto.
Defined.

Section mpred.

Context `{!heapGS Σ} (Espec : OracleKind) `{!externalGS OK_ty Σ}.

Definition closed_wrt_modvars c (F: @assert Σ) : Prop :=
    closed_wrt_vars (modifiedvars c) F.

Definition jsafeN (ge: genv) :=
  jsafe(genv_symb := genv_symb_injective) (cl_core_sem ge) OK_spec ge.

(*Definition ext_compat (ora : Z) (w : rmap) :=
  joins (ghost_of w) (Some (ghost_PCM.ext_ref ora, NoneP) :: nil).*)

Inductive contx :=
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
             jsafeN ge E ora (State f s ctl' ve te)
       | Cont (Kloop1 body incr ctl') =>
             jsafeN ge E ora (State f Sskip (Kloop1 body incr ctl') ve te)
       | Cont (Kloop2 body incr ctl') =>
             jsafeN ge E ora (State f (Sloop body incr) ctl' ve te)
       | Cont (Kcall id' f' ve' te' k') => 
             jsafeN ge E ora (State f (Sreturn None) (Kcall id' f' ve' te' k') ve te)
       | Cont Kstop =>
             jsafeN ge E ora (State f (Sreturn None) Kstop ve te)
       | Cont _ => |={E}=> False
       | Ret None ctl' =>
                jsafeN ge E ora (State f (Sreturn None) ctl' ve te)
       | Ret (Some v) ctl' => ∀ e, (∀ m, mem_auth m -∗ ⌜∃ v', Clight.eval_expr ge ve te m e v' ∧ Cop.sem_cast v' (typeof e) (fn_return f) m = Some v⌝) →
              (* Could we replace these with eval_expr and lose the memory dependence?
                 Right now, the only difference is that e must only access pointers that are valid in the current rmap.
                 But typechecking will also guarantee that. *)
              jsafeN ge E ora (State f (Sreturn (Some e)) ctl' ve te)
       end).

Definition list2opt {T: Type} (vl: list T) : option T :=
 match vl with nil => None | x::_ => Some x end.

Definition match_venv (ve: venviron) (vars: list (ident * type)) :=
 forall id, match ve id with Some (b,t) => In (id,t) vars | _ => True end.

Definition guard_environ (Delta: tycontext) (f: function) (rho: environ) : Prop :=
   typecheck_environ Delta rho /\
    match_venv (ve_of rho) (fn_vars f)
   /\ ret_type Delta = fn_return f.

Lemma guard_environ_e1:
   forall Delta f rho, guard_environ Delta f rho ->
     typecheck_environ Delta rho.
Proof. intros. destruct H; auto. Qed.

Definition _guard
    (gx: genv) E (Delta: tycontext) (f: function) (P : assert) (ctl: contx) : mpred :=
     ∀ tx : Clight.temp_env, ∀ vx : env,
          let rho := construct_rho (filter_genv gx) vx tx in
          ■ (⌜guard_environ Delta f rho⌝
                  ∧ P rho ∗ funassert Delta rho
             -∗ assert_safe gx E f vx tx ctl rho).

Definition guard'
    (gx: genv) E (Delta: tycontext) f P  (ctl: cont) :=
  _guard gx E Delta f P (Cont ctl).

Fixpoint break_cont (k: cont) :=
match k with
| Kseq _ k' => break_cont k'
| Kloop1 _ _ k' => Cont k'
| Kloop2 _ _ k' => Cont k'
| Kswitch k' => Cont k'
| _ => Stuck
end.

Fixpoint continue_cont (k: cont) :=
match k with
| Kseq _ k' => continue_cont k'
| Kloop1 s1 s2 k' => Cont (Kseq s2 (Kloop2 s1 s2 k'))
| Kswitch k' => continue_cont k'
| _ => Stuck
end.

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
    _guard gx E Delta f (proj_ret_assert R ek vl)  (exit_cont ek vl ctl).

Record semaxArg :Type := SemaxArg {
 sa_cs: compspecs;
 sa_E: coPset;
 sa_Delta: tycontext;
 sa_P: @assert Σ;
 sa_c: statement;
 sa_R: @ret_assert Σ
}.

Definition make_ext_rval  (gx: genviron) (tret: rettype) (v: option val):=
  match tret with AST.Tvoid => mkEnviron gx (Map.empty _) (Map.empty _) 
 | _ => 
  match v with
  | Some v' =>  mkEnviron gx (Map.empty _)
                              (Map.set 1%positive v' (Map.empty _))
  | None => mkEnviron gx (Map.empty _) (Map.empty _)
  end end.

Definition semax_external E
  ef
  (A: TypeTree)
  (P: dtfr (ArgsTT A))
  (Q: dtfr (AssertTT A)) :=
 ∀ gx: genv,
 ∀ x: dtfr A,
   ▷ ∀ F (ts: list typ),
   ∀ args: list val,
   ■ (⌜Val.has_type_list args (sig_args (ef_sig ef))⌝ ∧
     (P x (filter_genv gx, args) ∗ F) ={E}=∗
   ∀ m z, state_interp m z -∗ ∃ x': ext_spec_type OK_spec ef,
    ⌜ext_spec_pre OK_spec ef x' (genv_symb_injective gx) ts args z m⌝ ∧
     (*□*) ∀ tret: rettype, ∀ ret: option val, ∀ m': mem, ∀ z': OK_ty,
      ⌜ext_spec_post OK_spec ef x' (genv_symb_injective gx) tret ret z' m'⌝ → |={E}=>
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

Lemma semax_external_funspec_sub E
  {argtypes rtype cc ef A1 P1 Q1 A P Q}
  (Hsub: funspec_sub E (mk_funspec (argtypes, rtype) cc A1 P1 Q1)
                       (mk_funspec (argtypes, rtype) cc A P Q))
  (HSIG: ef_sig ef =
         mksignature
                     (map typ_of_type argtypes)
                     (rettype_of_type rtype) cc):
  semax_external E ef A1 P1 Q1 ⊢ semax_external E ef A P Q.
Proof.
  apply bi.forall_mono; intros g.
  iIntros "#H" (x). iIntros "!>" (F ts args) "!> (%HT & P & F)".
  destruct Hsub as [[??] Hsub]; subst.
  iMod (Hsub with "[$P]") as (x1 F1) "((F1 & P1) & %HQ)".
  { iPureIntro; split; auto.
    rewrite HSIG in HT; apply has_type_list_Forall2 in HT.
    eapply Forall2_implication; [ | apply HT]; auto. }
  iMod ("H" $! _ (F ∗ F1) with "[$P1 $F $F1]") as "H1"; first done.
  iIntros "!>" (??) "s".
  iDestruct ("H1" with "s") as (x') "[? H']".
  iExists x'; iFrame; iIntros (????) "Hpost".
  iMod ("H'" with "Hpost") as "($ & Q1 & $ & F1)".
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
Definition believe_external (gx: genv) E (v: val) (fsig: typesig) cc
  (A: TypeTree)
  (P: dtfr (ArgsTT A))
  (Q: dtfr (AssertTT A)) :=
  match Genv.find_funct gx v with
  | Some (External ef sigargs sigret cc') =>
        ⌜fsig = (typelist2list sigargs, sigret) /\ cc'=cc
           /\ ef_sig ef = mksignature
                           (typlist_of_typelist (typelist_of_type_list (fst fsig)))
                           (rettype_of_type (snd fsig)) cc
           /\ (ef_inline ef = false \/ withtype_empty A)⌝
        ∧ semax_external E ef A P Q
        ∧ ■ (∀ x: dtfr A,
              ∀ ret:option val,
                Q x (make_ext_rval (filter_genv gx) (rettype_of_type (snd fsig)) ret)
                  ∧ ⌜Builtins0.val_opt_has_rettype ret (rettype_of_type (snd fsig))⌝
                  -∗ ⌜tc_option_val sigret ret⌝)
  | _ => False
  end.

Lemma believe_external_funspec_sub {gx E v sig cc A P Q A' P' Q'}
      (Hsub: funspec_sub E (mk_funspec sig cc A P Q) (mk_funspec sig cc A' P' Q'))
      (WTE: withtype_empty A -> withtype_empty A'):
      believe_external gx E v sig cc A P Q ⊢ believe_external gx E v sig cc A' P' Q'.
Proof.
  unfold believe_external.
  destruct (Genv.find_funct gx v); trivial.
  destruct f; trivial. destruct sig as [argtypes rtype].
  iIntros "((% & % & %He & %) & H & #Htc)".
  rewrite TTL2 in He |- *.
  rewrite semax_external_funspec_sub; [iFrame | eauto..].
  iSplit.
  - iPureIntro; repeat split; auto; tauto.
  - iIntros "!>" (??) "[Q %]".
    destruct Hsub as [_ Hsub].
    iApply "Htc"; iSplit; last done.
    simpl in *; inv H.
Abort.

Definition fn_funsig (f: function) : funsig := (fn_params f, fn_return f).

Definition var_sizes_ok (cenv: composite_env) (vars: list (ident*type)) :=
   Forall (fun var : ident * type => @sizeof cenv (snd var) <= Ptrofs.max_unsigned)%Z vars.

Definition var_block' (sh: Share.t) (cenv: composite_env) (idt: ident * type): assert :=
  ⌜(sizeof (snd idt) <= Ptrofs.max_unsigned)%Z⌝ ∧
  assert_of (fun rho => (memory_block sh (sizeof (snd idt))) (eval_lvar (fst idt) (snd idt) rho)).

Definition stackframe_of' (cenv: composite_env) (f: Clight.function) : assert :=
  fold_right bi_sep emp
     (map (fun idt => var_block' Share.top cenv idt) (Clight.fn_vars f)).

Definition believe_internal_ CS
  (semax:semaxArg -> mpred)
  (gx: genv) E (Delta: tycontext) v (fsig: typesig) cc (A: TypeTree)
  (P: dtfr (ArgsTT A))
  (Q: dtfr (AssertTT A)) : mpred :=
  let ce := (@cenv_cs CS) in
  (∃ b: Values.block, ∃ f: function,
   let specparams := fst fsig in 
   let fparams := fn_params f in
   ⌜v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ Forall (fun it => complete_type ce (snd it) = true) (fn_vars f)
                 /\ list_norepet (map fst fparams ++ map fst f.(fn_temps))
                 /\ list_norepet (map fst f.(fn_vars)) /\ var_sizes_ok ce (f.(fn_vars))
                 /\ specparams = map snd fparams
                 /\ snd fsig = snd (fn_funsig f)
                 /\ f.(fn_callconv) = cc⌝
  ∧
   ∀ Delta':tycontext, ∀ CS':compspecs,
   ⌜forall f, tycontext_sub E (func_tycontext' f Delta) (func_tycontext' f Delta')⌝ →
     ⌜cenv_sub (@cenv_cs CS) (@cenv_cs CS')⌝ →
      (∀ x : dtfr A,
        ▷ semax (SemaxArg CS' E (func_tycontext' f Delta')
                         ((bind_args (f.(fn_params)) (argsassert_of (P x)) ∗ stackframe_of' (@cenv_cs CS') f)
                                        (*∗ funassert (func_tycontext' f Delta')*))
                          (f.(fn_body))
           (frame_ret_assert (function_body_ret_assert (fn_return f) (assert_of (Q x)))
              (stackframe_of' (@cenv_cs CS') f))))).

Definition empty_environ (ge: genv) := mkEnviron (filter_genv ge) (Map.empty _) (Map.empty _).

Definition claims (ge: genv) (Delta: tycontext) v fsig cc A P Q : Prop :=
  exists id, (glob_specs Delta) !! id = Some (mk_funspec fsig cc A P Q) /\
    exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Ptrofs.zero.

Definition believepred CS (semax: semaxArg -> mpred)
              E (Delta: tycontext) (gx: genv)  (Delta': tycontext) :=
  ∀ v:val, ∀ fsig: typesig, ∀ cc: calling_convention,
  ∀ A: TypeTree,
  ∀ P: dtfr (ArgsTT A),
  ∀ Q: dtfr (AssertTT A),
       ⌜claims gx Delta' v fsig cc A P Q⌝ →
      (believe_external gx E v fsig cc A P Q
        ∨ believe_internal_ CS semax gx E Delta v fsig cc A P Q).

Definition semax_
       (semax: semaxArg -d> iPropO Σ) : semaxArg -d> iPropO Σ := fun a =>
 match a with SemaxArg CS E Delta P c R =>
  ∀ gx: genv, ∀ Delta': tycontext,∀ CS':compspecs,
       ⌜tycontext_sub E Delta Delta' 
            /\ cenv_sub (@cenv_cs CS) (@cenv_cs CS') 
            /\ cenv_sub (@cenv_cs CS') (genv_cenv gx)⌝ →
      (believepred CS' semax E Delta' gx Delta') →
     ∀ k: cont, ∀ F: assert, ∀ f:function,
       (⌜closed_wrt_modvars c F⌝ ∧
              rguard gx E Delta' f (frame_ret_assert R F) k) →
        guard' gx E Delta' f (F ∗ P) (Kseq c k)
  end.

Local Instance semax_contractive : Contractive semax_.
Proof.
  rewrite /semax_ => n semax semax' Hsemax [??????].
  do 8 f_equiv.
  rewrite /believepred.
  do 14 f_equiv.
  rewrite /believe_internal_.
  do 13 f_equiv.
  by f_contractive.
Qed.

Definition semax' {CS: compspecs} E Delta P c R : mpred :=
  (fixpoint semax_) (SemaxArg CS E Delta P c R).

Definition believe_internal {CS: compspecs}
  (gx: genv) E (Delta: tycontext) v (fsig: typesig) cc (A: TypeTree)
  (P: dtfr (ArgsTT A))
  (Q: dtfr (AssertTT A)) :=
  let ce := @cenv_cs CS in
  (∃ b: Values.block, ∃ f: function,
   let specparams := fst fsig in 
   let fparams := fn_params f in
   ⌜v = Vptr b Ptrofs.zero /\ Genv.find_funct_ptr gx b = Some (Internal f)
                 /\ Forall (fun it => complete_type ce (snd it) = true) (fn_vars f)
                 /\ list_norepet (map fst fparams ++ map fst f.(fn_temps))
                 /\ list_norepet (map fst f.(fn_vars)) /\ var_sizes_ok ce (f.(fn_vars))
                 /\ specparams = map snd fparams
                 /\ snd fsig = snd (fn_funsig f)
                 /\ f.(fn_callconv) = cc⌝
  ∧ 
    ∀ Delta':tycontext,∀ CS':compspecs,
     ⌜forall f, tycontext_sub E (func_tycontext' f Delta) (func_tycontext' f Delta')⌝ →
      ⌜cenv_sub (@cenv_cs CS) (@cenv_cs CS')⌝ →
       (∀ x : dtfr A,
     ▷ @semax' CS' E (func_tycontext' f Delta')
                                ((bind_args (f.(fn_params)) (argsassert_of (P x)) ∗ stackframe_of' (@cenv_cs CS') f)
                                             (*∗ funassert (func_tycontext' f Delta')*))
                               (f.(fn_body))
           (frame_ret_assert (function_body_ret_assert (fn_return f) (assert_of (Q x))) (stackframe_of' (@cenv_cs CS') f)))).

Definition believe {CS: compspecs}
              E (Delta: tycontext) (gx: genv) (Delta': tycontext) :=
  ∀ v:val, ∀ fsig: typesig, ∀ cc: calling_convention,
  ∀ A: TypeTree,
  ∀ P: dtfr (ArgsTT A),
  ∀ Q: dtfr (AssertTT A),
       ⌜claims gx Delta' v fsig cc A P Q⌝ →
      (believe_external gx E v fsig cc A P Q
        ∨ believe_internal gx E Delta v fsig cc A P Q).

Lemma semax_fold_unfold : forall {CS: compspecs} E Delta P c R,
  semax' E Delta P c R ⊣⊢
  ∀ gx: genv, ∀ Delta': tycontext,∀ CS':compspecs,
       ⌜(tycontext_sub E Delta Delta'
           /\ cenv_sub (@cenv_cs CS) (@cenv_cs CS')
           /\ cenv_sub (@cenv_cs CS') (genv_cenv gx))⌝ →
       @believe CS' E Delta' gx Delta' →
     ∀ k: cont, ∀ F: assert, ∀ f: function,
        (⌜(closed_wrt_modvars c F)⌝ ∧ rguard gx E Delta' f (frame_ret_assert R F) k) →
        guard' gx E Delta' f (F ∗ P) (Kseq c k).
Proof.
intros.
unfold semax'.
by rewrite (fixpoint_unfold semax_ _).
Qed.

Lemma semax'_cenv_sub {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) E Delta P c R:
      @semax' CS E Delta P c R ⊢ @semax' CS' E Delta P c R.
Proof.
  rewrite !semax_fold_unfold.
  iIntros "H" (??? (? & ? & ?)); iApply "H"; iPureIntro.
  split; auto; split; auto; apply (cenv_sub_trans CSUB); auto.
Qed.
Lemma semax'_cssub {CS CS'} (CSUB: cspecs_sub  CS CS') E Delta P c R:
      @semax' CS E Delta P c R ⊢ @semax' CS' E Delta P c R.
Proof.
  destruct CSUB as [CSUB _].
  apply (@semax'_cenv_sub _ _ CSUB).
Qed.

Definition semax {CS: compspecs} E (Delta: tycontext) P c Q : Prop :=
  ⊢ @semax' CS E Delta P c Q.

Section believe_monotonicity.
Context {CS: compspecs}.

Lemma _guard_mono gx E Delta Gamma f (P Q:assert) ctl
  (GD1: forall e te, typecheck_environ Gamma (construct_rho (filter_genv gx) e te) ->
                     typecheck_environ Delta (construct_rho (filter_genv gx) e te))
  (GD2: ret_type Delta = ret_type Gamma)
  (GD3: forall e te, Q (construct_rho (filter_genv gx) e te) ⊢
                        P (construct_rho (filter_genv gx) e te))
  (GD4: forall e te, (funassert Gamma (construct_rho (filter_genv gx) e te)) ⊢
                     (funassert Delta (construct_rho (filter_genv gx) e te))):
  @_guard gx E Delta f P ctl ⊢
  @_guard gx E Gamma f Q ctl.
Proof.
  rewrite /_guard.
  iIntros "#H" (??) "!> (% & Q & ?)"; iApply "H".
  iSplit.
  - iPureIntro; unfold guard_environ in *.
    destruct H as (? & ? & ?); rewrite GD2; auto.
  - rewrite GD3 GD4; iFrame.
Qed.

Lemma guard_mono gx E Delta Gamma f (P Q:assert) ctl
  (GD1: forall e te, typecheck_environ Gamma (construct_rho (filter_genv gx) e te) ->
                     typecheck_environ Delta (construct_rho (filter_genv gx) e te))
  (GD2: ret_type Delta = ret_type Gamma)
  (GD3: forall e te, Q (construct_rho (filter_genv gx) e te) ⊢
                        P (construct_rho (filter_genv gx) e te))
  (GD4: forall e te, (funassert Gamma (construct_rho (filter_genv gx) e te)) ⊢
                     (funassert Delta (construct_rho (filter_genv gx) e te))):
  @guard' gx E Delta f P ctl ⊢
  @guard' gx E Gamma f Q ctl.
Proof.
  by apply _guard_mono.
Qed.

Lemma claims_antimono gx Gamma v sig cc A P Q Gamma' 
  (SUB: forall id spec, (glob_specs Gamma') !! id = Some spec ->
                        (glob_specs Gamma) !! id = Some spec)
  (CL: claims gx Gamma' v sig cc A P Q):
  claims gx Gamma v sig cc A P Q.
Proof. destruct CL as [id [Hid X]]; exists id; split; auto. Qed.

Lemma believe_antimonoR gx E Delta Gamma Gamma'
  (DG1: forall id spec, (glob_specs Gamma') !! id = Some spec ->
                        (glob_specs Gamma) !! id = Some spec):
  @believe CS E Delta gx Gamma ⊢ @believe CS E Delta gx Gamma'.
Proof. rewrite /believe. iIntros "H" (???????); iApply "H". iPureIntro; eapply claims_antimono; eauto. Qed.

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

Lemma believe_internal_cenv_sub {CS'} gx E Delta Delta' v sig cc A P Q
  (SUB: forall f, tycontext_sub E (func_tycontext' f Delta)
                                (func_tycontext' f Delta'))
  (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) :
  @believe_internal CS gx E Delta v sig cc A P Q ⊢
  @believe_internal CS' gx E Delta' v sig cc A P Q.
Proof.
  rewrite /believe_internal.
  iIntros "H"; iDestruct "H" as (b f Hv) "H".
  iExists b, f; iSplit.
  - iPureIntro; intuition.
    + eapply Forall_impl. apply H0. simpl; intros.
      apply (complete_type_cenv_sub CSUB); auto.
    + rewrite /var_sizes_ok !Forall_forall in H0 H4 |- *; intros.
      rewrite (cenv_sub_sizeof CSUB); eauto.
  - iIntros (?????); iApply ("H" with "[%] [%]").
    + simpl; intros. eapply tycontext_sub_trans; eauto.
    + apply (cenv_sub_trans CSUB); auto.
Qed.
Lemma believe_internal_mono {CS'} gx E Delta Delta' v sig cc A P Q
  (SUB: forall f, tycontext_sub E (func_tycontext' f Delta)
                                  (func_tycontext' f Delta'))
  (CSUB: cspecs_sub  CS CS') :
  @believe_internal CS gx E Delta v sig cc A P Q ⊢
  @believe_internal CS' gx E Delta' v sig cc A P Q.
Proof.
  destruct CSUB as [CSUB _].
  eapply (@believe_internal_cenv_sub CS'). apply SUB. apply CSUB.
Qed. 

Lemma believe_cenv_sub_L {CS'} gx E Delta Delta' Gamma
  (SUB: forall f, tycontext_sub E (func_tycontext' f Delta)
                                  (func_tycontext' f Delta'))
  (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')):
  @believe CS E Delta gx Gamma ⊢ @believe CS' E Delta' gx Gamma.
Proof.
  rewrite /believe.
  iIntros "H" (???????); iDestruct ("H" with "[%]") as "[?|?]"; eauto.
  iRight; iApply (believe_internal_cenv_sub with "[$]").
Qed.
Lemma believe_monoL {CS'} gx E Delta Delta' Gamma
  (SUB: forall f, tycontext_sub E (func_tycontext' f Delta)
                                  (func_tycontext' f Delta'))
  (CSUB: cspecs_sub  CS CS'):
  @believe CS E Delta gx Gamma ⊢ @believe CS' E Delta' gx Gamma.
Proof.
  destruct CSUB as [CSUB _].
  eapply (@believe_cenv_sub_L CS'). apply SUB. apply CSUB.
Qed.

Lemma believe_internal__mono sem gx E Delta Delta' v sig cc A P Q
  (SUB: forall f, tycontext_sub E (func_tycontext' f Delta)
                                  (func_tycontext' f Delta')) :
  believe_internal_ CS sem gx E Delta v sig cc A P Q ⊢
  believe_internal_ CS sem gx E Delta' v sig cc A P Q.
Proof.
  rewrite /believe_internal_.
  iIntros "H"; iDestruct "H" as (b f Hv) "H".
  iExists b, f; iSplit; first trivial.
  iIntros (?????); iApply ("H" with "[%] [%]"); last done.
  simpl; intros. eapply tycontext_sub_trans; eauto.
Qed.

End believe_monotonicity.

Lemma semax__mono {CS} E Delta Delta'
  (SUB: tycontext_sub E Delta Delta') sem P c R:
  @semax_ sem {| sa_cs := CS; sa_E := E; sa_Delta := Delta; sa_P := P; sa_c := c; sa_R := R |} ⊢
  @semax_ sem {| sa_cs:=CS; sa_E := E; sa_Delta := Delta'; sa_P := P; sa_c := c; sa_R := R |}.
Proof.
  unfold semax_.
  iIntros "H" (??? (? & ? & ?)).
  iApply "H"; iPureIntro; split; auto.
  eapply tycontext_sub_trans; eauto.
Qed.

Lemma semax_mono {CS} E Delta Delta' P Q
  (SUB: tycontext_sub E Delta Delta') c:
  @semax' CS E Delta P c Q ⊢
  @semax' CS E Delta' P c Q.
Proof.
  rewrite !semax_fold_unfold.
  iIntros "H" (??? (? & ? & ?)).
  iApply "H"; iPureIntro; split; auto.
  eapply tycontext_sub_trans; eauto.
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

End mpred.
