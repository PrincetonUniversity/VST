From compcert Require Export Clightdefs.
Require Export VST.veric.base.
Require Export VST.veric.SeparationLogic.
Require Export VST.msl.Extensionality.
Require Export compcert.lib.Coqlib.
Require Export VST.msl.Coqlib2 VST.veric.coqlib4 VST.floyd.coqlib3.
Require Export VST.floyd.jmeq_lemmas.
Require Export VST.floyd.find_nth_tactic.
Require Export VST.veric.juicy_extspec.
Require Import VST.veric.NullExtension.
Require Import VST.floyd.assert_lemmas.
Require Import VST.floyd.SeparationLogicFacts.
Import LiftNotation.
Local Open Scope logic.

Fixpoint all_suf_of_labeled_statements (P: labeled_statements -> Prop) (L: labeled_statements): Prop :=
  match L with
  | LSnil => P L
  | LScons _ s L' => P L /\ all_suf_of_labeled_statements P L'
  end.

Lemma all_suf_self: forall P L,
  all_suf_of_labeled_statements P L -> P L.
Proof.
  intros.
  destruct L; simpl in *; tauto.
Qed.

Lemma all_suf_LSnil: forall P L,
  all_suf_of_labeled_statements P L -> P LSnil.
Proof.
  intros.
  induction L; simpl in *; tauto.
Qed.

Lemma all_suf_select_switch: forall P L,
  all_suf_of_labeled_statements P L ->
  forall n, P (select_switch n L).
Proof.
  intros.
  unfold select_switch.
  destruct (select_switch_case) eqn:?H.
  + revert l H0; induction L; intros.
    - inv H0.
    - simpl in H0.
      destruct o; [if_tac in H0 |].
      * subst z; inv H0.
        destruct H as [? _]; auto.
      * apply IHL; auto.
        destruct H as [_ ?]; auto.
      * apply IHL; auto.
        destruct H as [_ ?]; auto.
  + clear H0.
    induction L.
    - apply all_suf_LSnil in H.
      auto.
    - simpl.
      destruct o.
      * destruct H as [_ ?].
        apply IHL; auto.
      * destruct H as [? _].
        auto.
Qed.

Section statement_ind.

Variables
  (P: statement -> Prop)
  (Hskip: P Sskip)
  (Hassign: forall e e0, P (Sassign e e0))
  (Hset : forall (i : ident) (e : expr), P (Sset i e))
  (Hcall : forall (o : option ident) (e : expr) (l : list expr), P (Scall o e l))
  (Hbuiltin : forall o e t l, P (Sbuiltin o e t l))
  (Hsequence : forall s : statement, P s -> forall s0 : statement, P s0 -> P (Ssequence s s0))
  (Hifthenelse : forall e s, P s -> forall s0, P s0 -> P (Sifthenelse e s s0))
  (Hloop : forall s : statement, P s -> forall s0 : statement, P s0 -> P (Sloop s s0))
  (Hbreak : P Sbreak)
  (Hcontinue : P Scontinue)
  (Hreturn : forall o : option expr, P (Sreturn o))
  (Hswitch : forall e L, all_suf_of_labeled_statements (fun L => P (seq_of_labeled_statement L)) L -> P (Sswitch e L))
  (Hlabel : forall (l : label) (s : statement), P s -> P (Slabel l s))
  (Hgoto : forall l : label, P (Sgoto l)).

Fixpoint statement_ind (s: statement): P s :=
  match s as s0 return (P s0) with
  | Sskip => Hskip
  | Sassign e e0 => Hassign e e0
  | Sset i e => Hset i e
  | Scall o e l => Hcall o e l
  | Sbuiltin o e t l => Hbuiltin o e t l
  | Ssequence s0 s1 => Hsequence s0 (statement_ind s0) s1 (statement_ind s1)
  | Sifthenelse e s0 s1 => Hifthenelse e s0 (statement_ind s0) s1 (statement_ind s1)
  | Sloop s0 s1 => Hloop s0 (statement_ind s0) s1 (statement_ind s1)
  | Sbreak => Hbreak
  | Scontinue => Hcontinue
  | Sreturn o => Hreturn o
  | Sswitch e l => Hswitch e l (labeled_statements_ind l)
  | Slabel l s0 => Hlabel l s0 (statement_ind s0)
  | Sgoto l => Hgoto l
  end
with labeled_statements_ind (L: labeled_statements): all_suf_of_labeled_statements (fun L => P (seq_of_labeled_statement L)) L :=
  match L with
  | LSnil => Hskip
  | LScons _ s L' => conj (Hsequence _ (statement_ind s) _ (all_suf_self _ _ (labeled_statements_ind L'))) (labeled_statements_ind L')
  end.

End statement_ind.

Ltac induction_stmt s :=
  revert dependent s;
  let s1 := fresh s "1" in
  let s2 := fresh s "2" in
  let IHs := fresh "IH" s in
  let IHs1 := fresh "IH" s1 in
  let IHs2 := fresh "IH" s2 in
  refine (statement_ind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
  [
  | intros ?e ?e
  | intros ?i ?e
  | intros ?o ?e ?l
  | intros ?o ?e ?t ?l
  | intros s1 IHs1 s2 IHs2
  | intros ?e s1 IHs1 s2 IHs2
  | intros s1 IHs1 s2 IHs2
  |
  |
  | intros ?o
  | intros ?e ?l ?IH; specialize (all_suf_select_switch _ _ IH); clear IH; intro IH; cbv beta in IH
  | intros ?l s IHs
  | intros ?l ].

Module AuxDefs.

Section AuxDefs.

Variable semax_external: forall {Hspec: OracleKind} (ids: list ident) (ef: external_function)
  (A: rmaps.TypeTree)
  (P Q: forall ts, functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (AssertTT A)) mpred),
    Prop.

Inductive semax {CS: compspecs} {Espec: OracleKind} (Delta: tycontext): (environ -> mpred) -> statement -> ret_assert -> Prop :=
| semax_ifthenelse :
   forall P (b: expr) c d R,
     @semax CS Espec Delta (P && local (`(typed_true (typeof b)) (eval_expr b))) c R ->
     @semax CS Espec Delta (P && local (`(typed_false (typeof b)) (eval_expr b))) d R ->
     @semax CS Espec Delta (!! (bool_type (typeof b) = true) && tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P) (Sifthenelse b c d) R
| semax_seq:
  forall R P Q h t,
    @semax CS Espec Delta P h (overridePost Q R) ->
    @semax CS Espec Delta Q t R ->
    @semax CS Espec Delta P (Ssequence h t) R
| semax_break: forall Q,
    @semax CS Espec Delta (RA_break Q) Sbreak Q
| semax_continue: forall Q,
    @semax CS Espec Delta (RA_continue Q) Scontinue Q
| semax_loop: forall Q Q' incr body R,
     @semax CS Espec Delta  Q body (loop1_ret_assert Q' R) ->
     @semax CS Espec Delta Q' incr (loop2_ret_assert Q R) ->
     @semax CS Espec Delta Q (Sloop body incr) R
| semax_switch: forall (Q: environ->mpred) a sl R,
     (forall rho, Q rho |-- tc_expr Delta a rho) ->
     (forall n,
     @semax CS Espec Delta 
               (local (`eq (eval_expr a) `(Vint n)) &&  Q)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) ->
     @semax CS Espec Delta (!! (is_int_type (typeof a) = true) && Q) (Sswitch a sl) R
(*| semax_call_backward: forall ret a bl R,
     @semax CS Espec Delta
         (EX argsig: _, EX retsig: _, EX cc: _,
          EX A: _, EX P: _, EX Q: _, EX NEP: _, EX NEQ: _, EX ts: _, EX x: _,
         !! (Cop.classify_fun (typeof a) =
             Cop.fun_case_f (type_of_params argsig) retsig cc /\
             (retsig = Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig) &&
          (|>((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>((`(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) * oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* R)))
         (Scall ret a bl)
         (normal_ret_assert R)*)
| semax_call_backward: forall ret a bl R,
     @semax CS Espec Delta
         (EX argsig: _, EX retsig: _, EX cc: _,
          EX A: _, EX P: _, EX Q: _, EX NEP: _, EX NEQ: _, EX ts: _, EX x: _,
         !! (Cop.classify_fun (typeof a) =
             Cop.fun_case_f (type_of_params argsig) retsig cc /\
             (retsig = Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig) &&
          (((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>((`(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) * oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* R)))
         (Scall ret a bl)
         (normal_ret_assert R)
| semax_return: forall (R: ret_assert) ret ,
      @semax CS Espec Delta
                ( (tc_expropt Delta ret (ret_type Delta)) &&
                `(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ))
                (Sreturn ret)
                R
| semax_set_ptr_compare_load_cast_load_backward: forall (P: environ->mpred) id e,
    @semax CS Espec Delta
       ((|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P)) ||
        (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
         EX ty: type, EX sh1: share, EX sh2: share,
          !! (e = Ebinop cmp e1 e2 ty /\
              sepalg.nonidentity sh1 /\ sepalg.nonidentity sh2 /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true) &&
            ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) P))) ||
        (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e) &&
              local (`(tc_val (typeof e) v2)) &&
              (`(mapsto sh (typeof e)) (eval_lvalue e) (`v2) * TT) &&
              subst id (`v2) P)) ||
        (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P)))
        (Sset id e) (normal_ret_assert P)
| semax_store_backward: forall e1 e2 P,
   @semax CS Espec Delta
          (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P))))
          (Sassign e1 e2)
          (normal_ret_assert P)
| semax_skip: forall P, @semax CS Espec Delta P Sskip (normal_ret_assert P)
| semax_builtin: forall P opt ext tl el, @semax CS Espec Delta FF (Sbuiltin opt ext tl el) P
| semax_label: forall (P:environ -> mpred) (c:statement) (Q:ret_assert) l,
    @semax CS Espec Delta P c Q -> @semax CS Espec Delta P (Slabel l c) Q
| semax_goto: forall P l, @semax CS Espec Delta FF (Sgoto l) P
| semax_conseq: forall P' (R': ret_assert) P c (R: ret_assert) ,
    local (tc_environ Delta) && ((allp_fun_id Delta) && P) |-- |==> |> FF || P' ->
    local (tc_environ Delta) && ((allp_fun_id Delta) && RA_normal R') |-- |==> |> FF || RA_normal R ->
    local (tc_environ Delta) && ((allp_fun_id Delta) && RA_break R') |-- |==> |> FF || RA_break R ->
    local (tc_environ Delta) && ((allp_fun_id Delta) && RA_continue R') |-- |==> |> FF || RA_continue R ->
    (forall vl, local (tc_environ Delta) && ((allp_fun_id Delta) && RA_return R' vl) |-- |==> |> FF || RA_return R vl) ->
    @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.

Definition semax_body
       (V: varspecs) (G: funspecs) {C: compspecs} (f: function) (spec: ident * funspec): Prop :=
  match spec with (_, mk_funspec _ cc A P Q NEP NEQ) =>
    forall Espec ts x, (*exists Ann,*)
      @semax C Espec (func_tycontext f V G nil (*Ann*))
          (P ts x *  stackframe_of f)
          (Ssequence f.(fn_body) (Sreturn None))
          (frame_ret_assert (function_body_ret_assert (fn_return f) (Q ts x)) (stackframe_of f))
 end.

Inductive semax_func: forall {Espec: OracleKind} (V: varspecs) (G: funspecs) {C: compspecs} (ge: Genv.t Clight.fundef type)(fdecs: list (ident * Clight.fundef)) (G1: funspecs), Prop :=
| semax_func_nil:   forall {Espec: OracleKind},
    forall V G C ge, @semax_func Espec V G C ge nil nil
| semax_func_cons:
  forall {Espec: OracleKind},
     forall fs id f cc A P Q NEP NEQ (V: varspecs) (G G': funspecs) {C: compspecs} ge b,
      andb (id_in_list id (map (@fst _ _) G))
      (andb (negb (id_in_list id (map (@fst ident Clight.fundef) fs)))
        (semax_body_params_ok f)) = true ->
      Forall
         (fun it : ident * type =>
          complete_type cenv_cs (snd it) =
          true) (fn_vars f) ->
       var_sizes_ok (f.(fn_vars)) ->
       f.(fn_callconv) = cc ->
 (*NEW*)  Genv.find_symbol ge id = Some b -> Genv.find_funct_ptr ge b = Some (Internal f) -> 
       precondition_closed f P ->
      semax_body V G f (id, mk_funspec (fn_funsig f) cc A P Q NEP NEQ)->
      semax_func V G ge fs G' ->
      semax_func V G ge ((id, Internal f)::fs)
                 ((id, mk_funspec (fn_funsig f) cc A P Q NEP NEQ)  :: G')
| semax_func_cons_ext:
  forall {Espec: OracleKind},
   forall (V: varspecs) (G: funspecs) {C: compspecs} ge fs id ef argsig retsig A P Q NEP NEQ
          argsig'
          (G': funspecs) cc (ids: list ident) b,
      ids = map fst argsig' -> (* redundant but useful for the client,
               to calculate ids by reflexivity *)
      argsig' = zip_with_tl ids argsig ->
      ef_sig ef =
      mksignature
        (typlist_of_typelist (type_of_params argsig'))
        (opttyp_of_type retsig) cc ->
      id_in_list id (map (@fst _ _) fs) = false ->
      length ids = length (typelist2list argsig) ->
      (forall gx ts x (ret : option val),
         (Q ts x (make_ext_rval gx ret)
            && !!step_lemmas.has_opttyp ret (opttyp_of_type retsig)
            |-- !!tc_option_val retsig ret)) ->
(*new*) Genv.find_symbol ge id = Some b -> Genv.find_funct_ptr ge b = Some (External ef argsig retsig cc) ->
      @semax_external Espec ids ef A P Q ->
      semax_func V G ge fs G' ->
      semax_func V G ge ((id, External ef argsig retsig cc)::fs)
           ((id, mk_funspec (argsig', retsig) cc A P Q NEP NEQ)  :: G')
| semax_func_mono: forall  {Espec CS CS'} (CSUB: cspecs_sub CS CS') ge ge'
  (Gfs: forall i,  sub_option (Genv.find_symbol ge i) (Genv.find_symbol ge' i))
  (Gffp: forall b, sub_option (Genv.find_funct_ptr ge b) (Genv.find_funct_ptr ge' b))
  V G fdecs G1 (H: @semax_func Espec V G CS ge fdecs G1), @semax_func Espec V G CS' ge' fdecs G1
                                                                      
| semax_func_app:
  forall Espec ge cs V H funs1 funs2 G1 G2
         (SF1: @semax_func Espec V H cs ge funs1 G1) (SF2: @semax_func Espec V H cs ge funs2 G2)
         (L:length funs1 = length G1),
    @semax_func Espec V H cs ge (funs1 ++ funs2) (G1++G2)
                
| semax_func_subsumption:
  forall Espec ge cs V V' F F'
         (SUB: tycontext_sub (nofunc_tycontext V F) (nofunc_tycontext V F'))
         (HV: forall id, sub_option (make_tycontext_g V F) ! id (make_tycontext_g V' F') ! id),
  forall funs G (SF: @semax_func Espec V F cs ge funs G),  @semax_func Espec V' F' cs ge funs G
                                                                       
| semax_func_join:
  forall {Espec cs ge V1 H1 V2 H2 V funs1 funs2 G1 G2 H}
  (SF1: @semax_func Espec V1 H1 cs ge funs1 G1) (SF2: @semax_func Espec V2 H2 cs ge funs2 G2)

  (K1: forall i, sub_option ((make_tycontext_g V1 H1) ! i) ((make_tycontext_g V1 H) ! i))
  (K2: forall i, subsumespec ((make_tycontext_s H1) ! i) ((make_tycontext_s H) ! i))
  (K3: forall i, sub_option ((make_tycontext_g V1 H) ! i) ((make_tycontext_g V H) ! i))

  (N1: forall i, sub_option ((make_tycontext_g V2 H2) ! i) ((make_tycontext_g V2 H) ! i))
  (N2: forall i, subsumespec ((make_tycontext_s H2) ! i) ((make_tycontext_s H) ! i))
  (N3: forall i, sub_option ((make_tycontext_g V2 H) ! i) ((make_tycontext_g V H) ! i)),
  @semax_func Espec V H cs ge (funs1 ++ funs2) (G1++G2)
  
| semax_func_firstn:
  forall {Espec cs ge H V n funs G} (SF: @semax_func Espec V H cs ge funs G),
    @semax_func Espec V H cs ge (firstn n funs) (firstn n G)
                
| semax_func_skipn:
  forall {Espec cs ge H V funs G} (HV:list_norepet (map fst funs))
         (SF: @semax_func Espec V H cs ge funs G) n,
    @semax_func Espec V H cs ge (skipn n funs) (skipn n G).

End AuxDefs.

End AuxDefs.

Module DeepEmbedded
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (MinimumLogic: MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC with Module CSHL_Def := Def).

Module DeepEmbeddedDef <: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Definition semax := @AuxDefs.semax.

Definition semax_func := @AuxDefs.semax_func (@Def.semax_external).

Definition semax_external := @Def.semax_external.

End DeepEmbeddedDef.

Module DeepEmbeddedDefs := DerivedDefs (DeepEmbeddedDef).

Import DeepEmbeddedDef DeepEmbeddedDefs.

Module CConseq: CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE with Module CSHL_Def := DeepEmbeddedDef.

Module CSHL_Def := DeepEmbeddedDef.

Definition semax_conseq := @AuxDefs.semax_conseq.

End CConseq.

Module CConseqFacts := GenCConseqFacts (DeepEmbeddedDef) (CConseq).

Module Conseq := GenConseq (DeepEmbeddedDef) (CConseq).

Module ConseqFacts := GenConseqFacts (DeepEmbeddedDef) (Conseq).

Import CConseq CConseqFacts Conseq ConseqFacts.

Lemma semax_skip_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R,
    @semax CS Espec Delta P Sskip R ->
    local (tc_environ Delta) && (allp_fun_id Delta && P) |-- |==> |> FF || RA_normal R.
Proof.
  intros.
  remember Sskip as c eqn:?H.
  induction H; try solve [inv H0].
  + apply derives_full_refl.
  + specialize (IHsemax H0).
    solve_derives_trans.
Qed.

Lemma semax_break_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R,
    @semax CS Espec Delta P Sbreak R ->
    local (tc_environ Delta) && (allp_fun_id Delta && P) |-- |==> |> FF || RA_break R.
Proof.
  intros.
  remember Sbreak as c eqn:?H.
  induction H; try solve [inv H0].
  + apply derives_full_refl.
  + specialize (IHsemax H0).
    solve_derives_trans.
Qed.

Lemma semax_continue_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R,
    @semax CS Espec Delta P Scontinue R ->
    local (tc_environ Delta) && (allp_fun_id Delta && P) |-- |==> |> FF || RA_continue R.
Proof.
  intros.
  remember Scontinue as c eqn:?H.
  induction H; try solve [inv H0].
  + apply derives_full_refl.
  + specialize (IHsemax H0).
    solve_derives_trans.
Qed.

Lemma semax_return_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P ret R,
  @semax CS Espec Delta P (Sreturn ret) R ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- |==> |> FF || ((tc_expropt Delta ret (ret_type Delta)) && `(|==> |> FF || RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ)).
Proof.
  intros.
  remember (Sreturn ret) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    reduce2ENTAIL.
    apply andp_ENTAIL; [apply ENTAIL_refl |].
    reduce2derives.
    unfold_lift.
    intro rho.
    simpl.
    eapply derives_trans; [| apply bupd_intro].
    apply orp_right2; auto.
  + derives_rewrite -> H; clear H.
    derives_rewrite -> (IHsemax H0); clear IHsemax.
    apply derives_bupd_derives_bupd0.
    reduceR.
    apply andp_ENTAILL; [solve_andp |].
    unfold_lift.
    intro rho.
    simpl.
    forget (cast_expropt ret (ret_type Delta) rho) as vl.
    revert rho.
    change (local (tc_environ Delta) && (allp_fun_id Delta && (|==> |> FF || RA_return R' vl)) |-- |==> |> FF || RA_return R vl).
    apply derives_full_bupd0_left, H4.
Qed.

Lemma semax_seq_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R h t,
    @semax CS Espec Delta P (Ssequence h t) R ->
    exists Q, @semax CS Espec Delta P h (overridePost Q R) /\
              @semax CS Espec Delta Q t R.
Proof.
  intros.
  remember (Ssequence h t) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    exists Q; auto.
  + subst c.
    pose proof IHsemax eq_refl. clear IHsemax.
    destruct H0 as [Q [? ?]].
    exists Q.
    split.
    - apply (AuxDefs.semax_conseq _ P' (overridePost Q R')); auto.
      * clear.
        destruct R, R'.
        apply derives_full_refl.
      * destruct R, R'; auto.
      * destruct R, R'; auto.
      * destruct R, R'; auto.
    - eapply semax_conseq; eauto.
      apply derives_full_refl.
Qed.

Lemma semax_seq_inv': forall {CS: compspecs} {Espec: OracleKind} Delta P R h t,
    @semax CS Espec Delta P (Ssequence h t) R ->
    @semax CS Espec Delta P h (overridePost (EX Q: environ -> mpred, !! (@semax CS Espec Delta Q t R) && Q) R).
Proof.
  intros.
  remember (Ssequence h t) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    clear IHsemax1 IHsemax2.
    eapply semax_post_simple; [.. | exact H].
    - destruct R; unfold overridePost, tycontext.RA_normal.
      apply (exp_right Q).
      apply andp_right; [apply prop_right |]; auto.
    - destruct R; apply derives_refl.
    - destruct R; apply derives_refl.
    - intro; destruct R; apply derives_refl.
  + subst c.
    pose proof IHsemax eq_refl. clear IHsemax.
    eapply AuxDefs.semax_conseq; [.. | exact H0]; auto.
    - unfold overridePost, tycontext.RA_normal.
      destruct R' as [R'0 R'1 R'2 R'3] at 1; clear R'0 R'1 R'2 R'3.
      destruct R as [R0 R1 R2 R3] at 1; clear R0 R1 R2 R3.
      reduce2derives.
      apply exp_derives.
      intros Q.
      normalize.
      apply andp_right; [apply prop_right | auto].
      eapply semax_conseq; [.. | apply H6]; auto.
      apply derives_full_refl.
    - destruct R, R'; auto.
    - destruct R, R'; auto.
    - destruct R, R'; auto.
Qed.

Lemma semax_store_inv: forall {CS: compspecs} {Espec: OracleKind} Delta e1 e2 P Q,
  @semax CS Espec Delta P (Sassign e1 e2) Q ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- |==> |> FF || (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* |==> |> FF || RA_normal Q)))).
Proof.
  intros.
  remember (Sassign e1 e2) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    reduce2derives.
    apply exp_derives; intro sh.
    apply andp_derives; auto.
    apply later_derives; auto.
    apply andp_derives; auto.
    apply sepcon_derives; auto.
    apply wand_derives; auto.
    eapply derives_trans; [| apply bupd_intro].
    apply orp_right2, derives_refl.
  + subst c.
    derives_rewrite -> H.
    derives_rewrite -> (IHsemax eq_refl).
    reduceR.
    apply exp_ENTAILL; intro sh.
    apply andp_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    apply later_ENTAILL.
    apply andp_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    apply sepcon_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    apply wand_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    apply derives_full_bupd0_left, H1.
Qed.

Lemma tc_fn_return_temp_guard_opt: forall ret retsig Delta,
  tc_fn_return Delta ret retsig ->
  temp_guard_opt Delta ret.
Proof.
  intros.
  destruct ret; hnf in H |- *; [destruct ((temp_types Delta) ! i) |]; auto; congruence.
Qed.

Lemma oboxopt_ENTAILL: forall Delta ret retsig P Q,
  tc_fn_return Delta ret retsig ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- Q ->
  local (tc_environ Delta) && (allp_fun_id Delta && oboxopt Delta ret P) |-- oboxopt Delta ret Q.
Proof.
  intros.
  apply oboxopt_left2'; auto.
  eapply tc_fn_return_temp_guard_opt; eauto.
Qed.

Lemma semax_call_inv: forall {CS: compspecs} {Espec: OracleKind} Delta ret a bl Pre Post,
  @semax CS Espec Delta Pre (Scall ret a bl) Post ->
  local (tc_environ Delta) && (allp_fun_id Delta && Pre) |-- |==> |> FF ||
         (EX argsig: _, EX retsig: _, EX cc: _,
          EX A: _, EX P: _, EX Q: _, EX NEP: _, EX NEQ: _, EX ts: _, EX x: _,
         !! (Cop.classify_fun (typeof a) =
             Cop.fun_case_f (type_of_params argsig) retsig cc /\
             (retsig = Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig) &&
          ((*|>*)((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>((`(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) * oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* |==> |> FF || RA_normal Post))).
Proof.
  intros.
  remember (Scall ret a bl) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    reduce2derives.
    apply exp_derives; intro argsig.
    apply exp_derives; intro retsig.
    apply exp_derives; intro cc.
    apply exp_derives; intro A.
    apply exp_derives; intro P.
    apply exp_derives; intro Q.
    apply exp_derives; intro NEP.
    apply exp_derives; intro NEQ.
    apply exp_derives; intro ts.
    apply exp_derives; intro x.
    apply andp_derives; auto.
    apply later_derives; auto.
    apply sepcon_derives; auto.
    apply oboxopt_K; auto.
    apply wand_derives; auto.
    eapply derives_trans; [| apply bupd_intro].
    apply orp_right2, derives_refl.
  + subst c.
    rename P into Pre, R into Post.
    derives_rewrite -> H.
    derives_rewrite -> (IHsemax eq_refl); clear IHsemax.
    reduceR.
    apply exp_ENTAILL; intro argsig.
    apply exp_ENTAILL; intro retsig.
    apply exp_ENTAILL; intro cc.
    apply exp_ENTAILL; intro A.
    apply exp_ENTAILL; intro P.
    apply exp_ENTAILL; intro Q.
    apply exp_ENTAILL; intro NEP.
    apply exp_ENTAILL; intro NEQ.
    apply exp_ENTAILL; intro ts.
    apply exp_ENTAILL; intro x.
    normalize.
    destruct H0 as [? [? ?]].
    apply andp_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    apply later_ENTAILL.
    apply sepcon_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    eapply oboxopt_ENTAILL; eauto.
    apply wand_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    apply derives_full_bupd0_left, H1.
Qed.

Lemma semax_Sset_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R id e,
  @semax CS Espec Delta P (Sset id e) R ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- |==> |> FF ||
    ( (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) (|==> |> FF || RA_normal R))) ||
      (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
         EX ty: type, EX sh1: share, EX sh2: share,
          !! (e = Ebinop cmp e1 e2 ty /\
              sepalg.nonidentity sh1 /\ sepalg.nonidentity sh2 /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true) &&
            ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) (|==> |> FF || RA_normal R)))) ||
      (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e) &&
              local (`(tc_val (typeof e) v2)) &&
              (`(mapsto sh (typeof e)) (eval_lvalue e) (`v2) * TT) &&
              subst id (`v2) (|==> |> FF || RA_normal R))) ||
      (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) (|==> |> FF || RA_normal R)))).
Proof.
  intros.
  remember (Sset id e) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    reduce2derives.
    apply orp_derives; [apply orp_derives; [apply orp_derives |] |].
    - apply later_derives.
      apply andp_derives; auto.
      apply subst_derives.
      eapply derives_trans; [| apply bupd_intro].
      apply orp_right2, derives_refl.
    - apply exp_derives; intros cmp.
      apply exp_derives; intros e1.
      apply exp_derives; intros e2.
      apply exp_derives; intros ty.
      apply exp_derives; intros sh1.
      apply exp_derives; intros sh2.
      apply andp_derives; auto.
      apply later_derives; auto.
      apply andp_derives; auto.
      apply subst_derives.
      eapply derives_trans; [| apply bupd_intro].
      apply orp_right2, derives_refl.
    - apply exp_derives; intros sh.
      apply exp_derives; intros t2.
      apply exp_derives; intros v2.
      apply andp_derives; auto.
      apply later_derives.
      apply andp_derives; auto.
      apply subst_derives.
      eapply derives_trans; [| apply bupd_intro].
      apply orp_right2, derives_refl.
    - apply exp_derives; intros sh.
      apply exp_derives; intros e1.
      apply exp_derives; intros t1.
      apply exp_derives; intros v2.
      apply andp_derives; auto.
      apply later_derives.
      apply andp_derives; auto.
      apply subst_derives.
      eapply derives_trans; [| apply bupd_intro].
      apply orp_right2, derives_refl.
  + subst c.
    rename P into Pre, R into Post.
    derives_rewrite -> H.
    derives_rewrite -> (IHsemax eq_refl); clear IHsemax.
    reduceR.
    apply orp_ENTAILL; [apply orp_ENTAILL; [apply orp_ENTAILL |] |].
    - apply later_ENTAILL.
      unfold tc_temp_id, typecheck_temp_id.
      destruct ((temp_types Delta) ! id) eqn:?H; [| normalize].
      eapply andp_subst_ENTAILL; [eauto | | reduceLL; apply ENTAIL_refl |].
      * destruct (is_neutral_cast (implicit_deref (typeof e)) t) eqn:?H; [| normalize].
        intro rho; unfold_lift; unfold local, lift1; simpl.
        normalize.
        apply andp_left2, andp_left1.
        eapply derives_trans; [apply typecheck_expr_sound; auto |].
        normalize.
        intros _.
        eapply expr2.neutral_cast_subsumption'; eauto.
      * apply derives_full_bupd0_left.
        auto.
    - apply exp_ENTAILL; intro cmp.
      apply exp_ENTAILL; intro e1.
      apply exp_ENTAILL; intro e2.
      apply exp_ENTAILL; intro ty.
      apply exp_ENTAILL; intro sh1.
      apply exp_ENTAILL; intro sh2.
      normalize.
      destruct H0 as [He [? [? [? [? [? ?]]]]]].
      apply later_ENTAILL.
      unfold typecheck_tid_ptr_compare in H10.
      destruct ((temp_types Delta) ! id) eqn:?H; [| inv H10].
      eapply andp_subst_ENTAILL; [eauto | | reduceLL; apply ENTAIL_refl |].
      * unfold_lift; unfold local, lift1; intro rho.
        rewrite <- He; simpl.
        normalize.
        apply andp_left2, andp_left1, andp_left1.
        eapply derives_trans; [apply andp_derives; [| apply derives_refl]; apply andp_derives; apply typecheck_expr_sound; auto |].
        normalize.
        subst e.
        simpl.
        unfold_lift.
        replace (sem_binary_operation' cmp) with (sem_cmp (expr.op_to_cmp cmp)); [| destruct cmp; inv H7; auto].
        apply binop_lemmas2.tc_val'_sem_cmp; auto.
      * apply derives_full_bupd0_left.
        auto.
    - apply exp_ENTAILL; intro sh.
      apply exp_ENTAILL; intro t2.
      apply exp_ENTAILL; intro v2.
      normalize.
      destruct H0 as [? [? ?]].
      apply later_ENTAILL.
      unfold typeof_temp in H0.
      destruct ((temp_types Delta) ! id) eqn:?H; inv H0.
      eapply andp_subst_ENTAILL; [eauto | | reduceLL; apply ENTAIL_refl |].
      * reduceL.
        apply andp_left1.
        apply andp_left2.
        unfold_lift; unfold local, lift1; intro rho; simpl; normalize.
        intros _; eapply expr2.neutral_cast_subsumption; eauto.
      * apply derives_full_bupd0_left.
        auto.
    - apply exp_ENTAILL; intro sh.
      apply exp_ENTAILL; intro e1.
      apply exp_ENTAILL; intro t1.
      apply exp_ENTAILL; intro t2.
      normalize.
      destruct H0 as [He [? [? ?]]].
      apply later_ENTAILL.
      unfold typeof_temp in H0.
      destruct ((temp_types Delta) ! id) eqn:?H; inv H0.
      eapply andp_subst_ENTAILL; [eauto | | reduceLL; apply ENTAIL_refl |].
      * reduceL.
        apply andp_left1.
        apply andp_left2.
        unfold_lift; unfold local, lift1; intro rho; simpl; normalize.
        intros _; auto.
      * apply derives_full_bupd0_left.
        auto.
Qed.

Lemma semax_Sbuiltin_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R opt ext tl el,
  @semax CS Espec Delta P (Sbuiltin opt ext tl el) R -> local (tc_environ Delta) && (allp_fun_id Delta && P) |-- |==> |> FF || FF.
Proof.
  intros.
  remember (Sbuiltin opt ext tl el) as c eqn:?H.
  induction H; try solve [inv H0].
  + reduceL; apply FF_left.
  + derives_rewrite -> H.
    derives_rewrite -> (IHsemax H0).
    reduceL; apply FF_left.
Qed.

Lemma semax_Slabel_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R l c,
  @semax CS Espec Delta P (Slabel l c) R -> @semax CS Espec Delta P c R.
Proof.
  intros.
  remember (Slabel l c) as c0 eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    apply H.
  + specialize (IHsemax H0).
    eapply semax_conseq; eauto.
Qed.

Lemma semax_Sgoto_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R l,
  @semax CS Espec Delta P (Sgoto l) R -> local (tc_environ Delta) && (allp_fun_id Delta && P) |-- |==> |> FF || FF.
Proof.
  intros.
  remember (Sgoto l) as c eqn:?H.
  induction H; try solve [inv H0].
  + reduceL; apply FF_left.
  + derives_rewrite -> H.
    derives_rewrite -> (IHsemax H0).
    reduceL; apply FF_left.
Qed.

Lemma semax_ifthenelse_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R b c1 c2,
  @semax CS Espec Delta P (Sifthenelse b c1 c2) R ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |--
  |==> |> FF || (!! (bool_type (typeof b) = true) && tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) &&
  EX P': environ -> mpred,
  !! (@semax CS Espec Delta (P' && local (`(typed_true (typeof b)) (eval_expr b))) c1 R /\
      @semax CS Espec Delta (P' && local (`(typed_false (typeof b)) (eval_expr b))) c2 R) &&
  P').
Proof.
  intros.
  remember (Sifthenelse b c1 c2) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0; clear IHsemax1 IHsemax2.
    reduce2derives.
    apply andp_derives; auto.
    apply (exp_right P).
    apply andp_right; [apply prop_right; auto |].
    auto.
  + derives_rewrite -> H.
    derives_rewrite -> (IHsemax H0); clear IHsemax.
    reduce2derives.
    apply andp_derives; auto.
    apply exp_derives; intros P''.
    normalize.
    apply andp_right; auto.
    apply prop_right.
    destruct H6; split.
    - eapply semax_conseq; eauto. apply derives_full_refl.
    - eapply semax_conseq; eauto. apply derives_full_refl.
Qed.

Lemma semax_loop_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R body incr,
  @semax CS Espec Delta P (Sloop body incr) R ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |--
  |==> |> FF || EX Q: environ -> mpred, EX Q': environ -> mpred,
  !! (@semax CS Espec Delta Q body (loop1_ret_assert Q' R) /\
      @semax CS Espec Delta Q' incr (loop2_ret_assert Q R)) &&
  Q.
Proof.
  intros.
  remember (Sloop body incr) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0; clear IHsemax1 IHsemax2.
    reduce2derives.
    apply (exp_right Q).
    apply (exp_right Q').
    apply andp_right; [apply prop_right; auto |].
    auto.
  + derives_rewrite -> H.
    derives_rewrite -> (IHsemax H0); clear IHsemax.
    reduce2derives.
    apply exp_derives; intros Q.
    apply exp_derives; intros Q'.
    normalize.
    apply andp_right; [apply prop_right |]; auto.
    destruct H6.
    split.
    - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR']; simpl in H6, H7 |- *.
      simpl RA_normal in H1; simpl RA_break in H2; simpl RA_continue in H3; simpl RA_return in H4.
      eapply semax_conseq; [.. | eassumption]; unfold loop1_ret_assert.
      * apply derives_full_refl.
      * simpl RA_normal.
        apply derives_full_refl.
      * simpl RA_break.
        auto.
      * simpl RA_continue.
        apply derives_full_refl.
      * simpl RA_return.
        auto.
    - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR']; simpl in H6, H7 |- *.
      simpl RA_normal in H1; simpl RA_break in H2; simpl RA_continue in H3; simpl RA_return in H4.
      eapply semax_conseq; [.. | eassumption]; unfold loop1_ret_assert.
      * apply derives_full_refl.
      * simpl RA_normal.
        apply derives_full_refl.
      * simpl RA_break.
        auto.
      * simpl RA_continue.
        apply derives_full_refl.
      * simpl RA_return.
        auto.
Qed.

Lemma semax_switch_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R a sl,
  @semax CS Espec Delta P (Sswitch a sl) R ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |--
        |==> |> FF || !! (is_int_type (typeof a) = true) && (tc_expr Delta a) &&
        EX P': environ -> mpred,
  !! (forall n,
     @semax CS Espec Delta 
               (local (`eq (eval_expr a) `(Vint n)) && P')
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) && P'.
Proof.
  intros.
  remember (Sswitch a sl) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    reduce2derives.
    rewrite andp_assoc.
    apply andp_derives; auto.
    apply andp_right; auto.
    apply (exp_right Q).
    apply andp_right; [apply prop_right; auto |].
    auto.
  + derives_rewrite -> H.
    derives_rewrite -> (IHsemax H0); clear IHsemax.
    reduce2derives.
    apply andp_derives; auto.
    apply exp_derives; intros P''.
    apply andp_derives; auto.
    apply prop_derives; intro.
    intro n; specialize (H6 n).
    eapply semax_conseq; [.. | exact H6].
    - apply derives_full_refl.
    - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR'].
      reduce2derives; apply FF_left.
    - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR'].
      exact H1.
    - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR'].
      exact H3.
    - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR'].
      exact H4.
Qed.

Module Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := CSHL_Def.

Module CSHL_Def := CSHL_Def.
Import CSHL_Def.

Arguments semax {_} {_} _ _ _ _.

Lemma semax_extract_exists:
  forall {CS: compspecs} {Espec: OracleKind},
  forall (A : Type)  (P : A -> environ->mpred) c (Delta: tycontext) (R: ret_assert),
  (forall x, @semax CS Espec Delta (P x) c R) ->
   @semax CS Espec Delta (EX x:A, P x) c R.
Proof.
  intros.
  revert A P R H; induction_stmt c; intros.
  + pose proof (fun x => semax_skip_inv _ _ _ (H x)).
    eapply semax_conseq.
    - rewrite !exp_andp2; apply exp_left.
      intro x.
      apply H0.
    - apply derives_full_refl.
    - apply derives_full_refl.
    - apply derives_full_refl.
    - intros; apply derives_full_refl.
    - eapply semax_post''; [.. | apply AuxDefs.semax_skip].
      apply ENTAIL_refl.
  + pose proof (fun x => semax_store_inv _ _ _ _ _ (H x)).
    clear H.
    apply exp_left in H0.
    rewrite <- !(exp_andp2 A) in H0.
    eapply semax_conseq; [exact H0 | intros; apply derives_full_refl .. | clear H0 ].
    eapply semax_conseq; [apply derives_full_refl | .. | apply AuxDefs.semax_store_backward].
    - reduceL. apply derives_refl.
    - reduceL. apply FF_left.
    - reduceL. apply FF_left.
    - intros; reduceL. apply FF_left.
  + pose proof (fun x => semax_Sset_inv _ _ _ _ _ (H x)).
    clear H.
    apply exp_left in H0.
    rewrite <- !(exp_andp2 A) in H0.
    eapply semax_conseq; [exact H0 | intros; apply derives_full_refl .. | clear H0 ].
    eapply semax_conseq; [apply derives_full_refl | .. | apply AuxDefs.semax_set_ptr_compare_load_cast_load_backward].
    - reduceL. apply derives_refl.
    - reduceL. apply FF_left.
    - reduceL. apply FF_left.
    - intros; reduceL. apply FF_left.
  + pose proof (fun x => semax_call_inv _ _ _ _ _ _ (H x)).
    clear H.
    apply exp_left in H0.
    rewrite <- !(exp_andp2 A) in H0.
    eapply semax_conseq; [exact H0 | intros; apply derives_full_refl .. | clear H0 ].
    eapply semax_conseq; [apply derives_full_refl | .. | apply AuxDefs.semax_call_backward].
    - reduceL. apply derives_refl.
    - reduceL. apply FF_left.
    - reduceL. apply FF_left.
    - intros; reduceL. apply FF_left.
  + pose proof (fun x => semax_Sbuiltin_inv _ _ _ _ _ _ _ (H x)).
    eapply semax_conseq; [| intros; apply derives_full_refl .. | apply AuxDefs.semax_builtin].
    rewrite !exp_andp2.
    apply exp_left; intros x; specialize (H0 x).
    auto.
  + apply AuxDefs.semax_seq with (EX Q: environ -> mpred, !! (semax Delta Q c2 R) && Q).
    - apply IHc1.
      intro x.
      apply semax_seq_inv'; auto.
    - apply IHc2.
      intros Q.
      apply semax_pre with (EX H0: semax Delta Q c2 R, Q).
      * apply andp_left2.
        apply derives_extract_prop; intros.
        apply (exp_right H0).
        auto.
      * apply IHc2.
        intro H0.
        auto.
  + eapply semax_conseq; [| intros; apply derives_full_refl .. | apply (AuxDefs.semax_ifthenelse _ (EX P': environ -> mpred, !! (semax Delta (P' && local (`(typed_true (typeof e)) (eval_expr e))) c1 R /\ semax Delta (P' && local (`(typed_false (typeof e)) (eval_expr e))) c2 R) && P'))].
    - pose proof (fun x => semax_ifthenelse_inv _ _ _ _ _ _ (H x)).
      clear H.
      apply exp_left in H0.
      rewrite <- !(exp_andp2 A) in H0.
      exact H0.
    - rewrite exp_andp1.
      apply IHc1.
      intro P'.
      apply semax_pre with (EX H0: semax Delta (P' && local ((` (typed_true (typeof e))) (eval_expr e))) c1 R, P' && local ((` (typed_true (typeof e))) (eval_expr e))).
      * apply andp_left2.
        rewrite !andp_assoc.
        apply derives_extract_prop; intros.
        apply (exp_right (proj1 H0)).
        solve_andp.
      * apply IHc1.
        intro H0.
        auto.
    - rewrite exp_andp1.
      apply IHc2.
      intro P'.
      apply semax_pre with (EX H0: semax Delta (P' && local ((` (typed_false (typeof e))) (eval_expr e))) c2 R, P' && local ((` (typed_false (typeof e))) (eval_expr e))).
      * apply andp_left2.
        rewrite !andp_assoc.
        apply derives_extract_prop; intros.
        apply (exp_right (proj2 H0)).
        solve_andp.
      * apply IHc2.
        intro H0.
        auto.
  + pose proof (fun x => semax_loop_inv _ _ _ _ _ (H x)).
    eapply (AuxDefs.semax_conseq _ 
      (EX Q : environ -> mpred, EX Q' : environ -> mpred,
         EX H: semax Delta Q c1 (loop1_ret_assert Q' R),
           EX H0: semax Delta Q' c2 (loop2_ret_assert Q R), Q));
    [| intros; apply derives_full_refl .. |].
    {
      rewrite !exp_andp2.
      apply exp_left.
      intros x.
      derives_rewrite -> (H0 x).
      reduce2derives.
      apply exp_derives; intros Q.
      apply exp_derives; intros Q'.
      apply derives_extract_prop; intros [? ?].
      apply (exp_right H1).
      apply (exp_right H2).
      auto.
    }
    apply (AuxDefs.semax_loop _ _
      (EX Q : environ -> mpred, EX Q' : environ -> mpred,
         EX H: semax Delta Q c1 (loop1_ret_assert Q' R),
           EX H0: semax Delta Q' c2 (loop2_ret_assert Q R), Q')).
    - apply IHc1.
      intros Q.
      apply IHc1.
      intros Q'.
      apply IHc1.
      intros ?H.
      apply IHc1.
      intros ?H.
      eapply semax_post_simple; [.. | exact H1].
      * destruct R as [nR bR cR rR].
        unfold loop1_ret_assert.
        apply (exp_right Q), (exp_right Q'), (exp_right H1), (exp_right H2).
        apply derives_refl.
      * destruct R as [nR bR cR rR].
        apply derives_refl.
      * destruct R as [nR bR cR rR].
        unfold loop1_ret_assert.
        apply (exp_right Q), (exp_right Q'), (exp_right H1), (exp_right H2).
        apply derives_refl.
      * intros.
        destruct R as [nR bR cR rR].
        apply derives_refl.
    - apply IHc2.
      intros Q.
      apply IHc2.
      intros Q'.
      apply IHc2.
      intros ?H.
      apply IHc2.
      intros ?H.
      eapply semax_post_simple; [.. | exact H2].
      * destruct R as [nR bR cR rR].
        unfold loop1_ret_assert.
        apply (exp_right Q), (exp_right Q'), (exp_right H1), (exp_right H2).
        apply derives_refl.
      * destruct R as [nR bR cR rR].
        apply derives_refl.
      * destruct R as [nR bR cR rR].
        apply derives_refl.
      * intros.
        destruct R as [nR bR cR rR].
        apply derives_refl.
  + pose proof (fun x => semax_break_inv _ _ _ (H x)).
    eapply semax_conseq; [| intros; apply derives_full_refl .. |].
    - rewrite !exp_andp2; apply exp_left.
      intro x; apply H0.
    - apply AuxDefs.semax_break.
  + pose proof (fun x => semax_continue_inv _ _ _ (H x)).
    eapply semax_conseq; [| intros; apply derives_full_refl .. |].
    - rewrite !exp_andp2; apply exp_left.
      intro x; apply H0.
    - apply AuxDefs.semax_continue.
  + pose proof (fun x => semax_return_inv _ _ _ _ (H x)).
    eapply (semax_conseq _ _ {| RA_normal := _; RA_break := _; RA_continue := _; RA_return := |==> |> FF || RA_return R |}); [.. | apply AuxDefs.semax_return].
    - rewrite !exp_andp2.
      apply exp_left; intros x.
      derives_rewrite -> (H0 x).
      apply derives_full_refl.
    - apply derives_full_refl.
    - apply derives_full_refl.
    - apply derives_full_refl.
    - intros; unfold RA_return at 1. apply derives_full_bupd0_left, derives_full_refl.
  + pose proof (fun x => semax_switch_inv _ _ _ _ _ (H x)).
    eapply semax_conseq; [| intros; apply derives_full_refl .. |].
    - rewrite !exp_andp2; apply exp_left.
      intro x; apply H0.
    - rewrite andp_assoc.
      apply AuxDefs.semax_switch; [intros; simpl; solve_andp |].
      intros.
      specialize (IH (Int.unsigned n)).
      rewrite !exp_andp2.
      apply IH.
      intros P'.
      apply semax_pre with (EX H: forall n0 : int,
           semax Delta (local ((` eq) (eval_expr e) (` (Vint n0))) && P')
             (seq_of_labeled_statement (select_switch (Int.unsigned n0) l))
             (switch_ret_assert R), local ((` eq) (eval_expr e) (` (Vint n))) && P').
      * rewrite (andp_comm (prop _)), <- !andp_assoc, <- (andp_comm (prop _)).
        apply derives_extract_prop; intros.
        apply (exp_right H1).
        solve_andp.
      * apply IH.
        intros ?H.
        auto.
  + pose proof (fun x => semax_Slabel_inv _ _ _ _ _ (H x)).
    apply AuxDefs.semax_label.
    apply IHc.
    auto.
  + pose proof (fun x => semax_Sgoto_inv _ _ _ _ (H x)).
    eapply semax_conseq; [| intros; apply derives_full_refl .. | apply AuxDefs.semax_goto].
    rewrite !exp_andp2.
    apply exp_left; intros x; specialize (H0 x).
    auto.
Qed.

End Extr.

Module ExtrFacts := GenExtrFacts (CSHL_Def) (Conseq) (Extr).
Module ExtrIFacts := GenIExtrFacts (CSHL_Def) (CConseq) (Extr).

Import Extr ExtrFacts ExtrIFacts.

Module DeepEmbeddedMinimumSeparationLogic <: MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC with Module CSHL_Def := DeepEmbeddedDef.

Module CSHL_Def := DeepEmbeddedDef.

Module CSHL_Defs := DeepEmbeddedDefs.

Definition semax_extract_exists := @semax_extract_exists.

Definition semax_func_nil := @AuxDefs.semax_func_nil (@Def.semax_external).

Definition semax_func_cons := @AuxDefs.semax_func_cons (@Def.semax_external).

Definition semax_func_cons_ext := @AuxDefs.semax_func_cons_ext (@Def.semax_external).
  
Theorem semax_ifthenelse :
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta P (b: expr) c d R,
      bool_type (typeof b) = true ->
     @semax CS Espec Delta (P && local (`(typed_true (typeof b)) (eval_expr b))) c R ->
     @semax CS Espec Delta (P && local (`(typed_false (typeof b)) (eval_expr b))) d R ->
     @semax CS Espec Delta (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P) (Sifthenelse b c d) R.
Proof.
  intros.
  pose proof @AuxDefs.semax_ifthenelse _ _ _ _ _ _ _ _ H0 H1.
  eapply semax_pre_simple; [| exact H2].
  normalize.
Qed.

Definition semax_seq := @AuxDefs.semax_seq.

Definition semax_break := @AuxDefs.semax_break.

Definition semax_continue := @AuxDefs.semax_continue.

Definition semax_loop := @AuxDefs.semax_loop.

Theorem semax_switch: 
  forall {CS: compspecs} Espec Delta (Q: environ -> mpred) a sl R,
     is_int_type (typeof a) = true ->
     (forall rho, Q rho |-- tc_expr Delta a rho) ->
     (forall n,
     @semax CS Espec Delta (fun rho => andp (prop (eval_expr a rho = Vint n)) (Q rho))
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) ->
     @semax CS Espec Delta Q (Sswitch a sl) R.
Proof.
  intros.
  pose proof AuxDefs.semax_switch _ _ _ _ _ H0 H1.
  eapply semax_pre_simple; [| exact H2].
  normalize.
Qed.

Module CallB: CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD with Module CSHL_Def := DeepEmbeddedDef.

Module CSHL_Def := DeepEmbeddedDef.

Definition semax_call_backward := @AuxDefs.semax_call_backward.

End CallB.

Module CallF := CallB2F (DeepEmbeddedDef) (Conseq) (CallB).

Definition semax_call := @CallF.semax_call_forward.

Definition semax_return := @AuxDefs.semax_return.

Module Sset: CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD with Module CSHL_Def := DeepEmbeddedDef.

Module CSHL_Def := DeepEmbeddedDef.

Definition semax_set_ptr_compare_load_cast_load_backward := @AuxDefs.semax_set_ptr_compare_load_cast_load_backward.

End Sset.

Module SetB := Sset2Set (DeepEmbeddedDef) (Conseq) (Sset).

Module SetF := SetB2F (DeepEmbeddedDef) (Conseq) (SetB).

Definition semax_set_forward := @SetF.semax_set_forward.

Module PtrCmpB := Sset2PtrCmp (DeepEmbeddedDef) (Conseq) (Sset).

Module PtrCmpF := PtrCmpB2F (DeepEmbeddedDef) (Conseq) (PtrCmpB).

Definition semax_ptr_compare := @PtrCmpF.semax_ptr_compare_forward.

Module LoadB := Sset2Load (DeepEmbeddedDef) (Conseq) (Sset).

Module LoadF := LoadB2F (DeepEmbeddedDef) (Conseq) (LoadB).

Definition semax_load := @LoadF.semax_load_forward.

Module CastLoadB := Sset2CastLoad (DeepEmbeddedDef) (Conseq) (Sset).

Module CastLoadF := CastLoadB2F (DeepEmbeddedDef) (Conseq) (CastLoadB).

Definition semax_cast_load := @CastLoadF.semax_cast_load_forward.

Module StoreB: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD with Module CSHL_Def := DeepEmbeddedDef.

Module CSHL_Def := DeepEmbeddedDef.

Definition semax_store_backward := @AuxDefs.semax_store_backward.

End StoreB.

Module StoreF := StoreB2F (DeepEmbeddedDef) (Conseq) (StoreB).

Definition semax_store := @StoreF.semax_store_forward.

Definition semax_skip := @AuxDefs.semax_skip.

Definition semax_conseq := @AuxDefs.semax_conseq.

Definition semax_Slabel := @AuxDefs.semax_label.

Definition semax_ext := @MinimumLogic.semax_ext.

Definition semax_ext_void := @MinimumLogic.semax_ext_void.

Definition semax_external_FF := @MinimumLogic.semax_external_FF.

Definition semax_func_mono := @AuxDefs.semax_func_mono (@Def.semax_external).

Definition semax_func_app := @AuxDefs.semax_func_app (@Def.semax_external).
Definition semax_func_subsumption := @AuxDefs.semax_func_subsumption (@Def.semax_external).
Definition semax_func_join  := @AuxDefs.semax_func_join (@Def.semax_external).
Definition semax_func_firstn := @AuxDefs.semax_func_firstn (@Def.semax_external).
Definition semax_func_skipn := @AuxDefs.semax_func_skipn (@Def.semax_external).

Lemma tc_fn_return_sub:
  forall (CS : compspecs) (Delta Delta' : tycontext),
  tycontext_sub Delta Delta' ->
  forall ret retsig,
  tc_fn_return Delta ret retsig ->
  tc_fn_return Delta' ret retsig.
Proof.
  intros.
  hnf in H0 |- *.
  destruct ret; auto.
  destruct H as [? _].
  specialize (H i).
  destruct ((temp_types Delta) ! i), ((temp_types Delta') ! i); auto.
  + subst; auto.
  + tauto.
Qed.

Lemma obox_sub:
  forall (Delta Delta' : tycontext) id P rho,
    tycontext_sub Delta Delta' ->
    temp_guard Delta id ->
    tc_environ Delta rho ->
    obox Delta id P rho |-- obox Delta' id P rho.
Proof.
  intros.
  unfold obox.
  destruct H as [? _].
  specialize (H id).
  hnf in H0.
  destruct ((temp_types Delta) ! id), ((temp_types Delta') ! id); auto.
  + subst; auto.
  + tauto.
  + tauto.
Qed.

Lemma oboxopt_sub:
  forall (Delta Delta' : tycontext) id P rho,
    tycontext_sub Delta Delta' ->
    temp_guard_opt Delta id ->
    tc_environ Delta rho ->
    oboxopt Delta id P rho |-- oboxopt Delta' id P rho.
Proof.
  intros.
  destruct id.
  + apply obox_sub; auto.
  + simpl.
    auto.
Qed.

Lemma typecheck_tid_ptr_compare_sub: forall Delta Delta' id,
  tycontext_sub Delta Delta' ->
  typecheck_tid_ptr_compare Delta id = true ->
  typecheck_tid_ptr_compare Delta' id = true.
Proof.
  unfold typecheck_tid_ptr_compare.
  intros.
  destruct H as [? _].
  specialize (H id).
  hnf in H0.
  destruct ((temp_types Delta) ! id), ((temp_types Delta') ! id); auto.
  + subst; auto.
  + inv H0.
Qed.

Theorem semax_Delta_subsumption:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta Delta' P c R,
       tycontext_sub Delta Delta' ->
     @semax CS Espec Delta P c R -> @semax CS Espec Delta' P c R.
Proof.
  intros.
  induction H0.
  + apply semax_pre with (!! (bool_type (typeof b) = true) && tc_expr Delta' (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P); [| apply AuxDefs.semax_ifthenelse; auto].
    apply andp_ENTAIL; [| apply ENTAIL_refl].
    apply andp_ENTAIL; [apply ENTAIL_refl |].
    intro rho; simpl.
    unfold local, lift1; normalize.
    apply Clight_assert_lemmas.tc_expr_sub; auto.
    eapply semax_lemmas.typecheck_environ_sub; eauto.
  + eapply AuxDefs.semax_seq; eauto.
  + eapply AuxDefs.semax_break; eauto.
  + eapply AuxDefs.semax_continue; eauto.
  + eapply AuxDefs.semax_loop; eauto.
  + eapply semax_pre with (!! (is_int_type (typeof a) = true) && (Q && local (tc_environ Delta'))); [solve_andp |].
    eapply AuxDefs.semax_switch.
    - intros; simpl.
      rewrite (add_andp _ _ (H0 _)).
      unfold local, lift1; normalize.
      apply andp_left2.
      apply Clight_assert_lemmas.tc_expr_sub; auto.
      eapply semax_lemmas.typecheck_environ_sub; eauto.
    - intros.
      eapply semax_pre; [| apply H2].
      solve_andp.
  + eapply semax_pre; [| apply AuxDefs.semax_call_backward].
    apply exp_ENTAIL; intros argsig.
    apply exp_ENTAIL; intros retsig.
    apply exp_ENTAIL; intros cc.
    apply exp_ENTAIL; intros A.
    apply exp_ENTAIL; intros P.
    apply exp_ENTAIL; intros Q.
    apply exp_ENTAIL; intros NEP.
    apply exp_ENTAIL; intros NEQ.
    apply exp_ENTAIL; intros ts.
    apply exp_ENTAIL; intros x.
    normalize.
    apply andp_ENTAIL; [apply andp_ENTAIL; [apply andp_right; [apply andp_left1 |] |] |].
    - intro rho; unfold local, lift1; normalize.
      simpl; apply prop_right.
      destruct H0; split; [auto |].
      destruct H2; split; [auto |].
      eapply tc_fn_return_sub; eauto.
    - (*apply later_ENTAIL.
      apply andp_ENTAIL.
      * intro rho; simpl; unfold local, lift1; normalize.
        apply Clight_assert_lemmas.tc_expr_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * intro rho; simpl; unfold local, lift1; normalize.
        apply Clight_assert_lemmas.tc_exprlist_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.*)
      apply andp_right. 
      * rewrite <- andp_assoc. apply andp_left1. intro rho; simpl; unfold local, lift1; normalize.
        apply Clight_assert_lemmas.tc_expr_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * rewrite (andp_comm (tc_expr Delta a)). rewrite <- andp_assoc. apply andp_left1.
        intro rho; simpl; unfold local, lift1; normalize.
        apply Clight_assert_lemmas.tc_exprlist_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
        
    - apply ENTAIL_refl.
    - apply later_ENTAIL.
      apply sepcon_ENTAIL; [apply ENTAIL_refl |].
      destruct H0 as [_ [_ ?]].
      intro rho; simpl.
      unfold local, lift1; normalize.
      apply oboxopt_sub; auto.
      * eapply tc_fn_return_temp_guard_opt; eauto.
      * eapply semax_lemmas.typecheck_environ_sub; eauto.
  + eapply semax_pre; [| apply AuxDefs.semax_return].
    assert (ret_type Delta = ret_type Delta') by (unfold tycontext_sub in *; tauto).
    rewrite H0.
    apply andp_ENTAIL; [| apply ENTAIL_refl].
    intro rho; simpl.
    unfold local, lift1; normalize.
    destruct ret.
    - apply Clight_assert_lemmas.tc_expr_sub; auto.
      eapply semax_lemmas.typecheck_environ_sub; eauto.
    - simpl; auto.
  + eapply semax_pre; [| apply AuxDefs.semax_set_ptr_compare_load_cast_load_backward].
    apply orp_ENTAIL; [apply orp_ENTAIL; [apply orp_ENTAIL |] |].
    - apply later_ENTAIL.
      apply andp_ENTAIL; [| apply ENTAIL_refl].
      apply andp_ENTAIL.
      * unfold local, lift1; intro rho; simpl; normalize.
        apply Clight_assert_lemmas.tc_expr_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * unfold local, lift1; intro rho; simpl; normalize.
        apply Clight_assert_lemmas.tc_temp_id_sub; auto.
    - apply exp_ENTAIL; intro cmp.
      apply exp_ENTAIL; intro e1.
      apply exp_ENTAIL; intro e2.
      apply exp_ENTAIL; intro ty.
      apply exp_ENTAIL; intro sh1.
      apply exp_ENTAIL; intro sh2.
      apply andp_ENTAIL; [| apply later_ENTAIL, andp_ENTAIL; [apply andp_ENTAIL; [apply andp_ENTAIL; [apply andp_ENTAIL; [apply andp_ENTAIL |] |] |] |]].
      * 
unfold local, lift1; intro rho; simpl; normalize.
        destruct H1; split; auto.
        destruct H2; split; auto.
        destruct H3; split; auto.
        destruct H4; split; auto.
        destruct H5; split; auto.
        destruct H6; split; auto.
        eapply typecheck_tid_ptr_compare_sub; eauto.
      * unfold local, lift1; intro rho; simpl; normalize.
        apply Clight_assert_lemmas.tc_expr_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * unfold local, lift1; intro rho; simpl; normalize.
        apply Clight_assert_lemmas.tc_expr_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
    - apply exp_ENTAIL; intro sh.
      apply exp_ENTAIL; intro t2.
      apply exp_ENTAIL; intro v2.
      apply andp_ENTAIL; [| apply later_ENTAIL, andp_ENTAIL; [apply andp_ENTAIL; [apply andp_ENTAIL |] |] ].
      * unfold local, lift1; intro rho; simpl; normalize.
        destruct H1; split; auto.
        eapply Clight_assert_lemmas.typeof_temp_sub; eauto.
      * unfold local, lift1; intro rho; simpl; normalize.
        apply Clight_assert_lemmas.tc_lvalue_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
    - apply exp_ENTAIL; intro sh.
      apply exp_ENTAIL; intro e1.
      apply exp_ENTAIL; intro t1.
      apply exp_ENTAIL; intro v2.
      apply andp_ENTAIL; [| apply later_ENTAIL, andp_ENTAIL; [apply andp_ENTAIL; [apply andp_ENTAIL |] |] ].
      * unfold local, lift1; intro rho; simpl; normalize.
        destruct H1; split; auto.
        destruct H2; split; auto.
        eapply Clight_assert_lemmas.typeof_temp_sub; eauto.
      * unfold local, lift1; intro rho; simpl; normalize.
        apply Clight_assert_lemmas.tc_lvalue_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
  + eapply semax_pre; [| apply AuxDefs.semax_store_backward].    
    apply exp_ENTAIL; intro sh.
    apply andp_ENTAIL; [apply ENTAIL_refl |].
    apply later_ENTAIL.
    apply andp_ENTAIL; [| apply ENTAIL_refl].
    apply andp_ENTAIL.
    - unfold local, lift1; intro rho; simpl; normalize.
      apply Clight_assert_lemmas.tc_lvalue_sub; auto.
      eapply semax_lemmas.typecheck_environ_sub; eauto.
    - unfold local, lift1; intro rho; simpl; normalize.
      apply Clight_assert_lemmas.tc_expr_sub; auto.
      eapply semax_lemmas.typecheck_environ_sub; eauto.
  + apply AuxDefs.semax_skip.
  + apply AuxDefs.semax_builtin.
  + apply AuxDefs.semax_label; auto.
  + apply AuxDefs.semax_goto.
  + eapply semax_conseq; [.. | exact IHsemax].
    - eapply derives_trans; [| exact H0].
      apply andp_derives; [| apply andp_derives]; auto.
      * unfold local, lift1; intro rho; simpl; normalize.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * intro; apply Clight_assert_lemmas.allp_fun_id_sub; auto.
    - eapply derives_trans; [| exact H1].
      apply andp_derives; [| apply andp_derives]; auto.
      * unfold local, lift1; intro rho; simpl; normalize.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * intro; apply Clight_assert_lemmas.allp_fun_id_sub; auto.
    - eapply derives_trans; [| exact H2].
      apply andp_derives; [| apply andp_derives]; auto.
      * unfold local, lift1; intro rho; simpl; normalize.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * intro; apply Clight_assert_lemmas.allp_fun_id_sub; auto.
    - eapply derives_trans; [| exact H3].
      apply andp_derives; [| apply andp_derives]; auto.
      * unfold local, lift1; intro rho; simpl; normalize.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * intro; apply Clight_assert_lemmas.allp_fun_id_sub; auto.
    - intros.
      eapply derives_trans; [| apply H4].
      apply andp_derives; [| apply andp_derives]; auto.
      * unfold local, lift1; intro rho; simpl; normalize.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * intro; apply Clight_assert_lemmas.allp_fun_id_sub; auto.
Qed.

Lemma rvalue_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub  CS CS') Delta e rho,
  tc_environ Delta rho ->
  @tc_expr CS Delta e rho |-- !! (@eval_expr CS e rho = @eval_expr CS' e rho).
Proof.
  intros. apply derives_trans with (!! tc_val (typeof e) (@eval_expr CS e rho) && @tc_expr CS Delta e rho).
  { apply andp_right; trivial. apply typecheck_expr_sound; trivial. }
  normalize. rewrite (expr_lemmas.eval_expr_cenv_sub_eq CSUB). normalize.
  intros N; rewrite N in H0; clear N. apply tc_val_Vundef in H0; trivial.
Qed.

Lemma lvalue_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub  CS CS') Delta e rho,
  tc_environ Delta rho ->
  @tc_lvalue CS Delta e rho |-- !! (@eval_lvalue CS e rho = @eval_lvalue CS' e rho).
Proof. 
  intros. apply derives_trans with (!! is_pointer_or_null (@eval_lvalue CS e rho) && @tc_lvalue CS Delta e rho).
  { apply andp_right; trivial. apply typecheck_lvalue_sound; trivial. }
  normalize. rewrite (expr_lemmas.eval_lvalue_cenv_sub_eq CSUB). normalize.
  intros N; rewrite N in H0; clear N. apply H0.
Qed.


Lemma denote_tc_bool_CSCS' {CS CS'} v e: @denote_tc_assert CS (tc_bool v e) = @denote_tc_assert CS' (tc_bool v e).
Proof. destruct v; simpl; trivial. Qed.

Lemma tc_expr_NoVundef {CS} Delta rho e (TE: typecheck_environ Delta rho):
  @tc_expr CS Delta e rho |-- !! (tc_val (typeof e) (@eval_expr CS e rho) /\ (@eval_expr CS e rho)<>Vundef).
Proof.
  eapply derives_trans. apply typecheck_expr_sound; trivial.
  normalize. split; trivial. intros N. rewrite N in H; clear N. apply tc_val_Vundef in H; trivial.
Qed. 

Definition SETpre CS Delta id e P :=
  |> (@tc_expr CS Delta e && @tc_temp_id id (typeof e) CS Delta e && @subst mpred id (@eval_expr CS e) P)
  || (EX cmp : Cop.binary_operation,
      EX e1 : expr,
      EX e2 : expr,
      EX ty : type,
      EX sh1 : share,
      EX sh2 : share,
      !! (e = Ebinop cmp e1 e2 ty /\
          @sepalg.nonidentity share Share.Join_ba pa_share sh1 /\
          @sepalg.nonidentity share Share.Join_ba pa_share sh2 /\
          is_comparison cmp = true /\
          eqb_type (typeof e1) int_or_ptr_type = false /\ eqb_type (typeof e2) int_or_ptr_type = false /\ typecheck_tid_ptr_compare Delta id = true) &&
      |> (@tc_expr CS Delta e1 && @tc_expr CS Delta e2 && local ((` (blocks_match cmp)) (@eval_expr CS e1) (@eval_expr CS e2)) &&
          ((` (mapsto_ sh1 (typeof e1))) (@eval_expr CS e1) * @TT (LiftEnviron mpred) (@LiftNatDed' mpred Nveric)) &&
          ((` (mapsto_ sh2 (typeof e2))) (@eval_expr CS e2) * @TT (LiftEnviron mpred) (@LiftNatDed' mpred Nveric)) &&
          @subst mpred id (@eval_expr CS (Ebinop cmp e1 e2 ty)) P))
  || (EX sh : share,
      EX t2 : type,
      EX v2 : val,
      !! (typeof_temp Delta id = @Some type t2 /\ is_neutral_cast (typeof e) t2 = true /\ readable_share sh) &&
      |> (@tc_lvalue CS Delta e && local (` (tc_val (typeof e) v2)) &&
          ((` (mapsto sh (typeof e))) (@eval_lvalue CS e) (` v2) * @TT (LiftEnviron mpred) (@LiftNatDed' mpred Nveric)) && @subst mpred id (` v2) P))
  || (EX sh : share,
      EX e1 : expr,
      EX t1 : type,
      EX v2 : val,
      !! (e = Ecast e1 t1 /\ typeof_temp Delta id = @Some type t1 /\ cast_pointer_to_bool (typeof e1) t1 = false /\ readable_share sh) &&
      |> (@tc_lvalue CS Delta e1 && local ((` (tc_val t1)) (` (eval_cast (typeof e1) t1 v2))) &&
          ((` (mapsto sh (typeof e1))) (@eval_lvalue CS e1) (` v2) * @TT (LiftEnviron mpred) (@LiftNatDed' mpred Nveric)) &&
          @subst mpred id (` (force_val (sem_cast (typeof e1) t1 v2))) P)).

Definition STOREpre CS Delta e1 e2 P := (EX sh : share,
     !! writable_share sh &&
     |> (@tc_lvalue CS Delta e1 && @tc_expr CS Delta (Ecast e2 (typeof e1)) &&
         ((` (mapsto_ sh (typeof e1))) (@eval_lvalue CS e1) *
          ((` (mapsto sh (typeof e1))) (@eval_lvalue CS e1) ((` force_val) ((` (sem_cast (typeof e2) (typeof e1))) (@eval_expr CS e2))) -* P)))).

Definition CALLpre CS Delta ret a bl R :=
     EX argsig : list (ident * type),
     EX retsig : type,
     EX cc : calling_convention,
     EX A : rmaps.TypeTree,
     EX P : forall ts : list Type, functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (AssertTT A)) mpred,
     EX Q : forall ts : list Type, functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (AssertTT A)) mpred,
     EX NEP : @super_non_expansive A P,
     EX NEQ : @super_non_expansive A Q,
     EX ts : list Type,
     EX x
     : functors.MixVariantFunctor._functor
         ((fix dtfr (T : rmaps.TypeTree) : functors.MixVariantFunctor.functor :=
             match T with
             | rmaps.ConstType A0 => functors.MixVariantFunctorGenerator.fconst A0
             | rmaps.Mpred => functors.MixVariantFunctorGenerator.fidentity
             | rmaps.DependentType n => functors.MixVariantFunctorGenerator.fconst (@nth Type n ts unit)
             | rmaps.ProdType T1 T2 => functors.MixVariantFunctorGenerator.fpair (dtfr T1) (dtfr T2)
             | rmaps.ArrowType T1 T2 => functors.MixVariantFunctorGenerator.ffunc (dtfr T1) (dtfr T2)
             | rmaps.SigType A f => @functors.MixVariantFunctorGenerator.fsig A (fun a => dtfr (f a))
             | rmaps.PiType I0 f => @functors.MixVariantFunctorGenerator.fpi I0 (fun i : I0 => dtfr (f i))
             | rmaps.ListType T0 => functors.MixVariantFunctorGenerator.flist (dtfr T0)
             end) A) mpred,
     !! (Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retsig cc /\
         (retsig = Tvoid -> ret = @None ident) /\ tc_fn_return Delta ret retsig) &&
     (*|>*) (@tc_expr CS Delta a && @tc_exprlist CS Delta (@snd (list ident) (list type) (@split ident type argsig)) bl) &&
     (` (func_ptr (mk_funspec (argsig, retsig) cc A P Q NEP NEQ))) (@eval_expr CS a) &&
     |>  (@sepcon (lifted (LiftEnviron mpred)) (@LiftNatDed' mpred Nveric) (@LiftSepLog' mpred Nveric Sveric)
                   (@liftx (Tarrow environ (LiftEnviron mpred)) (P ts x)
                            (@make_args' (argsig, retsig) (@eval_exprlist CS (@snd (list ident) (list type) (@split ident type argsig)) bl))) 
                   (oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* R))).
    
Lemma semax_cssub {CS CS'} (CSUB: cspecs_sub  CS CS') Espec Delta P c R:
      @semax CS Espec Delta P c R -> @semax CS' Espec Delta P c R.
Proof.
  intros.
  induction H.
  + apply semax_pre with (!! (bool_type (typeof b) = true) && @tc_expr CS' Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && (@tc_expr CS Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P)); [| apply AuxDefs.semax_ifthenelse; auto].
    {
    apply andp_right; [| solve_andp].
    rewrite <- andp_assoc.
    apply andp_left1.
    apply andp_ENTAIL; [apply ENTAIL_refl |].
    intro rho; simpl.
    unfold local, lift1; normalize.
    apply tc_expr_cspecs_sub; auto.
    }
    {
      eapply semax_pre; [| exact IHsemax1].
      apply andp_right; [solve_andp |].
      rewrite <- andp_assoc.
      apply imp_andp_adjoint.
      rewrite <- andp_assoc.
      apply andp_left1.
      apply derives_trans with (local (tc_environ Delta) && (@tc_expr CS Delta b)); [| apply derives_trans with ( local (fun rho => (@eval_expr CS b rho = @eval_expr CS' b rho)))].
      + unfold tc_expr.
        simpl denote_tc_assert.
        rewrite denote_tc_assert_andp.
        solve_andp.
      + intro rho; simpl.
        unfold local, lift1; normalize.
        apply rvalue_cspecs_sub; auto.
      + apply imp_andp_adjoint.
        intro rho; simpl.
        unfold local, lift1; normalize.
        unfold_lift.
        rewrite H1; auto.
    }
    { eapply semax_pre; [| exact IHsemax2].
      apply andp_right; [solve_andp |].
      rewrite <- andp_assoc.
      apply imp_andp_adjoint.
      rewrite <- andp_assoc.
      apply andp_left1.
      apply derives_trans with (local (tc_environ Delta) && (@tc_expr CS Delta b)); [| apply derives_trans with ( local (fun rho => (@eval_expr CS b rho = @eval_expr CS' b rho)))].
      + unfold tc_expr.
        simpl denote_tc_assert.
        rewrite denote_tc_assert_andp.
        solve_andp.
      + intro rho; simpl.
        unfold local, lift1; normalize.
        apply rvalue_cspecs_sub; auto.
      + apply imp_andp_adjoint.
        intro rho; simpl.
        unfold local, lift1; normalize.
        unfold_lift.
        rewrite H1; auto.
    }
  + eapply AuxDefs.semax_seq; eauto.
  + eapply AuxDefs.semax_break; eauto.
  + eapply AuxDefs.semax_continue; eauto.
  + eapply AuxDefs.semax_loop; eauto.
  + eapply semax_pre with (!! (is_int_type (typeof a) = true) && (Q && local (tc_environ Delta))); [solve_andp |].
    eapply AuxDefs.semax_switch.
    - intros. specialize (H rho). simpl. eapply derives_trans. apply andp_derives. apply H. apply derives_refl.
      simpl. unfold local, lift1; normalize. apply tc_expr_cspecs_sub; trivial.
    - intros; simpl. specialize (H1 n); simpl in H1.
      eapply semax_pre with (fun x : environ => local ((` (@eq val)) (@eval_expr CS a) (` (Vint n))) x &&  local ((` (@eq val)) (@eval_expr CS' a) (` (Vint n))) x && (Q x && local (tc_environ Delta) x)).
      * simpl. intros rho.
        apply andp_right; [| solve_andp].
        rewrite <- andp_assoc.
        unfold local, lift1; normalize. eapply derives_trans. apply H.
        eapply derives_trans. apply (rvalue_cspecs_sub CSUB Delta a rho H2). 
        unfold liftx, lift in H3. simpl in H3. unfold liftx, lift. simpl. normalize.
        rewrite <- H3, H4. rewrite <- H3. normalize.
      * eapply semax_pre; [simpl; intros rho | apply H1]. solve_andp. 
  + apply semax_pre with (CALLpre CS Delta ret a bl R && CALLpre CS' Delta ret a bl R).
    - simpl. intros rho.
      apply derives_extract_prop; intros TC.
      apply andp_right. apply derives_refl. unfold CALLpre; simpl.
      apply exp_derives; intros argsig.
      apply exp_derives; intros retsig.
      apply exp_derives; intros cc.
      apply exp_derives; intros A.
      apply exp_derives; intros P.
      apply exp_derives; intros Q.
      apply exp_derives; intros NEP.
      apply exp_derives; intros NEQ.
      apply exp_derives; intros ts.
      apply exp_derives; intros x. rewrite ! andp_assoc.
      apply andp_derives. trivial. (* unfold liftx, lift; simpl.
      assert (ZZ: (func_ptr (mk_funspec (argsig, retsig) cc A P Q NEP NEQ) (@eval_expr CS' a rho) =
                   |> (func_ptr (mk_funspec (argsig, retsig) cc A P Q NEP NEQ) (@eval_expr CS' a rho)))).
      { apply func_ptr_later_iff. }
      rewrite ZZ, func_ptr_later_iff; clear ZZ.
      (*rewrite <- ! later_andp.
      apply later_derives.*)
      apply derives_trans with
      ( ( (!!(@eval_expr CS a rho =  @eval_expr CS' a rho)) &&
          (!!((@eval_exprlist CS (@snd (list ident) (list type) (@split ident type argsig)) bl) rho = 
              (@eval_exprlist CS' (@snd (list ident) (list type) (@split ident type argsig)) bl) rho))) &&
          (@tc_expr CS Delta a rho &&
          @tc_exprlist CS Delta (@snd (list ident) (list type) (@split ident type argsig)) bl rho &&
          (func_ptr (mk_funspec (argsig, retsig) cc A P Q NEP NEQ) (@eval_expr CS a rho) &&
                    (P ts x (make_args' (argsig, retsig) (@eval_exprlist CS (@snd (list ident) (list type) (@split ident type argsig)) bl) rho) *
                     oboxopt Delta ret (fun rho0 : environ => maybe_retval (Q ts x) retsig ret rho0 -* R rho0) rho)))).
      { apply andp_right; trivial.
        apply andp_left1. apply andp_derives. apply rvalue_cspecs_sub; trivial. apply eval_exprlist_cspecs_sub; trivial. }
      normalize. rewrite ! H. unfold make_args'. simpl. rewrite ! H0.
      apply andp_derives; [ apply andp_derives | trivial].
      eapply tc_expr_cspecs_sub; trivial. apply tc_exprlist_cspecs_sub; trivial. 
    - eapply semax_pre; [| apply AuxDefs.semax_call_backward].
      simpl. intros rho.
      apply derives_extract_prop; intros TC.
      apply andp_left2. unfold CALLpre; simpl.
      apply exp_derives; intros argsig.
      apply exp_derives; intros retsig.
      apply exp_derives; intros cc.
      apply exp_derives; intros A.
      apply exp_derives; intros P.
      apply exp_derives; intros Q.
      apply exp_derives; intros NEP.
      apply exp_derives; intros NEQ.
      apply exp_derives; intros ts.
      apply exp_derives; intros x. apply derives_refl. *) Set Printing Implicit.
      apply derives_trans with
      ( ( (!!(@eval_expr CS a rho =  @eval_expr CS' a rho)) &&
          (!!((@eval_exprlist CS (@snd (list ident) (list type) (@split ident type argsig)) bl) rho = 
              (@eval_exprlist CS' (@snd (list ident) (list type) (@split ident type argsig)) bl) rho)))
          && (@tc_expr CS Delta a rho &&
              (@tc_exprlist CS Delta (@snd (list ident) (list type) (@split ident type argsig)) bl rho &&
                ((` (func_ptr (mk_funspec (argsig, retsig) cc A P Q NEP NEQ))) (@eval_expr CS a) rho &&
                  |> ((` (P ts x)) (make_args' (argsig, retsig) (@eval_exprlist CS (@snd (list ident) (list type)
                                                                (@split ident type argsig)) bl)) rho *
               oboxopt Delta ret (fun rho0 : environ => maybe_retval (Q ts x) retsig ret rho0 -* R rho0) rho))))).
      { apply andp_right; [| trivial]. rewrite <- andp_assoc. apply andp_left1. apply andp_derives.
        apply rvalue_cspecs_sub; trivial. apply eval_exprlist_cspecs_sub; trivial. }
      normalize. unfold liftx, lift, make_args'; simpl. rewrite ! H; rewrite ! H0.
      apply andp_derives; [ | apply andp_derives; [|trivial]].
      eapply tc_expr_cspecs_sub; trivial. apply tc_exprlist_cspecs_sub; trivial. 
    - eapply semax_pre; [| apply AuxDefs.semax_call_backward].
      simpl. intros rho.
      apply derives_extract_prop; intros TC.
      apply andp_left2. unfold CALLpre; simpl.
      apply exp_derives; intros argsig.
      apply exp_derives; intros retsig.
      apply exp_derives; intros cc.
      apply exp_derives; intros A.
      apply exp_derives; intros P.
      apply exp_derives; intros Q.
      apply exp_derives; intros NEP.
      apply exp_derives; intros NEQ.
      apply exp_derives; intros ts.
      apply exp_derives; intros x. apply derives_refl.
      
  + apply semax_pre with                        
      (@andp (forall _ : environ, mpred) (@LiftNatDed' mpred Nveric)
             (@andp (forall _ : environ, mpred) (@LiftNatDed' mpred Nveric)
                    (@tc_expropt CS Delta ret (ret_type Delta))
                    (@liftx (Tarrow (option val) (Tarrow environ (LiftEnviron mpred))) (RA_return R) (@cast_expropt CS ret (ret_type Delta)) (@id environ)))
             (@andp (forall _ : environ, mpred) (@LiftNatDed' mpred Nveric)
                    (@tc_expropt CS' Delta ret (ret_type Delta))
                    (@liftx (Tarrow (option val) (Tarrow environ (LiftEnviron mpred))) (RA_return R) (@cast_expropt CS' ret (ret_type Delta)) (@id environ)))).
    - apply andp_right; [ solve_andp |].
      unfold local, lift1; normalize. simpl. intros rho. apply derives_extract_prop; intros TC.
      apply andp_right. apply andp_left1. apply tc_expropt_cenv_sub; trivial.
      unfold liftx, lift; simpl. apply (RA_return_cast_expropt_cspecs_sub CSUB); trivial.
    - eapply semax_pre; [| apply AuxDefs.semax_return]. solve_andp. 
  + apply semax_pre with  (andp (SETpre CS Delta id e P) (SETpre CS' Delta id e P)).
    - simpl. intros rho. apply derives_extract_prop; intros TEDelta.
      apply andp_right. apply derives_refl. unfold SETpre; simpl. apply orp_derives.
      { apply orp_derives.
        + apply orp_derives.
          - apply later_derives. apply andp_right.
            * apply andp_left1. apply andp_derives. apply tc_expr_cspecs_sub; trivial.
              apply tc_temp_id_cspecs_sub; trivial.
            * apply derives_trans with (((@tc_expr CS Delta e) && (@subst mpred id (@eval_expr CS e) P)) rho).
              simpl. solve_andp.
              simpl. apply imp_andp_adjoint.
              eapply derives_trans. apply (rvalue_cspecs_sub CSUB Delta); trivial.
              simpl. normalize. unfold subst. simpl. rewrite H. apply imp_andp_adjoint. apply andp_left2. trivial.
          - apply exp_derives; intros op.
            apply exp_derives; intros e1.
            apply exp_derives; intros e2.
            apply exp_derives; intros t.
            apply exp_derives; intros sh1.
            apply exp_derives; intros sh2. normalize. apply later_derives. rewrite ! andp_assoc.
            apply derives_trans with ((!!( (@eval_expr CS e1 rho) = (@eval_expr CS' e1 rho)) && !!( (@eval_expr CS e2 rho) = (@eval_expr CS' e2 rho))) && (@tc_expr CS Delta e1 rho &&
  (@tc_expr CS Delta e2 rho &&
   (local ((` (blocks_match op)) (@eval_expr CS e1) (@eval_expr CS e2)) rho &&
    ((` (mapsto_ sh1 (typeof e1))) (@eval_expr CS e1) rho * @TT mpred Nveric &&
     ((` (mapsto_ sh2 (typeof e2))) (@eval_expr CS e2) rho * @TT mpred Nveric &&
                                                                 @subst mpred id ((` (force_val2 (@sem_binary_operation' CS op (typeof e1) (typeof e2)))) (@eval_expr CS e1) (@eval_expr CS e2)) P rho)))))).
            * apply andp_right; [apply andp_right | apply derives_refl].
              apply andp_left1. apply (rvalue_cspecs_sub CSUB Delta); trivial.
              apply andp_left2.  apply andp_left1. apply (rvalue_cspecs_sub CSUB Delta); trivial.
            * normalize. unfold liftx, lift, local, lift1, subst; simpl. rewrite ! H0; rewrite ! H1. normalize.
              apply andp_right. apply andp_left1. apply tc_expr_cspecs_sub; trivial.
              apply andp_right. apply andp_left2; apply andp_left1. apply tc_expr_cspecs_sub; trivial.
              apply andp_right. solve_andp.
              apply andp_right. solve_andp.
              apply andp_left2. apply andp_left2. apply andp_left2. apply andp_left2.
              unfold sem_binary_operation'. destruct H as [? [_ [_ [? [? [? ?]]]]]]. 
              destruct op; simpl; try solve [inv H3]; trivial. 
        + apply exp_derives; intros sh.
          apply exp_derives; intros t.
          apply exp_derives; intros v. normalize.
          apply later_derives. rewrite ! andp_assoc.
          apply andp_right. apply andp_left1; apply tc_lvalue_cspecs_sub; trivial.
          apply andp_right. solve_andp. 
          apply andp_right.
          eapply derives_trans.
          { apply andp_right. apply andp_left1.
            apply (lvalue_cspecs_sub CSUB Delta e rho TEDelta). apply derives_refl. }
          normalize. unfold liftx, lift; simpl. rewrite H0. solve_andp. solve_andp. }
      { apply exp_derives; intros sh.
        apply exp_derives; intros e1.
        apply exp_derives; intros t.
        apply exp_derives; intros v. normalize. apply later_derives. rewrite ! andp_assoc.
        apply derives_trans with (!!((@eval_lvalue CS e1 rho) = (@eval_lvalue CS' e1 rho)) && (@tc_lvalue CS Delta e1 rho &&
  (local ((` (tc_val t)) (` (force_val (sem_cast (typeof e1) t v)))) rho &&
         ((` (mapsto sh (typeof e1))) (@eval_lvalue CS e1) (` v) rho * @TT mpred Nveric && @subst mpred id (` (force_val (sem_cast (typeof e1) t v))) P rho)))).
        + apply andp_right; [apply andp_left1 | solve_andp]. apply lvalue_cspecs_sub; trivial.
        + normalize. apply andp_right. apply andp_left1. apply tc_lvalue_cspecs_sub; trivial.
          unfold liftx, lift; simpl. rewrite H0. solve_andp. }
    - eapply semax_pre;  [| apply AuxDefs.semax_set_ptr_compare_load_cast_load_backward].
      apply andp_left2. apply andp_left2. apply derives_refl.
  + apply semax_pre with (andp (STOREpre CS Delta e1 e2 P) (STOREpre CS' Delta e1 e2 P)).
    - intros rho. simpl. apply derives_extract_prop; intros TEDelta.
      apply andp_right. apply derives_refl. unfold STOREpre; simpl.
      apply exp_derives; intros sh. normalize. apply later_derives.
      apply andp_right.
      { apply andp_left1. apply andp_derives. apply tc_lvalue_cspecs_sub; trivial. apply tc_expr_cspecs_sub; trivial. }
      apply derives_trans with (((!!((@eval_lvalue CS e1 rho) = (@eval_lvalue CS' e1 rho))) && (!!((@eval_expr CS e2 rho) = (@eval_expr CS' e2 rho)))) && ((` (mapsto_ sh (typeof e1))) (@eval_lvalue CS e1) rho *
                                                                                                                                                           ((` (mapsto sh (typeof e1))) (@eval_lvalue CS e1) ((` (force_val oo sem_cast (typeof e2) (typeof e1))) (@eval_expr CS e2)) rho -* P rho))).
      * apply andp_derives; [ apply andp_derives| trivial].
        apply lvalue_cspecs_sub; trivial. 
        eapply derives_trans. 2: apply rvalue_cspecs_sub; eassumption.
        unfold tc_expr. simpl. rewrite denote_tc_assert_andp. simpl. solve_andp.
      * normalize. unfold liftx, lift; simpl. rewrite H0, H1; trivial.
    - eapply semax_pre; [| apply AuxDefs.semax_store_backward].   
      apply andp_left2. apply andp_left2. apply derives_refl. 
  + apply AuxDefs.semax_skip.
  + apply AuxDefs.semax_builtin.
  + apply AuxDefs.semax_label; auto.
  + apply AuxDefs.semax_goto.
  + eapply semax_conseq; [.. | exact IHsemax]; auto.
Qed.

Lemma semax_body_subsumption: forall cs V V' F F' f spec
      (SF: @semax_body V F cs f spec)
      (TS: tycontext_sub (func_tycontext f V F nil) (func_tycontext f V' F' nil)),
    @semax_body V' F' cs f spec.
Proof.
  unfold semax_body. 
  destruct spec. destruct f0; hnf; intros. 
  eapply semax_Delta_subsumption. apply TS. apply (SF Espec ts x).
Qed. 

Lemma semax_body_cenv_sub {CS CS'} (CSUB: cspecs_sub CS CS') V G f spec
      (COMPLETE : Forall (fun it : ident * type => complete_type (@cenv_cs CS) (snd it) = true) (fn_vars f)):
    @semax_body V G CS f spec -> @semax_body V G CS' f spec.
Proof.
  destruct spec. simpl. destruct f0; intros.  specialize (H Espec ts x). 
  rewrite <- (semax_prog.stackframe_of_cenv_sub CSUB); [apply (semax_cssub CSUB); apply H | trivial].
Qed. 

End DeepEmbeddedMinimumSeparationLogic.

Module DeepEmbeddedPracticalLogic <: PRACTICAL_CLIGHT_SEPARATION_HOARE_LOGIC.

Module CSHL_Def := DeepEmbeddedDef.

Module CSHL_Defs := DeepEmbeddedDefs.

Module CSHL_MinimumLogic := DeepEmbeddedMinimumSeparationLogic.

Definition semax_set := @DeepEmbeddedMinimumSeparationLogic.SetB.semax_set_backward.

Arguments semax {_} {_} _ _ _ _.

Lemma modifiedvars_aux: forall id, (fun i => isSome (insert_idset id idset0) ! i) = eq id.
Proof.
  intros.
  extensionality i.
  apply prop_ext.
  unfold insert_idset.
  destruct (ident_eq i id).
  + subst.
    rewrite PTree.gss.
    simpl; tauto.
  + rewrite PTree.gso by auto.
    unfold idset0.
    rewrite PTree.gempty.
    simpl.
    split; [tauto | intro].
    congruence.
Qed.

Lemma sepcon_derives_full: forall Delta P1 P2 Q1 Q2,
  local (tc_environ Delta) && (allp_fun_id Delta && P1) |-- |==> |> FF || P2 ->
  local (tc_environ Delta) && (allp_fun_id Delta && Q1) |-- |==> |> FF || Q2 ->
  local (tc_environ Delta) && (allp_fun_id Delta && (P1 * Q1)) |-- |==> |> FF || (P2 * Q2).
Proof.
  intros.
  pose proof sepcon_ENTAILL  _ _ _ _ _ H H0.
  eapply derives_trans; [exact H1 |].
  clear.
  eapply derives_trans; [apply bupd_sepcon |].
  apply bupd_mono.
  rewrite distrib_orp_sepcon, !distrib_orp_sepcon2.
  repeat apply orp_left.
  + apply orp_right1.
    rewrite <- later_sepcon.
    rewrite FF_sepcon; auto.
  + apply orp_right1.
    rewrite sepcon_comm.
    apply wand_sepcon_adjoint.
    eapply derives_trans; [apply now_later |].
    apply wand_sepcon_adjoint.
    rewrite <- later_sepcon.
    rewrite sepcon_FF.
    auto.
  + apply orp_right1.
    apply wand_sepcon_adjoint.
    eapply derives_trans; [apply now_later |].
    apply wand_sepcon_adjoint.
    rewrite <- later_sepcon.
    rewrite sepcon_FF.
    auto.
  + apply orp_right2; auto.
Qed.

Lemma semax_frame:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta P s R F,
   closed_wrt_modvars s F ->
  @semax CS Espec Delta P s R ->
    @semax CS Espec Delta (P * F) s (frame_ret_assert R F).
Proof.
  intros.
  induction H0.
  + apply semax_pre with (!! (bool_type (typeof b) = true) && tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && (P * F)).
    - normalize.
      apply andp_left2, andp_right.
      * eapply derives_trans; [apply sepcon_derives; [apply andp_left1 |]; apply derives_refl |].
        intro rho.
        apply (predicates_sl.extend_sepcon (extend_tc.extend_tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) rho)).
      * eapply derives_trans; [apply sepcon_derives; [apply andp_left2 |]; apply derives_refl |].
        auto.
    - rewrite semax_lemmas.closed_Sifthenelse in H; destruct H.
      apply AuxDefs.semax_ifthenelse.
      * eapply semax_pre; [| apply IHsemax1; auto].
        apply andp_left2.
        unfold_lift.
        intro rho; unfold local, lift1; simpl.
        normalize.
      * eapply semax_pre; [| apply IHsemax2; auto].
        apply andp_left2.
        unfold_lift.
        intro rho; unfold local, lift1; simpl.
        normalize.
  + rewrite semax_lemmas.closed_Ssequence in H; destruct H.
    apply AuxDefs.semax_seq with (Q * F).
    - destruct R; apply IHsemax1; auto.
    - destruct R; apply IHsemax2; auto.
  + replace (RA_break Q * F) with (RA_break (frame_ret_assert Q F)) by (destruct Q; auto).
    apply AuxDefs.semax_break.
  + replace (RA_continue Q * F) with (RA_continue (frame_ret_assert Q F)) by (destruct Q; auto).
    apply AuxDefs.semax_continue.
  + rewrite semax_lemmas.closed_Sloop in H; destruct H.
    eapply AuxDefs.semax_loop with (Q' * F).
    - destruct R; apply IHsemax1; auto.
    - replace (loop2_ret_assert (Q * F) (frame_ret_assert R F))
        with (frame_ret_assert (loop2_ret_assert Q R) F)
        by (destruct R; simpl; f_equal; extensionality rho; apply pred_ext; normalize).
      apply IHsemax2; auto.
  + rewrite corable_andp_sepcon1 by (apply corable_prop).
    eapply AuxDefs.semax_switch; auto.
    - intro.
      eapply derives_trans; [apply sepcon_derives; [apply H0 | apply derives_refl] |].
      apply (predicates_sl.extend_sepcon (extend_tc.extend_tc_expr Delta a rho)).
    - intros.
      rewrite <- corable_andp_sepcon1 by (intro; apply corable_prop).
      replace (switch_ret_assert (frame_ret_assert R F)) with
        (frame_ret_assert (switch_ret_assert R) F)
        by (destruct R; simpl; f_equal; extensionality rho; apply pred_ext; normalize).
      apply (H2 n).
      eapply semax_lemmas.closed_Sswitch; eauto.
  + rewrite frame_normal.
    eapply semax_pre; [.. | apply AuxDefs.semax_call_backward; auto].
    - apply andp_left2.
      rewrite exp_sepcon1. apply exp_derives; intros argsig.
      rewrite exp_sepcon1. apply exp_derives; intros retsig.
      rewrite exp_sepcon1. apply exp_derives; intros cc.
      rewrite exp_sepcon1. apply exp_derives; intros A.
      rewrite exp_sepcon1. apply exp_derives; intros P.
      rewrite exp_sepcon1. apply exp_derives; intros Q.
      rewrite exp_sepcon1. apply exp_derives; intros NEP.
      rewrite exp_sepcon1. apply exp_derives; intros NEQ.
      rewrite exp_sepcon1. apply exp_derives; intros ts.
      rewrite exp_sepcon1. apply exp_derives; intros x.
      normalize.
      apply andp_right; [apply andp_right |].
      * apply wand_sepcon_adjoint.
        apply andp_left1.
        apply andp_left1.
        apply wand_sepcon_adjoint.
        eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply now_later] |].
        (*rewrite <- later_sepcon.
        apply later_derives.*)
        intro rho.
        simpl.
        apply (predicates_sl.extend_sepcon (extend_tc.extend_andp _ _ (extend_tc.extend_tc_expr Delta a rho) (extend_tc.extend_tc_exprlist Delta (snd (split argsig)) bl rho))).
      * apply wand_sepcon_adjoint.
        apply andp_left1, andp_left2.
        apply wand_sepcon_adjoint.
        apply derives_left_sepcon_right_corable; auto.
        intro.
        apply corable_func_ptr.
      * apply wand_sepcon_adjoint.
        apply andp_left2.
        apply wand_sepcon_adjoint.
        eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply now_later] |].
        rewrite <- later_sepcon.
        apply later_derives.
        rewrite sepcon_assoc; apply sepcon_derives; auto.

        destruct H0 as [? [? ?]].
        rewrite <- (oboxopt_closed Delta ret F) at 1 by (try eapply tc_fn_return_temp_guard_opt; eauto).
        eapply derives_trans; [apply oboxopt_sepcon |].
        apply oboxopt_K.
        rewrite <- (sepcon_emp (maybe_retval _ _ _)) at 2.
        eapply derives_trans; [| apply wand_frame_hor].
        apply sepcon_derives; auto.
        apply wand_sepcon_adjoint.
        rewrite sepcon_emp; auto.
  + eapply semax_pre; [| apply AuxDefs.semax_return].
    apply andp_left2.
    apply andp_right.
    - intro rho; simpl.
      eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, derives_refl |].
      apply (predicates_sl.extend_sepcon (extend_tc.extend_tc_expropt Delta ret (ret_type Delta) rho)).
    - intro rho; simpl.
      eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left2, derives_refl |].
      destruct R; simpl.
      apply derives_refl.
  + rewrite frame_normal.
    eapply semax_pre; [| apply AuxDefs.semax_set_ptr_compare_load_cast_load_backward].
    apply andp_left2.
    rewrite !distrib_orp_sepcon.
    repeat apply orp_derives.
    - eapply derives_trans; [apply sepcon_derives; [apply derives_refl |]; apply now_later |].
      rewrite <- later_sepcon.
      apply later_derives.
      apply andp_right.
      * intro rho; simpl.
        eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, derives_refl |].
        apply (predicates_sl.extend_sepcon (extend_tc.extend_andp _ _ (extend_tc.extend_tc_expr Delta e rho) (extend_tc.extend_tc_temp_id id (typeof e) Delta e rho))).
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left2, derives_refl |].
        rewrite subst_sepcon.
        rewrite (closed_wrt_subst _ _ F); auto.
        unfold closed_wrt_modvars in H.
        rewrite <- modifiedvars_aux.
        auto.
    - rewrite exp_sepcon1; apply exp_derives; intros cmp.
      rewrite exp_sepcon1; apply exp_derives; intros e1.
      rewrite exp_sepcon1; apply exp_derives; intros e2.
      rewrite exp_sepcon1; apply exp_derives; intros ty.
      rewrite exp_sepcon1; apply exp_derives; intros sh1.
      rewrite exp_sepcon1; apply exp_derives; intros sh2.
      normalize.
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl |]; apply now_later |].
      rewrite <- later_sepcon.
      apply later_derives.
      apply andp_right; [apply andp_right; [apply andp_right; [apply andp_right |] |] |].
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left1, andp_left1, andp_left1, derives_refl |].
        intro rho; simpl.
        apply (predicates_sl.extend_sepcon (extend_tc.extend_andp _ _ (extend_tc.extend_tc_expr Delta e1 rho) (extend_tc.extend_tc_expr Delta e2 rho))).
      * unfold local, lift1; unfold_lift; intro rho; simpl.
        eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left1, andp_left1, andp_left2, derives_refl |].
        rewrite <- (andp_TT (prop _)) at 1.
        normalize.
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left1, andp_left2, derives_refl |].
        rewrite sepcon_assoc.
        apply sepcon_derives; auto.
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left2, derives_refl |].
        rewrite sepcon_assoc.
        apply sepcon_derives; auto.
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left2, derives_refl |].
        rewrite subst_sepcon.
        rewrite (closed_wrt_subst _ _ F); auto.
        unfold closed_wrt_modvars in H.
        rewrite <- modifiedvars_aux.
        auto.
    - rewrite exp_sepcon1; apply exp_derives; intros sh.
      rewrite exp_sepcon1; apply exp_derives; intros t2.
      rewrite exp_sepcon1; apply exp_derives; intros v2.
      normalize.
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl |]; apply now_later |].
      rewrite <- later_sepcon.
      apply later_derives.
      apply andp_right; [apply andp_right; [apply andp_right |] |].
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left1, andp_left1, derives_refl |].
        intro rho; simpl.
        apply (predicates_sl.extend_sepcon (extend_tc.extend_tc_lvalue Delta e rho)).
      * unfold local, lift1; unfold_lift; intro rho; simpl.
        eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left1, andp_left2, derives_refl |].
        rewrite <- (andp_TT (prop _)) at 1.
        normalize.
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left2, derives_refl |].
        rewrite sepcon_assoc.
        apply sepcon_derives; auto.
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left2, derives_refl |].
        rewrite subst_sepcon.
        rewrite (closed_wrt_subst _ _ F); auto.
        unfold closed_wrt_modvars in H.
        rewrite <- modifiedvars_aux.
        auto.
    - rewrite exp_sepcon1; apply exp_derives; intros sh.
      rewrite exp_sepcon1; apply exp_derives; intros e1.
      rewrite exp_sepcon1; apply exp_derives; intros t1.
      rewrite exp_sepcon1; apply exp_derives; intros v2.
      normalize.
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl |]; apply now_later |].
      rewrite <- later_sepcon.
      apply later_derives.
      apply andp_right; [apply andp_right; [apply andp_right |] |].
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left1, andp_left1, derives_refl |].
        intro rho; simpl.
        apply (predicates_sl.extend_sepcon (extend_tc.extend_tc_lvalue Delta e1 rho)).
      * unfold local, lift1; unfold_lift; intro rho; simpl.
        eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left1, andp_left2, derives_refl |].
        rewrite <- (andp_TT (prop _)) at 1.
        normalize.
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left2, derives_refl |].
        rewrite sepcon_assoc.
        apply sepcon_derives; auto.
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left2, derives_refl |].
        rewrite subst_sepcon.
        rewrite (closed_wrt_subst _ _ F); auto.
        unfold closed_wrt_modvars in H.
        rewrite <- modifiedvars_aux.
        auto.
  + rewrite frame_normal.
    eapply semax_pre; [| apply AuxDefs.semax_store_backward].
    apply andp_left2.
    rewrite exp_sepcon1; apply exp_derives; intros sh.
    normalize.
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl |]; apply now_later |].
    rewrite <- later_sepcon.
    apply later_derives.
    apply andp_right.
    - eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, derives_refl |].
      intro rho; simpl.
      apply (predicates_sl.extend_sepcon (extend_tc.extend_andp _ _ (extend_tc.extend_tc_lvalue Delta e1 rho) (extend_tc.extend_tc_expr Delta (Ecast e2 (typeof e1)) rho))).
    - eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left2, derives_refl |].
      rewrite sepcon_assoc; apply sepcon_derives; auto.
      rewrite <- (sepcon_emp ((` (mapsto sh (typeof e1))) (eval_lvalue e1)
                   ((` (force_val oo sem_cast (typeof e2) (typeof e1))) (eval_expr e2)))) at 2.
      eapply derives_trans; [| apply wand_frame_hor].
      apply sepcon_derives; [apply derives_refl |].
      rewrite <- wand_sepcon_adjoint.
      rewrite sepcon_emp; auto.
  + rewrite frame_normal.
    apply AuxDefs.semax_skip.
  + rewrite FF_sepcon.
    apply AuxDefs.semax_builtin.
  + apply AuxDefs.semax_label.
    apply IHsemax; auto.
  + rewrite FF_sepcon.
    apply AuxDefs.semax_goto.
  + eapply semax_conseq; [.. | apply IHsemax; auto].
    - apply sepcon_derives_full; [exact H0 |].
      reduce2derives.
      auto.
    - destruct R, R'.
      apply sepcon_derives_full; [exact H1 |].
      reduce2derives.
      auto.
    - destruct R, R'.
      apply sepcon_derives_full; [exact H2 |].
      reduce2derives.
      auto.
    - destruct R, R'.
      apply sepcon_derives_full; [exact H3 |].
      reduce2derives.
      auto.
    - intros; destruct R, R'.
      apply sepcon_derives_full; [apply H4 |].
      reduce2derives.
      auto.
Qed.
(*moved up
Lemma tc_fn_return_sub:
  forall (CS : compspecs) (Delta Delta' : tycontext),
  tycontext_sub Delta Delta' ->
  forall ret retsig,
  tc_fn_return Delta ret retsig ->
  tc_fn_return Delta' ret retsig.
Proof.
  intros.
  hnf in H0 |- *.
  destruct ret; auto.
  destruct H as [? _].
  specialize (H i).
  destruct ((temp_types Delta) ! i), ((temp_types Delta') ! i); auto.
  + subst; auto.
  + tauto.
Qed.

Lemma obox_sub:
  forall (Delta Delta' : tycontext) id P rho,
    tycontext_sub Delta Delta' ->
    temp_guard Delta id ->
    tc_environ Delta rho ->
    obox Delta id P rho |-- obox Delta' id P rho.
Proof.
  intros.
  unfold obox.
  destruct H as [? _].
  specialize (H id).
  hnf in H0.
  destruct ((temp_types Delta) ! id), ((temp_types Delta') ! id); auto.
  + subst; auto.
  + tauto.
  + tauto.
Qed.

Lemma oboxopt_sub:
  forall (Delta Delta' : tycontext) id P rho,
    tycontext_sub Delta Delta' ->
    temp_guard_opt Delta id ->
    tc_environ Delta rho ->
    oboxopt Delta id P rho |-- oboxopt Delta' id P rho.
Proof.
  intros.
  destruct id.
  + apply obox_sub; auto.
  + simpl.
    auto.
Qed.

Lemma typecheck_tid_ptr_compare_sub: forall Delta Delta' id,
  tycontext_sub Delta Delta' ->
  typecheck_tid_ptr_compare Delta id = true ->
  typecheck_tid_ptr_compare Delta' id = true.
Proof.
  unfold typecheck_tid_ptr_compare.
  intros.
  destruct H as [? _].
  specialize (H id).
  hnf in H0.
  destruct ((temp_types Delta) ! id), ((temp_types Delta') ! id); auto.
  + subst; auto.
  + inv H0.
Qed.

Theorem semax_Delta_subsumption:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta Delta' P c R,
       tycontext_sub Delta Delta' ->
     @semax CS Espec Delta P c R -> @semax CS Espec Delta' P c R.
Proof.
  intros.
  induction H0.
  + apply semax_pre with (!! (bool_type (typeof b) = true) && tc_expr Delta' (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P); [| apply AuxDefs.semax_ifthenelse; auto].
    apply andp_ENTAIL; [| apply ENTAIL_refl].
    apply andp_ENTAIL; [apply ENTAIL_refl |].
    intro rho; simpl.
    unfold local, lift1; normalize.
    apply Clight_assert_lemmas.tc_expr_sub; auto.
    eapply semax_lemmas.typecheck_environ_sub; eauto.
  + eapply AuxDefs.semax_seq; eauto.
  + eapply AuxDefs.semax_break; eauto.
  + eapply AuxDefs.semax_continue; eauto.
  + eapply AuxDefs.semax_loop; eauto.
  + eapply semax_pre with (!! (is_int_type (typeof a) = true) && (Q && local (tc_environ Delta'))); [solve_andp |].
    eapply AuxDefs.semax_switch.
    - intros; simpl.
      rewrite (add_andp _ _ (H0 _)).
      unfold local, lift1; normalize.
      apply andp_left2.
      apply Clight_assert_lemmas.tc_expr_sub; auto.
      eapply semax_lemmas.typecheck_environ_sub; eauto.
    - intros.
      eapply semax_pre; [| apply H2].
      solve_andp.
  + eapply semax_pre; [| apply AuxDefs.semax_call_backward].
    apply exp_ENTAIL; intros argsig.
    apply exp_ENTAIL; intros retsig.
    apply exp_ENTAIL; intros cc.
    apply exp_ENTAIL; intros A.
    apply exp_ENTAIL; intros P.
    apply exp_ENTAIL; intros Q.
    apply exp_ENTAIL; intros NEP.
    apply exp_ENTAIL; intros NEQ.
    apply exp_ENTAIL; intros ts.
    apply exp_ENTAIL; intros x.
    normalize.
    apply andp_ENTAIL; [apply andp_ENTAIL; [apply andp_right; [apply andp_left1 |] |] |].
    - intro rho; unfold local, lift1; normalize.
      simpl; apply prop_right.
      destruct H0; split; [auto |].
      destruct H2; split; [auto |].
      eapply tc_fn_return_sub; eauto.
    - apply later_ENTAIL.
      apply andp_ENTAIL.
      * intro rho; simpl; unfold local, lift1; normalize.
        apply Clight_assert_lemmas.tc_expr_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * intro rho; simpl; unfold local, lift1; normalize.
        apply Clight_assert_lemmas.tc_exprlist_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
    - apply ENTAIL_refl.
    - apply later_ENTAIL.
      apply sepcon_ENTAIL; [apply ENTAIL_refl |].
      destruct H0 as [_ [_ ?]].
      intro rho; simpl.
      unfold local, lift1; normalize.
      apply oboxopt_sub; auto.
      * eapply tc_fn_return_temp_guard_opt; eauto.
      * eapply semax_lemmas.typecheck_environ_sub; eauto.
  + eapply semax_pre; [| apply AuxDefs.semax_return].
    assert (ret_type Delta = ret_type Delta') by (unfold tycontext_sub in *; tauto).
    rewrite H0.
    apply andp_ENTAIL; [| apply ENTAIL_refl].
    intro rho; simpl.
    unfold local, lift1; normalize.
    destruct ret.
    - apply Clight_assert_lemmas.tc_expr_sub; auto.
      eapply semax_lemmas.typecheck_environ_sub; eauto.
    - simpl; auto.
  + eapply semax_pre; [| apply AuxDefs.semax_set_ptr_compare_load_cast_load_backward].
    apply orp_ENTAIL; [apply orp_ENTAIL; [apply orp_ENTAIL |] |].
    - apply later_ENTAIL.
      apply andp_ENTAIL; [| apply ENTAIL_refl].
      apply andp_ENTAIL.
      * unfold local, lift1; intro rho; simpl; normalize.
        apply Clight_assert_lemmas.tc_expr_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * unfold local, lift1; intro rho; simpl; normalize.
        apply Clight_assert_lemmas.tc_temp_id_sub; auto.
    - apply exp_ENTAIL; intro cmp.
      apply exp_ENTAIL; intro e1.
      apply exp_ENTAIL; intro e2.
      apply exp_ENTAIL; intro ty.
      apply exp_ENTAIL; intro sh1.
      apply exp_ENTAIL; intro sh2.
      apply andp_ENTAIL; [| apply later_ENTAIL, andp_ENTAIL; [apply andp_ENTAIL; [apply andp_ENTAIL; [apply andp_ENTAIL; [apply andp_ENTAIL |] |] |] |]].
      * 
unfold local, lift1; intro rho; simpl; normalize.
        destruct H1; split; auto.
        destruct H2; split; auto.
        destruct H3; split; auto.
        destruct H4; split; auto.
        destruct H5; split; auto.
        destruct H6; split; auto.
        eapply typecheck_tid_ptr_compare_sub; eauto.
      * unfold local, lift1; intro rho; simpl; normalize.
        apply Clight_assert_lemmas.tc_expr_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * unfold local, lift1; intro rho; simpl; normalize.
        apply Clight_assert_lemmas.tc_expr_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
    - apply exp_ENTAIL; intro sh.
      apply exp_ENTAIL; intro t2.
      apply exp_ENTAIL; intro v2.
      apply andp_ENTAIL; [| apply later_ENTAIL, andp_ENTAIL; [apply andp_ENTAIL; [apply andp_ENTAIL |] |] ].
      * unfold local, lift1; intro rho; simpl; normalize.
        destruct H1; split; auto.
        eapply Clight_assert_lemmas.typeof_temp_sub; eauto.
      * unfold local, lift1; intro rho; simpl; normalize.
        apply Clight_assert_lemmas.tc_lvalue_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
    - apply exp_ENTAIL; intro sh.
      apply exp_ENTAIL; intro e1.
      apply exp_ENTAIL; intro t1.
      apply exp_ENTAIL; intro v2.
      apply andp_ENTAIL; [| apply later_ENTAIL, andp_ENTAIL; [apply andp_ENTAIL; [apply andp_ENTAIL |] |] ].
      * unfold local, lift1; intro rho; simpl; normalize.
        destruct H1; split; auto.
        destruct H2; split; auto.
        eapply Clight_assert_lemmas.typeof_temp_sub; eauto.
      * unfold local, lift1; intro rho; simpl; normalize.
        apply Clight_assert_lemmas.tc_lvalue_sub; auto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
  + eapply semax_pre; [| apply AuxDefs.semax_store_backward].    
    apply exp_ENTAIL; intro sh.
    apply andp_ENTAIL; [apply ENTAIL_refl |].
    apply later_ENTAIL.
    apply andp_ENTAIL; [| apply ENTAIL_refl].
    apply andp_ENTAIL.
    - unfold local, lift1; intro rho; simpl; normalize.
      apply Clight_assert_lemmas.tc_lvalue_sub; auto.
      eapply semax_lemmas.typecheck_environ_sub; eauto.
    - unfold local, lift1; intro rho; simpl; normalize.
      apply Clight_assert_lemmas.tc_expr_sub; auto.
      eapply semax_lemmas.typecheck_environ_sub; eauto.
  + apply AuxDefs.semax_skip.
  + apply AuxDefs.semax_builtin.
  + apply AuxDefs.semax_label; auto.
  + apply AuxDefs.semax_goto.
  + eapply semax_conseq; [.. | exact IHsemax].
    - eapply derives_trans; [| exact H0].
      apply andp_derives; [| apply andp_derives]; auto.
      * unfold local, lift1; intro rho; simpl; normalize.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * intro; apply Clight_assert_lemmas.allp_fun_id_sub; auto.
    - eapply derives_trans; [| exact H1].
      apply andp_derives; [| apply andp_derives]; auto.
      * unfold local, lift1; intro rho; simpl; normalize.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * intro; apply Clight_assert_lemmas.allp_fun_id_sub; auto.
    - eapply derives_trans; [| exact H2].
      apply andp_derives; [| apply andp_derives]; auto.
      * unfold local, lift1; intro rho; simpl; normalize.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * intro; apply Clight_assert_lemmas.allp_fun_id_sub; auto.
    - eapply derives_trans; [| exact H3].
      apply andp_derives; [| apply andp_derives]; auto.
      * unfold local, lift1; intro rho; simpl; normalize.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * intro; apply Clight_assert_lemmas.allp_fun_id_sub; auto.
    - intros.
      eapply derives_trans; [| apply H4].
      apply andp_derives; [| apply andp_derives]; auto.
      * unfold local, lift1; intro rho; simpl; normalize.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * intro; apply Clight_assert_lemmas.allp_fun_id_sub; auto.
Qed.*)

Lemma semax_loop_nocontinue:
  forall {CS: compspecs} {Espec: OracleKind},
 forall Delta P body incr R,
 @semax CS Espec Delta P (Ssequence body incr) (loop_nocontinue_ret_assert P R) ->
 @semax CS Espec Delta P (Sloop body incr) R.
Proof.
  intros.
  apply semax_seq_inv in H.
  destruct H as [Q [? ?]].
  eapply (AuxDefs.semax_loop _ P Q).
  + clear - H.
    unfold overridePost, loop_nocontinue_ret_assert, loop1_ret_assert in *.
    eapply semax_post; [| | | | exact H].
    - apply andp_left2.
      destruct R.
      apply derives_refl.
    - apply andp_left2.
      destruct R.
      apply derives_refl.
    - apply andp_left2.
      destruct R.
      apply FF_left.
    - intro.
      apply andp_left2.
      destruct R.
      apply derives_refl.
  + clear - H0.
    unfold overridePost, loop_nocontinue_ret_assert, loop2_ret_assert in *.
    auto.
Qed.

Lemma semax_if_seq:
 forall {CS: compspecs} {Espec: OracleKind} Delta P e c1 c2 c Q,
 semax Delta P (Sifthenelse e (Ssequence c1 c) (Ssequence c2 c)) Q ->
 semax Delta P (Ssequence (Sifthenelse e c1 c2) c) Q.
Proof.
  intros.
  apply semax_ifthenelse_inv in H.
  eapply semax_conseq; [exact H | intros; apply derives_full_refl .. |].
  rewrite exp_andp2.
  apply semax_extract_exists.
  intros P'.
  rewrite andp_comm, andp_assoc.
  apply semax_extract_prop; intros [? ?].
  rewrite andp_comm.
  apply semax_seq_inv in H0.
  apply semax_seq_inv in H1.
  destruct H0 as [Q1 [? ?]], H1 as [Q2 [? ?]].
  apply AuxDefs.semax_seq with (orp Q1 Q2); [apply AuxDefs.semax_ifthenelse |].
  + eapply semax_post; [| | | | exact H0].
    - destruct Q; apply andp_left2, orp_right1, derives_refl.
    - destruct Q; apply andp_left2, derives_refl.
    - destruct Q; apply andp_left2, derives_refl.
    - intro; destruct Q; apply andp_left2, derives_refl.
  + eapply semax_post; [| | | | exact H1].
    - destruct Q; apply andp_left2, orp_right2, derives_refl.
    - destruct Q; apply andp_left2, derives_refl.
    - destruct Q; apply andp_left2, derives_refl.
    - intro; destruct Q; apply andp_left2, derives_refl.
  + rewrite orp_is_exp.
    apply semax_extract_exists.
    intro.
    destruct x; auto.
Qed.

Lemma semax_loop_unroll1:
  forall {CS: compspecs} {Espec: OracleKind} Delta P P' Q body incr R,
  @semax CS Espec Delta P body (loop1_ret_assert P' R) ->
  @semax CS Espec Delta P' incr (loop2_ret_assert Q R) ->
  @semax CS Espec Delta Q (Sloop body incr) R ->
  @semax CS Espec Delta P (Sloop body incr) R.
Proof.
  intros.
  apply semax_loop_inv in H1.
  apply semax_pre with (P || Q ||
                  (EX Q : environ -> mpred,
                    (EX Q' : environ -> mpred,
                     !! (semax Delta Q body (loop1_ret_assert Q' R) /\
                         semax Delta Q' incr (loop2_ret_assert Q R)) && Q))).
  { apply andp_left2, orp_right1, orp_right1, derives_refl. }
  apply AuxDefs.semax_loop with (P' ||
                  (EX Q : environ -> mpred,
                    (EX Q' : environ -> mpred,
                     !! (semax Delta Q body (loop1_ret_assert Q' R) /\
                         semax Delta Q' incr (loop2_ret_assert Q R)) && Q'))).
  + apply semax_orp; [apply semax_orp |].
    - eapply semax_post; [.. | exact H].
      * unfold loop1_ret_assert; destruct R.
        apply andp_left2, orp_right1, derives_refl.
      * unfold loop1_ret_assert; destruct R.
        apply andp_left2, derives_refl.
      * unfold loop1_ret_assert; destruct R.
        apply andp_left2, orp_right1, derives_refl.
      * intros.
        unfold loop1_ret_assert; destruct R.
        apply andp_left2, derives_refl.
    - eapply semax_conseq; [exact H1 | intros; apply derives_full_refl .. |].
      apply semax_extract_exists; intros Q'.
      apply semax_extract_exists; intros Q''.
      apply semax_extract_prop; intros [?H ?H].
      apply semax_post with (loop1_ret_assert Q'' R); auto.
      * unfold loop1_ret_assert; destruct R.
        apply andp_left2, orp_right2, (exp_right Q'), (exp_right Q'').
        apply andp_right; [apply prop_right; auto | apply derives_refl].
      * unfold loop1_ret_assert; destruct R.
        apply andp_left2, derives_refl.
      * unfold loop1_ret_assert; destruct R.
        apply andp_left2, orp_right2, (exp_right Q'), (exp_right Q'').
        apply andp_right; [apply prop_right; auto | apply derives_refl].
      * intros.
        unfold loop1_ret_assert; destruct R.
        apply andp_left2, derives_refl.
    - apply semax_extract_exists; intros Q'.
      apply semax_extract_exists; intros Q''.
      apply semax_extract_prop; intros [?H ?H].
      apply semax_post with (loop1_ret_assert Q'' R); auto.
      * unfold loop1_ret_assert; destruct R.
        apply andp_left2, orp_right2, (exp_right Q'), (exp_right Q'').
        apply andp_right; [apply prop_right; auto | apply derives_refl].
      * unfold loop1_ret_assert; destruct R.
        apply andp_left2, derives_refl.
      * unfold loop1_ret_assert; destruct R.
        apply andp_left2, orp_right2, (exp_right Q'), (exp_right Q'').
        apply andp_right; [apply prop_right; auto | apply derives_refl].
      * intros.
        unfold loop1_ret_assert; destruct R.
        apply andp_left2, derives_refl.
  + apply semax_orp.
    - apply semax_post with (loop2_ret_assert Q R); auto.
      * unfold loop2_ret_assert; destruct R.
        apply andp_left2, orp_right1, orp_right2, derives_refl.
      * unfold loop2_ret_assert; destruct R.
        apply andp_left2, derives_refl.
      * unfold loop2_ret_assert; destruct R.
        apply andp_left2, derives_refl.
      * intros.
        unfold loop1_ret_assert; destruct R.
        apply andp_left2, derives_refl.
    - apply semax_extract_exists; intros Q'.
      apply semax_extract_exists; intros Q''.
      apply semax_extract_prop; intros [?H ?H].
      apply semax_post with (loop2_ret_assert Q' R); auto.
      * unfold loop1_ret_assert; destruct R.
        apply andp_left2, orp_right2, (exp_right Q'), (exp_right Q'').
        apply andp_right; [apply prop_right; auto | apply derives_refl].
      * unfold loop1_ret_assert; destruct R.
        apply andp_left2, derives_refl.
      * unfold loop1_ret_assert; destruct R.
        apply andp_left2, derives_refl.
      * intros.
        unfold loop1_ret_assert; destruct R.
        apply andp_left2, derives_refl.
Qed.

Theorem seq_assoc:
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta P s1 s2 s3 R,
        @semax CS Espec Delta P (Ssequence s1 (Ssequence s2 s3)) R <->
        @semax CS Espec Delta P (Ssequence (Ssequence s1 s2) s3) R.
Proof.
  intros.
  split; intros.
  + apply semax_seq_inv in H.
    destruct H as [? [? ?]].
    apply semax_seq_inv in H0.
    destruct H0 as [? [? ?]].
    eapply AuxDefs.semax_seq; eauto.
    eapply AuxDefs.semax_seq; eauto.
    destruct R; auto.
  + apply semax_seq_inv in H.
    destruct H as [? [? ?]].
    apply semax_seq_inv in H.
    destruct H as [? [? ?]].
    eapply AuxDefs.semax_seq with x0; [destruct R; exact H |].
    eapply AuxDefs.semax_seq; eauto.
Qed.

Theorem semax_seq_skip:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta P s Q,
    @semax CS Espec Delta P s Q <-> @semax CS Espec Delta P (Ssequence s Sskip) Q.
Proof.
  intros.
  split; intros.
  + apply AuxDefs.semax_seq with (RA_normal Q).
    - destruct Q; auto.
    - eapply semax_post; [.. | apply AuxDefs.semax_skip].
      * apply ENTAIL_refl.
      * apply andp_left2, FF_left.
      * apply andp_left2, FF_left.
      * intros; apply andp_left2, FF_left.
  + apply semax_seq_inv in H.
    destruct H as [? [? ?]].
    apply semax_skip_inv in H0.
    eapply semax_conseq; [apply derives_full_refl | .. | exact H].
    - destruct Q; auto.
    - destruct Q; apply derives_full_refl.
    - destruct Q; apply derives_full_refl.
    - intros; destruct Q; apply derives_full_refl.
Qed.

Theorem semax_skip_seq:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta P s Q,
    @semax CS Espec Delta P s Q <-> @semax CS Espec Delta P (Ssequence Sskip s) Q.
Proof.
  intros.
  split; intros.
  + apply AuxDefs.semax_seq with P; auto.
    eapply semax_post; [.. | apply AuxDefs.semax_skip].
    - destruct Q; apply ENTAIL_refl.
    - apply andp_left2, FF_left.
    - apply andp_left2, FF_left.
    - intros; apply andp_left2, FF_left.
  + apply semax_seq_inv in H.
    destruct H as [? [? ?]].
    apply semax_skip_inv in H.
    eapply semax_conseq; [| intros; apply derives_full_refl .. | exact H0].
    destruct Q; auto.
Qed.

Theorem semax_seq_Slabel:
   forall {CS:compspecs} {Espec: OracleKind},
     forall Delta (P:environ -> mpred) (c1 c2:statement) (Q:ret_assert) l,
   @semax CS Espec Delta P (Ssequence (Slabel l c1) c2) Q <-> 
   @semax CS Espec Delta P (Slabel l (Ssequence c1 c2)) Q.
Proof.
  intros.
  split; intros.
  + apply semax_seq_inv in H.
    destruct H as [? [? ?]].
    apply semax_Slabel_inv in H.
    apply AuxDefs.semax_label.
    eapply AuxDefs.semax_seq; eauto.
  + apply semax_Slabel_inv in H.
    apply semax_seq_inv in H.
    destruct H as [? [? ?]].
    eapply AuxDefs.semax_seq; eauto.
    apply AuxDefs.semax_label; auto.
Qed.

Fixpoint fold_Ssequence lc :=
  match lc with
  | nil => Sskip
  | c1 :: nil => c1
  | c :: lc0 => Ssequence c (fold_Ssequence lc0)
  end.

Definition non_Sseq c :=
  match c with
  | Ssequence _ _ => False
  | _ => True
  end.

Inductive unfold_Sseq_rel: statement -> list statement -> Prop :=
  | singleton: forall c, non_Sseq c -> unfold_Sseq_rel c (c :: nil)
  | tl_step: forall c1 c2 lc, non_Sseq c1 -> unfold_Sseq_rel c2 lc ->
                 unfold_Sseq_rel (Ssequence c1 c2) (c1 :: lc)
  | hd_step: forall c1 c2 c3 lc, unfold_Sseq_rel (Ssequence c1 (Ssequence c2 c3)) lc ->
                 unfold_Sseq_rel (Ssequence (Ssequence c1 c2) c3) lc
  .

Lemma unfold_Sseq_rel_non_nil: forall {c} {P: Prop}, unfold_Sseq_rel c nil -> P.
Proof.
  intros.
  remember nil as lc.
  induction H.
  + congruence.
  + congruence.
  + auto.
Qed.

Definition semax_equiv {CS: compspecs} {Espec: OracleKind} c1 c2: Prop := forall Delta P Q, semax Delta P c1 Q <-> semax Delta P c2 Q.

Lemma semax_equiv_seq: forall {CS: compspecs} {Espec: OracleKind} c1 c2 c3 c4,
  semax_equiv c1 c2 ->
  semax_equiv c3 c4 ->
  semax_equiv (Ssequence c1 c3) (Ssequence c2 c4).
Proof.
  intros.
  hnf; intros; split; intros.
  + apply semax_seq_inv in H1.
    destruct H1 as [? [? ?]].
    rewrite (H Delta P _) in H1.
    rewrite (H0 Delta _ _) in H2.
    eapply AuxDefs.semax_seq; eauto.
  + apply semax_seq_inv in H1.
    destruct H1 as [? [? ?]].
    rewrite <- (H Delta P _) in H1.
    rewrite <- (H0 Delta _ _) in H2.
    eapply AuxDefs.semax_seq; eauto.
Qed.

Lemma semax_equiv_sym: forall {CS: compspecs} {Espec: OracleKind} c1 c2, semax_equiv c1 c2 -> semax_equiv c2 c1.
Proof.
  intros.
  hnf in H |- *.
  intros.
  specialize (H Delta P Q).
  tauto.
Qed.

Lemma semax_equiv_trans: forall {CS: compspecs} {Espec: OracleKind} c1 c2 c3, semax_equiv c1 c2 -> semax_equiv c2 c3 -> semax_equiv c1 c3.
Proof.
  intros.
  hnf in H, H0 |- *.
  intros.
  specialize (H Delta P Q).
  specialize (H0 Delta P Q).
  tauto.
Qed.
  
Lemma unfold_Sseq_rel_sound: forall {CS: compspecs} {Espec: OracleKind} c lc,
  unfold_Sseq_rel c lc -> semax_equiv (fold_Ssequence lc) c.
Proof.
  intros.
  induction H.
  + simpl.
    hnf; intros; tauto.
  + simpl.
    destruct lc; [apply (unfold_Sseq_rel_non_nil H0) |].
    apply semax_equiv_seq; [hnf; intros; tauto | assumption].
  + eapply semax_equiv_trans; [eauto |].
    hnf; intros.
    apply seq_assoc.
Qed.

Lemma unfold_Ssequence_unfold_Sseq_rel: forall c, unfold_Sseq_rel c (unfold_Ssequence c).
Proof.
  intros.
  induction c; try solve [apply singleton, I].
  revert c2 IHc2.
  clear IHc1.
  induction c1; intros; try solve [apply tl_step; [apply I | auto]].
  apply hd_step.
  replace (unfold_Ssequence (Ssequence (Ssequence c1_1 c1_2) c2)) with
    (unfold_Ssequence (Ssequence c1_1 (Ssequence c1_2 c2))).
  2:{
    simpl.
    rewrite <- app_assoc.
    reflexivity.
  }
  apply IHc1_1.
  apply IHc1_2.
  apply IHc2.
Qed.

Lemma unfold_Ssequence_sound: forall {CS: compspecs} {Espec: OracleKind} c, semax_equiv (fold_Ssequence (unfold_Ssequence c)) c.
Proof.
  intros.
  apply unfold_Sseq_rel_sound.
  apply unfold_Ssequence_unfold_Sseq_rel.
Qed.

Lemma semax_unfold_Ssequence': forall {CS: compspecs} {Espec: OracleKind} c1 c2,
  unfold_Ssequence c1 = unfold_Ssequence c2 ->
  (forall P Q Delta, semax Delta P c1 Q <-> semax Delta P c2 Q).
Proof.
  intros.
  eapply semax_equiv_trans.
  + apply semax_equiv_sym.
    apply unfold_Ssequence_sound.
  + rewrite H.
    apply unfold_Ssequence_sound.
Qed.

Lemma semax_unfold_Ssequence: forall {CS: compspecs} {Espec: OracleKind} c1 c2,
  unfold_Ssequence c1 = unfold_Ssequence c2 ->
  (forall P Q Delta, @semax CS Espec Delta P c1 Q -> @semax CS Espec Delta P c2 Q).
Proof.
  intros.
  pose proof semax_unfold_Ssequence' _ _ H.
  clear - H0 H1.
  firstorder.
Qed.

Lemma semax_fun_id:
  forall {CS: compspecs} {Espec: OracleKind},
      forall id f Delta P Q c,
    (var_types Delta) ! id = None ->
    (glob_specs Delta) ! id = Some f ->
    (glob_types Delta) ! id = Some (type_of_funspec f) ->
    @semax CS Espec Delta (P && `(func_ptr f) (eval_var id (type_of_funspec f)))
                  c Q ->
    @semax CS Espec Delta P c Q.
Proof.
  intros.
  eapply semax_conseq; [| intros; apply derives_full_refl .. | apply H2].
  reduceR.
  apply andp_right; [solve_andp |].
  rewrite andp_comm.
  rewrite imp_andp_adjoint.
  rewrite imp_andp_adjoint.
  intros rho.
  apply (allp_left _ id).
  apply (allp_left _ f).
  rewrite prop_imp by auto.
  apply exp_left; intros b.
  unfold local, lift1; unfold_lift; simpl. normalize.
  rewrite <- imp_andp_adjoint.
  rewrite <- imp_andp_adjoint. normalize. 
  unfold derives. apply predicates_hered.exp_right with (x:=b). eapply predicates_hered.prop_andp_right.
  - unfold eval_var. rewrite H3.
    destruct H4 as [_ [? _]].
    specialize (H4 id).
    rewrite H in H4.
    destruct (Map.get (ve_of rho) id) as [[? ?] |]; [exfalso | auto].
    specialize (H4 t).
    destruct H4 as [_ ?].
    specialize (H4 ltac:(eexists; eauto)). congruence.
  - unfold func_ptr, seplog.func_ptr. (* apply predicates_hered.exp_right with (x:=f). *)
    apply predicates_hered.andp_left1. 
    apply predicates_hered.exp_left; intros bb.
    apply normalize.derives_extract_prop; intros X; inv X. trivial.
Qed. (*old proof:
  intros.
  eapply semax_conseq; [| intros; apply derives_full_refl .. | apply H2].
  reduceR.
  apply andp_right; [solve_andp |].
  rewrite andp_comm.
  rewrite imp_andp_adjoint.
  rewrite imp_andp_adjoint.
  apply (allp_left _ id).
  apply (allp_left _ f).
  rewrite prop_imp by auto.
  apply exp_left; intros b.
  rewrite <- imp_andp_adjoint.
  rewrite <- imp_andp_adjoint.
  unfold local, lift1; unfold_lift; intro rho; simpl.
  unfold eval_var, func_ptr.
  apply (exp_right b).
  normalize.
  rewrite H3.
  apply andp_right; [| solve_andp].
  apply prop_right.
  destruct H4 as [_ [? _]].
  specialize (H4 id).
  rewrite H in H4.
  destruct (Map.get (ve_of rho) id) as [[? ?] |]; [exfalso | auto].
  specialize (H4 t).
  destruct H4 as [_ ?].
  specialize (H4 ltac:(eexists; eauto)).
  congruence.
Qed.
*)
(*Lemma semax_fun_id:
  forall {CS: compspecs} {Espec: OracleKind},
      forall id f Delta P Q c,
    (var_types Delta) ! id = None ->
    (glob_specs Delta) ! id = Some f ->
    (glob_types Delta) ! id = Some (type_of_funspec f) ->
    @semax CS Espec Delta (P && `(func_ptr f) (eval_var id (type_of_funspec f)))
                  c Q ->
    @semax CS Espec Delta P c Q.
Proof.
  intros.
  eapply semax_conseq; [| intros; apply derives_full_refl .. | apply H2].
  reduceR.
  apply andp_right; [solve_andp |].
  rewrite andp_comm.
  rewrite imp_andp_adjoint.
  rewrite imp_andp_adjoint. hnf. 
(*  apply (allp_left _ id).
  apply (allp_left _ f).*)
  rewrite prop_imp by auto.
  apply exp_left; intros b.
  rewrite <- imp_andp_adjoint.
  rewrite <- imp_andp_adjoint.
  unfold local, lift1; unfold_lift; intro rho; simpl.
  unfold eval_var, func_ptr.
  apply (exp_right b).
  normalize.
  rewrite H3.
  apply andp_right; [| solve_andp].
  apply prop_right.
  destruct H4 as [_ [? _]].
  specialize (H4 id).
  rewrite H in H4.
  destruct (Map.get (ve_of rho) id) as [[? ?] |]; [exfalso | auto].
  specialize (H4 t).
  destruct H4 as [_ ?].
  specialize (H4 ltac:(eexists; eauto)).
  congruence.
Qed.
*)

Lemma nocontinue_ls_spec: forall sl, nocontinue_ls sl = true -> nocontinue (seq_of_labeled_statement sl) = true.
Proof.
  intros.
  induction sl.
  + reflexivity.
  + simpl in *.
    destruct (nocontinue s); [| inv H].
    auto.
Qed.

Lemma nocontinue_ls_spec': forall sl n, nocontinue_ls sl = true -> nocontinue (seq_of_labeled_statement (select_switch n sl)) = true.
Proof.
  intros.
  apply nocontinue_ls_spec in H.
  unfold select_switch.
  destruct (select_switch_case n sl) eqn:?Hs.
  + induction sl.
    - inv Hs.
    - simpl in Hs.
      destruct o as [c|]; [destruct (zeq c n) |].
      * subst c; inv Hs.
        apply H.
      * change (nocontinue s && nocontinue (seq_of_labeled_statement sl) = true)%bool in H.
        rewrite andb_true_iff in H.
        apply IHsl; auto.
        tauto.
      * change (nocontinue s && nocontinue (seq_of_labeled_statement sl) = true)%bool in H.
        rewrite andb_true_iff in H.
        apply IHsl; auto.
        tauto.
  + induction sl.
    - reflexivity.
    - simpl in Hs |- *.
      destruct o.
      * change (nocontinue s && nocontinue (seq_of_labeled_statement sl) = true)%bool in H.
        rewrite andb_true_iff in H.
        apply IHsl; [tauto |].
        if_tac in Hs; [inv Hs | auto].
      * exact H.
Qed.

Lemma semax_nocontinue_inv:
  forall CS Espec Delta Pre s Post Post',
    nocontinue s = true ->
    RA_normal Post = RA_normal Post' ->
    RA_break Post = RA_break Post' ->
    RA_return Post = RA_return Post' ->
    @semax CS Espec Delta Pre s Post -> @semax CS Espec Delta Pre s Post'.
Proof.
  intros.
  revert Post' H0 H1 H2.
  induction H3; intros.
  + change (nocontinue c && nocontinue d = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H) _ H0 H1 H2).
    specialize (IHsemax2 (proj2 H) _ H0 H1 H2).
    apply AuxDefs.semax_ifthenelse; auto.
  + change (nocontinue h && nocontinue t = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H)).
    specialize (IHsemax2 (proj2 H) _ H0 H1 H2).
    eapply AuxDefs.semax_seq; [| eauto].
    apply IHsemax1; destruct Post', R; auto.
  + rewrite H1.
    apply AuxDefs.semax_break.
  + inv H.
  + clear IHsemax1 IHsemax2.
    replace (loop1_ret_assert Q' R) with (loop1_ret_assert Q' Post') in H3_
      by (destruct Post', R; simpl; f_equal; auto).
    replace (loop2_ret_assert Q R) with (loop2_ret_assert Q Post') in H3_0
      by (destruct Post', R; simpl; f_equal; auto).
    eapply AuxDefs.semax_loop; eauto.
  + apply AuxDefs.semax_switch; auto.
    intros n; specialize (H2 n).
    simpl in H.
    apply (nocontinue_ls_spec' _ (Int.unsigned n)) in H.
    specialize (H2 H).
    apply H2; destruct Post', R; simpl; auto.
  + eapply semax_post with (normal_ret_assert R);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply AuxDefs.semax_call_backward.
  + rewrite H2.
    apply AuxDefs.semax_return.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply AuxDefs.semax_set_ptr_compare_load_cast_load_backward.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply AuxDefs.semax_store_backward.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply AuxDefs.semax_skip.
  + apply AuxDefs.semax_builtin.
  + specialize (IHsemax H _ H0 H1 H2).
    apply AuxDefs.semax_label; auto.
  + apply AuxDefs.semax_goto.
  + apply (AuxDefs.semax_conseq _ P' (Build_ret_assert (RA_normal R') (RA_break R') (RA_continue Post') (RA_return R'))).
    - exact H0.
    - rewrite <- H6; exact H1.
    - rewrite <- H7; exact H2.
    - apply derives_full_refl.
    - intros. rewrite <- H8; exact (H4 vl).
    - apply IHsemax; auto.
Qed.

Lemma semax_loop_nocontinue1:
  forall CS Espec Delta Pre s1 s2 s3 Post,
  nocontinue s1 = true ->
  nocontinue s2 = true ->
  nocontinue s3 = true ->
   @semax CS Espec Delta Pre (Sloop (Ssequence s1 (Ssequence s2 s3)) Sskip) Post ->
    @semax CS Espec Delta Pre (Sloop (Ssequence s1 s2) s3) Post.
Proof.
intros.
 rename H1 into Hs3. rename H2 into H1.
apply semax_loop_inv in H1.
eapply AuxDefs.semax_conseq.
apply H1.
instantiate (1:=Post).
1,2,3,4: intros; eapply derives_trans; [  | apply bupd_orp_l];
apply orp_right2; apply andp_left2; apply andp_left2; apply bupd_intro.
apply semax_extract_exists; intro Q.
apply semax_extract_exists; intro Q'.
apply semax_extract_prop; intros [? ?].
apply seq_assoc in H2.
apply semax_seq_inv in H2.
destruct H2 as [Q3 [? ?]].
apply AuxDefs.semax_loop with Q3.
*
assert (nocontinue (Ssequence s1 s2) = true).
simpl; rewrite H,H0; auto.
forget (Ssequence s1 s2) as s.
clear - H2 H5.
revert H2.
apply semax_nocontinue_inv; auto; destruct Post; try reflexivity.
*
clear - H4 H3 Hs3.
apply semax_seq_skip.
econstructor; eauto.
clear - H4 Hs3.
revert H4; apply semax_nocontinue_inv; auto; destruct Post; try reflexivity.
Qed.

Lemma semax_convert_for_while':
 forall CS Espec Delta Pre s1 e2 s3 s4 s5 Post,
  nocontinue s4 = true ->
  nocontinue s3 = true -> 
  @semax CS Espec Delta Pre 
    (Ssequence s1 (Ssequence (Swhile e2 (Ssequence s4 s3)) s5)) Post ->
  @semax CS Espec Delta Pre (Ssequence (Sfor s1 e2 s4 s3) s5) Post.
Proof.
intros.
rename H0 into H9. rename H1 into H0.
apply semax_seq_inv in H0.
destruct H0 as [Q [? ?]].
apply semax_seq_inv in H1.
destruct H1 as [R [? ?]].
unfold Sfor, Swhile  in *.
apply AuxDefs.semax_seq with R; auto.
apply AuxDefs.semax_seq with Q; auto.
rewrite overridePost_overridePost; auto.
clear - H1 H H9.
assert (nocontinue (Sifthenelse e2 Sskip Sbreak) = true) by reflexivity.
forget (Sifthenelse e2 Sskip Sbreak) as s1.
forget (overridePost R Post) as R'; clear - H H1 H0 H9.
fold semax.
apply semax_loop_nocontinue1; auto.
Qed.


Definition semax_extract_prop := @ExtrFacts.semax_extract_prop.

Definition semax_extract_later_prop := @ExtrIFacts.semax_extract_later_prop.

End DeepEmbeddedPracticalLogic.

End DeepEmbedded.

(* After this succeeds, remove "weakest_pre" in veric/semax.v. *)
