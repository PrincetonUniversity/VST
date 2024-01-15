From compcert Require Export Clightdefs.
Require Export VST.veric.base.
Require Export VST.veric.SeparationLogic.
Require Export VST.msl.Extensionality.
Require Export compcert.lib.Coqlib.
Require Export VST.msl.Coqlib2 VST.veric.coqlib4 VST.floyd.coqlib3.
Require Export VST.floyd.jmeq_lemmas.
Require Export VST.floyd.find_nth_tactic.
Require Export VST.veric.juicy_extspec.
Require Import VST.floyd.val_lemmas VST.floyd.assert_lemmas.
Require Import VST.floyd.SeparationLogicFacts.
Import Ctypes LiftNotation.

Open Scope maps.

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
  generalize dependent s;
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

Variable semax_external: forall `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} (E: coPset) (ef: external_function) (A : TypeTree)
       (P: @dtfr Σ (ArgsTT A))
       (Q: @dtfr Σ (AssertTT A)), mpred.

Inductive semax `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} {CS: compspecs} (E: coPset) (Delta: tycontext): assert -> statement -> @ret_assert Σ -> Prop :=
| semax_ifthenelse :
   forall (P: assert) (b: expr) c d R,
     semax E Delta (P ∧ local (`(typed_true (typeof b)) (eval_expr b))) c R ->
     semax E Delta (P ∧ local (`(typed_false (typeof b)) (eval_expr b))) d R ->
     semax E Delta (⌜bool_type (typeof b) = true⌝ ∧ ▷ (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) ∧ P)) (Sifthenelse b c d) R
| semax_seq:
  forall R (P Q: assert) h t,
    semax E Delta P h (overridePost Q R) ->
    semax E Delta Q t R ->
    semax E Delta P (Ssequence h t) R
| semax_break: forall Q,
    semax E Delta (RA_break Q) Sbreak Q
| semax_continue: forall Q,
    semax E Delta (RA_continue Q) Scontinue Q
| semax_loop: forall Q Q' incr body R,
     semax E Delta  Q body (loop1_ret_assert Q' R) ->
     semax E Delta Q' incr (loop2_ret_assert Q R) ->
     semax E Delta Q (Sloop body incr) R
| semax_switch: forall (Q: assert) a sl R,
     (Q ⊢ tc_expr Delta a) ->
     (forall n,
     semax E Delta 
               (local (`eq (eval_expr a) `(Vint n)) ∧ Q)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) ->
     semax E Delta (⌜is_int_type (typeof a) = true⌝ ∧ Q) (Sswitch a sl) R
(*| semax_call_backward: forall ret a bl R,
     semax E Delta
         (∃ argsig: _, ∃ retsig: _, ∃ cc: _,
          ∃ A: _, ∃ P: _, ∃ Q: _, ∃ NEP: _, ∃ NEQ: _, ∃ ts: _, ∃ x: _,
         ⌜Cop.classify_fun (typeof a) =
             Cop.fun_case_f (type_of_params argsig) retsig cc /\
             (retsig = Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig) ∧
          (▷((tc_expr Delta a) ∧ (tc_exprlist Delta (snd (split argsig)) bl)))  ∧
         `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) ∧
          ▷((`(P ts x: assert) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) * oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -∗ R)))
         (Scall ret a bl)
         (normal_ret_assert R)*)
| semax_call_backward: forall ret a bl R,
     semax E Delta
         (∃ argsig: _, ∃ retsig: _, ∃ cc: _,
          ∃ Ef, ∃ A: _, ∃ P: _, ∃ Q: _, ∃ x: _,
         ⌜Ef ⊆ E /\ Cop.classify_fun (typeof a) =
             Cop.fun_case_f (typelist_of_type_list argsig) retsig cc /\
             (retsig = Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig⌝ ∧
          (((tc_expr Delta a) ∧ (tc_exprlist Delta argsig bl)))  ∧
         assert_of (`(func_ptr (mk_funspec  (argsig,retsig) cc Ef A P Q)) (eval_expr a)) ∗
          ▷(assert_of (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho)) ∗ oboxopt Delta ret (maybe_retval (assert_of (Q x)) retsig ret -∗ R)))
         (Scall ret a bl)
         (normal_ret_assert R)
| semax_return: forall (R: ret_assert) ret,
      semax E Delta
                ((tc_expropt Delta ret (ret_type Delta)) ∧
                assert_of (`(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ)))
                (Sreturn ret)
                R
| semax_set_ptr_compare_load_cast_load_backward: forall (P: assert) id e,
    semax E Delta
       ((((▷ ( (tc_expr Delta e) ∧
             (tc_temp_id id (typeof e) Delta e) ∧
             assert_of (subst id (eval_expr e) P))) ∨
        (∃ cmp: Cop.binary_operation, ∃ e1: expr, ∃ e2: expr,
         ∃ ty: type, ∃ sh1: share, ∃ sh2: share,
          ⌜e = Ebinop cmp e1 e2 ty /\
              sh1 ≠ Share.bot /\ sh2 ≠ Share.bot /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true⌝ ∧
            ( ▷ ( (tc_expr Delta e1) ∧
              (tc_expr Delta e2)  ∧
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) ∧
          (<absorb> assert_of (`(mapsto_ sh1 (typeof e1)) (eval_expr e1))) ∧
          (<absorb> assert_of (`(mapsto_ sh2 (typeof e2)) (eval_expr e2))) ∧
          assert_of (subst id (eval_expr (Ebinop cmp e1 e2 ty)) P))))) ∨
        (∃ sh: share, ∃ t2: type, ∃ v2: val,
              ⌜typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e) t2 = true /\
                  readable_share sh⌝ ∧
         ▷ ((tc_lvalue Delta e ∧
              ⌜tc_val (typeof e) v2⌝ ∧
              (<absorb> assert_of (`(mapsto sh (typeof e)) (eval_lvalue e) (`v2)))) ∧
              assert_of (subst id (`v2) P)))) ∨
        (∃ sh: share, ∃ e1: expr, ∃ t1: type, ∃ v2: val,
              ⌜e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh⌝ ∧
         ▷ ((tc_lvalue Delta e1) ∧
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) ∧
              (<absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ∧
              assert_of (subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P))))
        (Sset id e) (normal_ret_assert P)
| semax_store_store_union_hack_backward: forall (P: assert) e1 e2,
    semax E Delta
       ((∃ sh: share, ⌜writable_share sh⌝ ∧
             ▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)))  ∧
             (assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) ∗
              (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))) -∗ P))))
          ∨ (∃ (t2:type) (ch ch': memory_chunk) (sh: share),
             ⌜(numeric_type (typeof e1) && numeric_type t2)%bool = true /\
                 access_mode (typeof e1) = By_value ch /\
                 access_mode t2 = By_value ch' /\
                 decode_encode_val_ok ch ch' /\
                 writable_share sh⌝ ∧
             ▷ (((tc_lvalue Delta e1) ∧ (tc_expr Delta (Ecast e2 (typeof e1))))  ∧
             ((assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1))
                      ∧ assert_of (`(mapsto_ sh t2) (eval_lvalue e1))) ∗
              (∀ v': val,
                 assert_of (`(mapsto sh t2) (eval_lvalue e1) (`v')) -∗
                    (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') )) →
                      (P)))))
       )
        (Sassign e1 e2) (normal_ret_assert P)
| semax_skip: forall P, semax E Delta P Sskip (normal_ret_assert P)
| semax_builtin: forall P opt ext tl el, semax E Delta False (Sbuiltin opt ext tl el) P
| semax_label: forall (P: assert) (c: statement) (Q: ret_assert) l,
    semax E Delta P c Q -> semax E Delta P (Slabel l c) Q
| semax_goto: forall P l, semax E Delta False (Sgoto l) P
| semax_conseq: forall (P': assert) (R': ret_assert) (P: assert) c (R: ret_assert),
    (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ (|={E}=> P')) ->
    (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_normal R') ⊢ (|={E}=> RA_normal R)) ->
    (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_break R') ⊢ (|={E}=> RA_break R)) ->
    (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_continue R') ⊢ (|={E}=> RA_continue R)) ->
    (forall vl, local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_return R' vl) ⊢ (RA_return R vl)) ->
    semax E Delta P' c R' -> semax E Delta P c R
| semax_mask_mono: forall E' P c R, E' ⊆ E -> semax E' Delta P c R -> semax E Delta P c R.

Definition semax_body `{!VSTGS OK_ty Σ}
   (V: varspecs) (G: funspecs) {C: compspecs} (f: function) (spec: ident * funspec): Prop :=
match spec with (_, mk_funspec fsig cc E A P Q) => 
  fst fsig = map snd (fst (fn_funsig f)) /\ 
  snd fsig = snd (fn_funsig f) /\
forall OK_spec x,
  semax E (func_tycontext f V G nil)
      (Clight_seplog.close_precondition (map fst f.(fn_params)) (argsassert_of (P x)) ∗ stackframe_of f)
       f.(fn_body)
      (frame_ret_assert (function_body_ret_assert (fn_return f) (assert_of (Q x))) (stackframe_of f))
end.

Inductive semax_func `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} : forall (V: varspecs) (G: @funspecs Σ) {C: compspecs} (ge: Genv.t Clight.fundef type) (fdecs: list (ident * Clight.fundef)) (G1: funspecs), Prop :=
| semax_func_nil:
    forall C V G ge, semax_func V G ge nil nil
| semax_func_cons:
     forall {C: compspecs} fs id f fsig cc E A P Q (V: varspecs) (G G': funspecs) ge b,
      andb (id_in_list id (map (@fst _ _) G))
      (andb (negb (id_in_list id (map (@fst ident Clight.fundef) fs)))
        (semax_body_params_ok f)) = true ->
      Forall
         (fun it : ident * type =>
          complete_type cenv_cs (snd it) =
          true) (fn_vars f) ->
       var_sizes_ok (f.(fn_vars)) ->
       f.(fn_callconv) = cc ->
       Genv.find_symbol ge id = Some b -> Genv.find_funct_ptr ge b = Some (Internal f) -> 
      semax_body V G f (id, mk_funspec fsig cc E A P Q)->
      semax_func V G ge fs G' ->
      semax_func V G ge ((id, Internal f)::fs)
                 ((id, mk_funspec fsig cc E A P Q)  :: G')
| semax_func_cons_ext:
   forall (V: varspecs) (G: funspecs) {C: compspecs} ge fs id ef argsig retsig E A P (Q : dtfr (AssertTT A))
          argsig'
          (G': funspecs) cc b,
  argsig' = typelist2list argsig ->
  ef_sig ef = mksignature (typlist_of_typelist argsig) (rettype_of_type retsig) cc ->
  id_in_list id (map (@fst _ _) fs) = false ->
  (ef_inline ef = false \/ @withtype_empty Σ A) ->
  (forall gx x (ret : option val),
     (Q x (make_ext_rval gx (rettype_of_type retsig) ret)
        ∧ ⌜Builtins0.val_opt_has_rettype ret (rettype_of_type retsig)⌝
        ⊢ ⌜tc_option_val retsig ret⌝)) ->
  Genv.find_symbol ge id = Some b -> Genv.find_funct_ptr ge b = Some (External ef argsig retsig cc) ->
  (⊢ semax_external E ef A P Q) ->
  semax_func V G ge fs G' ->
  semax_func V G ge ((id, External ef argsig retsig cc)::fs)
       ((id, mk_funspec (argsig', retsig) cc E A P Q)  :: G')
| semax_func_mono: forall  {CS CS'} (CSUB: cspecs_sub CS CS') ge ge'
  (Gfs: forall i,  sub_option (Genv.find_symbol ge i) (Genv.find_symbol ge' i))
  (Gffp: forall b, sub_option (Genv.find_funct_ptr ge b) (Genv.find_funct_ptr ge' b))
  V G fdecs G1 (H: semax_func V G (C := CS) ge fdecs G1), semax_func V G (C := CS') ge' fdecs G1
                                                                      
| semax_func_app:
  forall cs ge V H funs1 funs2 G1 G2
         (SF1: semax_func V H ge funs1 G1) (SF2: semax_func V H ge funs2 G2)
         (L:length funs1 = length G1),
    semax_func V H ge (funs1 ++ funs2) (G1++G2)
                
| semax_func_subsumption:
  forall cs ge V V' F F'
         (SUB: tycontext_sub (nofunc_tycontext V F) (nofunc_tycontext V F'))
         (HV: forall id, sub_option ((make_tycontext_g V F) !! id) ((make_tycontext_g V' F') !! id)),
  forall funs G (SF: semax_func V F ge funs G),  semax_func V' F' ge funs G
                                                                       
| semax_func_join:
  forall {cs ge V1 H1 V2 H2 V funs1 funs2 G1 G2 H}
  (SF1: semax_func V1 H1 ge funs1 G1) (SF2: semax_func V2 H2 ge funs2 G2)

  (K1: forall i, sub_option ((make_tycontext_g V1 H1) !! i) ((make_tycontext_g V1 H) !! i))
  (K2: forall i, subsumespec ((make_tycontext_s H1) !! i) ((make_tycontext_s H) !! i))
  (K3: forall i, sub_option ((make_tycontext_g V1 H) !! i) ((make_tycontext_g V H) !! i))

  (N1: forall i, sub_option ((make_tycontext_g V2 H2) !! i) ((make_tycontext_g V2 H) !! i))
  (N2: forall i, subsumespec ((make_tycontext_s H2) !! i) ((make_tycontext_s H) !! i))
  (N3: forall i, sub_option ((make_tycontext_g V2 H) !! i) ((make_tycontext_g V H) !! i)),
  semax_func V H ge (funs1 ++ funs2) (G1++G2)
  
| semax_func_firstn:
  forall {cs ge H V n funs G} (SF: semax_func V H ge funs G),
    semax_func V H ge (firstn n funs) (firstn n G)
                
| semax_func_skipn:
  forall {cs ge H V funs G} (HV:list_norepet (map fst funs))
         (SF: semax_func V H ge funs G) n,
    semax_func V H ge (skipn n funs) (skipn n G).

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

Arguments semax _ _ _ _ _ _ _ (_)%I.

Section mpred.

Context `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty} {CS: compspecs}.

Lemma semax_skip_inv: forall E Delta P R,
    semax E Delta P Sskip R ->
    local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ |={E}=> RA_normal R.
Proof.
  intros.
  remember Sskip as c eqn:?H.
  induction H; try solve [inv H0].
  + apply derives_full_refl.
  + specialize (IHsemax H0).
    solve_derives_trans.
  + rewrite IHsemax //.
    by apply fupd_mask_mono.
Qed.

Lemma semax_break_inv: forall E Delta P R,
    semax E Delta P Sbreak R ->
    local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ |={E}=> RA_break R.
Proof.
  intros.
  remember Sbreak as c eqn:?H.
  induction H; try solve [inv H0].
  + apply derives_full_refl.
  + specialize (IHsemax H0).
    solve_derives_trans.
  + rewrite IHsemax //.
    by apply fupd_mask_mono.
Qed.

Lemma semax_continue_inv: forall E Delta P R,
    semax E Delta P Scontinue R ->
    local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ |={E}=> RA_continue R.
Proof.
  intros.
  remember Scontinue as c eqn:?H.
  induction H; try solve [inv H0].
  + apply derives_full_refl.
  + specialize (IHsemax H0).
    solve_derives_trans.
  + rewrite IHsemax //.
    by apply fupd_mask_mono.
Qed.

Lemma semax_return_inv: forall E Delta P ret R,
  semax E Delta P (Sreturn ret) R ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ |={E}=> ((tc_expropt Delta ret (ret_type Delta)) ∧ assert_of (`(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ))).
Proof.
  intros.
  remember (Sreturn ret) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    reduce2ENTAIL.
    apply andp_ENTAIL; [apply ENTAIL_refl |].
    reduce2derives.
    auto.
  + derives_rewrite -> H; clear H.
    derives_rewrite -> (IHsemax H0); clear IHsemax.
    reduceR.
    apply andp_ENTAILL; [by iIntros "(_ & _ & $)"|].
    unfold_lift.
    split => rho; monPred.unseal.
    forget (cast_expropt ret (ret_type Delta) rho) as vl.
    revert rho.
    destruct (H4 vl) as [H].
    revert H; monPred.unseal; eauto.
  + rewrite IHsemax //.
    by apply fupd_mask_mono.
Qed.

Lemma semax_seq_inv: forall E Delta P R h t,
    semax E Delta P (Ssequence h t) R ->
    exists Q, semax E Delta P h (overridePost Q R) /\
              semax E Delta Q t R.
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
    - apply (AuxDefs.semax_conseq _ _ P' (overridePost Q R')); auto.
      * clear.
        destruct R, R'.
        apply derives_full_refl.
      * destruct R, R'; auto.
      * destruct R, R'; auto.
      * destruct R, R'; auto.
    - eapply semax_conseq, H6; auto.
      apply derives_full_refl.
  + destruct IHsemax as (? & ? & ?); first done.
    eexists; split; eapply AuxDefs.semax_mask_mono; eauto.
Qed.

Lemma semax_seq_inv': forall E Delta P R h t,
    semax E Delta P (Ssequence h t) R ->
    semax E Delta P h (overridePost (∃ Q: assert, ⌜semax E Delta Q t R⌝ ∧ Q) R).
Proof.
  intros.
  remember (Ssequence h t) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    clear IHsemax1 IHsemax2.
    eapply semax_post_simple; [.. | exact H].
    - destruct R; unfold overridePost, tycontext.RA_normal.
      iIntros "?"; iExists Q; iFrame; auto.
    - destruct R; done.
    - destruct R; done.
    - intro; destruct R; done.
  + subst c.
    pose proof IHsemax eq_refl. clear IHsemax.
    eapply AuxDefs.semax_conseq; [.. | exact H0]; auto.
    - unfold overridePost, tycontext.RA_normal.
      destruct R' as [R'0 R'1 R'2 R'3] at 1; clear R'0 R'1 R'2 R'3.
      destruct R as [R0 R1 R2 R3] at 1; clear R0 R1 R2 R3.
      reduce2derives.
      apply bi.exist_mono.
      intros Q.
      iIntros "(% & $)"; iPureIntro; split; last done.
      eapply semax_conseq; [.. | apply H6]; auto.
      apply derives_full_refl.
    - destruct R, R'; auto.
    - destruct R, R'; auto.
    - destruct R, R'; auto.
  + eapply AuxDefs.semax_mask_mono; first done.
    eapply AuxDefs.semax_conseq, IHsemax; last done.
    - by iIntros "(_ & _ & $)".
    - destruct R; simpl.
      iIntros "(_ & _ & % & % & ?)".
      iExists Q; iFrame; iPureIntro.
      split; last done.
      eapply AuxDefs.semax_mask_mono; eauto.
    - destruct R; simpl.
      by iIntros "(_ & _ & $)".
    - destruct R; simpl.
      by iIntros "(_ & _ & $)".
    - destruct R; simpl.
      by iIntros (?) "(_ & _ & $)".
Qed.

Lemma semax_assign_inv: forall E Delta e1 e2 P Q,
  semax E Delta P (Sassign e1 e2) Q ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢
     |={E}=>
      ((∃ sh: share, ⌜writable_share sh⌝ ∧
             ▷ (((tc_lvalue Delta e1) ∧ (tc_expr Delta (Ecast e2 (typeof e1))))  ∧
             (assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) ∗
              (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))) -∗ |={E}=> RA_normal Q))))
          ∨ (∃ (t2:type) (ch ch': memory_chunk) (sh: share),
             ⌜(numeric_type (typeof e1) && numeric_type t2)%bool = true /\
                 access_mode (typeof e1) = By_value ch /\
                 access_mode t2 = By_value ch' /\
                 decode_encode_val_ok ch ch' /\
                 writable_share sh⌝ ∧
             ▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)))  ∧
             ((assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1))
                      ∧ assert_of (`(mapsto_ sh t2) (eval_lvalue e1))) ∗
              (∀ v': val,
                 assert_of (`(mapsto sh t2) (eval_lvalue e1) (`v')) -∗
                      (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') )) →
                      (|={E}=> RA_normal Q)))))
       ).
Proof.
  intros.
  remember (Sassign e1 e2) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    reduce2derives.
    apply bi.or_mono.
    - apply bi.exist_mono; intro sh.
      apply bi.and_mono; auto.
      apply bi.later_mono; auto.
      apply bi.and_mono; auto.
      apply bi.sep_mono; auto.
      apply bi.wand_mono; auto.
    - apply bi.exist_mono; intro t2.
      apply bi.exist_mono; intro ch.
      apply bi.exist_mono; intro ch'.
      apply bi.exist_mono; intro sh.
      apply bi.and_mono; auto.
      apply bi.later_mono; auto.
      apply bi.and_mono; auto.
      apply bi.sep_mono; auto.
      apply bi.forall_mono; intros v'.
      apply bi.wand_mono; auto.
      apply bi.impl_mono; auto.
  + subst c.
    derives_rewrite -> H.
    derives_rewrite -> (IHsemax eq_refl).
    reduceR.
    apply orp_ENTAILL.
    - apply exp_ENTAILL; intro sh.
      apply andp_ENTAILL; [reduceLL; apply ENTAIL_refl |].
      apply later_ENTAILL.
      apply andp_ENTAILL; [reduceLL; apply ENTAIL_refl |].
      apply sepcon_ENTAILL; [reduceLL; apply ENTAIL_refl |].
      apply wand_ENTAILL; [reduceLL; apply ENTAIL_refl |].
      apply derives_full_fupd_left, H1.
    - apply exp_ENTAILL; intro t2.
      apply exp_ENTAILL; intro ch.
      apply exp_ENTAILL; intro ch'.
      apply exp_ENTAILL; intro sh.
      apply andp_ENTAILL; [reduceLL; apply ENTAIL_refl |].
      apply later_ENTAILL.
      apply andp_ENTAILL; [reduceLL; apply ENTAIL_refl |].
      apply sepcon_ENTAILL; [reduceLL; apply ENTAIL_refl |].
      apply allp_ENTAILL; intro v'.
      apply wand_ENTAILL; [reduceLL; apply ENTAIL_refl |].
      apply imp_ENTAILL; [reduceLL; apply ENTAIL_refl |].
      apply derives_full_fupd_left, H1.
  + iIntros "H".
    iMod (fupd_mask_subseteq E') as "Hmask".
    iMod (IHsemax with "H") as "H".
    iMod "Hmask" as "_"; iIntros "!>".
    iDestruct "H" as "[(% & % & H) | (% & % & % & % & % & H)]"; [iLeft | iRight].
    - iExists _; iSplit; first done.
      rewrite fupd_mask_mono //.
    - iExists _, _, _, _; iSplit; first done.
      iNext; iApply (bi.and_mono with "H"); first done.
      iIntros "($ & ?)" (?).
      rewrite -(fupd_mask_mono E' E) //.
Qed.

Lemma tc_fn_return_temp_guard_opt: forall ret retsig Delta,
  tc_fn_return Delta ret retsig ->
  temp_guard_opt Delta ret.
Proof.
  intros.
  destruct ret; hnf in H |- *; [destruct ((temp_types Delta) !! i) |]; auto; congruence.
Qed.

Lemma oboxopt_ENTAILL: forall Delta ret retsig P Q,
  tc_fn_return Delta ret retsig ->
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ Q) ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ oboxopt Delta ret P) ⊢ oboxopt Delta ret Q.
Proof.
  intros.
  apply oboxopt_left2'; auto.
  eapply tc_fn_return_temp_guard_opt; eauto.
Qed.

Lemma semax_call_inv: forall E Delta ret a bl Pre Post,
  semax E Delta Pre (Scall ret a bl) Post ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ Pre) ⊢ |={E}=>
         (∃ argsig: _, ∃ retsig: _, ∃ cc: _,
          ∃ Ef, ∃ A: _, ∃ P: _, ∃ Q: _, ∃ x: _,
         ⌜Ef ⊆ E /\ Cop.classify_fun (typeof a) =
             Cop.fun_case_f (typelist_of_type_list argsig) retsig cc /\
             (retsig = Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig⌝ ∧
          ((*▷*)((tc_expr Delta a) ∧ (tc_exprlist Delta argsig bl)))  ∧
         assert_of (`(func_ptr (mk_funspec (argsig,retsig) cc Ef A P Q)) (eval_expr a)) ∗
          ▷(assert_of (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho)) ∗ oboxopt Delta ret (maybe_retval (assert_of (Q x)) retsig ret -∗ |={E}=> RA_normal Post))).
Proof.
  intros.
  remember (Scall ret a bl) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    reduce2derives.
    apply bi.exist_mono; intro argsig.
    apply bi.exist_mono; intro retsig.
    apply bi.exist_mono; intro cc.
    apply bi.exist_mono; intro Ef.
    apply bi.exist_mono; intro A.
    apply bi.exist_mono; intro P.
    apply bi.exist_mono; intro Q.
    apply bi.exist_mono; intro x.
    apply bi.and_mono; auto.
    apply bi.and_mono; auto.
    apply bi.sep_mono; auto.
    apply bi.later_mono; auto.
    apply bi.sep_mono; auto.
    apply oboxopt_K; auto.
    apply bi.wand_mono; auto.
  + subst c.
    rename P into Pre, R into Post.
    derives_rewrite -> H.
    derives_rewrite -> (IHsemax eq_refl); clear IHsemax.
    reduceR.
    apply exp_ENTAILL; intro argsig.
    apply exp_ENTAILL; intro retsig.
    apply exp_ENTAILL; intro cc.
    apply exp_ENTAILL; intro Ef.
    apply exp_ENTAILL; intro A.
    apply exp_ENTAILL; intro P.
    apply exp_ENTAILL; intro Q.
    apply exp_ENTAILL; intro x.
    iIntros "(#? & #? & (% & % & % & %) & H)"; iSplit; first done.
    iSplit; first rewrite bi.and_elim_l //; rewrite bi.and_elim_r.
    iDestruct "H" as "($ & H)".
    iNext; iDestruct "H" as "($ & H)".
    iApply oboxopt_ENTAILL; last by iFrame; iSplit.
    apply wand_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    apply derives_full_fupd_left, H1.
  + iIntros "H".
    iMod (fupd_mask_subseteq E') as "Hmask".
    iMod (IHsemax with "H") as (????????) "((% & %) & H)".
    iMod "Hmask" as "_"; iIntros "!>".
    iExists _, _, _, Ef, _, _, _, _; iSplit.
    { iPureIntro; split; [set_solver | done]. }
    rewrite oboxopt_K // fupd_mask_mono //.
Qed.

Lemma typecheck_expr_sound' : forall Delta e, local (typecheck_environ Delta) ∧ tc_expr Delta e ⊢ local ((`(tc_val (typeof e))) (eval_expr e)).
Proof.
  intros; split => rho; monPred.unseal.
  iIntros "(% & ?)"; by iApply typecheck_expr_sound.
Qed.

Lemma semax_Sset_inv: forall E Delta P R id e,
  semax E Delta P (Sset id e) R ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ |={E}=>
    ((((▷ ((tc_expr Delta e) ∧
             (tc_temp_id id (typeof e) Delta e) ∧
             assert_of (subst id (eval_expr e) (|={E}=> RA_normal R)))) ∨
      (∃ cmp: Cop.binary_operation, ∃ e1: expr, ∃ e2: expr,
         ∃ ty: type, ∃ sh1: share, ∃ sh2: share,
          ⌜e = Ebinop cmp e1 e2 ty /\
              sh1 ≠ Share.bot /\ sh2 ≠ Share.bot /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true⌝ ∧
            ( ▷ ((tc_expr Delta e1) ∧
              (tc_expr Delta e2)  ∧
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) ∧
          (<absorb> assert_of (`(mapsto_ sh1 (typeof e1)) (eval_expr e1))) ∧
          (<absorb> assert_of (`(mapsto_ sh2 (typeof e2)) (eval_expr e2))) ∧
          assert_of (subst id (eval_expr (Ebinop cmp e1 e2 ty)) (|={E}=> RA_normal R)))))) ∨
      (∃ sh: share, ∃ t2: type, ∃ v2: val,
              ⌜typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e) t2 = true /\
                  readable_share sh⌝ ∧
         ▷ (( (tc_lvalue Delta e) ∧
              ⌜tc_val (typeof e) v2⌝ ∧
              (<absorb> assert_of (`(mapsto sh (typeof e)) (eval_lvalue e) (`v2)))) ∧
              assert_of (subst id (`v2) (|={E}=> RA_normal R)))))) ∨
      (∃ sh: share, ∃ e1: expr, ∃ t1: type, ∃ v2: val,
              ⌜e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh⌝ ∧
         ▷ ( (tc_lvalue Delta e1) ∧
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) ∧
              (<absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ∧
              assert_of (subst id (`(force_val (sem_cast (typeof e1) t1 v2))) (|={E}=> RA_normal R)))).
Proof.
  intros.
  remember (Sset id e) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    reduce2derives.
    apply bi.or_mono; [apply bi.or_mono; [apply bi.or_mono |] |].
    - apply bi.later_mono.
      apply bi.and_mono; auto.
      apply bi.and_mono; auto.
      apply subst_derives.
      apply fupd_intro.
    - apply bi.exist_mono; intros cmp.
      apply bi.exist_mono; intros e1.
      apply bi.exist_mono; intros e2.
      apply bi.exist_mono; intros ty.
      apply bi.exist_mono; intros sh1.
      apply bi.exist_mono; intros sh2.
      apply bi.and_mono; auto.
      apply bi.later_mono; auto.
      apply bi.and_mono; auto.
      apply bi.and_mono; auto.
      apply bi.and_mono; auto.
      apply bi.and_mono; auto.
      apply bi.and_mono; auto.
      apply subst_derives.
      apply fupd_intro.
    - apply bi.exist_mono; intros sh.
      apply bi.exist_mono; intros t2.
      apply bi.exist_mono; intros v2.
      apply bi.and_mono; auto.
      apply bi.later_mono, bi.and_mono; auto.
      apply subst_derives.
      apply fupd_intro.
    - apply bi.exist_mono; intros sh.
      apply bi.exist_mono; intros e1.
      apply bi.exist_mono; intros t1.
      apply bi.exist_mono; intros v2.
      apply bi.and_mono; auto.
      apply bi.later_mono.
      apply bi.and_mono; auto.
      apply bi.and_mono; auto.
      apply bi.and_mono; auto.
      apply subst_derives.
      apply fupd_intro.
  + subst c.
    rename P into Pre, R into Post.
    derives_rewrite -> H.
    derives_rewrite -> (IHsemax eq_refl); clear IHsemax.
    reduceR.
    apply orp_ENTAILL; [apply orp_ENTAILL; [apply orp_ENTAILL |] |].
    - apply later_ENTAILL.
      unfold tc_temp_id, typecheck_temp_id.
      destruct ((temp_types Delta) !! id) eqn:Hid; last by rewrite denote_tc_assert_False; iIntros "(? & ? & _ & [] & _)".
      rewrite !bi.and_assoc.
      eapply andp_subst_ENTAILL; [eauto | | reduceLL; apply ENTAIL_refl |].
      * destruct (is_neutral_cast (implicit_deref (typeof e)) t) eqn:Ht; [|normalize; iIntros "(_ & _ & _ & [])"].
        split => rho; rewrite /local /lift1; monPred.unseal; unfold_lift.
        iIntros "(% & _ & H & _)".
        iPoseProof (typecheck_expr_sound with "H") as "%"; iPureIntro.
        eapply tc_val_tc_val', expr2.neutral_cast_subsumption'; eauto.
      * apply derives_full_fupd_left.
        auto.
    - apply exp_ENTAILL; intro cmp.
      apply exp_ENTAILL; intro e1.
      apply exp_ENTAILL; intro e2.
      apply exp_ENTAILL; intro ty.
      apply exp_ENTAILL; intro sh1.
      apply exp_ENTAILL; intro sh2.
      iIntros "(? & ? & (%He & % & % & % & % & % & %Ht) & H)"; iSplit; first done.
      iNext; iStopProof.
      unfold typecheck_tid_ptr_compare in Ht.
      destruct ((temp_types Delta) !! id) eqn:Hid; last done.
      rewrite -bi.persistent_and_affinely_sep_l !assoc; eapply andp_subst_ENTAILL; first done.
      * split => rho; rewrite /local /lift1; monPred.unseal; unfold_lift; apply bi.pure_intro.
        replace (sem_binary_operation' cmp) with (sem_cmp (expr.op_to_cmp cmp)); [| destruct cmp; inv H7; auto].
        apply binop_lemmas2.tc_val'_sem_cmp; auto.
      * iIntros "(_ & _ & $)".
      * iIntros "(? & ? & >?)"; iApply H1; iFrame.
    - apply exp_ENTAILL; intro sh.
      apply exp_ENTAILL; intro t2.
      apply exp_ENTAILL; intro v2.
      iIntros "(? & ? & (%Ht & % & %) & H)"; iSplit; first done.
      iNext; iStopProof.
      unfold typeof_temp in Ht.
      destruct ((temp_types Delta) !! id) eqn:Hid; inv Ht.
      rewrite -bi.persistent_and_affinely_sep_l !assoc; eapply andp_subst_ENTAILL; first done.
      * split => rho; rewrite /local /lift1; monPred.unseal; unfold_lift.
        iIntros "(% & _ & (_ & %) & _)"; iPureIntro.
        eapply tc_val_tc_val', neutral_cast_subsumption; eauto.
      * iIntros "(_ & _ & $)".
      * iIntros "(? & ? & >?)"; iApply H1; iFrame.
    - apply exp_ENTAILL; intro sh.
      apply exp_ENTAILL; intro e1.
      apply exp_ENTAILL; intro t1.
      apply exp_ENTAILL; intro t2.
      iIntros "(? & ? & (%He & %Ht & %) & H)"; iSplit; first done.
      iNext; iStopProof.
      unfold typeof_temp in Ht.
      destruct ((temp_types Delta) !! id) eqn:Hid; inv Ht.
      rewrite -bi.persistent_and_affinely_sep_l !assoc; eapply andp_subst_ENTAILL; first done.
      * split => rho; rewrite /local /lift1; monPred.unseal; unfold_lift.
        iIntros "(% & _ & (_ & %) & _)"; iPureIntro.
        apply tc_val_tc_val'; auto.
      * iIntros "(_ & _ & $)".
      * iIntros "(? & ? & >?)"; iApply H1; iFrame.
  + iIntros "H".
    iMod (fupd_mask_subseteq E') as "Hmask".
    iMod (IHsemax with "H") as "H".
    iMod "Hmask" as "_"; iIntros "!>".
    iDestruct "H" as "[[[H | H] | H] | H]"; [iLeft; iLeft; iLeft | iLeft; iLeft; iRight | iLeft; iRight | iRight].
    - rewrite subst_extens // fupd_mask_mono //.
    - iDestruct "H" as (??????) "H"; iExists _, _, _, _, _, _; rewrite subst_extens // fupd_mask_mono //.
    - iDestruct "H" as (???) "H"; iExists _, _, _; rewrite subst_extens // fupd_mask_mono //.
    - iDestruct "H" as (????) "H"; iExists _, _, _, _; rewrite subst_extens // fupd_mask_mono //.
Qed.

Lemma semax_Sbuiltin_inv: forall E Delta P R opt ext tl el,
  semax E Delta P (Sbuiltin opt ext tl el) R -> local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ |={E}=> False.
Proof.
  intros.
  remember (Sbuiltin opt ext tl el) as c eqn:?H.
  induction H; try solve [inv H0].
  + reduceL; apply False_left.
  + derives_rewrite -> H.
    derives_rewrite -> (IHsemax H0).
    reduceL; apply False_left.
  + rewrite -fupd_mask_mono //; auto.
Qed.

Lemma semax_Slabel_inv: forall E Delta P R l c,
  semax E Delta P (Slabel l c) R -> semax E Delta P c R.
Proof.
  intros.
  remember (Slabel l c) as c0 eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    apply H.
  + specialize (IHsemax H0).
    eapply semax_conseq; eauto.
  + eapply AuxDefs.semax_mask_mono; eauto.
    by apply IHsemax.
Qed.

Lemma semax_Sgoto_inv: forall E Delta P R l,
  semax E Delta P (Sgoto l) R -> local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢ |={E}=> False.
Proof.
  intros.
  remember (Sgoto l) as c eqn:?H.
  induction H; try solve [inv H0].
  + reduceL; apply False_left.
  + derives_rewrite -> H.
    derives_rewrite -> (IHsemax H0).
    reduceL; apply False_left.
  + rewrite -fupd_mask_mono //; auto.
Qed.

Lemma semax_ifthenelse_inv: forall E Delta P R b c1 c2,
  semax E Delta P (Sifthenelse b c1 c2) R ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢
  |={E}=> (⌜bool_type (typeof b) = true⌝ ∧ ▷ (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) ∧
  (∃ P': assert,
  ⌜semax E Delta (P' ∧ local (`(typed_true (typeof b)) (eval_expr b))) c1 R /\
      semax E Delta (P' ∧ local (`(typed_false (typeof b)) (eval_expr b))) c2 R⌝ ∧
  P'))).
Proof.
  intros.
  remember (Sifthenelse b c1 c2) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0; clear IHsemax1 IHsemax2.
    reduce2derives.
    apply bi.and_mono; auto.
    apply bi.later_mono.
    apply bi.and_mono; auto.
  + derives_rewrite -> H.
    derives_rewrite -> (IHsemax H0); clear IHsemax.
    reduce2derives.
    apply bi.and_mono; auto.
    apply bi.later_mono.
    apply bi.and_mono; auto.
    apply bi.exist_mono; intros P''.
    iIntros "((%Htrue & %Hfalse) & $)"; iPureIntro; split; last done.
    split; [eapply semax_conseq, Htrue | eapply semax_conseq, Hfalse]; eauto; apply derives_full_refl.
  + iIntros "H".
    iMod (fupd_mask_subseteq E') as "Hmask".
    iMod (IHsemax with "H") as "(% & H)".
    iMod "Hmask" as "_"; iIntros "!>"; iSplit; first done.
    iNext; iApply (bi.and_mono with "H"); first done.
    iIntros "H"; iDestruct "H" as (?) "((% & %) & H)".
    iExists P'; iSplit; last done.
    iPureIntro; split; eapply AuxDefs.semax_mask_mono; eauto.
Qed.

Lemma semax_loop_inv: forall E Delta P R body incr,
  semax E Delta P (Sloop body incr) R ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢
  |={E}=> ∃ Q: assert, ∃ Q': assert,
  ⌜semax E Delta Q body (loop1_ret_assert Q' R) /\
      semax E Delta Q' incr (loop2_ret_assert Q R)⌝ ∧
  Q.
Proof.
  intros.
  remember (Sloop body incr) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0; clear IHsemax1 IHsemax2.
    reduce2derives.
    iIntros "Q"; iExists Q, Q'; iFrame; auto.
  + derives_rewrite -> H.
    derives_rewrite -> (IHsemax H0); clear IHsemax.
    reduce2derives.
    apply bi.exist_mono; intros Q.
    apply bi.exist_mono; intros Q'.
    iIntros "((%Hs1 & %Hs2) & $)"; iPureIntro; split; last done.
    split.
    - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR']; simpl in Hs1, Hs2 |- *.
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
    - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR']; simpl in Hs1, Hs2 |- *.
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
  + iIntros "H".
    iMod (fupd_mask_subseteq E') as "Hmask".
    iMod (IHsemax with "H") as (??) "((% & %) & H)".
    iMod "Hmask" as "_"; iIntros "!>".
    iExists Q, Q'; iSplit; last done.
    iPureIntro; split; eapply AuxDefs.semax_mask_mono; eauto.
Qed.

Lemma semax_switch_inv: forall E Delta P R a sl,
  semax E Delta P (Sswitch a sl) R ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢
        |={E}=> ⌜is_int_type (typeof a) = true⌝ ∧ (tc_expr Delta a) ∧
        ∃ P': assert,
  ⌜forall n,
     semax E Delta 
               (local ((liftx eq) (eval_expr a) `(Vint n)) ∧ P')
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)⌝ ∧ P'.
Proof.
  intros.
  remember (Sswitch a sl) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    reduce2derives.
    apply bi.and_mono; auto.
    apply bi.and_intro; first done.
    iIntros "?"; iExists Q; iFrame; auto.
  + derives_rewrite -> H.
    derives_rewrite -> (IHsemax H0); clear IHsemax.
    reduce2derives.
    apply bi.and_mono; auto.
    apply bi.and_mono; auto.
    apply bi.exist_mono; intros P''.
    iIntros "(% & $)"; iPureIntro; split; last done.
    intro n; specialize (H6 n).
    eapply semax_conseq; [.. | exact H6].
    - apply derives_full_refl.
    - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR'].
      reduce2derives; apply False_left.
    - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR'].
      exact H1.
    - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR'].
      exact H3.
    - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR'].
      exact H4.
  + iIntros "H".
    iMod (fupd_mask_subseteq E') as "Hmask".
    iMod (IHsemax with "H") as "(% & H)".
    iMod "Hmask" as "_"; iIntros "!>"; iSplit; first done.
    iApply (bi.and_mono with "H"); first done.
    iIntros "H"; iDestruct "H" as (?) "(%HE' & ?)".
    iExists P'; iSplit; last done.
    iPureIntro; intros; eapply AuxDefs.semax_mask_mono, HE'; auto.
Qed.

End mpred.

Module Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := CSHL_Def.

Module CSHL_Def := CSHL_Def.
Import CSHL_Def.

Lemma semax_extract_exists:
  forall `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty} {CS: compspecs},
  forall (A : Type) (P : A -> assert) c E (Delta: tycontext) (R: ret_assert),
  (forall x, semax E Delta (P x) c R) ->
   semax E Delta (∃ x:A, P x) c R.
Proof.
  intros.
  revert A P R H; induction_stmt c; intros.
  + pose proof (fun x => semax_skip_inv _ _ _ _ (H x)).
    eapply (semax_conseq _ _ (RA_normal R)).
    - iIntros "(? & ? & % & ?)"; iApply H0; iFrame.
    - apply derives_full_refl.
    - apply derives_full_refl.
    - apply derives_full_refl.
    - intros; iIntros "(_ & _ & $)".
    - eapply semax_post''; [.. | apply AuxDefs.semax_skip].
      apply ENTAIL_refl.
  + pose proof (fun x => semax_assign_inv _ _ _ _ _ _ (H x)).
    clear H.
    apply bi.exist_elim in H0.
    rewrite -bi.and_exist_l -bi.sep_exist_l in H0.
    eapply semax_conseq; [exact H0 | intros; try apply derives_full_refl .. | clear H0 ].
    { iIntros "(_ & _ & $)". }
    eapply semax_conseq; [apply derives_full_refl | .. | apply AuxDefs.semax_store_store_union_hack_backward].
    - reduceL. done.
    - reduceL. apply False_left.
    - reduceL. apply False_left.
    - intros; reduceL. apply False_left.
  + pose proof (fun x => semax_Sset_inv _ _ _ _ _ _ (H x)).
    clear H.
    apply bi.exist_elim in H0.
    rewrite -bi.and_exist_l -bi.sep_exist_l in H0.
    eapply semax_conseq; [exact H0 | intros; try apply derives_full_refl .. | clear H0 ].
    { iIntros "(_ & _ & $)". }
    eapply semax_conseq; [apply derives_full_refl | .. | apply AuxDefs.semax_set_ptr_compare_load_cast_load_backward].
    - reduceL. done.
    - reduceL. apply False_left.
    - reduceL. apply False_left.
    - intros; reduceL. apply False_left.
  + pose proof (fun x => semax_call_inv _ _ _ _ _ _ _ (H x)).
    clear H.
    apply bi.exist_elim in H0.
    rewrite -bi.and_exist_l -bi.sep_exist_l in H0.
    eapply semax_conseq; [exact H0 | intros; try apply derives_full_refl .. | clear H0 ].
    { iIntros "(_ & _ & $)". }
    eapply semax_conseq; [apply derives_full_refl | .. | apply AuxDefs.semax_call_backward].
    - reduceL. done.
    - reduceL. apply False_left.
    - reduceL. apply False_left.
    - intros; reduceL. apply False_left.
  + pose proof (fun x => semax_Sbuiltin_inv _ _ _ _ _ _ _ _ (H x)).
    eapply semax_conseq; [| intros; try apply derives_full_refl .. | apply AuxDefs.semax_builtin].
    rewrite bi.sep_exist_l bi.and_exist_l.
    apply bi.exist_elim; intros x; specialize (H0 x).
    auto.
    { iIntros "(_ & _ & $)". }
  + apply AuxDefs.semax_seq with (∃ Q: assert, ⌜semax E Delta Q c2 R⌝ ∧ Q).
    - apply IHc1.
      intro x.
      apply semax_seq_inv'; auto.
    - apply IHc2.
      intros Q.
      apply semax_pre with (∃ H0: semax E Delta Q c2 R, Q).
      * iIntros "(_ & % & ?)".
        iExists H0; auto.
      * apply IHc2; auto.
  + eapply semax_conseq; [| intros; try apply derives_full_refl .. | apply (AuxDefs.semax_ifthenelse _ _ (∃ P': assert, ⌜semax E Delta (P' ∧ local (`(typed_true (typeof e)) (eval_expr e)))%I c1 R /\ semax E Delta (P' ∧ local (`(typed_false (typeof e)) (eval_expr e)))%I c2 R⌝ ∧ P'))].
    - pose proof (fun x => semax_ifthenelse_inv _ _ _ _ _ _ _ (H x)).
      clear H.
      apply bi.exist_elim in H0.
      rewrite -bi.and_exist_l -bi.sep_exist_l in H0.
      exact H0.
    - iIntros "(_ & _ & $)".
    - apply semax_pre with (∃ P': assert, ∃ H0: semax E Delta (P' ∧ local ((` (typed_true (typeof e))) (eval_expr e))) c1 R, P' ∧ local ((` (typed_true (typeof e))) (eval_expr e))).
      * rewrite bi.and_elim_r bi.and_exist_r; apply bi.exist_mono; intros.
        rewrite -assoc; iIntros "((% & %) & $)"; eauto.
      * auto.
    - apply semax_pre with (∃ P': assert, ∃ H0: semax E Delta (P' ∧ local ((` (typed_false (typeof e))) (eval_expr e))) c2 R, P' ∧ local ((` (typed_false (typeof e))) (eval_expr e))).
      * rewrite bi.and_elim_r bi.and_exist_r; apply bi.exist_mono; intros.
        rewrite -assoc; iIntros "((% & %) & $)"; eauto.
      * auto.
  + pose proof (fun x => semax_loop_inv _ _ _ _ _ _ (H x)).
    eapply (AuxDefs.semax_conseq _ _
      (∃ Q : assert, ∃ Q' : assert,
         ∃ H: semax E Delta Q c1 (loop1_ret_assert Q' R),
           ∃ H0: semax E Delta Q' c2 (loop2_ret_assert Q R), Q));
    [| intros; try apply derives_full_refl .. |].
    { rewrite bi.sep_exist_l bi.and_exist_l.
      apply bi.exist_elim; intros x.
      derives_rewrite -> (H0 x).
      reduce2derives.
      apply bi.exist_mono; intros Q.
      apply bi.exist_mono; intros Q'.
      iIntros "((% & %) & $)"; eauto. }
    { iIntros "(_ & _ & $)". }
    apply (AuxDefs.semax_loop _ _ _
      (∃ Q : assert, ∃ Q' : assert,
         ∃ H: semax E Delta Q c1 (loop1_ret_assert Q' R),
           ∃ H0: semax E Delta Q' c2 (loop2_ret_assert Q R), Q')).
    - apply IHc1.
      intros Q.
      apply IHc1.
      intros Q'.
      apply IHc1.
      intros H1.
      apply IHc1.
      intros H2.
      eapply semax_post_simple; [.. | exact H1].
      * destruct R as [nR bR cR rR].
        iIntros; iExists Q, Q', H1, H2; done.
      * destruct R as [nR bR cR rR]; done.
      * destruct R as [nR bR cR rR].
        iIntros; iExists Q, Q', H1, H2; done.
      * intros.
        destruct R as [nR bR cR rR]; done.
    - apply IHc2.
      intros Q.
      apply IHc2.
      intros Q'.
      apply IHc2.
      intros H1.
      apply IHc2.
      intros H2.
      eapply semax_post_simple; [.. | exact H2].
      * destruct R as [nR bR cR rR].
        iIntros; iExists Q, Q', H1, H2; done.
      * destruct R as [nR bR cR rR]; done.
      * destruct R as [nR bR cR rR]; done.
      * intros.
        destruct R as [nR bR cR rR]; done.
  + pose proof (fun x => semax_break_inv _ _ _ _ (H x)).
    eapply semax_conseq; [| intros; try apply derives_full_refl .. |].
    - rewrite bi.sep_exist_l bi.and_exist_l; apply bi.exist_elim.
      intro x; apply H0.
    - iIntros "(_ & _ & $)".
    - apply AuxDefs.semax_break.
  + pose proof (fun x => semax_continue_inv _ _ _ _ (H x)).
    eapply semax_conseq; [| intros; try apply derives_full_refl .. |].
    - rewrite bi.sep_exist_l bi.and_exist_l; apply bi.exist_elim.
      intro x; apply H0.
    - iIntros "(_ & _ & $)".
    - apply AuxDefs.semax_continue.
  + pose proof (fun x => semax_return_inv _ _ _ _ _ (H x)).
    eapply (semax_conseq _ _ _ {| RA_normal := _; RA_break := _; RA_continue := _; RA_return := RA_return R |} ); [.. | apply AuxDefs.semax_return].
    - rewrite bi.sep_exist_l bi.and_exist_l.
      apply bi.exist_elim; intros x.
      derives_rewrite -> (H0 x).
      apply derives_full_refl.
    - apply derives_full_refl.
    - apply derives_full_refl.
    - apply derives_full_refl.
    - intros; unfold RA_return at 1. iIntros "(_ & _ & $)".
  + pose proof (fun x => semax_switch_inv _ _ _ _ _ _ (H x)).
    eapply semax_conseq; [| intros; try apply derives_full_refl .. |].
    - rewrite bi.sep_exist_l bi.and_exist_l; apply bi.exist_elim.
      intro x; apply H0.
    - iIntros "(_ & _ & $)".
    - apply AuxDefs.semax_switch; [intros; simpl; solve_andp |].
      intros.
      specialize (IH (Int.unsigned n)).
      apply semax_pre with (∃ P': assert, ∃ H: forall n0 : int,
           semax E Delta (local ((` eq) (eval_expr e) (` (Vint n0))) ∧ P')
             (seq_of_labeled_statement (select_switch (Int.unsigned n0) l))
             (switch_ret_assert R), local ((` eq) (eval_expr e) (` (Vint n))) ∧ P').
      * iIntros "(_ & #? & _ & % & %H1 & ?)"; iExists P', H1; eauto.
      * auto.
  + pose proof (fun x => semax_Slabel_inv _ _ _ _ _ _ (H x)).
    apply AuxDefs.semax_label.
    apply IHc.
    auto.
  + pose proof (fun x => semax_Sgoto_inv _ _ _ _ _ (H x)).
    eapply semax_conseq; [| intros; try apply derives_full_refl .. | apply AuxDefs.semax_goto].
    rewrite bi.sep_exist_l bi.and_exist_l.
    apply bi.exist_elim; intros x; specialize (H0 x).
    auto.
    { iIntros "(_ & _ & $)". }
Qed.

End Extr.

Module ExtrFacts := GenExtrFacts (CSHL_Def) (Conseq) (Extr).
Module ExtrIFacts := GenIExtrFacts (CSHL_Def) (CConseq) (Extr).

Import Extr ExtrFacts ExtrIFacts.

Module DeepEmbeddedMinimumSeparationLogic <: MINIMUM_CLIGHT_SEPARATION_HOARE_LOGIC with Module CSHL_Def := DeepEmbeddedDef.

Module CSHL_Def := DeepEmbeddedDef.

Module CSHL_Defs := DeepEmbeddedDefs.

Lemma semax_mask_mono : forall `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty} {CS : compspecs} E E' Delta P c R,
  E ⊆ E' -> semax _ _ _ _ _ E Delta P c R -> semax _ _ _ _ _ E' Delta P c R.
Proof.
  intros; eapply AuxDefs.semax_mask_mono; eauto.
Qed.

Definition semax_extract_exists := @semax_extract_exists.

Definition semax_func_nil := @AuxDefs.semax_func_nil (@Def.semax_external).

Definition semax_func_cons := @AuxDefs.semax_func_cons (@Def.semax_external).

Definition semax_func_cons_ext := @AuxDefs.semax_func_cons_ext (@Def.semax_external).

Section mpred.

Context `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty} {CS: compspecs}.

Theorem semax_ifthenelse :
   forall E Delta P (b: expr) c d R,
      bool_type (typeof b) = true ->
     semax _ _ _ _ _ E Delta (P ∧ local (`(typed_true (typeof b)) (eval_expr b))) c R ->
     semax _ _ _ _ _ E Delta (P ∧ local (`(typed_false (typeof b)) (eval_expr b))) d R ->
     semax _ _ _ _ _ E Delta (▷ (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) ∧ P)) (Sifthenelse b c d) R.
Proof.
  intros.
  eapply semax_pre_simple, @AuxDefs.semax_ifthenelse; eauto.
Qed.

Definition semax_seq := @AuxDefs.semax_seq.

Definition semax_break := @AuxDefs.semax_break.

Definition semax_continue := @AuxDefs.semax_continue.

Definition semax_loop := @AuxDefs.semax_loop.

Theorem semax_switch: 
  forall E Delta (Q: assert) a sl R,
     is_int_type (typeof a) = true ->
     (Q ⊢ tc_expr Delta a) ->
     (forall n,
     semax _ _ _ _ _ E Delta (local ((` eq) (eval_expr a) `( Vint n)) ∧ Q)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) ->
     semax _ _ _ _ _ E Delta Q (Sswitch a sl) R.
Proof.
  intros.
  eapply semax_pre_simple, @AuxDefs.semax_switch; eauto.
  normalize.
Qed.

End mpred.

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

Module Sassign: CLIGHT_SEPARATION_HOARE_LOGIC_SASSIGN_BACKWARD with Module CSHL_Def := DeepEmbeddedDef.

Module CSHL_Def := DeepEmbeddedDef.

Definition semax_store_store_union_hack_backward := @AuxDefs.semax_store_store_union_hack_backward.

End Sassign.

Module StoreUnionHackB := Sassign2StoreUnionHack (DeepEmbeddedDef) (Conseq) (Sassign).

Module StoreUnionHackF := StoreUnionHackB2F (DeepEmbeddedDef) (Conseq) (StoreUnionHackB).

Definition semax_store_union_hack := @StoreUnionHackF.semax_store_union_hack_forward.

Module StoreB := Sassign2Store (DeepEmbeddedDef) (Conseq) (Sassign).

Module StoreF := StoreB2F (DeepEmbeddedDef) (Conseq) (StoreB).

Definition semax_store := @StoreF.semax_store_forward.

Definition semax_skip := @AuxDefs.semax_skip.

Definition semax_conseq := @AuxDefs.semax_conseq.

Definition semax_Slabel := @AuxDefs.semax_label.

Definition semax_ext := @MinimumLogic.semax_ext.

Definition semax_external_FF := @MinimumLogic.semax_external_FF.
Definition semax_external_funspec_sub := @MinimumLogic.semax_external_funspec_sub.
Definition semax_external_binaryintersection := @MinimumLogic.semax_external_binaryintersection.
Definition general_intersection_funspec_subIJ:= @MinimumLogic.general_intersection_funspec_subIJ.

Section mpred.

Context `{!VSTGS OK_ty Σ}.

Definition semax_body_binaryintersection:
forall {CS: compspecs} {V G} f sp1 sp2 phi
  (SB1: semax_body V G f sp1) (SB2: semax_body V G f sp2)
  (BI: binary_intersection (snd sp1) (snd sp2) = Some phi),
  semax_body V G f (fst sp1, phi).
Proof. intros.
  destruct sp1 as [i phi1]. destruct phi1 as [sig1 cc1 E1 A1 P1 Q1].
  destruct sp2 as [i2 phi2]. destruct phi2 as [sig2 cc2 E2 A2 P2 Q2].
  destruct phi as [sig cc E A P Q]. simpl snd in BI.
  simpl in BI.
  if_tac in BI; [inv H | discriminate]. if_tac in BI; [| discriminate]. if_tac in BI; [| discriminate].
  apply Some_inj, mk_funspec_inj in BI as ([=] & ? & ? & ? & ? & ?); subst.
  clear - SB1 SB2.
  destruct SB1 as [X [X1 SB1]]; destruct SB2 as [_ [X2 SB2]].
  split3; [ apply X | trivial | simpl in X; intros ].
  destruct x as [[|] ?]; [ apply SB1 | apply SB2].
Qed.

Definition semax_body_generalintersection {V G cs f iden I sig cc E} {phi : I -> funspec}
        (H1: forall i : I, typesig_of_funspec (phi i) = sig)
        (H2: forall i : I, callingconvention_of_funspec (phi i) = cc)
        (HE: forall i, mask_of_funspec (phi i) = E) (HI: inhabited I)
  (H: forall i, semax_body(C := cs) V G f (iden, phi i)):
  semax_body V G f (iden, @general_intersection _ I sig cc E phi H1 H2 HE).
Proof. destruct HI. split3.
  { specialize (H X). specialize (H1 X); subst. destruct (phi X). simpl. apply H. }
  { specialize (H X). specialize (H1 X); subst. destruct (phi X). simpl. apply H. }
  intros. destruct x as [i Hi].
  specialize (H i).
  assert (fst sig = map snd (fst (fn_funsig f)) /\
        snd sig = snd (fn_funsig f) /\
        (forall (x : dtfr ((WithType_of_funspec (phi i)))),
         semax E (func_tycontext f V G nil)
           (close_precondition (map fst (fn_params f)) (argsassert_of ((Pre_of_funspec (phi i)) x)) ∗ stackframe_of f) 
           (fn_body f) (frame_ret_assert (function_body_ret_assert (fn_return f) (assert_of ((Post_of_funspec (phi i)) x))) (stackframe_of f)))) as HH.
  { intros. specialize (H1 i); specialize (H2 i). specialize (HE i). subst. unfold semax_body in H.
    destruct (phi i); subst. destruct H as [? [? ?]]. split3; auto. }
  clear H H1 H2. destruct HH as [HH1 [HH2 HH3]].
  apply (HH3 Hi).
Qed.

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
  destruct ((temp_types Delta) !! i), ((temp_types Delta') !! i); auto.
  + subst; auto.
  + tauto.
Qed.

Lemma obox_sub:
  forall (Delta Delta' : tycontext) id P rho,
    tycontext_sub Delta Delta' ->
    temp_guard Delta id ->
    tc_environ Delta rho ->
    obox Delta id P rho ⊢ obox Delta' id P rho.
Proof.
  intros.
  unfold obox.
  destruct H as [? _].
  specialize (H id).
  hnf in H0.
  destruct ((temp_types Delta) !! id), ((temp_types Delta') !! id); auto.
  + subst; auto.
  + tauto.
  + tauto.
Qed.

Lemma oboxopt_sub:
  forall (Delta Delta' : tycontext) id P rho,
    tycontext_sub Delta Delta' ->
    temp_guard_opt Delta id ->
    tc_environ Delta rho ->
    oboxopt Delta id P rho ⊢ oboxopt Delta' id P rho.
Proof.
  intros.
  destruct id.
  + eapply obox_sub; eauto.
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
  destruct ((temp_types Delta) !! id), ((temp_types Delta') !! id); auto.
  + subst; auto.
  + inv H0.
Qed.

Lemma allp_fun_id_sub: forall Delta Delta',
  tycontext_sub Delta Delta' ->
  allp_fun_id Delta' ⊢ allp_fun_id Delta.
Proof.
  intros.
  split => rho.
  apply Clight_assert_lemmas.allp_fun_id_sub; auto.
Qed.

Theorem semax_Delta_subsumption {OK_spec: ext_spec OK_ty} {CS: compspecs}:
  forall E Delta Delta' P c R,
       tycontext_sub Delta Delta' ->
     semax E Delta P c R -> semax E Delta' P c R.
Proof.
  intros.
  induction H0.
  + apply semax_pre with (⌜bool_type (typeof b) = true⌝ ∧ ▷ (tc_expr Delta' (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) ∧ P)); [| apply AuxDefs.semax_ifthenelse; tauto].
    apply andp_ENTAIL; [apply ENTAIL_refl |].
    rewrite !bi.later_and; apply andp_ENTAIL, ENTAIL_refl.
    unfold local, lift1; normalize.
    apply bi.later_mono; eapply Clight_assert_lemmas.tc_expr_sub; eauto.
    eapply semax_lemmas.typecheck_environ_sub; eauto.
  + eapply AuxDefs.semax_seq; intuition eauto.
  + eapply AuxDefs.semax_break; eauto.
  + eapply AuxDefs.semax_continue; eauto.
  + eapply AuxDefs.semax_loop; intuition eauto.
  + eapply semax_pre with (⌜is_int_type (typeof a) = true⌝ ∧ (Q ∧ local (tc_environ Delta'))); first solve_andp.
    eapply AuxDefs.semax_switch.
    - rewrite (add_andp _ _ H0).
      unfold local, lift1; normalize.
      rewrite bi.and_elim_r.
      eapply Clight_assert_lemmas.tc_expr_sub; eauto.
      eapply semax_lemmas.typecheck_environ_sub; eauto.
    - intros.
      eapply semax_pre; [| apply H2; auto].
      solve_andp.
  + eapply semax_pre; [| apply AuxDefs.semax_call_backward].
    apply exp_ENTAIL; intros argsig.
    apply exp_ENTAIL; intros retsig.
    apply exp_ENTAIL; intros cc.
    apply exp_ENTAIL; intros Ef.
    apply exp_ENTAIL; intros A.
    apply exp_ENTAIL; intros P.
    apply exp_ENTAIL; intros Q.
    apply exp_ENTAIL; intros x.
    iIntros "(? & (% & % & % & %) & H)"; iSplit.
    { iPureIntro; split3; last split; [done.. |].
      eapply tc_fn_return_sub; eauto. }
    iSplit; [rewrite bi.and_elim_l | rewrite bi.and_elim_r].
    { iSplit; [rewrite bi.and_elim_l | rewrite bi.and_elim_r].
      * iStopProof; split => rho; monPred.unseal; rewrite monPred_at_affinely; iIntros "(% & ?)".
        iApply Clight_assert_lemmas.tc_expr_sub; last done.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * iStopProof; split => rho; monPred.unseal; rewrite monPred_at_affinely; iIntros "(% & ?)".
        iApply Clight_assert_lemmas.tc_exprlist_sub; last done.
        eapply semax_lemmas.typecheck_environ_sub; eauto. }
    iDestruct "H" as "($ & H)".
    iNext; iDestruct "H" as "($ & H)".
    iStopProof; split => rho; monPred.unseal; rewrite monPred_at_affinely; iIntros "(% & ?)".
    iApply oboxopt_sub; auto.
    * eapply tc_fn_return_temp_guard_opt; eauto.
    * eapply semax_lemmas.typecheck_environ_sub; eauto.
  + eapply semax_pre; [| apply AuxDefs.semax_return].
    assert (ret_type Delta = ret_type Delta') by (unfold tycontext_sub in *; tauto).
    rewrite H0.
    apply andp_ENTAIL; [| apply ENTAIL_refl].
    unfold local, lift1; normalize.
    destruct ret.
    - eapply Clight_assert_lemmas.tc_expr_sub; eauto.
      eapply semax_lemmas.typecheck_environ_sub; eauto.
    - simpl; auto.
  + eapply semax_pre; [| apply AuxDefs.semax_set_ptr_compare_load_cast_load_backward].
    apply orp_ENTAIL; [apply orp_ENTAIL; [apply orp_ENTAIL |] |].
    - apply later_ENTAIL.
      apply andp_ENTAIL, andp_ENTAIL; last apply ENTAIL_refl.
      * unfold local, lift1; normalize.
        eapply Clight_assert_lemmas.tc_expr_sub; eauto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * unfold local, lift1; normalize.
        eapply Clight_assert_lemmas.tc_temp_id_sub; eauto.
    - apply exp_ENTAIL; intro cmp.
      apply exp_ENTAIL; intro e1.
      apply exp_ENTAIL; intro e2.
      apply exp_ENTAIL; intro ty.
      apply exp_ENTAIL; intro sh1.
      apply exp_ENTAIL; intro sh2.
      apply andp_ENTAIL; [| apply later_ENTAIL, andp_ENTAIL; [|apply andp_ENTAIL; [|apply andp_ENTAIL; [|apply andp_ENTAIL; [|apply andp_ENTAIL] ] ] ]].
      * iIntros "(_ & % & % & % & % & % & % & %)"; iPureIntro; repeat split; auto.
        eapply typecheck_tid_ptr_compare_sub; eauto.
      * unfold local, lift1; normalize.
        eapply Clight_assert_lemmas.tc_expr_sub; eauto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * unfold local, lift1; normalize.
        eapply Clight_assert_lemmas.tc_expr_sub; eauto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
    - apply exp_ENTAIL; intro sh.
      apply exp_ENTAIL; intro t2.
      apply exp_ENTAIL; intro v2.
      apply andp_ENTAIL; [| apply later_ENTAIL, andp_ENTAIL; [apply andp_ENTAIL; [|apply andp_ENTAIL ] |] ].
      * iIntros "(_ & % & % & %)"; iPureIntro; repeat split; auto.
        eapply Clight_assert_lemmas.typeof_temp_sub; eauto.
      * unfold local, lift1; normalize.
        eapply Clight_assert_lemmas.tc_lvalue_sub; eauto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
    - apply exp_ENTAIL; intro sh.
      apply exp_ENTAIL; intro e1.
      apply exp_ENTAIL; intro t1.
      apply exp_ENTAIL; intro v2.
      apply andp_ENTAIL; [| apply later_ENTAIL, andp_ENTAIL; [|apply andp_ENTAIL; [|apply andp_ENTAIL ] ] ].
      * iIntros "(_ & % & % & % & %)"; iPureIntro; repeat split; auto.
        eapply Clight_assert_lemmas.typeof_temp_sub; eauto.
      * unfold local, lift1; normalize.
        eapply Clight_assert_lemmas.tc_lvalue_sub; eauto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
      * apply ENTAIL_refl.
  + eapply semax_pre; [| apply AuxDefs.semax_store_store_union_hack_backward].
    apply orp_ENTAIL.
    - apply exp_ENTAIL; intro sh.
      apply andp_ENTAIL; [apply ENTAIL_refl |].
      apply later_ENTAIL.
      apply andp_ENTAIL; [| apply ENTAIL_refl].
      apply andp_ENTAIL.
      * unfold local, lift1; normalize.
        eapply Clight_assert_lemmas.tc_lvalue_sub; eauto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * unfold local, lift1; normalize.
        eapply Clight_assert_lemmas.tc_expr_sub; eauto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
    - apply exp_ENTAIL; intro t2.
      apply exp_ENTAIL; intro ch.
      apply exp_ENTAIL; intro ch'.
      apply exp_ENTAIL; intro sh.
      apply andp_ENTAIL; [apply ENTAIL_refl |].
      apply later_ENTAIL.
      apply andp_ENTAIL; [| apply ENTAIL_refl].
      apply andp_ENTAIL.
      * unfold local, lift1; normalize.
        eapply Clight_assert_lemmas.tc_lvalue_sub; eauto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * unfold local, lift1; normalize.
        eapply Clight_assert_lemmas.tc_expr_sub; eauto.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
  + apply AuxDefs.semax_skip.
  + apply AuxDefs.semax_builtin.
  + apply AuxDefs.semax_label; intuition auto.
  + apply AuxDefs.semax_goto.
  + eapply semax_conseq; [.. | by apply IHsemax].
    - rewrite -H0.
      apply bi.and_mono; [| apply bi.sep_mono]; auto.
      * split => rho; apply bi.pure_mono.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * apply bi.affinely_mono, allp_fun_id_sub; auto.
    - rewrite -H1.
      apply bi.and_mono; [| apply bi.sep_mono]; auto.
      * split => rho; apply bi.pure_mono.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * apply bi.affinely_mono, allp_fun_id_sub; auto.
    - rewrite -H2.
      apply bi.and_mono; [| apply bi.sep_mono]; auto.
      * split => rho; apply bi.pure_mono.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * apply bi.affinely_mono, allp_fun_id_sub; auto.
    - rewrite -H3.
      apply bi.and_mono; [| apply bi.sep_mono]; auto.
      * split => rho; apply bi.pure_mono.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * apply bi.affinely_mono, allp_fun_id_sub; auto.
    - intros.
      rewrite -H4.
      apply bi.and_mono; [| apply bi.sep_mono]; auto.
      * split => rho; apply bi.pure_mono.
        eapply semax_lemmas.typecheck_environ_sub; eauto.
      * apply bi.affinely_mono, allp_fun_id_sub; auto.
  + eapply AuxDefs.semax_mask_mono; intuition eauto.
Qed.

Lemma rvalue_cenv_sub: forall {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) Delta e rho,
  tc_environ Delta rho ->
  tc_expr (CS := CS) Delta e rho ⊢ ⌜@eval_expr CS e rho = @eval_expr CS' e rho⌝.
Proof.
  intros. rewrite typecheck_expr_sound //; apply bi.pure_mono; intros.
  apply (expr_lemmas.eval_expr_cenv_sub_eq CSUB).
  intros N; rewrite N in H0; clear N. apply tc_val_Vundef in H0; trivial.
Qed.
Lemma rvalue_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub CS CS') Delta e rho,
  tc_environ Delta rho ->
  tc_expr (CS := CS) Delta e rho ⊢ ⌜@eval_expr CS e rho = @eval_expr CS' e rho⌝.
Proof. intros. destruct CSUB as [CSUB _]. apply (rvalue_cenv_sub CSUB); trivial. Qed. 

Lemma lvalue_cenv_sub: forall {CS CS'} (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) Delta e rho,
  tc_environ Delta rho ->
  tc_lvalue (CS := CS) Delta e rho ⊢ ⌜@eval_lvalue CS e rho = @eval_lvalue CS' e rho⌝.
Proof. 
  intros. rewrite typecheck_lvalue_sound //; apply bi.pure_mono; intros.
  apply (expr_lemmas.eval_lvalue_cenv_sub_eq CSUB).
  intros N; rewrite N in H0; clear N. apply H0.
Qed.
Lemma lvalue_cspecs_sub: forall {CS CS'} (CSUB: cspecs_sub  CS CS') Delta e rho,
  tc_environ Delta rho ->
  tc_lvalue (CS := CS) Delta e rho ⊢ ⌜@eval_lvalue CS e rho = @eval_lvalue CS' e rho⌝.
Proof. intros. destruct CSUB as [CSUB _]. apply (lvalue_cenv_sub CSUB); trivial. Qed.  

Lemma denote_tc_bool_CSCS' {CS CS'} v e: denote_tc_assert (CS := CS) (tc_bool v e) = denote_tc_assert (CS := CS') (tc_bool v e).
Proof. destruct v; simpl; trivial. Qed.

Lemma tc_expr_NoVundef {CS} Delta rho e (TE: typecheck_environ Delta rho):
  tc_expr Delta e rho ⊢ ⌜tc_val (typeof e) (eval_expr e rho) /\ (eval_expr e rho)<>Vundef⌝.
Proof.
  rewrite typecheck_expr_sound //; apply bi.pure_mono.
  split; trivial. intros N. rewrite N in H; clear N. apply tc_val_Vundef in H; trivial.
Qed. 

Definition SETpre (CS: compspecs) Delta id e P :=
  ▷ (tc_expr Delta e ∧ tc_temp_id id (typeof e) Delta e ∧ assert_of (@subst mpred id (eval_expr e) P))
  ∨ (∃ cmp : Cop.binary_operation,
      ∃ e1 : expr,
      ∃ e2 : expr,
      ∃ ty : type,
      ∃ sh1 : share,
      ∃ sh2 : share,
      ⌜e = Ebinop cmp e1 e2 ty /\
          @sepalg.nonidentity share Share.Join_ba pa_share sh1 /\
          @sepalg.nonidentity share Share.Join_ba pa_share sh2 /\
          is_comparison cmp = true /\
          eqb_type (typeof e1) int_or_ptr_type = false /\ eqb_type (typeof e2) int_or_ptr_type = false /\ typecheck_tid_ptr_compare Delta id = true⌝ ∧
      ▷ (tc_expr Delta e1 ∧ tc_expr Delta e2 ∧ local ((` (blocks_match cmp)) (eval_expr e1) (eval_expr e2)) ∧
          <absorb> assert_of ((` (mapsto_ sh1 (typeof e1))) (eval_expr e1)) ∧
          <absorb> assert_of ((` (mapsto_ sh2 (typeof e2))) (eval_expr e2)) ∧
          assert_of (@subst mpred id (@eval_expr CS (Ebinop cmp e1 e2 ty)) P)))
  ∨ (∃ sh : share,
      ∃ t2 : type,
      ∃ v2 : val,
      ⌜typeof_temp Delta id = @Some type t2 /\ is_neutral_cast (typeof e) t2 = true /\ readable_share sh⌝ ∧
      ▷ (tc_lvalue Delta e ∧ local (` (tc_val (typeof e) v2)) ∧
          <absorb> assert_of ((` (mapsto sh (typeof e))) (@eval_lvalue CS e) (` v2)) ∧ assert_of (@subst mpred id (` v2) P)))
  ∨ (∃ sh : share,
      ∃ e1 : expr,
      ∃ t1 : type,
      ∃ v2 : val,
      ⌜e = Ecast e1 t1 /\ typeof_temp Delta id = @Some type t1 /\ cast_pointer_to_bool (typeof e1) t1 = false /\ readable_share sh⌝ ∧
      ▷ (tc_lvalue Delta e1 ∧ local ((` (tc_val t1)) (` (eval_cast (typeof e1) t1 v2))) ∧
          <absorb> assert_of ((` (mapsto sh (typeof e1))) (@eval_lvalue CS e1) (` v2)) ∧
          assert_of (@subst mpred id (` (force_val (sem_cast (typeof e1) t1 v2))) P))).

Definition ASSIGNpre (CS: compspecs) Delta e1 e2 P: assert :=
  (∃ sh : share,
           ⌜writable_share sh⌝ ∧
           ▷ (tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)) ∧
               (assert_of ((` (mapsto_ sh (typeof e1))) (eval_lvalue e1)) ∗
                (assert_of ((` (mapsto sh (typeof e1))) (eval_lvalue e1)
                   ((` force_val)
                      ((` (sem_cast (typeof e2) (typeof e1))) (eval_expr e2)))) -∗ P))))
          ∨ (∃ (t2 : type) (ch ch' : memory_chunk) (sh : share),
              ⌜(numeric_type (typeof e1) ∧ numeric_type t2)%bool = true /\
                  access_mode (typeof e1) = By_value ch /\
                  access_mode t2 = By_value ch' /\
                  decode_encode_val_ok ch ch' /\ writable_share sh⌝ ∧
              ▷ (tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)) ∧
                  (assert_of ((` (mapsto_ sh (typeof e1))) (eval_lvalue e1)) ∧
                   assert_of ((` (mapsto_ sh t2)) (eval_lvalue e1)) ∗
                   (∀ v' : val,
                    assert_of ((` (mapsto sh t2)) (eval_lvalue e1) (` v')) -∗
                    (local
                      ((` decode_encode_val)
                         ((` force_val)
                            ((` (sem_cast (typeof e2) (typeof e1))) (eval_expr e2)))
                         (` ch) (` ch') (` v'))) → P)))) .

Definition STOREpre (CS: compspecs) Delta e1 e2 P := (∃ sh : share,
     ⌜writable_share sh⌝ ∧
     ▷ (tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)) ∧
         (assert_of ((` (mapsto_ sh (typeof e1))) (@eval_lvalue CS e1)) ∗
          (assert_of ((` (mapsto sh (typeof e1))) (@eval_lvalue CS e1) ((` force_val) ((` (sem_cast (typeof e2) (typeof e1))) (@eval_expr CS e2)))) -∗ P)))).

Definition CALLpre (CS: compspecs) E Delta ret a bl R :=
     ∃ argsig : list type,
     ∃ retsig : type,
     ∃ cc : calling_convention,
     ∃ Ef : coPset,
     ∃ A : TypeTree,
     ∃ P : dtfr (ArgsTT A),
     ∃ Q : dtfr (AssertTT A),
     ∃ x : dtfr A,
     ⌜Ef ⊆ E /\ Cop.classify_fun (typeof a) = Cop.fun_case_f (typelist_of_type_list argsig) retsig cc /\
         (retsig = Tvoid -> ret = @None ident) /\ tc_fn_return Delta ret retsig⌝ ∧
     (tc_expr Delta a ∧ tc_exprlist Delta argsig bl) ∧
     assert_of ((` (func_ptr (mk_funspec (argsig, retsig) cc Ef A P Q))) (@eval_expr CS a)) ∧
     ▷  (assert_of (fun rho => P x (ge_of rho, @eval_exprlist CS argsig bl rho)) ∗
                   (oboxopt Delta ret (maybe_retval (assert_of (Q x)) retsig ret -∗ R))).

(*A variant where (CSUB: cspecs_sub  CS CS') is replaced by (CSUB: cenv_sub (@cenv_cs CS) (@cenv_cs CS')) may be provable once tc_expr lemmas (and maybe eval_expr lemmas, sem_binop etc) have been modified to only take a composite_env rather than a compspecs*) 
Lemma semax_cssub {OK_spec: ext_spec OK_ty} {CS: compspecs} {CS'} (CSUB: cspecs_sub  CS CS') E Delta P c R:
      semax (C := CS) E Delta P c R -> semax (C := CS') E Delta P c R.
Proof.
  intros.
  induction H.
  + apply semax_pre with (⌜bool_type (typeof b) = true⌝ ∧ ▷ (tc_expr (CS := CS') Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) ∧ (tc_expr (CS := CS) Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) ∧ P))); [| apply AuxDefs.semax_ifthenelse; auto].
    { apply bi.and_intro. { rewrite bi.and_elim_r bi.and_elim_l; auto. }
      rewrite !bi.later_and; apply bi.and_intro; last by rewrite bi.and_elim_r bi.and_elim_r.
      unfold local, lift1; normalize.
      rewrite bi.and_elim_l; apply bi.later_mono, tc_expr_cspecs_sub; auto. }
    { eapply semax_pre; [| exact IHsemax1].
      apply bi.and_intro; [solve_andp |].
      rewrite /local /lift1; normalize.
      rewrite bi.and_elim_l.
      trans (tc_expr (CS := CS) Delta b rho); simpl.
      + rewrite denote_tc_assert_andp.
        solve_andp.
      + setoid_rewrite rvalue_cspecs_sub; try done.
        unfold_lift.
        by iIntros "->". }
    { eapply semax_pre; [| exact IHsemax2].
      apply bi.and_intro; [solve_andp |].
      rewrite /local /lift1; normalize.
      rewrite bi.and_elim_l.
      trans (tc_expr (CS := CS) Delta b rho); simpl.
      + rewrite denote_tc_assert_andp.
        solve_andp.
      + setoid_rewrite rvalue_cspecs_sub; try done.
        unfold_lift.
        by iIntros "->". }
  + eapply AuxDefs.semax_seq; eauto.
  + eapply AuxDefs.semax_break; eauto.
  + eapply AuxDefs.semax_continue; eauto.
  + eapply AuxDefs.semax_loop; eauto.
  + eapply semax_pre with (⌜is_int_type (typeof a) = true⌝ ∧ (Q ∧ local (tc_environ Delta))); [solve_andp |].
    eapply AuxDefs.semax_switch.
    - rewrite H.
      rewrite /local /lift1; normalize.
      apply tc_expr_cspecs_sub; trivial.
    - intros; simpl. specialize (H1 n); simpl in H1.
      eapply semax_pre with (local ((` (@eq val)) (@eval_expr CS a) (` (Vint n))) ∧  local ((` (@eq val)) (@eval_expr CS' a) (` (Vint n))) ∧ (Q ∧ local (tc_environ Delta))).
      * apply bi.and_intro; [| solve_andp].
        unfold local, lift1; normalize.
        rewrite H (rvalue_cspecs_sub CSUB Delta a rho H2).
        unfold_lift.
        by iIntros "->".
      * eapply semax_pre, H1. solve_andp. 
  + eapply semax_pre, AuxDefs.semax_call_backward.
    split => rho; rewrite /local /lift1; monPred.unseal.
    apply bi.pure_elim_l; intros TC.
    apply bi.exist_mono; intros argsig.
    apply bi.exist_mono; intros retsig.
    apply bi.exist_mono; intros cc.
    apply bi.exist_mono; intros Ef.
    apply bi.exist_mono; intros A.
    apply bi.exist_mono; intros P.
    apply bi.exist_mono; intros Q.
    apply bi.exist_mono; intros x.
    apply bi.and_mono. trivial.
    iIntros "H"; iAssert (⌜@eval_expr CS a rho = @eval_expr CS' a rho⌝ ∧ ⌜@eval_exprlist CS argsig bl rho = @eval_exprlist CS' argsig bl rho⌝) as "(%Ha & %Hbl)".
    { rewrite bi.and_elim_l. iApply (bi.and_mono with "H").
      apply rvalue_cspecs_sub; trivial. apply eval_exprlist_cspecs_sub; trivial. }
    unfold_lift; rewrite Ha Hbl.
    iApply (bi.and_mono with "H"); last done.
    apply bi.and_mono.
    eapply tc_expr_cspecs_sub; trivial. apply tc_exprlist_cspecs_sub; trivial.
  + eapply semax_pre, AuxDefs.semax_return.
    unfold local, lift1; normalize.
    apply bi.and_intro. rewrite bi.and_elim_l. destruct CSUB; apply tc_expropt_cenv_sub; trivial.
    apply (RA_return_cast_expropt_cspecs_sub CSUB); trivial.
  + eapply semax_pre, AuxDefs.semax_set_ptr_compare_load_cast_load_backward.
    split => rho; monPred.unseal. apply bi.pure_elim_l; intros TEDelta.
    apply bi.or_mono.
    { apply bi.or_mono.
      + apply bi.or_mono.
        - apply bi.later_mono. apply bi.and_intro, bi.and_intro.
          * rewrite bi.and_elim_l. apply tc_expr_cspecs_sub; trivial.
          * rewrite bi.and_elim_r bi.and_elim_l. apply tc_temp_id_cspecs_sub; trivial.
          * setoid_rewrite (rvalue_cspecs_sub CSUB Delta); last done.
            rewrite /subst /=; by iIntros "(-> & _ & ?)".
        - apply bi.exist_mono; intros op.
          apply bi.exist_mono; intros e1.
          apply bi.exist_mono; intros e2.
          apply bi.exist_mono; intros t.
          apply bi.exist_mono; intros sh1.
          apply bi.exist_mono; intros sh2. normalize. apply bi.later_mono.
          iIntros "H"; iAssert (⌜@eval_expr CS e1 rho = @eval_expr CS' e1 rho⌝ ∧ ⌜@eval_expr CS e2 rho = @eval_expr CS' e2 rho⌝) as "(%He1 & %He2)".
          { rewrite assoc bi.and_elim_l. iApply (bi.and_mono with "H").
            apply (rvalue_cspecs_sub CSUB Delta); trivial.
            apply (rvalue_cspecs_sub CSUB Delta); trivial. }
          rewrite /subst /lift1; unfold_lift; rewrite !monPred_at_absorbingly /= !He1 !He2.
          iApply (bi.and_mono with "H"); first by apply @tc_expr_cspecs_sub.
          apply bi.and_mono; first by apply @tc_expr_cspecs_sub.
          apply bi.and_mono; first done.
          apply bi.and_mono; first done.
          apply bi.and_mono; first done.
          rewrite /sem_binary_operation'. destruct H as [? [_ [_ [Hc [? [? ?]]]]]].
          destruct op; simpl; try solve [inv Hc]; trivial.
      + apply bi.exist_mono; intros sh.
        apply bi.exist_mono; intros t.
        apply bi.exist_mono; intros v. normalize.
        apply bi.and_intro; first by apply bi.pure_intro.
        apply bi.later_mono.
        apply bi.pure_elim_l; intros.
        rewrite -!assoc; apply bi.and_intro. rewrite !bi.and_elim_l; apply tc_lvalue_cspecs_sub; trivial.
        apply bi.and_intro; first by apply bi.pure_intro.
        setoid_rewrite lvalue_cspecs_sub; [| done..].
        rewrite !monPred_at_absorbingly /=; unfold_lift; by iIntros "(-> & ?)". }
    { apply bi.exist_mono; intros sh.
      apply bi.exist_mono; intros e1.
      apply bi.exist_mono; intros t.
      apply bi.exist_mono; intros v. normalize. apply bi.later_mono.
      iIntros "H"; iAssert ⌜@eval_lvalue CS e1 rho = @eval_lvalue CS' e1 rho⌝ as %He1.
      { setoid_rewrite lvalue_cspecs_sub; [| done..]. iDestruct "H" as "($ & _)". }
      iApply (bi.and_mono with "H"); first by apply @tc_lvalue_cspecs_sub.
      rewrite /lift1 !monPred_at_absorbingly /=; unfold_lift; rewrite He1 //. }
  + eapply semax_pre, AuxDefs.semax_store_store_union_hack_backward.
    split => rho; monPred.unseal. apply bi.pure_elim_l; intros TEDelta.
    apply bi.or_mono.
    * apply bi.exist_mono; intros sh. apply bi.and_mono; first done. apply bi.later_mono.
      apply bi.and_intro.
      { rewrite bi.and_elim_l. apply bi.and_mono. apply tc_lvalue_cspecs_sub; trivial. apply tc_expr_cspecs_sub; trivial. }
      iIntros "H"; iAssert (⌜@eval_lvalue CS e1 rho = @eval_lvalue CS' e1 rho⌝ ∧ ⌜@eval_expr CS e2 rho = @eval_expr CS' e2 rho⌝) as "(%He1 & %He2)".
      { rewrite bi.and_elim_l. iApply (bi.and_mono with "H").
        apply lvalue_cspecs_sub; trivial.
        etrans; last by apply rvalue_cspecs_sub.
        rewrite denote_tc_assert_andp. simpl. solve_andp. }
      rewrite bi.and_elim_r.
      unfold_lift; rewrite He1; iDestruct "H" as "($ & H)".
      iIntros (? [=]) "?"; subst; iApply "H"; first done.
      rewrite He1 He2 //.
    * apply bi.exist_mono; intros t2.
      apply bi.exist_mono; intros ch.
      apply bi.exist_mono; intros ch'.
      apply bi.exist_mono; intros sh.
      apply bi.and_mono; first done. apply bi.later_mono.
      apply bi.and_intro.
      { rewrite bi.and_elim_l. apply bi.and_mono. apply tc_lvalue_cspecs_sub; trivial. apply tc_expr_cspecs_sub; trivial. }
      iIntros "H"; iAssert (⌜@eval_lvalue CS e1 rho = @eval_lvalue CS' e1 rho⌝ ∧ ⌜@eval_expr CS e2 rho = @eval_expr CS' e2 rho⌝) as "(%He1 & %He2)".
      { rewrite bi.and_elim_l. iApply (bi.and_mono with "H").
        apply lvalue_cspecs_sub; trivial.
        etrans; last by apply rvalue_cspecs_sub.
        rewrite denote_tc_assert_andp. simpl. solve_andp. }
      rewrite bi.and_elim_r.
      unfold_lift; rewrite He1; iDestruct "H" as "($ & H)".
      iIntros (?? [=]) "?"; iIntros (? [=] ?); subst. rewrite -He1; iApply ("H" with "[%] [$]"); try done.
      rewrite /lift1 /= He2 //.
  + apply AuxDefs.semax_skip.
  + apply AuxDefs.semax_builtin.
  + apply AuxDefs.semax_label; auto.
  + apply AuxDefs.semax_goto.
  + eapply semax_conseq; [.. | exact IHsemax]; auto.
  + eapply AuxDefs.semax_mask_mono; eauto.
Qed.

Lemma semax_body_subsumption: forall {CS} V V' F F' f spec
      (SF: semax_body V F f spec)
      (TS: tycontext_sub (func_tycontext f V F nil) (func_tycontext f V' F' nil)),
    semax_body V' F' f spec.
Proof.
  destruct spec. destruct f0. 
  intros [? [? SF]] ?. split3; auto.
  intros.
  eapply semax_Delta_subsumption. apply TS.
  apply (SF _ x).
Qed.

(*Should perhaps be called semax_body_cespecs_sub, also in the Module Type *)
Lemma semax_body_cenv_sub {CS CS'} (CSUB: cspecs_sub CS CS') V G f spec
      (COMPLETE : Forall (fun it : ident * type => complete_type (@cenv_cs CS) (snd it) = true) (fn_vars f)):
    semax_body V G (C := CS) f spec -> semax_body V G (C := CS') f spec.
Proof.
  destruct spec. destruct f0.
  intros [H' [H'' H]]; split3; auto.
  intros.  specialize (H _ x).
  rewrite <- (semax_prog.stackframe_of_cspecs_sub CSUB); [apply (semax_cssub CSUB); apply H | trivial].
Qed. 

Lemma semax_extract_exists':
  forall  {OK_spec: ext_spec OK_ty} {CS: compspecs} (A : Type) (P : A -> assert) c E (Delta: tycontext) (R: ret_assert),
  (forall x, semax E Delta (P x) c R) ->
   semax E Delta (∃ x:A, P x) c R.
Proof. intros. apply semax_extract_exists in H. apply H. Qed.

Lemma semax_extract_prop':
  forall {OK_spec: ext_spec OK_ty} {CS: compspecs} E Delta (PP: Prop) P c Q,
           (PP -> semax E Delta P c Q) ->
           semax E Delta (⌜PP⌝ ∧ P) c Q.
Proof. intros. apply semax_extract_prop in H. apply H. Qed.

Lemma modifiedvars_aux: forall id, (fun i => isSome ((insert_idset id idset0) !! i)) = eq id.
Proof.
  intros.
  extensionality i.
  apply prop_ext.
  unfold insert_idset.
  destruct (ident_eq i id).
  + subst.
    setoid_rewrite Maps.PTree.gss.
    simpl; tauto.
  + setoid_rewrite Maps.PTree.gso; auto.
    unfold idset0.
    rewrite Maps.PTree.gempty.
    simpl.
    split; [tauto | intro].
    congruence.
Qed.

Lemma sep_mono_full: forall Delta E P1 P2 Q1 Q2,
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P1) ⊢ (|={E}=> P2)) ->
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ Q1) ⊢ (|={E}=> Q2)) ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ (P1 ∗ Q1)) ⊢ (|={E}=> (P2 ∗ Q2)).
Proof.
  intros.
  rewrite sepcon_ENTAILL //.
  by iIntros "(>$ & >$)".
Qed.

Lemma semax_frame:
  forall {OK_spec: ext_spec OK_ty} {CS: compspecs} E Delta P s R F,
   closed_wrt_modvars s F ->
  semax E Delta P s R ->
    semax E Delta (P ∗ F) s (frame_ret_assert R F).
Proof.
  intros.
  induction H0.
  + apply semax_pre with (⌜bool_type (typeof b) = true⌝ ∧ (▷ (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) ∧ (P ∗ F)))).
    - by iIntros "(_ & ($ & ?) & $)".
    - rewrite semax_lemmas.closed_Sifthenelse in H; destruct H.
      apply AuxDefs.semax_ifthenelse.
      * eapply semax_pre; [| apply IHsemax1; auto].
        iIntros "(_ & ($ & $) & $)".
      * eapply semax_pre; [| apply IHsemax2; auto].
        iIntros "(_ & ($ & $) & $)".
  + rewrite semax_lemmas.closed_Ssequence in H; destruct H.
    apply AuxDefs.semax_seq with (Q ∗ F).
    - destruct R; apply IHsemax1; auto.
    - destruct R; apply IHsemax2; auto.
  + replace (RA_break Q ∗ F) with (RA_break (frame_ret_assert Q F)) by (destruct Q; auto).
    apply AuxDefs.semax_break.
  + replace (RA_continue Q ∗ F) with (RA_continue (frame_ret_assert Q F)) by (destruct Q; auto).
    apply AuxDefs.semax_continue.
  + rewrite semax_lemmas.closed_Sloop in H; destruct H.
    eapply AuxDefs.semax_loop with (Q' ∗ F).
    - destruct R; apply IHsemax1; auto.
    - eapply semax_post, IHsemax2; auto; destruct R; simpl; intros; rewrite bi.and_elim_r //.
      rewrite bi.sep_False //.
  + eapply semax_pre, (AuxDefs.semax_switch _ _ (Q ∗ F)).
    - iIntros "(_ & ($ & $) & $)".
    - rewrite H0; iIntros "($ & _)".
    - intros; eapply semax_pre_post, H2; try solve [destruct R; simpl; intros; rewrite bi.and_elim_r //].
      * iIntros "(_ & $ & $ & $)".
      * destruct R; simpl; iIntros "(_ & [] & _)".
      * eapply semax_lemmas.closed_Sswitch; eauto.
  + eapply semax_pre_post; [.. | apply (AuxDefs.semax_call_backward _ _ _ _ _ (R ∗ F)); auto];
      try solve [destruct R; simpl; intros; rewrite bi.and_elim_r //; iIntros "[]"].
    rewrite bi.and_elim_r.
    rewrite bi.sep_exist_r. apply bi.exist_mono; intros argsig.
    rewrite bi.sep_exist_r. apply bi.exist_mono; intros retsig.
    rewrite bi.sep_exist_r. apply bi.exist_mono; intros cc.
    rewrite bi.sep_exist_r. apply bi.exist_mono; intros Ef.
    rewrite bi.sep_exist_r. apply bi.exist_mono; intros A.
    rewrite bi.sep_exist_r. apply bi.exist_mono; intros P.
    rewrite bi.sep_exist_r. apply bi.exist_mono; intros Q.
    rewrite bi.sep_exist_r. apply bi.exist_mono; intros x.
    iIntros "(((% & % & % & %) & H) & F)"; iSplit; first done.
    iSplit; first by rewrite bi.and_elim_l; iDestruct "F" as "_".
    iDestruct "H" as "(_ & $ & H)".
    iNext; iDestruct "H" as "($ & H)".
    rewrite <- (oboxopt_closed Delta ret F) at 1 by (try eapply tc_fn_return_temp_guard_opt; eauto).
    iCombine "H F" as "H"; rewrite oboxopt_sepcon.
    iApply (oboxopt_K with "H").
    iIntros "(H & $) ?"; iApply "H"; done.
  + eapply semax_pre; [| apply AuxDefs.semax_return].
    rewrite bi.and_elim_r.
    apply bi.and_intro.
    - iIntros "(($ & _) & _)".
    - split => rho; destruct R; simpl; monPred.unseal; unfold_lift.
      iIntros "((_ & $) & $)".
  + eapply semax_pre_post, AuxDefs.semax_set_ptr_compare_load_cast_load_backward;
      try solve [simpl; intros; rewrite bi.and_elim_r //; iIntros "[]"].
    rewrite bi.and_elim_r.
    rewrite !bi.sep_or_r.
    repeat apply bi.or_mono.
    - iIntros "H"; iNext.
      iSplit; first by iDestruct "H" as "(($ & _) & _)".
      iSplit; first by iDestruct "H" as "((_ & $ & _) & _)".
      rewrite !bi.and_elim_r subst_sepcon.
      iDestruct "H" as "($ & ?)".
      rewrite closed_wrt_subst //.
      rewrite -modifiedvars_aux //.
    - rewrite bi.sep_exist_r; apply bi.exist_mono; intros cmp.
      rewrite bi.sep_exist_r; apply bi.exist_mono; intros e1.
      rewrite bi.sep_exist_r; apply bi.exist_mono; intros e2.
      rewrite bi.sep_exist_r; apply bi.exist_mono; intros ty.
      rewrite bi.sep_exist_r; apply bi.exist_mono; intros sh1.
      rewrite bi.sep_exist_r; apply bi.exist_mono; intros sh2.
      iIntros "(($ & H) & ?)".
      iNext.
      repeat (iSplit; first rewrite bi.and_elim_l //; rewrite bi.and_elim_r).
      rewrite subst_sepcon; iFrame.
      rewrite closed_wrt_subst //.
      rewrite -modifiedvars_aux //.
    - rewrite bi.sep_exist_r; apply bi.exist_mono; intros sh.
      rewrite bi.sep_exist_r; apply bi.exist_mono; intros t2.
      rewrite bi.sep_exist_r; apply bi.exist_mono; intros v2.
      iIntros "(($ & H) & ?)".
      iNext.
      repeat (iSplit; first rewrite bi.and_elim_l //; rewrite bi.and_elim_r).
      rewrite subst_sepcon; iFrame.
      rewrite closed_wrt_subst //.
      rewrite -modifiedvars_aux //.
    - rewrite bi.sep_exist_r; apply bi.exist_mono; intros sh.
      rewrite bi.sep_exist_r; apply bi.exist_mono; intros e1.
      rewrite bi.sep_exist_r; apply bi.exist_mono; intros t1.
      rewrite bi.sep_exist_r; apply bi.exist_mono; intros v2.
      iIntros "(($ & H) & ?)".
      iNext.
      repeat (iSplit; first rewrite bi.and_elim_l //; rewrite bi.and_elim_r).
      rewrite subst_sepcon; iFrame.
      rewrite closed_wrt_subst //.
      rewrite -modifiedvars_aux //.
  + eapply semax_pre_post, AuxDefs.semax_store_store_union_hack_backward;
      try solve [simpl; intros; rewrite bi.and_elim_r //; iIntros "[]"].
    rewrite bi.and_elim_r.
    rewrite bi.sep_or_r.
    apply bi.or_mono.
    - rewrite bi.sep_exist_r; apply bi.exist_mono; intros sh.
      iIntros "(($ & H) & ?)".
      iNext.
      repeat (iSplit; first rewrite bi.and_elim_l //; rewrite bi.and_elim_r).
      iDestruct "H" as "($ & H)"; iIntros "?".
      iFrame; iApply "H"; done.
    - rewrite bi.sep_exist_r; apply bi.exist_mono; intros t2.
      rewrite bi.sep_exist_r; apply bi.exist_mono; intros ch.
      rewrite bi.sep_exist_r; apply bi.exist_mono; intros ch'.
      rewrite bi.sep_exist_r; apply bi.exist_mono; intros sh.
      iIntros "(($ & H) & ?)".
      iNext.
      repeat (iSplit; first rewrite bi.and_elim_l //; rewrite bi.and_elim_r).
      iDestruct "H" as "($ & H)"; iIntros (?) "?".
      iFrame; iApply "H"; done.
  + eapply semax_post, AuxDefs.semax_skip; try solve [simpl; intros; rewrite bi.and_elim_r //; iIntros "[]"].
  + eapply semax_pre, AuxDefs.semax_builtin.
    iIntros "(_ & [] & _)".
  + apply AuxDefs.semax_label.
    apply IHsemax; auto.
  + eapply semax_pre, AuxDefs.semax_goto.
    iIntros "(_ & [] & _)".
  + eapply semax_conseq; [.. | apply IHsemax; auto].
    - apply sep_mono_full; [exact H0 |].
      reduce2derives.
      auto.
    - destruct R, R'.
      apply sep_mono_full; [exact H1 |].
      reduce2derives.
      auto.
    - destruct R, R'.
      apply sep_mono_full; [exact H2 |].
      reduce2derives.
      auto.
    - destruct R, R'.
      apply sep_mono_full; [exact H3 |].
      reduce2derives.
      auto.
    - intros; destruct R, R'.
      apply sepcon_ENTAILL; auto.
      iIntros "(_ & _ & $)".
  + eapply AuxDefs.semax_mask_mono; intuition eauto.
Qed.

Lemma semax_adapt_frame {OK_spec: ext_spec OK_ty} {CS: compspecs} E Delta c (P P': assert) (Q Q' : ret_assert)
   (H: (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P)) ⊢
                   (∃ F: assert, (⌜closed_wrt_modvars c F⌝ ∧ (|={E}=> (P' ∗ F) ∧
                         ⌜local (tc_environ Delta) ∧ <affine> allp_fun_id Delta ∗ RA_normal (frame_ret_assert Q' F) ⊢ |={E}=> RA_normal Q⌝ ∧
                         ⌜local (tc_environ Delta) ∧ <affine> allp_fun_id Delta ∗ RA_break (frame_ret_assert Q' F) ⊢ |={E}=> RA_break Q⌝ ∧
                         ⌜local (tc_environ Delta) ∧ <affine> allp_fun_id Delta ∗ RA_continue (frame_ret_assert Q' F) ⊢ |={E}=> RA_continue Q⌝ ∧
                         ⌜forall vl, local (tc_environ Delta) ∧ <affine> allp_fun_id Delta ∗ RA_return (frame_ret_assert Q' F) vl ⊢ RA_return Q vl⌝))))
   (SEM: semax E Delta P' c Q'):
   semax E Delta P c Q.
Proof.
  apply (semax_conseq _ _ _ _ _ E Delta (∃ F: assert, (⌜closed_wrt_modvars c F⌝ ∧ (|={E}=> (P' ∗ F) ∧
                         ⌜(local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_normal (frame_ret_assert Q' F)) ⊢ |={E}=> (RA_normal Q))⌝ ∧
                         ⌜(local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_break (frame_ret_assert Q' F)) ⊢ |={E}=> (RA_break Q))⌝ ∧
                         ⌜(local (tc_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_continue (frame_ret_assert Q' F)) ⊢ |={E}=> (RA_continue Q))⌝ ∧
                         ⌜forall vl, ((local (tc_environ Delta)) ∧ (<affine> allp_fun_id Delta ∗ RA_return (frame_ret_assert Q' F) vl) ⊢ (RA_return Q vl))⌝)))
    Q).
  + rewrite H.
    iIntros "(% & % & >(? & % & % & % & %))"; iExists F; iFrame; done.
  + by iIntros "(_ & _ & $)".
  + by iIntros "(_ & _ & $)".
  + by iIntros "(_ & _ & $)".
  + intros; by iIntros "(_ & _ & $)".
  + apply semax_extract_exists'. intros F. clear H.
    apply semax_extract_prop'. intros.
    eapply semax_pre_fupd. 2:{ do 4 (apply semax_extract_prop; intros).
      eapply semax_conseq. 6:{ apply semax_frame. exact H. apply SEM. }
      2: { exact H0. }
      2: { exact H1. }
      2: { exact H2. }
      2: { exact H3. }
      rewrite bi.and_elim_r bi.affinely_elim_emp bi.emp_sep; apply fupd_intro. }
    by iIntros "(? & >($ & % & % & % & %))".
Qed.

Lemma semax_adapt: forall {OK_spec: ext_spec OK_ty} {CS: compspecs} E Delta c (P P': assert) (Q Q' : ret_assert)
   (H: (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P)) ⊢
      ((|={E}=> P' ∧
                        ⌜RA_normal Q' ⊢ |={E}=> (RA_normal Q)⌝ ∧
                        ⌜RA_break Q' ⊢ |={E}=> (RA_break Q)⌝ ∧
                        ⌜RA_continue Q' ⊢ |={E}=> (RA_continue Q)⌝ ∧
                        ⌜forall vl, RA_return Q' vl ⊢ (RA_return Q vl)⌝)))
   (SEM: semax E Delta P' c Q'),
   semax E Delta P c Q.
Proof.
  intros. eapply semax_adapt_frame; eauto.
  rewrite H; iIntros "H"; iExists emp; iSplit.
  { iPureIntro; intros ???; monPred.unseal; done. }
  iDestruct "H" as ">($ & % & % & % & %)".
  destruct Q'; simpl in *.
  iPureIntro; split3; last split3; auto; intros; rewrite bi.sep_emp bi.and_elim_r bi.affinely_elim_emp bi.emp_sep //.
Qed.

Lemma typecheck_environ_globals_only t rho: typecheck_environ (rettype_tycontext t) (globals_only rho).
Proof.
  split3; red; simpl; intros. setoid_rewrite Maps.PTree.gempty in H. congruence.
  split; intros. setoid_rewrite Maps.PTree.gempty in H. congruence. destruct H; inv H.
  setoid_rewrite Maps.PTree.gempty in H. congruence.
Qed. 

Lemma typecheck_environ_env_setglobals_only t rho x v: typecheck_environ (rettype_tycontext t) (env_set (globals_only rho) x v).
Proof.
  split3; red; simpl; intros. setoid_rewrite Maps.PTree.gempty in H. congruence.
  split; intros. setoid_rewrite Maps.PTree.gempty in H. congruence. destruct H; inv H.
  setoid_rewrite Maps.PTree.gempty in H. congruence.
Qed.
 
(*This proof can now be cleaned up, by replacing
use of tcvals in the argument to semax_adapt by hasType*)
Lemma semax_body_funspec_sub {CS : compspecs} {V G f i phi phi'} (SB: semax_body V G f (i, phi))
  (Sub: funspec_sub phi phi')
  (LNR: list_norepet (map fst (fn_params f) ++ map fst (fn_temps f))):
  semax_body V G f (i, phi').
Proof.
destruct phi as [sig cc E A P Q].
destruct phi' as [sig' cc' E' A' P' Q'].
destruct Sub as [(Tsigs & CC & HE) Sub]. subst cc' sig'. simpl in Sub.
destruct SB as [SB1 [SB2 SB3]].
split3; trivial. intros.
specialize (Sub x).
apply semax_adapt
 with
  (Q':= frame_ret_assert (function_body_ret_assert (fn_return f) (assert_of (Q' x)))
           (stackframe_of f))
  (P' :=
    ∃ vals:list val,
    ∃ x1 : dtfr A,
    ∃ FR: _,
    ⌜forall rho' : environ,
              ⌜tc_environ (rettype_tycontext (snd sig)) rho'⌝ ∧ (FR ∗ Q x1 rho') ⊢ (Q' x rho')⌝ ∧
      ((stackframe_of f ∗ ⎡FR⎤ ∗ assert_of (fun tau => P x1 (ge_of tau, vals))) ∧
            local (fun tau => map (Map.get (te_of tau)) (map fst (fn_params f)) = map Some vals /\ tc_vals (map snd (fn_params f)) vals))).
 - split => rho. monPred.unseal; rewrite /bind_ret monPred_at_affinely.
   iIntros "(%TC & #OM & (%vals & (%MAP & %VUNDEF) & HP') & M2)".
   specialize (Sub (ge_of rho, vals)). iMod (Sub with "[$HP']") as "Sub". {
     iPureIntro; split; trivial.
     simpl.
     rewrite SB1. simpl in TC. destruct TC as [TC1 [TC2 TC3]].
     unfold fn_funsig. simpl. clear - TC1 MAP LNR VUNDEF.
     specialize (@tc_temp_environ_elim (fn_params f) (fn_temps f) _ LNR TC1). simpl in TC1.  red in TC1. clear - MAP; intros TE.
     forget (fn_params f) as params. generalize dependent vals.
     induction params; simpl; intros.
     + destruct vals; inv MAP. constructor.
     + destruct vals; inv MAP. constructor.
       * clear IHparams. intros. destruct (TE (fst a) (snd a)) as [w [W Tw]].
         left; destruct a; trivial.
         rewrite W in H0. inv H0.
         apply tc_val_has_type; apply Tw; trivial.
       * apply IHparams; simpl; trivial.
         intros. apply TE. right; trivial. }
   iIntros "!>"; iSplit; last iPureIntro.
   clear Sub.
   iDestruct "Sub" as (x1 FR1) "(A1 & %RetQ)".
   iExists vals, x1, FR1.
   iSplit; last iSplit.
    + iPureIntro; simpl; intros. rewrite -RetQ.
      iIntros "(% & $)"; iPureIntro; split; last trivial.
      simpl in H. clear - H. destruct H as [_ [Hve _]].
      simpl in *. red in Hve. destruct rho'; simpl in *.
      apply Map.ext; intros x. specialize (Hve x).
      destruct (Map.get ve x); simpl.
      * destruct p; simpl in *. destruct (Hve t) as [_ H]; clear Hve.
        exploit H. exists b; trivial. rewrite Maps.PTree.gempty //.
      * reflexivity.
    + iFrame.
    + iPureIntro; split; trivial. destruct TC as [TC1 _]. simpl in TC1. red in TC1.
      clear - MAP VUNDEF TC1 LNR. forget (fn_params f) as params. forget (fn_temps f) as temps. forget (te_of rho) as tau.
      clear f rho. generalize dependent vals. induction params; simpl; intros; destruct vals; inv MAP; trivial.
      inv VUNDEF. inv LNR. destruct a; simpl in *.
      assert (X: forall id ty, (make_tycontext_t params temps) !! id = Some ty ->
                 exists v : val, Map.get tau id = Some v /\ tc_val' ty v).
      { intros. apply TC1. simpl. setoid_rewrite Maps.PTree.gso; trivial.
        apply make_context_t_get in H. intros ?; subst id. contradiction. }
      split; [ clear IHparams | apply (IHparams H6 X _ H1 H4)].
      destruct (TC1 i t) as [u [U TU]]; clear TC1. setoid_rewrite Maps.PTree.gss; trivial.
      rewrite U in H0; inv H0. apply TU; trivial.
    + split3; last split; intros; split => ?; monPred.unseal; auto.
 - clear Sub.
   apply semax_extract_exists; intros vals.
   apply semax_extract_exists; intros x1.
   apply semax_extract_exists; intros FRM.
   apply semax_extract_prop; intros QPOST.
   unfold fn_funsig in *. simpl in SB2; rewrite -> SB2 in *.
   apply (semax_frame E (func_tycontext f V G nil)
      (close_precondition (map fst (fn_params f)) (argsassert_of (P x1)) ∗
         stackframe_of f)
      (fn_body f)
      (frame_ret_assert (function_body_ret_assert (fn_return f) (assert_of (Q x1))) (stackframe_of f))
      ⎡FRM⎤) in SB3.
    + eapply AuxDefs.semax_mask_mono; first done.
      eapply semax_pre_post_fupd.
      6: apply SB3.
      all: clear SB3; intros; simpl; try iIntros "(_ & ([] & ?) & _)".
      * split => rho; monPred.unseal; iIntros "(%TC & (N1 & (? & N2)) & (%VALS & %TCVals)) !>"; iFrame.
        unfold close_precondition.
        iExists vals; iFrame; iPureIntro; repeat (split; trivial).
        apply (tc_vals_Vundef TCVals).
      * split => rho; rewrite /bind_ret; monPred.unseal; destruct (fn_return f); try iIntros "(_ & ([] & _) & _)".
        rewrite /= -QPOST; iIntros "(? & (? & ?) & ?)"; iFrame.
        iPureIntro; split; last done.
        apply tc_environ_rettype.
      * split => rho; rewrite /bind_ret; monPred.unseal; iIntros "(% & (Q & $) & ?)".
        destruct vl; simpl.
        -- rewrite -QPOST.
           iDestruct "Q" as "($ & $)"; iFrame; iPureIntro; split; last done.
           apply tc_environ_rettype_env_set.
        -- destruct (fn_return f); try iDestruct "Q" as "[]".
           rewrite /= -QPOST; iFrame; iPureIntro; split; last done.
           apply tc_environ_rettype.
    + do 2 red; intros; monPred.unseal; trivial.
Qed.

End mpred.

End DeepEmbeddedMinimumSeparationLogic.

Module DeepEmbeddedPracticalLogic <: PRACTICAL_CLIGHT_SEPARATION_HOARE_LOGIC.

Module CSHL_Def := DeepEmbeddedDef.

Module CSHL_Defs := DeepEmbeddedDefs.

Module CSHL_MinimumLogic := DeepEmbeddedMinimumSeparationLogic.

Definition semax_set := @DeepEmbeddedMinimumSeparationLogic.SetB.semax_set_backward.

Arguments semax {_} {_} {_} {_} {_}.

Section mpred.

Context `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty} {CS: compspecs}.

Lemma semax_loop_nocontinue:
 forall E Delta P body incr R,
 semax E Delta P (Ssequence body incr) (loop_nocontinue_ret_assert P R) ->
 semax E Delta P (Sloop body incr) R.
Proof.
  intros.
  apply semax_seq_inv in H.
  destruct H as [Q [? ?]].
  eapply (AuxDefs.semax_loop _ _ P Q).
  + clear - H.
    unfold overridePost, loop_nocontinue_ret_assert, loop1_ret_assert in *.
    eapply semax_post, H.
    - rewrite bi.and_elim_r.
      destruct R; done.
    - rewrite bi.and_elim_r.
      destruct R; done.
    - rewrite bi.and_elim_r.
      destruct R.
      apply False_left.
    - intro.
      rewrite bi.and_elim_r.
      destruct R; done.
  + clear - H0.
    unfold overridePost, loop_nocontinue_ret_assert, loop2_ret_assert in *.
    auto.
Qed.

Lemma semax_if_seq:
 forall E Delta P e c1 c2 c Q,
 semax E Delta P (Sifthenelse e (Ssequence c1 c) (Ssequence c2 c)) Q ->
 semax E Delta P (Ssequence (Sifthenelse e c1 c2) c) Q.
Proof.
  intros.
  apply semax_ifthenelse_inv in H.
  eapply (semax_conseq _ _ (∃ P', ▷ (⌜semax E Delta (P' ∧ local (liftx (typed_true (typeof e)) (eval_expr e)))%I (Ssequence c1 c) Q
               ∧ semax E Delta (P' ∧ local (liftx (typed_false (typeof e)) (eval_expr e)))%I (Ssequence c2 c) Q⌝) ∧ 
           ⌜bool_type (typeof e) = true⌝ ∧ ▷ (tc_expr Delta (Eunop Onotbool e (Tint I32 Signed noattr)) ∧ P')
            )); [| intros; try apply derives_full_refl .. |].
  { rewrite H bi.and_exist_l bi.later_exist bi.and_exist_l.
    iIntros ">(%P' & H) !>"; iExists P'.
    iDestruct "H" as "($ & H)"; rewrite -bi.later_and; iNext.
    iSplit; [iDestruct "H" as "(_ & $ & _)" | iSplit; [iDestruct "H" as "($ & _)" | iDestruct "H" as "(_ & _ & $)"]]. }
  { iIntros "(_ & _ & $)". }
  apply semax_extract_exists; intros P'.
  apply semax_extract_later_prop; intros [Ht Hf].
  apply semax_seq_inv in Ht.
  apply semax_seq_inv in Hf.
  destruct Ht as [Q1 [Ht ?]], Hf as [Q2 [Hf ?]].
  apply AuxDefs.semax_seq with (Q1 ∨ Q2); [apply AuxDefs.semax_ifthenelse |].
  + eapply semax_post, Ht.
    - destruct Q; rewrite bi.and_elim_r; apply bi.or_intro_l.
    - destruct Q; rewrite bi.and_elim_r //.
    - destruct Q; rewrite bi.and_elim_r //.
    - intro; destruct Q; rewrite bi.and_elim_r //.
  + eapply semax_post, Hf.
    - destruct Q; rewrite bi.and_elim_r; apply bi.or_intro_r.
    - destruct Q; rewrite bi.and_elim_r //.
    - destruct Q; rewrite bi.and_elim_r //.
    - intro; destruct Q; rewrite bi.and_elim_r //.
  + apply semax_orp; auto.
Qed.

Lemma semax_loop_unroll1:
  forall E Delta P P' Q body incr R,
  semax E Delta P body (loop1_ret_assert P' R) ->
  semax E Delta P' incr (loop2_ret_assert Q R) ->
  semax E Delta Q (Sloop body incr) R ->
  semax E Delta P (Sloop body incr) R.
Proof.
  intros.
  apply semax_loop_inv in H1.
  apply semax_pre with (P ∨ Q ∨
                  (∃ Q : assert,
                    (∃ Q' : assert,
                     ⌜semax E Delta Q body (loop1_ret_assert Q' R) /\
                         semax E Delta Q' incr (loop2_ret_assert Q R)⌝ ∧ Q))).
  { rewrite bi.and_elim_r; apply bi.or_intro_l. }
  apply AuxDefs.semax_loop with (P' ∨
                  (∃ Q : assert,
                    (∃ Q' : assert,
                     ⌜semax E Delta Q body (loop1_ret_assert Q' R) /\
                         semax E Delta Q' incr (loop2_ret_assert Q R)⌝ ∧ Q'))).
  + apply semax_orp; [| apply semax_orp].
    - eapply semax_post, H.
      * unfold loop1_ret_assert; destruct R.
        rewrite bi.and_elim_r; apply bi.or_intro_l.
      * unfold loop1_ret_assert; destruct R.
        rewrite bi.and_elim_r //.
      * unfold loop1_ret_assert; destruct R.
        rewrite bi.and_elim_r; apply bi.or_intro_l .
      * intros.
        unfold loop1_ret_assert; destruct R.
        rewrite bi.and_elim_r //.
    - eapply semax_conseq; [exact H1 | intros; try apply derives_full_refl .. |].
      { iIntros "(_ & _ & $)". }
      apply semax_extract_exists; intros Q'.
      apply semax_extract_exists; intros Q''.
      apply semax_extract_prop; intros [?H ?H].
      apply semax_post with (loop1_ret_assert Q'' R); auto.
      * unfold loop1_ret_assert; destruct R; simpl in *.
        iIntros "(_ & ?)"; iRight; iExists Q', Q''; iFrame; auto.
      * unfold loop1_ret_assert; destruct R.
        rewrite bi.and_elim_r //.
      * unfold loop1_ret_assert; destruct R.
        iIntros "(_ & ?)"; iRight; iExists Q', Q''; iFrame; auto.
      * intros.
        unfold loop1_ret_assert; destruct R.
        rewrite bi.and_elim_r //.
    - apply semax_extract_exists; intros Q'.
      apply semax_extract_exists; intros Q''.
      apply semax_extract_prop; intros [?H ?H].
      apply semax_post with (loop1_ret_assert Q'' R); auto.
      * unfold loop1_ret_assert; destruct R.
        iIntros "(_ & ?)"; iRight; iExists Q', Q''; iFrame; auto.
      * unfold loop1_ret_assert; destruct R.
        rewrite bi.and_elim_r //.
      * unfold loop1_ret_assert; destruct R.
        iIntros "(_ & ?)"; iRight; iExists Q', Q''; iFrame; auto.
      * intros.
        unfold loop1_ret_assert; destruct R.
        rewrite bi.and_elim_r //.
  + apply semax_orp.
    - apply semax_post with (loop2_ret_assert Q R); auto.
      * unfold loop2_ret_assert; destruct R; simpl.
        iIntros "(_ & ?)"; iRight; iLeft; done.
      * unfold loop2_ret_assert; destruct R.
        rewrite bi.and_elim_r //.
      * unfold loop2_ret_assert; destruct R.
        rewrite bi.and_elim_r //.
      * intros.
        unfold loop1_ret_assert; destruct R.
        rewrite bi.and_elim_r //.
    - apply semax_extract_exists; intros Q'.
      apply semax_extract_exists; intros Q''.
      apply semax_extract_prop; intros [?H ?H].
      apply semax_post with (loop2_ret_assert Q' R); auto.
      * unfold loop1_ret_assert; destruct R; simpl.
        iIntros "(_ & ?)"; iRight; iRight; iExists Q', Q''; iFrame; auto.
      * unfold loop1_ret_assert; destruct R.
        rewrite bi.and_elim_r //.
      * unfold loop1_ret_assert; destruct R.
        rewrite bi.and_elim_r //.
      * intros.
        unfold loop1_ret_assert; destruct R.
        rewrite bi.and_elim_r //.
Qed.

Theorem seq_assoc:
   forall E Delta P s1 s2 s3 R,
        semax E Delta P (Ssequence s1 (Ssequence s2 s3)) R <->
        semax E Delta P (Ssequence (Ssequence s1 s2) s3) R.
Proof.
  intros.
  split; intros.
  + apply semax_seq_inv in H as (? & ? & (? & ? & ?)%semax_seq_inv).
    eapply AuxDefs.semax_seq; eauto.
    eapply AuxDefs.semax_seq; eauto.
    destruct R; auto.
  + apply semax_seq_inv in H as (? & (Q & ? & ?)%semax_seq_inv & ?).
    eapply AuxDefs.semax_seq with Q; [destruct R; exact H |].
    eapply AuxDefs.semax_seq; eauto.
Qed.

Theorem semax_seq_skip:
  forall E Delta P s Q,
    semax E Delta P s Q <-> semax E Delta P (Ssequence s Sskip) Q.
Proof.
  intros.
  split; intros.
  + apply AuxDefs.semax_seq with (RA_normal Q).
    - destruct Q; auto.
    - eapply semax_post, AuxDefs.semax_skip.
      * apply ENTAIL_refl.
      * rewrite bi.and_elim_r; apply False_left.
      * rewrite bi.and_elim_r; apply False_left.
      * intros; rewrite bi.and_elim_r; apply False_left.
  + apply semax_seq_inv in H.
    destruct H as [? [? ?]].
    apply semax_skip_inv in H0.
    eapply semax_conseq; [apply derives_full_refl | .. | exact H].
    - destruct Q; auto.
    - destruct Q; apply derives_full_refl.
    - destruct Q; apply derives_full_refl.
    - intros; destruct Q; iIntros "(_ & _ & $)".
Qed.

Theorem semax_skip_seq:
  forall E Delta P s Q,
    semax E Delta P s Q <-> semax E Delta P (Ssequence Sskip s) Q.
Proof.
  intros.
  split; intros.
  + apply AuxDefs.semax_seq with P; auto.
    eapply semax_post, AuxDefs.semax_skip.
    - destruct Q; apply ENTAIL_refl.
    - rewrite bi.and_elim_r; apply False_left.
    - rewrite bi.and_elim_r; apply False_left.
    - intros; rewrite bi.and_elim_r; apply False_left.
  + apply semax_seq_inv in H.
    destruct H as [? [? ?]].
    apply semax_skip_inv in H.
    eapply semax_conseq; [| intros; try apply derives_full_refl .. | exact H0].
    destruct Q; auto.
    { iIntros "(_ & _ & $)". }
Qed.

Theorem semax_seq_Slabel:
     forall E Delta (P:assert) (c1 c2:statement) (Q:ret_assert) l,
   semax E Delta P (Ssequence (Slabel l c1) c2) Q <-> 
   semax E Delta P (Slabel l (Ssequence c1 c2)) Q.
Proof.
  intros.
  split; intros.
  + apply semax_seq_inv in H as (? & ?%semax_Slabel_inv & ?).
    apply AuxDefs.semax_label.
    eapply AuxDefs.semax_seq; eauto.
  + apply semax_Slabel_inv, semax_seq_inv in H as (? & ? & ?).
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
  | Ssequence _ _ => False%type
  | _ => True%type
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

Definition semax_equiv c1 c2: Prop := forall E Delta P Q, semax E Delta P c1 Q <-> semax E Delta P c2 Q.

Lemma semax_equiv_seq: forall c1 c2 c3 c4,
  semax_equiv c1 c2 ->
  semax_equiv c3 c4 ->
  semax_equiv (Ssequence c1 c3) (Ssequence c2 c4).
Proof.
  intros.
  hnf; intros; split; intros Hs.
  + apply semax_seq_inv in Hs as (? & H1 & H2).
    rewrite H in H1.
    rewrite H0 in H2.
    eapply AuxDefs.semax_seq; eauto.
  + apply semax_seq_inv in Hs as (? & H1 & H2).
    rewrite <- (H E Delta P _) in H1.
    rewrite <- (H0 E Delta _ _) in H2.
    eapply AuxDefs.semax_seq; eauto.
Qed.

Lemma semax_equiv_sym: forall c1 c2, semax_equiv c1 c2 -> semax_equiv c2 c1.
Proof.
  intros.
  hnf in H |- *.
  intros; symmetry; auto.
Qed.

Lemma semax_equiv_trans: forall c1 c2 c3, semax_equiv c1 c2 -> semax_equiv c2 c3 -> semax_equiv c1 c3.
Proof.
  intros.
  hnf in H, H0 |- *.
  intros.
  rewrite H //.
Qed.
  
Lemma unfold_Sseq_rel_sound: forall c lc,
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

Lemma unfold_Ssequence_sound: forall c, semax_equiv (fold_Ssequence (unfold_Ssequence c)) c.
Proof.
  intros.
  apply unfold_Sseq_rel_sound.
  apply unfold_Ssequence_unfold_Sseq_rel.
Qed.

Lemma semax_unfold_Ssequence': forall c1 c2,
  unfold_Ssequence c1 = unfold_Ssequence c2 ->
  (forall P Q E Delta, semax E Delta P c1 Q <-> semax E Delta P c2 Q).
Proof.
  intros.
  eapply semax_equiv_trans.
  + apply semax_equiv_sym.
    apply unfold_Ssequence_sound.
  + rewrite H.
    apply unfold_Ssequence_sound.
Qed.

Lemma semax_unfold_Ssequence: forall c1 c2,
  unfold_Ssequence c1 = unfold_Ssequence c2 ->
  (forall P Q E Delta, semax E Delta P c1 Q -> semax E Delta P c2 Q).
Proof.
  intros.
  pose proof semax_unfold_Ssequence' _ _ H.
  clear - H0 H1.
  rewrite -H1 //.
Qed.

Lemma semax_fun_id:
      forall id f E Delta P Q c,
    (var_types Delta) !! id = None ->
    (glob_specs Delta) !! id = Some f ->
    (glob_types Delta) !! id = Some (type_of_funspec f) ->
    semax E Delta (P ∗ assert_of (`(func_ptr f) (eval_var id (type_of_funspec f))))
                  c Q ->
    semax E Delta P c Q.
Proof.
  intros.
  eapply semax_conseq; [| intros; by iIntros "(_ & _ & $)" .. | apply H2].
  reduceR.
  split => rho; monPred.unseal.
  rewrite monPred_at_affinely /allp_fun_id /=; iIntros "(%TC & H & $)".
  unfold_lift; rewrite /eval_var /=.
  iDestruct ("H" with "[%]") as "(% & -> & ?)"; first done.
  destruct TC as (? & Hve & ?).
  specialize (Hve id); rewrite H in Hve.
  destruct (Map.get (ve_of rho) id) as [(?, ?)|]; last done.
  edestruct Hve as [_ Hid]; spec Hid; eauto; done.
Qed.

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
  forall E Delta Pre s Post Post',
    nocontinue s = true ->
    RA_normal Post = RA_normal Post' ->
    RA_break Post = RA_break Post' ->
    RA_return Post = RA_return Post' ->
    semax E Delta Pre s Post -> semax E Delta Pre s Post'.
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
      [intros; rewrite bi.and_elim_r; try apply False_left; rewrite H0; auto .. |].
    apply AuxDefs.semax_call_backward.
  + rewrite H2.
    apply AuxDefs.semax_return.
  + eapply semax_post with (normal_ret_assert P);
      [intros; rewrite bi.and_elim_r; try apply False_left; rewrite H0; auto .. |].
    apply AuxDefs.semax_set_ptr_compare_load_cast_load_backward.
  + eapply semax_post with (normal_ret_assert P);
      [intros; rewrite bi.and_elim_r; try apply False_left; rewrite H0; auto .. |].
    apply AuxDefs.semax_store_store_union_hack_backward.
  + eapply semax_post with (normal_ret_assert P);
      [intros; rewrite bi.and_elim_r; try apply False_left; rewrite H0; auto .. |].
    apply AuxDefs.semax_skip.
  + apply AuxDefs.semax_builtin.
  + specialize (IHsemax H _ H0 H1 H2).
    apply AuxDefs.semax_label; auto.
  + apply AuxDefs.semax_goto.
  + apply (AuxDefs.semax_conseq _ _ P' (Build_ret_assert (RA_normal R') (RA_break R') (RA_continue Post') (RA_return R'))).
    - exact H0.
    - rewrite <- H6; exact H1.
    - rewrite <- H7; exact H2.
    - apply derives_full_refl.
    - intros. rewrite <- H8; exact (H4 vl).
    - apply IHsemax; auto.
  + eapply AuxDefs.semax_mask_mono, IHsemax; auto.
Qed.

Lemma semax_loop_nocontinue1:
  forall E Delta Pre s1 s2 s3 Post
  (Hs1 : nocontinue s1 = true)
  (Hs2 : nocontinue s2 = true)
  (Hs3 : nocontinue s3 = true)
  (H1 : semax E Delta Pre (Sloop (Ssequence s1 (Ssequence s2 s3)) Sskip) Post),
  semax E Delta Pre (Sloop (Ssequence s1 s2) s3) Post.
Proof.
  intros.
  apply semax_loop_inv in H1.
  eapply semax_conseq; [apply H1 | intros; by iIntros "(_ & _ & $)" .. |].
  apply semax_extract_exists; intro Q.
  apply semax_extract_exists; intro Q'.
  apply semax_extract_prop; intros [H2 ?].
  apply seq_assoc, semax_seq_inv in H2 as [Q3 [Hs' Hs3']].
  apply AuxDefs.semax_loop with Q3.
  * assert (nocontinue (Ssequence s1 s2) = true).
    { rewrite /= Hs1 Hs2 //. }
    revert Hs'; apply semax_nocontinue_inv; auto; destruct Post; try reflexivity.
  * apply semax_seq_skip.
    econstructor; eauto.
    revert Hs3'; apply semax_nocontinue_inv; auto; destruct Post; try reflexivity.
Qed.

Lemma semax_convert_for_while':
 forall E Delta Pre s1 e2 s3 s4 s5 Post,
  nocontinue s4 = true ->
  nocontinue s3 = true -> 
  semax E Delta Pre 
    (Ssequence s1 (Ssequence (Swhile e2 (Ssequence s4 s3)) s5)) Post ->
  semax E Delta Pre (Ssequence (Sfor s1 e2 s4 s3) s5) Post.
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
Definition semax_frame := @DeepEmbeddedMinimumSeparationLogic.semax_frame.
Definition semax_adapt_frame := @DeepEmbeddedMinimumSeparationLogic.semax_adapt_frame.
Definition semax_adapt := @DeepEmbeddedMinimumSeparationLogic.semax_adapt.

End mpred.

End DeepEmbeddedPracticalLogic.

End DeepEmbedded.
