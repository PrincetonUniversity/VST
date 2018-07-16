From compcert Require Export Clightdefs.
Require Export VST.veric.SeparationLogic.
Require Export VST.msl.Extensionality.
Require Export compcert.lib.Coqlib.
Require Export VST.msl.Coqlib2 VST.veric.coqlib4 VST.floyd.coqlib3.
Require Export VST.floyd.jmeq_lemmas.
Require Export VST.floyd.find_nth_tactic.
Require Export VST.veric.juicy_extspec.
Require VST.veric.SeparationLogicSoundness.
Export SeparationLogicSoundness.SoundSeparationLogic.CSL.
Require Import VST.veric.NullExtension.
Require Import VST.floyd.SeparationLogicFacts.
Local Open Scope logic.

Module ClightSeparationHoareLogic.

Module AuxDefs.

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
     is_int_type (typeof a) = true ->
     (forall rho, Q rho |-- tc_expr Delta a rho) ->
     (forall n,
     @semax CS Espec Delta 
               (local (`eq (eval_expr a) `(Vint n)) &&  Q)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) ->
     @semax CS Espec Delta Q (Sswitch a sl) R
| semax_call_backward: forall ret a bl R,
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
         (normal_ret_assert R)
| semax_return: forall (R: ret_assert) ret ,
      @semax CS Espec Delta
                ( (tc_expropt Delta ret (ret_type Delta)) &&
                `(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ))
                (Sreturn ret)
                R
| semax_set: forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P))
          (Sset id e) (normal_ret_assert P)
| semax_set_forward: forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
          P))
          (Sset id e)
        (normal_ret_assert
          (EX old:val, local (`eq (eval_id id) (subst id (`old) (eval_expr e))) &&
                            subst id (`old) P))
| semax_ptr_compare: forall P id cmp e1 e2 ty sh1 sh2,
    sepalg.nonidentity sh1 -> sepalg.nonidentity sh2 ->
   is_comparison cmp = true  ->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   typecheck_tid_ptr_compare Delta id = true ->
   @semax CS Espec Delta
        ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&

          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          P))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (EX old:val,
                 local (`eq (eval_id id)  (subst id `(old)
                     (eval_expr (Ebinop cmp e1 e2 ty)))) &&
                            subst id `(old) P))
| semax_load: forall  sh id P e1 t2 (v2: environ -> val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
    local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) v2 * TT ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val (typeof e1)) v2) &&
          P))
       (Sset id e1)
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (subst id (`old) v2)) &&
                                          (subst id (`old) P)))
| semax_cast_load: forall sh id P e1 t1 (v2: environ -> val),
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
    local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) v2 * TT ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val t1) (`(eval_cast (typeof e1) t1) v2)) &&
          P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (subst id (`old) (`(eval_cast (typeof e1) t1) v2))) &&
                                          (subst id (`old) P)))
| semax_store_backward: forall e1 e2 P,
   @semax CS Espec Delta
          (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P))))
          (Sassign e1 e2)
          (normal_ret_assert P)
| semax_skip: forall P, @semax CS Espec Delta P Sskip (normal_ret_assert P)
| semax_builtin: forall P opt ext tl el, @semax CS Espec Delta FF (Sbuiltin opt ext tl el) P
| semax_pre_post_bupd: forall P' (R': ret_assert) P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- |==> P') ->
    local (tc_environ Delta) && RA_normal R' |-- |==> RA_normal R ->
    local (tc_environ Delta) && RA_break R' |-- |==> RA_break R ->
    local (tc_environ Delta) && RA_continue R' |-- |==> RA_continue R ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- |==> RA_return R vl) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.

End AuxDefs.

Module Defs<: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Definition semax: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext), (environ -> mpred) -> statement -> ret_assert -> Prop := @AuxDefs.semax.

End Defs.

Module Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Defs.

Module CSHL_Def := Defs.
Import CSHL_Def.

Definition semax_pre_post_bupd := @AuxDefs.semax_pre_post_bupd.

End Conseq.

Module ConseqFacts := CSHL_ConseqFacts (Defs) (Conseq).

Export Defs Conseq ConseqFacts.

Lemma semax_skip_inv: forall {Espec: OracleKind}{CS: compspecs} Delta P R,
    @semax CS Espec Delta P Sskip R ->
    local (tc_environ Delta) && P |-- |==> RA_normal R.
Proof.
  intros.
  remember Sskip as c eqn:?H.
  induction H; try solve [inv H0].
  + apply andp_left2, bupd_intro.
  + specialize (IHsemax H0).
    eapply derives_bupd_trans; [exact H |].
    eapply derives_bupd_trans; [exact IHsemax |].
    auto.
Qed.

Lemma semax_break_inv: forall {Espec: OracleKind}{CS: compspecs} Delta P R,
    @semax CS Espec Delta P Sbreak R ->
    local (tc_environ Delta) && P |-- |==> RA_break R.
Proof.
  intros.
  remember Sbreak as c eqn:?H.
  induction H; try solve [inv H0].
  + apply andp_left2, bupd_intro.
  + specialize (IHsemax H0).
    eapply derives_bupd_trans; [exact H |].
    eapply derives_bupd_trans; [exact IHsemax |].
    auto.
Qed.

Lemma semax_continue_inv: forall {Espec: OracleKind}{CS: compspecs} Delta P R,
    @semax CS Espec Delta P Scontinue R ->
    local (tc_environ Delta) && P |-- |==> RA_continue R.
Proof.
  intros.
  remember Scontinue as c eqn:?H.
  induction H; try solve [inv H0].
  + apply andp_left2, bupd_intro.
  + specialize (IHsemax H0).
    eapply derives_bupd_trans; [exact H |].
    eapply derives_bupd_trans; [exact IHsemax |].
    auto.
Qed.

Lemma semax_seq_inv: forall {Espec: OracleKind}{CS: compspecs} Delta P R h t,
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
    - apply (semax_pre_post_bupd _ P' (overridePost Q R')); auto.
      * clear.
        destruct R, R'.
        apply andp_left2, bupd_intro.
      * destruct R, R'; auto.
      * destruct R, R'; auto.
      * destruct R, R'; auto.
    - apply (semax_post_bupd R'); auto.
Qed.

Lemma semax_seq_inv': forall {Espec: OracleKind}{CS: compspecs} Delta P R h t,
    @semax CS Espec Delta P (Ssequence h t) R ->
    @semax CS Espec Delta P h (overridePost (EX Q: environ -> mpred, !! (@semax CS Espec Delta Q t R) && Q) R).
Proof.
  intros.
  remember (Ssequence h t) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    clear IHsemax1 IHsemax2.
    eapply semax_post; [.. | exact H].
    - apply andp_left2; destruct R; unfold overridePost, tycontext.RA_normal.
      apply (exp_right Q).
      apply andp_right; [apply prop_right |]; auto.
    - destruct R; apply andp_left2, derives_refl.
    - destruct R; apply andp_left2, derives_refl.
    - intro; destruct R; apply andp_left2, derives_refl.
  + subst c.
    pose proof IHsemax eq_refl. clear IHsemax.
    eapply semax_pre_post_bupd; [.. | exact H0]; auto.
    - unfold overridePost, tycontext.RA_normal.
      destruct R' as [R'0 R'1 R'2 R'3] at 1; clear R'0 R'1 R'2 R'3.
      destruct R as [R0 R1 R2 R3] at 1; clear R0 R1 R2 R3.
      rewrite exp_andp2.
      apply exp_left; intro Q.
      normalize.
      eapply derives_trans; [| apply bupd_intro].
      apply (exp_right Q).
      apply andp_right; [apply prop_right | apply andp_left2; auto].
      eapply semax_post_bupd; [.. | apply H6]; auto.
    - destruct R, R'; auto.
    - destruct R, R'; auto.
    - destruct R, R'; auto.
Qed.

Lemma semax_store_inv: forall {Espec: OracleKind}{CS: compspecs} Delta e1 e2 P Q,
  @semax CS Espec Delta P (Sassign e1 e2) Q ->
  local (tc_environ Delta) && P |-- |==> (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* |==> RA_normal Q)))).
Proof.
  intros.
  remember (Sassign e1 e2) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    apply andp_left2.
    eapply derives_trans; [| apply bupd_intro].
    apply exp_derives; intro sh.
    apply andp_derives; auto.
    apply later_derives; auto.
    apply andp_derives; auto.
    apply sepcon_derives; auto.
    apply wand_derives; auto.
    apply bupd_intro.
  + subst c.
    specialize (IHsemax eq_refl).
    eapply derives_bupd_trans; [exact H | clear H].
    eapply derives_bupd_trans; [exact IHsemax | clear IHsemax].
    intro rho; simpl.
    unfold local, lift1.
    normalize.
    eapply derives_trans; [| apply bupd_intro].
    apply (exp_right x).
    normalize.
    apply later_derives.
    apply andp_derives; auto.
    apply sepcon_derives; auto.
    apply wand_derives; auto.
    specialize (H1 rho).
    unfold local, lift1 in H1; simpl in H1.
    normalize in H1.
    eapply derives_trans; [apply bupd_mono, H1 | apply bupd_trans].
Qed.

Lemma semax_call_inv: forall {Espec: OracleKind}{CS: compspecs} Delta ret a bl Pre Post,
  @semax CS Espec Delta Pre (Scall ret a bl) Post ->
  local (tc_environ Delta) && Pre |-- |==>
         (EX argsig: _, EX retsig: _, EX cc: _,
          EX A: _, EX P: _, EX Q: _, EX NEP: _, EX NEQ: _, EX ts: _, EX x: _,
         !! (Cop.classify_fun (typeof a) =
             Cop.fun_case_f (type_of_params argsig) retsig cc /\
             (retsig = Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig) &&
          (|>((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>((`(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) * oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* |==> RA_normal Post))).
Proof.
  intros.
  remember (Scall ret a bl) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    apply andp_left2.
    eapply derives_trans; [| apply bupd_intro].
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
    apply bupd_intro.
  + subst c.
    rename P into Pre, R into Post.
    specialize (IHsemax eq_refl).
    eapply derives_bupd_trans; [exact H | clear H].
    eapply derives_bupd_trans; [exact IHsemax | clear IHsemax].
    eapply derives_trans; [| apply bupd_intro].
    rewrite exp_andp2; apply exp_derives; intro argsig.
    rewrite exp_andp2; apply exp_derives; intro retsig.
    rewrite exp_andp2; apply exp_derives; intro cc.
    rewrite exp_andp2; apply exp_derives; intro A.
    rewrite exp_andp2; apply exp_derives; intro P.
    rewrite exp_andp2; apply exp_derives; intro Q.
    rewrite exp_andp2; apply exp_derives; intro NEP.
    rewrite exp_andp2; apply exp_derives; intro NEQ.
    rewrite exp_andp2; apply exp_derives; intro ts.
    rewrite exp_andp2; apply exp_derives; intro x.
    apply andp_right; [solve_andp |].
    rewrite andp_comm, imp_andp_adjoint.
    normalize.
    destruct H as [? [? ?]].
    apply andp_left2.
    rewrite <- imp_andp_adjoint, andp_comm.
    apply later_left2.
    rewrite <- corable_sepcon_andp1 by (intro; apply corable_prop).
    apply sepcon_derives; auto.
    apply oboxopt_left2.
      1: destruct ret; hnf in H6 |- *; [destruct ((temp_types Delta) ! i) |]; auto; congruence.
    rewrite <- wand_sepcon_adjoint.
    rewrite corable_andp_sepcon1 by (intro; apply corable_prop).
    rewrite andp_comm, imp_andp_adjoint.
    eapply derives_trans; [rewrite sepcon_comm; apply modus_ponens_wand |].
    rewrite <- imp_andp_adjoint, andp_comm.
    eapply derives_bupd_trans; [| exact H1].
    apply andp_left2; auto.
Qed.

Lemma semax_Sbuiltin_inv: forall {Espec: OracleKind}{CS: compspecs} Delta P R opt ext tl el,
  @semax CS Espec Delta P (Sbuiltin opt ext tl el) R -> local (tc_environ Delta) && P |-- |==> FF.
Proof.
  intros.
  remember (Sbuiltin opt ext tl el) as c eqn:?H.
  induction H; try solve [inv H0].
  + apply andp_left2, FF_left.
  + eapply derives_bupd_trans; [exact H | clear H].
    apply IHsemax in H0; auto.
Qed.

Lemma semax_ifthenelse_inv: forall {Espec: OracleKind}{CS: compspecs} Delta P R b c1 c2,
  @semax CS Espec Delta P (Sifthenelse b c1 c2) R ->
  local (tc_environ Delta) && P |--
  |==> (!! (bool_type (typeof b) = true) && tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) &&
  EX P': environ -> mpred,
  !! (@semax CS Espec Delta (P' && local (`(typed_true (typeof b)) (eval_expr b))) c1 R /\
      @semax CS Espec Delta (P' && local (`(typed_false (typeof b)) (eval_expr b))) c2 R) &&
  P').
Proof.
  intros.
  remember (Sifthenelse b c1 c2) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0; clear IHsemax1 IHsemax2.
    eapply derives_trans; [| apply bupd_intro].
    apply andp_right; [solve_andp |].
    apply (exp_right P).
    apply andp_right; [apply prop_right; auto |].
    solve_andp.
  + specialize (IHsemax H0).
    eapply derives_bupd_trans; [exact H |].
    eapply derives_bupd_trans; [exact IHsemax | clear IHsemax].
    eapply derives_trans; [| apply bupd_intro].
    apply andp_right; [solve_andp |].
    rewrite (andp_comm (local _)); rewrite imp_andp_adjoint; apply andp_left2.
    apply exp_left; intro P''.
    rewrite <- imp_andp_adjoint; rewrite <- (andp_comm (local _)).
    apply (exp_right P'').
    normalize.
    destruct H6.
    apply andp_right; [apply prop_right; split | solve_andp].
    - eapply semax_post_bupd; eauto.
    - eapply semax_post_bupd; eauto.
Qed.

Lemma semax_loop_inv: forall {Espec: OracleKind}{CS: compspecs} Delta P R body incr,
  @semax CS Espec Delta P (Sloop body incr) R ->
  local (tc_environ Delta) && P |--
  |==> EX Q: environ -> mpred, EX Q': environ -> mpred,
  !! (@semax CS Espec Delta Q body (loop1_ret_assert Q' R) /\
      @semax CS Espec Delta Q' incr (loop2_ret_assert Q R)) &&
  Q.
Proof.
  intros.
  remember (Sloop body incr) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0; clear IHsemax1 IHsemax2.
    eapply derives_trans; [| apply bupd_intro].
    apply (exp_right Q).
    apply (exp_right Q').
    apply andp_right; [apply prop_right; auto |].
    solve_andp.
  + specialize (IHsemax H0).
    eapply derives_bupd_trans; [exact H |].
    eapply derives_bupd_trans; [exact IHsemax | clear IHsemax].
    eapply derives_trans; [| apply bupd_intro].
    rewrite exp_andp2; apply exp_left; intros Q.
    rewrite exp_andp2; apply exp_left; intros Q'.
    normalize.
    destruct H6.
    apply (exp_right Q), (exp_right Q').
    apply andp_right; [apply prop_right; split | solve_andp].
    - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR']; simpl in H6, H7 |- *.
      simpl RA_normal in H1; simpl RA_break in H2; simpl RA_continue in H3; simpl RA_return in H4.
      eapply semax_post_bupd; [.. | eassumption]; unfold loop1_ret_assert.
      * simpl RA_normal.
        apply andp_left2, bupd_intro.
      * simpl RA_break.
        auto.
      * simpl RA_continue.
        apply andp_left2, bupd_intro.
      * simpl RA_return.
        auto.
    - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR']; simpl in H6, H7 |- *.
      simpl RA_normal in H1; simpl RA_break in H2; simpl RA_continue in H3; simpl RA_return in H4.
      eapply semax_post_bupd; [.. | eassumption]; unfold loop1_ret_assert.
      * simpl RA_normal.
        apply andp_left2, bupd_intro.
      * simpl RA_break.
        auto.
      * simpl RA_continue.
        apply andp_left2, bupd_intro.
      * simpl RA_return.
        auto.
Qed.    

Lemma extract_exists_pre:
  forall  {Espec: OracleKind}{CS: compspecs} ,
  forall (A : Type)  (P : A -> environ->mpred) c (Delta: tycontext) (R: ret_assert),
  (forall x, @semax CS Espec Delta (P x) c R) ->
   @semax CS Espec Delta (EX x:A, P x) c R.
Proof.
  intros.
  revert A P R H; induction c; intros.
  + eapply semax_post_bupd; [.. | apply AuxDefs.semax_skip].
    - change (RA_normal (normal_ret_assert (EX x : A, P x))) with (EX x : A, P x).
      rewrite exp_andp2; apply exp_left.
      intro x.
      specialize (H x).
      apply semax_skip_inv in H.
      auto.
    - apply andp_left2, FF_left.
    - apply andp_left2, FF_left.
    - intro; apply andp_left2, FF_left.
  + pose proof (fun x => semax_store_inv _ _ _ _ _ (H x)).
    clear H.
    apply exp_left in H0.
    rewrite <- (exp_andp2 A) in H0.
    eapply semax_pre_bupd; [exact H0 | clear H0].
    eapply semax_post''_bupd; [.. | apply AuxDefs.semax_store_backward].
    apply andp_left2, derives_refl.
  + admit.
  + pose proof (fun x => semax_call_inv _ _ _ _ _ _ (H x)).
    clear H.
    apply exp_left in H0.
    rewrite <- (exp_andp2 A) in H0.
    eapply semax_pre_bupd; [exact H0 | clear H0].
    eapply semax_post''_bupd; [.. | apply AuxDefs.semax_call_backward].
    apply andp_left2, derives_refl.
  + pose proof (fun x => semax_Sbuiltin_inv _ _ _ _ _ _ _ (H x)).
    apply semax_pre_bupd with FF; [| apply AuxDefs.semax_builtin].
    rewrite exp_andp2.
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
        normalize.
        apply (exp_right H0).
        auto.
      * apply IHc2.
        intro H0.
        auto.
  + eapply semax_pre_bupd; [| apply (AuxDefs.semax_ifthenelse _ (EX P': environ -> mpred, !! (semax Delta (P' && local (`(typed_true (typeof e)) (eval_expr e))) c1 R /\ semax Delta (P' && local (`(typed_false (typeof e)) (eval_expr e))) c2 R) && P'))].
    - pose proof (fun x => semax_ifthenelse_inv _ _ _ _ _ _ (H x)).
      clear H.
      apply exp_left in H0.
      rewrite <- (exp_andp2 A) in H0.
      eapply derives_bupd_trans; [exact H0 | clear H0].
      apply andp_left2, bupd_intro.
    - rewrite exp_andp1.
      apply IHc1.
      intro P'.
      apply semax_pre with (EX H0: semax Delta (P' && local ((` (typed_true (typeof e))) (eval_expr e))) c1 R, P' && local ((` (typed_true (typeof e))) (eval_expr e))).
      * apply andp_left2.
        normalize.
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
        normalize.
        apply (exp_right (proj2 H0)).
        solve_andp.
      * apply IHc2.
        intro H0.
        auto.
  + pose proof (fun x => semax_loop_inv _ _ _ _ _ (H x)).
    eapply semax_pre_bupd with
      (EX Q : environ -> mpred, EX Q' : environ -> mpred,
         EX H: semax Delta Q c1 (loop1_ret_assert Q' R),
           EX H0: semax Delta Q' c2 (loop2_ret_assert Q R), Q).
    {
      rewrite exp_andp2.
      apply exp_left.
      intros x.
      eapply derives_trans; [apply H0 |].
      apply bupd_mono.
      apply exp_derives; intros Q.
      apply exp_derives; intros Q'.
      normalize.
      destruct H1.
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
      eapply semax_post; [.. | exact H1].
      * destruct R as [nR bR cR rR].
        unfold loop1_ret_assert.
        apply (exp_right Q), (exp_right Q'), (exp_right H1), (exp_right H2).
        apply andp_left2, derives_refl.
      * destruct R as [nR bR cR rR].
        apply andp_left2, derives_refl.
      * destruct R as [nR bR cR rR].
        unfold loop1_ret_assert.
        apply (exp_right Q), (exp_right Q'), (exp_right H1), (exp_right H2).
        apply andp_left2, derives_refl.
      * intros.
        destruct R as [nR bR cR rR].
        apply andp_left2, derives_refl.
    - apply IHc2.
      intros Q.
      apply IHc2.
      intros Q'.
      apply IHc2.
      intros ?H.
      apply IHc2.
      intros ?H.
      eapply semax_post; [.. | exact H2].
      * destruct R as [nR bR cR rR].
        unfold loop1_ret_assert.
        apply (exp_right Q), (exp_right Q'), (exp_right H1), (exp_right H2).
        apply andp_left2, derives_refl.
      * destruct R as [nR bR cR rR].
        apply andp_left2, derives_refl.
      * destruct R as [nR bR cR rR].
        apply andp_left2, derives_refl.
      * intros.
        destruct R as [nR bR cR rR].
        apply andp_left2, derives_refl.
  + pose proof (fun x => semax_break_inv _ _ _ (H x)).
    eapply semax_pre_bupd.
    - rewrite exp_andp2; apply exp_left.
      intro x; apply H0.
    - apply AuxDefs.semax_break.
  + pose proof (fun x => semax_continue_inv _ _ _ (H x)).
    eapply semax_pre_bupd.
    - rewrite exp_andp2; apply exp_left.
      intro x; apply H0.
    - apply AuxDefs.semax_continue.
Admitted.

Lemma semax_extract_prop:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta (PP: Prop) P c Q,
           (PP -> @semax CS Espec Delta P c Q) ->
           @semax CS Espec Delta (!!PP && P) c Q.
Admitted.

Definition loop_nocontinue_ret_assert (Inv: environ->mpred) (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Inv;
     RA_break := n; 
     RA_continue := seplog.FF;
     RA_return := r |}
 end.

Lemma semax_loop_nocontinue:
  forall {Espec: OracleKind}{CS: compspecs} ,
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
 forall {Espec: OracleKind} {CS: compspecs} Delta P e c1 c2 c Q,
 semax Delta P (Sifthenelse e (Ssequence c1 c) (Ssequence c2 c)) Q ->
 semax Delta P (Ssequence (Sifthenelse e c1 c2) c) Q.
Proof.
  intros.
  apply semax_ifthenelse_inv in H.
  eapply semax_pre_bupd; [exact H |].
  rewrite exp_andp2.
  apply extract_exists_pre.
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
    apply extract_exists_pre.
    intro.
    destruct x; auto.
Qed.

End ClightSeparationHoareLogic.
(*
Module WITH_EXISTS_PRE.


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
     is_int_type (typeof a) = true ->
     (forall rho, Q rho |-- tc_expr Delta a rho) ->
     (forall n,
     @semax CS Espec Delta 
               (local (`eq (eval_expr a) `(Vint n)) &&  Q)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) ->
     @semax CS Espec Delta Q (Sswitch a sl) R
| semax_call: forall A P Q NEP NEQ ts x (F: environ -> mpred) ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc ->
           (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
          ((|>((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         (`(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>(F * `(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl)))))
         (Scall ret a bl)
         (normal_ret_assert
          (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret))
| semax_return: forall (R: ret_assert) ret ,
      @semax CS Espec Delta
                ( (tc_expropt Delta ret (ret_type Delta)) &&
                `(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ))
                (Sreturn ret)
                R
| semax_set: forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P))
          (Sset id e) (normal_ret_assert P)
| semax_set_forward: forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
          P))
          (Sset id e)
        (normal_ret_assert
          (EX old:val, local (`eq (eval_id id) (subst id (`old) (eval_expr e))) &&
                            subst id (`old) P))
| semax_ptr_compare: forall P id cmp e1 e2 ty sh1 sh2,
    sepalg.nonidentity sh1 -> sepalg.nonidentity sh2 ->
   is_comparison cmp = true  ->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   typecheck_tid_ptr_compare Delta id = true ->
   @semax CS Espec Delta
        ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&

          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          P))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (EX old:val,
                 local (`eq (eval_id id)  (subst id `(old)
                     (eval_expr (Ebinop cmp e1 e2 ty)))) &&
                            subst id `(old) P))
| semax_load: forall  sh id P e1 t2 (v2: environ -> val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
    local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) v2 * TT ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val (typeof e1)) v2) &&
          P))
       (Sset id e1)
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (subst id (`old) v2)) &&
                                          (subst id (`old) P)))
| semax_cast_load: forall sh id P e1 t1 (v2: environ -> val),
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
    local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) v2 * TT ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val t1) (`(eval_cast (typeof e1) t1) v2)) &&
          P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (subst id (`old) (`(eval_cast (typeof e1) t1) v2))) &&
                                          (subst id (`old) P)))
| semax_store_backward: forall e1 e2 P,
    @semax CS Espec Delta
   (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* |==> P))))
          (Sassign e1 e2)
          (normal_ret_assert P)
| semax_skip: forall P, @semax CS Espec Delta P Sskip (normal_ret_assert P)
| semax_pre_post_bupd: forall P' (R': ret_assert) P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- |==> P') ->
    local (tc_environ Delta) && RA_normal R' |-- |==> RA_normal R ->
    local (tc_environ Delta) && RA_break R' |-- |==> RA_break R ->
    local (tc_environ Delta) && RA_continue R' |-- |==> RA_continue R ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- |==> RA_return R vl) ->
    @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R
| extract_exists_pre:
  forall (A : Type)  (P : A -> environ->mpred) c (R: ret_assert),
  (forall x, @semax CS Espec Delta (P x) c R) ->
   @semax CS Espec Delta (EX x:A, P x) c R
| extract_prop_pre:
  forall (P0: Prop)  (P : environ->mpred) c (R: ret_assert),
  (P0 -> @semax CS Espec Delta P c R) ->
   @semax CS Espec Delta (!! P0 && P) c R.

Lemma semax_skip_inv: forall {Espec: OracleKind}{CS: compspecs} Delta P R,
    @semax CS Espec Delta P Sskip R ->
    local (tc_environ Delta) && P |-- |==> RA_normal R.
Proof.
  intros.
  remember Sskip as c eqn:?H.
  induction H; try solve [inv H0].
  + apply andp_left2, bupd_intro.
  + specialize (IHsemax H0).
    eapply derives_bupd_trans; [exact H |].
    eapply derives_bupd_trans; [exact IHsemax |].
    auto.
  + rewrite exp_andp2; apply exp_left.
    intro x; specialize (H1 x H0).
    auto.
  + normalize.
Qed.

Lemma semax_seq_inv: forall {Espec: OracleKind}{CS: compspecs} Delta P R h t,
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
    - apply (semax_pre_post_bupd _ P' (overridePost Q R')); auto.
      * clear.
        destruct R, R'.
        apply andp_left2, bupd_intro.
      * destruct R, R'; auto.
      * destruct R, R'; auto.
      * destruct R, R'; auto.
    - apply (semax_post_bupd R'); auto.
  + exists (EX x: A, EX Q: environ -> mpred, !! (semax Delta (P x) h (overridePost Q R) /\ semax Delta Q t R) && Q).
    split.
    - apply extract_exists_pre.
      intro x.
      specialize (H x).
      specialize (H1 x H0).
      clear H0.
      destruct H1 as [Q [? ?]].
      eapply semax_post; [.. | exact H0].
      * destruct R; unfold overridePost.
        unfold tycontext.RA_normal.
        apply (exp_right x), (exp_right Q).
        apply andp_right; [apply prop_right |]; auto.
        solve_andp.
      * destruct R; apply andp_left2, derives_refl.
      * destruct R; apply andp_left2, derives_refl.
      * intro; destruct R; apply andp_left2, derives_refl.
    - apply extract_exists_pre.
      intro x.
      apply extract_exists_pre.
      intro Q.
      apply extract_prop_pre.
      intro; tauto.
  + exists (!! P0 && EX Q: environ -> mpred, !! (semax Delta P h (overridePost Q R) /\ semax Delta Q t R) && Q).
    split.
    - apply extract_prop_pre.
      intros.
      specialize (H H2).
      specialize (H1 H2 H0).
      clear H0.
      destruct H1 as [Q [? ?]].
      eapply semax_post; [.. | exact H0].
      * destruct R; unfold overridePost.
        unfold tycontext.RA_normal.
        apply andp_right; [apply prop_right |]; auto.
        apply (exp_right Q).
        apply andp_right; [apply prop_right |]; auto.
        solve_andp.
      * destruct R; apply andp_left2, derives_refl.
      * destruct R; apply andp_left2, derives_refl.
      * intro; destruct R; apply andp_left2, derives_refl.
    - apply extract_prop_pre.
      intros.
      apply extract_exists_pre.
      intro Q.
      apply extract_prop_pre.
      intro; tauto.
Qed.

Lemma semax_store_inv: forall {Espec: OracleKind}{CS: compspecs} Delta e1 e2 P Q,
  @semax CS Espec Delta P (Sassign e1 e2) Q ->
  local (tc_environ Delta) && P |-- |==>
    (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* |==> RA_normal Q)))).
Proof.
  intros.
  remember (Sassign e1 e2) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    apply andp_left2, bupd_intro.
  + subst c.
    specialize (IHsemax eq_refl).
    eapply derives_bupd_trans; eauto.
    eapply derives_bupd_trans; eauto.
    eapply derives_trans; [| apply bupd_intro].
    rewrite exp_andp2; apply exp_left; intro sh; apply (exp_right sh).
    rewrite (andp_comm (local (tc_environ Delta))), !andp_assoc.
    apply andp_derives; [auto |].
    rewrite <- !andp_assoc; rewrite <- (andp_comm (local (tc_environ Delta))).
    apply later_left2.
    rewrite (andp_comm (local (tc_environ Delta))), !andp_assoc.
    apply andp_derives; [auto |].
    apply andp_derives; [auto |].
    rewrite <- (andp_comm (local (tc_environ Delta))).
    rewrite <- corable_sepcon_andp2 by (intro; apply corable_prop).
    apply sepcon_derives; [auto |].
    apply wand_sepcon_adjoint.
    rewrite sepcon_comm, corable_sepcon_andp2 by (intro; apply corable_prop).
    eapply derives_trans; [apply andp_derives; [apply derives_refl | apply modus_ponens_wand] |].
    eapply derives_trans; [apply local_andp_bupd |].
    eapply derives_trans; [apply bupd_mono, H1 |].
    apply bupd_trans.
  + rewrite exp_andp2; apply exp_left.
    intro x.
    apply (H1 x H0).
  + normalize.
Qed.

Lemma semax_ifthenelse_inv: forall {Espec: OracleKind}{CS: compspecs} Delta P R b c1 c2,
  @semax CS Espec Delta P (Sifthenelse b c1 c2) R ->
  exists P',
  @semax CS Espec Delta (P' && local (`(typed_true (typeof b)) (eval_expr b))) c1 R /\
  @semax CS Espec Delta (P' && local (`(typed_false (typeof b)) (eval_expr b))) c2 R /\
  local (tc_environ Delta) && P |-- |==> !! (bool_type (typeof b) = true ) && (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P').
Proof.
  intros.
  remember (Sifthenelse b c1 c2) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0; clear IHsemax1 IHsemax2.
    exists P.
    split; [| split]; auto.
    eapply derives_trans; [| apply bupd_intro].
    solve_andp.
  + specialize (IHsemax H0).
    destruct IHsemax as [P'' [? [? ?]]].
    exists P''.
    split; [| split].
    - eapply semax_post_bupd; [.. | exact H6]; auto.
    - eapply semax_post_bupd; [.. | exact H7]; auto.
    - eapply derives_bupd_trans; [exact H |].
      auto.
  + exists (EX x: A, EX P': environ -> mpred,
     !! (semax Delta (P' && local ((` (typed_true (typeof b))) (eval_expr b))) c1 R /\
         semax Delta (P' && local ((` (typed_false (typeof b))) (eval_expr b))) c2 R /\
         local (tc_environ Delta) && P x
               |-- |==> !! (bool_type (typeof b) = true ) && tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P') && P').
    split; [| split].
    - rewrite exp_andp1; apply extract_exists_pre; intro x.
      rewrite exp_andp1; apply extract_exists_pre; intro P'.
      rewrite !andp_assoc; apply extract_prop_pre.
      tauto.
    - rewrite exp_andp1; apply extract_exists_pre; intro x.
      rewrite exp_andp1; apply extract_exists_pre; intro P'.
      rewrite !andp_assoc; apply extract_prop_pre.
      tauto.
    - rewrite exp_andp2; apply exp_left; intro x.
      specialize (H1 x H0).
      destruct H1 as [P' [? [? ?]]].
      eapply derives_trans; [exact H3 |].
      apply bupd_mono.
      apply andp_derives; auto.
      apply andp_derives; auto.
      apply (exp_right x), (exp_right P').
      apply andp_right; [apply prop_right |]; auto.
      split; [| split]; auto.
      rewrite andp_assoc.
      auto.
  + exists (!! P0 && EX P': environ -> mpred,
     !! (semax Delta (P' && local ((` (typed_true (typeof b))) (eval_expr b))) c1 R /\
         semax Delta (P' && local ((` (typed_false (typeof b))) (eval_expr b))) c2 R /\
         local (tc_environ Delta) && P
               |-- |==> !! (bool_type (typeof b) = true ) && tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P') && P').
    split; [| split].
    - rewrite !andp_assoc; apply extract_prop_pre; intros.
      rewrite exp_andp1; apply extract_exists_pre; intro P'.
      rewrite !andp_assoc; apply extract_prop_pre.
      tauto.
    - rewrite !andp_assoc; apply extract_prop_pre; intros.
      rewrite exp_andp1; apply extract_exists_pre; intro P'.
      rewrite !andp_assoc; apply extract_prop_pre.
      tauto.
    - normalize.
      specialize (H1 H2 H0).
      destruct H1 as [P' [? [? ?]]].
      eapply derives_trans; [exact H4 |].
      apply bupd_mono.
      apply (exp_right P').
      apply andp_derives; auto.
      apply andp_derives; auto.
      normalize.
      apply andp_right; [apply prop_right |]; auto.
      split; [| split]; auto.
      rewrite andp_assoc.
      auto.
Qed.

Definition loop_nocontinue_ret_assert (Inv: environ->mpred) (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Inv;
     RA_break := n; 
     RA_continue := seplog.FF;
     RA_return := r |}
 end.

Lemma semax_loop_nocontinue:
  forall {Espec: OracleKind}{CS: compspecs} ,
 forall Delta P body incr R,
 @semax CS Espec Delta P (Ssequence body incr) (loop_nocontinue_ret_assert P R) ->
 @semax CS Espec Delta P (Sloop body incr) R.
Proof.
  intros.
  apply semax_seq_inv in H.
  destruct H as [Q [? ?]].
  eapply (semax_loop _ P Q).
  + clear - H.
    unfold overridePost, loop_nocontinue_ret_assert, loop1_ret_assert in *.
    eapply semax_pre_post_bupd; [| | | | | exact H].
    - apply andp_left2.
      apply bupd_intro.
    - apply andp_left2.
      destruct R.
      apply bupd_intro.
    - apply andp_left2.
      destruct R.
      apply bupd_intro.
    - apply andp_left2.
      destruct R.
      apply FF_left.
    - intro.
      apply andp_left2.
      destruct R.
      apply bupd_intro.
  + clear - H0.
    unfold overridePost, loop_nocontinue_ret_assert, loop2_ret_assert in *.
    auto.
Qed.

Lemma semax_if_seq:
 forall {Espec: OracleKind} {CS: compspecs} Delta P e c1 c2 c Q,
 semax Delta P (Sifthenelse e (Ssequence c1 c) (Ssequence c2 c)) Q ->
 semax Delta P (Ssequence (Sifthenelse e c1 c2) c) Q.
Proof.
  intros.
  apply semax_ifthenelse_inv in H.
  destruct H as [P' [? [? ?]]].
  apply semax_seq_inv in H.
  apply semax_seq_inv in H0.
  destruct H as [Q1 [? ?]], H0 as [Q2 [? ?]].
  apply semax_pre_bupd with (!! (bool_type (typeof e) = true) && (tc_expr Delta (Eunop Cop.Onotbool e (Tint I32 Signed noattr)) && P')); auto.
  rewrite <- andp_assoc.
  apply semax_seq with (orp Q1 Q2); [apply semax_ifthenelse |].
  + eapply semax_post; [| | | | exact H].
    - destruct Q; apply andp_left2, orp_right1, derives_refl.
    - destruct Q; apply andp_left2, derives_refl.
    - destruct Q; apply andp_left2, derives_refl.
    - intro; destruct Q; apply andp_left2, derives_refl.
  + eapply semax_post; [| | | | exact H0].
    - destruct Q; apply andp_left2, orp_right2, derives_refl.
    - destruct Q; apply andp_left2, derives_refl.
    - destruct Q; apply andp_left2, derives_refl.
    - intro; destruct Q; apply andp_left2, derives_refl.
  + rewrite orp_is_exp.
    apply extract_exists_pre.
    intro.
    destruct x; auto.
Qed.

Lemma semax_store:
  forall {Espec: OracleKind}{CS: compspecs},
 forall Delta e1 e2 sh P,
   writable_share sh ->
   @semax CS Espec Delta
          (|> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) * P)))
          (Sassign e1 e2)
          (normal_ret_assert
               (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) * P)).
Proof.
  intros.
  eapply semax_pre; [| apply semax_store_backward].
  apply (exp_right sh).
  apply andp_right; [apply prop_right; auto |].
  apply andp_left2, later_derives.
  apply andp_derives; auto.
  apply sepcon_derives; auto.
  rewrite <- wand_sepcon_adjoint.
  rewrite sepcon_comm; apply bupd_intro.
Qed.

Lemma semax_frame:
  forall {Espec: OracleKind}{CS: compspecs},
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
      apply semax_ifthenelse.
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
    apply semax_seq with (Q * F).
    - destruct R; apply IHsemax1; auto.
    - destruct R; apply IHsemax2; auto.
  + replace (RA_break Q * F) with (RA_break (frame_ret_assert Q F)) by (destruct Q; auto).
    apply semax_break.
  + replace (RA_continue Q * F) with (RA_continue (frame_ret_assert Q F)) by (destruct Q; auto).
    apply semax_continue.
  + rewrite semax_lemmas.closed_Sloop in H; destruct H.
    eapply semax_loop with (Q' * F).
    - destruct R; apply IHsemax1; auto.
    - replace (loop2_ret_assert (Q * F) (frame_ret_assert R F))
        with (frame_ret_assert (loop2_ret_assert Q R) F)
        by (destruct R; simpl; f_equal; extensionality rho; apply pred_ext; normalize).
      apply IHsemax2; auto.
  + eapply semax_switch; auto.
    - intro.
      eapply derives_trans; [apply sepcon_derives; [apply H1 | apply derives_refl] |].
      apply (predicates_sl.extend_sepcon (extend_tc.extend_tc_expr Delta a rho)).
    - intros.
      rewrite <- corable_andp_sepcon1 by (intro; apply corable_prop).
      replace (switch_ret_assert (frame_ret_assert R F)) with
        (frame_ret_assert (switch_ret_assert R) F)
        by (destruct R; simpl; f_equal; extensionality rho; apply pred_ext; normalize).
      apply (H3 n).
      eapply semax_lemmas.closed_Sswitch; eauto.
  + eapply semax_pre_post; [.. | apply (semax_call Delta A P Q NEP NEQ ts x (F0 * F) ret argsig retsig cc a bl); auto].
    - apply andp_left2.
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply now_later] |].
      apply andp_right; [| apply andp_right].
      * apply wand_sepcon_adjoint.
        apply andp_left1.
        apply wand_sepcon_adjoint.
        rewrite <- later_sepcon.
        apply later_derives.
        intro rho.
        simpl.
        apply (predicates_sl.extend_sepcon (extend_tc.extend_andp _ _ (extend_tc.extend_tc_expr Delta a rho) (extend_tc.extend_tc_exprlist Delta (snd (split argsig)) bl rho))).
      * apply wand_sepcon_adjoint.
        apply andp_left2, andp_left1.
        apply wand_sepcon_adjoint.
        apply derives_left_sepcon_right_corable; auto.
        intro.
        apply corable_func_ptr.
      * apply wand_sepcon_adjoint.
        apply andp_left2, andp_left2.
        apply wand_sepcon_adjoint.
        rewrite <- later_sepcon.
        apply later_derives.
        rewrite (sepcon_comm _ F), <- sepcon_assoc, (sepcon_comm F0).
        auto.
    - apply andp_left2.
      unfold RA_normal, normal_ret_assert, frame_ret_assert.
      apply (exp_left); intros old.
      rewrite exp_sepcon1.
      apply (exp_right old).
      rewrite (sepcon_comm (_ * _) F), <- sepcon_assoc, (sepcon_comm _ F).
      apply sepcon_derives; auto.
      unfold substopt.
      destruct ret; auto.
      unfold subst.
Abort.

End WITH_EXISTS_PRE.
*)
(* After this succeeds, remove "weakest_pre" in veric/semax.v. *)
