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
Local Open Scope logic.

(* Aux *)

Lemma local_andp_bupd: forall P Q,
  (local P && |==> Q) |-- |==> (local P && Q).
Proof.
  intros.
  rewrite !(andp_comm (local P)).
  apply bupd_andp2_corable.
  intro; apply corable_prop.
Qed.

Lemma bupd_andp_local: forall P Q,
  (|==> P) && local Q |-- |==> (P && local Q).
Proof.
  intros.
  apply bupd_andp2_corable.
  intro; apply corable_prop.
Qed.

Lemma derives_bupd_trans: forall TC P Q R,
  local TC && P |-- |==> Q ->
  local TC && Q |-- |==> R ->
  local TC && P |-- |==> R.
Proof.
  intros.
  rewrite (add_andp _ _ H).
  rewrite (andp_comm _ P), andp_assoc; apply andp_left2.
  eapply derives_trans; [apply local_andp_bupd |].
  rewrite (add_andp _ _ H0).
  rewrite (andp_comm _ Q), andp_assoc; eapply derives_trans; [apply bupd_mono, andp_left2, derives_refl |].
  eapply derives_trans; [apply bupd_mono,local_andp_bupd |].
  eapply derives_trans; [apply bupd_trans|].
  apply bupd_mono; solve_andp.
Qed.

(* Aux ends *)

Definition loop2_ret_assert (Inv: environ->mpred) (R: ret_assert) : ret_assert :=
 match R with 
  {| RA_normal := n; RA_break := b; RA_continue := c; RA_return := r |} =>
  {| RA_normal := Inv;
     RA_break := n; 
     RA_continue := seplog.FF;
     RA_return := r |}
 end.

Module NO_EXISTS_PRE.

Inductive semax {CS: compspecs} {Espec: OracleKind} (Delta: tycontext): (environ -> mpred) -> statement -> ret_assert -> Prop :=
| semax_ifthenelse :
   forall P (b: expr) c d R,
      bool_type (typeof b) = true ->
     @semax CS Espec Delta (P && local (`(typed_true (typeof b)) (eval_expr b))) c R ->
     @semax CS Espec Delta (P && local (`(typed_false (typeof b)) (eval_expr b))) d R ->
     @semax CS Espec Delta (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P) (Sifthenelse b c d) R
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
| semax_store: forall e1 e2 sh P,
   writable_share sh ->
   @semax CS Espec Delta
          (|> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) * P)))
          (Sassign e1 e2)
          (normal_ret_assert
             (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) * P))
| semax_skip: forall P, @semax CS Espec Delta P Sskip (normal_ret_assert P)
| semax_pre_post_bupd: forall P' (R': ret_assert) P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- |==> P') ->
    local (tc_environ Delta) && RA_normal R' |-- |==> RA_normal R ->
    local (tc_environ Delta) && RA_break R' |-- |==> RA_break R ->
    local (tc_environ Delta) && RA_continue R' |-- |==> RA_continue R ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- |==> RA_return R vl) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.

(* Copied from canon.v *)

Lemma semax_pre_post : forall {Espec: OracleKind}{CS: compspecs},
 forall P' (R': ret_assert) Delta P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- P') ->
    local (tc_environ Delta) && RA_normal R' |-- RA_normal R ->
    local (tc_environ Delta) && RA_break R' |-- RA_break R ->
    local (tc_environ Delta) && RA_continue R' |-- RA_continue R ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- RA_return R vl) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.
Proof.
  intros; eapply semax_pre_post_bupd; eauto; intros; eapply derives_trans, bupd_intro; auto.
Qed.

Lemma semax_pre_bupd:
 forall P' Espec {cs: compspecs} Delta P c R,
     local (tc_environ Delta) && P |-- |==> P' ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_post_bupd; eauto;
intros; apply andp_left2, bupd_intro; auto.
Qed.

Lemma semax_pre: forall {Espec: OracleKind}{cs: compspecs},
 forall P' Delta P c R,
     local (tc_environ Delta) && P |-- P' ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_bupd; eauto.
eapply derives_trans, bupd_intro; auto.
Qed.

Lemma semax_post_bupd:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   local (tc_environ Delta) && RA_normal R' |-- |==> RA_normal R ->
   local (tc_environ Delta) && RA_break R' |-- |==> RA_break R ->
   local (tc_environ Delta) && RA_continue R' |-- |==> RA_continue R ->
   (forall vl, local (tc_environ Delta) && RA_return R' vl |-- |==> RA_return R vl) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_post_bupd; try eassumption.
apply andp_left2, bupd_intro; auto.
Qed.

Lemma semax_post:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   local (tc_environ Delta) && RA_normal R' |-- RA_normal R ->
   local (tc_environ Delta) && RA_break R' |-- RA_break R ->
   local (tc_environ Delta) && RA_continue R' |-- RA_continue R ->
   (forall vl, local (tc_environ Delta) && RA_return R' vl |-- RA_return R vl) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply andp_left2; auto.
Qed.

(* Copied from canon.v end. *)

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
  exists sh P',
    writable_share sh /\
    local (tc_environ Delta) && P |-- |==> ((|> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  && (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) * P')))) /\
    local (tc_environ Delta) && (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) * P') |-- |==> RA_normal Q.
Proof.
  intros.
  remember (Sassign e1 e2) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    exists sh, P.
    split; [| split]; auto.
    - apply andp_left2, bupd_intro.
    - apply andp_left2, bupd_intro.
  + subst c.
    destruct (IHsemax eq_refl) as [sh [P'' [? [? ?]]]]; clear IHsemax.
    exists sh, P''.
    split; [| split]; auto.
    - eapply derives_bupd_trans; eauto.
    - eapply derives_bupd_trans; eauto.
Qed.

Lemma semax_ifthenelse_inv: forall {Espec: OracleKind}{CS: compspecs} Delta P R b c1 c2,
  @semax CS Espec Delta P (Sifthenelse b c1 c2) R ->
  exists P',
  bool_type (typeof b) = true /\
  @semax CS Espec Delta (P' && local (`(typed_true (typeof b)) (eval_expr b))) c1 R /\
  @semax CS Espec Delta (P' && local (`(typed_false (typeof b)) (eval_expr b))) c2 R /\
  local (tc_environ Delta) && P |-- |==> (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P').
Proof.
  intros.
  remember (Sifthenelse b c1 c2) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0; clear IHsemax1 IHsemax2.
    exists P.
    split; [| split; [| split]]; auto.
    eapply derives_trans; [| apply bupd_intro].
    solve_andp.
  + specialize (IHsemax H0).
    destruct IHsemax as [P'' [? [? [? ?]]]].
    exists P''.
    split; [| split; [| split]].
    - auto.
    - eapply semax_post_bupd; [.. | exact H7]; auto.
    - eapply semax_post_bupd; [.. | exact H8]; auto.
    - eapply derives_bupd_trans; [exact H |].
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
  + eapply semax_post_bupd; [.. | apply semax_skip].
    - change (RA_normal (normal_ret_assert (EX x : A, P x))) with (EX x : A, P x).
      rewrite exp_andp2; apply exp_left.
      intro x.
      specialize (H x).
      apply semax_skip_inv in H.
      auto.
    - apply andp_left2, FF_left.
    - apply andp_left2, FF_left.
    - intro; apply andp_left2, FF_left.
  + eapply semax_pre_post_bupd; [.. |]. Check  semax_store.
    - rewrite exp_andp2; apply exp_left.
      intro; specialize (H x).
      apply semax_store_inv in H.
      destruct H as [sh [P' [? [? ?]]]].
      Fail exact H0.
      admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  + admit.
  + admit.
  + admit.
  + apply semax_seq with (EX Q: environ -> mpred, !! (semax Delta Q c2 R) && Q).
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
  destruct H as [P' [? [? [? ?]]]].
  apply semax_seq_inv in H0.
  apply semax_seq_inv in H1.
  destruct H0 as [Q1 [? ?]], H1 as [Q2 [? ?]].
  apply semax_pre_bupd with (tc_expr Delta (Eunop Cop.Onotbool e (Tint I32 Signed noattr)) && P'); auto.
  apply semax_seq with (orp Q1 Q2); [apply semax_ifthenelse |].
  + auto.
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

End NO_EXISTS_PRE.

Module WITH_EXISTS_PRE.

Lemma veric_semax_store_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext) e1 e2 P,
   @semax CS Espec Delta
          (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* |==> P))))
          (Sassign e1 e2)
          (normal_ret_assert P).
Proof.
  intros.
  eapply semax_pre_post_bupd; [.. | eapply (extract_exists _ _ _ _ (fun _ => normal_ret_assert P))].
  + apply andp_left2, bupd_intro.
  + apply andp_left2.
    change (RA_normal (existential_ret_assert (fun _ : share => normal_ret_assert P))) with (EX _: share, P).
    apply exp_left; intros.
    apply bupd_intro.
  + apply andp_left2.
    change (RA_break (existential_ret_assert (fun _ : share => normal_ret_assert P))) with (EX _: share, FF: environ -> mpred).
    apply exp_left; intros.
    apply FF_left.
  + apply andp_left2.
    change (RA_continue (existential_ret_assert (fun _ : share => normal_ret_assert P))) with (EX _: share, FF: environ -> mpred).
    apply exp_left; intros.
    apply FF_left.
  + intro.
    apply andp_left2.
    change (RA_return (existential_ret_assert (fun _ : share => normal_ret_assert P)) vl) with (EX _: share, FF: environ -> mpred).
    apply exp_left; intros.
    apply FF_left.
  + intros sh.
    apply semax_extract_prop; intro SH.
    eapply semax_pre_post_bupd; [apply andp_left2, bupd_intro | .. | eapply semax_store; auto].
    - apply andp_left2.
      apply modus_ponens_wand.
    - apply andp_left2, FF_left.
    - apply andp_left2, FF_left.
    - intros; apply andp_left2, FF_left.
Qed.

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

(* Copied from canon.v *)

Lemma semax_pre_post : forall {Espec: OracleKind}{CS: compspecs},
 forall P' (R': ret_assert) Delta P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- P') ->
    local (tc_environ Delta) && RA_normal R' |-- RA_normal R ->
    local (tc_environ Delta) && RA_break R' |-- RA_break R ->
    local (tc_environ Delta) && RA_continue R' |-- RA_continue R ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- RA_return R vl) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.
Proof.
  intros; eapply semax_pre_post_bupd; eauto; intros; eapply derives_trans, bupd_intro; auto.
Qed.

Lemma semax_pre_bupd:
 forall P' Espec {cs: compspecs} Delta P c R,
     local (tc_environ Delta) && P |-- |==> P' ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_post_bupd; eauto;
intros; apply andp_left2, bupd_intro; auto.
Qed.

Lemma semax_pre: forall {Espec: OracleKind}{cs: compspecs},
 forall P' Delta P c R,
     local (tc_environ Delta) && P |-- P' ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_bupd; eauto.
eapply derives_trans, bupd_intro; auto.
Qed.

Lemma semax_post_bupd:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   local (tc_environ Delta) && RA_normal R' |-- |==> RA_normal R ->
   local (tc_environ Delta) && RA_break R' |-- |==> RA_break R ->
   local (tc_environ Delta) && RA_continue R' |-- |==> RA_continue R ->
   (forall vl, local (tc_environ Delta) && RA_return R' vl |-- |==> RA_return R vl) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_post_bupd; try eassumption.
apply andp_left2, bupd_intro; auto.
Qed.

Lemma semax_post:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   local (tc_environ Delta) && RA_normal R' |-- RA_normal R ->
   local (tc_environ Delta) && RA_break R' |-- RA_break R ->
   local (tc_environ Delta) && RA_continue R' |-- RA_continue R ->
   (forall vl, local (tc_environ Delta) && RA_return R' vl |-- RA_return R vl) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply andp_left2; auto.
Qed.

(* Copied from canon.v end. *)

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

(* After this succeeds, remove "weakest_pre" in veric/semax.v. *)
