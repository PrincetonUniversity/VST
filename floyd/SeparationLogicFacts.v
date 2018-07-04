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

(* Closed and subst. copied from closed_lemmas.v. *)

Lemma closed_wrt_subst:
  forall {A} id e (P: environ -> A), closed_wrt_vars (eq id) P -> subst id e P = P.
Proof.
intros.
unfold subst, closed_wrt_vars in *.
extensionality rho.
symmetry.
apply H.
intros.
destruct (eq_dec id i); auto.
right.
rewrite Map.gso; auto.
Qed.

(* End of copied from closed_lemmas.v. *)

Definition obox (i: ident) (P: environ -> mpred): environ -> mpred :=
  (fun rho => P (mkEnviron (ge_of rho) (ve_of rho) (Map.remove i (te_of rho)))) &&  ALL v: _, subst i (`v) P.

Definition odia (i: ident) (P: environ -> mpred): environ -> mpred :=
  (fun rho => P (mkEnviron (ge_of rho) (ve_of rho) (Map.remove i (te_of rho)))) || EX v: _, subst i (`v) P.

Lemma subst_obox: forall id v (P: environ -> mpred), subst id (`v) (obox id P) = obox id P.
Proof.
  intros.
  apply closed_wrt_subst.
  hnf; intros.
  unfold obox; simpl.
  f_equal.
  + f_equal.
    f_equal.
    apply Map.ext; intros j.
    destruct (ident_eq id j).
    - subst.
      rewrite !Map.grs; auto.
    - rewrite !Map.gro by congruence.
      destruct (H j); [congruence |].
      auto.
  + apply allp_congr; intros.
    unfold subst.
    simpl.
    f_equal.
    unfold_lift.
    unfold env_set.
    f_equal.
    simpl.
    apply Map.ext; intros j.
    destruct (ident_eq id j).
    - subst.
      rewrite !Map.gss; auto.
    - rewrite !Map.gso by congruence.
      destruct (H j); [congruence |].
      auto.
Qed.

Lemma obox_T: forall i (P: environ -> mpred),
  obox i P |-- P.
Proof.
  intros.
  intro rho; simpl.
  destruct (Map.get (te_of rho) i) eqn:?H.
  + unfold obox; simpl.
    apply andp_left2.
    apply (allp_left _ v).
    unfold subst.
    apply derives_refl'.
    f_equal.
    unfold_lift.
    destruct rho.
    unfold env_set; simpl in *.
    f_equal.
    apply Map.ext; intro j.
    destruct (ident_eq i j).
    - subst.
      rewrite Map.gss; auto.
    - rewrite Map.gso by auto.
      auto.
  + unfold obox; simpl.
    apply andp_left1.
    apply derives_refl'.
    f_equal.
    unfold_lift.
    destruct rho.
    f_equal.
    apply Map.ext; intro j.
    destruct (ident_eq i j).
    - subst.
      rewrite Map.grs; auto.
    - rewrite Map.gro by auto.
      auto.
Qed.

Lemma subst_odia: forall i P,
  EX v: val, subst i (`v) P = odia i P && (fun rho => !! (Map.get (te_of rho) i <> None)).
Proof.
  intros.
  unfold odia.
  apply pred_ext.
  + apply andp_right.
    - apply orp_right2, derives_refl.
    - apply exp_left; intros v rho.
      unfold_lift; unfold subst.
      unfold env_set.
      Abort.
Definition oboxopt ret P :=
  match ret with
  | Some id => obox id P
  | _ => P
  end.

Lemma substopt_oboxopt: forall id v (P: environ -> mpred), substopt id (`v) (oboxopt id P) = oboxopt id P.
Proof.
  intros.
  destruct id; [| auto].
  apply subst_obox.
Qed.

Lemma oboxopt_T: forall i (P: environ -> mpred),
  oboxopt i P |-- P.
Proof.
  intros.
  destruct i; [| apply derives_refl].
  apply obox_T.
Qed.

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

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Parameter semax: forall {CS: compspecs} {Espec: OracleKind},
    tycontext -> (environ->mpred) -> statement -> ret_assert -> Prop.

End CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_pre_post_bupd:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall P' (R': ret_assert) P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- |==> P') ->
    local (tc_environ Delta) && RA_normal R' |-- |==> RA_normal R ->
    local (tc_environ Delta) && RA_break R' |-- |==> RA_break R ->
    local (tc_environ Delta) && RA_continue R' |-- |==> RA_continue R ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- |==> RA_return R vl) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.

End CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE.

Module CSHL_ConseqFacts
       (CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (CSHL_Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := CSHL_Def).

Import CSHL_Def.
Import CSHL_Conseq.

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

Lemma semax_post': forall R' Espec {cs: compspecs} Delta R P c,
           local (tc_environ Delta) && R' |-- R ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Proof. intros. eapply semax_post; eauto.
 simpl RA_normal; auto.
 simpl RA_break; normalize.
 simpl RA_continue; normalize.
 intro vl; simpl RA_return; normalize.
Qed.

Lemma semax_pre_post': forall P' R' Espec {cs: compspecs} Delta R P c,
      local (tc_environ Delta) && P |-- P' ->
      local (tc_environ Delta) && R' |-- R ->
      @semax cs Espec Delta P' c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Proof. intros.
 eapply semax_pre; eauto.
 eapply semax_post'; eauto.
Qed.

(* Copied from canon.v end. *)

End CSHL_ConseqFacts.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_extract_exists:
  forall {CS: compspecs} {Espec: OracleKind},
  forall (A : Type)  (P : A -> environ->mpred) c (Delta: tycontext) (R: ret_assert),
  (forall x, @semax CS Espec Delta (P x) c R) ->
   @semax CS Espec Delta (EX x:A, P x) c R.

Axiom semax_extract_later_prop:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta (PP: Prop) P c Q,
           (PP -> @semax CS Espec Delta P c Q) ->
           @semax CS Espec Delta ((|> !!PP) && P) c Q.

End CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION.

Module CSHL_ExtrFacts
       (CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (CSHL_Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := CSHL_Def)
       (CSHL_Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := CSHL_Def).

Module CSHL_ConseqFacts := CSHL_ConseqFacts (CSHL_Def) (CSHL_Conseq).
Import CSHL_Def.
Import CSHL_Conseq.
Import CSHL_ConseqFacts.
Import CSHL_Extr.

Lemma semax_extract_prop:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta (PP: Prop) P c Q,
           (PP -> @semax CS Espec Delta P c Q) ->
           @semax CS Espec Delta (!!PP && P) c Q.
Proof.
  intros.
  eapply semax_pre; [| apply semax_extract_later_prop, H].
  apply andp_left2.
  apply andp_derives; auto.
  apply now_later.
Qed.

End CSHL_ExtrFacts.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_store_forward:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall e1 e2 sh P,
   writable_share sh ->
   @semax CS Espec Delta
          (|> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) * P)))
          (Sassign e1 e2)
          (normal_ret_assert
             (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) * P)).

End CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_store_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext) e1 e2 P,
   @semax CS Espec Delta
          (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* |==> P))))
          (Sassign e1 e2)
          (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD.

Module CSHL_StoreF2B
       (CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (CSHL_Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := CSHL_Def)
       (CSHL_Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := CSHL_Def)
       (CSHL_StoreF: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD with Module CSHL_Def := CSHL_Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD.

Module CSHL_Def := CSHL_Def.
Module CSHL_ConseqFacts := CSHL_ConseqFacts (CSHL_Def) (CSHL_Conseq).
Module CSHL_ExtrFacts := CSHL_ExtrFacts (CSHL_Def) (CSHL_Conseq) (CSHL_Extr).
Import CSHL_Def.
Import CSHL_Conseq.
Import CSHL_ConseqFacts.
Import CSHL_Extr.
Import CSHL_ExtrFacts.
Import CSHL_StoreF.
  
Theorem semax_store_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext) e1 e2 P,
   @semax CS Espec Delta
          (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* |==> P))))
          (Sassign e1 e2)
          (normal_ret_assert P).
Proof.
  intros.
  eapply semax_post'; [.. | eapply (semax_extract_exists _ _ _ _ (normal_ret_assert P))].
  + apply andp_left2.
    change (RA_normal (existential_ret_assert (fun _ : share => normal_ret_assert P))) with (EX _: share, P).
    apply derives_refl.
  + intros sh.
    apply semax_extract_prop; intro SH.
    eapply semax_post_bupd; [.. | eapply semax_store_forward; auto].
    - apply andp_left2.
      apply modus_ponens_wand.
    - apply andp_left2, FF_left.
    - apply andp_left2, FF_left.
    - intros; apply andp_left2, FF_left.
Qed.

End CSHL_StoreF2B.

Module CSHL_StoreB2F
       (CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (CSHL_Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := CSHL_Def)
       (CSHL_StoreB: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD with Module CSHL_Def := CSHL_Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD.

Module CSHL_Def := CSHL_Def.
Module CSHL_ConseqFacts := CSHL_ConseqFacts (CSHL_Def) (CSHL_Conseq).
Import CSHL_Def.
Import CSHL_Conseq.
Import CSHL_ConseqFacts.
Import CSHL_StoreB.

Theorem semax_store_forward:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall e1 e2 sh P,
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
  normalize.
  apply andp_left2.
  apply later_derives.
  apply andp_derives; auto.
  apply sepcon_derives; auto.
  apply wand_sepcon_adjoint.
  unfold normal_ret_assert, RA_normal.
  rewrite sepcon_comm.
  apply bupd_intro.
Qed.

End CSHL_StoreB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_call_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
    forall A P Q NEP NEQ ts x (F: environ -> mpred) ret argsig retsig cc a bl,
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
            (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).

End CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_call_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
    forall ret a bl R,
  @semax CS Espec Delta
         (EX argsig: _, EX retsig: _, EX cc: _,
          EX A: _, EX P: _, EX Q: _, EX NEP: _, EX NEQ: _, EX ts: _, EX x: _,
         !! (Cop.classify_fun (typeof a) =
             Cop.fun_case_f (type_of_params argsig) retsig cc /\
             (retsig = Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig) &&
          (|>((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>((`(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) * oboxopt ret (maybe_retval (Q ts x) retsig ret -* R)))
         (Scall ret a bl)
         (normal_ret_assert R).

End CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD.

Module CSHL_CallF2B
       (CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (CSHL_Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := CSHL_Def)
       (CSHL_Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := CSHL_Def)
       (CSHL_CallF: CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD with Module CSHL_Def := CSHL_Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD.

Module CSHL_Def := CSHL_Def.
Module CSHL_ConseqFacts := CSHL_ConseqFacts (CSHL_Def) (CSHL_Conseq).
Module CSHL_ExtrFacts := CSHL_ExtrFacts (CSHL_Def) (CSHL_Conseq) (CSHL_Extr).
Import CSHL_Def.
Import CSHL_Conseq.
Import CSHL_ConseqFacts.
Import CSHL_Extr.
Import CSHL_ExtrFacts.
Import CSHL_CallF.
  
Theorem semax_call_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
    forall ret a bl R,
  @semax CS Espec Delta
         (EX argsig: _, EX retsig: _, EX cc: _,
          EX A: _, EX P: _, EX Q: _, EX NEP: _, EX NEQ: _, EX ts: _, EX x: _,
         !! (Cop.classify_fun (typeof a) =
             Cop.fun_case_f (type_of_params argsig) retsig cc /\
             (retsig = Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig) &&
          (|>((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>((`(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) * oboxopt ret (maybe_retval (Q ts x) retsig ret -* R)))
         (Scall ret a bl)
         (normal_ret_assert R).
Proof.
  intros.
  apply semax_extract_exists; intro argsig.
  apply semax_extract_exists; intro retsig.
  apply semax_extract_exists; intro cc.
  apply semax_extract_exists; intro A.
  apply semax_extract_exists; intro P.
  apply semax_extract_exists; intro Q.
  apply semax_extract_exists; intro NEP.
  apply semax_extract_exists; intro NEQ.
  apply semax_extract_exists; intro ts.
  apply semax_extract_exists; intro x.
  rewrite !andp_assoc.
  apply semax_extract_prop; intros [? [? ?]].
  eapply semax_pre_post'; [.. | apply semax_call_forward; auto].
  + apply andp_left2.
    apply andp_derives; [apply derives_refl |].
    apply andp_derives; [apply derives_refl |].
    apply later_derives.
    rewrite sepcon_comm.
    apply derives_refl.
  + unfold RA_normal, normal_ret_assert.
    apply andp_left2.
    apply exp_left; intro old.
    rewrite wand_sepcon_adjoint.
    rewrite substopt_oboxopt.
    apply oboxopt_T.
  + auto.
  + auto.
  + auto.
Qed.

End CSHL_CallF2B.

Module CSHL_CallB2F
       (CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (CSHL_Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := CSHL_Def)
       (CSHL_CallB: CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD with Module CSHL_Def := CSHL_Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD.

Module CSHL_Def := CSHL_Def.
Module CSHL_ConseqFacts := CSHL_ConseqFacts (CSHL_Def) (CSHL_Conseq).
Import CSHL_Def.
Import CSHL_Conseq.
Import CSHL_ConseqFacts.
Import CSHL_CallB.

Theorem semax_call_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
    forall A P Q NEP NEQ ts x (F: environ -> mpred) ret argsig retsig cc a bl,
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
            (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).
Proof.
  intros.
  eapply semax_pre; [| apply semax_call_backward].
  apply (exp_right argsig), (exp_right retsig), (exp_right cc), (exp_right A), (exp_right P), (exp_right Q), (exp_right NEP), (exp_right NEQ), (exp_right ts), (exp_right x).
  apply andp_left2.
  rewrite !andp_assoc.
  apply andp_right; [apply prop_right; auto |].
  apply andp_derives; auto.
  apply andp_derives; auto.
  apply later_derives.
  rewrite sepcon_comm.
  apply sepcon_derives; auto.
  Print tc_environ.
  Print typecheck_environ.