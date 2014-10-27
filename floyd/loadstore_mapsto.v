Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.mapsto_memory_block.

Local Open Scope logic.

(***************************************

Auxilliary Lemmas

***************************************)

Lemma remove_PROP_LOCAL_left: forall P Q R S, R |-- S -> PROPx P (LOCALx Q R) |-- S.
Proof.
  intros.
  go_lower.
  normalize.
Qed.

Lemma remove_PROP_LOCAL_left': forall P Q R S, R |-- S -> PROPx P (LOCALx Q SEP (R)) |-- S.
Proof.
  intros.
  go_lower.
  normalize.
Qed.

Lemma SEP_nth_isolate:
  forall n R Rn, nth_error R n = Some Rn ->
      SEPx R = SEPx (Rn :: replace_nth n R emp).
Proof.
 unfold SEPx.
 induction n; destruct R; intros; inv H; extensionality rho.
 simpl; rewrite emp_sepcon; auto.
 unfold replace_nth; fold @replace_nth.
 transitivity (m rho * fold_right sepcon emp R rho).
 reflexivity.
 rewrite (IHn R Rn H1).
 simpl.
 rewrite <- sepcon_assoc.
 rewrite (sepcon_comm (Rn rho)).
 simpl.
 repeat rewrite sepcon_assoc.
 f_equal. rewrite sepcon_comm; reflexivity.
Qed.

Lemma nth_error_SEP_sepcon_TT: forall P Q R n Rn S,
  PROPx P (LOCALx Q (SEPx (Rn :: nil))) |-- S ->
  nth_error R n = Some Rn ->
  PROPx P (LOCALx Q (SEPx R)) |-- S * TT.
Proof.
  intros.
  erewrite SEP_nth_isolate by eauto.
  unfold PROPx, LOCALx, SEPx in *.
  unfold local, lift1 in H |- *.
  unfold_lift in H.
  unfold_lift.
  simpl in H |- *.
  intros rho.
  specialize (H rho).
  rewrite <- !andp_assoc in H |- *.
  rewrite <- !prop_and in H |- *.
  rewrite sepcon_emp in H.
  rewrite <- sepcon_andp_prop'.
  apply sepcon_derives.
  exact H.
  apply prop_right.
  auto.
Qed.

Lemma SEP_replace_nth_isolate:
  forall n R Rn Rn', 
       nth_error R n = Some Rn ->
      SEPx (replace_nth n R Rn') = SEPx (Rn' :: replace_nth n R emp).
Proof.
 unfold SEPx.
 intros.
 revert R H.
 induction n; destruct R; intros; inv H; intros; extensionality rho.
 simpl; rewrite emp_sepcon; auto.
 unfold replace_nth; fold @replace_nth.
 transitivity (m rho * fold_right sepcon emp (replace_nth n R Rn') rho).
 reflexivity.
 rewrite (IHn R H1). clear IHn.
 simpl.
 repeat rewrite <- sepcon_assoc.
 rewrite (sepcon_comm (Rn' rho)).
 rewrite sepcon_assoc.
 reflexivity.
Qed.

Lemma replace_nth_replace_nth: forall {A: Type} R n {Rn Rn': A},
  replace_nth n (replace_nth n R Rn) Rn' = replace_nth n R Rn'.
Proof.
  intros.
  revert R; induction n; destruct R; simpl in *.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + rewrite IHn.
    reflexivity.
Qed.

Lemma local_andp_lemma:
  forall P Q, P |-- local Q -> P = local Q && P.
Proof.
intros.
apply pred_ext.
apply andp_right; auto.
apply andp_left2; auto.
Qed.

Lemma SEP_TT_right:
  forall R, R |-- SEP(TT).
Proof. intros. go_lowerx. rewrite sepcon_emp. apply TT_right.
Qed.

Lemma replace_nth_SEP: forall P Q R n Rn Rn', Rn |-- Rn' -> PROPx P (LOCALx Q (SEPx (replace_nth n R Rn))) |-- PROPx P (LOCALx Q (SEPx (replace_nth n R Rn'))).
Proof.
  simpl.
  intros.
  specialize (H x).
  normalize.
  revert R.
  induction n.
  + destruct R.
    - simpl. cancel.
    - simpl. cancel.
  + destruct R.
    - simpl. cancel.
    - intros. simpl in *. cancel.
Qed.

Lemma replace_nth_SEP': forall P Q R n Rn Rn', PROPx P (LOCALx Q (SEP (Rn))) |-- Rn' -> (PROPx P (LOCALx Q (SEPx (replace_nth n R Rn)))) |-- (PROPx P (LOCALx Q (SEPx (replace_nth n R Rn')))).
Proof.
  simpl.
  intros.
  specialize (H x).
  normalize.
  normalize in H.
  revert R.
  induction n.
  + destruct R.
    - simpl. cancel.
    - simpl. cancel.
  + destruct R.
    - simpl. cancel.
    - intros. simpl in *. cancel.
Qed.

Lemma replace_nth_SEP_andp_local': forall P Q R n Rn (Rn': environ -> mpred) Rn'' x,
  nth_error R n = Some Rn ->
  (PROPx P (LOCALx Q (SEPx (replace_nth n R ((`prop Rn'') && Rn'))))) x
  = (PROPx P (LOCALx (Rn'' :: Q) (SEPx (replace_nth n R Rn')))) x.
Proof.
  intros.
  normalize.
  assert ((@fold_right (environ -> mpred) (environ -> mpred)
              (@sepcon (environ -> mpred) (@LiftNatDed' mpred Nveric)
                 (@LiftSepLog' mpred Nveric Sveric))
              (@emp (environ -> mpred) (@LiftNatDed' mpred Nveric)
                 (@LiftSepLog' mpred Nveric Sveric))
              (@replace_nth (lifted (LiftEnviron mpred)) n R
                 (@andp (lifted (LiftEnviron mpred))
                    (@LiftNatDed' mpred Nveric)
                    (@liftx (Tarrow Prop (LiftEnviron mpred))
                       (@prop (lift_T (LiftEnviron mpred)) Nveric) Rn'') Rn'))
              x) =
   (@andp mpred Nveric
           (@prop mpred Nveric
              (Rn'' x))
           (@fold_right (environ -> mpred) (environ -> mpred)
              (@sepcon (environ -> mpred) (@LiftNatDed' mpred Nveric)
                 (@LiftSepLog' mpred Nveric Sveric))
              (@emp (environ -> mpred) (@LiftNatDed' mpred Nveric)
                 (@LiftSepLog' mpred Nveric Sveric))
              (@replace_nth (lifted (LiftEnviron mpred)) n R Rn') x))); 
  [| rewrite H0; apply pred_ext; normalize].

  revert R H.
  induction n; intros.
  + destruct R; inversion H.
    subst l.
    simpl. normalize.
  + destruct R; inversion H.
    pose proof IHn R H1.
    unfold replace_nth in *.
    fold (@replace_nth (LiftEnviron mpred)) in *.
    simpl fold_right in *.
    rewrite <- sepcon_andp_prop, H0.
    reflexivity.
Qed.

Lemma replace_nth_SEP_andp_local: forall P Q R n Rn (Rn': environ -> mpred) Rn'',
  nth_error R n = Some Rn ->
  (PROPx P (LOCALx Q (SEPx (replace_nth n R ((`prop Rn'') && Rn')))))
  = (PROPx P (LOCALx (Rn'' :: Q) (SEPx (replace_nth n R Rn')))).
Proof.
  intros.
  extensionality.
  eapply replace_nth_SEP_andp_local'.
  exact H.
Qed.

Lemma replace_nth_nth_error: forall {A:Type} R n (Rn:A), 
  nth_error R n = Some Rn ->
  R = replace_nth n R Rn.
Proof.
  intros.
  revert R H; induction n; intros; destruct R.
  + reflexivity.
  + simpl. inversion H. reflexivity.
  + inversion H.
  + inversion H. simpl.
    rewrite (IHn R) at 1; simpl; [reflexivity|exact H1].
Qed.

Lemma nth_error_replace_nth: forall {A:Type} R n (Rn Rn':A), 
  nth_error R n = Some Rn ->
  nth_error (replace_nth n R Rn') n = Some Rn'.
Proof.
  intros.
  revert R H; induction n; intros; destruct R; simpl.
  + inversion H.
  + inversion H.
    reflexivity.
  + inversion H.
  + inversion H.
    apply IHn, H1.
Qed.

Lemma LOCAL_2_hd: forall P Q R Q1 Q2,
  (PROPx P (LOCALx (Q1 :: Q2 :: Q) (SEPx R))) = 
  (PROPx P (LOCALx (Q2 :: Q1 :: Q) (SEPx R))).
Proof.
  intros.
  extensionality.
  apply pred_ext; normalize.
Qed.

Lemma eq_sym_LOCAL: forall P Q R id v, 
  PROPx P (LOCALx (`eq v (eval_id id) :: Q) (SEPx R)) = 
  PROPx P (LOCALx (`eq (eval_id id) v:: Q) (SEPx R)).
Proof.
  intros.
  extensionality; apply pred_ext; normalize.
Qed.

Lemma eq_sym_LOCAL': forall P Q R id v, 
  PROPx P (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)) = 
  PROPx P (LOCALx (`eq (eval_id id) `v:: Q) (SEPx R)).
Proof.
  intros.
  normalize.
Qed.

(* This lemma is for load_37 *)
Lemma eq_sym_post_LOCAL: forall P Q R id v,
  (EX  old : val, PROPx P
  (LOCALx (`eq (subst id `old v) (eval_id id)::map (subst id `old) Q) (SEPx (map (subst id `old) R)))) = 
  (EX  old : val, PROPx P
  (LOCALx (`eq (eval_id id) (subst id `old v)::map (subst id `old) Q) (SEPx (map (subst id `old) R)))).
Proof.
  intros.
  apply pred_ext; normalize; apply (exp_right old);
  rewrite eq_sym_LOCAL; apply derives_refl.
Qed.

(* This lemma is for load_37' *)
Lemma eq_sym_post_LOCAL': forall P Q R id v,
  (EX  old : val, PROPx P
  (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q) (SEPx (map (subst id `old) R)))) = 
  (EX  old : val, PROPx P
  (LOCALx (`eq (eval_id id) `v ::  map (subst id `old) Q) (SEPx (map (subst id `old) R)))).
Proof.
  intros.
  apply pred_ext; normalize; apply (exp_right old);
  rewrite eq_sym_LOCAL'; apply derives_refl.
Qed.

(***************************************

Load/store lemmas about mapsto:
  semax_store_nth.
  semax_load_37
  semax_load_37'
  semax_cast_load_37
  semax_cast_load_37'

***************************************)

Lemma semax_store_nth:
forall {Espec: OracleKind} n Delta P Q R e1 e2 Rn sh t1,
  typeof e1 = t1 ->
  nth_error R n = Some Rn ->
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (Rn :: nil))) |--
    `(mapsto_ sh t1) (eval_lvalue e1) ->
  writable_share sh ->
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
    local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t1)) ->
  semax Delta 
      (|> PROPx P (LOCALx Q (SEPx R)))
      (Sassign e1 e2) 
      (normal_ret_assert
         (PROPx P (LOCALx Q (SEPx (replace_nth n R
           (`(mapsto sh t1) (eval_lvalue e1) (eval_expr (Ecast e2 t1)) )))))).
Proof.
  intros.
  subst t1.
  eapply semax_pre_post ; [ | | 
    apply  (semax_store Delta e1 e2 sh 
    (PROPx P (LOCALx Q (SEPx (replace_nth n R emp)))) H2)].
  + hoist_later_left.
    apply later_derives.
    repeat rewrite insert_local.
    apply andp_right; [exact H3 |].

    rewrite insert_SEP.
    erewrite <- SEP_replace_nth_isolate by eauto.
    rewrite (replace_nth_nth_error R _ _ H0) at 1.
    eapply derives_trans; [apply replace_nth_SEP', H1|].
    simpl; intros; normalize.
  + intros.
    apply andp_left2.
    apply normal_ret_assert_derives'.
    rewrite insert_SEP.
    apply andp_derives; auto.
    apply andp_derives; auto.
    rewrite (SEP_replace_nth_isolate _ _ _ _ H0).
    auto.
Qed.

Definition semax_load_37 := @semax_load. 

Lemma semax_load_37' : 
  forall {Espec: OracleKind},
forall (Delta: tycontext) sh id P Q R e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
         local (tc_lvalue Delta e1) &&
         local (`(tc_val (typeof e1) v2)) &&
         (`(mapsto sh (typeof e1)) (eval_lvalue e1) `v2 * TT) ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id e1)
       (normal_ret_assert (EX old:val, 
             PROPx P 
   (LOCALx (`(eq v2) (eval_id id) :: map (subst id (`old)) Q)
     (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  eapply semax_pre_post; [ | | apply semax_load with sh t2; auto].
  + instantiate (1:= PROPx P (LOCALx Q (SEPx R))).
    apply later_left2.
    rewrite insert_local.
    rewrite <- (andp_dup (PROPx P (LOCALx (_ :: _) _))).
    eapply derives_trans.
    apply andp_derives; [apply derives_refl | apply H1].
    clear H.
    go_lowerx.
    autorewrite with gather_prop.
    apply derives_extract_prop; intros [? ?].
    apply andp_right.
    apply prop_right; repeat split; try eassumption.
    instantiate (1:= `v2). apply H5.
    apply andp_left1; auto.
  + rewrite eq_sym_post_LOCAL'.
    intros. apply andp_left2; auto.
    apply normal_ret_assert_derives'.
    apply exp_derives; intro old.
    autorewrite with subst.
    rewrite insert_local.
    apply andp_derives; auto.
  + rewrite insert_local.
    eapply derives_trans; [apply H1 | clear H1].
    apply andp_left2. auto.
Qed.

Definition semax_cast_load_37 := @semax_cast_load. 

Lemma semax_cast_load_37' : 
  forall {Espec: OracleKind},
forall (Delta: tycontext) sh id P Q R e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
         local (tc_lvalue Delta e1) &&
         local (`(tc_val t1 (eval_cast (typeof e1) t1 v2))) &&
         (`(mapsto sh (typeof e1)) (eval_lvalue e1) `v2 * TT) ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (EX old:val, 
             PROPx P 
   (LOCALx (`(eq (eval_cast (typeof e1) t1 v2)) (eval_id id) :: map (subst id (`old)) Q)
     (SEPx (map (subst id (`old)) R))))).
Proof.
  intros. rename H0 into H1; pose proof I.
  eapply semax_pre_post; [ | | apply semax_cast_load with (sh0:=sh)(v3:= `v2); auto].
  * instantiate (1:= PROPx P (LOCALx Q (SEPx R))).
    apply later_left2.
    rewrite insert_local.
    rewrite <- (andp_dup (PROPx P (LOCALx (_ :: _) _))).
    eapply derives_trans.
    apply andp_derives; [apply derives_refl | apply H1].
    clear H1.
    go_lowerx.
    autorewrite with gather_prop.
    apply derives_extract_prop; intros [? ?].
    apply andp_right.
    apply prop_right; repeat split; eassumption.
    apply andp_left1; auto.
  * rewrite eq_sym_post_LOCAL'.
    intros. apply andp_left2; auto.
    apply normal_ret_assert_derives'.
    apply exp_derives; intro old.
    autorewrite with subst.
    rewrite insert_local.
    apply andp_derives; auto.
  * rewrite insert_local.
    eapply derives_trans; [apply H1 | clear H1].
    apply andp_left2. auto.
Qed.

