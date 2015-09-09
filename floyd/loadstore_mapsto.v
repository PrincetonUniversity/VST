Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.mapsto_memory_block.

Local Open Scope logic.

(***************************************

Load/store lemmas about mapsto:
  semax_store_nth.
  semax_load_37
  semax_load_37'
  semax_cast_load_37
  semax_cast_load_37'

***************************************)

Lemma semax_store_nth:
forall {Espec: OracleKind} {cs: compspecs} n Delta P Q R e1 e2 Rn sh t1,
  typeof e1 = t1 ->
  nth_error R n = Some Rn ->
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (Rn :: nil))) |--
    `(mapsto_ sh t1) (eval_lvalue e1) ->
  writable_share sh ->
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
     (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 t1)) ->
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
  forall {Espec: OracleKind}{cs: compspecs} ,
forall (Delta: tycontext) sh id P Q R e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
          (tc_lvalue Delta e1) &&
         local (`(tc_val (typeof e1) v2)) &&
         (`(mapsto sh (typeof e1)) (eval_lvalue e1) `v2 * TT) ->
    @semax cs Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
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
    apply derives_extract_prop; intro.
    apply andp_right.
    apply prop_right; repeat split; try eassumption.
    instantiate (1:= `v2). assumption.
    apply andp_right.
    apply andp_left2. apply andp_left1; auto.
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
  forall {Espec: OracleKind}{cs: compspecs} ,
forall (Delta: tycontext) sh id P Q R e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
          (tc_lvalue Delta e1) &&
         local (`(tc_val t1 (eval_cast (typeof e1) t1 v2))) &&
         (`(mapsto sh (typeof e1)) (eval_lvalue e1) `v2 * TT) ->
    @semax cs Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
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
    apply derives_extract_prop; intro.
    apply andp_right.
    apply prop_right; repeat split; eassumption.
    apply andp_right.
    apply andp_left2. apply andp_left1; auto.
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

