Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.closed_lemmas.
Require Import Coq.Logic.JMeq.

Local Open Scope logic.

(***************************************

In this file, only load lemmas about mapsto has postcondition as
  `eq (eval_id id) `v
In other load lemmas, postconditions are like the following. It offers some
convenience about in setx_wow.
  `(eq v)  (eval_id id)

***************************************)

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

Lemma replace_nth_SEP': forall P Q R n Rn Rn' x, Rn x |-- Rn' x -> (PROPx P (LOCALx Q (SEPx (replace_nth n R Rn)))) x |-- (PROPx P (LOCALx Q (SEPx (replace_nth n R Rn')))) x.
Proof.
  intros.
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

Lemma replace_nth_SEP: forall P Q R n Rn Rn', Rn |-- Rn' -> PROPx P (LOCALx Q (SEPx (replace_nth n R Rn))) |-- PROPx P (LOCALx Q (SEPx (replace_nth n R Rn'))).
Proof.
  simpl; intros.
  apply replace_nth_SEP'.
  apply H.
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
  semax_store_nth'.
  semax_load_37
  semax_load_37'
  semax_cast_load_37
  semax_cast_load_37'

***************************************)

Lemma semax_store_nth:
forall {Espec: OracleKind} n Delta P Q R e1 e2 Rn sh t1,
   typeof e1 = t1 ->
   nth_error R n = Some Rn ->
   Rn |-- `(mapsto_ sh t1) (eval_lvalue e1) ->
   forall (WS: writable_share sh),
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
                 local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t1)) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sassign e1 e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q (SEPx (replace_nth n R
              (`(mapsto sh t1) (eval_lvalue e1) 
                  (`force_val (`(sem_cast (typeof e2) t1) (eval_expr e2))))))))).
Proof.
intros.
subst t1.
eapply semax_pre_post ; [ | | 
 apply  (semax_store Delta e1 e2 sh 
       (PROPx P (LOCALx Q (SEPx (replace_nth n R emp)))) WS)].
apply later_left2.
repeat rewrite insert_local.
apply andp_right. auto.
rewrite <- insert_local.
apply andp_left2.
rewrite insert_SEP.
apply andp_derives; auto.
apply andp_derives; auto.
rewrite (SEP_nth_isolate _ _ _ H0).
go_lowerx; apply sepcon_derives; auto.
apply H1.
intros.
apply andp_left2.
apply normal_ret_assert_derives'.
rewrite insert_SEP.
apply andp_derives; auto.
apply andp_derives; auto.
rewrite (SEP_replace_nth_isolate _ _ _ _ H0).
auto.
Qed.

Lemma semax_store_nth':
  forall {Espec: OracleKind},
    forall (n : nat) (Delta : tycontext) (P : list Prop)
         (Q : list (environ -> Prop)) (R : list (LiftEnviron mpred))
         (e1 e2 : expr) (Rn : LiftEnviron mpred) (sh : Share.t) 
         (t1 : type),
       typeof e1 = t1 ->
       nth_error R n = Some Rn ->
       Rn |-- `(mapsto_ sh t1) (eval_lvalue e1) ->
       writable_share sh ->
       PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
       |-- local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t1)) ->
       semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
         (Sassign e1 e2)
         (normal_ret_assert
            (PROPx P
               (LOCALx Q
                  (SEPx
                     (replace_nth n R
                        (`(mapsto sh t1) (eval_lvalue e1)
                           (eval_expr (Ecast e2 t1)) )))))).
Proof.
  intros.
  simpl (eval_expr (Ecast e2 t1)).
  unfold force_val1.
  eapply semax_store_nth.
  + exact H.
  + exact H0.
  + exact H1.
  + exact H2.
  + exact H3.
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
   (LOCALx (`eq (eval_id id) `v2 :: map (subst id (`old)) Q)
     (SEPx (map (subst id (`old)) R))))).
Proof.
intros.
eapply semax_pre_post; [ | | apply semax_load with sh t2; auto].
* instantiate (1:= PROPx P (LOCALx Q (SEPx R))).
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
* intros. apply andp_left2; auto.
  apply normal_ret_assert_derives'.
  apply exp_derives; intro old.
  autorewrite with subst.
  rewrite insert_local.
  apply andp_derives; auto.
* rewrite insert_local.
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
   (LOCALx (`eq (eval_id id) `(eval_cast (typeof e1) t1 v2) :: map (subst id (`old)) Q)
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
* intros. apply andp_left2; auto.
  apply normal_ret_assert_derives'.
  apply exp_derives; intro old.
  autorewrite with subst.
  rewrite insert_local.
  apply andp_derives; auto.
* rewrite insert_local.
  eapply derives_trans; [apply H1 | clear H1].
  apply andp_left2. auto.
Qed.

(***************************************

Load/store lemmas about data_at:
  semax_data_load_37'.
  semax_data_cast_load_37'.
  semax_data_store_nth.

***************************************)

Lemma is_neutral_cast_by_value: forall t t', 
  is_neutral_cast t t' = true ->
  type_is_by_value t.
Proof.
  intros.
  destruct t, t'; try inversion H; simpl; auto.
Qed.

Lemma is_neutral_reptype: forall t t', is_neutral_cast t t' = true -> reptype t = val.
Proof.
  intros.
  eapply by_value_reptype, is_neutral_cast_by_value, H.
Qed.

Lemma look_up_empty_ti: forall i, look_up_ident_default i empty_ti = Tvoid.
Proof.
  intros.
  unfold look_up_ident_default.
  rewrite PTree.gempty.
  reflexivity.
Qed.

Lemma is_neutral_data_at: forall sh t t' v v' p,
  is_neutral_cast t t' = true ->
  JMeq v v' ->
  data_at sh t v p = (!! size_compatible t p) && (!! align_compatible t p) && mapsto sh t p v'.
Proof.
  intros.
  apply by_value_data_at; try assumption.
  eapply is_neutral_cast_by_value, H.
Qed.

Lemma is_neutral_lifted_data_at: forall sh t t' v (v':val) (p: environ -> val),
  is_neutral_cast t t' = true ->
  JMeq v v' ->
  `(data_at sh t v) p = `prop (`(size_compatible t) p) && `prop (`(align_compatible t) p) && `(mapsto sh t) p `(v').
Proof.
  intros.
  unfold liftx, lift. simpl.
  extensionality.
  erewrite is_neutral_data_at; [| exact H| exact H0].
  reflexivity.
Qed.

Lemma is_neutral_data_at_: forall sh t t' p, 
  is_neutral_cast t t' = true ->
  data_at_ sh t p = (!! size_compatible t p) && (!! align_compatible t p) && mapsto_ sh t p.
Proof.
  intros.
  apply by_value_data_at_; try assumption.
  eapply is_neutral_cast_by_value, H.
Qed.

Lemma is_neutral_lifted_data_at_: forall sh t t' p,
  is_neutral_cast t t' = true ->
  `(data_at_ sh t) p = `prop (`(size_compatible t) p) &&
  `prop (`(align_compatible t) p) && `(mapsto_ sh t) p.
Proof.
  intros.
  unfold liftx, lift. simpl.
  extensionality.
  eapply is_neutral_data_at_; try assumption.
  exact H.
Qed.

Lemma semax_data_load_37:
  forall {Espec: OracleKind},
    forall Delta sh id P Q R (e1 : expr)
    (t: type) (v: environ -> val),
    typeof_temp Delta id = Some t ->
    is_neutral_cast (typeof e1) t = true ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
      local (tc_lvalue Delta e1) && local (`(tc_val (typeof e1)) v) &&
      (`(data_at sh (typeof e1)) (`(valinject (typeof e1)) v) (eval_lvalue e1) * TT) ->
    semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
      (Sset id e1)
        (normal_ret_assert
          (EX  old : val,
            PROPx P
              (LOCALx (`(eq) (subst id `old v) (eval_id id) :: map (subst id `old) Q)
                 (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  rewrite eq_sym_post_LOCAL.
  eapply semax_post'; [|eapply semax_pre_simple].
  + instantiate (1:= 
       (EX  old : val,
        (local (`eq (eval_id id) (subst id `old v))) && (subst id `old (PROPx P (LOCALx Q (SEPx R)))))).
    apply exp_left; intro old; apply (exp_right old).
    rewrite <- insert_local.
    rewrite subst_PROP.
    apply derives_refl.
  + instantiate (1:= |> (local (tc_lvalue Delta e1) && local (`(tc_val (typeof e1)) v) && 
      PROPx P (LOCALx Q (SEPx R)) )).
    rewrite later_andp; apply andp_right; [|apply andp_left2; apply derives_refl].
    eapply derives_trans; [apply andp_derives; [apply now_later|apply derives_refl]|].
    rewrite <- later_andp. apply later_derives.
    rewrite <- insert_local in H1.
    eapply derives_trans; [exact H1|apply andp_left1; apply derives_refl].
  + eapply semax_load_37.
    exact H.
    exact H0.
    rewrite <- insert_local in H1.
    eapply derives_trans; [exact H1|apply andp_left2].
    rewrite lifted_by_value_data_at; [|eapply is_neutral_cast_by_value, H0].
    go_lower.
    normalize.
Qed.

Lemma semax_data_cast_load_37:
  forall {Espec: OracleKind},
    forall Delta sh id P Q R (e1: expr)
    (t: type) (v: environ -> val),
    typeof_temp Delta id = Some t ->
    type_is_by_value (typeof e1) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
      local (tc_lvalue Delta e1) &&
      local (`(tc_val t) (`(eval_cast (typeof e1) t) v)) &&
      (`(data_at sh (typeof e1)) (`(valinject (typeof e1)) v) (eval_lvalue e1) * TT) ->
    semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
      (Sset id (Ecast e1 t))
        (normal_ret_assert (EX old:val, 
          PROPx P 
            (LOCALx (`eq (subst id `old (`(eval_cast (typeof e1) t) v)) (eval_id id) :: map (subst id (`old)) Q)
              (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  rewrite eq_sym_post_LOCAL.
  eapply semax_post'; [|eapply semax_pre_simple].
  + instantiate (1:= 
       (EX  old : val,
        (local (`eq (eval_id id) (subst id `old (`(eval_cast (typeof e1) t) v)))) && (subst id `old (PROPx P (LOCALx Q (SEPx R)))))).
    apply exp_left; intro old; apply (exp_right old).
    rewrite <- insert_local.
    rewrite subst_PROP.
    apply derives_refl.
  + instantiate (1:= |> (local (tc_lvalue Delta e1) && 
      local (`(tc_val t) (`(eval_cast (typeof e1) t) v)) && 
      PROPx P (LOCALx Q (SEPx R)) )).
    rewrite later_andp; apply andp_right; [|apply andp_left2; apply derives_refl].
    eapply derives_trans; [apply andp_derives; [apply now_later|apply derives_refl]|].
    rewrite <- later_andp. apply later_derives.
    rewrite <- insert_local in H1.
    eapply derives_trans; [exact H1|apply andp_left1; apply derives_refl].
  + eapply semax_cast_load_37.
    exact H.
    rewrite <- insert_local in H1.
    eapply derives_trans; [exact H1|apply andp_left2].
    rewrite lifted_by_value_data_at by exact H0.
    go_lower.
    normalize.
Qed.

Lemma semax_data_load_37':
  forall {Espec: OracleKind},
    forall Delta sh id P Q R (e1 : expr) 
    (t : type) (v : val) (v' : reptype (typeof e1)),
    typeof_temp Delta id = Some t ->
    is_neutral_cast (typeof e1) t = true ->
    JMeq v' v ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
      local (tc_lvalue Delta e1) && local `(tc_val (typeof e1) v) &&
      (`(data_at sh (typeof e1) v') (eval_lvalue e1) * TT) ->
    semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
      (Sset id e1)
        (normal_ret_assert
          (EX  old : val,
            PROPx P
              (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q)
                 (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  rewrite eq_sym_post_LOCAL'.
  rename H0 into Htype.
  eapply semax_load_37'.
  + exact H.
  + exact Htype.
  + instantiate (1:=sh).
    apply (derives_trans _ _ _ H2).
    apply andp_derives; [normalize |].
    remember (eval_lvalue e1) as p.
    go_lower.
    erewrite is_neutral_data_at; [normalize| exact Htype | exact H1].
Qed.

Lemma semax_data_cast_load_37':
  forall {Espec: OracleKind},
    forall Delta sh id P Q R (e1: expr)
    (t: type) (v: val) (v' : reptype (typeof e1)),
    typeof_temp Delta id = Some t ->
    type_is_by_value (typeof e1) ->
    JMeq v' v ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
      local (tc_lvalue Delta e1) &&
      local (`(tc_val t (eval_cast (typeof e1) t v))) &&
      (`(data_at sh (typeof e1) v') (eval_lvalue e1) * TT) ->
    semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
      (Sset id (Ecast e1 t))
        (normal_ret_assert (EX old:val, 
          PROPx P 
            (LOCALx (`(eq (eval_cast (typeof e1) t v)) (eval_id id) :: map (subst id (`old)) Q)
              (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  rewrite eq_sym_post_LOCAL'.
  eapply semax_cast_load_37'.
  exact H.
  eapply derives_trans; [exact H2 |].
  apply andp_derives; [apply derives_refl |].
  unfold liftx, lift; simpl; intros.
  erewrite by_value_data_at; [normalize | exact H0 | exact H1].
Qed.

Lemma semax_data_store_nth:
  forall {Espec: OracleKind},
    forall Delta sh n P Q R Rn (e1 e2 : expr)
      (t : type),
      typeof e1 = t ->
      type_is_by_value t ->
      nth_error R n = Some Rn ->
      Rn |-- `(data_at_ sh t) (eval_lvalue e1) ->
      writable_share sh ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign e1 e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(data_at sh t) (`(valinject t) (eval_expr (Ecast e2 t))) (eval_lvalue e1)
                          )))))).
Proof.
  intros.
  erewrite lifted_by_value_data_at; [|exact H0].
  erewrite lifted_by_value_data_at_ in H2; [|exact H0].
  
  assert (Rn |-- `prop (`(size_compatible t) (eval_lvalue e1)) &&
                  `prop (`(align_compatible t) (eval_lvalue e1)) && Rn) by (
    apply andp_right; [|apply derives_refl];
    eapply derives_trans; [exact H2|apply andp_left1; apply derives_refl]).           

  eapply semax_pre0.
  apply later_derives. Focus 1.
  + instantiate (1:= PROPx P (LOCALx Q (SEPx (replace_nth n R (`prop (`(size_compatible t) (eval_lvalue e1)) && `prop (`(align_compatible t) (eval_lvalue e1)) && Rn))))).
    rewrite (replace_nth_nth_error R _ _ H1) at 1.
    apply replace_nth_SEP, H5.
    
  rewrite andp_assoc.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn) by (exact H1)).
  rewrite <- replace_nth_nth_error by exact H1.

  rewrite andp_assoc.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn) by (exact H1)).

  rewrite andp_assoc in H5.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn) in H5 by (exact H1)).

  eapply semax_post0; [| eapply semax_store_nth'].
  + apply derives_refl.
  + exact H.
  + exact H1.
  + eapply derives_trans; [exact H2|]. apply andp_left2; apply derives_refl.
  + exact H3.
  + eapply derives_trans; [|exact H4].
    go_lower; normalize.
Qed.

(***************************************

Load/store lemmas about data_at with uncompomize function on type:
  semax_ucdata_load_37'.
  semax_ucdata_cast_load_37'.
  semax_ucdata_load_38.
  semax_ucdata_cast_load_38.
  semax_ucdata_store_nth.

***************************************)

Lemma is_neutral_reptype': forall e t t' t'',
  uncompomize e t = t' ->
  is_neutral_cast t' t'' = true ->
  reptype t = val.
Proof.
  intros.
  destruct t, t', t''; try inversion H; try inversion H0; try reflexivity.
Qed.

Lemma is_neutral_data_at': forall sh e t t' t'' v v' p,
  uncompomize e t = t' ->
  is_neutral_cast t' t'' = true ->
  JMeq v v' ->
  data_at sh t v p =
  (!! size_compatible (uncompomize e t) p) &&
  (!! align_compatible (uncompomize e t) p) && mapsto sh t' p v'.
Proof.
  intros.
  subst t'.
  apply uncompomize_by_value_data_at; try assumption.
  eapply is_neutral_cast_by_value, H0.
Qed.

Lemma is_neutral_lifted_data_at': forall sh e t t' t'' v (v': val) p,
  uncompomize e t = t' ->
  is_neutral_cast t' t'' = true ->
  JMeq v v' ->
  `(data_at sh t v) p = 
  `prop (`(size_compatible (uncompomize e t)) p) &&
  `prop (`(align_compatible (uncompomize e t)) p) && `(mapsto sh t') p `v'.
Proof.
  intros.
  unfold liftx, lift. simpl.
  extensionality.
  eapply is_neutral_data_at'; try assumption.
  exact H0.
Qed.

Lemma is_neutral_data_at_': forall sh e t t' t'' p,
  uncompomize e t = t' ->
  is_neutral_cast t' t'' = true ->
  data_at_ sh t p =
  (!! size_compatible (uncompomize e t) p) &&
  (!! align_compatible (uncompomize e t) p) && mapsto_ sh t' p.
Proof.
  intros.
  subst t'.
  apply uncompomize_by_value_data_at_; try assumption.
  eapply is_neutral_cast_by_value, H0.
Qed.

Lemma is_neutral_lifted_data_at_': forall sh e t t' t'' p,
  uncompomize e t = t' ->
  is_neutral_cast t' t'' = true ->
  `(data_at_ sh t) p =
  `prop (`(size_compatible (uncompomize e t)) p) &&
  `prop (`(align_compatible (uncompomize e t)) p) && `(mapsto_ sh t') p.
Proof.
  intros.
  unfold liftx, lift. simpl.
  extensionality.
  eapply is_neutral_data_at_'; try assumption.
  exact H0.
Qed.

Lemma semax_ucdata_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1 : expr) 
      (t1 t2 : type) (v : val) (v' : reptype t1),
      typeof_temp Delta id = Some t2 ->
      uncompomize e t1 = typeof e1 ->
      is_neutral_cast (typeof e1) t2 = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
      |-- local (tc_lvalue Delta e1) && local `(tc_val (typeof e1) v) &&
        (`(data_at sh t1 v') (eval_lvalue e1) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id e1)
          (normal_ret_assert
            (EX  old : val,
              PROPx P
                (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  rewrite eq_sym_post_LOCAL'.
  eapply semax_load_37'.
  + exact H.
  + exact H1.
  + instantiate (1:=sh).
    apply (derives_trans _ _ _ H3).
    apply andp_derives; [normalize |].
    forget (eval_lvalue e1) as p.
    go_lower.
    erewrite is_neutral_data_at'; [normalize| | |]; try eassumption.
Qed.

Lemma semax_ucdata_cast_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t1 t2: type) (v: val) (v' : reptype t2),
      typeof_temp Delta id = Some t1 ->
      uncompomize e t2 = typeof e1 ->
      type_is_by_value (typeof e1) ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_lvalue Delta e1) &&
        local (`(tc_val t1 (eval_cast (typeof e1) t1 v))) &&
        (`(data_at sh t2 v') (eval_lvalue e1) * TT) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast e1 t1))
          (normal_ret_assert
            (EX old:val, 
              PROPx P 
                (LOCALx (`(eq (eval_cast (typeof e1) t1 v)) (eval_id id) :: map (subst id (`old)) Q)
                  (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  rewrite eq_sym_post_LOCAL'.
  eapply semax_cast_load_37'.
  exact H.
  eapply derives_trans; [exact H3 |].
  apply andp_derives; [apply derives_refl |].
  unfold liftx, lift; simpl; intros.
  erewrite uncompomize_by_value_data_at with (e := e); [rewrite H0; normalize | rewrite H0; exact H1 | exact H2].
Qed.

Lemma semax_ucdata_load_38:
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1 : expr) 
      (t1 t2 : type) (v : val) (v' : reptype t1),
      Forall (closed_wrt_vars (eq id)) Q ->
      Forall (closed_wrt_vars (eq id)) R ->
      typeof_temp Delta id = Some t2 ->
      uncompomize e t1 = typeof e1 ->
      is_neutral_cast (typeof e1) t2 = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
      |-- local (tc_lvalue Delta e1) && local `(tc_val (typeof e1) v) &&
        (`(data_at sh t1 v') (eval_lvalue e1) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id e1)
          (normal_ret_assert
            (PROPx P
                (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)))).
Proof.
  intros.
  eapply semax_post';[ | eapply semax_ucdata_load_37'; eauto].
  apply exp_left; intro old.
  autorewrite with subst. apply derives_refl.
Qed.

Lemma semax_ucdata_cast_load_38:
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t1 t2: type) (v: val) (v' : reptype t2),
      Forall (closed_wrt_vars (eq id)) Q ->
      Forall (closed_wrt_vars (eq id)) R ->
      typeof_temp Delta id = Some t1 ->
      uncompomize e t2 = typeof e1 ->
      type_is_by_value (typeof e1) ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_lvalue Delta e1) &&
        local (`(tc_val t1 (eval_cast (typeof e1) t1 v))) &&
        (`(data_at sh t2 v') (eval_lvalue e1) * TT) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast e1 t1))
          (normal_ret_assert
            (PROPx P 
              (LOCALx (`(eq (eval_cast (typeof e1) t1 v)) (eval_id id) :: Q) (SEPx R)))).
Proof.
  intros.
  eapply semax_post';[ | eapply semax_ucdata_cast_load_37'; eauto].
  apply exp_left; intro old.
  autorewrite with subst. apply derives_refl.
Qed.

Lemma semax_ucdata_store_nth:
  forall {Espec: OracleKind},
    forall Delta sh e n P Q R Rn (e1 e2 : expr)
      (t1 t2: type),
      typeof e1 = t1 ->
      uncompomize e t2 = t1 ->
      type_is_by_value t1 ->
      nth_error R n = Some Rn ->
      Rn |-- `(data_at_ sh t2) (eval_lvalue e1) ->
      writable_share sh ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t1)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R)))
        (Sassign e1 e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(data_at sh t2) (`(valinject t2) (eval_expr (Ecast e2 t1))) (eval_lvalue e1)
                          )))))).
Proof.
  intros.
  erewrite lifted_uncompomize_by_value_data_at with (e:=e); [| rewrite H0; exact H1].
  erewrite lifted_uncompomize_by_value_data_at_ with (e:=e) in H3; [| rewrite H0; exact H1].

  assert (Rn |-- `prop (`(size_compatible (uncompomize e t2)) (eval_lvalue e1)) &&
                  `prop (`(align_compatible (uncompomize e t2)) (eval_lvalue e1)) && Rn) by (
    apply andp_right; [|apply derives_refl];
    eapply derives_trans; [exact H3|apply andp_left1; apply derives_refl]).        

  eapply semax_pre0.
  apply later_derives. Focus 1.
  + instantiate (1:= PROPx P (LOCALx Q (SEPx (replace_nth n R (`prop (`(size_compatible (uncompomize e t2)) (eval_lvalue e1)) && `prop (`(align_compatible (uncompomize e t2)) (eval_lvalue e1)) && Rn))))).
    rewrite (replace_nth_nth_error R _ _ H2) at 1.
    apply replace_nth_SEP, H6.
    
  rewrite andp_assoc.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn) by exact H2).
  rewrite <- replace_nth_nth_error by exact H2.

  rewrite andp_assoc.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn) by exact H2).

  rewrite andp_assoc in H6.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn) in H6 by exact H2).

  eapply semax_post0; [| eapply semax_store_nth'].
  + rewrite <- H0; apply derives_refl.
  + rewrite H0; exact H.
  + exact H2.
  + eapply derives_trans; [exact H3|]. rewrite H0; apply andp_left2; apply derives_refl.
  + exact H4.
  + rewrite H0; eapply derives_trans; [|exact H5].
    go_lower; normalize.
Qed.

(********************************************

Max length ids field_at load store:
  semax_max_path_field_load_37'.
  semax_max_path_field_cast_load_37'.
  semax_max_path_field_load_38.
  semax_max_path_field_cast_load_38.
  semax_max_path_field_load_40.
  semax_max_path_field_cast_load_40.
  semax_max_path_field_store_nth.

********************************************)

Fixpoint legal_nested_efield env t (ids: list ident) (tts: list type) : bool :=
  match ids, tts with
  | nil, nil => eqb_type (uncompomize env t) t
  | nil, _ => false
  | _ , nil => false
  | cons id ids', cons t_ tts' => 
    match nested_field_rec t ids with
    | Some (_, ttt) => (legal_nested_efield env t ids' tts' && 
                       eqb_type (uncompomize env ttt) t_)%bool
    | None => false
    end
  end.

Lemma legal_nested_efield_cons: forall env id ids t tts e,
  legal_nested_efield env (typeof e) (id :: ids) (t :: tts) = true ->
  legal_nested_efield env (typeof e) ids tts = true.
Proof.
  intros.
  simpl in H.
  valid_nested_field_rec (typeof e) ids H.
  destruct t0; inversion H; clear H2;
  (solve_field_offset_type id f; [|inversion H]);
  apply andb_true_iff in H;
  destruct H;
  rewrite H, H1;
  reflexivity.
Qed.

Fixpoint nested_efield (e: expr) (ids: list ident) (tts: list type) : expr :=
  match ids, tts with
  | nil, _ => e
  | _, nil => e
  | cons id ids', cons t_ tts' => Efield (nested_efield e ids' tts') id t_
  end.

Fixpoint compute_nested_efield e : expr * list ident * list type :=
  match e with
  | Efield e' id t => 
    match compute_nested_efield e' with
    | (e'', ids, tts) => (e'', id :: ids, t :: tts)
    end
  | _ => (e, nil, nil)
  end.

Lemma compute_nested_efield_lemma: forall e,
  match compute_nested_efield e with
  | (e', ids, tts) => nested_efield e' ids tts = e
  end.
Proof.
  intros.
  induction e; try reflexivity.
  simpl.
  destruct (compute_nested_efield e) as ((?, ?), ?).
  simpl.
  rewrite IHe.
  reflexivity.
Qed.

Lemma typeof_nested_efield: forall env e ids tts,
  legal_nested_efield env (typeof e) ids tts = true ->
  eqb_type (uncompomize env (nested_field_type2 (typeof e) ids))
  (typeof (nested_efield e ids tts)) = true .
Proof.
  intros.
  revert tts H.
  induction ids; intros; destruct tts; unfold nested_field_type2 in *; simpl in *.
  + exact H.
  + inversion H.
  + inversion H.
  + valid_nested_field_rec (typeof e) ids H.
    destruct t0; inversion H; clear H2;
    (solve_field_offset_type a f; [|inversion H]);
    apply andb_true_iff in H;
    destruct H as [H HH];
    rewrite H, HH;
    reflexivity.
Qed.

Lemma eval_lvalue_nested_efield: forall env e ids tts rho,
  legal_nested_efield env (typeof e) ids tts = true ->
  offset_val (Int.repr (nested_field_offset2 (typeof e) ids)) (eval_lvalue e rho) = 
  offset_val Int.zero (eval_lvalue (nested_efield e ids tts) rho).
Proof.
  intros.
  assert (offset_val (Int.repr (nested_field_offset2 (typeof e) ids + 0)) (eval_lvalue e rho) = 
          offset_val (Int.repr 0) (eval_lvalue (nested_efield e ids tts) rho)); [|
    replace (nested_field_offset2 (typeof e) ids + 0) with 
      (nested_field_offset2 (typeof e) ids) in H0 by omega;
    exact H0].
  forget 0 as pos;
  revert pos tts H.
  induction ids; intros; destruct tts; unfold nested_field_offset2 in *; simpl.
  + reflexivity.
  + reflexivity.
  + inversion H.
  + unfold eval_field.
    pose proof legal_nested_efield_cons _ _ _ _ _ _ H.
    pose proof typeof_nested_efield _ _ _ _ H0.
    unfold nested_field_type2 in H1.
    valid_nested_field_rec (typeof e) ids H. 
    apply eqb_type_true in H1.
    destruct t0; inversion H; clear H4; simpl uncompomize in H1; rewrite <- H1.
    - solve_field_offset_type a f; [|inversion H].
      unfold liftx, lift; simpl.
      apply andb_true_iff in H.
      destruct H.
      rewrite offset_offset_val, add_repr, Zplus_assoc_reverse.
      apply (IHids _ _ H).
    - solve_field_offset_type a f; [|inversion H].
      unfold liftx, lift; simpl.
      apply andb_true_iff in H.
      destruct H.
      rewrite <- field_mapsto.offset_val_force_ptr.
      rewrite offset_offset_val, int_add_repr_0_l.
      apply (IHids _ _ H).
Qed.

Lemma semax_max_path_field_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t : type) (ids: list ident) (tts: list type)
      (v : val) (v' : reptype (nested_field_type2 (typeof e1) ids)),
      typeof_temp Delta id = Some t ->
      uncompomize e (nested_field_type2 (typeof e1) ids) = typeof (nested_efield e1 ids tts) ->
      is_neutral_cast (typeof (nested_efield e1 ids tts)) t = true ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) ids tts = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (nested_efield e1 ids tts)) &&
        local `(tc_val (typeof (nested_efield e1 ids tts)) v) &&
        (`(field_at sh (typeof e1) ids v') (eval_lvalue e1) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 ids tts))
          (normal_ret_assert
            (EX old : val,
              PROPx P
                (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  eapply semax_ucdata_load_37'.
  + exact H.
  + exact H0.
  + exact H1.
  + exact H4.
  + eapply derives_trans; [exact H5|].
    instantiate (1:=sh).
    apply andp_derives; [normalize |].
    remember eval_lvalue as el.
    go_lower.
    subst el.
    rewrite field_at_data_at; [|exact H2].
    rewrite at_offset'_eq; [| rewrite <- data_at_offset_zero; reflexivity].
    rewrite (eval_lvalue_nested_efield e _ _ tts); [| exact H3].
    rewrite <- data_at_offset_zero.
    normalize.
Qed.

Lemma semax_max_path_field_cast_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t : type) (ids: list ident) (tts: list type)
      (v : val) (v' : reptype (nested_field_type2 (typeof e1) ids)),
      typeof_temp Delta id = Some t ->
      uncompomize e (nested_field_type2 (typeof e1) ids) = typeof (nested_efield e1 ids tts) ->
      type_is_by_value (typeof (nested_efield e1 ids tts)) ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) ids tts = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_lvalue Delta (nested_efield e1 ids tts)) &&
        local (`(tc_val t (eval_cast (typeof (nested_efield e1 ids tts)) t v))) &&
        (`(field_at sh (typeof e1) ids v') (eval_lvalue e1) * TT) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (nested_efield e1 ids tts) t))
          (normal_ret_assert
            (EX old:val,
              PROPx P
                (LOCALx (`(eq (eval_cast (typeof (nested_efield e1 ids tts)) t v)) (eval_id id) :: map (subst id (`old)) Q)
                  (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  eapply semax_ucdata_cast_load_37'; try assumption.
  + exact H0.
  + exact H4.
  + eapply derives_trans; [exact H5|].
    apply andp_derives; [apply derives_refl|].
    remember eval_lvalue as el.
    go_lower.
    subst el.
    rewrite field_at_data_at; [|exact H2].
    rewrite at_offset'_eq; [| rewrite <- data_at_offset_zero; reflexivity].
    rewrite (eval_lvalue_nested_efield e _ _ tts); [| exact H3].
    rewrite <- data_at_offset_zero.
    normalize.
Qed.

Lemma semax_max_path_field_load_38:
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t : type) (ids: list ident) (tts: list type)
      (v : val) (v' : reptype (nested_field_type2 (typeof e1) ids)),
      Forall (closed_wrt_vars (eq id)) Q ->
      Forall (closed_wrt_vars (eq id)) R ->
      typeof_temp Delta id = Some t ->
      uncompomize e (nested_field_type2 (typeof e1) ids) = typeof (nested_efield e1 ids tts) ->
      is_neutral_cast (typeof (nested_efield e1 ids tts)) t = true ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) ids tts = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (nested_efield e1 ids tts)) &&
        local `(tc_val (typeof (nested_efield e1 ids tts)) v) &&
        (`(field_at sh (typeof e1) ids v') (eval_lvalue e1) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 ids tts))
          (normal_ret_assert
            (PROPx P
              (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)))).
Proof.
  intros.
  eapply semax_post';[ | eapply semax_max_path_field_load_37'; eauto].
  apply exp_left; intro old.
  autorewrite with subst. apply derives_refl.
Qed.

Lemma semax_max_path_field_cast_load_38:
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t : type) (ids: list ident) (tts: list type)
      (v : val) (v' : reptype (nested_field_type2 (typeof e1) ids)),
      Forall (closed_wrt_vars (eq id)) Q ->
      Forall (closed_wrt_vars (eq id)) R ->
      typeof_temp Delta id = Some t ->
      uncompomize e (nested_field_type2 (typeof e1) ids) = typeof (nested_efield e1 ids tts) ->
      type_is_by_value (typeof (nested_efield e1 ids tts)) ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) ids tts = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_lvalue Delta (nested_efield e1 ids tts)) &&
        local (`(tc_val t (eval_cast (typeof (nested_efield e1 ids tts)) t v))) &&
        (`(field_at sh (typeof e1) ids v') (eval_lvalue e1) * TT) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (nested_efield e1 ids tts) t))
          (normal_ret_assert
            (PROPx P
              (LOCALx (`(eq (eval_cast (typeof (nested_efield e1 ids tts)) t v)) (eval_id id) :: Q) (SEPx R)))).
Proof.
  intros.
  eapply semax_post';[ | eapply semax_max_path_field_cast_load_37'; eauto].
  apply exp_left; intro old.
  autorewrite with subst. apply derives_refl.
Qed.

Lemma semax_max_path_field_load_40:
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t t_str: type) (ids: list ident) (tts: list type)
      (v : val) (v' : reptype (nested_field_type2 t_str ids)),
      Forall (closed_wrt_vars (eq id)) Q ->
      Forall (closed_wrt_vars (eq id)) R ->
      typeof_temp Delta id = Some t ->
      uncompomize e (nested_field_type2 t_str ids) = typeof (nested_efield (Ederef e1 t_str) ids tts) ->
      is_neutral_cast (typeof (nested_efield (Ederef e1 t_str) ids tts)) t = true ->
      legal_alignas_type t_str = true ->
      legal_nested_efield e t_str ids tts = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (nested_efield (Ederef e1 t_str) ids tts)) &&
        local `(tc_val (typeof (nested_efield (Ederef e1 t_str) ids tts)) v) &&
        (`(field_at sh t_str ids v') (eval_lvalue (Ederef e1 t_str)) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield (Ederef e1 t_str) ids tts))
          (normal_ret_assert
            (PROPx P
              (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)))).
Proof.
  intros until v.
  change t_str with (typeof (Ederef e1 t_str)) at 1 2 5 6 9.
  apply semax_max_path_field_load_38.
Qed.

Lemma semax_max_path_field_cast_load_40:
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t t_str: type) (ids: list ident) (tts: list type)
      (v: val) (v': reptype (nested_field_type2 t_str ids)),
      Forall (closed_wrt_vars (eq id)) Q ->
      Forall (closed_wrt_vars (eq id)) R ->
      typeof_temp Delta id = Some t ->
      uncompomize e (nested_field_type2 t_str ids) = typeof (nested_efield (Ederef e1 t_str) ids tts) ->
      type_is_by_value (typeof (nested_efield (Ederef e1 t_str) ids tts)) ->
      legal_alignas_type t_str = true ->
      legal_nested_efield e t_str ids tts = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_lvalue Delta (nested_efield (Ederef e1 t_str) ids tts)) &&
        local (`(tc_val t (eval_cast (typeof (nested_efield (Ederef e1 t_str) ids tts)) t v))) &&
        (`(field_at sh t_str ids v') (eval_lvalue (Ederef e1 t_str)) * TT) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (nested_efield (Ederef e1 t_str) ids tts) t))
          (normal_ret_assert
            (PROPx P
              (LOCALx (`(eq (eval_cast (typeof (nested_efield (Ederef e1 t_str) ids tts)) t v)) (eval_id id) :: Q) (SEPx R)))).
Proof.
  intros until v.
  change t_str with (typeof (Ederef e1 t_str)) at 1 2 5 6 9.
  apply semax_max_path_field_cast_load_38.
Qed.

Lemma lower_andp_lifted_val:
  forall (P Q: val->mpred) v, 
  (`(P && Q) v) = (`P v && `Q v).
Proof. reflexivity. Qed.

Lemma semax_max_path_field_store_nth:
  forall {Espec: OracleKind},
    forall Delta sh e n P Q R Rn (e1 e2 : expr)
      (t : type) (ids: list ident) (tts: list type),
      typeof (nested_efield e1 ids tts) = t ->
      uncompomize e (nested_field_type2 (typeof e1) ids) = t ->
      type_is_by_value t ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) ids tts = true ->
      nth_error R n = Some Rn ->
      Rn |-- `(field_at_ sh (typeof e1) ids) (eval_lvalue e1) ->
      writable_share sh ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (nested_efield e1 ids tts)) && 
        local (tc_expr Delta (Ecast e2 t)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (nested_efield e1 ids tts) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(field_at sh (typeof e1) ids)
                      (`(valinject (nested_field_type2 (typeof e1) ids)) (eval_expr (Ecast e2 t))) 
                        (eval_lvalue e1)
                          )))))).
Proof.
  intros.
  rewrite lifted_field_at_data_at in *; [|exact H2].
  rewrite lifted_field_at__data_at_ in *; [|exact H2].
  assert (Rn |-- 
           `prop (`(size_compatible (typeof e1)) (eval_lvalue e1)) &&
           `prop (`(align_compatible (typeof e1)) (eval_lvalue e1)) &&
           `prop (`(isSome (nested_field_rec (typeof e1) ids))) && Rn).
    apply andp_right; [apply (derives_trans _ _ _ H5) | apply derives_refl].
    apply andp_left1; apply derives_refl.
  rewrite (replace_nth_nth_error _ _ _ H4) at 1.
  eapply semax_pre0; [apply later_derives, replace_nth_SEP, H8|].

  rewrite andp_assoc.
  rewrite andp_assoc.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn) by exact H4).
  rewrite <- replace_nth_nth_error by exact H4.

  rewrite andp_assoc.
  rewrite andp_assoc.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn) by exact H4).

  rewrite andp_assoc in H8.
  rewrite andp_assoc in H8.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn) in H8 by exact H4).

  eapply semax_post0; [| eapply semax_ucdata_store_nth].
  Focus 2. exact H.
  Focus 2. exact H0.
  Focus 2. exact H1.
  Focus 2. exact H4.
  Focus 2. eapply derives_trans; [exact H5|].
           apply andp_left2.
           unfold_lift; simpl; intros.
           rewrite at_offset'_eq; [| rewrite <- data_at__offset_zero; reflexivity].
           erewrite eval_lvalue_nested_efield; [|exact H3].
           rewrite <- data_at__offset_zero.
           apply derives_refl.
  Focus 2. exact H6.
  
  + apply normal_ret_assert_derives'.
    apply replace_nth_SEP.
    unfold liftx, lift; simpl; intros.
    rewrite at_offset'_eq; [| rewrite <- data_at_offset_zero; reflexivity].
    erewrite eval_lvalue_nested_efield; [|exact H3].
    rewrite <- data_at_offset_zero.
    apply derives_refl.
  + eapply derives_trans; [|exact H7].
    go_lower; normalize.
Qed.

(********************************************

Length-1 ids field_at load store

********************************************)

Lemma semax_field_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t: type) (fld: ident) (t1: type)
      (v: val) (v': reptype (nested_field_type2 (typeof e1) (fld::nil))),
      typeof_temp Delta id = Some t ->
      uncompomize e (nested_field_type2 (typeof e1) (fld::nil)) = t1 ->
      is_neutral_cast t1 t = true ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) (fld::nil) (t1::nil) = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (Efield e1 fld t1)) &&
        local `(tc_val t1 v) &&
        (`(field_at sh (typeof e1) (fld::nil) v') (eval_lvalue e1) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (Efield e1 fld t1))
          (normal_ret_assert
            (EX old : val,
              PROPx P
                (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros until t1.
  change (Efield e1 fld t1) with (nested_efield e1 (fld::nil) (t1::nil)).
  change t1 with (typeof (nested_efield e1 (fld::nil) (t1::nil))) at 1 2 5.
  apply semax_max_path_field_load_37'.
Qed.

Definition semax_load_field'' := @semax_field_load_37'.

Lemma semax_field_cast_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t: type) (fld: ident) (t1: type)
      (v: val) (v' : reptype (nested_field_type2 (typeof e1) (fld::nil))),
      typeof_temp Delta id = Some t ->
      uncompomize e (nested_field_type2 (typeof e1) (fld::nil)) = t1 ->
      type_is_by_value t1 ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) (fld::nil) (t1::nil) = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_lvalue Delta (Efield e1 fld t1)) &&
        local (`(tc_val t (eval_cast t1 t v))) &&
        (`(field_at sh (typeof e1) (fld::nil) v') (eval_lvalue e1) * TT) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (Efield e1 fld t1) t))
          (normal_ret_assert
            (EX old:val,
              PROPx P 
                (LOCALx (`(eq (eval_cast t1 t v)) (eval_id id) :: map (subst id (`old)) Q)
                  (SEPx (map (subst id (`old)) R))))).
Proof.
  intros until t1.
  change (Efield e1 fld t1) with (nested_efield e1 (fld::nil) (t1::nil)).
  change t1 with (typeof (nested_efield e1 (fld::nil) (t1::nil))) at 1 2.
  apply semax_max_path_field_cast_load_37'.
Qed.

Definition semax_cast_load_field'' := @semax_field_cast_load_37'.

Lemma semax_load_field_38:
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t : type) (fld: ident) (t1: type)
      (v : val) (v' : reptype (nested_field_type2 (typeof e1) (fld::nil))),
      Forall (closed_wrt_vars (eq id)) Q ->
      Forall (closed_wrt_vars (eq id)) R ->
      typeof_temp Delta id = Some t ->
      uncompomize e (nested_field_type2 (typeof e1) (fld::nil)) = t1 ->
      is_neutral_cast t1 t = true ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) (fld::nil) (t1::nil) = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (Efield e1 fld t1)) &&
        local `(tc_val t1 v) &&
        (`(field_at sh (typeof e1) (fld::nil) v') (eval_lvalue e1) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (Efield e1 fld t1))
          (normal_ret_assert
            (PROPx P
              (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)))).
Proof.
  intros until t1.
  change (Efield e1 fld t1) with (nested_efield e1 (fld::nil) (t1::nil)).
  change t1 with (typeof (nested_efield e1 (fld::nil) (t1::nil))) at 1 2 5.
  apply semax_max_path_field_load_38.
Qed.

Lemma semax_cast_load_field_38:
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t: type) (fld: ident) (t1: type)
      (v: val) (v' : reptype (nested_field_type2 (typeof e1) (fld::nil))),
      Forall (closed_wrt_vars (eq id)) Q ->
      Forall (closed_wrt_vars (eq id)) R ->
      typeof_temp Delta id = Some t ->
      uncompomize e (nested_field_type2 (typeof e1) (fld::nil)) = t1 ->
      type_is_by_value t1 ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) (fld::nil) (t1::nil) = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_lvalue Delta (Efield e1 fld t1)) &&
        local (`(tc_val t (eval_cast t1 t v))) &&
        (`(field_at sh (typeof e1) (fld::nil) v') (eval_lvalue e1) * TT) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (Efield e1 fld t1) t))
          (normal_ret_assert
            (PROPx P 
              (LOCALx (`(eq (eval_cast t1 t v)) (eval_id id) :: Q) (SEPx R)))).
Proof.
  intros until t1.
  change (Efield e1 fld t1) with (nested_efield e1 (fld::nil) (t1::nil)).
  change t1 with (typeof (nested_efield e1 (fld::nil) (t1::nil))) at 1 2 5 7.
  apply semax_max_path_field_cast_load_38.
Qed.

Lemma semax_load_field_40:
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t t_str: type) (fld: ident) (t1: type)
      (v : val) (v' : reptype (nested_field_type2 t_str (fld::nil))),
      Forall (closed_wrt_vars (eq id)) Q ->
      Forall (closed_wrt_vars (eq id)) R ->
      typeof_temp Delta id = Some t ->
      uncompomize e (nested_field_type2 t_str (fld::nil)) = t1 ->
      is_neutral_cast t1 t = true ->
      legal_alignas_type t_str = true ->
      legal_nested_efield e t_str (fld::nil) (t1::nil) = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (Efield (Ederef e1 t_str) fld t1)) &&
        local `(tc_val t1 v) &&
        (`(field_at sh t_str (fld::nil) v') (eval_lvalue (Ederef e1 t_str)) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (Efield (Ederef e1 t_str) fld t1))
          (normal_ret_assert
            (PROPx P
              (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)))).
Proof.
  intros until t1.
  change (Efield e1 fld t1) with (nested_efield (Ederef e1 t_str) (fld::nil) (t1::nil)).
  change t1 with (typeof (nested_efield (Ederef e1 t_str) (fld::nil) (t1::nil))) at 1 2 5.
  apply semax_max_path_field_load_40.
Qed.

Lemma semax_cast_load_field_40:
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t t_str: type) (fld: ident) (t1: type)
      (v: val) (v' : reptype (nested_field_type2 t_str (fld::nil))),
      Forall (closed_wrt_vars (eq id)) Q ->
      Forall (closed_wrt_vars (eq id)) R ->
      typeof_temp Delta id = Some t ->
      uncompomize e (nested_field_type2 t_str (fld::nil)) = t1 ->
      type_is_by_value t1 ->
      legal_alignas_type t_str = true ->
      legal_nested_efield e t_str (fld::nil) (t1::nil) = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_lvalue Delta (Efield (Ederef e1 t_str) fld t1)) &&
        local (`(tc_val t (eval_cast t1 t v))) &&
        (`(field_at sh t_str (fld::nil) v') (eval_lvalue (Ederef e1 t_str)) * TT) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (Efield (Ederef e1 t_str) fld t1) t))
          (normal_ret_assert
            (PROPx P 
              (LOCALx (`(eq (eval_cast t1 t v)) (eval_id id) :: Q) (SEPx R)))).
Proof.
  intros until t1.
  change (Efield e1 fld t1) with (nested_efield (Ederef e1 t_str) (fld::nil) (t1::nil)).
  change t1 with (typeof (nested_efield (Ederef e1 t_str) (fld::nil) (t1::nil))) at 1 2 5.
  apply semax_max_path_field_cast_load_40.
Qed.

Lemma semax_store_field_nth:
  forall {Espec: OracleKind},
    forall Delta sh e n P Q R Rn (e1 e2 : expr)
      (t: type) (fld: ident) (t1: type),
      t1 = t ->
      uncompomize e (nested_field_type2 (typeof e1) (fld::nil)) = t ->
      type_is_by_value t ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) (fld::nil) (t1::nil) = true ->
      nth_error R n = Some Rn ->
      Rn |-- `(field_at_ sh (typeof e1) (fld::nil)) (eval_lvalue e1) ->
      writable_share sh ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (Efield e1 fld t1)) && 
        local (tc_expr Delta (Ecast e2 t)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (Efield e1 fld t1) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(field_at sh (typeof e1) (fld::nil)) 
                      (`(valinject (nested_field_type2 (typeof e1) (fld::nil))) (eval_expr (Ecast e2 t)))
                        (eval_lvalue e1)
                          )))))).
Proof.
  intros until t1.
  change (Efield e1 fld t1) with (nested_efield e1 (fld::nil) (t1::nil)).
  change t1 with (typeof (nested_efield e1 (fld::nil) (t1::nil))) at 1.
  apply semax_max_path_field_store_nth.
Qed.

(*
(* Original lemma and original proof *)
Lemma semax_store_field_nth:
forall Espec (Delta: tycontext) n sh t1 fld P Q R e1 e2 t2 R1 sid fields, 
    nth_error R n = Some R1 ->
    writable_share sh ->
    t1 = Tstruct sid fields noattr ->
    typeof e1 = t1 ->
    t2 = type_of_field (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
    R1 |-- `(field_at_ sh t1 fld) (eval_lvalue e1) ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--  
              local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sassign (Efield e1 fld t2) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx (replace_nth n R
                    (`(field_at sh (typeof e1) fld)
                       (`force_val (`(sem_cast (typeof e2) t2) (eval_expr e2)))
                         (eval_lvalue e1) )))))).
Proof.
intros.
subst t1.
eapply semax_pre_post ; [ | |
 apply (semax_store_field Espec Delta sh e1 fld
       (PROPx P (LOCALx Q (SEPx (replace_nth n R emp))))
    t2 e2 sid fields H0); auto].
*
apply later_left2.
repeat rewrite insert_local.
apply andp_right; auto.
rewrite insert_SEP.
rewrite H2.
match goal with |- ?A |-- _ => rewrite <- (andp_dup A) end.
eapply derives_trans; [apply andp_derives; [| apply derives_refl ] | ].
apply H5.
rewrite (SEP_nth_isolate _ _ _ H).
go_lowerx.  apply sepcon_derives; auto.
apply H4.
*
intros ek vl; unfold normal_ret_assert.
normalize. rewrite insert_SEP.
apply andp_left2.
rewrite (SEP_replace_nth_isolate _ _ _ _ H).
unfold exit_tycon.
auto.
Qed.

Lemma semax_load_field'':
forall  (sh: share) (v: val)
       Espec (Delta: tycontext) id t1 fld P Q R e1 t2 t3 sid fields ,
    typeof e1 = Tstruct sid fields noattr ->
    typeof_temp Delta id = Some t3 ->
   t1 = typeof e1 ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   is_neutral_cast t2 t3 = true ->
   PROPx P (LOCALx (tc_environ Delta :: `isptr (eval_lvalue e1) :: Q) (SEPx R)) 
                           |-- local (tc_lvalue Delta e1) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
        |--  `(field_at sh t1 fld v) (eval_lvalue e1) * TT ->
   tc_val t2 v ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert (
         EX old:val, PROPx P 
                     (LOCALx (`(eq v) (eval_id id) :: map (subst id (`old)) Q)
                     (SEPx (map (subst id (`old)) R))))).
Proof.
pose proof I.
pose proof I.
intros until fields; intros H1 H2 TE1 TC2 CLASSIFY TC3 H6 TC4.
subst t1.
repeat rewrite <- insert_local in H6.
repeat rewrite <- insert_local in TC3.
replace  (EX  old : val,
      PROPx P
        (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q)
           (SEPx (map (subst id `old) R))))
  with  (EX  old : val, local (`(eq v) (eval_id id)) && 
                   subst id `old (PROPx P (LOCALx Q (SEPx R))))
  by (f_equal; extensionality old; autorewrite with subst; rewrite insert_local; auto).
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
eapply semax_pre_post; [ | | apply (semax_load Delta sh id PQR _ t3 (`v)); auto].
* (* PRECONDITION *)
apply later_left2.
apply andp_right; [ | apply andp_left2; auto].
apply derives_trans with 
 (local (tc_lvalue Delta e1)  && (`(field_at sh (typeof e1) fld v) (eval_lvalue e1) * TT)).
apply andp_right.
eapply derives_trans; [ | apply TC3].
apply andp_right. apply andp_left1; auto. apply andp_right; [ |  apply andp_left2; auto].
eapply derives_trans; [apply H6 | ].
go_lowerx. rewrite field_at_isptr. clear; normalize.
auto.
go_lowerx.
apply andp_right; [ | apply prop_right; auto].
unfold field_at, tc_lvalue.
simpl. rewrite H1. rewrite field_offset_unroll.
destruct (field_offset fld fields);   try (rewrite FF_sepcon; apply FF_left).
rewrite <- TC2.
normalize.
apply prop_right; repeat split; auto.
rewrite denote_tc_assert_andp; split.
apply H3. rewrite H4. apply I.
* (* POSTCONDITION *)
intros ek vl.
apply andp_left2. apply normal_ret_assert_derives'.
apply exp_derives; intro old.
apply andp_derives; auto.
clear; intro; unfold_lift; apply prop_derives; auto.
*
 eapply derives_trans; [ apply H6 | ].
apply sepcon_derives; auto.
unfold field_at.
go_lowerx.
unfold_lift.
rewrite H1.
rewrite field_offset_unroll.
simpl.
destruct (field_offset fld fields);   try apply FF_left.
rewrite <- TC2.
normalize.
Qed.

Lemma semax_cast_load_field'':
forall  (sh: share) (v: val)
       Espec (Delta: tycontext) id t1 fld P Q R e1 t2 t3 sid fields ,
    typeof_temp Delta id = Some t3 ->
    typeof e1 = Tstruct sid fields noattr ->
   t1 = typeof e1 ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   PROPx P (LOCALx (tc_environ Delta :: `isptr (eval_lvalue e1) :: Q) (SEPx R)) 
                           |-- local (tc_lvalue Delta e1) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
        |--  `(field_at sh t1 fld v) (eval_lvalue e1) * TT ->
   tc_val t3 (eval_cast t2 t3 v) ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ecast (Efield e1 fld t2) t3))
       (normal_ret_assert (
         EX old:val, PROPx P 
                     (LOCALx (`(eq (eval_cast t2 t3 v)) (eval_id id) :: map (subst id (`old)) Q)
                     (SEPx (map (subst id (`old)) R))))).
Proof.
intros until fields; intros H H1 TE1 TC2 TC3 H6 TC4.
pose proof I.
subst t1.
repeat rewrite <- insert_local in H6.
repeat rewrite <- insert_local in TC3.
replace  (EX  old : val,
      PROPx P
        (LOCALx (`(eq (eval_cast t2 t3 v)) (eval_id id) :: map (subst id `old) Q)
           (SEPx (map (subst id `old) R))))
  with  (EX  old : val, local (`(eq (eval_cast t2 t3 v)) (eval_id id)) && 
                   subst id `old (PROPx P (LOCALx Q (SEPx R))))
  by (f_equal; extensionality old; autorewrite with subst; rewrite insert_local; auto).
forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
eapply semax_pre_post; [ | | 
   apply (semax_cast_load Delta sh id PQR _ _ `v); auto].
* (* PRECONDITION *)
apply later_left2.
apply andp_right; [ | apply andp_left2; auto].
apply derives_trans with 
 (local (tc_lvalue Delta e1)  && (`(field_at sh (typeof e1) fld v) (eval_lvalue e1) * TT)).
apply andp_right.
eapply derives_trans; [ | apply TC3].
apply andp_right. apply andp_left1; auto. apply andp_right; [ |  apply andp_left2; auto].
eapply derives_trans; [apply H6 | ].
go_lowerx. rewrite field_at_isptr. clear; normalize.
auto.
go_lowerx.
unfold field_at, tc_lvalue.
simpl. rewrite H1. rewrite field_offset_unroll.
destruct (field_offset fld fields);   try (rewrite FF_sepcon; apply FF_left).
rewrite <- TC2.
normalize.
apply prop_right; repeat split; auto.
rewrite denote_tc_assert_andp; split.
apply H2. rewrite H3. apply I.
* (* POSTCONDITION *)
intros ek vl.
apply andp_left2. apply normal_ret_assert_derives'.
apply exp_derives; intro old.
apply andp_derives; auto.
clear; intro; unfold_lift; apply prop_derives; auto.
*
 eapply derives_trans; [ apply H6 | ].
apply sepcon_derives; auto.
unfold field_at.
go_lowerx.
unfold_lift.
rewrite H1.
rewrite field_offset_unroll.
simpl.
destruct (field_offset fld fields);   try apply FF_left.
rewrite <- TC2.
normalize.
Qed.

Lemma semax_load_field_38:
forall  (sh: share) (v: val)
       Espec (Delta: tycontext) id t1 fld P Q R e1 t2 t3 sid fields ,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
    typeof e1 = Tstruct sid fields noattr ->
    typeof_temp Delta id = Some t3 ->
   t1 = typeof e1 ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   is_neutral_cast t2 t3 = true ->
   PROPx P (LOCALx (tc_environ Delta :: `isptr (eval_lvalue e1) :: Q) (SEPx R)) 
                     |-- local (tc_lvalue Delta e1) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
                     |--  `(field_at sh t1 fld v) (eval_lvalue e1) * TT ->
   tc_val t2 v ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Efield e1 fld t2))
       (normal_ret_assert (PROPx P (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)))).
Proof.
intros.
eapply semax_post';[ | eapply semax_load_field''; eauto].
apply exp_left; intro old.
autorewrite with subst. auto.
Qed.

Lemma semax_cast_load_field_38:
forall  (sh: share) (v: val)
       Espec (Delta: tycontext) id t1 fld P Q R e1 t2 t3 sid fields ,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
    typeof e1 = Tstruct sid fields noattr ->
    typeof_temp Delta id = Some t3 ->
   t1 = typeof e1 ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   PROPx P (LOCALx (tc_environ Delta :: `isptr (eval_lvalue e1) :: Q) (SEPx R)) 
                     |-- local (tc_lvalue Delta e1) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
                     |--  `(field_at sh t1 fld v) (eval_lvalue e1) * TT ->
   tc_val t3 (eval_cast t2 t3 v) ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ecast (Efield e1 fld t2) t3))
       (normal_ret_assert (PROPx P (LOCALx (`(eq (eval_cast t2 t3 v)) (eval_id id) :: Q) (SEPx R)))).
Proof.
intros.
eapply semax_post';[ | eapply semax_cast_load_field''; eauto].
apply exp_left; intro old.
autorewrite with subst. auto.
Qed.

Lemma semax_load_field_40:
forall  (sh: share) (v: val)
       Espec (Delta: tycontext) id t1 fld P Q R e1 t2 t3 sid fields ,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
    t1 = Tstruct sid fields noattr ->
   typeof_temp Delta id = Some t3 ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   typeof e1 = tptr t1 ->
   is_neutral_cast t2 t3 = true ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
         |--  local (tc_expr Delta e1) && (`(field_at sh t1 fld v) (eval_expr e1) * TT) ->
   tc_val t2 v ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Efield (Ederef e1 t1) fld t2))
       (normal_ret_assert (PROPx P (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)))).
Proof.
intros. rename H7 into TC4.
eapply semax_load_field_38; eauto.
do 2 rewrite <- insert_local. rewrite <- andp_assoc.
rewrite (andp_comm (local _)).
rewrite andp_assoc. apply andp_left2. rewrite insert_local.
apply derives_trans with (local (tc_expr Delta e1) && local (`isptr (eval_expr e1))).
apply andp_right; auto.
eapply derives_trans; [ apply H6 | ].
apply andp_left1; auto.
eapply derives_trans; [ apply H6 | ].
apply andp_left2.
clear; go_lowerx. rewrite field_at_isptr; normalize.
go_lowerx. intro. apply prop_right.
unfold tc_lvalue; simpl denote_tc_assert.
repeat rewrite denote_tc_assert_andp.
repeat split; auto.
rewrite H4. apply I.
rewrite H1; apply I.
eapply derives_trans; [ apply H6 | ].
apply andp_left2.
apply sepcon_derives; auto.
go_lowerx.
unfold_lift. rewrite field_at_force_ptr.
apply derives_refl.
Qed.

Lemma semax_cast_load_field_40:
forall  (sh: share) (v: val)
       Espec (Delta: tycontext) id t1 fld P Q R e1 t2 t3 sid fields ,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
    t1 = Tstruct sid fields noattr ->
   typeof_temp Delta id = Some t3 ->
   t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   typeof e1 = tptr t1 ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) 
         |--  local (tc_expr Delta e1) && (`(field_at sh t1 fld v) (eval_expr e1) * TT) ->
   tc_val t3 (eval_cast t2 t3 v) ->
    @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ecast (Efield (Ederef e1 t1) fld t2) t3))
       (normal_ret_assert (PROPx P (LOCALx (`(eq (eval_cast t2 t3 v)) (eval_id id) :: Q) (SEPx R)))).
Proof.
intros until 6. pose proof I; intros; rename H7 into TC4.
eapply semax_cast_load_field_38; eauto.
do 2 rewrite <- insert_local. rewrite <- andp_assoc.
rewrite (andp_comm (local _)).
rewrite andp_assoc. apply andp_left2. rewrite insert_local.
apply derives_trans with (local (tc_expr Delta e1) && local (`isptr (eval_expr e1))).
apply andp_right; auto.
eapply derives_trans; [ apply H6 | ].
apply andp_left1; auto.
eapply derives_trans; [ apply H6 | ].
apply andp_left2.
clear; go_lowerx. rewrite field_at_isptr; normalize.
go_lowerx. intro. apply prop_right.
unfold tc_lvalue; simpl denote_tc_assert.
repeat rewrite denote_tc_assert_andp.
repeat split; auto.
rewrite H4. apply I.
rewrite H1; apply I.
eapply derives_trans; [ apply H6 | ].
apply andp_left2.
apply sepcon_derives; auto.
go_lowerx.
unfold_lift. rewrite field_at_force_ptr.
apply derives_refl.
Qed.
*)
