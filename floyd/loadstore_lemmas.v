Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.closed_lemmas.
Require Import Coq.Logic.JMeq.

Local Open Scope logic.

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
  semax_data_load.
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

Lemma semax_data_load: 
  forall {Espec: OracleKind},
    forall (Delta : tycontext) (sh : Share.t) (id : ident) 
         (P : list Prop) (Q : list (environ -> Prop))
         (R : list (environ -> mpred)) (e1 : expr) 
         (t2 : type) (v2 : reptype (typeof e1)) (v2' : val),
       typeof_temp Delta id = Some t2 ->
       is_neutral_cast (typeof e1) t2 = true ->
       JMeq v2 v2' ->
       PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
       |-- local (tc_lvalue Delta e1) && local `(tc_val (typeof e1) v2') &&
           (`(data_at sh (typeof e1) v2) (eval_lvalue e1) * TT) ->
       semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
         (Sset id e1)
         (normal_ret_assert
            (EX  old : val,
             PROPx P
               (LOCALx (`eq (eval_id id) `v2' :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
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

Lemma semax_data_store_nth:
  forall {Espec: OracleKind},
    forall (n : nat) (Delta : tycontext) (P : list Prop)
         (Q : list (environ -> Prop)) (R : list (LiftEnviron mpred))
         (e1 e2 : expr) (Rn : LiftEnviron mpred) (sh : Share.t) 
         (t1 : type) (v: val) (v' : reptype t1),
       is_neutral_cast t1 t1 = true ->
       JMeq v' v ->
       typeof e1 = t1 ->
       nth_error R n = Some Rn ->
       Rn |-- `(data_at_ sh t1) (eval_lvalue e1) ->
       writable_share sh ->
       PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
       |-- local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t1)) ->
       PROPx P (LOCALx Q (SEPx (replace_nth n R (`(data_at_ sh t1) (eval_lvalue e1)) ))) |-- local (`(eq) (eval_expr (Ecast e2 t1)) `v) ->
       semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
         (Sassign e1 e2)
         (normal_ret_assert
            (PROPx P
               (LOCALx Q
                  (SEPx
                     (replace_nth n R
                        (`(data_at sh t1 v') (eval_lvalue e1)
                          )))))).
Proof.
  intros until v'. intro Htype. intros.

  erewrite is_neutral_lifted_data_at; [|exact Htype| exact H].
  erewrite is_neutral_lifted_data_at_ in H2; [|exact Htype].
  erewrite is_neutral_lifted_data_at_ in H5; [|exact Htype].

  assert (Rn |-- `prop (`(size_compatible t1) (eval_lvalue e1)) &&
                  `prop (`(align_compatible t1) (eval_lvalue e1)) && Rn) by (
    apply andp_right; [|apply derives_refl];
    eapply derives_trans; [exact H2|apply andp_left1; apply derives_refl]).           

  eapply semax_pre0.
  apply later_derives. Focus 1.
  + instantiate (1:= PROPx P (LOCALx Q (SEPx (replace_nth n R (`prop (`(size_compatible t1) (eval_lvalue e1)) && `prop (`(align_compatible t1) (eval_lvalue e1)) && Rn))))).
    rewrite (replace_nth_nth_error R _ _ H1) at 1.
    apply replace_nth_SEP, H6.
    
  rewrite andp_assoc.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn); [|exact H1]).
  rewrite <- replace_nth_nth_error.

  rewrite andp_assoc.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn); [|exact H1]).

  rewrite andp_assoc in H5.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn) in H5; [|exact H1]).

  eapply semax_post0; [| eapply semax_store_nth'].
  Focus 2. exact H0.
  Focus 2. exact H1.
  Focus 2. eapply derives_trans; [exact H2|]. apply andp_left2; apply derives_refl.
  Focus 2. exact H3.
  Focus 2. rewrite (replace_nth_nth_error R _ _ H1).
           rewrite LOCAL_2_hd. rewrite <- (replace_nth_SEP_andp_local P _ R n Rn); [|exact H1].
           rewrite LOCAL_2_hd. rewrite -> (replace_nth_SEP_andp_local P _ R n Rn); [|exact H1].
           rewrite <- (replace_nth_nth_error R _ _ H1).
           eapply derives_trans; [|exact H4].
           go_lower; normalize.
  Focus 2. exact H1.

  apply normal_ret_assert_derives'.

  eapply derives_trans.
  + instantiate (1:= PROPx P
     (LOCALx (`eq (eval_expr (Ecast e2 t1)) `v :: `(align_compatible t1) (eval_lvalue e1)
         :: `(size_compatible t1) (eval_lvalue e1) :: Q) (SEPx (replace_nth n R (`(mapsto sh t1) (eval_lvalue e1) (eval_expr (Ecast e2 t1))))))).
    assert (
    PROPx P
     (LOCALx (`(align_compatible t1) (eval_lvalue e1)
         :: `(size_compatible t1) (eval_lvalue e1) ::Q)
        (SEPx
           (replace_nth n R
              (`(mapsto sh t1) (eval_lvalue e1) (eval_expr (Ecast e2 t1))))))
    |--
    PROPx P
     (LOCALx (`(align_compatible t1) (eval_lvalue e1)
         :: `(size_compatible t1) (eval_lvalue e1) ::Q)
        (SEPx
           (replace_nth n R
              (`(mapsto_ sh t1) (eval_lvalue e1)))))).
      apply replace_nth_SEP. unfold liftx, lift. simpl. intros. apply mapsto_mapsto_.
    unfold PROPx, LOCALx.
    unfold PROPx, LOCALx in H5, H7.
    simpl.
    simpl in H5, H7.
    intros.
    repeat rewrite local_lift2_and in *.
    simpl.
    repeat try apply andp_right.
    - apply andp_left1; cancel.
    - eapply derives_trans; [exact (H7 x)| exact (H5 x)].
    - apply andp_left2; apply andp_left1; apply andp_left1; cancel.
    - apply andp_left2; apply andp_left1; apply andp_left2; apply andp_left1; cancel.
    - apply andp_left2; apply andp_left1; apply andp_left2; apply andp_left2; cancel.
    - apply andp_left2; apply andp_left2; cancel.
  + rewrite <- insert_local.
    unfold local, lift1.
Opaque eval_expr.
    simpl; intros.
    remember PROPx as m.
    normalize.
    subst m.
    unfold liftx, lift in H7; simpl in H7.
Transparent eval_expr.
    subst v.
    apply replace_nth_SEP'.
    unfold liftx, lift. cancel.
Qed.

(***************************************

Load/store lemmas about data_at with uncompomize function on type:
  semax_data_load'.
  semax_data_store_nth'.

***************************************)

Lemma is_neutral_reptype': forall t t' t'',
  uncompomize t = t' ->
  is_neutral_cast t' t'' = true ->
  reptype t = val.
Proof.
  intros.
  destruct t, t', t''; try inversion H; try inversion H0; try reflexivity.
Qed.

Lemma is_neutral_data_at': forall sh t t' t'' v v' p,
  uncompomize t = t' ->
  is_neutral_cast t' t'' = true ->
  JMeq v v' ->
  data_at sh t v p =
  (!! size_compatible (uncompomize t) p) &&
  (!! align_compatible (uncompomize t) p) && mapsto sh t' p v'.
Proof.
  intros.
  subst t'.
  apply uncompomize_by_value_data_at; try assumption.
  eapply is_neutral_cast_by_value, H0.
Qed.

Lemma is_neutral_lifted_data_at': forall sh t t' t'' v (v': val) p,
  uncompomize t = t' ->
  is_neutral_cast t' t'' = true ->
  JMeq v v' ->
  `(data_at sh t v) p = 
  `prop (`(size_compatible (uncompomize t)) p) &&
  `prop (`(align_compatible (uncompomize t)) p) && `(mapsto sh t') p `v'.
Proof.
  intros.
  unfold liftx, lift. simpl.
  extensionality.
  eapply is_neutral_data_at'; try assumption.
  exact H0.
Qed.

Lemma is_neutral_data_at_': forall sh t t' t'' p,
  uncompomize t = t' ->
  is_neutral_cast t' t'' = true ->
  data_at_ sh t p =
  (!! size_compatible (uncompomize t) p) &&
  (!! align_compatible (uncompomize t) p) && mapsto_ sh t' p.
Proof.
  intros.
  subst t'.
  apply uncompomize_by_value_data_at_; try assumption.
  eapply is_neutral_cast_by_value, H0.
Qed.

Lemma is_neutral_lifted_data_at_': forall sh t t' t'' p,
  uncompomize t = t' ->
  is_neutral_cast t' t'' = true ->
  `(data_at_ sh t) p =
  `prop (`(size_compatible (uncompomize t)) p) &&
  `prop (`(align_compatible (uncompomize t)) p) && `(mapsto_ sh t') p.
Proof.
  intros.
  unfold liftx, lift. simpl.
  extensionality.
  eapply is_neutral_data_at_'; try assumption.
  exact H0.
Qed.

Lemma semax_data_load':
  forall {Espec: OracleKind},
    forall (Delta : tycontext) (sh : Share.t) (id : ident) 
      (P : list Prop) (Q : list (environ -> Prop))
      (R : list (environ -> mpred)) (e1 : expr) 
      (t1 t2 : type) (v2 : reptype t1) (v2' : val),
      uncompomize t1 = typeof e1 ->
      is_neutral_cast (typeof e1) t2 = true ->
      typeof_temp Delta id = Some t2 ->
      JMeq v2 v2' ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
      |-- local (tc_lvalue Delta e1) && local `(tc_val (typeof e1) v2') &&
          (`(data_at sh t1 v2) (eval_lvalue e1) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
         (Sset id e1)
         (normal_ret_assert
            (EX  old : val,
             PROPx P
               (LOCALx (`eq (eval_id id) `v2' :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  eapply semax_load_37'.
  + exact H1.
  + exact H0.
  + instantiate (1:=sh).
    apply (derives_trans _ _ _ H3).
    apply andp_derives; [normalize |].
    forget (eval_lvalue e1) as p.
    go_lower.
    erewrite is_neutral_data_at'; [normalize| | |]; try assumption.
    exact H0.
Qed.

Lemma semax_data_store_nth':
  forall {Espec: OracleKind},
    forall (n : nat) (Delta : tycontext) (P : list Prop)
         (Q : list (environ -> Prop)) (R : list (LiftEnviron mpred))
         (e1 e2 : expr) (Rn : LiftEnviron mpred) (sh : Share.t) 
         (t1 t2: type) (v: val) (v' : reptype t2),
       uncompomize t2 = t1 ->
       is_neutral_cast t1 t1 = true ->
       JMeq v' v ->
       typeof e1 = t1 ->
       nth_error R n = Some Rn ->
       Rn |-- `(data_at_ sh t2) (eval_lvalue e1) ->
       writable_share sh ->
       PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
       |-- local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t1)) ->
       PROPx P (LOCALx Q (SEPx (replace_nth n R (`(data_at_ sh t2) (eval_lvalue e1)) ))) |-- local (`(eq) (eval_expr (Ecast e2 t1)) `v) ->
       semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
         (Sassign e1 e2)
         (normal_ret_assert
            (PROPx P
               (LOCALx Q
                  (SEPx
                     (replace_nth n R
                        (`(data_at sh t2 v') (eval_lvalue e1)
                          )))))).
Proof.
  intros.
  erewrite is_neutral_lifted_data_at'; [| exact H | exact H0 | exact H1].
  erewrite is_neutral_lifted_data_at_' in H4; [| exact H | exact H0].
  erewrite is_neutral_lifted_data_at_' in H7; [| exact H | exact H0].

  assert (Rn |-- `prop (`(size_compatible (uncompomize t2)) (eval_lvalue e1)) &&
                  `prop (`(align_compatible (uncompomize t2)) (eval_lvalue e1)) && Rn) by (
    apply andp_right; [|apply derives_refl];
    eapply derives_trans; [exact H4|apply andp_left1; apply derives_refl]).           

  eapply semax_pre0.
  apply later_derives. Focus 1.
  + instantiate (1:= PROPx P (LOCALx Q (SEPx (replace_nth n R (`prop (`(size_compatible (uncompomize t2)) (eval_lvalue e1)) && `prop (`(align_compatible (uncompomize t2)) (eval_lvalue e1)) && Rn))))).
    rewrite (replace_nth_nth_error R _ _ H3) at 1.
    apply replace_nth_SEP, H8.
    
  rewrite andp_assoc.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn); [|exact H3]).
  rewrite <- replace_nth_nth_error.

  rewrite andp_assoc.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn); [|exact H3]).

  rewrite andp_assoc in H7.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn) in H7; [|exact H3]).

  eapply semax_post0; [| eapply semax_store_nth'].
  Focus 2. exact H2.
  Focus 2. exact H3.
  Focus 2. eapply derives_trans; [exact H4|]. apply andp_left2; apply derives_refl.
  Focus 2. exact H5.
  Focus 2. rewrite (replace_nth_nth_error R _ _ H3).
           rewrite LOCAL_2_hd. rewrite <- (replace_nth_SEP_andp_local P _ R n Rn); [|exact H3].
           rewrite LOCAL_2_hd. rewrite -> (replace_nth_SEP_andp_local P _ R n Rn); [|exact H3].
           rewrite <- (replace_nth_nth_error R _ _ H3).
           eapply derives_trans; [|exact H6].
           go_lower; normalize.
  Focus 2. exact H3.

  apply normal_ret_assert_derives'.

  eapply derives_trans.
  + instantiate (1:= PROPx P
     (LOCALx (`eq (eval_expr (Ecast e2 (uncompomize t2))) `v :: `(align_compatible (uncompomize t2)) (eval_lvalue e1)
         :: `(size_compatible t1) (eval_lvalue e1) :: Q) (SEPx (replace_nth n R (`(mapsto sh t1) (eval_lvalue e1) (eval_expr (Ecast e2 t1))))))).
    assert (
    PROPx P
     (LOCALx (`(align_compatible (uncompomize t2)) (eval_lvalue e1)
         :: `(size_compatible (uncompomize t2)) (eval_lvalue e1) ::Q)
        (SEPx
           (replace_nth n R
              (`(mapsto sh t1) (eval_lvalue e1) (eval_expr (Ecast e2 t1))))))
    |--
    PROPx P
     (LOCALx (`(align_compatible (uncompomize t2)) (eval_lvalue e1)
         :: `(size_compatible (uncompomize t2)) (eval_lvalue e1) ::Q)
        (SEPx
           (replace_nth n R
              (`(mapsto_ sh t1) (eval_lvalue e1)))))).
      apply replace_nth_SEP. unfold liftx, lift. simpl. intros. apply mapsto_mapsto_.
    unfold PROPx, LOCALx.
    unfold PROPx, LOCALx in H7, H9.
    simpl.
    simpl in H7, H9.
    intros.
    repeat rewrite local_lift2_and in *.
    simpl.
    subst t1; repeat try apply andp_right.
    - apply andp_left1; cancel.
    - eapply derives_trans; [exact (H9 x)|exact (H7 x)].
    - apply andp_left2; apply andp_left1; apply andp_left1; cancel.
    - apply andp_left2; apply andp_left1; apply andp_left2; apply andp_left1; cancel.
    - apply andp_left2; apply andp_left1; apply andp_left2; apply andp_left2; cancel.
    - apply andp_left2; apply andp_left2; cancel.
  + rewrite <- insert_local.
    unfold local, lift1.
Opaque eval_expr.
    simpl; intros.
    remember PROPx as m.
    normalize.
    subst m.
    unfold liftx, lift in H9; simpl in H9.
Transparent eval_expr.
    subst v.
    subst t1; apply replace_nth_SEP'.
    unfold liftx, lift. cancel.
Qed.

(********************************************

Max length ids field_at load store

********************************************)

Fixpoint legal_nested_efield t (ids: list ident) (tts: list type) : bool :=
  match ids, tts with
  | nil, nil => eqb_type (uncompomize t) t
  | nil, _ => false
  | _ , nil => false
  | cons id ids', cons t_ tts' => 
    match nested_field_rec t ids with
    | Some (_, ttt) => (legal_nested_efield t ids' tts' && 
                       eqb_type (uncompomize ttt) t_)%bool
    | None => false
    end
  end.

Lemma legal_nested_efield_cons: forall id ids t tts e,
  legal_nested_efield (typeof e) (id :: ids) (t :: tts) = true ->
  legal_nested_efield (typeof e) ids tts = true.
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

Lemma typeof_nested_efield: forall e ids tts,
  legal_nested_efield (typeof e) ids tts = true ->
  eqb_type (uncompomize (nested_field_type2 (typeof e) ids))
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

Lemma eval_lvalue_nested_efield: forall e ids tts rho,
  legal_nested_efield (typeof e) ids tts = true ->
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
    pose proof legal_nested_efield_cons _ _ _ _ _ H.
    pose proof typeof_nested_efield _ _ _ H0.
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

Lemma semax_field_load_max_path:
  forall {Espec: OracleKind},
    forall (Delta : tycontext) (sh : Share.t) (id : ident) 
         (P : list Prop) (Q : list (environ -> Prop))
         (R : list (environ -> mpred)) (e1 : expr) 
         (t2 : type) (ids: list ident) (tts: list type)
         (v2 : reptype (nested_field_type2 (typeof e1) ids)) (v2' : val),
       uncompomize (nested_field_type2 (typeof e1) ids) = typeof (nested_efield e1 ids tts) ->
       is_neutral_cast (typeof (nested_efield e1 ids tts)) t2 = true ->
       legal_alignas_type (typeof e1) = true ->
       legal_nested_efield (typeof e1) ids tts = true ->
       typeof_temp Delta id = Some t2 ->
       JMeq v2 v2' ->
       PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
       |-- local (tc_lvalue Delta (nested_efield e1 ids tts)) &&
           local `(tc_val (typeof (nested_efield e1 ids tts)) v2') &&
           (`(field_at sh (typeof e1) ids v2) (eval_lvalue e1) * TT) ->
       semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
         (Sset id (nested_efield e1 ids tts))
         (normal_ret_assert
            (EX  old : val,
             PROPx P
               (LOCALx (`eq (eval_id id) `v2' :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  eapply semax_data_load'.
  + exact H.
  + exact H0.
  + exact H3.
  + exact H4.
  + eapply derives_trans; [exact H5|].
    instantiate (1:=sh).
    apply andp_derives; [normalize |].
    remember eval_lvalue as v.
    go_lower.
    subst v.
    rewrite field_at_data_at; [|exact H1].
    rewrite at_offset'_eq; [| rewrite <- data_at_offset_zero; reflexivity].
    rewrite (eval_lvalue_nested_efield _ _ tts); [| exact H2].
    rewrite <- data_at_offset_zero.
    normalize.
Qed.

Lemma lower_andp_lifted_val:
  forall (P Q: val->mpred) v, 
  (`(P && Q) v) = (`P v && `Q v).
Proof. reflexivity. Qed.

Lemma field_at__data_at_: forall sh t ids p,
  legal_alignas_type t = true ->
  field_at_ sh t ids p = 
  (!! (size_compatible t p)) &&  
  (!! (align_compatible t p)) &&
  (!! (isSome (nested_field_rec t ids))) && 
  at_offset' (data_at_ sh (nested_field_type2 t ids)) (nested_field_offset2 t ids) p.
Proof.
  intros.
  unfold field_at_, data_at_.
  apply field_at_data_at, H.
Qed.

Lemma lifted_field_at_data_at: forall sh t ids v p,
       legal_alignas_type t = true ->
       `(field_at sh t ids v) p =
       `prop (`(size_compatible t) p) && 
       `prop (`(align_compatible t) p) && 
       `prop (`(isSome (nested_field_rec t ids))) &&
       `(at_offset' (data_at sh (nested_field_type2 t ids) v)
         (nested_field_offset2 t ids)) p.
Proof.
  intros.
  extensionality rho.
  unfold liftx, lift; simpl.
  apply field_at_data_at, H.
Qed.

Lemma lifted_field_at__data_at_: forall sh t ids p,
       legal_alignas_type t = true ->
       `(field_at_ sh t ids) p =
       `prop (`(size_compatible t) p) && 
       `prop (`(align_compatible t) p) && 
       `prop (`(isSome (nested_field_rec t ids))) &&
       `(at_offset' (data_at_ sh (nested_field_type2 t ids))
         (nested_field_offset2 t ids)) p.
Proof.
  intros.
  extensionality rho.
  unfold liftx, lift; simpl.
  apply field_at__data_at_, H.
Qed.

Lemma semax_field_store_nth_max_len:
  forall {Espec: OracleKind},
    forall (n : nat) (Delta : tycontext) (P : list Prop)
         (Q : list (environ -> Prop)) (R : list (LiftEnviron mpred))
         (e1 e2 : expr) (Rn : LiftEnviron mpred) (sh : Share.t) 
         (t1: type) ids tts (v: val) (v' : reptype (nested_field_type2 (typeof e1) ids)),
       uncompomize (nested_field_type2 (typeof e1) ids) = t1 ->
       is_neutral_cast t1 t1 = true ->
       legal_alignas_type (typeof e1) = true ->
       legal_nested_efield (typeof e1) ids tts = true ->
       JMeq v' v ->
       typeof (nested_efield e1 ids tts) = t1 ->
       nth_error R n = Some Rn ->
       Rn |-- `(field_at_ sh (typeof e1) ids) (eval_lvalue e1) ->
       writable_share sh ->
       PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
       |-- local (tc_lvalue Delta (nested_efield e1 ids tts)) && 
           local (tc_expr Delta (Ecast e2 t1)) ->
       PROPx P (LOCALx Q (SEPx (replace_nth n R (`(field_at_ sh (typeof e1) ids) (eval_lvalue e1)))))
       |-- local (`(eq) (eval_expr (Ecast e2 t1)) `v) ->
       semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
         (Sassign (nested_efield e1 ids tts) e2)
         (normal_ret_assert
            (PROPx P
               (LOCALx Q
                  (SEPx
                     (replace_nth n R
                        (`(field_at sh (typeof e1) ids v') (eval_lvalue e1)
                          )))))).
Proof.
  intros.
  rewrite lifted_field_at_data_at in *; [|exact H1].
  rewrite lifted_field_at__data_at_ in *; [|exact H1|exact H1|exact H1].
  assert (Rn |-- 
           `prop (`(size_compatible (typeof e1)) (eval_lvalue e1)) &&
           `prop (`(align_compatible (typeof e1)) (eval_lvalue e1)) &&
           `prop (`(isSome (nested_field_rec (typeof e1) ids))) && Rn).
    apply andp_right; [apply (derives_trans _ _ _ H6) | apply derives_refl].
    apply andp_left1; apply derives_refl.
  rewrite (replace_nth_nth_error _ _ _ H5) at 1.
  eapply semax_pre0; [apply later_derives, replace_nth_SEP, H10|].

  rewrite andp_assoc.
  rewrite andp_assoc.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn); [|exact H5]).
  rewrite <- replace_nth_nth_error; [|exact H5].

  rewrite andp_assoc.
  rewrite andp_assoc.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn); [|exact H5]).

  rewrite andp_assoc in H9.
  rewrite andp_assoc in H9.
  repeat (rewrite (replace_nth_SEP_andp_local P _ R n Rn) in H9; [|exact H5]).


  eapply semax_post0; [| eapply semax_data_store_nth'].
  Focus 2. exact H.
  Focus 2. exact H0.
  Focus 2. exact H3.
  Focus 2. exact H4.
  Focus 2. exact H5.
  Focus 3. exact H7.
  
  + apply normal_ret_assert_derives'.
    apply replace_nth_SEP.
    unfold liftx, lift; simpl; intros.
    rewrite at_offset'_eq; [| rewrite <- data_at_offset_zero; reflexivity].
    erewrite eval_lvalue_nested_efield; [|exact H2].
    rewrite <- data_at_offset_zero.
    apply derives_refl.
  + apply (derives_trans _ _ _ H6).
    apply andp_left2.
    unfold liftx, lift; simpl; intros.
    rewrite at_offset'_eq; [| rewrite <- data_at__offset_zero; reflexivity].
    erewrite eval_lvalue_nested_efield; [|exact H2].
    rewrite <- data_at__offset_zero.
    apply derives_refl.
  + rewrite (replace_nth_nth_error R _ _ H5).
    rewrite LOCAL_2_hd. rewrite <- (replace_nth_SEP_andp_local P _ R n Rn); [|exact H5].
    rewrite LOCAL_2_hd. rewrite <- (replace_nth_SEP_andp_local P _ R n Rn); [|exact H5].
    rewrite LOCAL_2_hd. rewrite <- (replace_nth_SEP_andp_local P _ R n Rn); [|exact H5].
    eapply derives_trans; [|exact H8].
    rewrite (replace_nth_nth_error R _ _ H5) at 2.
    apply replace_nth_SEP.
    repeat apply andp_left2; apply derives_refl.
  + eapply derives_trans; [|exact H9].
    apply replace_nth_SEP.
    unfold liftx, lift; simpl; intros.
    rewrite at_offset'_eq; [| rewrite <- data_at__offset_zero; reflexivity].
    erewrite eval_lvalue_nested_efield; [|exact H2].
    rewrite <- data_at__offset_zero.
    apply derives_refl.
Qed.

(*
Lemma semax_store_field: 
forall Espec (Delta: tycontext) sh e1 fld P t2 e2 sid fields ,
    writable_share sh ->
    typeof e1 = Tstruct sid fields noattr ->
    t2 = type_of_field
             (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld ->
   @semax Espec Delta 
       (|> (local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
          (`(field_at_ sh (typeof e1) fld) (eval_lvalue e1) * P)))
       (Sassign (Efield e1 fld t2) e2) 
       (normal_ret_assert 
          (`(field_at sh (typeof e1) fld) 
                  (`force_val (`(sem_cast (typeof e2) t2) (eval_expr e2))) (eval_lvalue e1)  * P)).
Proof.
pose proof I. intros until fields. intro WS.
intros.
rename H0 into TE1.
unfold field_at_, field_at.

apply semax_pre0 with
 (EX v2: val,
   ((|>(local (tc_lvalue Delta e1) && local (tc_expr Delta (Ecast e2 t2)) &&
      (lift1(fun v1 : val =>
         match v1 with
         | Vundef => FF
         | Vint _ => FF
         | Vlong _ => FF
         | Vfloat _ => FF
         | Vptr l ofs =>
             match typeof e1 with
             | Tstruct id fList _ =>
                 match
                   field_offset fld
                     (unroll_composite_fields id (typeof e1) fList)
                 with
                 | Errors.OK delta =>
                     match
                       access_mode
                         (type_of_field
                            (unroll_composite_fields id (typeof e1) fList)
                            fld)
                     with
                     | By_value ch =>
                         !!(type_is_volatile
                              (type_of_field
                                 (unroll_composite_fields id (typeof e1)
                                    fList) fld) = false) &&
                         (address_mapsto ch v2 (Share.unrel Share.Lsh sh)
                            (Share.unrel Share.Rsh sh)
                            (l, Int.unsigned (Int.add ofs (Int.repr delta))))
                     | _ => FF
                     end
                 | _ => FF
                 end
             | _ => FF
             end
         end) (eval_lvalue e1) * P))))).
rewrite <- later_exp' by apply Vundef.
apply later_derives.
rewrite <- exp_andp2.
apply andp_derives; auto.
unfold lift1; intro rho; unfold_lift.
simpl sepcon. cbv beta.
rewrite TE1. rewrite <- H1. rewrite field_offset_unroll.
destruct (field_offset fld fields);
   try (rewrite FF_sepcon; apply FF_left).
normalize.
unfold mapsto.
destruct (access_mode t2);    try (rewrite FF_sepcon; apply FF_left).
destruct (type_is_volatile t2); try (rewrite FF_sepcon; apply FF_left).
case_eq (eval_lvalue e1 rho); simpl; intros; try rewrite FF_sepcon; try apply FF_left.
rewrite distrib_orp_sepcon.
apply orp_left.
normalize. elimtype False; clear - H3; destruct t2; contradiction.
normalize. apply exp_right with v2'. normalize.
apply extract_exists_pre; intro v0.

pose proof (semax_store Delta (Efield e1 fld t2) e2 sh 
               (local (`(tc_val t2) (`force_val (`(sem_cast (typeof e2) t2) (eval_expr e2)))) &&
                 !! (type_is_volatile t2 = false) &&   P)).
simpl typeof in H0. 
eapply semax_pre_post ; [ | | apply H0; auto]; clear H0.
match goal with |- (?A && |> ?B |-- |> ?C) =>
  apply derives_trans with (|> (A && B));
    [rewrite (later_andp A B); apply andp_derives; auto; apply now_later 
    | apply later_derives]
end.

intro rho; unfold lift1; unfold_lift.
 simpl andp; simpl sepcon. cbv beta.
rewrite TE1.
normalize.
unfold mapsto_, mapsto.
case_eq (eval_lvalue e1 rho); intros; try (rewrite FF_sepcon; apply FF_left).
case_eq (field_offset fld
    (unroll_composite_fields sid (Tstruct sid fields noattr) fields)); intros; try (rewrite FF_sepcon; apply FF_left).
rewrite <- H1.
case_eq (access_mode t2); intros; try (rewrite FF_sepcon; apply FF_left).
simpl eval_lvalue.
unfold lift1. unfold_lift. 
rewrite TE1. rewrite H4; simpl eval_field.
rewrite field_offset_unroll in H5. rewrite H5.
normalize.
rewrite H7.
repeat apply andp_right; try apply prop_right; 
  repeat simple apply conj; auto.
hnf; simpl. rewrite TE1.
rewrite H5. rewrite tc_andp_TT2.
rewrite denote_tc_assert_andp.
split; auto. rewrite H7; auto.
hnf in H3. simpl in H3.
rewrite denote_tc_assert_andp in H3. destruct H3.
rewrite tc_val_eq;
eapply expr_lemmas.typecheck_val_sem_cast; eassumption.
apply sepcon_derives; auto.
simpl.
apply orp_right2. apply andp_right; try apply prop_right; auto.
apply exp_right with v0; auto.

intros ek vl; unfold normal_ret_assert; go_lowerx.
normalize.
apply sepcon_derives; auto.
unfold mapsto, field_at.
rewrite TE1.
rewrite field_offset_unroll.
simpl.
case_eq (field_offset fld fields); simpl; intros; try apply FF_left.
rewrite <- H1.
destruct (access_mode t2); try apply FF_left.
destruct (type_is_volatile t2); try apply FF_left.
rewrite prop_true_andp by auto.
auto.
destruct (access_mode t2); try apply FF_left.
destruct (type_is_volatile t2); try apply FF_left.
Qed.

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
