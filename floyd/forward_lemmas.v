Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.
Import Cop.
Local Open Scope logic.

Lemma semax_frame_seq:
 forall {Espec: OracleKind} Frame Delta 
     P Q c1 c2 R P1 Q1 R1 P2 Q2 R2 R3,
    semax Delta (PROPx P1 (LOCALx Q1 (SEPx R1))) c1 
                      (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx R2)))) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
    PROPx P1 (LOCALx Q1 (SEPx (R1 ++ Frame))) ->
    closed_wrt_modvars c1 (SEPx Frame) ->
    semax (update_tycon Delta c1) 
         (PROPx P2 (LOCALx Q2 (SEPx (R2 ++ Frame)))) c2 R3 ->
    semax Delta (PROPx P (LOCALx Q (SEPx R))) (Ssequence c1 c2) R3.
Proof.
intros.
eapply semax_seq'.
eapply semax_pre.
apply H0.
apply semax_frame_PQR; auto.
apply H.
apply H2.
Qed.

Lemma semax_ifthenelse_PQR : 
   forall Espec Delta P Q R (b: expr) c d Post,
      bool_type (typeof b) = true ->
     @semax Espec Delta (PROPx P (LOCALx (`(typed_true (typeof b)) (eval_expr b) :: Q) (SEPx R)))
                        c Post -> 
     @semax Espec Delta (PROPx P (LOCALx (`(typed_false (typeof b)) (eval_expr b) :: Q) (SEPx R)))
                        d Post -> 
     @semax Espec Delta (PROPx P (LOCALx (tc_expr Delta b :: Q) (SEPx R)))
                         (Sifthenelse b c d) Post.
Proof.
 intros.
 eapply semax_pre0; [ | apply semax_ifthenelse]; auto.
 instantiate (1:=(PROPx P (LOCALx Q (SEPx R)))).
 clear. 
 go_lowerx.
 eapply semax_pre0; [ | eassumption].
 go_lowerx. apply andp_right; auto. apply prop_right; auto.
 eapply semax_pre0; [ | eassumption].
 go_lowerx. apply andp_right; auto. apply prop_right; auto.
Qed.

Definition logical_and_result v1 t1 v2 t2 :=
match (strict_bool_val t1 v1) with
| Some b1 => if b1 then match (strict_bool_val t2 v2) with
                            | Some b2 => if b2 then  Vint Int.one 
                                         else Vint Int.zero
                            | None => Vundef end
                   else Vint Int.zero
| None => Vundef
end.

Definition logical_or_result v1 t1 v2 t2 :=
match (strict_bool_val t1 v1) with
| Some b1 => if b1 then Vint Int.one
                   else match (strict_bool_val t2 v2) with
                            | Some b2 => if b2 then  Vint Int.one 
                                         else Vint Int.zero
                            | None => Vundef end
| None => Vundef
end.

Definition logical_or tid e1 e2 :=
(Sifthenelse e1
             (Sset tid (Econst_int (Int.repr 1) tint))
             (Ssequence
                (Sset tid (Ecast e2 tbool))
                (Sset tid (Ecast (Etempvar tid tbool) tint)))).


Definition logical_and tid e1 e2 :=
(Sifthenelse e1
            (Ssequence
              (Sset tid (Ecast e2 tbool))
              (Sset tid (Ecast (Etempvar tid tbool) tint)))
            (Sset tid (Econst_int (Int.repr 0) tint))).

Lemma semax_pre_flipped : 
 forall (P' : environ -> mpred) (Espec : OracleKind)
         (Delta : tycontext) (P1 : list Prop) (P2 : list (environ -> Prop))
         (P3 : list (environ -> mpred)) (c : statement) 
         (R : ret_assert),
       semax Delta P' c R ->
       PROPx P1 (LOCALx (tc_environ Delta :: P2) (SEPx P3)) |-- P' ->
        semax Delta (PROPx P1 (LOCALx P2 (SEPx P3))) c R.
Proof. intros. 
eapply semax_pre. apply H0. auto.
Qed.

Lemma tc_environ_init: forall Delta id rho,
                         tc_environ (initialized id Delta) rho ->
                         tc_environ Delta rho.
Proof.  
intros.
unfold tc_environ in *. destruct Delta. destruct p. destruct p.
unfold initialized in *. simpl in *. unfold temp_types in *.
unfold var_types in *. unfold ret_type in *. simpl in *.
remember (t1 ! id). destruct o; auto.
destruct p. unfold typecheck_environ in *. intuition.
clear - H0 Heqo. unfold typecheck_temp_environ in *.
intros. destruct (eq_dec id id0). subst.
specialize (H0 id0 true t3). spec H0.
unfold temp_types in *. simpl in *. rewrite PTree.gss. auto.
destruct H0. exists x. intuition. unfold temp_types in *.
simpl in H. rewrite H in *. inv Heqo. auto.
apply H0. 
unfold temp_types in *. simpl in *.
rewrite PTree.gso. auto. auto.
Qed.

Lemma bool_cast : forall e rho,
   tc_val (typeof e) (eval_expr e rho) ->
  force_val (Cop2.sem_cast tbool tint (force_val (Cop2.sem_cast (typeof e) tbool (eval_expr e rho)))) =
   match strict_bool_val (eval_expr e rho) (typeof e) with
   | Some true => Vint Int.one
   | Some false => Vint Int.zero
   | None => Vundef
   end.
Proof.
intros.
rewrite tc_val_eq in H.
 simpl. unfold Cop2.sem_cast.
remember (eval_expr e rho). destruct v. inv H. simpl.
remember (typeof e); destruct t; inv H; simpl;
remember (Int.eq i Int.zero); if_tac; auto; try congruence.
remember (typeof e); destruct t; inv H; simpl;
remember (Int64.eq i Int64.zero); if_tac; auto; try congruence.
remember (typeof e); destruct t; inv H. simpl.
if_tac; auto.
destruct (typeof e); inv H; auto.
Qed.

Lemma tycontext_eqv_sub:
  forall Delta Delta', tycontext_eqv Delta Delta' ->
         tycontext_sub Delta Delta'.
Admitted.

Lemma semax_while : 
 forall Espec Delta Q test body R,
     bool_type (typeof test) = true ->
     (local (tc_environ Delta) && Q |-- local (tc_expr Delta test)) ->
     (local (tc_environ Delta) && local (lift1 (typed_false (typeof test)) (eval_expr test)) && Q |-- R EK_normal None) ->
     @semax Espec Delta (local (`(typed_true (typeof test)) (eval_expr test)) && Q)  body (loop1_ret_assert Q R) ->
     @semax Espec Delta Q (Swhile test body) R.
Proof.
intros ? ? ? ? ? ? BT TC Post H.
unfold Swhile.
apply (@semax_loop Espec Delta Q Q).
Focus 2.
 clear; eapply semax_post; [ | apply semax_skip];
 destruct ek; unfold normal_ret_assert, loop2_ret_assert; intros;
 go_lowerx; try discriminate.
(* End Focus 2*)
apply semax_seq with 
 (local (`(typed_true (typeof test)) (eval_expr test)) && Q).
apply semax_pre_simple with (local (tc_expr Delta test) && Q).
apply andp_right. apply TC.
apply andp_left2.
intro; auto.
apply semax_ifthenelse; auto.
eapply semax_post; [ | apply semax_skip].
intros.
 unfold normal_ret_assert, overridePost;  go_lowerx.
 subst. rewrite if_true by auto. repeat rewrite prop_true_andp by auto. auto.
eapply semax_pre_simple; [ | apply semax_break].
 unfold overridePost. go_lowerx.
eapply derives_trans; try apply Post.
 unfold local,lift0,lift1; simpl.
 repeat apply andp_right; try apply prop_right; auto.
simpl update_tycon.
apply semax_extensionality_Delta with Delta; auto.
apply tycontext_eqv_sub. 
apply tycontext_eqv_symm; apply join_tycon_same.
Qed.

Lemma semax_while' : 
 forall Espec Delta P Q R test body Post,
     bool_type (typeof test) = true ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta test) ->
     PROPx P (LOCALx (tc_environ Delta :: `(typed_false (typeof test)) (eval_expr test) :: Q) (SEPx R)) |-- Post EK_normal None ->
     @semax Espec Delta (PROPx P (LOCALx (`(typed_true (typeof test)) (eval_expr test) :: Q) (SEPx R)))  body (loop1_ret_assert (PROPx P (LOCALx Q (SEPx R))) Post) ->
     @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) (Swhile test body) Post.
Proof.
intros.
apply semax_while; auto.
eapply derives_trans; [ | apply H0].
normalize.
eapply derives_trans; [ | apply H1].
 go_lowerx.
 apply andp_right; auto. apply prop_right; auto.
eapply semax_pre_simple; [ | apply H2].
 go_lowerx.  apply andp_right; auto. apply prop_right; auto.
Qed.

Lemma semax_whilex : 
 forall Espec Delta A P Q R test body Post,
     bool_type (typeof test) = true ->
     (forall x, PROPx (P x) (LOCALx (tc_environ Delta :: (Q x)) (SEPx (R x))) |-- 
                               local (tc_expr Delta test)) ->
     (forall x, PROPx (P x) (LOCALx (tc_environ Delta :: `(typed_false (typeof test)) (eval_expr test) :: (Q x)) (SEPx (R x))) 
                    |-- Post EK_normal None) ->
     (forall x:A, @semax Espec Delta (PROPx (P x) (LOCALx (`(typed_true (typeof test)) (eval_expr test) :: Q x) (SEPx (R x))))  
                           body 
                            (loop1_ret_assert (EX x:A, PROPx (P x) (LOCALx (Q x) (SEPx (R x)))) Post))->
     @semax Espec Delta (EX x:A, PROPx (P x) (LOCALx (Q x) (SEPx (R x) ))) (Swhile test body) Post.
Proof.
intros.
apply semax_while; auto.
rewrite exp_andp2.
apply exp_left. intro x; eapply derives_trans; [ | apply (H0 x)].
 go_lowerx. apply andp_right; auto. apply prop_right; auto.
rewrite exp_andp2.
apply exp_left. intro x; eapply derives_trans; [ | apply (H1 x)].
 go_lowerx. apply andp_right; auto. apply prop_right; auto.
normalize.
apply extract_exists_pre; intro x.
eapply semax_pre_simple; [ | apply (H2 x)].
 go_lowerx. apply andp_right; auto. apply prop_right; auto.
Qed.

Lemma semax_whilex2 : 
 forall Espec Delta A1 A2 P Q R test body Post,
     bool_type (typeof test) = true ->
     (forall x1 x2, PROPx (P x1 x2) (LOCALx (tc_environ Delta :: (Q x1 x2)) (SEPx (R x1 x2))) |-- 
                               local (tc_expr Delta test)) ->
     (forall x1 x2, PROPx (P x1 x2) (LOCALx (tc_environ Delta :: `(typed_false (typeof test)) (eval_expr test) :: (Q x1 x2)) (SEPx (R x1 x2))) 
                    |-- Post EK_normal None) ->
     (forall (x1:A1) (x2: A2), 
               @semax Espec Delta (PROPx (P x1 x2) (LOCALx (`(typed_true (typeof test)) (eval_expr test) :: Q x1 x2) (SEPx (R x1 x2))))  
                           body 
                            (loop1_ret_assert (EX x1:A1, EX x2:A2, PROPx (P x1 x2) (LOCALx (Q x1 x2) (SEPx (R x1 x2)))) Post))->
     @semax Espec Delta (EX x1:A1, EX x2:A2, PROPx (P x1 x2) (LOCALx (Q x1 x2) (SEPx (R x1 x2) ))) (Swhile test body) Post.
Proof.
intros.
apply semax_while; auto.
rewrite exp_andp2. apply exp_left. intro x1.
rewrite exp_andp2. apply exp_left. intro x2.
 eapply derives_trans; [ | apply (H0 x1 x2)].
 go_lowerx. apply andp_right; auto. apply prop_right; auto.
rewrite exp_andp2. apply exp_left. intro x1.
rewrite exp_andp2. apply exp_left. intro x2.
 eapply derives_trans; [ | apply (H1 x1 x2)].
 go_lowerx. apply andp_right; auto. apply prop_right; auto.
rewrite exp_andp2.  apply extract_exists_pre; intro x1.
rewrite exp_andp2. apply extract_exists_pre; intro x2.
eapply semax_pre_simple; [ | apply (H2 x1 x2)].
 go_lowerx. apply andp_right; auto. apply prop_right; auto.
Qed.

Lemma closed_wrt_map_subst':
   forall {A: Type} id e (Q: list (environ -> A)),
         Forall (closed_wrt_vars (eq id)) Q ->
         @map (LiftEnviron A) _ (subst id e) Q = Q.
Proof.
apply @closed_wrt_map_subst.
Qed.

Hint Rewrite @closed_wrt_map_subst' using safe_auto_with_closed : norm.
Hint Rewrite @closed_wrt_map_subst' using safe_auto_with_closed : subst.

Lemma forward_setx_closed_now':
  forall Espec Delta P (Q: list (environ -> Prop)) (R: list (environ->mpred)) id e,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
  closed_wrt_vars (eq id) (eval_expr e) ->
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta e)  ->
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))  |-- local (tc_temp_id id (typeof e) Delta e) ->
  @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) (Sset id e) 
        (normal_ret_assert (PROPx P (LOCALx (`eq (eval_id id) (eval_expr e)::Q) (SEPx R)))).
Proof.
intros.
eapply semax_pre_simple; [ | apply semax_set].
rewrite insert_local.
eapply derives_trans; [ | apply now_later].
apply andp_right; auto.
apply andp_right; auto.
autorewrite with subst.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; unfold local,lift1; simpl.
apply prop_derives; simpl; intro; split; auto.
unfold_lift; reflexivity.
unfold_lift; unfold_lift in H4. destruct H4; auto.
Qed.


Lemma forward_setx_closed_now:
  forall Espec Delta (Q: list (environ -> Prop)) (R: list (environ->mpred)) id e PQR,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
  closed_wrt_vars (eq id) (eval_expr e) ->
  PROPx nil (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta e)  ->
  PROPx nil (LOCALx (tc_environ Delta :: Q) (SEPx R))  |-- local (tc_temp_id id (typeof e) Delta e) ->
  normal_ret_assert (PROPx nil (LOCALx (`eq (eval_id id) (eval_expr e)::Q) (SEPx R))) |-- PQR ->
  @semax Espec Delta (PROPx nil (LOCALx Q (SEPx R))) (Sset id e) PQR.
Proof.
intros.
eapply semax_post.
intros ek vl. apply andp_left2. apply H4.
apply forward_setx_closed_now'; auto.
Qed.


Lemma forward_ptr_compare_closed_now :
forall Espec Delta P Q R id e1 e2 cmp ty sh1 sh2 PQR
(TID : typecheck_tid_ptr_compare Delta id = true), 
Forall (closed_wrt_vars (eq id)) Q ->
Forall (closed_wrt_vars (eq id)) R ->
closed_wrt_vars (eq id) (eval_expr ((Ebinop cmp e1 e2 ty))) ->
( PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta (Ebinop cmp e1 e2 ty))  /\
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))  |-- local (tc_temp_id id (ty) Delta (Ebinop cmp e1 e2 ty)))
\/
PROPx P (LOCALx ((tc_environ Delta)::Q) (SEPx R)) |-- (local (tc_expr Delta e1) && local (tc_expr Delta e2) &&
      local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
      (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
      (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT)) ->
((normal_ret_assert
     (PROPx P (LOCALx (`eq (eval_id id) 
                     (eval_expr ((Ebinop cmp e1 e2 ty))) :: Q)
          (SEPx  R))))) |-- PQR ->
is_comparison cmp = true ->
@semax Espec Delta
  (PROPx P (LOCALx Q (SEPx R))) (Sset id (Ebinop cmp e1 e2 ty)) PQR
  .
Proof. 
intros.
intuition.
eapply semax_post; [ | apply forward_setx_closed_now'; auto with closed].
intros.  intro rho. normalize. apply H3.

eapply semax_post. intros ek vl rho. 
simpl. apply andp_left2. apply H3.

eapply semax_pre_post; [ | | eapply (semax_ptr_compare Delta (PROPx P (LOCALx Q (SEPx R))) _ _ _ _ _ sh1 sh2)]; auto.
  +eapply derives_trans; [ | apply now_later].
  apply andp_right. rewrite insert_local.  apply H5. apply andp_left2; auto.
  
  +intros ex vl.
    unfold normal_ret_assert.
    repeat rewrite exp_andp2; apply exp_left; intro old.
    autorewrite with subst.
    go_lowerx.    repeat apply andp_right; try apply prop_right; auto. 
Qed.  

Lemma forward_setx_closed_now_seq:
  forall Espec Delta (Q: list (environ -> Prop)) (R: list (environ->mpred)) id e c PQR,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
  closed_wrt_vars (eq id) (eval_expr e) ->
  PROPx nil (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta e)  ->
  PROPx nil (LOCALx (tc_environ Delta :: Q) (SEPx R))  |-- local (tc_temp_id id (typeof e) Delta e) ->
  semax (update_tycon Delta (Sset id e))
           (PROPx nil (LOCALx (`eq (eval_id id) (eval_expr e)::Q) (SEPx R))) c PQR ->
  @semax Espec Delta (PROPx nil (LOCALx Q (SEPx R))) (Ssequence (Sset id e) c) PQR.
Proof.
 intros.
 eapply semax_seq.
 apply sequential'.
 apply forward_setx_closed_now; auto.
 apply H4.
Qed.

Lemma writable_share_top: writable_share Tsh.
Admitted.
Hint Resolve writable_share_top.


Lemma field_mapsto_mapsto__at1:
  forall Espec Delta P Q sh ty fld e v R c Post,
    @semax Espec Delta (PROPx P (LOCALx Q (SEPx (`(field_mapsto_ sh ty fld) e :: R)))) c Post ->
    @semax Espec Delta (PROPx P (LOCALx Q (SEPx (`(field_mapsto sh ty fld) e v :: R)))) c Post.
Proof.
intros.
 eapply semax_pre0; [ | apply H].
 intro rho; unfold PROPx, LOCALx, SEPx.
 simpl.
 apply andp_derives; auto.
 apply andp_derives; auto.
 apply sepcon_derives; auto.
 unfold_lift; apply field_mapsto_field_mapsto_.
Qed.

Lemma later_field_mapsto_mapsto__at1:
  forall Espec Delta P Q sh ty fld e v R c Post,
    @semax Espec Delta (PROPx P (LOCALx Q (SEPx (|>`(field_mapsto_ sh ty fld) e :: R)))) c Post ->
    @semax Espec Delta (PROPx P (LOCALx Q (SEPx (|> `(field_mapsto sh ty fld) e v :: R)))) c Post.
Proof.
intros.
 eapply semax_pre0; [ | apply H].
 intro rho; unfold PROPx, LOCALx, SEPx.
 simpl.
 apply andp_derives; auto.
 apply andp_derives; auto.
 apply sepcon_derives; auto.
 apply later_derives; auto.
 unfold_lift; apply field_mapsto_field_mapsto_.
Qed.

Lemma forward_setx':
  forall Espec Delta P id e,
  (P |-- local (tc_expr Delta e) && local (tc_temp_id id (typeof e) Delta e) ) ->
  @semax Espec Delta
             P
             (Sset id e)
             (normal_ret_assert
                  (EX old:val,  local (`eq (eval_id id) (subst id (`old) (eval_expr e))) &&
                            subst id (`old) P)).
Proof.
intros.
eapply semax_pre_post; [ | | apply (semax_set_forward Delta P id e); auto].
+ eapply derives_trans ; [ | apply now_later].
   apply andp_left2; apply andp_right; auto.
+ intros ek vl; unfold normal_ret_assert; go_lowerx.
Qed.


Lemma forward_setx:
  forall Espec Delta P Q R id e,
  (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta e) && local (tc_temp_id id (typeof e) Delta e) ) ->
  @semax Espec Delta
             (PROPx P (LOCALx Q (SEPx R)))
             (Sset id e)
             (normal_ret_assert
                  (EX old:val,  
                    PROPx P
                     (LOCALx (`eq (eval_id id) (subst id (`old) (eval_expr e)) ::
                                     map (subst id (`old)) Q)
                      (SEPx (map (subst id (`old)) R))))).
Proof.
 intros.
intros.
eapply semax_pre_post;
   [ | | apply (semax_set_forward Delta (PROPx P (LOCALx (tc_environ Delta :: Q)  (SEPx R))) id e); auto].
+  eapply derives_trans ; [ | apply now_later].
  rewrite andp_assoc.  repeat rewrite insert_local.
 rewrite <- (andp_dup (PROPx _ (LOCALx (_ :: Q) _))).
 eapply derives_trans; [apply andp_derives  | ].
 apply H. apply derives_refl.
  rewrite andp_assoc.  repeat rewrite insert_local.
 apply derives_refl.
+
 intros ek vl.
 intro rho.
 unfold andp at 1. unfold LiftNatDed', LiftNatDed.
 unfold local at 1. unfold lift1.
 apply derives_extract_prop. intro.
 apply normal_ret_assert_derives'.
 apply exp_derives; intro x.
  autorewrite with subst.
 rewrite insert_local.
 clear.
 go_lowerx. simpl. apply andp_right; auto.
 apply prop_right; repeat split; auto. 
Qed.

Lemma forward_setx_weak:
  forall Espec Delta P Q R id e,
  (PROPx P (LOCALx Q (SEPx R)) |-- local (tc_expr Delta e) && local (tc_temp_id id (typeof e) Delta e) ) ->
  @semax Espec Delta
             (PROPx P (LOCALx Q (SEPx R)))
             (Sset id e)
             (normal_ret_assert
                  (EX old:val,  
                    PROPx P
                     (LOCALx (`eq (eval_id id) (subst id (`old) (eval_expr e)) ::
                                     map (subst id (`old)) Q)
                      (SEPx (map (subst id (`old)) R))))).
Proof.
 intros.
 eapply semax_post; [ | apply forward_setx'; auto].
 intros.
 autorewrite with ret_assert subst.
 repeat rewrite normal_ret_assert_eq.
 repeat rewrite exp_andp2. apply exp_derives; intro x.
  autorewrite with subst.
 go_lowerx. repeat apply andp_right; try apply prop_right; auto.
Qed.

Lemma forward_ptr_compare'': 
forall Espec Delta P id e1 e2 sh1 sh2 cmp ty, 
P |-- (local (tc_expr Delta e1) && local (tc_expr Delta e2) &&
      local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
      (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
      (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT)) ->
is_comparison cmp = true ->
typecheck_tid_ptr_compare Delta id = true ->
@semax Espec Delta
  P
    (Sset id (Ebinop cmp e1 e2 ty))
  ((normal_ret_assert
     (EX  old : val,
       (local (`eq (eval_id id) (subst id `old (eval_expr 
                                     (Ebinop cmp e1 e2 ty))))) &&
       (subst id (`old)) P))).
Proof. 
intros.
eapply semax_pre_post; [ | | apply (semax_ptr_compare Delta P _ _ _ _ _ sh1 sh2)]; auto. 
+ eapply derives_trans; [ | apply now_later].
    apply andp_left2. apply andp_right; auto.
+ intros ek vl. unfold normal_ret_assert.
   repeat rewrite exp_andp2. apply exp_derives; intro x.
  apply andp_left2; auto.
Qed. 

Lemma forward_ptr_compare' : 
forall {Espec: OracleKind},
forall (Delta: tycontext) P Q R id cmp e1 e2 ty sh1 sh2 PQR,
    is_comparison cmp = true  ->
    typecheck_tid_ptr_compare Delta id = true ->
    (PROPx P (LOCALx Q (SEPx R)) |-- 
           local (tc_expr Delta (Ebinop cmp e1 e2 ty)) && 
           local (tc_temp_id id ty Delta 
                             (Ebinop cmp e1 e2 ty))) \/
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
         |-- local (tc_expr Delta e1) &&
             local (tc_expr Delta e2)  && 
          local (`(SeparationLogic.blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1 ) * TT) && 
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2 ) * TT) ->
    (normal_ret_assert 
          (EX old:val, 
           PROPx P
           (LOCALx (`eq (eval_id id)  (subst id `old 
                     (eval_expr (Ebinop cmp e1 e2 ty))) ::
                       map (subst id `old) Q)
           (SEPx (map (subst id `old) R))))) |-- PQR ->
   @semax Espec Delta 
         (PROPx P (LOCALx Q (SEPx R)))
          (Sset id (Ebinop cmp e1 e2 ty)) PQR
        .
Proof.
intros.
intuition.
eapply semax_post.
intros ek vl rho. simpl. apply andp_left2.
apply H2. 
apply forward_setx_weak; auto.

eapply semax_post. intros ek vl rho.
simpl. apply andp_left2. apply H2.
eapply semax_pre_post; [ | | apply (semax_ptr_compare Delta (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))) _ _ _ _ _ sh1 sh2)].
eapply derives_trans; [ | apply now_later].
rewrite insert_local; apply andp_right; auto.
intros ek vl. unfold normal_ret_assert.
repeat rewrite exp_andp2. apply exp_derives; intro x.
autorewrite with subst.
go_lowerx. repeat apply andp_right; try apply prop_right; auto.
auto. auto. 
Qed.


Lemma forward_ptr_compare:
forall Espec Delta P Q R id e1 e2 sh1 sh2 cmp ty, 
PROPx P (LOCALx Q (SEPx R)) |-- (local (tc_expr Delta e1) && local (tc_expr Delta e2) &&
      local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
      (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
      (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT)) ->
is_comparison cmp = true ->
typecheck_tid_ptr_compare Delta id = true ->
@semax Espec Delta
  (PROPx P (LOCALx Q (SEPx R)))
    (Sset id (Ebinop cmp e1 e2 ty))
 (normal_ret_assert 
          (EX old:val, 
           PROPx P
           (LOCALx (`eq (eval_id id)  (subst id `old 
                     (eval_expr (Ebinop cmp e1 e2 ty))) ::
                       map (subst id `old) Q)
           (SEPx (map (subst id `old) R))))). 
Proof. 
 intros.
 eapply semax_post; [ | apply forward_ptr_compare'' with (sh1 := sh1) (sh2 := sh2); auto].
 intros.
 autorewrite with ret_assert subst.
 repeat rewrite normal_ret_assert_eq.
repeat rewrite exp_andp2. apply exp_derives; intro x.
 autorewrite with  subst.  go_lowerx.
 repeat apply andp_right; try apply prop_right; auto. 
Qed. 

Lemma normal_ret_assert_derives':
  forall ek vl P Q, 
      P |-- Q ->
      normal_ret_assert P ek vl |-- normal_ret_assert Q ek vl.
Proof. intros; intro rho. apply normal_ret_assert_derives. auto.
Qed.

Lemma normal_ret_assert_derives'':
  forall (P: environ->mpred) (Q: ret_assert), 
      (P |-- Q EK_normal None) ->
      normal_ret_assert P |-- Q.
Proof. intros; intros ek vl; unfold normal_ret_assert.
  go_lowerx. subst; apply H.
Qed.

Lemma after_set_special1:
  forall (A: Type) id e Delta Post  P Q R,
    EX x:A, PROPx (P x) (LOCALx (tc_environ(initialized id Delta) :: Q x) (SEPx (R x))) |-- Post ->
 forall ek vl,
   local (tc_environ (exit_tycon (Sset id e) Delta ek)) && 
    normal_ret_assert (EX  x : A, PROPx (P x) (LOCALx (Q x) (SEPx (R x)))) ek vl 
   |-- normal_ret_assert Post ek vl.
Proof.
 intros. unfold normal_ret_assert.
 repeat rewrite exp_andp2.
 apply exp_left; intro x.
 apply andp_right. go_lowerx; apply prop_right; auto.
 apply andp_right. go_lowerx; apply prop_right; auto.
 eapply derives_trans; [ | apply H].
 apply exp_right with x.
 rewrite <- insert_local.
 go_lowerx. subst.
 repeat apply andp_right; try apply prop_right; auto.
Qed.


Lemma elim_redundant_Delta:
  forall Espec Delta P Q R c Post,
  @semax Espec Delta (PROPx P (LOCALx Q R)) c Post ->
  @semax Espec Delta (PROPx P (LOCALx (tc_environ Delta:: Q) R)) c Post.
Proof.
 intros.
 eapply semax_pre_simple; try apply H.
  apply andp_left2.
 intro rho; simpl.
 unfold PROPx; simpl; apply andp_derives; auto.
  unfold LOCALx; simpl; apply andp_derives; auto.
  unfold local,lift1; unfold_lift; simpl.
 apply prop_derives; intros [? ?]; auto.
Qed.

Lemma semax_load_assist1:
  forall B P Q1 Q R,
  (forall rho, Q1 rho = True) ->
  B && PROPx P (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx (Q1::Q) (SEPx R)).
Proof.
 intros. rewrite <- insert_local. apply andp_derives; auto.
 intro rho; apply prop_right; simpl. rewrite H; auto.
Qed.

Lemma snd_split_map {A B}:
  forall l: list (A*B), map (@snd _ _) l = snd (split l).
Proof.
  induction l; simpl; auto. destruct a. rewrite IHl.
destruct (split l); f_equal; auto.
Qed.

Opaque tc_andp.

Lemma tc_expr_init:
  forall i Delta rho e, tc_expr Delta e rho ->
                 tc_expr (initialized i Delta) e rho
with tc_lvalue_init:
  forall i Delta rho e, tc_lvalue Delta e rho ->
                 tc_lvalue (initialized i Delta) e rho.
Proof.
clear tc_expr_init; induction e; intros; auto;
 unfold tc_expr in *; simpl in *.
 destruct (access_mode t) eqn:?; auto.
  unfold get_var_type in *.
 rewrite expr_lemmas.set_temp_ve.
 destruct ((var_types Delta) ! i0); auto.
 rewrite expr_lemmas.set_temp_ge.
 destruct ((glob_types Delta) ! i0); auto.
 destruct (negb (type_is_volatile t)); auto.
 destruct ( (temp_types Delta) ! i0) eqn:?; [ | contradiction].
 destruct p.  
 destruct (eq_dec i i0). subst. 
  apply temp_types_init_same in Heqo. rewrite Heqo.
  destruct b; [apply H | ]. simpl in *.
  if_tac; auto. apply I.
  rewrite <- expr_lemmas.initialized_ne by auto.  rewrite Heqo.
  auto.
  rewrite denote_tc_assert_andp in H|-*.
  destruct H; split; auto. apply tc_lvalue_init; auto.
  rewrite denote_tc_assert_andp in H|-*.
 destruct H; split; auto.
  repeat rewrite denote_tc_assert_andp in H|-*.
  destruct H as [[? ?] ?]. split; auto.
    rewrite denote_tc_assert_andp in H|-*.
  destruct H; split; auto.
 destruct (access_mode t); auto.
  repeat rewrite denote_tc_assert_andp in H|-*.
  destruct H as [[? ?] ?]. split; auto. split; auto.
 apply tc_lvalue_init; auto.

 clear tc_lvalue_init.
 unfold tc_lvalue; induction e; simpl; auto; intro.
 unfold get_var_type in *.  rewrite expr_lemmas.set_temp_ve.
 destruct ((var_types Delta) ! i0); auto.
rewrite expr_lemmas.set_temp_ge.
 destruct ((glob_types Delta) ! i0); auto.
   repeat rewrite denote_tc_assert_andp in H|-*.
 decompose [and] H; repeat split; auto.
 apply tc_expr_init; auto.
   repeat rewrite denote_tc_assert_andp in H|-*.
 decompose [and] H; clear H; repeat split; auto.
Qed.
Transparent tc_andp.  (* ? should leave it opaque, maybe? *)

Lemma semax_logical_or:
 forall Espec Delta P Q R tid e1 e2 b
   (CLOSQ : Forall (closed_wrt_vars (eq tid)) Q)
   (CLOSR : Forall (closed_wrt_vars (eq tid)) R)
   (CLOSE1 : closed_wrt_vars (eq tid) (eval_expr e1))
   (CLOSE2 : closed_wrt_vars (eq tid) (eval_expr e2)),
 bool_type (typeof e1) = true ->
 bool_type (typeof e2) = true ->
 (temp_types Delta) ! tid = Some (tint, b) ->
  @semax Espec Delta (PROPx P (LOCALx ((tc_expr Delta e1)::
              (`or (`(typed_true (typeof e1)) (eval_expr e1))  (tc_expr Delta e2))::tc_temp_id tid tbool Delta (Ecast e2 tbool) ::
   Q) (SEPx (R))))
    (logical_or tid e1 e2)
  (normal_ret_assert (PROPx P (LOCALx 
((`eq (eval_id tid) 
   (`logical_or_result 
          `(typeof e1) (eval_expr e1) `(typeof e2) (eval_expr e2)))::Q) (SEPx (R))))). 
Proof.
intros.
apply semax_ifthenelse_PQR. 
  - auto. 
  -  eapply semax_pre. apply derives_refl.
     eapply semax_post_flipped.
     apply forward_setx. 
     go_lowerx. apply andp_right; apply prop_right.
    apply I.   unfold tc_temp_id, typecheck_temp_id. rewrite H1.
     simpl. apply I.
     intros ek vl.
    unfold normal_ret_assert. repeat rewrite exp_andp2.
     apply exp_left;  intro.
     autorewrite with subst.
   replace (`(typed_true (typeof e1)) (subst tid `x (eval_expr e1)))
    with (`(typed_true (typeof e1)) (eval_expr e1))
  by (extensionality rho; unfold_lift; autorewrite with subst; auto).
   go_lowerx. subst. apply andp_right; auto. apply prop_right; split; auto.
   rewrite H6.
   unfold logical_or_result.
 destruct (typeof e1), (eval_expr e1 rho); inv H; inv H8; simpl;
   try rewrite H3; auto.
  - eapply semax_seq'. 
      + eapply forward_setx_weak.
         go_lowerx. 
         destruct H4. congruence.
         apply andp_right; apply prop_right; auto.
        unfold tc_expr. simpl. rewrite tc_andp_sound.
        simpl. super_unfold_lift. split. auto. 
        unfold isCastResultType. destruct (typeof e2); 
                                        inv H0; simpl; apply I.
      + simpl update_tycon. apply extract_exists_pre. intro oldval.
        autorewrite with subst.  
        apply (semax_pre ((PROPx P
        (LOCALx
           (tc_environ (initialized tid Delta) ::
             `eq (eval_id tid) (eval_expr (Ecast e2 tbool))
            :: `(typed_false (typeof e1)) (eval_expr e1)
               :: `or (`(typed_true (typeof e1)) (eval_expr e1))
                    (tc_expr Delta e2)
                  :: Q)
           (SEPx R))))).
       go_lowerx. repeat apply andp_right; auto. apply prop_right; auto.
        eapply semax_post_flipped.
        eapply forward_setx.
        go_lowerx. apply andp_right; apply prop_right; auto.
        unfold tc_expr. simpl. rewrite tc_andp_sound. 
        super_unfold_lift. split. 
        erewrite temp_types_init_same by eauto. simpl. apply I.
         apply I.
        simpl. unfold tc_temp_id. unfold typecheck_temp_id.
        erewrite temp_types_init_same by eauto. rewrite tc_andp_sound.
        simpl. super_unfold_lift; auto.
        intros. unfold normal_ret_assert.
        repeat rewrite exp_andp2. apply exp_left; intro.
       simpl eval_expr. 
       autorewrite with subst.
       rewrite (closed_wrt_subst _ _ (eval_expr e1)) by auto.
       rewrite (closed_wrt_subst _ _ (eval_expr e2)) by auto.
       go_lowerx. apply andp_right; auto. apply prop_right; split; auto.
       rewrite H6. rewrite H8.
        unfold logical_or_result.
        subst ek vl. simpl in  H2.
        rewrite H9.
       unfold subst in *.
       apply bool_cast.
      replace (eval_expr e2 rho) with (eval_expr e2 (env_set rho tid x))
      by (symmetry; apply CLOSE2; intro i; destruct (eq_dec tid i); [left; auto | right]; rewrite Map.gso by auto; auto).
      eapply expr_lemmas.typecheck_expr_sound; eauto.
    apply tc_expr_init. destruct H10; congruence.
Qed.

Lemma semax_logical_and:
 forall Espec Delta P Q R tid e1 e2 b
   (CLOSQ : Forall (closed_wrt_vars (eq tid)) Q)
   (CLOSR : Forall (closed_wrt_vars (eq tid)) R)
   (CLOSE1 : closed_wrt_vars (eq tid) (eval_expr e1))
   (CLOSE2 : closed_wrt_vars (eq tid) (eval_expr e2)),
 bool_type (typeof e1) = true ->
 bool_type (typeof e2) = true ->
 (temp_types Delta) ! tid = Some (tint, b) ->
  @semax Espec Delta (PROPx P (LOCALx ((tc_expr Delta e1)::
    (`or (`(typed_false (typeof e1)) (eval_expr e1))  (tc_expr Delta e2))::tc_temp_id tid tbool Delta (Ecast e2 tbool) ::
   Q) (SEPx (R))))
    (logical_and tid e1 e2)
  (normal_ret_assert (PROPx P (LOCALx 
((`eq (eval_id tid) 
   (`logical_and_result 
          `(typeof e1) (eval_expr e1) `(typeof e2) (eval_expr e2)))::Q) (SEPx (R)))))
  . 
Proof.
intros.
apply semax_ifthenelse_PQR. 
  - auto. 
  - eapply semax_seq'. 
      + eapply forward_setx_weak.
         go_lowerx. apply andp_right; apply prop_right; auto.
        unfold tc_expr. simpl. rewrite tc_andp_sound.
        simpl. super_unfold_lift. split.
        destruct H4; auto; congruence.         
        unfold isCastResultType. destruct (typeof e2); 
                                        inv H0; simpl; apply I.
      + simpl update_tycon. apply extract_exists_pre. intro oldval.
        autorewrite with subst.  
        apply (semax_pre ((PROPx P
        (LOCALx
           (tc_environ (initialized tid Delta) ::
             `eq (eval_id tid) (eval_expr (Ecast e2 tbool))
            :: `(typed_true (typeof e1)) (eval_expr e1)
               :: `or (`(typed_false (typeof e1)) (eval_expr e1))
                    (tc_expr Delta e2)
                  :: Q)
           (SEPx R))))).
       go_lowerx. repeat apply andp_right; auto. apply prop_right; auto.
        eapply semax_post_flipped.
        eapply forward_setx.
        go_lowerx. apply andp_right; apply prop_right; auto.
        unfold tc_expr. simpl. rewrite tc_andp_sound. 
        super_unfold_lift. split. 
        erewrite temp_types_init_same by eauto. simpl. apply I.
         apply I.
        simpl. unfold tc_temp_id. unfold typecheck_temp_id.
        erewrite temp_types_init_same by eauto. rewrite tc_andp_sound.
        simpl. super_unfold_lift; auto.
        intros. unfold normal_ret_assert.
        repeat rewrite exp_andp2. apply exp_left; intro.
       simpl eval_expr. 
       autorewrite with subst.
       rewrite (closed_wrt_subst _ _ (eval_expr e1)) by auto.
       rewrite (closed_wrt_subst _ _ (eval_expr e2)) by auto.
       go_lowerx. apply andp_right; auto. apply prop_right; split; auto.
       rewrite H6. rewrite H8.
        unfold logical_and_result.
        subst ek vl. simpl in  H2.
        rewrite H9.
       unfold subst in *.
       apply bool_cast.
      replace (eval_expr e2 rho) with (eval_expr e2 (env_set rho tid x))
      by (symmetry; apply CLOSE2; intro i; destruct (eq_dec tid i); [left; auto | right]; rewrite Map.gso by auto; auto).
        eapply expr_lemmas.typecheck_expr_sound; eauto.
        destruct H10; try congruence.
    apply tc_expr_init; congruence.
- eapply semax_pre. apply derives_refl.
     eapply semax_post_flipped.
     apply forward_setx. 
     go_lowerx. apply andp_right; try apply prop_right; auto.
     apply I.
     unfold tc_temp_id. unfold typecheck_temp_id. rewrite H1.
     simpl. apply I.
     intros ek vl. unfold normal_ret_assert.
   repeat rewrite exp_andp2. apply exp_left; intro x.
   autorewrite with subst.  
    go_lowerx. apply andp_right; auto.
  apply prop_right; split; auto.
     unfold logical_and_result. unfold typed_false in *.
    autorewrite with subst in H8. rewrite H8.
    apply H6.
Qed.

Lemma semax_logical_and_PQR: 
  forall Espec Delta P Q R PQR tid e1 e2 b
   (CLOSQ : Forall (closed_wrt_vars (eq tid)) Q)
   (CLOSR : Forall (closed_wrt_vars (eq tid)) R)
   (CLOSE1 : closed_wrt_vars (eq tid) (eval_expr e1))
   (CLOSE2 : closed_wrt_vars (eq tid) (eval_expr e2)),
 bool_type (typeof e1) = true ->
 bool_type (typeof e2) = true ->
 (temp_types Delta) ! tid = Some (tint, b) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta e1) &&
         (local (`(typed_false (typeof e1)) (eval_expr e1)) || local (tc_expr Delta e2)) && local (tc_temp_id tid tbool Delta (Ecast e2 tbool)) ->
  (normal_ret_assert (PROPx P (LOCALx ((`eq (eval_id tid) (`logical_and_result 
          `(typeof e1) (eval_expr e1) `(typeof e2) (eval_expr e2)))::Q) (SEPx (R))))) |-- PQR ->   
   @semax Espec Delta (PROPx P (LOCALx (Q) (SEPx (R))))
    (logical_and tid e1 e2) PQR.
Proof.
intros. 
eapply semax_pre_flipped.
eapply semax_post_flipped. 
eapply semax_logical_and; try eassumption.
intros.
specialize (H3 ek vl). 
apply andp_left2. apply H3.
intro rho. specialize (H2 rho). normalize. normalize in H2.
apply andp_right; auto.
eapply derives_trans; [ apply H2 | ].
normalize. simpl. apply orp_left; normalize.
Qed.

Lemma semax_logical_or_PQR: 
  forall Espec Delta P Q R PQR tid e1 e2 b
   (CLOSQ : Forall (closed_wrt_vars (eq tid)) Q)
   (CLOSR : Forall (closed_wrt_vars (eq tid)) R)
   (CLOSE1 : closed_wrt_vars (eq tid) (eval_expr e1))
   (CLOSE2 : closed_wrt_vars (eq tid) (eval_expr e2)),
 bool_type (typeof e1) = true ->
 bool_type (typeof e2) = true ->
 (temp_types Delta) ! tid = Some (tint, b) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta e1) &&
        (local (`(typed_true (typeof e1)) (eval_expr e1)) || local (tc_expr Delta e2)) && local (tc_temp_id tid tbool Delta (Ecast e2 tbool)) ->
  (normal_ret_assert (PROPx P (LOCALx ((`eq (eval_id tid) (`logical_or_result 
          `(typeof e1) (eval_expr e1) `(typeof e2) (eval_expr e2)))::Q) (SEPx (R))))) |-- PQR ->   
   @semax Espec Delta (PROPx P (LOCALx (Q) (SEPx (R))))
    (logical_or tid e1 e2) PQR.
Proof.
intros. 
eapply semax_pre_flipped.
eapply semax_post_flipped. 
eapply semax_logical_or; try eassumption.
intros.
specialize (H3 ek vl). 
apply andp_left2. apply H3.
intro rho. specialize (H2 rho). normalize. normalize in H2.
apply andp_right.
eapply derives_trans. apply H2.
normalize. simpl.
 apply orp_left;
normalize. normalize.
Qed.