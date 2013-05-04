Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.
Import Cop.
Local Open Scope logic.

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
    normalize; try solve [inv H]; apply andp_left2; auto.
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
intro rho; unfold normal_ret_assert, overridePost; simpl.
normalize. rewrite if_true by auto.
normalize.
eapply semax_pre_simple; [ | apply semax_break].
unfold overridePost. rewrite if_false by congruence.
unfold loop1_ret_assert.
eapply derives_trans; try apply Post.
rewrite andp_assoc. apply andp_derives; auto.
rewrite andp_comm; auto.
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
intro rho; unfold PROPx,LOCALx,local,lift1; unfold_lift; simpl; normalize.
repeat rewrite prop_true_andp by auto. auto.
eapply semax_pre_simple; [ | apply H2].
intro rho; unfold PROPx,LOCALx, lift1; unfold_lift; simpl; normalize.
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
normalize.
rewrite exp_andp2.
apply exp_left. intro x; eapply derives_trans; [ | apply (H1 x)].
intro rho; unfold PROPx,LOCALx,local,lift1; unfold_lift; simpl; normalize.
normalize.
apply extract_exists_pre; intro x.
eapply semax_pre_simple; [ | apply (H2 x)].
intro rho; unfold PROPx,LOCALx,local,lift1; unfold_lift; simpl; normalize.
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
normalize.
rewrite exp_andp2. apply exp_left. intro x1.
rewrite exp_andp2. apply exp_left. intro x2.
 eapply derives_trans; [ | apply (H1 x1 x2)].
intro rho; unfold PROPx,LOCALx,local,lift1; unfold_lift; simpl; normalize.
normalize. apply extract_exists_pre; intro x1.
normalize. apply extract_exists_pre; intro x2.
eapply semax_pre_simple; [ | apply (H2 x1 x2)].
intro rho; unfold PROPx,LOCALx,local,lift1; unfold_lift; simpl; normalize.
Qed.

Lemma closed_wrt_map_subst':
   forall {A: Type} id e (Q: list (environ -> A)),
         Forall (closed_wrt_vars (eq id)) Q ->
         @map (LiftEnviron A) _ (subst id e) Q = Q.
Proof.
apply @closed_wrt_map_subst.
Qed.

Hint Rewrite @closed_wrt_map_subst' using solve [auto with closed] : norm.
Hint Rewrite @closed_wrt_map_subst' using solve [auto with closed] : subst.


Lemma forward_ptr_compare_closed_now :
forall Espec Delta P Q R id e1 e2 cmp ty sh1 sh2
(TID : typecheck_tid_ptr_compare Delta id = true), 
Forall (closed_wrt_vars (eq id)) Q ->
Forall (closed_wrt_vars (eq id)) R ->
closed_wrt_vars (eq id) (`(cmp_ptr_no_mem (op_to_cmp cmp)) 
         (eval_expr e1) (eval_expr e2)) ->
PROPx P (LOCALx ((tc_environ Delta)::Q) (SEPx R)) |-- (local (tc_expr Delta e1) && local (tc_expr Delta e2) &&
      local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
      (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
      (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT)) ->
is_comparison cmp = true ->
@semax Espec Delta
  (PROPx P (LOCALx Q (SEPx R)))
    (Sset id (Ebinop cmp e1 e2 ty))
  ((normal_ret_assert
     (EX  old : val,
       PROPx P (LOCALx (`eq (eval_id id) 
                     (`(cmp_ptr_no_mem (op_to_cmp cmp))
                       (eval_expr e1) (eval_expr e2)) :: Q)
          (SEPx  R))))). 
Proof. 
intros. 
eapply semax_pre_post; [ | | eapply (semax_ptr_compare Delta (PROPx P (LOCALx Q (SEPx R))) _ _ _ _ _ sh1 sh2)].
  +eapply derives_trans; [ | apply now_later]. 
   intro rho. normalize. 
   apply andp_right; auto.
   specialize (H2 rho).   
   simpl in H2.
   normalize in H2. 
   normalize.
  
  +intros ex vl rho.
   unfold normal_ret_assert. simpl.
   super_unfold_lift. 
   repeat apply andp_right. 
   normalize. 
   normalize. 
   apply exp_right. apply Vundef. 
   normalize. 
   autorewrite with subst in *. normalize.

   +auto. 
   +auto.
Qed. 
(*Later
Lemma forward_ptr_compare_closed_now' :
forall Espec Delta P Q R id e1 e2 cmp ty sh1 sh2
(TID : typecheck_tid_ptr_compare Delta id = true), 
Forall (closed_wrt_vars (eq id)) Q ->
Forall (closed_wrt_vars (eq id))  
   (`(mapsto_ sh1 (typeof e1)) (eval_expr e1)::
    `(mapsto_ sh2 (typeof e2)) (eval_expr e2)::R) ->
closed_wrt_vars (eq id) (`(cmp_ptr_no_mem (op_to_cmp cmp)) 
         (eval_expr e1) (eval_expr e2)) ->
PROPx P (LOCALx ((tc_environ Delta)::Q) 
  (SEPx (R))) |-- 
      (local (tc_expr Delta e1) && local (tc_expr Delta e2) &&
      local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2))) ->
is_comparison cmp = true ->
@semax Espec Delta
  (PROPx P (LOCALx Q (
     (SEPx (`(mapsto_ sh1 (typeof e1)) (eval_expr e1)::
            `(mapsto_ sh2 (typeof e2)) (eval_expr e2)::
           R)) )))
    (Sset id (Ebinop cmp e1 e2 ty))
  ((normal_ret_assert
     (EX  old : val,
       PROPx P (LOCALx (`eq (eval_id id) 
                     (`(cmp_ptr_no_mem (op_to_cmp cmp))
                       (eval_expr e1) (eval_expr e2)) :: Q)
          (SEPx (`(mapsto_ sh1 (typeof e1)) (eval_expr e1)::
                 `(mapsto_ sh2 (typeof e2)) (eval_expr e2)::R)))))). 
Proof. intros.  
intros. 
eapply semax_pre_post; [ | | eapply (semax_ptr_compare Delta (PROPx P (LOCALx Q (SEPx R))) _ _ _ _ _ sh1 sh2)].
  +eapply derives_trans; [ | apply now_later]. 
   intro rho. normalize. 
   apply andp_right; auto.
   specialize (H2 rho).   
   simpl in H2.
   normalize in H2. 
   normalize.

eapply forward_ptr_compare_closed_now; auto with closed.
intro rho. normalize. 
apply andp_right. 
apply andp_right. specialize (H2 rho). simpl in H2.
normalize in H2. 

Qed.*)

Lemma forward_ptr_compare_closed_now_2 :
forall Espec Delta P Q R id e1 e2 cmp ty sh1 sh2
(TID : typecheck_tid_ptr_compare Delta id = true), 
Forall (closed_wrt_vars (eq id)) Q ->
Forall (closed_wrt_vars (eq id))  (`(mapsto_ sh1 (typeof e1)) (eval_expr e1)::R) ->
closed_wrt_vars (eq id) (`(cmp_ptr_no_mem (op_to_cmp cmp)) 
         (eval_expr e1) (eval_expr e2)) ->
PROPx P (LOCALx ((tc_environ Delta)::Q) 
  (SEPx (`(mapsto_ sh1 (typeof e1)) (eval_expr e1)::R))) |-- 
      (local (tc_expr Delta e1) && local (tc_expr Delta e2) &&
      local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
      (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
      (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT)) ->
is_comparison cmp = true ->
@semax Espec Delta
  (PROPx P (LOCALx Q (
     (SEPx (`(mapsto_ sh1 (typeof e1)) (eval_expr e1)::R)) )))
    (Sset id (Ebinop cmp e1 e2 ty))
  ((normal_ret_assert
     (EX  old : val,
       PROPx P (LOCALx (`eq (eval_id id) 
                     (`(cmp_ptr_no_mem (op_to_cmp cmp))
                       (eval_expr e1) (eval_expr e2)) :: Q)
          (SEPx (`(mapsto_ sh1 (typeof e1)) (eval_expr e1)::R)))))). 
Proof. intros.  
eapply forward_ptr_compare_closed_now; auto with closed.
intro rho. normalize. 
Qed.


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
 change SEPx with SEPx'.
 intro rho; unfold PROPx, LOCALx, SEPx'.
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
 change SEPx with SEPx'.
 intro rho; unfold PROPx, LOCALx, SEPx'.
 simpl.
 apply andp_derives; auto.
 apply andp_derives; auto.
 apply sepcon_derives; auto.
 apply later_derives; auto.
 unfold_lift; apply field_mapsto_field_mapsto_.
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
       (local (`eq (eval_id id) (subst id `old (`(cmp_ptr_no_mem 
                (op_to_cmp cmp)) (eval_expr e1) (eval_expr e2))))) &&
       (subst id (`old)) P))).
Proof. 
intros.
eapply semax_pre_post; [ | | apply (semax_ptr_compare Delta P _ _ _ _ _ sh1 sh2)].
eapply derives_trans; [ | apply now_later]. 
intro rho. normalize. 
apply andp_right; auto.  
eapply derives_trans. apply H. normalize. 
intros ek vl rho. unfold normal_ret_assert. simpl. 
normalize. 
apply exp_right with x. normalize. 
auto. auto. 
Qed. 

Lemma forward_ptr_compare' : 
forall {Espec: OracleKind},
forall (Delta: tycontext) P Q R id cmp e1 e2 ty sh1 sh2,
    is_comparison cmp = true  ->
    typecheck_tid_ptr_compare Delta id = true ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
         |-- local (tc_expr Delta e1) &&
             local (tc_expr Delta e2)  && 
          local (`(SeparationLogic.blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1 ) * TT) && 
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2 ) * TT) ->
   @semax Espec Delta 
         (PROPx P (LOCALx Q (SEPx R)))
          (Sset id (Ebinop cmp e1 e2 ty)) 
        (normal_ret_assert 
          (EX old:val, 
           PROPx P
           (LOCALx (`eq (eval_id id)  (subst id `old 
                     (`(cmp_ptr_no_mem (op_to_cmp cmp)) (eval_expr e1) (eval_expr e2))) ::
                       map (subst id `old) Q)
           (SEPx (map (subst id `old) R))))).
Proof.
intros.
eapply semax_pre_post; [ | | apply (semax_ptr_compare Delta (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))) _ _ _ _ _ sh1 sh2)].
eapply derives_trans; [ | apply now_later].
apply andp_right; normalize.
intros ek vl rho. unfold normal_ret_assert. simpl.
normalize. apply exp_right with x. normalize.
autorewrite with subst. normalize. 
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
  ((normal_ret_assert
     (EX  old : val,
       PROPx P 
        (LOCALx (`eq (eval_id id) 
                     (subst id `old (`(cmp_ptr_no_mem (op_to_cmp cmp))
                              (eval_expr e1) (eval_expr e2))) ::
                     map (subst id (`old)) Q)
          (SEPx (map (subst id (`old)) R)))))). 
Proof. 
 intros.
 eapply semax_post; [ | apply forward_ptr_compare'' with (sh1 := sh1) (sh2 := sh2); auto].
 intros.
 autorewrite with ret_assert subst.
 intro rho. simpl. normalize.
 apply exp_right with x.
 autorewrite with  subst. normalize.
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
eapply derives_trans ; [ | apply now_later].
intro rho; normalize.
apply andp_right; auto.
eapply derives_trans; [apply H | ].
normalize.
intros ek vl rho; unfold normal_ret_assert. simpl; normalize.
apply exp_right with x.
normalize.
Qed.


Lemma forward_setx:
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
 intro rho. simpl. normalize.
 apply exp_right with x.
 autorewrite with  subst. normalize.
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
Proof. intros; intros ek vl rho. 
    unfold normal_ret_assert; destruct ek; simpl; normalize.
   inv H0. inv H0. inv H0.
Qed.

Lemma after_set_special1:
  forall (A: Type) id e Delta Post  P Q R,
    EX x:A, PROPx (P x) (LOCALx (tc_environ(initialized id Delta) :: Q x) (SEPx (R x))) |-- Post ->
 forall ek vl,
   local (tc_environ (exit_tycon (Sset id e) Delta ek)) && 
    normal_ret_assert (EX  x : A, PROPx (P x) (LOCALx (Q x) (SEPx (R x)))) ek vl 
   |-- normal_ret_assert Post ek vl.
Proof.
 intros.
 intro rho; unfold local,lift1. simpl.
 apply derives_extract_prop. intro.
 unfold normal_ret_assert.
 simpl. apply derives_extract_prop. intro.
 simpl. subst. apply andp_right. apply prop_right; auto.
 apply andp_derives; auto.
 eapply derives_trans; [ | apply H]; clear H.
 simpl. apply exp_derives; intro x.
 unfold PROPx. simpl. apply andp_derives; auto.
 unfold LOCALx; simpl; apply andp_derives; auto.
 unfold local,lift1; unfold_lift.
 apply prop_derives.
 intro; split; auto.
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
Proof. intros; intro rho;  normalize.
 apply andp_left2.
  apply andp_right; auto. apply andp_right; apply prop_right; auto.
 rewrite H; auto.
Qed.

Lemma snd_split_map {A B}:
  forall l: list (A*B), map (@snd _ _) l = snd (split l).
Proof.
  induction l; simpl; auto. destruct a. rewrite IHl.
destruct (split l); f_equal; auto.
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
 unfold PROPx, LOCALx; intro rho; normalize.
 eapply semax_pre0; [ | eassumption].
 unfold PROPx, LOCALx; intro rho; normalize.
 eapply semax_pre0; [ | eassumption].
 unfold PROPx, LOCALx; intro rho; normalize.
Qed.
