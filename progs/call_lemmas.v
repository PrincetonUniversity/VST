Load loadpath.
Require Import progs.base.
Require Import progs.client_lemmas.
Require Import progs.field_mapsto.
Require Import progs.assert_lemmas.
Local Open Scope logic.

Lemma semax_call': forall Delta A (Pre Post: A -> environ->mpred) (x: A) ret argsig retsig a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retsig ->
   match retsig, ret with
   | Tvoid, None => True
   | Tvoid, Some _ => False
   | _, Some _ => True
   | _, _ => False
   end ->
  semax Delta
         (PROPx P (LOCALx (tc_expr Delta a :: tc_exprlist Delta (snd (split argsig)) bl :: Q)
            (SEPx (`(Pre x) ( (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) ::
                      `(func_ptr' (mk_funspec (argsig,retsig) A Pre Post)) (eval_expr a) :: R))))
          (Scall ret a bl)
          (normal_ret_assert 
            (EX old:val, 
              PROPx P (LOCALx (map (substopt ret (`old)) Q) 
                (SEPx (`(Post x) (get_result ret) :: map (substopt ret (`old)) R))))).
Proof.
 intros.
eapply semax_pre_post ; [ | | 
   apply (semax_call Delta A Pre Post x (PROPx P (LOCALx Q (SEPx R))) ret argsig retsig a bl H)].
 Focus 3.
 clear - H0.
 destruct retsig; destruct ret; simpl in *; try contradiction; split; intros; congruence.
unfold_lift; unfold local, lift1. intro rho; simpl. normalize.
unfold func_ptr'.
repeat rewrite corable_andp_sepcon1 by apply corable_func_ptr.
rewrite sepcon_comm. rewrite emp_sepcon.
repeat rewrite corable_andp_sepcon1 by apply corable_func_ptr.
apply derives_refl.
intros.
normalize.
intro old.
apply exp_right with old; destruct ret; normalize.
intro rho; normalize.
rewrite sepcon_comm; auto.
intro rho; normalize.
rewrite sepcon_comm; auto.
unfold substopt.
repeat rewrite list_map_identity.
normalize.
Qed.

Lemma semax_call1: forall Delta A (Pre Post: A -> environ->mpred) (x: A) id argsig retsig a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) retsig ->
   match retsig with
   | Tvoid => False
   | _ => True
   end ->
  semax Delta
         (PROPx P (LOCALx (tc_expr Delta a :: tc_exprlist Delta (snd (split argsig)) bl :: Q)
            (SEPx (`(Pre x) ( (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) ::
                      `(func_ptr' (mk_funspec (argsig,retsig) A Pre Post)) (eval_expr a) :: R))))
          (Scall (Some id) a bl)
          (normal_ret_assert 
            (EX old:val, 
              PROPx P (LOCALx (map (subst id (`old)) Q) 
                (SEPx (`(Post x) (get_result1 id) :: map (subst id (`old)) R))))).
Proof.
intros.
apply semax_call'; auto.
Qed.

Lemma semax_call0: forall Delta A (Pre Post: A -> environ->mpred) (x: A) argsig a bl P Q R,
   Cop.classify_fun (typeof a) = Cop.fun_case_f (type_of_params argsig) Tvoid ->
  semax Delta
         (PROPx P (LOCALx (tc_expr Delta a :: tc_exprlist Delta (snd (split argsig)) bl :: Q)
            (SEPx (`(Pre x) ( (make_args' (argsig,Tvoid) (eval_exprlist (snd (split argsig)) bl))) ::
                      `(func_ptr' (mk_funspec (argsig,Tvoid) A Pre Post)) (eval_expr a) :: R))))
          (Scall None a bl)
          (normal_ret_assert 
            (PROPx P (LOCALx Q (SEPx (`(Post x) (make_args nil nil) :: R))))).
Proof.
intros.
eapply semax_pre_post ; [ | | 
   apply (semax_call Delta A Pre Post x (PROPx P (LOCALx Q (SEPx R))) None argsig Tvoid a bl H)].
 Focus 3.
 split; intros; congruence.
 intro rho; normalize.
unfold func_ptr'.
repeat rewrite corable_andp_sepcon1 by apply corable_func_ptr.
rewrite emp_sepcon, sepcon_comm. 
repeat rewrite corable_andp_sepcon1 by apply corable_func_ptr.
apply derives_refl.
intros.
normalize.
intro rho; normalize.
rewrite sepcon_comm; auto.
Qed.

Lemma semax_fun_id':
      forall id f
              Delta P Q R PostCond c
            (GLBL: (var_types Delta) ! id = None),
            (glob_types Delta) ! id = Some (Global_func f) ->
       semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(func_ptr' f) (eval_var id (globtype (Global_func f))) :: R))))
                              c PostCond ->
       semax Delta (PROPx P (LOCALx Q (SEPx R))) c PostCond.
Proof.
intros. 
apply (semax_fun_id id f Delta); auto.
eapply semax_pre0; [ | apply H0].
change SEPx with SEPx'; unfold PROPx,LOCALx,SEPx',local, lift1; unfold_lift; simpl;
intro rho; normalize.
rewrite andp_comm.
unfold func_ptr'.
rewrite corable_andp_sepcon1 by apply corable_func_ptr.
rewrite emp_sepcon; auto.
Qed.

Lemma eqb_typelist_refl: forall tl, eqb_typelist tl tl = true.
Proof.
induction tl; simpl; auto.
apply andb_true_iff.
split; auto.
apply eqb_type_refl.
Qed.


Lemma semax_call_id0:
 forall Delta P Q R id bl argsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
   (glob_types Delta) ! id = Some (Global_func (mk_funspec (argsig, Tvoid) A Pre Post)) ->
  semax Delta (PROPx P (LOCALx (tc_exprlist Delta (snd (split argsig)) bl :: Q)
                 (SEPx (`(Pre x) (make_args' (argsig,Tvoid) (eval_exprlist (snd (split argsig)) bl)) :: R))))
    (Scall None (Evar id (Tfunction (type_of_params argsig) Tvoid)) bl)
    (normal_ret_assert 
       (PROPx P (LOCALx Q (SEPx (`(Post x) (make_args nil nil) :: R))))).
Proof.
intros.
assert (Cop.classify_fun (typeof (Evar id (Tfunction (type_of_params argsig) Tvoid)))=
               Cop.fun_case_f (type_of_params argsig) Tvoid).
simpl. subst. reflexivity.
apply semax_fun_id' with id (mk_funspec (argsig,Tvoid) A Pre Post); auto.
subst. 

eapply semax_pre; [ | apply (semax_call0 Delta A Pre Post x argsig _ bl P Q R H0)].
apply andp_left2.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; simpl.
subst.
autorewrite with norm.
apply andp_right.
apply prop_right. hnf.
simpl.
unfold get_var_type. rewrite GLBL. rewrite H.
simpl.
rewrite eqb_typelist_refl.
simpl. hnf; auto.
auto.
change SEPx with SEPx'.
simpl.
intro rho.
rewrite sepcon_comm.
rewrite sepcon_assoc.
autorewrite with norm.
apply sepcon_derives; auto.
rewrite sepcon_comm.
apply sepcon_derives; auto.
Qed.

Lemma semax_call_id1:
 forall Delta P Q R ret id retty bl argsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
   (glob_types Delta) ! id = Some (Global_func (mk_funspec (argsig,retty) A Pre Post)) ->
   match retty with
   | Tvoid => False
   | _ => True
   end ->
  semax Delta (PROPx P (LOCALx (tc_exprlist Delta (snd (split argsig)) bl :: Q) 
                 (SEPx (`(Pre x) (make_args' (argsig,Tvoid) (eval_exprlist (snd (split argsig)) bl)) :: R))))
    (Scall (Some ret)
             (Evar id (Tfunction (type_of_params argsig) retty))
             bl)
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (`old)) Q) 
             (SEPx (`(Post x) (get_result1 ret) :: map (subst ret (`old)) R))))).
Proof.
intros.
assert (Cop.classify_fun (typeof (Evar id (Tfunction (type_of_params argsig) retty)))=
               Cop.fun_case_f (type_of_params argsig) retty).
subst; reflexivity.
apply semax_fun_id' with id (mk_funspec (argsig,retty)  A Pre Post); auto.
subst. 
eapply semax_pre; [ | apply (semax_call1 Delta A Pre Post x ret argsig retty _ bl P Q R H1 H0)].
apply andp_left2.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; simpl.
subst.
autorewrite with norm.
apply andp_right.
apply prop_right. hnf.
simpl.
unfold get_var_type. rewrite GLBL. rewrite H.
simpl.
rewrite eqb_typelist_refl.
rewrite eqb_type_refl.
simpl. split; hnf; auto.
auto.
change SEPx with SEPx'.
simpl.
intro rho.
rewrite sepcon_comm.
rewrite sepcon_assoc.
autorewrite with norm.
apply sepcon_derives; auto.
rewrite sepcon_comm.
apply sepcon_derives; auto.
Qed.


Lemma semax_call_id1':
 forall Delta P Q R ret id retty bl argsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
   (glob_types Delta) ! id = Some (Global_func (mk_funspec (argsig,retty) A Pre Post)) ->
   match retty with
   | Tvoid => False
   | _ => True
   end ->
  forall 
   (CLOSQ: Forall (closed_wrt_vars (eq ret)) Q)
   (CLOSR: Forall (closed_wrt_vars (eq ret)) R),
  semax Delta (PROPx P (LOCALx (tc_exprlist Delta (snd (split argsig)) bl :: Q)
            (SEPx (`(Pre x) (make_args' (argsig,retty) (eval_exprlist (snd (split argsig)) bl)) :: R))))
    (Scall (Some ret)
             (Evar id (Tfunction (type_of_params argsig) retty))
             bl)
    (normal_ret_assert 
       (PROPx P (LOCALx Q   (SEPx (`(Post x) (get_result1 ret) ::  R))))).
Proof.
intros.
eapply semax_post;
  [ | apply (semax_call_id1 Delta P Q R ret id retty bl argsig A x Pre Post 
     GLBL H H0)].
intros ek vl.
apply andp_left2.
unfold normal_ret_assert.
apply andp_derives; auto.
apply andp_derives; auto.
apply exp_left; intro v.
apply andp_derives; auto.
apply andp_derives.
unfold local, lift1 ;intro rho.
clear - CLOSQ.
apply prop_left. intro.
apply prop_right.
induction Q; simpl; auto.
inv CLOSQ.
destruct H.
split.
rewrite closed_wrt_subst in H; auto.
auto.
clear - CLOSR.
change SEPx with SEPx'.
unfold SEPx'. intro rho.
simpl.
apply sepcon_derives; auto.
induction R; simpl; auto.
inv CLOSR.
apply sepcon_derives.
rewrite closed_wrt_subst; auto.
apply IHR; auto.
Qed.

Lemma semax_call_id1_Eaddrof:
 forall Delta P Q R ret id retty bl argsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
   (glob_types Delta) ! id = Some (Global_func (mk_funspec (argsig,retty) A Pre Post)) ->
   match retty with
   | Tvoid => False
   | _ => True
   end ->
  semax Delta (PROPx P (LOCALx (tc_exprlist Delta (snd (split argsig)) bl :: Q) 
               (SEPx (`(Pre x) (make_args' (argsig,retty) (eval_exprlist (snd (split argsig)) bl)) :: R))))
    (Scall (Some ret)
             (Eaddrof (Evar id (Tfunction (type_of_params argsig) retty)) (Tpointer (Tfunction (type_of_params argsig) retty) noattr))
             bl)
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (`old)) Q) 
             (SEPx (`(Post x) (get_result1 ret) :: map (subst ret (`old)) R))))).
Proof.
intros.
assert (Cop.classify_fun (typeof (Eaddrof (Evar id (Tfunction (type_of_params argsig) retty)) (Tpointer (Tfunction (type_of_params argsig) retty) noattr)))=
               Cop.fun_case_f (type_of_params argsig) retty).
subst; reflexivity.
apply semax_fun_id' with id (mk_funspec (argsig,retty) A Pre Post); auto.
subst. 
eapply semax_pre; [ | apply (semax_call1 Delta A Pre Post x ret argsig retty _ bl P Q R H1 H0)].
apply andp_left2.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; simpl.
subst.
autorewrite with norm.
apply andp_right.
apply prop_right. hnf.
simpl.
unfold get_var_type. rewrite GLBL. rewrite H.
simpl.
rewrite eqb_typelist_refl.
rewrite eqb_type_refl.
simpl. apply I.
auto.
change SEPx with SEPx'.
simpl.
intro rho.
cancel.
Qed.


Lemma semax_call_id_aux1: forall P Q1 Q R S,
     PROPx P (LOCALx (Q1::Q) R) |-- S -> local Q1 && PROPx P (LOCALx Q R) |-- S.
Proof. intros. eapply derives_trans; try apply H.
  intro rho; normalize.
 unfold PROPx. simpl.
 apply andp_derives; auto.
 unfold LOCALx. simpl.
 unfold local,lift2,lift1.
 apply derives_extract_prop; intro.
 apply andp_right; auto.
 apply prop_right; split; auto.
Qed.
