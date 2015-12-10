Require Import floyd.base.
Require Import floyd.expr_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.closed_lemmas.
Require Import floyd.compare_lemmas.
Require Import floyd.semax_tactics.
Require Import floyd.forward_lemmas.
Require Import floyd.entailer.

Local Open Scope logic.

Definition op_Z_int (op: Z->Z->Prop) (x: Z) (y: val) :=
 match y with Vint y' => op x (Int.signed y') | _ => False end.

Definition op_Z_uint (op: Z->Z->Prop) (x: Z) (y: val) :=
 match y with Vint y' => op x (Int.unsigned y') | _ => False end.

Lemma semax_for_simple : 
 forall Inv Espec {cs: compspecs} Delta Pre
           (P:  Z -> list Prop) Q1 (Q: Z -> list localdef) (R: Z -> list mpred)
           _i init hi body Post
     (INV: Inv = EX i:Z, local Q1 && PROPx (P i)  (LOCALx (Q i) (SEPx (R i))))
     (TI: (temp_types (update_tycon Delta init)) ! _i = Some (tint, true))
     (Thi: typeof hi = tint)
     (CLOQ: forall i, Forall (closed_wrt_vars (eq _i)) (Q1 :: map locald_denote (Q i))),
     @semax cs Espec Delta Pre init
      (normal_ret_assert 
        (EX i:Z, local Q1 && PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i)
              (LOCALx (temp _i (Vint (Int.repr i)) :: Q i) (SEPx (R i))))) ->
     (forall i, ENTAIL (update_tycon Delta init), PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i) 
       (LOCALx (temp _i (Vint (Int.repr i))  :: Q i)
       (SEPx (R i))) |-- 
            (tc_expr (update_tycon Delta init) (Ebinop Olt (Etempvar _i tint) hi tint))) ->
     (EX i:Z, local (`(op_Z_int Z.ge i) (eval_expr hi)) && local Q1 && local (tc_environ (update_tycon Delta init)) &&
                 PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i) (LOCALx (temp _i (Vint (Int.repr i)) 
                                  :: (Q i)) (SEPx (R i)))
            |-- Post EK_normal None)    ->
     (forall i,
     @semax cs Espec (update_tycon Delta init)
        (local (`(op_Z_int Z.lt i) (eval_expr hi)) && local Q1 &&
         PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i))  :: (Q i))
         (SEPx (R i))))
        body
        (normal_ret_assert (local Q1 && PROPx ((Int.min_signed <= i+1 <= Int.max_signed) :: P (i+1))  (LOCALx (temp _i (Vint (Int.repr i))  :: Q (i+1)) (SEPx (R (i+1))))))) ->
     @semax cs Espec Delta Pre 
       (Sfor init
                (Ebinop Olt (Etempvar _i tint) hi tint)
                body 
                (Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))) Post.
Proof.
intros.
unfold Sfor.
eapply semax_seq'; [ eassumption | ].
simpl.
clear Pre H.
assert (H0': forall i : Z,
     ENTAIL (update_tycon Delta init), 
     PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i)
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i) (SEPx (R i)))
     |-- tc_expr (update_tycon Delta init)
           ((Eunop Cop.Onotbool (Ebinop Olt (Etempvar _i tint) hi tint) tint))). {
 intros; eapply derives_trans; [apply H0 | ].
 clear.
 intro rho; unfold tc_expr; simpl;
 rewrite ?denote_tc_assert_andp;
 repeat apply andp_derives; auto.
}
clear H0. rename H0' into H0.
apply (@semax_loop Espec cs _ _
            (EX i:Z, local Q1 && PROPx ((Int.min_signed <= i+1 <= Int.max_signed) :: P (i+1)) 
                (LOCALx (temp _i (Vint (Int.repr i))  :: Q (i+1))
                (SEPx (R (i+1))))));
 [apply semax_pre_simple with ( (tc_expr (update_tycon Delta init) (Eunop Cop.Onotbool (Ebinop Olt (Etempvar _i tint) hi tint) tint))
                                      && 
                          (EX i:Z, local Q1 && PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i)  (LOCALx (temp _i (Vint (Int.repr i))  :: Q i) (SEPx (R i)))))
 | ].
*
replace (fun a : environ =>
 EX  x : Z, local Q1 a &&
 PROPx ((Int.min_signed <= x <= Int.max_signed) :: P x)
   (LOCALx (temp _i (Vint (Int.repr x)) :: Q x) (SEPx (R x))) a)
   with (EX  x : Z, local Q1 && PROPx ((Int.min_signed <= x <= Int.max_signed) :: P x)
   (LOCALx (temp _i (Vint (Int.repr x)) :: Q x) (SEPx (R x))))
 by (extensionality; reflexivity).
apply andp_right; [ | apply andp_left2; auto].
repeat rewrite exp_andp2. apply exp_left; intro i.
eapply derives_trans; [ | apply (H0 i)].
go_lowerx; normalize. apply andp_right; auto. apply prop_right; repeat (split; auto).
destruct H4; auto.
destruct H4; auto.
*
rewrite exp_andp2.
apply extract_exists_pre. intro i.
apply semax_seq with (local (`(typed_true (typeof (Ebinop Olt (Etempvar _i tint) hi tint)))
                             (eval_expr (Ebinop Olt (Etempvar _i tint) hi tint))) && local Q1 &&
           PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i)
          (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i))
             (SEPx (R i)))).
eapply semax_ifthenelse; auto.
rewrite andp_comm.
simpl typeof.
eapply semax_post; [ | apply semax_skip].
intros.
apply andp_left2.
unfold normal_ret_assert; normalize.
 autorewrite with norm1 norm2; normalize.
unfold overridePost. rewrite if_true by auto. normalize.
apply andp_right. apply andp_right. apply andp_left1; auto.
apply andp_left2; apply andp_left1; auto.
apply andp_left2; apply andp_left2; auto.
rewrite andp_comm.
eapply semax_pre_post; [ | intros; apply andp_left2; auto |  apply semax_break].
unfold overridePost. rewrite if_false by discriminate.
unfold loop1_ret_assert.
simpl typeof.
eapply derives_trans; [ | eassumption].
apply exp_right with i; auto.
simpl eval_expr.
go_lowerx.
repeat apply andp_right; try apply prop_right; auto.
unfold_lift in H3.
rewrite <- H7 in H3. rewrite Thi in H3. simpl in H3.
destruct (eval_expr hi rho); simpl in H3; try solve [inv H3].
hnf in H3. red.
unfold Int.lt in H3.
if_tac in H3; inv H3.
rewrite Int.signed_repr in H9; auto.
simpl update_tycon.
apply semax_extensionality_Delta with (update_tycon Delta init).
apply tycontext_eqv_sub.
apply tycontext_eqv_symm.
apply join_tycon_same.
simpl typeof.
eapply semax_post_flipped.
eapply semax_pre0; [ | apply (H2 i)].
go_lowerx. repeat apply andp_right; try apply prop_right; auto.
rewrite Thi in H. unfold_lift in H. rewrite <- H6 in H.
destruct (eval_expr hi rho); simpl in H; try solve [inv H].
hnf in H. red.
unfold Int.lt in H.
if_tac in H; inv H.
rewrite Int.signed_repr in H8; auto.
intros.
apply andp_left2.
unfold normal_ret_assert, loop1_ret_assert; normalize.
intro rho; unfold subst; simpl.
apply exp_right with i.
normalize.
*
replace (fun a : environ =>
 EX  x : Z,
 PROPx (P x)
   (LOCALx (temp _i (Vint (Int.repr x)) :: Q x) (SEPx (R x))) a)
   with (EX  x : Z, PROPx (P x)
   (LOCALx (temp _i (Vint (Int.repr x)) :: Q x) (SEPx (R x))))
 by (extensionality; reflexivity).
apply sequential.
eapply semax_pre_simple; [ | apply semax_set].
eapply derives_trans; [ | apply now_later].
simpl typeof.
unfold loop2_ret_assert.
apply andp_right.
apply andp_left1.
intro rho.
unfold local, lift1.
simpl.
normalize.
apply andp_right.
unfold tc_expr;
unfold typecheck_expr; fold typecheck_expr.
repeat rewrite denote_tc_assert_andp.
repeat apply andp_right; try apply @TT_right.
rewrite TI. apply @TT_right.
unfold tc_temp_id, typecheck_temp_id.
rewrite TI.
rewrite denote_tc_assert_andp;
repeat apply andp_right; apply @TT_right.
unfold loop2_ret_assert.
intro rho.
rewrite exp_andp2.
simpl.
unfold subst.
apply exp_left; intro i.
apply exp_right with (i+1).
simpl.
repeat rewrite <- insert_local.
simpl.
specialize (CLOQ (i+1)).
inv CLOQ.
rename H4 into CLOQ1; rename H5 into CLOQ.
apply andp_right.
apply andp_left2; apply andp_left1.
 autorewrite with norm1 norm2; normalize.
apply andp_left2. apply andp_left2.
apply andp_right.
apply andp_left1.
unfold locald_denote; simpl.
 autorewrite with norm1 norm2; normalize.
rewrite <- H. simpl.  normalize.
normalize;
 autorewrite with norm1 norm2; normalize.
apply andp_right; auto.
apply prop_right.
split; auto.
Qed.

Lemma semax_for_simple_u : 
 forall Inv Espec {cs: compspecs} Delta Pre
           (P:  Z -> list Prop) Q1 (Q: Z -> list localdef) (R: Z -> list mpred)
           _i init hi body Post s1 s2 s3
     (INV: Inv = EX i:Z, local Q1 && PROPx (P i)  (LOCALx (Q i) (SEPx (R i))))
     (TI: (temp_types (update_tycon Delta init)) ! _i = Some (tuint, true))
     (Thi: typeof hi = Tint I32 s1 noattr)
     (CLOQ: forall i, Forall (closed_wrt_vars (eq _i)) (Q1 :: map locald_denote (Q i))),
     @semax cs Espec Delta Pre init
      (normal_ret_assert 
        (EX i:Z, local Q1 && PROPx ((0 <=i <= Int.max_unsigned) :: P i)
              (LOCALx (temp _i (Vint (Int.repr i)) :: Q i) (SEPx (R i))))) ->
     (forall i, ENTAIL (update_tycon Delta init),
       PROPx ((0 <= i <= Int.max_unsigned) :: P i) 
       (LOCALx (temp _i (Vint (Int.repr i))  :: Q i)
       (SEPx (R i))) |-- 
           (tc_expr (update_tycon Delta init) (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)))) ->
     (EX i:Z, local (`(op_Z_uint Z.ge i) (eval_expr hi)) && local Q1 && local (tc_environ (update_tycon Delta init)) &&
                PROPx ((0 <= i <= Int.max_unsigned) :: P i) (LOCALx (temp _i (Vint (Int.repr i)) 
                                  :: (Q i)) (SEPx (R i)))
            |-- Post EK_normal None)    ->
     (forall i,
     @semax cs Espec (update_tycon Delta init)
        (local (`(op_Z_uint Z.lt i) (eval_expr hi)) && local Q1 &&
         PROPx ((0 <= i <= Int.max_unsigned) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i))  :: (Q i))
         (SEPx (R i))))
        body
        (normal_ret_assert (local Q1 && PROPx ((0 <= i+1 <= Int.max_unsigned) :: P (i+1))  (LOCALx (temp _i (Vint (Int.repr i))  :: Q (i+1)) (SEPx (R (i+1))))))) ->
     @semax cs Espec Delta Pre 
       (Sfor init
                (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr))
                body 
                (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) (Tint I32 s2 noattr)) tuint))) Post.
Proof.
intros.
unfold Sfor.
eapply semax_seq'; [ eassumption | ].
simpl.
clear Pre H.
assert (H0': forall i : Z,
     ENTAIL (update_tycon Delta init), 
     PROPx ((0 <= i <= Int.max_unsigned) :: P i)
       (LOCALx
          (temp _i (Vint (Int.repr i)) :: Q i) (SEPx (R i)))
     |-- tc_expr (update_tycon Delta init)
           ((Eunop Cop.Onotbool (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)) tint))). {
 intros; eapply derives_trans; [apply H0 | ].
 clear.
 intro rho; unfold tc_expr; simpl;
 rewrite ?denote_tc_assert_andp;
 repeat apply andp_derives; auto.
}
clear H0. rename H0' into H0.
apply (@semax_loop Espec cs _ _
            (EX i:Z, local Q1 && PROPx ((0 <= i+1 <= Int.max_unsigned) :: P (i+1)) 
                (LOCALx (temp _i (Vint (Int.repr i))  :: Q (i+1))
                (SEPx (R (i+1))))));
 [apply semax_pre_simple with ( (tc_expr (update_tycon Delta init) (Eunop Cop.Onotbool (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)) tint))
                                      &&
                          (EX i:Z,   local Q1 && PROPx ((0 <= i <= Int.max_unsigned) :: P i)  (LOCALx (temp _i (Vint (Int.repr i))  :: Q i) (SEPx (R i)))))
 | ].
*
replace (fun a : environ =>
 EX  x : Z, local Q1 a && 
 PROPx ((0 <= x <= Int.max_unsigned) :: P x)
   (LOCALx (temp _i (Vint (Int.repr x)) :: Q x) (SEPx (R x))) a)
   with (EX  x : Z, local Q1 && PROPx ((0 <= x <= Int.max_unsigned) :: P x)
   (LOCALx (temp _i (Vint (Int.repr x)) :: Q x) (SEPx (R x))))
 by (extensionality; reflexivity).
apply andp_right; [ | apply andp_left2; auto].
repeat rewrite exp_andp2. apply exp_left; intro i. 
eapply derives_trans; [ | apply (H0 i)].
go_lowerx; normalize. apply andp_right; auto. apply prop_right; repeat (split; auto).
destruct H4; auto.
destruct H4; auto.
*
rewrite exp_andp2.
apply extract_exists_pre. intro i.
apply semax_seq with (local (`(typed_true (typeof (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr))))
                             (eval_expr (Ebinop Olt (Etempvar _i tuint) hi tuint))) && local Q1 &&
          PROPx ((0 <= i <= Int.max_unsigned) :: P i)
          (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i))
             (SEPx (R i)))).
eapply semax_ifthenelse; auto.
rewrite andp_comm.
simpl typeof.
eapply semax_post; [ | apply semax_skip].
intros.
apply andp_left2.
unfold normal_ret_assert; normalize.
unfold overridePost. rewrite if_true by auto.
normalize. autorewrite with norm1 norm2; normalize.
apply andp_right. apply andp_right. apply andp_left1; auto.
apply andp_left2; apply andp_left1; auto.
apply andp_left2; apply andp_left2; auto.
rewrite andp_comm.
eapply semax_pre_post; [ | intros; apply andp_left2; auto | apply semax_break].
unfold overridePost. rewrite if_false by discriminate.
unfold loop1_ret_assert.
simpl typeof.
eapply derives_trans; [ | eassumption].
apply exp_right with i; auto.
simpl eval_expr.
go_lowerx.
repeat apply andp_right; try apply prop_right; auto.
rename H5 into H5'; rename H3 into H5.
unfold_lift in H5.
rewrite <- H7 in H5. rewrite Thi in H5. simpl in H5.
destruct (eval_expr hi rho); simpl in H5; try solve [inv H5].
hnf in H5. red.
unfold Int.ltu in H5.
if_tac in H5; inv H5.
rewrite Int.unsigned_repr in H3; auto.
simpl update_tycon.
apply semax_extensionality_Delta with (update_tycon Delta init).
apply tycontext_eqv_sub.
apply tycontext_eqv_symm.
apply join_tycon_same.
simpl typeof.
eapply semax_post_flipped.
eapply semax_pre0; [ | apply (H2 i)].
go_lowerx. repeat apply andp_right; try apply prop_right; auto.
rename H4 into H4'; rename H into H4.
rewrite Thi in H4. unfold_lift in H4. rewrite <- H6 in H4.
destruct (eval_expr hi rho); simpl in H4; try solve [inv H4].
hnf in H4. red.
unfold Int.ltu in H4.
if_tac in H4; inv H4.
rewrite Int.unsigned_repr in H; auto.
intros.
apply andp_left2.
unfold normal_ret_assert, loop1_ret_assert; normalize.
intro rho; unfold subst; simpl.
apply exp_right with i.
normalize.
*
replace (fun a : environ =>
 EX  x : Z,
 PROPx (P x)
   (LOCALx (temp _i (Vint (Int.repr x)) :: Q x) (SEPx (R x))) a)
   with (EX  x : Z, PROPx (P x)
   (LOCALx (temp _i (Vint (Int.repr x)) :: Q x) (SEPx (R x))))
 by (extensionality; reflexivity).
apply sequential.
eapply semax_pre_simple; [ | apply semax_set].
eapply derives_trans; [ | apply now_later].
simpl typeof.
unfold loop2_ret_assert.
apply andp_right.
apply andp_left1.
intro rho.
unfold local, lift1.
simpl.
normalize.
apply andp_right.
unfold tc_expr;
unfold typecheck_expr; fold typecheck_expr.
repeat rewrite denote_tc_assert_andp.
repeat apply andp_right; try apply @TT_right.
rewrite TI. apply @TT_right.
unfold tc_temp_id, typecheck_temp_id.
rewrite TI.
rewrite denote_tc_assert_andp;
repeat apply andp_right; apply @TT_right.
unfold loop2_ret_assert.
intro rho.
rewrite exp_andp2.
simpl.
unfold subst.
apply exp_left; intro i.
apply exp_right with (i+1).
simpl.
repeat rewrite <- insert_local.
simpl.
specialize (CLOQ (i+1)).
inv CLOQ.
rename H4 into CLOQ1; rename H5 into CLOQ.
apply andp_right.
apply andp_left2; apply andp_left1.
 autorewrite with norm1 norm2; normalize.
apply andp_left2. apply andp_left2.
apply andp_right.
apply andp_left1.
unfold locald_denote; simpl.
 autorewrite with norm1 norm2; normalize.
rewrite <- H. simpl.  normalize.
normalize;
 autorewrite with norm1 norm2; normalize.
apply andp_right; auto.
apply prop_right.
split; auto.
Qed.

Lemma op_Z_int_Vint_repr:
  forall op i n, 
   Int.min_signed <= n <= Int.max_signed ->
    op_Z_int op i (Vint (Int.repr n)) = op i n.
Proof.
 intros.
 unfold op_Z_int. rewrite Int.signed_repr by auto.
 auto.
Qed.
Hint Rewrite op_Z_int_Vint_repr using repable_signed : norm.

Lemma op_Z_uint_Vint_repr:
  forall op i n, 
   0 <= n <= Int.max_unsigned ->
    op_Z_uint op i (Vint (Int.repr n)) = op i n.
Proof.
 intros.
 unfold op_Z_uint. rewrite Int.unsigned_repr by auto.
 auto.
Qed.
Hint Rewrite op_Z_uint_Vint_repr using repable_signed : norm.

Lemma semax_for_simple_bound : 
 forall n Inv Espec {cs: compspecs} Delta Pre
           (P:  Z -> list Prop) (Q: Z -> list localdef) (R: Z -> list mpred)
           _i init hi body Post 
     (INV: Inv = EX i:Z, PROPx (P i)  (LOCALx (Q i) (SEPx (R i))))
     (RANGE: Int.min_signed <= n <= Int.max_signed)
     (TI: (temp_types (update_tycon Delta init)) ! _i = Some (tint, true))
     (Thi: typeof hi = tint)
     (CLOhi: closed_wrt_vars (eq _i) (eval_expr hi))
     (CLOQ: forall i, Forall (closed_wrt_vars (eq _i)) (map locald_denote (Q i))),
     @semax cs Espec Delta Pre init
      (normal_ret_assert 
        (EX i:Z, local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
         PROPx ((Int.min_signed <= i <= n) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i)) :: Q i)
         (SEPx (R i))))) ->
     (forall i, ENTAIL (update_tycon Delta init),
       PROPx ((Int.min_signed <= i <= n) :: P i) 
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i)
       (SEPx (R i))) |-- 
            (tc_expr (update_tycon Delta init) (Ebinop Olt (Etempvar _i tint) hi tint))) ->
       ENTAIL (update_tycon Delta init), PROPx (P n)
                  (LOCALx (temp _i (Vint (Int.repr n))
                                  :: (Q n)) (SEPx (R n)))
            |-- Post EK_normal None    ->
     (forall i,
     @semax cs Espec (update_tycon Delta init)
        (PROPx ((Int.min_signed <= i < n) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i))
         (SEPx (R i))))
        body
        (normal_ret_assert (local (`(eq (Vint (Int.repr n))) (eval_expr hi) ) &&
                             PROPx ((Int.min_signed <= i+1 <= n) :: P (i+1)) 
                             (LOCALx (temp _i (Vint (Int.repr i)) :: Q (i+1))
                             (SEPx (R (i+1))))))) ->
     @semax cs Espec Delta Pre 
       (Sfor init
                (Ebinop Olt (Etempvar _i tint) hi tint)
                body 
                (Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))) Post.
Proof.
intros.
subst Inv.
eapply (semax_for_simple (EX i:Z, local (`(eq (Vint (Int.repr n))) (eval_expr hi)) && PROPx ((i<=n) :: P i)  (LOCALx (Q i) (SEPx (R i)))));
 try reflexivity; auto.
intros. simpl. auto with closed.
eapply semax_post_flipped; [ apply H | ].
intros. apply andp_left2. apply normal_ret_assert_derives'.
go_lowerx.
apply exp_derives; intro i.
normalize. apply andp_right; auto.
apply prop_right; repeat split; auto; try omega.
intro i. eapply derives_trans; [ | solve [eauto]].
instantiate (1:=i).
go_lowerx. normalize. apply andp_right; auto.
apply prop_right.
split; [omega | ].
split. split; auto. split; auto.
apply exp_left; intro i.
eapply derives_trans; [ | solve [eauto]].
go_lowerx; normalize.
rewrite <- H4 in H3.
normalize in H3.
assert (i=n) by omega.
subst i.
apply andp_right; auto.
apply prop_right.
split; auto.
intro.
eapply semax_pre_post; [ | | solve [eauto]].
instantiate (1:=i).
apply andp_left2. go_lowerx; normalize.
apply andp_right; auto.
apply prop_right.
split; auto. omega. split; auto. split; auto.
rewrite <- H4 in H3; normalize in H3.
intros.
apply andp_left2.
apply normal_ret_assert_derives'.
go_lowerx; normalize.
apply andp_right; auto.
apply prop_right.
split; auto. omega. split; auto. split; auto.
omega. split; auto. omega.
Qed.


Lemma semax_for_simple_bound_u : 
 forall n Inv Espec {cs: compspecs} Delta Pre
           (P:  Z -> list Prop) (Q: Z -> list localdef) (R: Z -> list mpred)
           _i init hi body Post s1 s2 s3
     (INV: Inv = EX i:Z, PROPx (P i)  (LOCALx (Q i) (SEPx (R i))))
     (RANGE: 0 <= n <= Int.max_unsigned)
     (TI: (temp_types (update_tycon Delta init)) ! _i = Some (tuint, true))
     (Thi: typeof hi = Tint I32 s1 noattr)
     (CLOhi: closed_wrt_vars (eq _i) (eval_expr hi))
     (CLOQ: forall i, Forall (closed_wrt_vars (eq _i)) (map locald_denote (Q i))),
     @semax cs Espec Delta Pre init
      (normal_ret_assert 
        (EX i:Z, local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
          PROPx ((0 <= i <= n) :: P i)
          (LOCALx (temp _i (Vint (Int.repr i)) :: Q i)
           (SEPx (R i))))) ->
     (forall i, 
       ENTAIL (update_tycon Delta init), 
       PROPx ((0 <= i <= n) :: P i) 
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i)
       (SEPx (R i))) |-- 
            (tc_expr (update_tycon Delta init) (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)))) ->
     (ENTAIL (update_tycon Delta init), 
            PROPx (P n)
                  (LOCALx (temp _i (Vint (Int.repr n))
                                  :: (Q n)) (SEPx (R n)))
            |-- Post EK_normal None)    ->
     (forall i,
     @semax cs Espec (update_tycon Delta init)
        (PROPx ((0 <= i < n) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i))
         (SEPx (R i))))
        body
        (normal_ret_assert (local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
                             PROPx ((0 <= i+1 <= n) :: P (i+1)) 
                             (LOCALx (temp _i (Vint (Int.repr i)) :: Q (i+1))
                             (SEPx (R (i+1))))))) ->
     @semax cs Espec Delta Pre 
       (Sfor init
                (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr))
                body 
                (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) (Tint I32 s2 noattr)) tuint))) Post.
Proof.
intros.
subst Inv.
eapply (semax_for_simple_u (EX i:Z, local (`(eq (Vint (Int.repr n))) (eval_expr hi)) && PROPx ((i<=n) :: P i)  (LOCALx (Q i) (SEPx (R i)))));
 try reflexivity; eauto.
intros. simpl. auto with closed.
eapply semax_post_flipped; [ apply H | ].
intros. apply andp_left2. apply normal_ret_assert_derives'.
apply exp_derives; intro i.
go_lowerx. normalize. apply andp_right; auto.
apply prop_right; repeat split; auto; try omega.
intro i. eapply derives_trans; [ | solve [eauto]].
instantiate (1:=i).
go_lowerx. normalize. apply andp_right; auto.
apply prop_right.
split; [omega | ].
split. split; auto. split; auto.
apply exp_left; intro i.
eapply derives_trans; [ | solve [eauto]].
go_lowerx; normalize.
rewrite <- H4 in H3.
normalize in H3.
assert (i=n) by omega.
subst i.
apply andp_right; auto.
apply prop_right.
split; auto.
intro.
eapply semax_pre_post; [ | | solve [eauto]].
instantiate (1:=i).
apply andp_left2. go_lowerx; normalize.
apply andp_right; auto.
apply prop_right.
split; auto. omega. split; auto. split; auto.
rewrite <- H4 in H3; normalize in H3.
intros.
apply andp_left2.
apply normal_ret_assert_derives'.
go_lowerx; normalize.
apply andp_right; auto.
apply prop_right.
split; auto. omega. split; auto. split; auto.
omega. split; auto. omega.
Qed.

Lemma semax_for_simple_bound_const_init : 
 forall n Inv Espec {cs: compspecs} Delta (Pre: environ -> mpred)
           (P:  Z -> list Prop) (Q: Z -> list localdef) (R: Z -> list mpred)
           _i lo hi body Post
     (INV: Inv = EX i:Z, PROPx (P i)  (LOCALx (Q i) (SEPx (R i))))
     (RANGElo: Int.min_signed <= lo <= n)
     (RANGE: n <= Int.max_signed)
     (TI: typeof_temp Delta _i = Some tint)
     (Thi: typeof hi = tint)
     (CLOhi: closed_wrt_vars (eq _i) (eval_expr hi))
     (CLOQ: forall i, Forall (closed_wrt_vars (eq _i)) (map locald_denote (Q i))),
     local (tc_environ Delta) && Pre |-- local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
        (PROPx (P lo)
         (LOCALx (Q lo)
         (SEPx (R lo)))) ->
     (forall i, ENTAIL (initialized _i Delta),
       PROPx ((lo <= i <= n) :: P i) 
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i)
       (SEPx (R i))) |-- 
            (tc_expr (initialized _i Delta) (Ebinop Olt (Etempvar _i tint) hi tint))) ->
     (ENTAIL (initialized _i Delta),
         PROPx (P n)
                  (LOCALx (temp _i (Vint (Int.repr n)) :: (Q n)) (SEPx (R n)))
            |-- Post EK_normal None)    ->
     (forall i,
     @semax cs Espec (initialized _i Delta)
        (PROPx ((lo <= i < n) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i))
         (SEPx (R i))))
        body
        (normal_ret_assert (local (`(eq (Vint (Int.repr n))) (eval_expr hi)) && 
                             PROPx ((lo <= i+1 <= n) :: P (i+1)) 
                             (LOCALx (temp _i (Vint (Int.repr i)) :: Q (i+1))
                             (SEPx (R (i+1))))))) ->
     @semax cs Espec Delta Pre 
       (Sfor (Sset _i (Econst_int (Int.repr lo) tint))
                (Ebinop Olt (Etempvar _i tint) hi tint)
                body 
                (Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))) Post.
Proof.
intros.
eapply (semax_for_simple_bound n (EX i:Z, PROPx ((lo<=i) :: P i)  (LOCALx (Q i) (SEPx (R i)))));
 try reflexivity; eauto.
*
omega.
*
 simpl. clear - TI.
unfold typeof_temp in TI.
destruct ((temp_types Delta) ! _i) eqn:?; inv TI. destruct p. inv H0.
eapply temp_types_init_same; eauto.
*
eapply semax_pre_simple
  with (!!fold_right and True (P lo) && local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
         (PROPx nil
          (LOCALx (Q lo) (SEPx (R lo))))).
eapply derives_trans; [apply H | ].
go_lowerx; normalize.
rewrite andp_assoc. 
apply semax_extract_prop; intro.
eapply semax_post_flipped'.
eapply forward_setx'.
go_lowerx.
apply andp_right. apply @TT_right.
unfold tc_temp_id. unfold typecheck_temp_id. 
unfold typeof_temp in TI.
destruct ((temp_types Delta) ! _i); inv TI. destruct p. inv H8.
rewrite denote_tc_assert_andp.
apply andp_right. rewrite denote_tc_assert_bool.
apply prop_right. auto. apply @TT_right.
simpl exit_tycon.
Intros old.
autorewrite with subst.
Exists lo.
go_lowerx. normalize. apply andp_right; auto.
apply prop_right.
split; [omega  |].
split.
split. omega. split; auto. omega.
unfold_lift; split; auto.
*
intro.
eapply derives_trans; [ | solve [eauto]].
instantiate (1:=i).
go_lowerx; normalize.
 progress (autorewrite with norm1 norm2); normalize.
apply andp_right; auto.
apply prop_right. split; [omega | ].
split; auto.
*
eapply derives_trans; [ | solve [eauto]].
go_lowerx; normalize.
*
intro.
simpl.
eapply semax_pre_post; [ | | apply H2].
instantiate (1:=i).
go_lowerx; normalize; 
 progress (autorewrite with norm1 norm2); normalize;
apply andp_right; [apply prop_right | auto].
split; auto. omega.
intros.
apply andp_left2.
apply normal_ret_assert_derives'.
go_lowerx; normalize; apply andp_right; [apply prop_right | auto].
split; [omega | ].
split; auto.
split; [omega | ].
split; [omega | ].
auto.
Qed.

Lemma semax_for_simple_bound_const_init_u : 
 forall n Inv Espec {cs: compspecs} Delta (Pre: environ -> mpred)
           (P:  Z -> list Prop) (Q: Z -> list localdef) (R: Z -> list mpred)
           _i lo hi body Post s0 s1 s2 s3
     (INV: Inv = EX i:Z, PROPx (P i)  (LOCALx (Q i) (SEPx (R i))))
     (RANGElo: 0 <= lo <= n)
     (RANGE: n <= Int.max_unsigned)
     (TI: typeof_temp Delta _i = Some tuint)
     (Thi: typeof hi = Tint I32 s1 noattr)
     (CLOhi: closed_wrt_vars (eq _i) (eval_expr hi))
     (CLOQ: forall i, Forall (closed_wrt_vars (eq _i)) (map locald_denote (Q i))),
     local (tc_environ Delta) && Pre |-- local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
        (PROPx (P lo)
         (LOCALx (Q lo)
         (SEPx (R lo)))) ->
     (forall i, ENTAIL (initialized _i Delta),
        PROPx ((lo <= i <= n) :: P i) 
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i)
       (SEPx (R i))) |-- 
            (tc_expr (initialized _i Delta) (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)))) ->
     (ENTAIL (initialized _i Delta), PROPx (P n)
                  (LOCALx (temp _i (Vint (Int.repr n))
                                  :: (Q n)) (SEPx (R n)))
            |-- Post EK_normal None)    ->
     (forall i,
     @semax cs Espec (initialized _i Delta)
        (PROPx ((lo <= i < n) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i))
         (SEPx (R i))))
        body
        (normal_ret_assert (local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
                             PROPx ((lo <= i+1 <= n) :: P (i+1)) 
                             (LOCALx (temp _i (Vint (Int.repr i)) :: Q (i+1))
                             (SEPx (R (i+1))))))) ->
     @semax cs Espec Delta Pre 
       (Sfor (Sset _i (Econst_int (Int.repr lo) (Tint I32 s0 noattr)))
                (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr))
                body 
                (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) (Tint I32 s2 noattr)) tuint))) Post.
Proof.
intros.
eapply (semax_for_simple_bound_u n (EX i:Z, PROPx ((lo<=i) :: P i)  (LOCALx (Q i) (SEPx (R i)))));
 try reflexivity; eauto.
*
omega.
*
 simpl. clear - TI.
unfold typeof_temp in TI.
destruct ((temp_types Delta) ! _i) eqn:?; inv TI. destruct p. inv H0.
eapply temp_types_init_same; eauto.
*
eapply semax_pre_simple
  with (!!fold_right and True (P lo) && local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
         (PROPx nil
          (LOCALx
             (Q lo)
             (SEPx (R lo))))).
eapply derives_trans; [apply H | ].
go_lowerx; normalize.
rewrite andp_assoc.
apply semax_extract_prop; intro.
eapply semax_post_flipped'.
eapply forward_setx'.
go_lowerx.
apply andp_right; try apply @TT_right.
unfold tc_temp_id. unfold typecheck_temp_id. 
unfold typeof_temp in TI.
destruct ((temp_types Delta) ! _i); inv TI. destruct p. inv H8.
rewrite denote_tc_assert_andp, denote_tc_assert_bool.
apply andp_right. apply prop_right; auto.
destruct s0; apply @TT_right.
Intro old.
autorewrite with subst.
Exists lo.
go_lowerx. normalize. apply andp_right; auto.
apply prop_right.
split; [omega  |].
split.
split. omega. split; auto. omega.
unfold_lift; split; auto.
*
intro.
eapply derives_trans; [ | solve [eauto]].
instantiate (1:=i).
go_lowerx; normalize.
 progress (autorewrite with norm1 norm2); normalize.
apply andp_right; auto.
apply prop_right. split; [omega | ].
split; auto.
*
eapply derives_trans; [ | solve [eauto]].
go_lowerx; normalize.
*
intro.
simpl.
eapply semax_pre_post; [ | | apply H2].
instantiate (1:=i).
go_lowerx; normalize; 
 progress (autorewrite with norm1 norm2); normalize;
apply andp_right; [apply prop_right | auto].
split; auto. omega.
intros.
apply andp_left2.
apply normal_ret_assert_derives'.
go_lowerx; normalize; apply andp_right; [apply prop_right | auto].
split; [omega | ].
split; auto.
split; [omega | ].
split; [omega | ].
auto.
Qed.

Lemma semax_for_const_bound_const_init : 
 forall n Inv Espec {cs: compspecs} Delta (Pre: environ -> mpred)
           (P:  Z -> list Prop) (Q: Z -> list localdef) (R: Z -> list mpred)
           _i lo hi body Post
     (INV: Inv = EX i:Z, PROPx (P i)  (LOCALx (Q i) (SEPx (R i))))
     (RANGElo: Int.min_signed <= lo <= n)
     (RANGE: n <= Int.max_signed)
     (TI: typeof_temp Delta _i = Some tint)
     (Thi: hi=n)
     (CLOQ: forall i, Forall (closed_wrt_vars (eq _i)) (map locald_denote (Q i))),
     local (tc_environ Delta) && Pre |-- 
        (PROPx (P lo) (LOCALx (Q lo) (SEPx (R lo)))) ->
     (forall i, ENTAIL (initialized _i Delta), 
           PROPx ((lo <= i <= n) :: P i) 
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i)
       (SEPx (R i))) |-- 
            (tc_expr (initialized _i Delta) (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr hi) tint) tint))) ->
     (ENTAIL (initialized _i Delta), 
           PROPx (P n)
                  (LOCALx (temp _i (Vint (Int.repr n)) :: (Q n)) (SEPx (R n)))
            |-- Post EK_normal None)    ->
     (forall i,
     @semax cs Espec (initialized _i Delta)
        (PROPx ((lo <= i < n) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i))
         (SEPx (R i))))
        body
        (normal_ret_assert (PROPx ((lo <= i+1 <= n) :: P (i+1)) 
                             (LOCALx (temp _i (Vint (Int.repr i)) ::  Q (i+1))
                             (SEPx (R (i+1))))))) ->
     @semax cs Espec Delta Pre 
       (Sfor (Sset _i (Econst_int (Int.repr lo) tint))
                (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr hi) tint) tint)
                body 
                (Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))) Post.
Proof.
intros.
subst n.
eapply semax_for_simple_bound_const_init;
 eauto.
*
 auto with closed.
* 
 eapply derives_trans ; [apply H | ].
 go_lowerx. repeat apply andp_right; try apply prop_right; auto.
* 
(* intros.
 drop_LOCAL 2%nat. apply H0.
*
 eapply derives_trans; [ | apply H1].
 go_lowerx. apply andp_right; auto.
 apply prop_right; auto. 
*
*)
 intros.
(* drop_LOCAL 1%nat.*)
 eapply semax_post_flipped'; [ apply H2 | ].
 go_lowerx. repeat rewrite prop_true_andp. auto.
 unfold_lift; simpl. repeat split; auto.
 split; auto. reflexivity.
Qed.

Lemma semax_for_const_bound_const_init_u : 
 forall n Inv Espec {cs: compspecs} Delta (Pre: environ -> mpred)
           (P:  Z -> list Prop) (Q: Z -> list localdef) (R: Z -> list mpred)
           _i lo hi body Post s1 s2
     (INV: Inv = EX i:Z, PROPx (P i)  (LOCALx (Q i) (SEPx (R i))))
     (RANGElo: 0 <= lo <= n)
     (RANGE: n <= Int.max_unsigned)
     (TI: typeof_temp Delta _i = Some tuint)
     (Thi: hi=n)
     (CLOQ: forall i, Forall (closed_wrt_vars (eq _i)) (map locald_denote (Q i))),
     local (tc_environ Delta) && Pre |-- 
        (PROPx (P lo) (LOCALx (Q lo) (SEPx (R lo)))) ->
     (forall i, ENTAIL (initialized _i Delta), 
           PROPx ((lo <= i <= n) :: P i) 
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i)
       (SEPx (R i))) |-- 
            (tc_expr (initialized _i Delta) (Ebinop Olt (Etempvar _i tuint) (Econst_int (Int.repr hi) (Tint I32 s1 noattr)) tint))) ->
     (ENTAIL (initialized _i Delta), 
           PROPx (P n)
                  (LOCALx (temp _i (Vint (Int.repr n)) :: (Q n)) (SEPx (R n)))
            |-- Post EK_normal None)    ->
     (forall i,
     @semax cs Espec (initialized _i Delta)
        (PROPx ((lo <= i < n) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i))
         (SEPx (R i))))
        body
        (normal_ret_assert (PROPx ((lo <= i+1 <= n) :: P (i+1)) 
                             (LOCALx (temp _i (Vint (Int.repr i)) ::  Q (i+1))
                             (SEPx (R (i+1))))))) ->
     @semax cs Espec Delta Pre 
       (Sfor (Sset _i (Econst_int (Int.repr lo) tint))
                (Ebinop Olt (Etempvar _i tuint) (Econst_int (Int.repr hi) (Tint I32 s1 noattr)) tint)
                body 
                (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) (Tint I32 s2 noattr)) tuint))) Post.
Proof.
intros.
subst n.
eapply semax_for_simple_bound_const_init_u;
 eauto.
* 
 reflexivity.
*
 auto with closed.
* 
 eapply derives_trans ; [apply H | ].
 go_lowerx. repeat apply andp_right; try apply prop_right; auto.
*
(* 
 intros.
 drop_LOCAL 2%nat. apply H0.
*
 eapply derives_trans; [ | apply H1].
 go_lowerx. apply andp_right; auto.
 apply prop_right; auto. 
*
*)
 intros.
 eapply semax_post_flipped'; [ apply H2 | ].
 go_lowerx. repeat rewrite prop_true_andp. auto.
 unfold_lift; simpl. repeat split; auto.
 split; auto. auto.
Qed.


Lemma upd_compose:
  forall {A}{B}{C} {EA: EqDec A}(f: B ->C) (g: A -> B) (x: A) (y: B) x', 
           upd (Basics.compose f g) x (f y) x' = f (upd g x y x').
Proof.
 intros; unfold upd, Basics.compose.  if_tac; auto.
Qed.
Hint Rewrite @upd_compose : norm.

Lemma semax_for_resolve_postcondition:
 forall Delta P Q R,
   ENTAIL Delta,       PROPx P (LOCALx Q (SEPx R)) |--
    normal_ret_assert (PROPx P (LOCALx Q (SEPx R))) EK_normal None.
Proof.
intros.
 apply andp_left2.
 rewrite normal_ret_assert_elim.
 auto.
Qed.

Ltac forward_for_simple_bound' n Pre :=
 first 
 [ first [eapply (semax_for_const_bound_const_init n Pre)
         | eapply (semax_for_const_bound_const_init_u n Pre)];
  [reflexivity | try repable_signed | try repable_signed | reflexivity | try reflexivity; omega
(*  | auto 50 with closed*)
  | intro; unfold map at 1; auto 50 with closed
  | cbv beta; simpl update_tycon
  | intro; cbv beta; simpl update_tycon; try solve [entailer!]
  | try apply semax_for_resolve_postcondition
  | intro; cbv beta; simpl update_tycon; abbreviate_semax;
   try (apply semax_extract_PROP; intro) ]
 | first [eapply (semax_for_simple_bound_const_init n Pre)
         | eapply (semax_for_simple_bound_const_init_u n Pre)];
  [reflexivity | try repable_signed | try repable_signed | reflexivity | reflexivity
  | auto 50 with closed
  | intro; unfold map at 1; auto 50 with closed
  | cbv beta; simpl update_tycon
  | intro; cbv beta; simpl update_tycon; try solve [entailer!]
  | try apply semax_for_resolve_postcondition
  | intro; cbv beta; simpl update_tycon; abbreviate_semax;
   try (apply semax_extract_PROP; intro) ]
 |first [eapply (semax_for_simple_bound n Pre)
         |eapply (semax_for_simple_bound_u n Pre)];
  [reflexivity | try repable_signed | reflexivity | reflexivity
  | auto 50 with closed
  | intro; unfold map at 1; auto 50 with closed
  | cbv beta; simpl update_tycon
  | intro; cbv beta; simpl update_tycon; try solve [entailer!]
  | try apply semax_for_resolve_postcondition
  | intro; cbv beta; simpl update_tycon; abbreviate_semax;
     try (apply semax_extract_PROP; intro) ]
  ].
