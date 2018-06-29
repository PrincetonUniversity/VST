Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.compare_lemmas.
Require Import VST.floyd.semax_tactics.
Require Import VST.floyd.forward_lemmas.
Require Import VST.floyd.entailer.
Import Cop.
Local Open Scope logic.

Definition op_Z_int (op: Z->Z->Prop) (x: Z) (y: val) :=
 match y with Vint y' => op x (Int.signed y') | _ => False end.

Definition op_Z_uint (op: Z->Z->Prop) (x: Z) (y: val) :=
 match y with Vint y' => op x (Int.unsigned y') | _ => False end.

Lemma semax_for_simple :
 forall (Inv: environ->mpred) Espec {cs: compspecs} Delta
           (Pre: environ->mpred)
           (A: Type) (P:  Z -> A -> list Prop) (Q1: environ->Prop) (Q: Z -> A -> list localdef) (R: Z -> A -> list mpred)
           _i (init: statement) (hi: expr) (body: statement) (Post: ret_assert)
     (INV: Inv = EX i:Z, EX x:A, local Q1 && PROPx (P i x)  (LOCALx (Q i x) (SEPx (R i x))))
     (TI: (temp_types Delta) ! _i = Some tint)
     (Thi: typeof hi = tint)
     (CLOQ: forall i x, Forall (closed_wrt_vars (eq _i)) (Q1 :: map locald_denote (Q i x))),
     @semax cs Espec Delta Pre init
      (normal_ret_assert
        (EX i:Z, EX x:A, local Q1 && PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i x)
              (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x) (SEPx (R i x))))) ->
     (forall i (x:A), ENTAIL Delta, PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i x)
       (LOCALx (temp _i (Vint (Int.repr i))  :: Q i x)
       (SEPx (R i x))) |--
            (tc_expr Delta (Ebinop Olt (Etempvar _i tint) hi tint))) ->
     (EX i:Z, local (`(op_Z_int Z.ge i) (eval_expr hi)) && local Q1 && local (tc_environ Delta) &&
                 (EX x:A, PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i x) (LOCALx (temp _i (Vint (Int.repr i))
                                  :: (Q i x)) (SEPx (R i x))))
            |-- RA_normal Post)    ->
     (forall i (x:A),
     @semax cs Espec Delta
        (local (`(op_Z_int Z.lt i) (eval_expr hi)) && local Q1 &&
         PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i x)
         (LOCALx (temp _i (Vint (Int.repr i))  :: (Q i x))
         (SEPx (R i x))))
        body
        (normal_ret_assert (EX x:A, local Q1 && PROPx ((Int.min_signed < i+1 <= Int.max_signed) :: P (i+1) x)
                                                                  (LOCALx (temp _i (Vint (Int.repr i))  :: Q (i+1) x)
                                                                  (SEPx (R (i+1) x)))))) ->
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
assert (H0': forall (i : Z) (x:A),
     ENTAIL Delta,
       PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i x)
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x) (SEPx (R i x)))
     |-- tc_expr Delta
           ((Eunop Cop.Onotbool (Ebinop Olt (Etempvar _i tint) hi tint) tint))). {
 intros; eapply derives_trans; [apply H0 | ].
 clear.
 intro rho; unfold tc_expr; simpl;
 rewrite ?denote_tc_assert_andp;
 repeat apply andp_derives; auto.
}
clear H0. rename H0' into H0.
apply (@semax_loop Espec cs _ _
            (EX i:Z, EX x:A, local Q1 && PROPx ((Int.min_signed <(*=*) i+1 <= Int.max_signed) :: P (i+1) x)
                (LOCALx (temp _i (Vint (Int.repr i))  :: Q (i+1) x)
                (SEPx (R (i+1) x)))));
 [apply semax_pre_simple with ( (tc_expr Delta (Eunop Cop.Onotbool (Ebinop Olt (Etempvar _i tint) hi tint) tint))
                                      &&
                          (EX i:Z, EX x:A, local Q1 && PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i x)
                                                       (LOCALx (temp _i (Vint (Int.repr i))  :: Q i x) (SEPx (R i x)))))
 | ].
*
replace (fun a : environ =>
 EX  i:Z, EX x:A, local Q1 a &&
 PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i x)
   (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x) (SEPx (R i x))) a)
   with (EX  i:Z, EX x:A, local Q1 && PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i x)
   (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x) (SEPx (R i x))))
 by (extensionality; reflexivity).
apply andp_right; [ | apply andp_left2; auto].
repeat rewrite exp_andp2. apply exp_left; intro i.
repeat rewrite exp_andp2. apply exp_left; intro x.
eapply derives_trans; [ | apply (H0 i x)].
go_lowerx; normalize.
*
rewrite exp_andp2.
apply extract_exists_pre. intro i.
rewrite exp_andp2.
apply extract_exists_pre. intro x.
apply semax_seq with (local (`(typed_true (typeof (Ebinop Olt (Etempvar _i tint) hi tint)))
                             (eval_expr (Ebinop Olt (Etempvar _i tint) hi tint))) && local Q1 &&
           PROPx ((Int.min_signed <= i <= Int.max_signed) :: P i x)
          (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i x))
             (SEPx (R i x))));
  [eapply semax_ifthenelse; auto | ].
+
rewrite andp_comm.
simpl typeof.
eapply semax_post; try apply semax_skip.
all: intros; destruct Post; simpl_ret_assert;
 try (apply andp_left2; apply FF_left).
apply andp_left2.
normalize; autorewrite with norm1 norm2; normalize.
apply andp_right. apply andp_right. apply andp_left1; auto.
apply andp_left2; apply andp_left1; auto.
apply andp_left2; apply andp_left2; auto.
+
rewrite andp_comm.
eapply semax_pre; try apply semax_break; autorewrite with ret_assert.
simpl typeof.
eapply derives_trans; [ | eassumption].
apply exp_right with i; auto.
simpl eval_expr.
go_lowerx.
repeat apply andp_right; try apply prop_right; auto.
 -
  unfold_lift in H3.
  destruct H7 as [H7 H7'].
  unfold_lift in H7.
  rewrite <- H7 in H3. rewrite Thi in H3.
  clear - H3 H5. red. hnf in H3.
 simpl in H3. 
 destruct (eval_expr hi rho); simpl in H3; try solve [inv H3].
 unfold strict_bool_val, both_int, Cop2.sem_cast, Cop2.classify_cast in H3.
 destruct Archi.ptr64 eqn:Hp; simpl in H3.
  unfold Int.lt in H3. if_tac in H3; inv H3.
  rewrite Int.signed_repr in H; auto.
  unfold Int.lt in H3. if_tac in H3; inv H3.
  rewrite Int.signed_repr in H; auto.
 -
    apply exp_right with x; auto.
    repeat apply andp_right; try apply prop_right; auto.
+
apply semax_extensionality_Delta with Delta.
apply tycontext_sub_refl.
simpl typeof.
eapply semax_post_flipped.
eapply semax_pre0; [ | apply (H2 i)].
go_lowerx. repeat apply andp_right; try apply prop_right; auto; try apply derives_refl.
rewrite Thi in H. unfold_lift in H.
destruct H6 as [H6 H6'].
  unfold_lift in H6.
   rewrite <- H6 in H.
destruct (eval_expr hi rho); simpl in H; try solve [inv H].
 unfold strict_bool_val, both_int, Cop2.sem_cast, Cop2.classify_cast in H.
destruct Archi.ptr64 eqn:Hp; simpl in H.
  unfold Int.lt in H. if_tac in H; inv H.
  rewrite Int.signed_repr in H8; auto.
  unfold Int.lt in H. if_tac in H; inv H.
  rewrite Int.signed_repr in H8; auto.
auto.
auto.
all: autorewrite with ret_assert; simpl_ret_assert;
 intros; apply andp_left2; try apply FF_left.
normalize.
intro rho; unfold subst; simpl.
apply exp_right with i.
apply exp_right with x0.
normalize.
*
replace (fun a : environ =>
 EX  i : Z, EX x:A,
 PROPx (P i x)
   (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x) (SEPx (R i x))) a)
   with (EX  i:Z, EX x:A, PROPx (P i x)
   (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x) (SEPx (R i x))))
 by (extensionality; reflexivity).
apply sequential.
eapply semax_pre_simple; [ | apply semax_set].
eapply derives_trans; [ | apply now_later].
simpl typeof.
unfold loop2_ret_assert.
apply andp_right.
+
rewrite exp_andp2. apply exp_left; intro i.
rewrite exp_andp2. apply exp_left; intro x.

apply derives_trans with
  (prop (Int.min_signed < i+1 <= Int.max_signed) &&
   (local (tc_environ Delta) &&
    local (locald_denote (temp _i (Vint (Int.repr i)))))). {
 clear; apply andp_right.
 apply andp_left2; apply andp_left2.
 apply andp_left1. intro rho.
 simpl. apply prop_derives. intros [? ?]; auto.
 apply andp_right.
 apply andp_left1; auto.
 apply andp_left2. apply andp_left2.
 apply andp_left2. apply andp_left1.
 intro rho. unfold local, lift1.
 apply prop_derives; simpl; unfold_lift.  intuition. 
 }
apply derives_extract_prop; intro RANGE.
intro rho.
unfold local, lift1.
simpl.
normalize. hnf in H3.
apply andp_right.
{
unfold tc_expr;
unfold typecheck_expr; fold typecheck_expr.
repeat rewrite denote_tc_assert_andp.
repeat apply andp_right; try apply @TT_right.
unfold isBinOpResultType. simpl classify_add; cbv iota.
repeat rewrite denote_tc_assert_andp; simpl.
repeat apply andp_right; try apply @TT_right.
{
simpl. unfold_lift.
destruct H3 as [H3 H3'].
  unfold_lift in H3.
   rewrite <- H3.
clear - RANGE; unfold denote_tc_nosignedover.
apply prop_right.
rewrite !Int.signed_repr by rep_omega.
omega.
}
{
rewrite TI. simpl.
unfold_lift in H3; destruct H3.
unfold eval_id in H3.
destruct (Map.get (te_of rho) _i); inv H3.
apply prop_right; eauto.
}
}
{
unfold tc_temp_id, typecheck_temp_id.
rewrite TI.
rewrite denote_tc_assert_andp; simpl;
repeat apply andp_right; apply @TT_right.
}
+
destruct Post; simpl_ret_assert.
intro rho.
rewrite exp_andp2.
simpl.
unfold subst.
apply exp_left; intro i.
apply exp_right with (i+1).
rewrite exp_andp2.
apply exp_left; intro x.
apply exp_right with x.
simpl.
repeat rewrite <- insert_local.
simpl.
specialize (CLOQ (i+1) x).
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
rewrite <- H. simpl. 
unfold force_val, both_int, Cop2.sem_cast; simpl.
 destruct Archi.ptr64 eqn:Hp; simpl; normalize.
 - split; auto. clear. congruence.
 - split; auto. clear. congruence.
 - 
 autorewrite with norm1 norm2; normalize.

normalize;
 autorewrite with norm1 norm2; normalize.
 apply andp_right; auto.
apply prop_right.
split; auto.
clear - H4 H5; omega.
Qed.

Lemma semax_for_simple_u :
 forall (Inv: environ->mpred) Espec {cs: compspecs} Delta
           (Pre: environ->mpred)
           (A: Type) (P:  Z -> A -> list Prop) (Q1: environ->Prop) (Q: Z -> A -> list localdef) (R: Z -> A -> list mpred)
           _i (init: statement) (hi: expr) (body: statement) (Post: ret_assert)
            s1 s2 s3
     (INV: Inv = EX i:Z, EX x:A, local Q1 && PROPx (P i x)  (LOCALx (Q i x) (SEPx (R i x))))
     (TI: (temp_types Delta) ! _i = Some tuint)
     (Thi: typeof hi = Tint I32 s1 noattr)
     (CLOQ: forall i x, Forall (closed_wrt_vars (eq _i)) (Q1 :: map locald_denote (Q i x))),
     @semax cs Espec Delta Pre init
      (normal_ret_assert
        (EX i:Z, EX x:A, local Q1 && PROPx ((0 <=i <= Int.max_unsigned) :: P i x)
              (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x) (SEPx (R i x))))) ->
     (forall i x, ENTAIL Delta,
       PROPx ((0 <= i <= Int.max_unsigned) :: P i x)
       (LOCALx (temp _i (Vint (Int.repr i))  :: Q i x)
       (SEPx (R i x))) |--
           (tc_expr Delta (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)))) ->
     (EX i:Z, local (`(op_Z_uint Z.ge i) (eval_expr hi)) && local Q1 && local (tc_environ Delta) &&
                (EX x:A, PROPx ((0 <= i <= Int.max_unsigned) :: P i x) (LOCALx (temp _i (Vint (Int.repr i))
                                  :: (Q i x)) (SEPx (R i x))))
            |-- RA_normal Post)    ->
     (forall i x,
     @semax cs Espec Delta
        (local (`(op_Z_uint Z.lt i) (eval_expr hi)) && local Q1 &&
         PROPx ((0 <= i <= Int.max_unsigned) :: P i x)
         (LOCALx (temp _i (Vint (Int.repr i))  :: (Q i x))
         (SEPx (R i x))))
        body
        (normal_ret_assert (EX x:A, local Q1 && PROPx ((0 <= i+1 <= Int.max_unsigned) :: P (i+1) x)
                                         (LOCALx (temp _i (Vint (Int.repr i))  :: Q (i+1) x) (SEPx (R (i+1) x)))))) ->
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
assert (H0': forall (i : Z) (x:A),
     ENTAIL Delta,
     PROPx ((0 <= i <= Int.max_unsigned) :: P i x)
       (LOCALx
          (temp _i (Vint (Int.repr i)) :: Q i x) (SEPx (R i x)))
     |-- tc_expr Delta
           ((Eunop Cop.Onotbool (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)) tint))). {
 intros; eapply derives_trans; [apply H0 | ].
 clear.
 intro rho; unfold tc_expr; simpl;
 rewrite ?denote_tc_assert_andp;
 repeat apply andp_derives; auto.
}
clear H0. rename H0' into H0.
apply (@semax_loop Espec cs _ _
            (EX i:Z, EX x:A, local Q1 && PROPx ((0 <= i+1 <= Int.max_unsigned) :: P (i+1) x)
                (LOCALx (temp _i (Vint (Int.repr i))  :: Q (i+1) x)
                (SEPx (R (i+1) x)))));
 [apply semax_pre_simple with ( (tc_expr Delta (Eunop Cop.Onotbool (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)) tint))
                                      &&
                          (EX i:Z, EX x:A,  local Q1 && PROPx ((0 <= i <= Int.max_unsigned) :: P i x)
                             (LOCALx (temp _i (Vint (Int.repr i))  :: Q i x) (SEPx (R i x)))))
 | ].
*
replace (fun a : environ =>
 EX  i : Z, EX x:A, local Q1 a &&
 PROPx ((0 <= i <= Int.max_unsigned) :: P i x)
   (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x) (SEPx (R i x))) a)
   with (EX  i:Z, EX x:A,  local Q1 && PROPx ((0 <= i <= Int.max_unsigned) :: P i x)
   (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x) (SEPx (R i x))))
 by (extensionality; reflexivity).
apply andp_right; [ | apply andp_left2; auto].
repeat rewrite exp_andp2. apply exp_left; intro i.
repeat rewrite exp_andp2. apply exp_left; intro x.
eapply derives_trans; [ | apply (H0 i x)].
go_lowerx; normalize. 
*
rewrite exp_andp2.
apply extract_exists_pre. intro i.
rewrite exp_andp2.
apply extract_exists_pre. intro x.
apply semax_seq with (local (`(typed_true (typeof (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr))))
                             (eval_expr (Ebinop Olt (Etempvar _i tuint) hi tuint))) && local Q1 &&
          PROPx ((0 <= i <= Int.max_unsigned) :: P i x)
          (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i x))
             (SEPx (R i x))));
 [ eapply semax_ifthenelse; auto | ].
+
rewrite andp_comm.
simpl typeof.
apply sequential'.
eapply semax_post'; [ | apply semax_skip].
apply andp_left2.
apply andp_right. apply andp_right. apply andp_left1; auto.
apply derives_refl.
apply andp_left2; apply andp_left1; auto.
apply andp_left2; apply andp_left2; auto.
+
rewrite andp_comm.
eapply semax_pre; [ | apply semax_break].
autorewrite with ret_assert.
simpl typeof.
eapply derives_trans; [ | eassumption].
apply exp_right with i; auto.
simpl eval_expr.
go_lowerx.
repeat apply andp_right; try apply prop_right; auto.
 -
 rename H5 into H5'; rename H3 into H5.
 unfold_lift in H5.
 unfold_lift in H7; destruct H7 as [H7 H7'].
 rewrite <- H7 in H5. rewrite Thi in H5. simpl in H5.
 destruct (eval_expr hi rho); simpl in H5; try solve [inv H5].
 hnf in H5. red.
 unfold strict_bool_val, both_int, Cop2.sem_cast, Cop2.classify_cast in H5.
 destruct Archi.ptr64 eqn:Hp; simpl in H5.
  unfold Int.ltu in H5; if_tac in H5; inv H5;
  rewrite Int.unsigned_repr in H3; auto.
  unfold Int.ltu in H5; if_tac in H5; inv H5;
  rewrite Int.unsigned_repr in H3; auto.
 -
  apply exp_right with x; auto.
  repeat apply andp_right; try apply prop_right; auto.
+
apply semax_extensionality_Delta with Delta.
apply tycontext_sub_refl.
simpl typeof.
apply sequential.
autorewrite with ret_assert.
eapply semax_post'; try (eapply semax_pre0; [ | apply (H2 i x)]).
Intros x0. Exists i x0. apply andp_left2; auto.
go_lowerx. repeat apply andp_right; try apply prop_right; auto.
rename H4 into H4'; rename H into H4.
rewrite Thi in H4. unfold_lift in H4.
 unfold_lift in H6; destruct H6 as [H6 H6'].
  rewrite <- H6 in H4.
destruct (eval_expr hi rho); simpl in H4; try solve [inv H4].
hnf in H4. red.
 unfold strict_bool_val, both_int, Cop2.sem_cast, Cop2.classify_cast in H4.
 destruct Archi.ptr64 eqn:Hp; simpl in H4.
  unfold Int.ltu in H4; if_tac in H4; inv H4;
  rewrite Int.unsigned_repr in H; auto.
  unfold Int.ltu in H4; if_tac in H4; inv H4;
  rewrite Int.unsigned_repr in H; auto.
*
replace (fun a : environ =>
 EX  i:Z, EX x:A,
 PROPx (P i x)
   (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x) (SEPx (R i x))) a)
   with (EX  i:Z, EX x:A, PROPx (P i x)
   (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x) (SEPx (R i x))))
 by (extensionality; reflexivity).
apply sequential.
eapply semax_pre_simple; [ | apply semax_set].
eapply derives_trans; [ | apply now_later].
simpl typeof.
autorewrite with ret_assert.
apply andp_right.
apply andp_left1.
intro rho.
unfold local, lift1.
simpl.
normalize.
apply andp_right.
unfold tc_expr;
unfold typecheck_expr; fold typecheck_expr.
repeat rewrite denote_tc_assert_andp; simpl.
repeat apply andp_right; try apply @TT_right.
rewrite TI. apply @TT_right.
unfold tc_temp_id, typecheck_temp_id.
rewrite TI.
rewrite denote_tc_assert_andp; simpl;
repeat apply andp_right; apply @TT_right.
autorewrite with ret_assert.
intro rho.
rewrite exp_andp2.
simpl.
unfold subst.
apply exp_left; intro i.
apply exp_right with (i+1).
rewrite exp_andp2.
apply exp_left; intro x.
apply exp_right with x.
simpl.
repeat rewrite <- insert_local.
simpl.
specialize (CLOQ (i+1) x).
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
 unfold force_val2, both_int; rewrite <- H; simpl.
 unfold Cop2.sem_cast, Cop2.classify_cast. simpl.
 destruct Archi.ptr64 eqn:Hp; simpl.
 normalize.
 simpl; normalize.
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
Hint Rewrite op_Z_int_Vint_repr using rep_omega : norm.

Lemma op_Z_uint_Vint_repr:
  forall op i n,
   0 <= n <= Int.max_unsigned ->
    op_Z_uint op i (Vint (Int.repr n)) = op i n.
Proof.
 intros.
 unfold op_Z_uint. rewrite Int.unsigned_repr by auto.
 auto.
Qed.
Hint Rewrite op_Z_uint_Vint_repr using rep_omega : norm.

Lemma semax_for_simple_bound_ex :
 forall n Inv Espec {cs: compspecs} Delta Pre (A: Type)
           (P:  Z -> A -> list Prop) (Q: Z -> A -> list localdef) (R: Z -> A -> list mpred)
           _i init hi body Post
     (INV: Inv = EX i:Z, EX x:A, PROPx (P i x)  (LOCALx (Q i x) (SEPx (R i x))))
     (RANGE: Int.min_signed <= n <= Int.max_signed)
     (TI: (temp_types Delta) ! _i = Some (tint, true))
     (Thi: typeof hi = tint)
     (CLOhi: closed_wrt_vars (eq _i) (eval_expr hi))
     (CLOQ: forall i x, Forall (closed_wrt_vars (eq _i)) (map locald_denote (Q i x))),
     @semax cs Espec Delta Pre init
      (normal_ret_assert
        (EX i:Z, EX x:A, local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
         PROPx ((Int.min_signed <= i <= n) :: P i x)
         (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x)
         (SEPx (R i x))))) ->
     (forall i x, ENTAIL Delta,
       PROPx ((Int.min_signed <= i <= n) :: P i x)
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x)
       (SEPx (R i x))) |--
            (tc_expr Delta (Ebinop Olt (Etempvar _i tint) hi tint))) ->
       (ENTAIL Delta, EX x:A, PROPx (P n x)
                  (LOCALx (temp _i (Vint (Int.repr n))
                                  :: (Q n x)) (SEPx (R n x)))
            |-- RA_normal Post)    ->
     (forall i x,
     @semax cs Espec Delta
        (PROPx ((Int.min_signed <= i < n) :: P i x)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i x))
         (SEPx (R i x))))
        body
        (normal_ret_assert (local (`(eq (Vint (Int.repr n))) (eval_expr hi) ) &&
                          EX x:A,  PROPx ((Int.min_signed < i+1 <= n) :: P (i+1) x)
                             (LOCALx (temp _i (Vint (Int.repr i)) :: Q (i+1) x)
                             (SEPx (R (i+1) x)))))) ->
     @semax cs Espec Delta Pre
       (Sfor init
                (Ebinop Olt (Etempvar _i tint) hi tint)
                body
                (Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))) Post.
Proof.
intros.
subst Inv.
eapply (semax_for_simple (EX i:Z, EX x:A, local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
                                                     PROPx ((i<=n) :: P i x)  (LOCALx (Q i x) (SEPx (R i x)))));
 try reflexivity; auto.
+
intros. simpl. auto with closed.
+
eapply semax_post'; [ | apply H].
intros. apply andp_left2.
go_lowerx.
apply exp_derives; intro i.
apply exp_derives; intro x.
normalize. apply andp_right; auto.
apply prop_right; repeat split; auto; try omega.
+
intros i x. eapply derives_trans; [ | solve [eauto]].
instantiate (1:=x).
instantiate (1:=i).
go_lowerx. normalize. apply andp_right; auto.
apply prop_right.
split; [omega | ].
split; auto.
+
apply exp_left; intro i.
rewrite exp_andp2.
apply exp_left; intro x.
eapply derives_trans; [ | apply H1].
Exists x.
go_lowerx; normalize.
rewrite <- H4 in H3.
normalize in H3.
assert (i=n) by omega.
subst i.
apply andp_right; auto.
apply prop_right.
split; auto.
+
intros i x.
eapply semax_pre_post'; [ | | solve [eauto]].
instantiate (1:=x).
instantiate (1:=i).
apply andp_left2. go_lowerx; normalize.
apply andp_right; auto.
apply prop_right.
split; auto.
rewrite <- H4 in H3; normalize in H3.
omega.
intros.
apply andp_left2.
go_lowerx; normalize.
apply exp_right with x0.
normalize.
apply andp_right; auto.
apply prop_right.
split; auto. omega. split; auto. split; auto.
omega.
Qed.

Lemma semax_for_simple_bound :
 forall n Inv Espec {cs: compspecs} Delta Pre
           (P:  Z -> list Prop) (Q: Z -> list localdef) (R: Z -> list mpred)
           _i init hi body Post
     (INV: Inv = EX i:Z, PROPx (P i)  (LOCALx (Q i) (SEPx (R i))))
     (RANGE: Int.min_signed <= n <= Int.max_signed)
     (TI: (temp_types Delta) ! _i = Some (tint, true))
     (Thi: typeof hi = tint)
     (CLOhi: closed_wrt_vars (eq _i) (eval_expr hi))
     (CLOQ: forall i, Forall (closed_wrt_vars (eq _i)) (map locald_denote (Q i))),
     @semax cs Espec Delta Pre init
      (normal_ret_assert
        (EX i:Z, local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
         PROPx ((Int.min_signed <= i <= n) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i)) :: Q i)
         (SEPx (R i))))) ->
     (forall i, ENTAIL Delta,
       PROPx ((Int.min_signed <= i <= n) :: P i)
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i)
       (SEPx (R i))) |--
            (tc_expr Delta (Ebinop Olt (Etempvar _i tint) hi tint))) ->
       ENTAIL Delta, PROPx (P n)
                  (LOCALx (temp _i (Vint (Int.repr n))
                                  :: (Q n)) (SEPx (R n)))
            |-- RA_normal Post  ->
     (forall i,
     @semax cs Espec Delta
        (PROPx ((Int.min_signed <= i < n) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i))
         (SEPx (R i))))
        body
        (normal_ret_assert (local (`(eq (Vint (Int.repr n))) (eval_expr hi) ) &&
                             PROPx ((Int.min_signed < i+1 <= n) :: P (i+1))
                             (LOCALx (temp _i (Vint (Int.repr i)) :: Q (i+1))
                             (SEPx (R (i+1))))))) ->
     @semax cs Espec Delta Pre
       (Sfor init
                (Ebinop Olt (Etempvar _i tint) hi tint)
                body
                (Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))) Post.
Proof.
intros.
apply (@semax_for_simple_bound_ex n
   (EX i:Z, EX x:unit, PROPx (P i) (LOCALx (Q i) (SEPx (R i))))
   Espec cs Delta Pre unit (fun i x => P i) (fun i x => Q i) (fun i x => R i)
    _i init hi body Post); auto.
eapply semax_post'; try eassumption.
*
apply andp_left2; apply exp_derives; intro i. apply exp_right with tt. auto.
*
Intros u. auto.
*
intros.
eapply semax_post'; [ | apply (H2 i)].
apply andp_left2.
apply andp_derives; auto. apply exp_right with tt; auto.
Qed.

Lemma semax_for_simple_bound_ex_u :
 forall n Inv Espec {cs: compspecs} Delta Pre (A: Type)
           (P:  Z -> A -> list Prop) (Q: Z -> A -> list localdef) (R: Z -> A -> list mpred)
           _i init hi body Post s1 s2 s3
     (INV: Inv = EX i:Z, EX x:A, PROPx (P i x)  (LOCALx (Q i x) (SEPx (R i x))))
     (RANGE: 0 <= n <= Int.max_unsigned)
     (TI: (temp_types Delta) ! _i = Some (tuint, true))
     (Thi: typeof hi = Tint I32 s1 noattr)
     (CLOhi: closed_wrt_vars (eq _i) (eval_expr hi))
     (CLOQ: forall i x, Forall (closed_wrt_vars (eq _i)) (map locald_denote (Q i x))),
     @semax cs Espec Delta Pre init
      (normal_ret_assert
        (EX i:Z, EX x:A, local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
          PROPx ((0 <= i <= n) :: P i x)
          (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x)
           (SEPx (R i x))))) ->
     (forall i x,
       ENTAIL Delta,
       PROPx ((0 <= i <= n) :: P i x)
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x)
       (SEPx (R i x))) |--
            (tc_expr Delta (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)))) ->
     (ENTAIL Delta,
            EX x:A, PROPx (P n x)
                  (LOCALx (temp _i (Vint (Int.repr n))
                                  :: (Q n x)) (SEPx (R n x)))
            |-- RA_normal Post)    ->
     (forall i x,
     @semax cs Espec Delta
        (PROPx ((0 <= i < n) :: P i x)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i x))
         (SEPx (R i x))))
        body
        (normal_ret_assert (local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
                          EX x:A,   PROPx ((0 <= i+1 <= n) :: P (i+1) x)
                             (LOCALx (temp _i (Vint (Int.repr i)) :: Q (i+1) x)
                             (SEPx (R (i+1) x)))))) ->
     @semax cs Espec Delta Pre
       (Sfor init
                (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr))
                body
                (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) (Tint I32 s2 noattr)) tuint))) Post.
Proof.
intros.
subst Inv.
eapply (semax_for_simple_u (EX i:Z, EX x:A, local (`(eq (Vint (Int.repr n))) (eval_expr hi)) && PROPx ((i<=n) :: P i x)  (LOCALx (Q i x) (SEPx (R i x)))));
 try reflexivity; eauto.
+
intros. simpl. auto with closed.
+
eapply semax_post'; [ | apply H].
intros. apply andp_left2.
apply exp_derives; intro i.
apply exp_derives; intro x.
go_lowerx. normalize. apply andp_right; auto.
apply prop_right; repeat split; auto; try omega.
+
intros i x. eapply derives_trans; [ | solve [eauto]].
instantiate (1:=x).
instantiate (1:=i).
go_lowerx. normalize. apply andp_right; auto.
apply prop_right.
split; [omega | ].
split; auto.
+
apply exp_left; intro i.
rewrite exp_andp2.
apply exp_left; intro x.
eapply derives_trans; [ | solve [eauto]].
go_lowerx; normalize.
rewrite <- H4 in H3.
normalize in H3.
assert (i=n) by omega.
subst i.
Exists x.
normalize.
+
intros i x.
eapply semax_pre_post'; [ | | solve [eauto]].
instantiate (1:=x).
instantiate (1:=i).
apply andp_left2. go_lowerx; normalize.
apply andp_right; auto.
apply prop_right.
split; auto.
rewrite <- H4 in H3; normalize in H3.
omega.
intros.
apply andp_left2.
rewrite exp_andp2. apply exp_derives; intro x0.
go_lowerx; normalize.
apply andp_right; auto.
apply prop_right.
split; auto. omega. split; auto. split; auto.
omega.
Qed.

Lemma semax_for_simple_bound_u :
 forall n Inv Espec {cs: compspecs} Delta Pre
           (P:  Z -> list Prop) (Q: Z -> list localdef) (R: Z -> list mpred)
           _i init hi body Post s1 s2 s3
     (INV: Inv = EX i:Z, PROPx (P i)  (LOCALx (Q i) (SEPx (R i))))
     (RANGE: 0 <= n <= Int.max_unsigned)
     (TI: (temp_types Delta) ! _i = Some (tuint, true))
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
       ENTAIL Delta,
       PROPx ((0 <= i <= n) :: P i)
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i)
       (SEPx (R i))) |--
            (tc_expr Delta (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)))) ->
     (ENTAIL Delta,
            PROPx (P n)
                  (LOCALx (temp _i (Vint (Int.repr n))
                                  :: (Q n)) (SEPx (R n)))
            |-- RA_normal Post)    ->
     (forall i,
     @semax cs Espec Delta
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
apply (@semax_for_simple_bound_ex_u n
   (EX i:Z, EX x:unit, PROPx (P i) (LOCALx (Q i) (SEPx (R i))))
   Espec cs Delta Pre unit (fun i x => P i) (fun i x => Q i) (fun i x => R i)
    _i init hi body Post s1 s2 s3); auto.
eapply semax_post'; try eassumption.
*
apply andp_left2; apply exp_derives; intro i. apply exp_right with tt. auto.
*
Intros u; auto.
*
intros.
eapply semax_post'; [ | apply (H2 i)].
apply andp_left2; 
apply andp_derives; auto. apply exp_right with tt; auto.
Qed.

Lemma semax_for_simple_bound_const_init_ex :
 forall n Inv Espec {cs: compspecs} Delta (Pre: environ -> mpred) (A: Type)
           (P:  Z -> A -> list Prop) (Q: Z -> A -> list localdef) (R: Z -> A -> list mpred)
           _i lo hi body Post
     (INV: Inv = EX i:Z, EX x:A, PROPx (P i x)  (LOCALx (Q i x) (SEPx (R i x))))
     (RANGElo: Int.min_signed <= lo <= n)
     (RANGE: n <= Int.max_signed)
     (TI: typeof_temp Delta _i = Some tint)
     (Thi: typeof hi = tint)
     (CLOhi: closed_wrt_vars (eq _i) (eval_expr hi))
     (CLOQ: forall i x, Forall (closed_wrt_vars (eq _i)) (map locald_denote (Q i x))),
     local (tc_environ Delta) && Pre |-- local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
       (EX x:A, (PROPx (P lo x)
         (LOCALx (Q lo x)
         (SEPx (R lo x))))) ->
     (forall i x, ENTAIL (initialized _i Delta),
       PROPx ((lo <= i <= n) :: P i x)
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x)
       (SEPx (R i x))) |--
            (tc_expr (initialized _i Delta) (Ebinop Olt (Etempvar _i tint) hi tint))) ->
     (ENTAIL (initialized _i Delta),
         EX x:A, PROPx (P n x)
                  (LOCALx (temp _i (Vint (Int.repr n)) :: (Q n x)) (SEPx (R n x)))
            |-- RA_normal Post)    ->
     (forall i x,
     @semax cs Espec (initialized _i Delta)
        (PROPx ((lo <= i < n) :: P i x)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i x))
         (SEPx (R i x))))
        body
        (normal_ret_assert (local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
                           EX x:A,  PROPx ((lo < i+1 <= n) :: P (i+1) x)
                             (LOCALx (temp _i (Vint (Int.repr i)) :: Q (i+1) x)
                             (SEPx (R (i+1) x)))))) ->
     @semax cs Espec Delta Pre
       (Sfor (Sset _i (Econst_int (Int.repr lo) tint))
                (Ebinop Olt (Etempvar _i tint) hi tint)
                body
                (Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))) Post.
Proof.
intros.
eapply (semax_for_simple_bound_ex n (EX i:Z, EX x:A, PROPx ((lo<=i) :: P i x)  (LOCALx (Q i x) (SEPx (R i x)))));
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
  with (EX x:A, !!fold_right and True (P lo x) && local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
         (PROPx nil
          (LOCALx (Q lo x) (SEPx (R lo x))))).
eapply derives_trans; [apply H | ].
go_lowerx; normalize.
apply exp_right with x.
normalize.
apply extract_exists_pre; intro x.
rewrite andp_assoc.
apply semax_extract_prop; intro.
eapply semax_post_flipped'.
eapply forward_setx'.
go_lowerx.
apply andp_right. apply @TT_right.
unfold tc_temp_id. unfold typecheck_temp_id.
unfold typeof_temp in TI.
destruct ((temp_types Delta) ! _i); inv TI. destruct p. inv H8.
rewrite denote_tc_assert_andp; simpl.
apply andp_right.
apply prop_right. auto. apply @TT_right.
simpl exit_tycon.
Intros old.
autorewrite with subst.
Exists lo x.
go_lowerx. normalize. apply andp_right; auto.
apply prop_right.
split.
split; [omega  | auto].
unfold_lift; split; auto.
*
intros i x.
eapply derives_trans; [ | solve [eauto]].
instantiate (1:=x).
instantiate (1:=i).
go_lowerx; normalize.
 progress (autorewrite with norm1 norm2); normalize.
apply andp_right; auto.
apply prop_right. split; [omega | ].
split; auto.
*
simpl update_tycon. cbv beta.
Intros x.
eapply derives_trans; [ | apply H1].
Exists x.
go_lowerx; normalize.
*
intros i x.
simpl.
eapply semax_pre_post'; [ | | apply H2].
instantiate (1:=x).
instantiate (1:=i).
go_lowerx; normalize;
 progress (autorewrite with norm1 norm2); normalize;
apply andp_right; [apply prop_right | auto].
split; auto. omega.
intros.
apply andp_left2.
rewrite exp_andp2. apply exp_left; intro x0.
go_lowerx; normalize.
apply exp_right with x0; normalize.
apply andp_right; [apply prop_right | auto].
split; [omega | ].
split; auto.
split; [omega | ].
auto.
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
            |-- RA_normal Post)    ->
     (forall i,
     @semax cs Espec (initialized _i Delta)
        (PROPx ((lo <= i < n) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i))
         (SEPx (R i))))
        body
        (normal_ret_assert (local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
                             PROPx ((lo < i+1 <= n) :: P (i+1))
                             (LOCALx (temp _i (Vint (Int.repr i)) :: Q (i+1))
                             (SEPx (R (i+1))))))) ->
     @semax cs Espec Delta Pre
       (Sfor (Sset _i (Econst_int (Int.repr lo) tint))
                (Ebinop Olt (Etempvar _i tint) hi tint)
                body
                (Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))) Post.
Proof.
intros.
apply (@semax_for_simple_bound_const_init_ex n
   (EX i:Z, EX x:unit, PROPx (P i) (LOCALx (Q i) (SEPx (R i))))
   Espec cs Delta Pre unit (fun i x => P i) (fun i x => Q i) (fun i x => R i)
           _i lo hi body Post); auto.
*
Exists tt. auto.
*
Intros u.
eapply derives_trans; [ | apply H1].
go_lowerx; normalize.
*
intros.
eapply semax_post'; [ | apply (H2 i)].
apply andp_left2; apply andp_derives; auto. apply exp_right with tt; auto.
Qed.


Lemma semax_for_simple_bound_const_init_ex_u :
 forall n Inv Espec {cs: compspecs} Delta (Pre: environ -> mpred) (A: Type)
           (P:  Z -> A -> list Prop) (Q: Z -> A -> list localdef) (R: Z -> A -> list mpred)
           _i lo hi body Post s0 s1 s2 s3
     (INV: Inv = EX i:Z, EX x:A, PROPx (P i x)  (LOCALx (Q i x) (SEPx (R i x))))
     (RANGElo: 0 <= lo <= n)
     (RANGE: n <= Int.max_unsigned)
     (TI: typeof_temp Delta _i = Some tuint)
     (Thi: typeof hi = Tint I32 s1 noattr)
     (CLOhi: closed_wrt_vars (eq _i) (eval_expr hi))
     (CLOQ: forall i x, Forall (closed_wrt_vars (eq _i)) (map locald_denote (Q i x))),
     local (tc_environ Delta) && Pre |-- local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
       (EX x:A, (PROPx (P lo x)
         (LOCALx (Q lo x)
         (SEPx (R lo x))))) ->
     (forall i x, ENTAIL (initialized _i Delta),
        PROPx ((lo <= i <= n) :: P i x)
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x)
       (SEPx (R i x))) |--
            (tc_expr (initialized _i Delta) (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr)))) ->
     (ENTAIL (initialized _i Delta), EX x:A, PROPx (P n x)
                  (LOCALx (temp _i (Vint (Int.repr n))
                                  :: (Q n x)) (SEPx (R n x)))
            |-- RA_normal Post)    ->
     (forall i x,
     @semax cs Espec (initialized _i Delta)
        (PROPx ((lo <= i < n) :: P i x)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i x))
         (SEPx (R i x))))
        body
        (normal_ret_assert (local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
                 EX x:A,  PROPx ((lo <= i+1 <= n) :: P (i+1) x)
                             (LOCALx (temp _i (Vint (Int.repr i)) :: Q (i+1) x)
                             (SEPx (R (i+1) x)))))) ->
     @semax cs Espec Delta Pre
       (Sfor (Sset _i (Econst_int (Int.repr lo) (Tint I32 s0 noattr)))
                (Ebinop Olt (Etempvar _i tuint) hi (Tint I32 s3 noattr))
                body
                (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) (Tint I32 s2 noattr)) tuint))) Post.
Proof.
intros.
eapply (semax_for_simple_bound_ex_u n
   (EX i:Z, EX x:A, PROPx ((lo<=i) :: P i x)  (LOCALx (Q i x) (SEPx (R i x)))));
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
  with (EX x:A, !!fold_right and True (P lo x) && local (`(eq (Vint (Int.repr n))) (eval_expr hi)) &&
         (PROPx nil
          (LOCALx
             (Q lo x)
             (SEPx (R lo x))))).
eapply derives_trans; [apply H | ].
go_lowerx; normalize.
Exists x; normalize.
apply extract_exists_pre. intro x.
rewrite andp_assoc.
apply semax_extract_prop; intro.
eapply semax_post_flipped'.
eapply forward_setx'.
go_lowerx.
apply andp_right; try apply @TT_right.
unfold tc_temp_id. unfold typecheck_temp_id.
unfold typeof_temp in TI.
destruct ((temp_types Delta) ! _i); inv TI. destruct p. inv H8.
rewrite denote_tc_assert_andp, denote_tc_assert_bool; simpl.
apply andp_right. apply prop_right; auto.
destruct s0; apply @TT_right.
Intro old.
autorewrite with subst.
Exists lo x.
go_lowerx. normalize. apply andp_right; auto.
apply prop_right.
split. 
split; [omega  | auto].
unfold_lift; split; auto.
*
intros i x.
eapply derives_trans; [ | solve [eauto]].
instantiate (1:=x).
instantiate (1:=i).
go_lowerx; normalize.
 progress (autorewrite with norm1 norm2); normalize.
apply andp_right; auto.
apply prop_right. split; [omega | ].
split; auto.
*
eapply derives_trans; [ | apply H1].
Intros x; Exists x.
go_lowerx; normalize.
*
intros i x.
simpl.
eapply semax_pre_post'; [ | | apply H2].
instantiate (1:=x).
instantiate (1:=i).
go_lowerx; normalize;
 progress (autorewrite with norm1 norm2); normalize;
apply andp_right; [apply prop_right | auto].
split; auto. omega.
intros.
apply andp_left2.
rewrite exp_andp2. apply exp_left; intro x0.
go_lowerx; normalize.
apply exp_right with x0; normalize.
apply andp_right; [apply prop_right | auto].
split; [omega | ].
split; auto.
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
            |-- RA_normal Post)    ->
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
apply (@semax_for_simple_bound_const_init_ex_u n
   (EX i:Z, EX x:unit, PROPx (P i) (LOCALx (Q i) (SEPx (R i))))
   Espec cs Delta Pre unit (fun i x => P i) (fun i x => Q i) (fun i x => R i)
           _i lo hi body Post s0 s1 s2 s3); auto.
*
Exists tt. auto.
*
Intros u.
eapply derives_trans; [ | apply H1]. go_lowerx; normalize.
*
intros.
eapply semax_post'; [ | apply (H2 i)].
apply andp_left2; 
apply andp_derives; auto. apply exp_right with tt; auto.
Qed.


Lemma semax_for_const_bound_const_init_ex :
 forall n Inv Espec {cs: compspecs} Delta (Pre: environ -> mpred) (A: Type)
           (P:  Z -> A -> list Prop) (Q: Z -> A -> list localdef) (R: Z -> A -> list mpred)
           _i lo hi body Post
     (INV: Inv = EX i:Z, EX x:A, PROPx (P i x)  (LOCALx (Q i x) (SEPx (R i x))))
     (RANGElo: Int.min_signed <= lo <= n)
     (RANGE: n <= Int.max_signed)
     (TI: typeof_temp Delta _i = Some tint)
     (Thi: hi=n)
     (CLOQ: forall i x, Forall (closed_wrt_vars (eq _i)) (map locald_denote (Q i x))),
     local (tc_environ Delta) && Pre |--
       (EX x:A, PROPx (P lo x) (LOCALx (Q lo x) (SEPx (R lo x)))) ->
     (forall i x, ENTAIL (initialized _i Delta),
           PROPx ((lo <= i <= n) :: P i x)
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x)
       (SEPx (R i x))) |--
            (tc_expr (initialized _i Delta) (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr hi) tint) tint))) ->
     (ENTAIL (initialized _i Delta),
           EX x:A, PROPx (P n x)
                  (LOCALx (temp _i (Vint (Int.repr n)) :: (Q n x)) (SEPx (R n x)))
            |-- RA_normal Post)    ->
     (forall i x,
     @semax cs Espec (initialized _i Delta)
        (PROPx ((lo <= i < n) :: P i x)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i x))
         (SEPx (R i x))))
        body
        (normal_ret_assert (EX x:A, PROPx ((lo < i+1 <= n) :: P (i+1) x)
                             (LOCALx (temp _i (Vint (Int.repr i)) ::  Q (i+1) x)
                             (SEPx (R (i+1) x)))))) ->
     @semax cs Espec Delta Pre
       (Sfor (Sset _i (Econst_int (Int.repr lo) tint))
                (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr hi) tint) tint)
                body
                (Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))) Post.
Proof.
intros.
subst n.
eapply semax_for_simple_bound_const_init_ex;
 eauto.
*
 auto with closed.
*
 eapply derives_trans ; [apply H | ].
 go_lowerx. repeat apply andp_right; try apply prop_right; auto.
*
 intros.
 eapply semax_post_flipped'; [ apply H2 | ].
 go_lowerx. repeat rewrite prop_true_andp. auto.
 unfold_lift; simpl. repeat split; auto.
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
            |-- RA_normal Post)    ->
     (forall i,
     @semax cs Espec (initialized _i Delta)
        (PROPx ((lo <= i < n) :: P i)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i))
         (SEPx (R i))))
        body
        (normal_ret_assert (PROPx ((lo < i+1 <= n) :: P (i+1))
                             (LOCALx (temp _i (Vint (Int.repr i)) ::  Q (i+1))
                             (SEPx (R (i+1))))))) ->
     @semax cs Espec Delta Pre
       (Sfor (Sset _i (Econst_int (Int.repr lo) tint))
                (Ebinop Olt (Etempvar _i tint) (Econst_int (Int.repr hi) tint) tint)
                body
                (Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))) Post.
Proof.
intros.
apply (@semax_for_const_bound_const_init_ex n
   (EX i:Z, EX x:unit, PROPx (P i) (LOCALx (Q i) (SEPx (R i))))
   Espec cs Delta Pre unit (fun i x => P i) (fun i x => Q i) (fun i x => R i)
           _i lo hi body Post); auto.
*
Exists tt; auto.
*
Intros u.
eapply derives_trans; [ | apply H1]. go_lowerx; normalize.
*
intros.
eapply semax_post'; [ | apply (H2 i)].
apply andp_left2; 
Exists tt; auto.
Qed.


Lemma semax_for_const_bound_const_init_ex_u :
 forall n Inv Espec {cs: compspecs} Delta (Pre: environ -> mpred) (A: Type)
           (P:  Z -> A -> list Prop) (Q: Z -> A -> list localdef) (R: Z -> A -> list mpred)
           _i lo hi body Post s1 s2
     (INV: Inv = EX i:Z, EX x:A, PROPx (P i x)  (LOCALx (Q i x) (SEPx (R i x))))
     (RANGElo: 0 <= lo <= n)
     (RANGE: n <= Int.max_unsigned)
     (TI: typeof_temp Delta _i = Some tuint)
     (Thi: hi=n)
     (CLOQ: forall i x, Forall (closed_wrt_vars (eq _i)) (map locald_denote (Q i x))),
     local (tc_environ Delta) && Pre |--
        (EX x:A, PROPx (P lo x) (LOCALx (Q lo x) (SEPx (R lo x)))) ->
     (forall i x, ENTAIL (initialized _i Delta),
           PROPx ((lo <= i <= n) :: P i x)
       (LOCALx (temp _i (Vint (Int.repr i)) :: Q i x)
       (SEPx (R i x))) |--
            (tc_expr (initialized _i Delta) (Ebinop Olt (Etempvar _i tuint) (Econst_int (Int.repr hi) (Tint I32 s1 noattr)) tint))) ->
     (ENTAIL (initialized _i Delta),
           EX x:A, PROPx (P n x)
                  (LOCALx (temp _i (Vint (Int.repr n)) :: (Q n x)) (SEPx (R n x)))
            |-- RA_normal Post)    ->
     (forall i x,
     @semax cs Espec (initialized _i Delta)
        (PROPx ((lo <= i < n) :: P i x)
         (LOCALx (temp _i (Vint (Int.repr i)) :: (Q i x))
         (SEPx (R i x))))
        body
        (normal_ret_assert (EX x:A, PROPx ((lo <= i+1 <= n) :: P (i+1) x)
                             (LOCALx (temp _i (Vint (Int.repr i)) ::  Q (i+1) x)
                             (SEPx (R (i+1) x)))))) ->
     @semax cs Espec Delta Pre
       (Sfor (Sset _i (Econst_int (Int.repr lo) tint))
                (Ebinop Olt (Etempvar _i tuint) (Econst_int (Int.repr hi) (Tint I32 s1 noattr)) tint)
                body
                (Sset _i (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) (Tint I32 s2 noattr)) tuint))) Post.
Proof.
intros.
subst n.
eapply semax_for_simple_bound_const_init_ex_u;
 eauto.
*
 reflexivity.
*
 auto with closed.
*
 eapply derives_trans ; [apply H | ].
 go_lowerx. repeat apply andp_right; try apply prop_right; auto.
* intros.
 eapply semax_post_flipped'; [ apply H2 | ].
 go_lowerx. repeat rewrite prop_true_andp. auto.
 unfold_lift; simpl. repeat split; auto.
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
            |-- RA_normal Post)    ->
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
apply (@semax_for_const_bound_const_init_ex_u n
   (EX i:Z, EX x:unit, PROPx (P i) (LOCALx (Q i) (SEPx (R i))))
   Espec cs Delta Pre unit (fun i x => P i) (fun i x => Q i) (fun i x => R i)
           _i lo hi body Post s1 s2); auto.
*
Exists tt; auto.
*
Intros u. eapply derives_trans; [ | apply H1]. go_lowerx; normalize.
*
intros.
eapply semax_post'; [ | apply (H2 i)].
apply andp_left2; 
Exists tt; auto.
Qed.

Lemma upd_compose:
  forall {A}{B}{C} {EA: EqDec A}(f: B ->C) (g: A -> B) (x: A) (y: B) x',
           upd (Basics.compose f g) x (f y) x' = f (upd g x y x').
Proof.
 intros; unfold upd, Basics.compose.  if_tac; auto.
Qed.
Hint Rewrite @upd_compose : norm.

Lemma semax_for_resolve_postcondition:
 forall Delta P,
   ENTAIL Delta, P |-- RA_normal (normal_ret_assert P).
Proof.
intros.
 apply andp_left2.
 rewrite normal_ret_assert_elim.
 auto.
Qed.

Ltac forward_for_simple_bound' n Pre :=
 first
 [ first [eapply (semax_for_const_bound_const_init n Pre); [reflexivity|..]
         | eapply (semax_for_const_bound_const_init_u n Pre); [reflexivity|..]
         | eapply (semax_for_const_bound_const_init_ex n Pre); [reflexivity|..]
         | eapply (semax_for_const_bound_const_init_ex_u n Pre); [reflexivity|..]];
  [try rep_omega | try rep_omega | reflexivity | try reflexivity; omega
  | intro; unfold map at 1; auto 50 with closed
  | cbv beta; simpl update_tycon
  | intro; cbv beta; simpl update_tycon; try solve [entailer!]
  | intros; cbv beta; try apply semax_for_resolve_postcondition
  | intros; cbv beta; simpl update_tycon; abbreviate_semax;
   try (apply semax_extract_PROP; intro) ]
 | first [eapply (semax_for_simple_bound_const_init n Pre); [reflexivity|..]
         | eapply (semax_for_simple_bound_const_init_u n Pre); [reflexivity|..]
         | eapply (semax_for_simple_bound_const_init_ex n Pre); [reflexivity|..]
         | eapply (semax_for_simple_bound_const_init_ex_u n Pre); [reflexivity|..]];
  [try rep_omega | try rep_omega | reflexivity | reflexivity
  | auto 50 with closed
  | intro; unfold map at 1; auto 50 with closed
  | cbv beta; simpl update_tycon
  | intro; cbv beta; simpl update_tycon; try solve [entailer!]
  | intros; cbv beta; try apply semax_for_resolve_postcondition
  | intros; cbv beta; simpl update_tycon; abbreviate_semax;
   try (apply semax_extract_PROP; intro) ]
 |first [eapply (semax_for_simple_bound n Pre); [reflexivity|..]
         |eapply (semax_for_simple_bound_u n Pre); [reflexivity|..]
         |eapply (semax_for_simple_bound_ex n Pre); [reflexivity|..]
         |eapply (semax_for_simple_bound_ex_u n Pre); [reflexivity|..]];
  [try rep_omega | reflexivity | reflexivity
  | auto 50 with closed
  | intro; unfold map at 1; auto 50 with closed
  | cbv beta; simpl update_tycon
  | intro; cbv beta; simpl update_tycon; try solve [entailer!]
  | intros; cbv beta; try apply semax_for_resolve_postcondition
  | intros; cbv beta; simpl update_tycon; abbreviate_semax;
     try (apply semax_extract_PROP; intro) ]
  ].
