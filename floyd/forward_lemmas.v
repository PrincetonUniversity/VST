Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.expr_lemmas.
Require Import floyd.client_lemmas.
(*Require Import floyd.nested_field_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
*)
Require Import floyd.closed_lemmas.
Import Cop.
Local Open Scope logic.

Lemma semax_func_skip1: 
   forall {Espec: OracleKind} 
        V (G: funspecs) (cs: compspecs) fs i f j f' G',
      i <> j ->
      semax_func V G fs ((j,f')::G') ->
      semax_func V G ((i,f)::fs) ((j,f')::G').
Proof.
intros.
apply semax_func_skip; auto.
Qed.

Lemma semax_func_nil': 
   forall {Espec: OracleKind} 
        V (G: funspecs)  (cs: compspecs) fs,
      semax_func V G fs nil.
Proof.
intros.
induction fs. 
apply semax_func_nil.
apply semax_func_skip; auto.
Qed.

Lemma semax_ifthenelse_PQR : 
   forall Espec {cs: compspecs} Delta P Q R (b: expr) c d Post,
      bool_type (typeof b) = true ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--  (tc_expr Delta (Eunop Cop.Onotbool b tint)) ->
     @semax cs Espec Delta (PROPx P (LOCALx (`(typed_true (typeof b)) (eval_expr b) :: Q) (SEPx R)))
                        c Post -> 
     @semax cs Espec Delta (PROPx P (LOCALx (`(typed_false (typeof b)) (eval_expr b) :: Q) (SEPx R)))
                        d Post -> 
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
                         (Sifthenelse b c d) Post.
Proof.
 intros.
 eapply semax_pre;  [ | apply semax_ifthenelse]; auto.
 instantiate (1:=(PROPx P (LOCALx Q (SEPx R)))).
 apply andp_right; auto. rewrite <- insert_local; apply andp_left2; auto.
 rewrite andp_comm. rewrite insert_local. auto.
 rewrite andp_comm. rewrite insert_local. auto.
Qed.

Lemma int_eq_false_e:
  forall i j, Int.eq i j = false -> i <> j.
Proof.
intros.
intro; subst.
rewrite Int.eq_true in H; inv H.
Qed.


Lemma repr_inj_signed:
  forall i j, 
    repable_signed i -> repable_signed j -> Int.repr i = Int.repr j -> i=j.
Proof.
intros.
rewrite <- (Int.signed_repr i) by repable_signed.
rewrite <- (Int.signed_repr j) by repable_signed.
congruence.
Qed.

Lemma repr_inj_unsigned:
  forall i j, 
    0 <= i <= Int.max_unsigned -> 
    0 <= j <= Int.max_unsigned -> 
    Int.repr i = Int.repr j -> i=j.
Proof.
intros.
rewrite <- (Int.unsigned_repr i) by repable_signed.
rewrite <- (Int.unsigned_repr j) by repable_signed.
congruence.
Qed.


Lemma repr_inj_signed':
  forall i j, 
    (* The first two premises are not needed to prove this,
     but are used to limit its applicability *)
    repable_signed i -> repable_signed j -> 
    Int.repr i <> Int.repr j -> i<>j.
Proof.
intros.
congruence.
Qed.

Lemma repr_inj_unsigned':
  forall i j, 
    0 <= i <= Int.max_unsigned -> 
    0 <= j <= Int.max_unsigned -> 
    Int.repr i <> Int.repr j -> i<>j.
Proof.
intros.
congruence.
Qed.

Lemma semax_ifthenelse_PQR' : 
   forall Espec {cs: compspecs} (v: val) Delta P Q R (b: expr) c d Post,
      bool_type (typeof b) = true ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
         (tc_expr Delta (Eunop Cop.Onotbool b tint))  ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (`(eq v) (eval_expr b)) ->
     @semax cs Espec Delta (PROPx (typed_true (typeof b) v :: P) (LOCALx Q (SEPx R)))
                        c Post -> 
     @semax cs Espec Delta (PROPx (typed_false (typeof b) v :: P) (LOCALx Q (SEPx R)))
                        d Post -> 
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
                         (Sifthenelse b c d) Post.
Proof.
 intros.
 eapply semax_pre;  [ | apply semax_ifthenelse]; auto.
 instantiate (1:=(PROPx P (LOCALx (`(eq v) (eval_expr b) :: Q) (SEPx R)))).
 apply andp_right; auto.
 rewrite <- (insert_local (`(eq v) _)).
 apply andp_right; auto.
 rewrite <- insert_local; apply andp_left2; auto.
 rewrite andp_comm, insert_local.
 eapply semax_pre; [ | eassumption].
 go_lowerx. normalize. apply andp_right; auto.
 subst; apply prop_right; repeat split; auto.
 rewrite andp_comm, insert_local.
 eapply semax_pre; [ | eassumption].
 go_lowerx. normalize. apply andp_right; auto.
 subst; apply prop_right; repeat split; auto.
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

(* NOTE: In both logical_or and logical_and,
  compcert (up to 2.4) has (Etempvar tid tbool)
  where I conjecture that it should have (Etempvar tid tint).
  That means our lemmas here are incompatible with
  compcert, at the moment.
*)

Definition logical_or tid e1 e2 :=
(Sifthenelse e1
             (Sset tid (Econst_int (Int.repr 1) tint))
             (Ssequence
                (Sset tid (Ecast e2 tbool))
                (Sset tid (Ecast (Etempvar tid tint (*tbool*)) tint)))).



Definition logical_and tid e1 e2 :=
(Sifthenelse e1
            (Ssequence
              (Sset tid (Ecast e2 tbool))
              (Sset tid (Ecast (Etempvar tid tint (*tbool*)) tint)))
            (Sset tid (Econst_int (Int.repr 0) tint))).

Lemma semax_pre_flipped : 
 forall (P' : environ -> mpred) (Espec : OracleKind) {cs: compspecs}
         (Delta : tycontext) (P1 : list Prop) (P2 : list (environ -> Prop))
         (P3 : list (environ -> mpred)) (c : statement) 
         (R : ret_assert),
       semax Delta P' c R ->
       PROPx P1 (LOCALx (tc_environ Delta :: P2) (SEPx P3)) |-- P' ->
        semax Delta (PROPx P1 (LOCALx P2 (SEPx P3))) c R.
Proof. intros. 
eapply semax_pre. apply H0. auto.
Qed.

(*
Lemma bool_cast : forall Delta e rho,
   tc_val (typeof e) (eval_expr Delta e rho) ->
  force_val (Cop2.sem_cast tbool tint (force_val (Cop2.sem_cast (typeof e) tbool (eval_expr Delta e rho)))) =
   match strict_bool_val (eval_expr Delta e rho) (typeof e) with
   | Some true => Vint Int.one
   | Some false => Vint Int.zero
   | None => Vundef
   end.
Proof.
intros.
rewrite tc_val_eq in H.
 simpl. unfold Cop2.sem_cast.
remember (eval_expr Delta e rho).
destruct v.
* inv H.
* destruct (typeof e) as [ | | | [ | ] |  | | | | ]; inv H; simpl;
  remember (Int.eq i Int.zero); if_tac; auto; try congruence.
* destruct (typeof e) as [ | | | [ | ] |  | | | | ]; inv H; simpl;
  remember (Int64.eq i Int64.zero); if_tac; auto; try congruence.
* destruct (typeof e) as [ | | | [ | ] |  | | | | ]; inv H; simpl;
    if_tac; auto.
*destruct (typeof e) as [ | | | [ | ] |  | | | | ]; inv H; simpl;
    if_tac; auto.
*destruct (typeof e) as [ | | | [ | ] |  | | | | ]; inv H; simpl; auto.
Qed.
*)

Lemma semax_while : 
 forall Espec {cs: compspecs} Delta Q test body R,
     bool_type (typeof test) = true ->
     (local (tc_environ Delta) && Q |--  (tc_expr Delta (Eunop Cop.Onotbool test tint))) ->
     (local (tc_environ Delta) && local (lift1 (typed_false (typeof test)) (eval_expr test)) && Q |-- R EK_normal None) ->
     @semax cs Espec Delta (local (`(typed_true (typeof test)) (eval_expr test)) && Q)  body (loop1_ret_assert Q R) ->
     @semax cs Espec Delta Q (Swhile test body) R.
Proof.
intros ? ? ? ? ? ? ? BT TC Post H.
unfold Swhile.
apply (@semax_loop Espec cs Delta Q Q).
Focus 2.
 clear; eapply semax_post; [ | apply semax_skip];
 destruct ek; unfold normal_ret_assert, loop2_ret_assert; intros;
 go_lowerx; try discriminate.
(* End Focus 2*)
apply semax_seq with 
 (local (`(typed_true (typeof test)) (eval_expr test)) && Q).
apply semax_pre_simple with ( (tc_expr Delta (Eunop Cop.Onotbool test tint)) && Q).
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

Lemma semax_while_3g1 : 
 forall Espec {cs: compspecs} {A} (v: A -> val) Delta P Q R test body Post,
     bool_type (typeof test) = true ->
     (forall a, PROPx (P a) (LOCALx (tc_environ Delta :: Q a) (SEPx (R a))) |-- (tc_expr Delta (Eunop Cop.Onotbool test tint))) ->
     (forall a, PROPx (P a) (LOCALx (tc_environ Delta :: Q a) (SEPx (R a))) |-- local (`(eq (v a)) (eval_expr test))) ->
     (forall a, @semax cs Espec Delta (PROPx (typed_true (typeof test) (v a) :: (P a)) (LOCALx (Q a) (SEPx (R a))))
                 body (loop1_ret_assert (EX a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a)))) 
                           (overridePost 
                            (EX a:A, PROPx (typed_false (typeof test) (v a) :: P a)  (LOCALx (Q a) (SEPx (R a))))
                            Post))) ->
     @semax cs Espec Delta (EX a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a)))) 
                 (Swhile test body) 
                 (overridePost
                   (EX a:A, PROPx (typed_false (typeof test) (v a) :: P a)  (LOCALx (Q a) (SEPx (R a))))
                   Post).
Proof.
intros.
apply semax_while; auto.
*
 rewrite exp_andp2. apply exp_left; intro a.
 eapply derives_trans; [ | apply H0].
 rewrite insert_local; apply derives_refl.
*
repeat rewrite exp_andp2. apply exp_left; intro a.
rewrite overridePost_normal'.
apply exp_right with a.
eapply derives_trans.
apply andp_right; [ | apply derives_refl].
eapply derives_trans; [ | apply (H1 a)].
rewrite (andp_comm (local _)).
rewrite andp_assoc. apply andp_left2. rewrite insert_local; auto.
go_lowerx; normalize.
repeat apply andp_right; auto. apply prop_right; split; auto.
rewrite H3; auto.
*
 repeat rewrite exp_andp2.
 apply extract_exists_pre; intro a.
 rewrite insert_local.
 eapply semax_pre; [ | apply (H2 a)].
 eapply derives_trans.
 apply andp_right; [ | apply derives_refl].
 eapply derives_trans; [ | apply (H1 a)].
 repeat rewrite <- insert_local.
 apply andp_derives; auto.
 apply andp_left2; auto.
 go_lowerx.
 repeat apply andp_right; auto; apply prop_right; repeat split; auto.
 rewrite H3; auto.
Qed.

Lemma semax_while_3g : 
 forall Espec {cs: compspecs} (v: val) Delta P Q R test body Post,
     bool_type (typeof test) = true ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- (tc_expr Delta (Eunop Cop.Onotbool test tint)) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`(eq v) (eval_expr test)) ->
     @semax cs Espec Delta (PROPx (typed_true (typeof test) v :: P) (LOCALx Q (SEPx R)))
                 body (loop1_ret_assert (PROPx P (LOCALx Q (SEPx R))) 
                           (overridePost 
                            (PROPx (typed_false (typeof test) v :: P)  (LOCALx Q (SEPx R)))
                            Post)) ->
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) 
                 (Swhile test body) 
                 (overridePost
                   (PROPx (typed_false (typeof test) v :: P)  (LOCALx Q (SEPx R)))
                   Post).
Proof.
intros.
apply semax_while; auto.
*
 rewrite insert_local; auto.
*
rewrite overridePost_normal'.
eapply derives_trans.
apply andp_right; [ | apply derives_refl].
eapply derives_trans; [ | apply H1].
rewrite (andp_comm (local _)).
rewrite andp_assoc. apply andp_left2. rewrite insert_local; auto.
go_lowerx; normalize.
repeat apply andp_right; auto. apply prop_right; split; auto.
rewrite H3; auto.
*
 rewrite insert_local.
 eapply semax_pre; [ | apply H2].
 eapply derives_trans.
 apply andp_right; [ | apply derives_refl].
 eapply derives_trans; [ | apply H1].
 repeat rewrite <- insert_local.
 apply andp_derives; auto.
 apply andp_left2; auto.
 go_lowerx.
 repeat apply andp_right; auto; apply prop_right; repeat split; auto.
 rewrite H3; auto.
Qed.

Lemma semax_while'_new :  (* DELETE ME *)
 forall Espec {cs: compspecs} (v: val) Delta P Q R test body Post,
     bool_type (typeof test) = true ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--  (tc_expr Delta (Eunop Cop.Onotbool test tint)) ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`(eq v) (eval_expr test)) ->
     PROPx (typed_false (typeof test) v :: P) (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- Post EK_normal None ->
     @semax cs Espec Delta (PROPx (typed_true (typeof test) v :: P) (LOCALx Q (SEPx R)))  body (loop1_ret_assert (PROPx P (LOCALx Q (SEPx R))) Post) ->
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) (Swhile test body) Post.
Proof.
intros.
apply semax_while; auto.
eapply derives_trans; [ | apply H0].
normalize. 
normalize; autorewrite with norm1 norm2; normalize.
eapply derives_trans; [ | apply H2].
 apply derives_trans with (local (`(eq v) (eval_expr test)) &&
     PROPx P
      (LOCALx (tc_environ Delta :: `(typed_false (typeof test)) (eval_expr test) :: Q) (SEPx R))).
 apply andp_right. 
 rewrite (andp_comm (local (tc_environ _))). 
 rewrite andp_assoc. apply andp_left2. rewrite insert_local; auto.
 rewrite andp_assoc; repeat rewrite insert_local.
 go_lowerx.
 apply andp_right; auto. apply prop_right.
 split3; auto.
 rewrite insert_local.
 go_lowerx. subst v. 
 apply andp_right; auto. apply prop_right.
 split; auto.
 apply andp_right; auto. apply prop_right.
 split; auto.
eapply semax_pre_simple; [ | apply H3].
 rewrite <- andp_assoc.
 apply derives_trans with (local (`(eq v) (eval_expr test)) &&
     PROPx P
      (LOCALx (tc_environ Delta :: `(typed_true (typeof test)) (eval_expr test) :: Q) (SEPx R))).
 apply andp_right. 
 rewrite (andp_comm (local (tc_environ _))). 
 rewrite andp_assoc. apply andp_left2. rewrite insert_local; auto.
 rewrite andp_assoc; repeat rewrite insert_local.
 go_lowerx.
 apply andp_right; auto. apply prop_right.
 split3; auto.
 rewrite insert_local.
 go_lowerx. subst v. 
 apply andp_right; auto. apply prop_right.
 split; auto.
 apply andp_right; auto. apply prop_right.
 auto. 
Qed.

Lemma semax_while'_new1 : (* DELETE ME *)
 forall Espec {cs: compspecs} {A} (v: A -> val) Delta P Q R test body Post,
     bool_type (typeof test) = true ->
     (forall a, PROPx (P a) (LOCALx (tc_environ Delta :: Q a) (SEPx (R a))) |-- (tc_expr Delta (Eunop Cop.Onotbool test tint))) ->
     (forall a, PROPx (P a) (LOCALx (tc_environ Delta :: Q a) (SEPx (R a))) |-- local (`(eq (v a)) (eval_expr test))) ->
     (forall a, PROPx (typed_false (typeof test) (v a) :: (P a)) (LOCALx (tc_environ Delta :: (Q a)) (SEPx (R a))) 
                       |-- Post EK_normal None) ->
     (forall a, @semax cs Espec Delta (PROPx (typed_true (typeof test) (v a) :: (P a)) (LOCALx (Q a) (SEPx (R a))))
                 body (loop1_ret_assert (EX a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a)))) Post)) ->
     @semax cs Espec Delta (EX a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a)))) (Swhile test body) Post.
Proof.
intros.
apply semax_while; auto.
rewrite exp_andp2. apply exp_left; intro a.
eapply derives_trans; [ | apply H0].
normalize. 
normalize; autorewrite with norm1 norm2; normalize.
repeat rewrite exp_andp2. apply exp_left; intro a.
eapply derives_trans; [ | apply (H2 a)].
 apply derives_trans with (local (`(eq (v a)) (eval_expr test)) &&
     PROPx (P a)
      (LOCALx (tc_environ Delta :: `(typed_false (typeof test)) (eval_expr test) :: (Q a)) (SEPx (R a)))).
 apply andp_right. 
 rewrite (andp_comm (local (tc_environ _))). 
 rewrite andp_assoc. apply andp_left2. rewrite insert_local; auto.
 rewrite andp_assoc; repeat rewrite insert_local.
 go_lowerx.
 apply andp_right; auto. apply prop_right.
 split3; auto.
 rewrite insert_local.
 go_lowerx. rewrite H5 in *; clear H5.
 apply andp_right; auto. apply prop_right.
 split; auto.
 apply andp_right; auto. apply prop_right.
 split; auto.
 repeat rewrite exp_andp2. apply extract_exists_pre; intro a.
eapply semax_pre_simple; [ | apply (H3 a)]. clear - H1.
 rewrite <- andp_assoc.
 apply derives_trans with (local (`(eq (v a)) (eval_expr test)) &&
     PROPx (P a)
      (LOCALx (tc_environ Delta :: `(typed_true (typeof test)) (eval_expr test) :: (Q a)) (SEPx (R a)))).
 apply andp_right. 
 rewrite (andp_comm (local (tc_environ _))). 
 rewrite andp_assoc. apply andp_left2. rewrite insert_local; auto.
 rewrite andp_assoc; repeat rewrite insert_local.
 go_lowerx.
 apply andp_right; auto. apply prop_right.
 split3; auto.
 rewrite insert_local.
 go_lowerx.
 apply andp_right; auto. apply prop_right.
 split; auto. rewrite H0; auto.
 apply andp_right; auto. apply prop_right.
 auto. 
Qed.

Lemma semax_while' : (* DELETE ME *)
 forall Espec {cs: compspecs} Delta P Q R test body Post,
     bool_type (typeof test) = true ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--  (tc_expr Delta (Eunop Cop.Onotbool test tint)) ->
     PROPx P (LOCALx (tc_environ Delta :: `(typed_false (typeof test)) (eval_expr test) :: Q) (SEPx R)) |-- Post EK_normal None ->
     @semax cs Espec Delta (PROPx P (LOCALx (`(typed_true (typeof test)) (eval_expr test) :: Q) (SEPx R)))  body (loop1_ret_assert (PROPx P (LOCALx Q (SEPx R))) Post) ->
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) (Swhile test body) Post.
Proof.
intros.
apply semax_while; auto.
eapply derives_trans; [ | apply H0].
normalize; autorewrite with norm1 norm2; normalize.
eapply derives_trans; [ | apply H1].
 go_lowerx.
 apply andp_right; auto. apply prop_right; auto.
eapply semax_pre_simple; [ | apply H2].
 go_lowerx.  apply andp_right; auto. apply prop_right; auto.
Qed.

Lemma semax_for : 
 forall Espec {cs: compspecs} Delta Q test body incr PreIncr Post,
     bool_type (typeof test) = true ->
     local (tc_environ Delta) && Q |-- (tc_expr Delta (Eunop Cop.Onotbool test tint)) ->
     local (tc_environ Delta) 
      && local (`(typed_false (typeof test)) (eval_expr test)) 
      && Q |-- Post EK_normal None ->
     @semax cs Espec Delta (local (`(typed_true (typeof test)) (eval_expr test)) && Q)
             body (loop1_ret_assert PreIncr Post) ->
     @semax cs Espec Delta PreIncr incr (normal_ret_assert Q) ->
     @semax cs Espec Delta Q
       (Sloop (Ssequence (Sifthenelse test Sskip Sbreak) body) incr)
       Post.
Proof.
intros.
apply semax_loop with PreIncr.
eapply semax_seq.
apply semax_pre_simple with  ( (tc_expr Delta (Eunop Cop.Onotbool test tint)) && Q).
apply andp_right; auto.
apply andp_left2; auto.
apply semax_ifthenelse; auto.
eapply semax_post_flipped.
apply semax_skip.
intros.
unfold normal_ret_assert.
normalize. simpl exit_tycon.
unfold overridePost. rewrite if_true by auto. rewrite prop_true_andp by auto.
apply derives_refl.
eapply semax_pre_simple; [ | apply semax_break].
unfold overridePost. rewrite if_false by congruence.
unfold loop1_ret_assert.
eapply derives_trans; [ | apply H1].
rewrite andp_assoc.
apply andp_derives; auto.
rewrite andp_comm.
auto.
simpl update_tycon. 
apply semax_extensionality_Delta with Delta.
apply tycontext_eqv_sub.
apply tycontext_eqv_symm.
apply join_tycon_same.
eapply semax_pre_simple; [ | apply H2].
apply andp_left2.
apply andp_left2.
rewrite andp_comm. auto.
eapply semax_post_flipped. apply H3.
intros.
apply andp_left2.
unfold normal_ret_assert, loop2_ret_assert.
normalize.
Qed.

Lemma semax_for' : 
 forall Espec {cs: compspecs} Delta P Q R test body incr PreIncr Post,
     bool_type (typeof test) = true ->
     PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- (tc_expr Delta (Eunop Cop.Onotbool test tint)) ->
     PROPx P (LOCALx (tc_environ Delta :: `(typed_false (typeof test)) (eval_expr test) :: Q) (SEPx R)) |-- Post EK_normal None ->
     @semax cs Espec Delta (PROPx P (LOCALx (`(typed_true (typeof test)) (eval_expr test) :: Q) (SEPx R)))
             body (loop1_ret_assert PreIncr Post) ->
     @semax cs Espec Delta PreIncr incr (normal_ret_assert (PROPx P (LOCALx Q (SEPx R)))) ->
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) 
       (Sloop (Ssequence (Sifthenelse test Sskip Sbreak) body) incr)
       Post.
Proof.
intros.
apply semax_for with PreIncr; auto.
rewrite insert_local; auto.
rewrite andp_assoc; repeat rewrite insert_local; auto.
rewrite insert_local; auto.
Qed.

Lemma forward_setx_closed_now':
  forall Espec {cs: compspecs} Delta P (Q: list (environ -> Prop)) (R: list (environ->mpred)) id e,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
  closed_wrt_vars (eq id) (eval_expr e) ->
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- (tc_expr Delta e)  ->
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))  |-- (tc_temp_id id (typeof e) Delta e) ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) (Sset id e) 
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
  forall Espec {cs: compspecs} Delta (Q: list (environ -> Prop)) (R: list (environ->mpred)) id e PQR,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
  closed_wrt_vars (eq id) (eval_expr e) ->
  PROPx nil (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- (tc_expr Delta e)  ->
  PROPx nil (LOCALx (tc_environ Delta :: Q) (SEPx R))  |-- (tc_temp_id id (typeof e) Delta e) ->
  normal_ret_assert (PROPx nil (LOCALx (`eq (eval_id id) (eval_expr e)::Q) (SEPx R))) |-- PQR ->
  @semax cs Espec Delta (PROPx nil (LOCALx Q (SEPx R))) (Sset id e) PQR.
Proof.
intros.
eapply semax_post.
intros ek vl. apply andp_left2. apply H4.
apply forward_setx_closed_now'; auto.
Qed.


Lemma forward_ptr_compare_closed_now :
forall Espec {cs: compspecs} Delta P Q R id e1 e2 cmp ty sh1 sh2 PQR
(TID : typecheck_tid_ptr_compare Delta id = true), 
 sepalg.nonidentity sh1 ->
 sepalg.nonidentity sh2 ->
Forall (closed_wrt_vars (eq id)) Q ->
Forall (closed_wrt_vars (eq id)) R ->
closed_wrt_vars (eq id) (eval_expr ((Ebinop cmp e1 e2 ty))) ->
( PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- (tc_expr Delta (Ebinop cmp e1 e2 ty))  /\
  PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))  |-- (tc_temp_id id (ty) Delta (Ebinop cmp e1 e2 ty)))
\/
PROPx P (LOCALx ((tc_environ Delta)::Q) (SEPx R)) |-- ((tc_expr Delta e1) && (tc_expr Delta e2) &&
      local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
      (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
      (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT)) ->
((normal_ret_assert
     (PROPx P (LOCALx (`eq (eval_id id) 
                     (eval_expr ((Ebinop cmp e1 e2 ty))) :: Q)
          (SEPx  R))))) |-- PQR ->
is_comparison cmp = true ->
@semax cs Espec Delta
  (PROPx P (LOCALx Q (SEPx R))) (Sset id (Ebinop cmp e1 e2 ty)) PQR
  .
Proof. 
intros until 1. intros N1 N2. intros.
intuition.
eapply semax_post; [ | apply forward_setx_closed_now'; auto with closed].
intros.  intro rho. normalize.
autorewrite with subst norm1 norm2; normalize.
 apply H3.

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
  forall Espec {cs: compspecs} Delta (Q: list (environ -> Prop)) (R: list (environ->mpred)) id e c PQR,
  Forall (closed_wrt_vars (eq id)) Q ->
  Forall (closed_wrt_vars (eq id)) R ->
  closed_wrt_vars (eq id) (eval_expr e) ->
  PROPx nil (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- (tc_expr Delta e)  ->
  PROPx nil (LOCALx (tc_environ Delta :: Q) (SEPx R))  |-- (tc_temp_id id (typeof e) Delta e) ->
  semax (update_tycon Delta (Sset id e))
           (PROPx nil (LOCALx (`eq (eval_id id) (eval_expr e)::Q) (SEPx R))) c PQR ->
  @semax cs Espec Delta (PROPx nil (LOCALx Q (SEPx R))) (Ssequence (Sset id e) c) PQR.
Proof.
 intros.
 eapply semax_seq.
 apply sequential'.
 apply forward_setx_closed_now; auto.
 apply H4.
Qed.

(*
Lemma field_at_mapsto__at1:
  forall Espec Delta P Q sh ty fld e v R c Post,
    @semax Espec Delta (PROPx P (LOCALx Q (SEPx (`(field_at_ sh ty fld) e :: R)))) c Post ->
    @semax Espec Delta (PROPx P (LOCALx Q (SEPx (`(field_at sh ty fld) v e :: R)))) c Post.
Proof.
intros.
 eapply semax_pre0; [ | apply H].
 intro rho; unfold PROPx, LOCALx, SEPx.
 simpl.
 apply andp_derives; auto.
 apply andp_derives; auto.
 apply sepcon_derives; auto.
 unfold_lift; apply field_at_field_at_.
Qed.

Lemma later_field_at_mapsto__at1:
  forall Espec Delta P Q sh ty fld e v R c Post,
    @semax Espec Delta (PROPx P (LOCALx Q (SEPx (|>`(field_at_ sh ty fld) e :: R)))) c Post ->
    @semax Espec Delta (PROPx P (LOCALx Q (SEPx (|> `(field_at sh ty fld) v e :: R)))) c Post.
Proof.
intros.
 eapply semax_pre0; [ | apply H].
 intro rho; unfold PROPx, LOCALx, SEPx.
 simpl.
 apply andp_derives; auto.
 apply andp_derives; auto.
 apply sepcon_derives; auto.
 apply later_derives; auto.
 unfold_lift; apply field_at_field_at_.
Qed.
*)

Lemma forward_setx':
  forall Espec {cs: compspecs} Delta P id e,
  (P |-- (tc_expr Delta e) && (tc_temp_id id (typeof e) Delta e) ) ->
  @semax cs Espec Delta
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
  forall Espec {cs: compspecs} Delta P Q R id e,
  (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- (tc_expr Delta e) && (tc_temp_id id (typeof e) Delta e) ) ->
  @semax cs Espec Delta
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
 rewrite <- (andp_dup (PROPx _ (LOCALx (_ :: Q) _))) at 1.
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
  forall Espec {cs: compspecs} Delta P Q R id e,
  (PROPx P (LOCALx Q (SEPx R)) |-- (tc_expr Delta e) && (tc_temp_id id (typeof e) Delta e) ) ->
  @semax cs Espec Delta
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
forall Espec {cs: compspecs} Delta P id e1 e2 sh1 sh2 cmp ty, 
  sepalg.nonidentity sh1 ->
  sepalg.nonidentity sh2 ->
P |-- ((tc_expr Delta e1) && (tc_expr Delta e2) &&
      local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
      (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
      (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT)) ->
is_comparison cmp = true ->
typecheck_tid_ptr_compare Delta id = true ->
@semax cs Espec Delta
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
forall {Espec: OracleKind}{cs: compspecs} ,
forall (Delta: tycontext) P Q R id cmp e1 e2 ty sh1 sh2 PQR,
  sepalg.nonidentity sh1 ->
  sepalg.nonidentity sh2 ->
    is_comparison cmp = true  ->
    typecheck_tid_ptr_compare Delta id = true ->
    (PROPx P (LOCALx Q (SEPx R)) |-- 
           (tc_expr Delta (Ebinop cmp e1 e2 ty)) && 
           (tc_temp_id id ty Delta 
                             (Ebinop cmp e1 e2 ty))) \/
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
         |-- (tc_expr Delta e1) &&
             (tc_expr Delta e2)  && 
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
   @semax cs Espec Delta 
         (PROPx P (LOCALx Q (SEPx R)))
          (Sset id (Ebinop cmp e1 e2 ty)) PQR
        .
Proof.
intros until 0. intros N1 N2. intros.
intuition.
eapply semax_post.
intros ek vl rho. simpl. apply andp_left2.
apply H2. 
apply forward_setx_weak; auto.

eapply semax_post. intros ek vl rho.
simpl. apply andp_left2. apply H2.
eapply semax_pre_post; [ | | apply (semax_ptr_compare Delta (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))) _ _ _ _ _ sh1 sh2); auto].
eapply derives_trans; [ | apply now_later].
rewrite insert_local; apply andp_right; auto.
intros ek vl. unfold normal_ret_assert.
repeat rewrite exp_andp2. apply exp_derives; intro x.
autorewrite with subst.
go_lowerx. repeat apply andp_right; try apply prop_right; auto.
Qed.


Lemma forward_ptr_compare:
forall Espec {cs: compspecs} Delta P Q R id e1 e2 sh1 sh2 cmp ty, 
  sepalg.nonidentity sh1 ->
  sepalg.nonidentity sh2 ->
PROPx P (LOCALx Q (SEPx R)) |-- ((tc_expr Delta e1) && (tc_expr Delta e2) &&
      local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
      (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
      (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT)) ->
is_comparison cmp = true ->
typecheck_tid_ptr_compare Delta id = true ->
@semax cs Espec Delta
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
  forall Espec {cs: compspecs} Delta P Q R c Post,
  @semax cs Espec Delta (PROPx P (LOCALx Q R)) c Post ->
  @semax cs Espec Delta (PROPx P (LOCALx (tc_environ Delta:: Q) R)) c Post.
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

Transparent tc_andp.  (* ? should leave it opaque, maybe? *)

(*
Lemma semax_logical_or:
 forall Espec Delta P Q R tid e1 e2 b
   (CLOSQ : Forall (closed_wrt_vars (eq tid)) Q)
   (CLOSR : Forall (closed_wrt_vars (eq tid)) R)
   (CLOSE1 : closed_eval_expr tid e1 = true)
   (CLOSE2 : closed_eval_expr tid e2 = true),
 bool_type (typeof e1) = true ->
 bool_type (typeof e2) = true ->
 (temp_types Delta) ! tid = Some (tint, b) ->
  @semax Espec Delta (PROPx P (LOCALx ((tc_expr Delta e1)::
              (`or (`(typed_true (typeof e1)) (eval_expr Delta e1))  (tc_expr Delta e2))::
              tc_temp_id tid tbool Delta (Ecast e2 tbool) ::
   Q) (SEPx (R))))
    (logical_or tid e1 e2)
  (normal_ret_assert (PROPx P (LOCALx 
((`eq (eval_id tid) 
   (`logical_or_result 
          `(typeof e1) (eval_expr Delta e1) `(typeof e2) (eval_expr Delta e2)))::Q) (SEPx (R))))). 
Proof.
intros.
assert (CLOSE1' := closed_eval_expr_e Delta _ _ CLOSE1).
assert (CLOSE2' := closed_eval_expr_e Delta _ _ CLOSE2).
apply semax_ifthenelse_PQR. 
  - auto.
  - rewrite <- insert_local; apply andp_left2. 
    rewrite <- insert_local; apply andp_left1. auto.
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
  rewrite (closed_wrt_subst _ _ (tc_expr Delta e1)) by auto with closed.
  rewrite (closed_wrt_subst _ _ (tc_expr Delta e2)) by auto with closed.
   go_lowerx. subst. apply andp_right; auto. apply prop_right; split; auto.
   rewrite H6.
   unfold logical_or_result.
 destruct (typeof e1) as [ | | | [ | ] |  | | | | ], (eval_expr Delta e1 rho); inv H; inv H8; simpl;
   try rewrite H3; auto.
  - eapply semax_seq'. 
      + eapply forward_setx_weak.
         go_lowerx. 
         destruct H5. congruence.
         apply andp_right; apply prop_right; auto.
        unfold tc_expr. simpl. rewrite tc_andp_sound.
        simpl. super_unfold_lift. split. auto. 
         destruct (typeof e2) as [ | | | [ | ] |  | | | | ] eqn:?;
                                        inv H0; try  apply I.
      + simpl update_tycon. apply extract_exists_pre. intro oldval.
          rewrite (@closed_wrt_subst _ tid _ (eval_expr Delta (Ecast e2 tbool)))
    by (simpl; auto with closed).
    rewrite (closed_wrt_map_subst _ _ R) by auto.
   repeat rewrite map_cons. 
   rewrite closed_wrt_subst by auto with closed.
   rewrite closed_wrt_subst by auto with closed.
    rewrite (closed_wrt_map_subst _ _ Q) by auto.
    unfold tc_temp_id.
   unfold typecheck_temp_id. rewrite H1.  simpl denote_tc_assert.
   autorewrite with subst.
   repeat apply andp_right; auto.
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
       go_lowerx. apply andp_right; auto. apply prop_right; split; auto.
       rewrite H6. rewrite H7. 
        unfold logical_or_result. rewrite H8.
        subst ek vl. simpl in  H2.
       apply bool_cast. destruct H10. congruence.
      eapply expr_lemmas.typecheck_expr_sound.
      apply tc_environ_init in H2.
      apply tc_environ_init in H2.
      apply H2.
      apply H3.
Qed.

Lemma semax_logical_and:
 forall Espec Delta P Q R tid e1 e2 b
   (CLOSQ : Forall (closed_wrt_vars (eq tid)) Q)
   (CLOSR : Forall (closed_wrt_vars (eq tid)) R)
   (CLOSE1 : closed_eval_expr tid e1 = true)
   (CLOSE2 : closed_eval_expr tid e2 = true),
 bool_type (typeof e1) = true ->
 bool_type (typeof e2) = true ->
 (temp_types Delta) ! tid = Some (tint, b) ->
  @semax Espec Delta (PROPx P (LOCALx ((tc_expr Delta e1)::
    (`or (`(typed_false (typeof e1)) (eval_expr Delta e1))  (tc_expr Delta e2))::tc_temp_id tid tbool Delta (Ecast e2 tbool) ::
   Q) (SEPx (R))))
    (logical_and tid e1 e2)
  (normal_ret_assert (PROPx P (LOCALx 
((`eq (eval_id tid) 
   (`logical_and_result 
          `(typeof e1) (eval_expr Delta e1) `(typeof e2) (eval_expr Delta e2)))::Q) (SEPx (R)))))
  . 
Proof.
intros.
assert (CLOSE1' := closed_eval_expr_e Delta _ _ CLOSE1).
assert (CLOSE2' := closed_eval_expr_e Delta _ _ CLOSE2).
apply semax_ifthenelse_PQR. 
  - auto. 
  - rewrite <- insert_local; apply andp_left2. 
    rewrite <- insert_local; apply andp_left1. auto.
  - eapply semax_seq'. 
      + eapply forward_setx_weak.
         go_lowerx. apply andp_right; apply prop_right; auto.
        unfold tc_expr. simpl. rewrite tc_andp_sound.
        simpl. super_unfold_lift. split.
        destruct H5; auto; congruence.         
        unfold isCastResultType. destruct (typeof e2) as [ | | | [ | ] |  | | | | ]; 
                                        inv H0; simpl; apply I.
      + simpl update_tycon. apply extract_exists_pre. intro oldval.
          rewrite (@closed_wrt_subst _ tid _ (eval_expr Delta (Ecast e2 tbool)))
    by (simpl; auto with closed).
  autorewrite with subst.
    unfold tc_temp_id.
   unfold typecheck_temp_id. rewrite H1.  simpl denote_tc_assert.
   autorewrite with subst.
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
       go_lowerx. apply andp_right; auto. apply prop_right; split; auto.
       rewrite H6. rewrite H7.
        unfold logical_and_result.
        subst ek vl. simpl in  H2.
        rewrite H8.
       apply bool_cast.  destruct H10. congruence.
      eapply expr_lemmas.typecheck_expr_sound.
      apply tc_environ_init in H2.
      apply tc_environ_init in H2.
      apply H2. auto.
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
   (CLOSE1 : closed_eval_expr tid e1 = true)
   (CLOSE2 : closed_eval_expr tid e2 = true),
 bool_type (typeof e1) = true ->
 bool_type (typeof e2) = true ->
 (temp_types Delta) ! tid = Some (tint, b) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta e1) &&
         (local (`(typed_false (typeof e1)) (eval_expr Delta e1)) || local (tc_expr Delta e2)) && local (tc_temp_id tid tbool Delta (Ecast e2 tbool)) ->
  (normal_ret_assert (PROPx P (LOCALx ((`eq (eval_id tid) (`logical_and_result 
          `(typeof e1) (eval_expr Delta e1) `(typeof e2) (eval_expr Delta e2)))::Q) (SEPx (R))))) |-- PQR ->   
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
   (CLOSE1 : closed_eval_expr tid e1 = true)
   (CLOSE2 : closed_eval_expr tid e2 = true),
 bool_type (typeof e1) = true ->
 bool_type (typeof e2) = true ->
 (temp_types Delta) ! tid = Some (tint, b) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta e1) &&
        (local (`(typed_true (typeof e1)) (eval_expr Delta e1)) || local (tc_expr Delta e2)) && local (tc_temp_id tid tbool Delta (Ecast e2 tbool)) ->
  (normal_ret_assert (PROPx P (LOCALx ((`eq (eval_id tid) (`logical_or_result 
          `(typeof e1) (eval_expr Delta e1) `(typeof e2) (eval_expr Delta e2)))::Q) (SEPx (R))))) |-- PQR ->   
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
*)