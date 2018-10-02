Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Import Cop.
Local Open Scope logic.

Lemma semax_func_cons_ext_vacuous:
     forall {Espec: OracleKind} (V : varspecs) (G : funspecs) (C : compspecs)
         (fs : list (ident * Clight.fundef)) (id : ident) (ef : external_function)
         (argsig : typelist) (retsig : type)
         (G' : funspecs) cc,
       (id_in_list id (map fst fs)) = false ->
       ef_sig ef =
       {|
         sig_args := typlist_of_typelist (type_of_params (arglist 1 argsig));
         sig_res := opttyp_of_type retsig;
         sig_cc := cc_of_fundef (External ef argsig retsig cc) |} ->
       semax_func V G fs G' ->
       semax_func V G ((id, External ef argsig retsig cc) :: fs)
         ((id, vacuous_funspec (External ef argsig retsig cc)) :: G').
Proof.
intros.
eapply semax_func_cons_ext; try reflexivity; auto.
*
 clear.
 forget 1%positive as i.
 revert i; induction argsig; simpl; intros; auto.
 f_equal; auto.
*
  forget 1%positive as i.
  clear.
  revert i; induction argsig; simpl; intros; auto.
*
  intros. simpl. apply andp_left1, FF_left.
*
  apply semax_external_FF.
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
rewrite <- (Int.signed_repr i) by rep_omega.
rewrite <- (Int.signed_repr j) by rep_omega.
congruence.
Qed.

Lemma repr_inj_unsigned:
  forall i j,
    0 <= i <= Int.max_unsigned ->
    0 <= j <= Int.max_unsigned ->
    Int.repr i = Int.repr j -> i=j.
Proof.
intros.
rewrite <- (Int.unsigned_repr i) by rep_omega.
rewrite <- (Int.unsigned_repr j) by rep_omega.
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
     ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_expr Delta (Eunop Cop.Onotbool b tint))  ->
     ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
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
 instantiate (1:=(local (`(eq v) (eval_expr b)) && PROPx P (LOCALx Q (SEPx R)))).
 apply andp_right; try assumption. apply andp_right; try assumption.
 apply andp_left2; auto.
 eapply semax_pre; [ | eassumption].
 rewrite <- insert_prop.
 forget ( PROPx P (LOCALx Q (SEPx R))) as PQR.
 go_lowerx. normalize. apply andp_right; auto.
 subst; apply prop_right; repeat split; auto.
 eapply semax_pre; [ | eassumption].
 rewrite <- insert_prop.
 forget ( PROPx P (LOCALx Q (SEPx R))) as PQR.
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
         (Delta : tycontext) (P1 : list Prop) (P2 : list localdef)
         (P3 : list mpred) (c : statement)
         (R : ret_assert),
       semax Delta P' c R ->
       ENTAIL Delta, PROPx P1 (LOCALx P2 (SEPx P3)) |-- P' ->
        semax Delta (PROPx P1 (LOCALx P2 (SEPx P3))) c R.
Proof. intros.
eapply semax_pre. apply H0. auto.
Qed.

Lemma semax_while :
 forall Espec {cs: compspecs} Delta Q test body (R: ret_assert),
     bool_type (typeof test) = true ->
     (local (tc_environ Delta) && Q |--  (tc_expr Delta (Eunop Cop.Onotbool test tint))) ->
     (local (tc_environ Delta) && local (lift1 (typed_false (typeof test)) (eval_expr test)) && Q |-- RA_normal R) ->
     @semax cs Espec Delta (local (`(typed_true (typeof test)) (eval_expr test)) && Q)  body (loop1_ret_assert Q R) ->
     @semax cs Espec Delta Q (Swhile test body) R.
Proof.
intros ? ? ? ? ? ? ? BT TC Post H.
unfold Swhile.
apply (@semax_loop cs Espec Delta Q Q).
2:{
 clear. eapply semax_post_flipped. apply semax_skip.
 all: try (intros; apply andp_left2; destruct R; apply derives_refl).
 intros. apply andp_left2. destruct R; simpl. normalize.
 intros. apply andp_left2. destruct R; simpl. normalize.
} 
apply semax_seq with
 (local (`(typed_true (typeof test)) (eval_expr test)) && Q).
apply semax_pre_simple with ( (tc_expr Delta (Eunop Cop.Onotbool test tint)) && Q).
apply andp_right. apply TC.
apply andp_left2.
intro; auto.
clear H.
apply semax_ifthenelse; auto.
eapply semax_post_flipped. apply semax_skip.
destruct R as [?R ?R ?R ?R].
simpl RA_normal in *. apply andp_left2. intro rho; simpl. rewrite andp_comm. auto.
all: try (intro rho; simpl; normalize).
eapply semax_pre_simple; [ | apply semax_break].
rewrite (andp_comm Q).
rewrite <- andp_assoc.
eapply derives_trans; try apply Post.
destruct R; simpl; auto.
auto.
Qed.

Lemma semax_while_3g1 :
 forall Espec {cs: compspecs} {A} (v: A -> val) Delta P Q R test body Post,
     bool_type (typeof test) = true ->
     (forall a, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) |-- (tc_expr Delta (Eunop Cop.Onotbool test tint))) ->
     (forall a, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) |-- local (`(eq (v a)) (eval_expr test))) ->
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
 apply derives_refl.
*
repeat rewrite exp_andp2. apply exp_left; intro a.
rewrite overridePost_normal'.
apply exp_right with a.
eapply derives_trans.
apply andp_right; [ | apply derives_refl].
eapply derives_trans; [ | apply (H1 a)].
rewrite (andp_comm (local _)).
rewrite andp_assoc. apply andp_left2. auto.
go_lowerx; normalize.
repeat apply andp_right; auto. apply prop_right; split; auto.
rewrite H3; auto.
*
 repeat rewrite exp_andp2.
 apply extract_exists_pre; intro a.
 eapply semax_pre_post; try apply (H2 a).
 +
 rewrite <- andp_assoc.
 rewrite <- insert_prop.
 apply andp_right; [ | apply andp_left2; auto].
 rewrite (andp_comm (local _)). rewrite andp_assoc.
 eapply derives_trans.
 apply andp_right; [ | apply derives_refl].
 apply andp_left2; apply (H1 a).
 rewrite <- andp_assoc.
 apply andp_left1.
 go_lowerx. intro; apply prop_right. rewrite H3; auto.
 + apply andp_left2. destruct Post; simpl; auto.
 + apply andp_left2. destruct Post; simpl; auto.
 + apply andp_left2. destruct Post; simpl; auto.
 + intros; apply andp_left2. destruct Post; simpl; auto.
Qed.

Lemma semax_for_x :
 forall Espec {cs: compspecs} Delta Q test body incr PreIncr Post,
     bool_type (typeof test) = true ->
     local (tc_environ Delta) && Q |-- (tc_expr Delta (Eunop Cop.Onotbool test tint)) ->
     local (tc_environ Delta)
      && local (`(typed_false (typeof test)) (eval_expr test))
      && Q |-- RA_normal Post ->
     @semax cs Espec Delta (local (`(typed_true (typeof test)) (eval_expr test)) && Q)
             body (loop1_ret_assert PreIncr Post) ->
     @semax cs Espec Delta PreIncr incr (normal_ret_assert Q) ->
     @semax cs Espec Delta Q
       (Sloop (Ssequence (Sifthenelse test Sskip Sbreak) body) incr)
       Post.
Proof.
intros.
apply semax_loop with PreIncr.
apply semax_seq with (local (tc_environ Delta) &&
   (Q && local (` (typed_true (typeof test)) (eval_expr test)))) .
apply semax_pre_simple with  ( (tc_expr Delta (Eunop Cop.Onotbool test tint)) && Q).
apply andp_right; auto.
apply andp_left2; auto.
apply semax_ifthenelse; auto.
*
eapply semax_post_flipped; [ apply semax_skip | .. ].
intro rho; destruct Post as [?P ?P ?P ?P]; simpl; normalize.
intro rho; destruct Post as [?P ?P ?P ?P]; simpl; normalize.
intro rho; destruct Post as [?P ?P ?P ?P]; simpl; normalize.
intros vl rho; destruct Post as [?P ?P ?P ?P]; simpl; normalize.
*
eapply semax_pre_simple; [ | apply semax_break].
intro rho; destruct Post as [?P ?P ?P ?P]; simpl; normalize.
eapply derives_trans; [ | apply (H1 rho)].
rewrite (andp_comm (Q rho)).
simpl.
rewrite andp_assoc.
auto.
*
eapply semax_pre_simple; [ | apply H2].
apply andp_left2.
apply andp_left2.
rewrite andp_comm. auto.
*
eapply semax_post_flipped. apply H3.
apply andp_left2; intro rho; destruct Post as [?P ?P ?P ?P]; simpl; auto.
apply andp_left2; intro rho; destruct Post as [?P ?P ?P ?P]; simpl; auto.
normalize.
apply andp_left2; intro rho; destruct Post as [?P ?P ?P ?P]; simpl; auto.
intro; apply andp_left2; intro rho; destruct Post as [?P ?P ?P ?P]; simpl; auto.
normalize.
Qed.

Lemma semax_for :
 forall Espec {cs: compspecs} {A:Type} (v: A -> val) Delta P Q R test body incr PreIncr Post,
     bool_type (typeof test) = true ->
     (forall a:A, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a)))
           |-- tc_expr Delta (Eunop Cop.Onotbool test tint)) ->
     (forall a:A, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) |--  local (`(eq (v a)) (eval_expr test))) ->
     (forall a:A,
        @semax cs Espec Delta (PROPx (typed_true (typeof test) (v a) :: P a) (LOCALx (Q a) (SEPx (R a))))
             body (loop1_ret_assert (PreIncr a) Post)) ->
     (forall a, @semax cs Espec Delta (PreIncr a) incr (normal_ret_assert (PROPx (P a) (LOCALx (Q a) (SEPx (R a)))))) ->
     (forall a:A, ENTAIL Delta, PROPx (typed_false (typeof test) (v a) :: P a) (LOCALx (Q a) (SEPx (R a)))
          |-- RA_normal Post) ->
     @semax cs Espec Delta (EX a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a))))
       (Sloop (Ssequence (Sifthenelse test Sskip Sbreak) body) incr)
       Post.
Proof.
intros.
apply semax_for_x with (EX a:A, PreIncr a); auto.
normalize.
normalize.
eapply derives_trans; [ | apply (H4 a)].
clear - H4 H1.
eapply derives_trans; [ | eapply derives_trans; [ eapply andp_derives | ]].
apply andp_right.
rewrite (andp_comm (local (tc_environ _))).
rewrite andp_assoc. apply andp_left2.
apply H1. apply derives_refl. apply derives_refl. apply derives_refl.
rewrite <- insert_prop.
rewrite <- !andp_assoc.
apply andp_derives; auto.
intro rho; unfold local, lift1; unfold_lift. simpl.
normalize. split; auto. rewrite H0; auto.
normalize.
apply extract_exists_pre; intro a.
eapply semax_pre_post; try apply (H2 a).
rewrite <- insert_prop.
eapply derives_trans; [ | eapply derives_trans].
eapply andp_right; [ | apply derives_refl].
eapply derives_trans; [ | apply (H1 a)].
apply andp_derives; auto.
apply andp_left2; auto.
apply derives_refl.
rewrite <- !andp_assoc.
apply andp_derives; auto.
intro rho; unfold local, lift1; unfold_lift. simpl.
normalize. rewrite H6; auto.
intros.
apply andp_left2.
unfold loop1_ret_assert.
destruct Post as [?P ?P ?P ?P]; apply exp_right with a; apply derives_refl.
destruct Post as [?P ?P ?P ?P]; apply andp_left2; apply derives_refl.
destruct Post as [?P ?P ?P ?P]; apply exp_right with a; apply andp_left2; simpl; auto.
intros vl; destruct Post as [?P ?P ?P ?P]; apply andp_left2; apply derives_refl.
apply extract_exists_pre; intro a.
eapply semax_post'; try apply (H3 a).
apply exp_right with a; auto.
apply andp_left2; auto.
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
eapply semax_pre; try apply (semax_set_forward Delta P id e).
+ eapply derives_trans ; [ | apply now_later].
   apply andp_left2; apply andp_right; auto.
Qed.

(*
Lemma forward_setx:
  forall Espec {cs: compspecs} Delta P Q R id e,
  (PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R)) |-- (tc_expr Delta e) && (tc_temp_id id (typeof e) Delta e) ) ->
  @semax cs Espec Delta
             (PROPx P (LOCALx Q (SEPx R)))
             (Sset id e)
             (normal_ret_assert
                  (EX old:val,
                    PROPx P
                     (LOCALx (`eq (eval_id id) (subst id (`old) (eval_expr e)) ::
                                     map (subst id (`old)) Q)
                      (SEPx R)))).
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
*)

Lemma semax_switch_PQR: 
  forall {Espec: OracleKind}{CS: compspecs} ,
  forall n Delta (Pre: environ->mpred) a sl (Post: ret_assert),
     is_int_type (typeof a) = true ->
     ENTAIL Delta, Pre |-- tc_expr Delta a ->
     ENTAIL Delta, Pre |-- local (`(eq (Vint (Int.repr n))) (eval_expr a)) ->
     @semax CS Espec Delta 
               Pre
               (seq_of_labeled_statement (select_switch (Int.unsigned (Int.repr n)) sl))
               (switch_ret_assert Post) ->
     @semax CS Espec Delta Pre (Sswitch a sl) Post.
Proof.
intros.
eapply semax_pre.
apply derives_refl.
apply (semax_switch); auto.
intro n'.
assert_PROP (n' = Int.repr n). {
apply derives_trans with (local (`( eq (Vint (Int.repr n))) (eval_expr a)) && local (` eq (eval_expr a) `(Vint n'))).
apply andp_right.
eapply derives_trans; [ | eassumption].
intro rho.
unfold local, lift1, liftx, lift; simpl.
normalize.
intro rho.
unfold local, lift1, liftx, lift; simpl.
normalize.
intro rho.
unfold local, lift1, liftx, lift; simpl.
normalize.
rewrite <- H3 in H4.
apply Vint_inj in H4.
auto.
}
subst n'.
eapply semax_pre; [ | eassumption].
apply andp_left2.
apply andp_left2.
apply andp_left2.
auto.
Qed.

Lemma modulo_samerepr:
 forall x y, 
  Z.modulo x Int.modulus = Z.modulo y Int.modulus -> 
  Int.repr x = Int.repr y.
Proof.
intros.
apply Int.eqm_samerepr.
apply Zmod_divide_minus in H; [ | reflexivity].
unfold Int.eqm.
unfold Int.eqmod.
set (m := Int.modulus) in *.
destruct H as [z ?].
assert (x = y mod m + z * m) by omega.
clear H. subst x.
pose proof (Z.div_mod y m).
spec H. intro Hx; inv Hx.
evar (k: Z).
exists k.
rewrite H at 2; clear H.
rewrite (Z.mul_comm m).
assert (z * m = k*m + (y/m*m))%Z; [ | omega].
rewrite <- Z.mul_add_distr_r.
f_equal.
assert (k = z - y/m); [ | omega].
subst k.
reflexivity.
Qed.

Lemma select_switch_case_signed:
 forall y n x c sl,
 Z.modulo x Int.modulus = Z.modulo y Int.modulus ->
 0 <= x < Int.modulus ->
 select_switch_case n (LScons (Some x) c sl) = 
 if zeq (Int.unsigned (Int.repr y)) n then Some (LScons (Some x) c sl)
 else select_switch_case n sl.
Proof.
intros.
simpl.
apply modulo_samerepr in H.
rewrite <- H.
rewrite Int.unsigned_repr by rep_omega.
auto.
Qed.

Definition signof (e: expr) := 
  match typeof e with
  | Tint _ s _ => s
  | Tlong s _ => s 
  | _ =>  Unsigned
  end.

Definition adjust_for_sign (s: signedness) (x: Z) :=
 match s with
 | Unsigned => x 
 | Signed => if (zlt x Int.half_modulus) then x else x - Int.modulus 
 end.

(*
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
*)

(*
Lemma elim_redundant_Delta:
  forall Espec {cs: compspecs} Delta P Q R c Post,
  @semax cs Espec Delta (PROPx P (LOCALx Q R)) c Post ->
  @semax cs Espec Delta (PROPx P (LOCALx (tc_env Delta:: Q) R)) c Post.
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
*)

Lemma semax_for_3g1 :
 forall Espec {cs: compspecs} {A} (PQR: A -> environ -> mpred) (v: A -> val) Delta P Q R test body incr Post,
     bool_type (typeof test) = true ->
     (forall a, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) |-- (tc_expr Delta (Eunop Cop.Onotbool test tint))) ->
     (forall a, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) |-- local (`(eq (v a)) (eval_expr test))) ->
     (forall a, @semax cs Espec Delta (PROPx (typed_true (typeof test) (v a) :: (P a)) (LOCALx (Q a) (SEPx (R a))))
                 body (loop1_ret_assert (EX a:A, PQR a) Post)) ->
     (forall a, @semax cs Espec Delta (PQR a) incr
                         (normal_ret_assert (EX a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a)))))) ->
     (forall a, ENTAIL Delta, PROPx (typed_false (typeof test) (v a) :: (P a)) (LOCALx (Q a) (SEPx (R a))) 
                             |-- RA_normal Post) ->
     @semax cs Espec Delta (EX a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a))))
                 (Sloop (Ssequence (Sifthenelse test Sskip Sbreak)  body) incr)
                 Post.
Proof.
intros.
apply semax_loop with (Q':= (EX a:A, PQR a)).
*
 apply extract_exists_pre; intro a.
 apply semax_seq with (Q0 := PROPx (typed_true (typeof test) (v a) :: P a) (LOCALx (Q a) (SEPx (R a)))).
 apply semax_pre with (tc_expr Delta (Eunop Onotbool test (Tint I32 Signed noattr)) 
                                        && (local (`(eq (v a)) (eval_expr test)) && (PROPx (P a) (LOCALx (Q a) (SEPx (R a))))));
   [ | apply semax_ifthenelse; auto].
 apply andp_right; auto.
 apply andp_right; auto.
 apply andp_left2; auto.
 apply sequential.
 eapply semax_post_flipped; [apply semax_skip | | | | ].
+
 apply andp_left2.
 destruct Post; simpl_ret_assert.
 clear.
 rewrite <- insert_prop.
 forget (PROPx (P a) (LOCALx (Q a) (SEPx (R a)))) as PQR.
 intro rho.  simpl. unfold_lift.  unfold local, lift1. normalize.
 rewrite H0. normalize.
+
 destruct Post; simpl_ret_assert. apply andp_left2; auto.
+
 destruct Post; simpl_ret_assert. apply andp_left2; auto.
+
 intros; destruct Post; simpl_ret_assert. apply andp_left2; auto.
+
 eapply semax_pre; [ | apply semax_break].
 autorewrite with ret_assert.
 eapply derives_trans; [ | apply (H4 a)]. clear.
 apply andp_derives; auto.
 rewrite <- insert_prop.
 clear.
 forget (PROPx (P a) (LOCALx (Q a) (SEPx (R a)))) as PQR.
 intro rho.  simpl. unfold_lift.  unfold local, lift1. normalize.
 rewrite H0. normalize.
+
 eapply semax_post_flipped.
 apply H2.
 all: intros; apply andp_left2; auto.
*
 make_sequential.
 Intros a.
 eapply semax_post_flipped. apply (H3 a).
 all: intros; destruct Post; simpl_ret_assert; apply andp_left2; auto.
Qed.

(*
Definition mk_ret_assert (n b c : environ -> mpred) (r: option val -> environ -> mpred) : ret_assert :=
    fun (ek : exitkind) (vl : option val) =>
 match ek with
 | EK_normal => !! (vl=None) && n
 | EK_break => !! (vl=None) && b
 | EK_continue => !! (vl=None) && c
 | EK_return => r vl
 end.
*)

Lemma semax_for_3g2:  (* no break statements in loop *)
 forall Espec {cs: compspecs} {A} (PQR: A -> environ -> mpred) (v: A -> val) Delta P Q R test body incr Post,
     bool_type (typeof test) = true ->
     (forall a, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) |-- (tc_expr Delta (Eunop Cop.Onotbool test tint))) ->
     (forall a, ENTAIL Delta, PROPx (P a) (LOCALx (Q a) (SEPx (R a))) |-- local (`(eq (v a)) (eval_expr test))) ->
     (forall a, @semax cs Espec Delta (PROPx (typed_true (typeof test) (v a) :: (P a)) (LOCALx (Q a) (SEPx (R a))))
                 body (loop1x_ret_assert (EX a:A, PQR a) Post)) ->
     (forall a, @semax cs Espec Delta (PQR a) incr
                         (normal_ret_assert (EX a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a)))))) ->
     @semax cs Espec Delta (EX a:A, PROPx (P a) (LOCALx (Q a) (SEPx (R a))))
                 (Sloop (Ssequence (Sifthenelse test Sskip Sbreak)  body) incr)
                 (overridePost
                      (EX a:A, PROPx (typed_false (typeof test) (v a) :: (P a)) (LOCALx (Q a) (SEPx (R a))))
                  Post).
Proof.
intros.
eapply semax_for_3g1; try eassumption.
*
 intro a.  eapply semax_post_flipped. apply H2.
 all: intros; destruct Post; simpl_ret_assert; apply andp_left2; auto.
 apply FF_left.
*
 intro a.
 apply andp_left2. destruct Post; simpl_ret_assert. Exists a. auto.
Qed.

Transparent tc_andp.  (* ? should leave it opaque, maybe? *)

(*

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
                      (SEPx R)))).
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
    apply Coq.Init.Logic.I.   unfold tc_temp_id, typecheck_temp_id. rewrite H1.
     simpl. apply Coq.Init.Logic.I.
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
                                        inv H0; try  apply Coq.Init.Logic.I.
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
        erewrite temp_types_init_same by eauto. simpl. apply Coq.Init.Logic.I.
         apply Coq.Init.Logic.I.
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
                                        inv H0; simpl; apply Coq.Init.Logic.I.
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
        erewrite temp_types_init_same by eauto. simpl. apply Coq.Init.Logic.I.
         apply Coq.Init.Logic.I.
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
     apply Coq.Init.Logic.I.
     unfold tc_temp_id. unfold typecheck_temp_id. rewrite H1.
     simpl. apply Coq.Init.Logic.I.
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