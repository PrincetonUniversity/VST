Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Import Cop.
Import LiftNotation.
Import compcert.lib.Maps.
Local Open Scope logic.

Lemma semax_while_peel:
  forall {CS: compspecs} {Espec: OracleKind} Inv Delta P expr body R,
  @semax CS Espec Delta P (Ssequence (Sifthenelse expr Sskip Sbreak) body) 
                             (loop1_ret_assert Inv R) ->
  @semax CS Espec Delta Inv (Swhile expr body) R ->
  @semax CS Espec Delta P (Swhile expr body) R.
Proof.
intros.
apply semax_loop_unroll1 with (P' := Inv) (Q := Inv); auto.
eapply semax_pre; [ |  apply sequential; apply semax_skip].
destruct R; apply ENTAIL_refl.
Qed.

Lemma typelist2list_arglist: forall l i, map snd (arglist i l) = typelist2list l.
Proof. induction l. simpl; intros; trivial.
intros. simpl. f_equal. apply IHl.
Qed. 

Lemma semax_func_cons_ext_vacuous:
     forall {Espec: OracleKind} (V : varspecs) (G : funspecs) (C : compspecs) ge
         (fs : list (ident * Clight.fundef)) (id : ident) (ef : external_function)
         (argsig : typelist) (retsig : type)
         (G' : funspecs) cc b,
       (id_in_list id (map fst fs)) = false ->
       ef_sig ef =
       {|
         sig_args := typlist_of_typelist argsig;
         sig_res := rettype_of_type retsig;
         sig_cc := cc_of_fundef (External ef argsig retsig cc) |} ->
       Genv.find_symbol ge id = Some b ->
       Genv.find_funct_ptr ge b = Some (External ef argsig retsig cc) ->
       semax_func V G ge fs G' ->
       semax_func V G ge ((id, External ef argsig retsig cc) :: fs)
         ((id, vacuous_funspec (External ef argsig retsig cc)) :: G').
Proof.
intros.
specialize (@semax_func_cons_ext Espec V G C ge fs id ef argsig retsig
  (rmaps.ConstType Impossible) (fun _ _ => FF) (fun _ _ => FF) ). simpl. 
intros HH; eapply HH; clear HH; try assumption; trivial.
* rewrite <-(typelist2list_arglist _ 1). reflexivity.
* right. clear. hnf. intros. simpl in X; inv X.
* intros. simpl. apply andp_left1, FF_left.
* eassumption.
* assumption.
* apply semax_external_FF.
Qed.

Lemma semax_func_cons_int_vacuous
  (Espec : OracleKind) (V : varspecs) (G : funspecs) 
    (cs : compspecs) (ge : Genv.t (fundef function) type)
    (fs : list (ident * Clight.fundef)) (id : ident) ifunc
    (b : block) G'
  (ID: id_in_list id (map fst fs) = false)
  (ID2: id_in_list id (map fst G) = true)
  (GfsB: Genv.find_symbol ge id = Some b)
  (GffpB: Genv.find_funct_ptr ge b = Some (Internal ifunc))
  (CTvars: Forall (fun it : ident * type => complete_type cenv_cs (snd it) = true) (fn_vars ifunc))
  (LNR_PT: list_norepet (map fst (fn_params ifunc) ++ map fst (fn_temps ifunc)))
  (LNR_Vars: list_norepet (map fst (fn_vars ifunc)))
  (VarSizes: semax.var_sizes_ok cenv_cs (fn_vars ifunc))
  (Sfunc: @semax_func Espec V G cs ge fs G'):
  @semax_func Espec V G cs ge ((id, Internal ifunc) :: fs)
    ((id, vacuous_funspec (Internal ifunc)) :: G').
Proof.
eapply semax_func_cons; try eassumption.
+ rewrite ID, ID2. simpl. unfold semax_body_params_ok.
  apply compute_list_norepet_i in LNR_PT. rewrite LNR_PT.
  apply compute_list_norepet_i in LNR_Vars. rewrite LNR_Vars. trivial.
+ destruct ifunc; simpl; trivial.
+ red; simpl. split3.
  - destruct ifunc; simpl; trivial.
  - destruct ifunc; simpl; trivial.
  - intros ? ? Impos. inv Impos.
Qed.

Lemma semax_prog_semax_func_cons_int_vacuous
  (Espec : OracleKind) (V : varspecs) (G : funspecs) 
    (cs : compspecs) (ge : Genv.t (fundef function) type)
    (fs : list (ident * Clight.fundef)) (id : ident) ifunc
    (b : block) G'
  (ID: id_in_list id (map fst fs) = false)
  (GfsB: Genv.find_symbol ge id = Some b)
  (GffpB: Genv.find_funct_ptr ge b = Some (Internal ifunc))
  (CTvars: Forall (fun it : ident * type => complete_type cenv_cs (snd it) = true) (fn_vars ifunc))
  (LNR_PT: list_norepet (map fst (fn_params ifunc) ++ map fst (fn_temps ifunc)))
  (LNR_Vars: list_norepet (map fst (fn_vars ifunc)))
  (VarSizes: semax.var_sizes_ok cenv_cs (fn_vars ifunc))
  (Sfunc: @semax_prog.semax_func Espec V G cs ge fs G'):
  @semax_prog.semax_func Espec V G cs ge ((id, Internal ifunc) :: fs)
    ((id, vacuous_funspec (Internal ifunc)) :: G').
Proof.
apply id_in_list_false in ID. destruct Sfunc as [Hyp1 [Hyp2 Hyp3]].
split3.
{ constructor. 2: apply Hyp1. simpl. destruct ifunc; simpl.
  unfold type_of_function. simpl. rewrite TTL1; trivial. }
{ clear Hyp3. red; intros j fd J. destruct J; [ inv H | auto].
  exists b; split; trivial. }
intros. specialize (Hyp3 _ Gfs Gffp n).
intros v sig cc A P Q ? m NM EM CL. simpl in CL. red in CL.
destruct CL as [j [Pne [Qne [J GJ]]]]. simpl in J.
rewrite PTree.gsspec in J.
destruct (peq j id); subst.
+ specialize (Hyp3 v sig cc A P Q _ _ NM EM).
  clear Hyp3.
  destruct GJ as [bb [BB VV]]. inv J. 
  assert (bb = b). 
  { clear - GfsB Gfs BB. specialize (Gfs id); unfold sub_option, Clight.fundef in *.
    rewrite GfsB in Gfs. destruct ge'. simpl in *. rewrite Gfs in BB. inv BB; trivial. }
  subst bb. right. simpl. exists b, ifunc.
  specialize (Gffp b).
  unfold Clight.fundef in *. simpl in *. rewrite GffpB in Gffp. simpl in Gffp.
  repeat split; trivial.
  destruct ifunc; trivial.
  destruct ifunc; trivial.
  intros until b2; intros Impos; inv Impos.
+ apply (Hyp3 v sig cc A P Q _ _ NM EM).
  simpl. exists j; do 2 eexists; split. apply J. apply GJ.
Qed. 

Lemma int_eq_false_e:
  forall i j, Int.eq i j = false -> i <> j.
Proof.
intros.
intro; subst.
rewrite Int.eq_true in H; inv H.
Qed.

Lemma int64_eq_false_e:
  forall i j, Int64.eq i j = false -> i <> j.
Proof.
intros.
intro; subst.
rewrite Int64.eq_true in H; inv H.
Qed.

Lemma ptrofs_eq_false_e:
  forall i j, Ptrofs.eq i j = false -> i <> j.
Proof.
intros.
intro; subst.
rewrite Ptrofs.eq_true in H; inv H.
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
     @semax cs Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
                         (Sifthenelse b c d) Post.
Proof.
 intros.
 eapply semax_pre;  [ | apply semax_ifthenelse]; auto.
 instantiate (1:=(local (`(eq v) (eval_expr b)) && PROPx P (LOCALx Q (SEPx R)))).
 eapply derives_trans; [apply andp_derives, derives_refl; apply now_later|].
 rewrite <- later_andp; apply later_derives.
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

Definition logical_or tid e1 e2 :=
(Sifthenelse e1
             (Sset tid (Econst_int (Int.repr 1) tint))
             (Ssequence
                (Sset tid (Ecast e2 tbool))
                (Sset tid (Ecast (Etempvar tid tint) tint)))).



Definition logical_and tid e1 e2 :=
(Sifthenelse e1
            (Ssequence
              (Sset tid (Ecast e2 tbool))
              (Sset tid (Ecast (Etempvar tid tint) tint)))
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
apply semax_pre_simple with (|>( (tc_expr Delta (Eunop Cop.Onotbool test tint)) && Q)).
eapply derives_trans, now_later.
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
     (local (tc_environ Delta) && Q |-- (tc_expr Delta (Eunop Cop.Onotbool test tint))) ->
     (local (tc_environ Delta)
      && local (`(typed_false (typeof test)) (eval_expr test))
      && Q |-- RA_normal Post) ->
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
apply semax_pre_simple with (|> ((tc_expr Delta (Eunop Cop.Onotbool test tint)) && Q)).
eapply derives_trans, now_later.
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
unfold Zbits.eqmod.
set (m := Int.modulus) in *.
destruct H as [z ?].
assert (x = y mod m + z * m) by lia.
clear H. subst x.
pose proof (Z.div_mod y m).
spec H. intro Hx; inv Hx.
evar (k: Z).
exists k.
rewrite H at 2; clear H.
rewrite (Z.mul_comm m).
assert (z * m = k*m + (y/m*m))%Z; [ | lia].
rewrite <- Z.mul_add_distr_r.
f_equal.
assert (k = z - y/m); [ | lia].
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
rewrite Int.unsigned_repr by rep_lia.
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
 apply @semax_seq with (Q := PROPx (typed_true (typeof test) (v a) :: P a) (LOCALx (Q a) (SEPx (R a)))).
 apply semax_pre with (|> (tc_expr Delta (Eunop Onotbool test (Tint I32 Signed noattr)) 
                                        && (local (`(eq (v a)) (eval_expr test)) && (PROPx (P a) (LOCALx (Q a) (SEPx (R a)))))));
   [ | apply semax_ifthenelse; auto].
 eapply derives_trans, now_later.
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

