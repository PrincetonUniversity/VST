Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.
Require Import floyd.compare_lemmas.
Require Import floyd.malloc_lemmas.
Local Open Scope logic.

Fixpoint fold_range' {A: Type} (f: Z -> A -> A) (zero: A) (lo: Z) (n: nat) : A :=
 match n with
  | O => zero
  | S n' => f lo (fold_range' f  zero (Zsucc lo) n')
 end.

Definition fold_range {A: Type} (f: Z -> A -> A) (zero: A) (lo hi: Z) : A :=
  fold_range' f zero lo (nat_of_Z (hi-lo)).

Lemma rangespec'_ext:
 forall f f' contents lo,
   (forall i, i>=lo -> f i = f' i) -> 
   rangespec' lo contents f = rangespec' lo contents f'.
Proof.
induction contents; intros.
simpl. auto.
simpl. f_equal. apply H. omega.
apply IHcontents. intros. apply H. omega.
Qed.

Definition repinject (t: type) : option (reptype t -> val) :=
  match t as t0 return option (reptype t0 -> val) with
 | Tint _ _ _ => Some Vint
 | Tlong _ _ => Some Vlong
 | Tfloat _ _ => Some Vfloat
  | Tpointer _ _ => Some (fun x => x)
  | _ => None
 end.

Lemma repinject_typed_mapsto:
  forall sh t loc c inject,
   repinject t = Some inject ->
   typed_mapsto sh t loc c = mapsto sh t loc (inject c).
Proof.
intros.
 destruct t; inv H; unfold typed_mapsto, typed_mapsto', eq_rect_r; simpl;
  rewrite withspacer_spacer;
 unfold spacer; rewrite align_0; simpl; try rewrite emp_sepcon; auto;
 try destruct i; try destruct f; try omega.
Qed.

Lemma split3_array_at:
  forall i ty sh contents lo hi v,
       lo <= i < hi ->
     array_at ty sh contents lo hi v =
     array_at ty sh contents lo i v *
     typed_mapsto sh ty (add_ptr_int ty v i) (contents i) *
     array_at ty sh contents (Zsucc i) hi v.
Proof.
 intros.
 unfold array_at, rangespec.
 remember (nat_of_Z (i - lo)) as n.
 replace (nat_of_Z (hi - lo)) with (n + nat_of_Z (hi - i))%nat.
Focus 2. {subst; unfold nat_of_Z; rewrite <- Z2Nat.inj_add by omega.
   f_equal.  omega.
} Unfocus.
 unfold nat_of_Z in *.
 replace (Z.to_nat (hi - i)) with (S (Z.to_nat (hi-Z.succ i))).
Focus 2. {
 unfold Z.succ. 
 replace (hi-i) with (1 + (hi-(i+1))) by omega.
 rewrite Z2Nat.inj_add by omega.
 simpl. auto.
 } Unfocus.
 revert lo Heqn H; induction n; simpl; intros.
* destruct (zlt 0 (i-lo)).
  destruct (i-lo); try omega.
  rewrite Z2Nat.inj_pos in Heqn.
  generalize (Pos2Nat.is_pos p); omega.
  generalize (Pos2Z.neg_is_neg p); omega.
  assert (i=lo) by omega. subst i.
  rewrite emp_sepcon.
  simpl. f_equal; auto.
* repeat rewrite sepcon_assoc.
  f_equal; auto.
  assert (i<>lo).
  intro. subst. replace (lo-lo) with 0 in Heqn by omega. 
  inv Heqn.
  assert (n = Z.to_nat (i - Z.succ lo)).
    replace (i - Z.succ lo) with ((i-lo)- 1) by omega.
    rewrite Z2Nat.inj_sub by omega.  
   rewrite <- Heqn. simpl. omega.
  rewrite (IHn (Z.succ lo)); clear IHn; auto.
  rewrite sepcon_assoc. auto.
  omega.
Qed.

Lemma lift_split3_array_at:
  forall i ty sh contents lo hi,
       lo <= i < hi ->
     array_at ty sh contents lo hi =
     array_at ty sh contents lo i *
     (fun v => typed_mapsto sh ty (add_ptr_int ty v i) (contents i)) *
     array_at ty sh contents (Zsucc i) hi.
Proof.
 intros. extensionality v. simpl. apply split3_array_at. auto.
Qed.

Lemma at_offset_array: forall v t1 sh contents lo hi ofs,
     `(at_offset (array_at t1 sh contents lo hi) ofs) v =
     `(array_at t1 sh contents lo hi) (`(offset_val (Int.repr ofs)) v).
Proof.
 intros. extensionality rho. unfold_lift.
 rewrite at_offset_eq; auto.
  unfold array_at, rangespec.
 apply rangespec'_ext. intros.
 destruct (v rho); simpl; auto.
 f_equal. f_equal. rewrite Int.add_zero. auto.
Qed.

Definition strictAllowedCast tfrom tto :=
match Cop.classify_cast tfrom tto with 
| Cop.cast_case_neutral => 
   orb (andb (is_pointer_type tfrom) (is_pointer_type tto))
         (andb (is_int_type tfrom) (is_int_type tto))
| Cop.cast_case_i2i _ _ => true
| Cop.cast_case_l2l => true
| Cop.cast_case_f2f _ => true
| _  => false
end.

Lemma strictAllowedValCast:
  forall t1 t2, strictAllowedCast t1 t2 = true -> forall v, allowedValCast v t1 t2 = true.
Proof.
intros.
destruct t1,t2; inv H; destruct v; reflexivity.
Qed. 

Definition in_range (lo hi: Z) (x: Z) := lo <= x < hi.
Arguments in_range lo hi x /.

Lemma SEP_nth_isolate:
  forall n R Rn, nth_error R n = Some Rn ->
      SEPx R = SEPx (Rn :: replace_nth n R emp).
Proof.
 change SEPx with SEPx'.
 induction n; destruct R; simpl; intros; inv H; extensionality rho.
 rewrite emp_sepcon; auto.
 rewrite <- sepcon_assoc.
 rewrite (sepcon_comm (Rn rho)).
 rewrite sepcon_assoc.
 f_equal. rewrite (IHn R Rn H1).
 reflexivity.
Qed.


Lemma SEP_replace_nth_isolate:
  forall n R Rn Rn', 
       nth_error R n = Some Rn ->
      SEPx (replace_nth n R Rn') = SEPx (Rn' :: replace_nth n R emp).
Proof.
 intros.
 change SEPx with SEPx'.
 revert R H.
 induction n; destruct R; intros; inv H; simpl; intros; extensionality rho.
 rewrite emp_sepcon; auto.
 rewrite <- sepcon_assoc.
 rewrite (sepcon_comm (Rn' rho)).
 rewrite sepcon_assoc.
 f_equal. rewrite (IHn R H1).
 reflexivity.
Qed.

Lemma map_replace_nth:
  forall {A B} (f: A -> B) n R X, map f (replace_nth n R X) = 
       replace_nth n (map f R) (f X).
Proof.
intros.
 revert R; induction n; destruct R; simpl; auto.
 f_equal; auto.
Qed.

Lemma fold_right_sepcon_subst:
 forall i e R, fold_right sepcon emp (map (subst i e) R) = subst i e (fold_right sepcon emp R).
Proof.
 intros. induction R; auto.
 autorewrite with subst. f_equal; auto.
Qed.

Lemma resubst: forall {A} i (v: val) (e: environ -> A), subst i (`v) (subst i `v e) = subst i `v e.
Proof.
 intros. extensionality rho. unfold subst.
 f_equal.
 unfold env_set. 
 f_equal.
 apply Map.ext. intro j.
 destruct (eq_dec i j). subst. repeat rewrite Map.gss. f_equal.
 simpl.
 repeat rewrite Map.gso by auto. auto.
Qed.

Hint Rewrite @resubst : subst.

Lemma Zsucc_sub_self:
 forall x: Z, nat_of_Z (Z.succ x - x) = 1%nat.
Proof.
  intro. replace (Z.succ x - x) with 1 by omega. reflexivity.
Qed.

Require floyd.loadstore_lemmas.

Lemma semax_load_array':
forall Espec (Delta: tycontext) id sh t1 inject P Q R lo hi contents e1 (v1 v2: environ->val) t1' i2,
    typeof e1 =  tptr t1 ->
    (temp_types Delta) ! id = Some (t1',i2) ->
    type_is_volatile t1 = false ->
    strictAllowedCast t1 t1' = true ->
    repinject t1 = Some inject ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
            `(array_at t1 sh contents lo hi) v1 * TT ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
     local (tc_expr Delta e1) && local (`(tc_val tint) v2) && 
     local (`(in_range lo hi) (`force_signed_int v2)) && local (`isptr v1) && 
     local (`eq (`(eval_binop Oadd (tptr t1) tint) v1 v2) (eval_expr e1)) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ederef e1 t1))
       (normal_ret_assert 
        (EX old:val,
          PROPx P (LOCALx (`eq (eval_id id) (subst id (`old) (`inject (`contents (`force_signed_int v2)))) :: map (subst id (`old)) Q)
                (SEPx 
                  (map (subst id (`old)) R))))).
Proof.
 intros until 2. intros NONVOL CLASSIFY H3 H5 H2.

eapply semax_pre_post;
  [ | |  apply (loadstore_lemmas.semax_load_37 Delta sh id 
                (PROPx P (LOCALx (tc_expr Delta e1
           :: `(tc_val tint) v2
              :: `(in_range lo hi) (`force_signed_int v2)
                 :: `isptr v1
                    :: `eq (`force_val (`sem_add `(tptr t1)  `tint v1 v2))
                         (eval_expr e1) :: Q)
                (SEPx R))) (Ederef e1 t1)
    (`inject (`contents (`force_signed_int v2))))].
* (* precondition *)
apply loadstore_lemmas.later_left2.
rewrite insert_local.
rewrite <- (andp_dup (PROPx _ _)).
eapply derives_trans.
apply andp_derives.
apply derives_refl.
rewrite <- (andp_dup (PROPx _ _)).
apply andp_derives.
apply H2.
apply H5.
clear H2 H5.

go_lowerx.
forget (fold_right
  (fun (P0 Q0 : environ -> mpred) (rho0 : environ) => P0 rho0 * Q0 rho0)
  (fun _ : environ => emp) R rho) as RR.
normalize. repeat rewrite prop_and.
repeat apply andp_right; try apply prop_right; auto.
hnf; simpl. repeat rewrite denote_tc_assert_andp; repeat split; auto.
rewrite H; apply I.
hnf. unfold_lift. rewrite <- H10.
destruct (v2 rho); inv H6.
destruct (v1 rho); inv H9.
apply I.
rewrite NONVOL; apply I.
exists t1',i2; split; auto. apply strictAllowedValCast; auto.
apply andp_left1; auto.

* (* postcondition *)
clear. intros ek vl. apply andp_left2. apply normal_ret_assert_derives'.
 apply exp_derives; intro old.
 autorewrite with subst.
 go_lowerx. normalize.

* (* condition for semax_load_37 *)
eapply derives_trans; [ | eapply derives_trans; [ | ]].
Focus 2.
apply andp_derives; [apply H2 | apply H5].
rewrite andp_dup.
rewrite <- (insert_local (tc_environ Delta)).
apply andp_derives; auto.
repeat (rewrite <- insert_local; apply andp_left2).
auto.
clear H2 H5.
go_lowerx. normalize.
destruct (v2 rho); inv H2.
simpl in H4|-*.
unfold in_range in H4.
rewrite (split3_array_at (Int.signed i)  _ _ _ lo hi _ (conj H4 H5)).
rewrite (sepcon_comm (array_at t1 sh contents lo (Int.signed i) _)).
repeat rewrite sepcon_assoc.
apply sepcon_derives; auto.
rewrite <- H7.
destruct (v1 rho); inv H6.
simpl.
rewrite <- repinject_typed_mapsto by auto.
apply derives_refl'.
f_equal.
unfold add_ptr_int, eval_binop; simpl.
f_equal.
rewrite Int.repr_signed.
auto.
Qed.

Lemma semax_load_array:
forall Espec (Delta: tycontext) id sh t1 inject P Q R lo hi contents e1 (v1 v2: environ->val) t1' i2,
    typeof e1 =  tptr t1 ->
    (temp_types Delta) ! id = Some (t1',i2) ->
    type_is_volatile t1 = false ->
    strictAllowedCast t1 t1' = true ->
    repinject t1 = Some inject ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
            `(array_at t1 sh contents lo hi) v1 * TT ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
     local (tc_expr Delta e1) && local (`(tc_val tint) v2) && 
     local (`(in_range lo hi) (`force_signed_int v2)) && 
     local (`eq (`(eval_binop Oadd (tptr t1) tint) v1 v2) (eval_expr e1)) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ederef e1 t1))
       (normal_ret_assert 
        (EX old:val,
          PROPx P (LOCALx (`eq (eval_id id) (subst id (`old) (`inject (`contents (`force_signed_int v2)))) :: map (subst id (`old)) Q)
                (SEPx 
                  (map (subst id (`old)) R))))).
Proof.
intros.
eapply semax_load_array'; eauto.
rewrite <- (andp_dup (PROPx _ _)).
eapply derives_trans.
apply andp_derives.
apply H4.
apply H5.
clear.
go_lowerx.
normalize.
repeat apply andp_right; try solve [apply prop_right; auto].
unfold array_at, rangespec.
destruct (nat_of_Z (hi-lo)) eqn:?.
elimtype False; clear - H1 H2 Heqn.
assert (Z.of_nat (nat_of_Z (hi-lo)) = (hi-lo)).
apply nat_of_Z_eq; omega.
rewrite Heqn in H. simpl in H. omega.
unfold rangespec'; fold rangespec'.
rewrite sepcon_assoc.
eapply derives_trans.
apply sepcon_derives; [ | apply TT_right].
apply typed_mapsto_typed_mapsto_.
rewrite typed_mapsto__isptr.
normalize.
apply prop_right.
destruct (v1 rho); inv H4; simpl; auto.
Qed.

Lemma array_at_ext:
  forall t sh f  f' lo hi,
   (forall i, lo <= i < hi -> f i = f' i) ->
   array_at t sh f lo hi = array_at t sh f' lo hi.
Proof.
intros.
unfold array_at.
extensionality v.
unfold rangespec.
assert ( lo > hi \/ lo <= hi) by omega.
destruct H0.
rewrite nat_of_Z_neg by omega.
simpl. auto.
assert (hi = lo + Z_of_nat (nat_of_Z (hi-lo))).
rewrite nat_of_Z_eq by omega.
omega.
forget (nat_of_Z (hi-lo)) as n.
subst hi.
clear H0.
revert lo H; induction n; intros; auto.
simpl. 
rewrite Nat2Z.inj_succ in H.
f_equal.
rewrite H; auto.
omega.
apply IHn.
intros.
apply H.
omega.
Qed.

Definition typecheck_store' t := 
(is_int_type t = true -> t = Tint I32 Signed noattr) /\
(is_float_type t = true -> t = Tfloat F64 noattr).

Lemma mapsto_mapsto_: forall sh t v v',
   mapsto sh t v v' |-- mapsto_ sh t v.
Proof. unfold mapsto, mapsto_; intros.
normalize.
unfold umapsto.
destruct (access_mode t); auto.
destruct v; auto.
apply orp_left.
apply orp_right2.
apply andp_right. apply prop_right; auto.
apply exp_right with v'; auto.
normalize.
apply orp_right2. apply exp_right with v2'.
normalize.
Qed.
Hint Resolve mapsto_mapsto_ : cancel.

Lemma semax_store_array:
forall Espec (Delta: tycontext) n sh t1 (contents: Z -> reptype t1)
              lo hi   
              (v1: environ-> val) inject P Q R            
             e1  e2 (v2: Z) (v: reptype t1),
    writable_share sh ->
    typeof e1 =  tptr t1 ->
    type_is_volatile t1 = false ->
    typecheck_store' t1 ->
    repinject t1 = Some inject ->
    nth_error R n = Some (`(array_at t1 sh contents lo hi) v1) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
          local (`eq (`(eval_binop Oadd (tptr t1) tint) v1 `(Vint (Int.repr v2))) (eval_expr e1))
          && !! (in_range lo hi v2)
          && local (tc_expr Delta e1) && local (tc_expr Delta (Ecast e2 t1))
          && local (`(eq (inject v)) (eval_expr (Ecast e2 t1))) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sassign (Ederef e1 t1) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx (replace_nth n R
                    (`(array_at t1 sh (upd contents v2 v) lo hi) v1)))))).
Proof.
intros.
rewrite (SEP_nth_isolate _ _ _ H4) in H5|-*.
rewrite (SEP_replace_nth_isolate _ _ _ (`(array_at t1 sh (upd contents v2 v) lo hi) v1) H4).
forget (@replace_nth (environ -> mpred) n R (@emp _ _ _)) as R'.
clear n H4 R. rename R' into R.
eapply semax_pre_post;
 [ | | apply (semax_store Delta _ _ sh 
          (PROPx P (LOCALx
              (`eq (`(eval_binop Oadd (tptr t1) tint) v1 `(Vint (Int.repr v2))) (eval_expr e1) ::
              tc_expr Delta e1 :: tc_expr Delta (Ecast e2 t1) :: `(in_range lo hi v2) ::
              `(eq (inject v)) (eval_expr (Ecast e2 t1)) :: 
             Q)
            (SEPx 
             (`(array_at t1 sh contents lo v2) v1 ::
             `(array_at t1 sh contents (Zsucc v2) hi) v1 :: R))))); auto].
* apply loadstore_lemmas.later_left2.
  rewrite insert_local.
  rewrite <- (andp_dup (PROPx _ _)).
  eapply derives_trans; [apply andp_derives; [apply derives_refl | apply H5] |  clear H5].
  go_lowerx.
  gather_prop. apply derives_extract_prop.
  intros [? [? [? [? ?]]]].
  saturate_local.
  apply prop_right.
  repeat split; auto.
  hnf. simpl. repeat rewrite denote_tc_assert_andp; repeat split; auto.
  rewrite H0; reflexivity. simpl. unfold_lift. rewrite <- H7; simpl.
  destruct (v1 rho); inv H12; apply I.
  rewrite H1; reflexivity.
  omega. omega.
  apply derives_extract_prop; intros [? [? [? [? ?]]]].
  saturate_local.
  apply sepcon_derives; auto.
  rewrite  (split3_array_at v2).
  cancel.
  unfold_lift. rewrite <- H7; simpl.
  destruct (v1 rho); inv H12. simpl.
  unfold add_ptr_int; simpl.
  rewrite (repinject_typed_mapsto _ _ _ _ _ H3).
  cancel.
  omega.
* intros.
  clear H5.
  go_lowerx. apply normal_ret_assert_derives.
  unfold_lift.
  autorewrite with gather_prop.
  apply derives_extract_prop; intros [? [? [? [? [? [? ?]]]]]].
  saturate_local.  
  rewrite  (split3_array_at v2 _ _ _ lo hi).
  apply andp_right; [apply prop_right | ].
  repeat split; auto.
  cancel.
  rewrite (sepcon_comm (mapsto _ _ _ _)).
  apply sepcon_derives; [apply sepcon_derives | ].
  apply derives_refl'; apply equal_f; apply array_at_ext; intros.
  rewrite upd_neq; auto. omega.
  rewrite (repinject_typed_mapsto _ _ _ _ _ H3).
  destruct (eval_expr e1 rho); inv H12.
  destruct (v1 rho); inv H6.
  unfold add_ptr_int. simpl.
  rewrite upd_eq. rewrite H10. unfold_lift; simpl.
  apply derives_refl.
  apply derives_refl'; apply equal_f; apply array_at_ext; intros.
  rewrite upd_neq by omega. auto. omega.
Qed.
