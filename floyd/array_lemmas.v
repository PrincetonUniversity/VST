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
 f_equal. f_equal. rewrite Int.add_assoc. f_equal.
 rewrite Int.add_zero_l. auto.
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

Lemma subst_derives:
  forall id e P Q, P |-- Q -> subst id e P |-- subst id e Q.
Proof.
 intros. intro rho. unfold subst. apply H.
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

Lemma semax_load_array:
forall Espec (Delta: tycontext) n id sh t1 inject P Q R lo hi contents e1 (v1 v2: environ->val) t1' i2 ofs,
    typeof e1 =  tptr t1 ->
    (temp_types Delta) ! id = Some (t1',i2) ->
    type_is_volatile t1 = false ->
    strictAllowedCast t1 t1' = true ->
    repinject t1 = Some inject ->
    @nth_error (LiftEnviron mpred) R n = Some (`(array_at t1 sh contents lo hi)
                                 (`(offset_val (Int.repr ofs)) v1)) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
     local (tc_expr Delta e1) && local (`(tc_val tint) v2) && 
     local (`(in_range lo hi) (`force_signed_int v2)) && local (`isptr v1) && 
     local (`eq (`force_val (`sem_add (`(offset_val (Int.repr ofs)) v1) `(tptr t1) v2 `tint)) (eval_expr e1)) ->
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
 rewrite (SEP_nth_isolate _ _ _ H5) in H2|-*.
replace (EX  old : val,
      PROPx P
        (LOCALx
           (`eq (eval_id id)
              (subst id `old (`inject (`contents (`force_signed_int v2))))
            :: map (subst id `old) Q)
           (SEPx
              (map (subst id `old) R))))
 with  (EX  old : val,
      PROPx P
        (LOCALx
           (`eq (eval_id id)
              (subst id `old (`inject (`contents (`force_signed_int v2))))
            :: map (subst id `old) Q)
           (SEPx
              (map (subst id `old)
                 (`(array_at t1 sh contents lo hi) (`(offset_val (Int.repr ofs)) v1) ::
                    replace_nth n R emp))))).
Focus 2. {
  f_equal. extensionality old.  f_equal. f_equal.
 assert (subst id `old (SEPx 
              (`(array_at t1 sh contents lo hi) (`(offset_val (Int.repr ofs)) v1)
                  :: (replace_nth n R emp))) =
             subst id `old (SEPx R)).
f_equal.
 rewrite (SEP_nth_isolate _ _ _ H5). auto.
 clear - H1. 
 change SEPx with SEPx' in *; unfold SEPx' in *.
 autorewrite with subst in H1.
 repeat rewrite fold_right_sepcon_subst.
 auto.
} Unfocus.
clear H5.

change (@replace_nth (environ -> mpred) n R 
       (@emp (environ -> mpred) (@LiftNatDed' mpred Nveric)
                      (@LiftSepLog' mpred Nveric Sveric))) 
  with (@replace_nth (LiftEnviron mpred) n R
       (@emp (LiftEnviron mpred) (@LiftNatDed' mpred Nveric)
                      (@LiftSepLog' mpred Nveric Sveric))) 
 in *.
forget (@replace_nth (LiftEnviron mpred) n R emp) as R'. clear n R.
 (* rewrite at_offset_array in H2|-*. *)

apply semax_pre_post with
   (|>PROPx P
       (LOCALx (tc_expr Delta e1 :: `(tc_val tint) v2 ::
                      `(in_range lo hi) (`force_signed_int v2) :: `isptr v1 ::
                     `eq (`force_val (`sem_add (`(offset_val (Int.repr ofs)) v1) `(tptr t1) v2 `tint)) (eval_expr e1) :: Q)
          (SEPx
             (`(array_at t1 sh contents)  
                   (`force_signed_int v2)
                   (`Z.succ (`force_signed_int v2)) 
                   (`(offset_val (Int.repr ofs)) v1) :: `(array_at t1 sh contents lo)  (`force_signed_int v2)
                (`(offset_val (Int.repr ofs)) v1) :: 
             `(array_at t1 sh contents)  
                   (`Z.succ (`force_signed_int v2)) `hi
                   (`(offset_val (Int.repr ofs)) v1) :: 
               R'))))
  (normal_ret_assert
     (EX  old : val,
      PROPx P
        (LOCALx
           (`eq (eval_id id)
              (subst id `old (`inject (`contents (`force_signed_int v2))))
            :: map (subst id `old) (`(in_range lo hi) (`force_signed_int v2)
                       :: `isptr v1 :: `(tc_val tint) v2
                       :: Q))
           (SEPx
              (map (subst id `old)
                 (`(array_at t1 sh contents)  
                   (`force_signed_int (subst id `old v2))
                   (`Z.succ (`force_signed_int (subst id `old v2)))
                   (`(offset_val (Int.repr ofs)) v1) :: 
                 `(array_at t1 sh contents lo)  (`force_signed_int v2)
                        (`(offset_val (Int.repr ofs)) v1) :: 
                `(array_at t1 sh contents)  
                   (`Z.succ (`force_signed_int (subst id `old v2))) `hi
                   (`(offset_val (Int.repr ofs)) v1) :: 
               R')))))).
{eapply derives_trans. apply andp_derives. apply now_later. apply derives_refl.
 rewrite <- later_andp. apply later_derives.
 rewrite insert_local.
 eapply derives_trans.
 apply andp_right. apply H2. apply derives_refl.
 clear.
 go_lowerx.
 apply andp_right. destruct H1; apply prop_right; repeat split; auto. 
 rewrite (split3_array_at (force_signed_int (v2 rho)) _ _ _ lo hi) by apply H1.
 rewrite (sepcon_comm (array_at _ _ _ _ _ _)).
 repeat rewrite sepcon_assoc.
 apply sepcon_derives; auto.
 unfold array_at, rangespec.
 replace ( (Z.succ (force_signed_int (v2 rho)) - force_signed_int (v2 rho))) with 1 by omega.
 simpl. rewrite sepcon_emp.
 apply derives_refl.
}

{ clear. intros ek vl. apply andp_left2. apply normal_ret_assert_derives'.
 apply exp_derives; intro old.
 autorewrite with subst.

 go_lowerx. normalize. cancel.
  clear - H1 H2 H3.
  destruct (subst id (fun _ : environ => old) v1 rho); inv H2.
  destruct (subst id (fun _ : environ => old) v2 rho); inv H3.
  simpl in *.  
  rewrite (split3_array_at (Int.signed i0)  _ _ _ lo hi _ H1).
 simpl.
 cancel.
 unfold array_at, rangespec.
  replace (Z.succ (Int.signed i0) - Int.signed i0) with 1 by omega.
 simpl.
 rewrite sepcon_emp. apply derives_refl.
}

 eapply semax_pre_post;
  [ | |  apply (semax_load Delta sh id 
                (PROPx P (LOCALx (tc_expr Delta e1
           :: `(tc_val tint) v2
              :: `(in_range lo hi) (`force_signed_int v2)
                 :: `isptr v1
                    :: `eq (`force_val (`sem_add (`(offset_val (Int.repr ofs)) v1) `(tptr t1) v2 `tint))
                         (eval_expr e1) :: Q)
                (SEPx (`(array_at t1 sh contents lo) (`force_signed_int v2)
                   (`(offset_val (Int.repr ofs)) v1)
                 :: `(array_at t1 sh contents)
                      (`Z.succ (`force_signed_int v2)) `hi
                      (`(offset_val (Int.repr ofs)) v1) :: R')))) (Ederef e1 t1)
    (`inject (`contents (`force_signed_int v2))))]; auto.
 clear H2.
  eapply derives_trans; [apply andp_derives; [ apply now_later | apply derives_refl] | ].
  rewrite <- later_andp.
  apply later_derives.
  go_lowerx. apply andp_right.
  apply prop_right. unfold tc_lvalue; simpl.
    repeat rewrite denote_tc_assert_andp; repeat split; auto.
    rewrite H; apply I. hnf. unfold_lift. rewrite <- H8.
   destruct (v1 rho); inv H7. destruct (v2 rho); inv H5; reflexivity.
    rewrite NONVOL; apply I.
 apply andp_right. apply prop_right.
  unfold tc_temp_id_load. rewrite H0.
    do 2  eexists; split; try reflexivity.
    apply strictAllowedValCast; auto.

 normalize. apply sepcon_derives; auto.
 unfold array_at, rangespec. rewrite Zsucc_sub_self.
 simpl. unfold_lift. rewrite <- H8.
      destruct (v1 rho); inv H7. destruct (v2 rho); inv H5.
 simpl. rewrite sepcon_emp.
  rewrite Int.repr_signed.
 forget (Vptr b
     (Int.add (Int.add i (Int.repr ofs)) (Int.mul (Int.repr (sizeof t1)) i0))) as loc.
 forget (contents (Int.signed i0)) as c.
 clear - H3.
 rewrite <- repinject_typed_mapsto by auto. auto.

{intros ek vl. apply andp_left2.
 apply normal_ret_assert_derives'.
 apply exp_derives; intro old.
 clear H2. simpl eval_lvalue.
 autorewrite with subst.  repeat rewrite resubst.
forget (subst id `old v2) as v2'.
forget (subst id `old v1) as v1'.
 forget (subst id `old (eval_expr e1)) as e1'.
 clear v1 v2.
 go_lowerx. normalize. cancel. rewrite <- H8.
 destruct (v2' rho); inv H5.
 destruct (v1' rho); inv H7.
 simpl.
 unfold array_at, rangespec.
 rewrite Zsucc_sub_self. simpl. rewrite sepcon_emp.

 rewrite repinject_typed_mapsto with (inject := inject); auto.
 simpl. rewrite Int.repr_signed.
 apply derives_refl.
}
Qed.
