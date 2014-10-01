Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.compare_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.loadstore_lemmas.
Require Import Coq.Logic.JMeq.
Local Open Scope logic.

Lemma tc_val_Vundef:
  forall t, ~ tc_val t Vundef.
Proof. destruct t as [ | | | [ | ] |  | | | | | ]; intro H; inv H.
Qed.

Lemma ZnthV_map_Vint_is_int:
  forall l i, 0 <= i < Zlength l -> is_int (ZnthV tint (map Vint l) i).
Proof.
intros.
unfold ZnthV.
if_tac; [omega | ].
assert (Z.to_nat i < length l)%nat.
destruct H.
rewrite Zlength_correct in H1.
apply Z2Nat.inj_lt in H1; try omega.
rewrite Nat2Z.id in H1. auto.
clear - H1.
revert l H1; induction (Z.to_nat i); destruct l; intros; simpl in *.
omega. auto. omega. apply IHn; omega.
Qed.

Fixpoint fold_range' {A: Type} (f: Z -> A -> A) (zero: A) (lo: Z) (n: nat) : A :=
 match n with
  | O => zero
  | S n' => f lo (fold_range' f  zero (Zsucc lo) n')
 end.

Definition fold_range {A: Type} (f: Z -> A -> A) (zero: A) (lo hi: Z) : A :=
  fold_range' f zero lo (nat_of_Z (hi-lo)).

Lemma rangespec'_ext: forall f f' lo len,
  (forall i, lo <= i < lo + Z_of_nat len -> f i = f' i) -> 
  rangespec' lo len f = rangespec' lo len f'.
Proof.
  intros; revert lo H; 
  induction len; intros.
  + simpl. auto.
  + simpl. f_equal.
    - apply H.
      rewrite Nat2Z.inj_succ.
      rewrite <- Z.add_1_r.
      pose proof Zle_0_nat (S len).
      omega.
    - apply IHlen. intros. apply H.
      rewrite Nat2Z.inj_succ.
      rewrite <- Z.add_1_r.
      pose proof Zle_0_nat (S len).
      omega.
Qed.

Lemma rangespec'_elim: forall f lo len i,
  lo <= i < lo + Z_of_nat len -> rangespec' lo len f |-- f i * TT.
Proof.
  intros. revert lo i H; induction len; intros.
  + simpl in H. omega.
  + simpl. destruct (Z.eq_dec i lo).
    - subst. cancel.
    - replace (f i * TT) with (TT * (f i * TT)) by (apply pred_ext; cancel).
      apply sepcon_derives; [cancel |].
      apply IHlen.
      rewrite Nat2Z.inj_succ in H.
      rewrite <- Z.add_1_l in *.
      omega.
Qed.      

Lemma prop_false_andp {A}{NA :NatDed A}:
 forall P Q, ~P -> !! P && Q = FF.
Proof.
intros.
apply pred_ext; normalize.
Qed.
Lemma orp_FF {A}{NA: NatDed A}:
 forall Q, Q || FF = Q.
Proof.
intros. apply pred_ext. apply orp_left; normalize. apply orp_right1; auto.
Qed.
Lemma FF_orp {A}{NA: NatDed A}:
 forall Q, FF || Q = Q.
Proof.
intros. apply pred_ext. apply orp_left; normalize. apply orp_right2; auto.
Qed.

Lemma offset_in_range_mid: forall lo hi i t p,
  lo <= i <= hi ->
  offset_in_range (sizeof t * lo) p ->
  offset_in_range (sizeof t * hi) p ->
  offset_in_range (sizeof t * i) p.
Proof.
  intros.
  unfold offset_in_range in *.
  destruct p; auto.
  pose proof sizeof_pos t.
  assert (sizeof t * i <= sizeof t * hi) by (apply Zmult_le_compat_l; omega).
  assert (sizeof t * lo <= sizeof t * i) by (apply Zmult_le_compat_l; omega).
  omega.
Qed.

Lemma split3_array_at:
  forall i ty sh contents lo hi v,
       lo <= i < hi ->
     array_at ty sh contents lo hi v =
     array_at ty sh contents lo i v *
     data_at sh ty  (contents i) (add_ptr_int ty v i)*
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
 normalize.
 f_equal; [f_equal; apply prop_ext; intuition| revert lo Heqn H; induction n; simpl; intros].
* eapply offset_in_range_mid with lo hi; try omega; assumption.
* eapply offset_in_range_mid with lo hi; try omega; assumption.
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

Lemma prop_andp_ext':
 forall {A} {ND: NatDed A}
    P1 Q1 P2 Q2, 
    (P1 <-> P2) -> (P1 -> (Q1 = Q2)) ->
    (!! P1 && Q1 = !! P2 && Q2).
Proof.
intros.
apply pred_ext; intros; normalize; rewrite H0; auto; intuition;
 apply andp_right; auto; apply prop_right; intuition.
Qed.

Lemma split3_array_at':
  forall i ty sh contents lo hi v (c: val),
     type_is_by_value ty  ->
     legal_alignas_type ty = true ->
     JMeq (contents i) c ->
     reptype ty = val ->
       lo <= i < hi ->
     array_at ty sh contents lo hi v =
     array_at ty sh contents lo i v *
     mapsto sh ty (add_ptr_int ty v i) c *
     array_at ty sh contents (Zsucc i) hi v.
Proof.
  intros until 1; intro LAT; intros.
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
 normalize.
 apply prop_andp_ext'.
 intuition.
 eapply offset_in_range_mid with lo hi; try omega; assumption.
 eapply offset_in_range_mid with lo hi; try omega; assumption.
 intros [? [? [? ?]]].
 assert (H7: 0 < sizeof ty)
  by ( clear - H; destruct ty; try contradiction; try destruct i; try destruct f; try destruct s; simpl; omega).
 revert lo Heqn H2 H6; induction n; simpl; intros.
*
  destruct (zlt 0 (i-lo)).
  destruct (i-lo); try omega.
  rewrite Z2Nat.inj_pos in Heqn.
  generalize (Pos2Nat.is_pos p); omega.
  generalize (Pos2Z.neg_is_neg p); omega.
  assert (i=lo) by omega. subst i.
 clear g Heqn.
 rewrite (by_value_data_at sh ty (contents lo) c); auto.
 normalize.
 rewrite prop_true_andp; auto.
 destruct v; try contradiction.
 hnf in H4,H6.
 assert (H6': 0 <= Int.unsigned i + sizeof ty * lo < Int.modulus). {
  split; [ omega | ].
  assert (Int.unsigned i + sizeof ty * lo < Int.unsigned i + sizeof ty * hi).
 apply Zplus_lt_compat_l.
 apply Zmult_lt_compat_l.
 omega.
 omega. omega.
}
 split.
+
 hnf in H4. unfold add_ptr_int. simpl eval_binop. rewrite mul_repr.
 red. rewrite <- (Int.repr_unsigned i).
  rewrite add_repr. 
  rewrite Int.unsigned_repr
    by ( change Int.max_unsigned with (Int.modulus - 1); omega).
 assert (sizeof ty * lo + sizeof ty <= sizeof ty * hi); [ | omega].
 replace (sizeof ty * lo + sizeof ty) with (sizeof ty * (lo+1))%Z.
 apply Zmult_le_compat_l; try omega.
 rewrite Z.mul_add_distr_l. omega.
+
  destruct H3 as [z ?].
  unfold add_ptr_int. simpl eval_binop.
 hnf in H6.
 hnf.
 rewrite <- (Int.repr_unsigned i).
 rewrite H3 in H6|-*.
 rewrite mul_repr. rewrite add_repr.
 rewrite Int.unsigned_repr
     by ( change Int.max_unsigned with (Int.modulus - 1); omega).
  apply legal_alignas_sizeof_alignof_compat in LAT.
 destruct LAT.
 rewrite H8.
 exists (z+x*lo).
 rewrite Z.mul_add_distr_r.
 f_equal. repeat rewrite <- Z.mul_assoc. f_equal.
 apply Z.mul_comm.
* repeat rewrite sepcon_assoc.
  f_equal; auto.
  assert (i<>lo).
  intro. subst. replace (lo-lo) with 0 in Heqn by omega. 
  inv Heqn.
  assert (n = Z.to_nat (i - Z.succ lo)).
    replace (i - Z.succ lo) with ((i-lo)- 1) by omega.
    rewrite Z2Nat.inj_sub by omega.  
   rewrite <- Heqn. simpl. omega.
 rewrite (IHn (Z.succ lo)); auto.
 repeat rewrite sepcon_assoc.
 f_equal.
 omega.
 clear - H7 H4 H6 H2.
 hnf in H4,H6|-*.
 destruct v; auto.
 unfold Z.succ.
 assert (sizeof ty * lo < sizeof ty * (lo+1) <= sizeof ty * hi); [ | omega].
 split.
 apply Zmult_lt_compat_l; try omega.
 apply Zmult_le_compat_l; try omega.
Qed.


Lemma lift_split3_array_at:
  forall i ty sh contents lo hi,
       lo <= i < hi ->
     array_at ty sh contents lo hi =
     array_at ty sh contents lo i *
     (fun v => data_at sh ty  (contents i) (add_ptr_int ty v i)) *
     array_at ty sh contents (Zsucc i) hi.
Proof.
 intros. extensionality v. simpl. apply split3_array_at; auto.
Qed.

(*
Lemma at_offset_array: forall v t1 sh contents lo hi ofs,
     `(at_offset ofs (array_at t1 sh contents lo hi)) v =
     `(array_at t1 sh contents lo hi) (`(offset_val (Int.repr ofs)) v).
Proof.
 intros. extensionality rho. unfold_lift.
 rewrite at_offset_eq; auto.
  unfold array_at, rangespec.
 apply rangespec'_ext. intros.
 destruct (v rho); simpl; auto.
 f_equal. f_equal. rewrite Int.add_zero. auto.
Qed.
*)

(*
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
*)

Definition in_range (lo hi: Z) (x: Z) := lo <= x < hi.
Arguments in_range lo hi x /.

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

Definition defined_rep {t} : reptype t -> Prop :=
match t as t0 return (reptype t0 -> Prop) with
| Tvoid => fun _ : reptype Tvoid => False
| Tint i s a =>
    fun v0 : reptype (Tint i s a) => exists v' : int, v0 = Vint v'
| Tlong s a =>
    fun v0 : reptype (Tlong s a) => exists v' : int64, v0 = Vlong v'
| Tfloat f a =>
    fun v0 : reptype (Tfloat f a) => exists v' : float, v0 = Vfloat v'
| Tpointer t0 a => fun v0 : reptype (Tpointer t0 a) => is_pointer_or_null v0
| Tarray t0 z a => fun _ : reptype (Tarray t0 z a) => False
| Tfunction t0 t1 cc => fun _ : reptype (Tfunction t0 t1 cc) => False
| Tstruct i f a => fun _ : reptype (Tstruct i f a) => False
| Tunion i f a => fun _ : reptype (Tunion i f a) => False
| Tcomp_ptr i a => fun _ : reptype (Tcomp_ptr i a) => False
end.

Lemma sem_add_pi_ptr': forall (t : type) p ofs,
  isptr p ->
  is_int ofs ->
  isptr (force_val (sem_add_pi t p ofs)).
Proof.
  intros.
  destruct ofs; inversion H0.
  rewrite sem_add_pi_ptr; [|exact H].
  destruct p; inversion H.
  simpl.
  tauto.
Qed.

Lemma array_at_non_volatile: forall t sh contents lo hi v,
  lo < hi ->
  array_at t sh contents lo hi v |-- !! (nested_non_volatile_type t = true).
Proof.
  admit.
Qed.

Lemma semax_deref_load_37:
  forall {Espec: OracleKind},
    forall Delta sh id P Q R (e1: expr)
      (t t1: type) (v: environ -> val),
      typeof_temp Delta id = Some t ->
      is_neutral_cast t1 t = true ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_lvalue Delta (Ederef e1 t1)) &&
        local (`(tc_val t1) v) &&
        (`(data_at sh t1) (`(valinject t1) v) (eval_expr e1) * TT) ->
      semax Delta 
        (|> PROPx P (LOCALx Q (SEPx R)))
          (Sset id (Ederef e1 t1))
            (normal_ret_assert
              (EX old:val,
                PROPx P 
                  (LOCALx (`(eq) (subst id `old v) (eval_id id) :: map (subst id (`old)) Q)
                    (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  eapply semax_data_load_37.
  + exact H.
  + simpl. exact H0.
  + simpl typeof. simpl eval_lvalue.
    rewrite <- offset_val_force_ptr.
    unfold liftx, lift in *; simpl in *; intros.
    change Int.zero with (Int.repr 0).
    rewrite <- data_at_offset_zero.
    exact (H1 x).
Qed.

Lemma semax_deref_cast_load_37:
  forall {Espec: OracleKind},
    forall Delta sh id P Q R (e1: expr)
    (t t1: type) (v: environ -> val),
    typeof_temp Delta id = Some t ->
    type_is_by_value t1 ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
      local (tc_lvalue Delta (Ederef e1 t1)) &&
      local (`(tc_val t) (`(eval_cast t1 t) v)) &&
      (`(data_at sh t1) (`(valinject t1) v) (eval_expr e1) * TT) ->
    semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
      (Sset id (Ecast (Ederef e1 t1) t))
        (normal_ret_assert
          (EX old:val, 
            PROPx P 
              (LOCALx (`eq (subst id `old (`(eval_cast t1 t) v)) (eval_id id) :: map (subst id (`old)) Q)
                (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  eapply semax_data_cast_load_37.
  + exact H.
  + simpl. exact H0.
  + simpl typeof. simpl eval_lvalue.
    rewrite <- offset_val_force_ptr.
    unfold liftx, lift in *; simpl in *; intros.
    change Int.zero with (Int.repr 0).
    rewrite <- data_at_offset_zero.
    exact (H1 x).
Qed.

Lemma valinject_repinject: forall t v,
  type_is_by_value t ->
  (valinject t (repinject t v)) = v.
Proof.
  intros.
  destruct t; inversion H; reflexivity.
Qed.

Lemma semax_load_array:
forall Espec (Delta: tycontext) id sh t1 P Q R lo hi (contents: Z -> reptype t1) e1 v1 v2 t1',
    typeof_temp Delta id = Some t1' ->
    is_neutral_cast t1 t1' = true ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
      local (tc_lvalue Delta (Ederef e1 t1)) &&
      local (`(tc_val t1) (`(repinject t1) (`contents (`force_signed_int v2)))) &&
      local (`(tc_val tint) v2) && 
      local (`(in_range lo hi) (`force_signed_int v2)) && 
      local (`eq (`(eval_binop Oadd (tptr t1) tint) v1 v2) (eval_expr e1)) &&
      (`(array_at t1 sh contents lo hi) v1 * TT) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ederef e1 t1))
       (normal_ret_assert
        (EX old:val,
          PROPx P 
            (LOCALx (`eq (subst id (`old) (`(repinject t1) (
              (`contents (`force_signed_int v2))))) (eval_id id) :: map (subst id (`old)) Q)
                (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  eapply semax_deref_load_37.
  + exact H.
  + exact H0.
  + eapply derives_trans; [exact H1|].
    unfold liftx, lift, local, lift1; simpl; intros.
    normalize.
    instantiate (1:=sh).
      erewrite split3_array_at; [|split; [exact H3 | exact H4]].
      unfold add_ptr_int.
      simpl eval_binop.
      rewrite <- H2.
      replace (Vint (Int.repr (force_signed_int (v2 x)))) with (v2 x).
      rewrite valinject_repinject; [cancel|].
        eapply is_neutral_cast_by_value, H0.
        destruct (v2 x); inversion H5; simpl.
        rewrite Int.repr_signed; reflexivity.
Qed.

Lemma semax_cast_load_array:
  forall {Espec: OracleKind},
    forall Delta sh id P Q R (e1: expr)
    (t t1: type) (contents: Z -> reptype t1) lo hi v1 v2,
    typeof_temp Delta id = Some t ->
    type_is_by_value t1 ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
      local (tc_lvalue Delta (Ederef e1 t1)) &&
      local (`(tc_val t) (`(eval_cast t1 t) (`(repinject t1) (`contents (`force_signed_int v2))))) &&
      local (`(tc_val tint) v2) && 
      local (`(in_range lo hi) (`(force_signed_int) v2)) && 
      local (`eq (`(eval_binop Oadd (tptr t1) tint) v1 v2) (eval_expr e1)) &&
      (`(array_at t1 sh contents lo hi) v1 * TT) ->
    semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
      (Sset id (Ecast (Ederef e1 t1) t))
        (normal_ret_assert
          (EX old:val, 
            PROPx P 
              (LOCALx (`eq (subst id (`old) (`(eval_cast t1 t) (`(repinject t1) (`contents (`force_signed_int v2))))) (eval_id id) :: map (subst id (`old)) Q)
                (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  eapply semax_deref_cast_load_37.
  + exact H.
  + exact H0.
  + eapply derives_trans; [exact H1|].
    unfold liftx, lift, local, lift1; simpl; intros.
    normalize.
    instantiate (1:=sh).
      erewrite split3_array_at; [|split; [exact H3 | exact H4]].
      unfold add_ptr_int.
      simpl eval_binop.
      rewrite <- H2.
      replace (Vint (Int.repr (force_signed_int (v2 x)))) with (v2 x).
        rewrite valinject_repinject; [cancel|exact H0].
        destruct (v2 x); inversion H5; simpl.
        rewrite Int.repr_signed; reflexivity.
Qed.

(*
Lemma semax_load_array':
forall Espec (Delta: tycontext) id sh t1 P Q R lo hi 
       (contents: Z -> reptype t1) e1 (v1 v2: environ->val) t1',
    typeof e1 =  tptr t1 ->
    typeof_temp Delta id = Some t1' ->
    no_attr_type t1 = true ->
    is_neutral_cast t1 t1' = true ->
    type_is_by_value t1 -> (*repinject t1 = Some inject -> *)
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
            `(array_at t1 sh contents lo hi) v1 * TT ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
     local (tc_expr Delta e1) && local (`(tc_val tint) v2) && 
     local (`(in_range lo hi) (`force_signed_int v2)) && 
     local (`(tc_val t1) (`(repinject t1) (`contents (`force_signed_int v2))))  && 
     local (`isptr v1) && 
     local (`eq (`(eval_binop Oadd (tptr t1) tint) v1 v2) (eval_expr e1)) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ederef e1 t1))
       (normal_ret_assert 
        (EX old:val,
          PROPx P (LOCALx (
                `eq (eval_id id) (subst id (`old) (`(repinject t1) (
                                          (`contents (`force_signed_int v2)))))
                            :: map (subst id (`old)) Q)
                (SEPx 
                  (map (subst id (`old)) R))))).
Proof.
 intros until 2. intros NONVOL CLASSIFY H3 H5 H2.
eapply semax_pre_post;
  [ | |  apply (semax_load Delta sh id 
                (PROPx P (LOCALx (tc_expr Delta e1
           :: `(tc_val tint) v2
              :: `(in_range lo hi) (`force_signed_int v2)
                 :: `isptr v1
                    :: `eq (`force_val (`sem_add `(tptr t1)  `tint v1 v2))
                         (eval_expr e1) :: Q)
                (SEPx R))) (Ederef e1 t1)
    t1' (`(repinject t1) ((`contents (`force_signed_int v2))))); auto].
* (* precondition *)
apply later_left2.
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
hnf. rewrite <- H11. 
destruct (v2 rho); inv H6.
destruct (v1 rho); inv H10.
apply I.
rewrite (no_attr_type_nonvol _ NONVOL); apply I.
apply andp_left1; auto.

* (* postcondition *)
clear. intros ek vl. apply andp_left2. apply normal_ret_assert_derives'.
 apply exp_derives; intro old.
 autorewrite with subst.
 go_lowerx. normalize.

* (* condition for semax_load *)
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
simpl in H4,H5|-*.
rewrite (split3_array_at (Int.signed i)  _ _ _ lo hi _  (conj H4 H5)).
rewrite (sepcon_comm (array_at t1 sh contents lo (Int.signed i) _)).
repeat rewrite sepcon_assoc.
apply sepcon_derives; auto.
rewrite <- H8.
destruct (v1 rho); inv H7.
simpl.
erewrite by_value_data_at by auto.
simpl in H6.
unfold add_ptr_int. simpl.
rewrite Int.repr_signed.
auto.
Qed.

Lemma semax_load_array:
forall Espec (Delta: tycontext) id sh t1 P Q R lo hi contents e1 (v1 v2: environ->val) t1',
    typeof e1 =  tptr t1 ->
    typeof_temp Delta id = Some t1' ->
    no_attr_type t1 = true ->
    is_neutral_cast t1 t1' = true ->
    type_is_by_value t1 -> (*repinject t1 = Some inject -> *)
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
            `(array_at t1 sh contents lo hi) v1 * TT ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
     local (tc_expr Delta e1) && local (`(tc_val tint) v2) && 
     local (`(in_range lo hi) (`force_signed_int v2)) && 
     local (`(tc_val t1) (`(repinject t1) (`contents (`force_signed_int v2))))  && 
     local (`eq (`(eval_binop Oadd (tptr t1) tint) v1 v2) (eval_expr e1)) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ederef e1 t1))
       (normal_ret_assert 
        (EX old:val,
          PROPx P (LOCALx (
                `eq (eval_id id) (subst id (`old) (`(repinject t1)  
                                          (`contents (`force_signed_int v2))))
                            :: map (subst id (`old)) Q)
                (SEPx 
                  (map (subst id (`old)) R))))).
Proof.
intros.
eapply semax_load_array' with (v1:=v1)(v2:=v2); eauto.
rewrite <- (andp_dup (PROPx _ _)).
eapply derives_trans.
apply andp_derives.
apply H4.
apply H5.
clear.
go_lowerx.
normalize.
destruct (v2 rho); inv H0.
simpl in H2, H3.
simpl in H1.
assert (lo<hi) by omega.
saturate_local.
destruct (v1 rho); inv H5.
apply prop_right; repeat split; try eassumption.
Qed.

Lemma semax_cast_load_array:
forall Espec (Delta: tycontext) id sh t1 P Q R lo hi contents e1 (v1 v2: environ->val) t1',
    typeof e1 =  tptr t1 ->
    typeof_temp Delta id = Some t1' ->
    no_attr_type t1 = true ->
    type_is_by_value t1 ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
            `(array_at t1 sh contents lo hi) v1 * TT ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
     local (tc_expr Delta e1) && local (`(tc_val tint) v2) && 
     local (`(in_range lo hi) (`force_signed_int v2)) && 
     local (`(tc_val t1')
       (`(eval_cast t1 t1') (`(repinject t1) (`contents (`force_signed_int v2)))))  && 
     local (`eq (`(eval_binop Oadd (tptr t1) tint) v1 v2) (eval_expr e1)) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sset id (Ecast (Ederef e1 t1) t1'))
       (normal_ret_assert 
        (EX old:val,
          PROPx P (LOCALx (
                `eq (eval_id id) (subst id (`old) (`(eval_cast t1 t1') (`(repinject t1)  
                                          (`contents (`force_signed_int v2)))))
                            :: map (subst id (`old)) Q)
                (SEPx 
                  (map (subst id (`old)) R))))).
Proof.
intros.
eapply semax_pre_post;
  [ | |  apply (semax_cast_load Delta sh id 
                (PROPx P (LOCALx (tc_expr Delta e1
           :: `(tc_val tint) v2
              :: `(in_range lo hi) (`force_signed_int v2)
                 :: `isptr v1
                    :: `eq (`force_val (`sem_add `(tptr t1)  `tint v1 v2))
                         (eval_expr e1) :: Q)
                (SEPx R)))
            _ t1' 
             ((`(repinject t1)  
                                          (`contents (`force_signed_int v2))))
             ); auto].
*
apply loadstore_lemmas.later_left2.
rewrite insert_local.
rewrite <- (andp_dup (PROPx _ _)).
eapply derives_trans.
apply andp_derives.
apply derives_refl.
rewrite <- (andp_dup (PROPx _ _)).
apply andp_derives; [apply H3 | apply H4].
clear H3 H4.

go_lowerx.
forget (fold_right
  (fun (P0 Q0 : environ -> mpred) (rho0 : environ) => P0 rho0 * Q0 rho0)
  (fun _ : environ => emp) R rho) as RR.
normalize. repeat rewrite prop_and.
rewrite array_at_isptr.
normalize.
apply andp_right; [ | apply andp_left1; auto].
apply prop_right; repeat split; auto.
hnf; simpl. repeat rewrite denote_tc_assert_andp; repeat split; auto.
rewrite H; apply I.
hnf. rewrite <- H11. 
destruct (v2 rho); inv H7.
destruct (v1 rho); inv H12.
apply I.
rewrite (no_attr_type_nonvol _ H1); apply I.
*
clear. intros ek vl. apply andp_left2. apply normal_ret_assert_derives'.
 apply exp_derives; intro old.
 autorewrite with subst.
 go_lowerx. normalize.
*(* condition for semax_load *)
eapply derives_trans; [ | eapply derives_trans; [ | ]].
Focus 2.
apply andp_derives; [apply H3 | apply H4].
rewrite andp_dup.
rewrite <- (insert_local (tc_environ Delta)).
apply andp_derives; auto.
repeat (rewrite <- insert_local; apply andp_left2).
auto.
clear H3 H4.
go_lowerx. normalize.
destruct (v2 rho); inv H4.
rewrite array_at_isptr; normalize.
destruct (v1 rho); inv H4.
simpl in H5,H6|-*.
rewrite (split3_array_at (Int.signed i)  _ _ _ lo hi _  (conj H5 H6)).
rewrite (sepcon_comm (array_at t1 sh contents lo (Int.signed i) _)).
repeat rewrite sepcon_assoc.
apply sepcon_derives; auto.
rewrite <- H8.
simpl.
rewrite data_at_mapsto by auto.
simpl in H8.
unfold add_ptr_int. simpl.
rewrite Int.repr_signed.
auto.
Qed.
*)

Lemma array_at_ext:
  forall t sh f  f' lo hi,
   (forall i, lo <= i < hi -> f i = f' i) ->
   array_at t sh f lo hi = array_at t sh f' lo hi.
Proof.
intros.
unfold array_at.
extensionality v.
f_equal.
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

Lemma array_at_ext':
  forall t sh f g lo hi p,
   (forall i, lo <= i < hi -> f i = g i) ->
   array_at t sh f lo hi p |-- array_at t sh g lo hi p.
Proof.
 intros.
 apply derives_refl';  apply equal_f;  apply array_at_ext; auto.
Qed.

Hint Extern 2 (array_at _ _ _ _ _ _ |-- array_at _ _ _ _ _ _) =>
  (apply array_at_ext'; intros; solve [normalize]) : cancel.

Lemma upd_Znth_next:
 forall t jl i v,
  Zlength jl = i ->
  upd (ZnthV t jl) i v = ZnthV t (jl++ (v::nil)).
Proof.
intros;
extensionality n.
unfold ZnthV, upd.
if_tac.
subst n.
if_tac. subst. rewrite Zlength_correct in H0. omega.
rewrite <- H.
subst i.
rewrite Zlength_correct.
rewrite Nat2Z.id.
induction jl; simpl; auto.
apply IHjl.
rewrite Zlength_correct; omega.
if_tac; auto.
subst i.
assert (Z.to_nat n <> length jl).
rewrite <- (Z2Nat.id n) in H0 by omega.
contradict H0. rewrite Zlength_correct; rewrite <- H0. auto.
clear - H.
revert jl H; induction (Z.to_nat n); destruct jl; intros; simpl; auto.
contradiction H; reflexivity.
destruct n0; reflexivity.
apply IHn0. simpl in H. contradict H; f_equal; auto. 
Qed.

Lemma array_at__array_at_None:
  forall t sh,  array_at_ t sh = array_at t sh (fun _ => default_val t).
Proof.
intros. reflexivity.
Qed.

Lemma semax_deref_store_nth:
  forall {Espec: OracleKind},
    forall Delta sh n P Q R Rn (e1 e2 : expr)
      (t t1: type),
      t1 = t ->
      type_is_by_value t ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (Rn))) |--
        `(data_at_ sh t) (eval_expr e1) ->
      writable_share sh ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (Ederef e1 t1)) && local (tc_expr Delta (Ecast e2 t)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (Ederef e1 t1) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(data_at sh t) (`(valinject t) (eval_expr (Ecast e2 t))) (eval_expr e1)
                          )))))).
Proof.
  intros.
  replace (`(data_at sh t) (`(valinject t) (eval_expr (Ecast e2 t))) (eval_expr e1)) with 
          (`(data_at sh t) (`(valinject t) (eval_expr (Ecast e2 t))) (eval_lvalue (Ederef e1 t1))) by (
    extensionality rho; simpl; unfold liftx, lift; simpl; intros;
    rewrite <- offset_val_force_ptr;
    rewrite <- data_at_offset_zero;
    reflexivity).
  eapply semax_data_store_nth.
  + exact H.
  + exact H0.
  + exact H1.
  + simpl; intro rho. eapply derives_trans; [exact (H2 rho)|].
    simpl; unfold liftx, lift; simpl; intros;
    rewrite <- offset_val_force_ptr;
    rewrite <- data_at__offset_zero.
    apply derives_refl.
  + exact H3.
  + exact H4.
Qed.

Ltac Z_and_int :=
  repeat
  match goal with
  | |- appcontext [Z.mul _ 0] => rewrite Z.mul_0_r
  | |- appcontext [Z.add _ 0] => rewrite Z.add_0_r
  | |- appcontext [Z.max _ _] => rewrite Z.max_r by omega
  | |- appcontext [Z.max _ _] => rewrite Z.max_l by omega
  | |- appcontext [Int.repr (Int.unsigned _)] => rewrite Int.repr_unsigned
  | |- Int.unsigned ?I <= Int.modulus => pose proof Int.unsigned_range I; omega
  | |- appcontext [Int.add] => unfold Int.add
  | |- appcontext [Int.mul] => unfold Int.mul
  | |- appcontext [Z.of_nat (S _)] => rewrite Nat2Z.inj_succ
  | |- appcontext [Z.succ _] => rewrite <- Z.add_1_r
  | |- appcontext [Int.unsigned (Int.repr _)] => rewrite Int.unsigned_repr by (unfold Int.max_unsigned; omega)
  | |- appcontext [Int.Z_mod_modulus ?Z] => change (Int.Z_mod_modulus Z) with (Int.unsigned (Int.repr Z))
  | H: appcontext [Z.of_nat (S _)] |- _ => rewrite Nat2Z.inj_succ in H
  | H: appcontext [Z.succ _] |- _ => rewrite <- Z.add_1_r in H
  | H: appcontext [Int.add] |- _ => unfold Int.add in H
  | H: appcontext [Int.mul] |- _ => unfold Int.mul in H
  | H: appcontext [Int.unsigned (Int.repr _)] |- _ => rewrite Int.unsigned_repr in H by (unfold Int.max_unsigned; omega)
  | H: appcontext [Int.Z_mod_modulus ?Z] |- _ => change (Int.Z_mod_modulus Z) with (Int.unsigned (Int.repr Z)) in H
  end.

Lemma array_at_array_at_: forall t sh contents lo hi p,
  legal_alignas_type t = true ->
  array_at t sh contents lo hi p |-- array_at_ t sh lo hi p.
Proof.
  intros.
  unfold array_at_, array_at, rangespec.
  normalize.
  destruct (zlt hi lo).
  + rewrite nat_of_Z_neg by omega. apply derives_refl.
  + replace hi with (lo + Z.of_nat (nat_of_Z (hi - lo))) in H1 by
      (rewrite nat_of_Z_eq by omega; omega).
    forget (nat_of_Z (hi - lo)) as m. clear hi g.
    revert lo H1 H2; induction m; intros; simpl.
    - apply derives_refl.
    - apply sepcon_derives; [|apply IHm].
      * eapply derives_trans; [apply data_at_data_at_, H|].
        unfold data_at_.
        apply derives_refl.
      * Z_and_int. eapply offset_in_range_mid; [| exact H2 | exact H1].
        omega.
      * Z_and_int. eapply offset_in_range_mid; [| exact H2 | exact H1].
        omega.
Qed.

Hint Resolve array_at_array_at_: cancel.

Lemma replace_nth_commute:
  forall {A} i j R (a b: A),
   i <> j ->
   replace_nth i (replace_nth j R b) a =
   replace_nth j (replace_nth i R a) b.
Proof.
intros.
rename i into i'. rename j into j'. rename R into R'.
assert (forall i j R (a b: A),
             (i<j)%nat -> 
              replace_nth i (replace_nth j R b) a = replace_nth j (replace_nth i R a) b). {
induction i; destruct j, R; simpl; intros; auto; try omega.
f_equal. apply IHi. omega.
}
assert (i'<j' \/ i'>j')%nat by omega.
clear H.
destruct H1.
apply H0; auto.
symmetry; apply H0; auto.
Qed.

Lemma nth_error_replace_nth':
  forall {A} i j R (a:A),
  (i <> j)%nat -> nth_error (replace_nth i R a) j = nth_error R j.
Proof.
induction i; destruct j,R; intros; simpl; auto.
contradiction H; auto.
Qed.

Lemma add_ptr_int_unfold: forall t1 v1 v2,
  is_int v2 ->
  force_val (sem_add_pi t1 v1 v2) = add_ptr_int t1 v1 (force_signed_int v2).
Proof.
  intros.
  destruct v2; inversion H.
  unfold add_ptr_int.
  simpl.
  rewrite Int.repr_signed.
  reflexivity.
Qed.

Lemma size_compatible_array_left: forall t n a i b ofs ofs',
  size_compatible (Tarray t n a) (Vptr b ofs) ->
  0 <= i < n ->
  add_ptr_int t (Vptr b ofs) i = (Vptr b ofs') ->
  Int.unsigned ofs' = Int.unsigned ofs + sizeof t * i.
Proof.
  intros.
  unfold add_ptr_int in H1.
  simpl in *.
  inversion H1; clear ofs' H1 H3.
  rewrite Z.max_r in H by omega.
  unfold Int.mul.
  destruct (zeq i 0); [|destruct (zeq (sizeof t) 0)].
  + subst i.
    simpl.
    repeat rewrite <- Zmult_0_r_reverse.
    simpl.
    repeat rewrite <- Zplus_0_r_reverse.
    rewrite Int.Z_mod_modulus_eq.
    rewrite <- Int.unsigned_repr_eq.
    rewrite Int.repr_unsigned.
    reflexivity.
  + rewrite e; clear e.
    simpl.
    repeat rewrite <- Zplus_0_r_reverse.
    rewrite Int.Z_mod_modulus_eq.
    rewrite <- Int.unsigned_repr_eq.
    rewrite Int.repr_unsigned.
    reflexivity.
  + assert (i > 0) by omega.
    assert (n >= 2) by omega.
    pose proof sizeof_pos t.
    pose proof Int.modulus_pos.
    pose proof Int.unsigned_range ofs.
    assert (sizeof t < Int.modulus).
      assert (sizeof t * 2 <= sizeof t * n) by (apply Zmult_le_compat_l; omega).
      rewrite <- Zplus_diag_eq_mult_2 in H6.
      omega.
    assert (n <= Int.modulus).
      assert (n <= sizeof t * n) by (rewrite <- Z.mul_1_l at 1; apply Zmult_le_compat_r; omega).
      omega.
    assert (sizeof t * i < sizeof t * n) by (apply Zmult_lt_compat_l; omega).
    assert (sizeof t * i > 0) by (apply Zmult_gt_0_compat; omega).
    rewrite Int.unsigned_repr by (unfold Int.max_unsigned; omega).
    rewrite Int.unsigned_repr by (unfold Int.max_unsigned; omega).
    simpl.
    repeat (rewrite Int.Z_mod_modulus_eq; rewrite <- Int.unsigned_repr_eq).
    rewrite (Int.unsigned_repr (sizeof t * i)) by (unfold Int.max_unsigned; omega).
    rewrite Int.unsigned_repr; unfold Int.max_unsigned; try omega.
Qed.
(*
Lemma size_compatible_array_right: forall t n a b ofs,
  (forall i ofs', 
  0 <= i < n ->
  add_ptr_int t (Vptr b ofs) i = (Vptr b ofs') ->
  Int.unsigned ofs' + sizeof t <= Int.modulus) ->
  size_compatible (Tarray t n a) (Vptr b ofs).
Proof.
  intros.
  unfold size_compatible; simpl.
  destruct (zlt n 0); Z_and_int.
  assert (Z.of_nat (nat_of_Z n) = n) by (apply nat_of_Z_eq; omega).
  remember (nat_of_Z n) as nn eqn:HH.
  revert n g HH H H0.
  induction nn; intros.
  + simpl in H0; subst. Z_and_int.
  + assert (Int.unsigned ofs + sizeof t * (n - 1) <= Int.modulus).
    - apply (IHnn (n - 1)).
      * Z_and_int.
        pose proof Zle_0_nat nn; omega.
      * subst.
        Z_and_int.
        replace (Z.of_nat nn + 1 - 1) with (Z.of_nat nn) by omega.
        rewrite nat_of_Z_of_nat; reflexivity.
      * intros.
        apply (H i ofs'); [omega | assumption].
      * subst. Z_and_int.
        omega.
    - Z_and_int. assert (0 <= n - 1 < n) by omega.
      pose proof H (n - 1) (Int.repr (Int.unsigned ofs + sizeof t * (n - 1))) H2.
      unfold add_ptr_int in H3; simpl in H3.
      Z_and_int.
      replace (Int.unsigned
               (Int.repr
                  (Int.unsigned (Int.repr (sizeof t)) *
                   Int.unsigned (Int.repr (n - 1))))) with 
              (Int.unsigned
               (Int.repr
                  (sizeof t * (n - 1)))) in H3.
      assert (

SearchAbout Z.of_nat nat_of_Z.
*)

Lemma data_at_array_at_aux: forall i t p n a,
  legal_alignas_type (Tarray t n a) = true ->
  size_compatible (Tarray t n a) p ->
  align_compatible (Tarray t n a) p ->
  0 <= i < 0 + Z.of_nat (nat_of_Z (n - 0)) ->
  isptr p -> 
  size_compatible t (add_ptr_int t p i) /\
  align_compatible t (add_ptr_int t p i).
Proof.
  intros.
  destruct p; inversion H3.
  rewrite <- Zminus_0_l_reverse in H2.
  rewrite nat_of_Z_max in H2.
  rewrite Zplus_0_l in H2.
  replace (Z.max n 0) with n in H2 by (
    destruct (Z.max_spec_le n 0) as [[? HH] | [? ?]]; [
    rewrite HH in H2; omega |
    auto]).
  destruct (add_ptr_int t (Vptr b i0) i) eqn:HH; inversion HH.
  subst b0.
  rewrite H6 in *.
  pose proof size_compatible_array_left _ _ _ _ _ _ _ H0 H2 HH.
  unfold size_compatible, align_compatible in *.
  rewrite legal_alignas_type_Tarray in H1 by exact H.
  rewrite H4.
  split; simpl in *.
  - rewrite Zplus_assoc_reverse, Zmult_succ_r_reverse.
    rewrite <- Z.add_1_r.
    assert (sizeof t * (i + 1) <= sizeof t * Z.max 0 n).
      pose proof Z.le_max_r 0 n.
      pose proof sizeof_pos t.
      apply Zmult_le_compat_l; omega.
    omega.
  - apply Z.divide_add_r; auto.
    apply Z.divide_mul_l, legal_alignas_sizeof_alignof_compat.
    eapply nested_pred_Tarray.
    exact H. omega.
Qed.

Lemma offset_in_range_size_compatible: forall n t a p,
  offset_in_range (sizeof t * n) p -> size_compatible (Tarray t n a) p.
Proof.
  intros.
  unfold offset_in_range in *.
  unfold size_compatible; simpl sizeof.
  destruct p; auto.
  destruct (zlt n 0); Z_and_int; omega.
Qed.

Lemma data_at_array_at: forall sh t n a v v', 
  JMeq v v' ->
  n >= 0 ->
  legal_alignas_type (Tarray t n a) = true ->
  data_at sh (Tarray t n a) v = 
  array_at t sh (ZnthV t v') 0 n.
Proof.
  intros.
  extensionality p.
  unfold array_at, data_at.
  simpl.
  unfold array_at', rangespec.
  apply pred_ext; normalize; apply andp_right.
  + apply prop_right.
    unfold align_compatible in *.
    rewrite legal_alignas_type_Tarray in H3 by assumption.
    unfold size_compatible in *; simpl sizeof in *.
    unfold offset_in_range.
    destruct p; auto.
    pose proof Int.unsigned_range i.
    rewrite Z.max_r in H2 by omega.
    pose proof sizeof_pos t.
    assert (0 <= sizeof t * n) by (apply Z.mul_nonneg_nonneg; omega).
    repeat split; auto; omega.
  + erewrite rangespec'_ext; [apply derives_refl|]; intros.
    simpl.
    rewrite andp_comm.
    rewrite <- add_andp; [rewrite H; reflexivity | apply prop_right].
    eapply data_at_array_at_aux; eassumption.
  + apply prop_right. unfold align_compatible in *.
    rewrite legal_alignas_type_Tarray by assumption.
    assert (size_compatible (Tarray t n a) p) by
      (apply offset_in_range_size_compatible; assumption).
    tauto.
  + erewrite rangespec'_ext; [apply derives_refl|]; intros.
    simpl.
    simpl in v.
    subst v.
    apply pred_ext; normalize.
    apply andp_right; [apply prop_right | cancel].
    eapply data_at_array_at_aux; try eassumption.
    - apply offset_in_range_size_compatible; assumption.
    - unfold align_compatible in *.
      rewrite legal_alignas_type_Tarray by assumption.
      assumption.
Qed.

Lemma array_at_ZnthV_nil:
  forall t sh, array_at t sh (ZnthV t nil) = array_at_ t sh.
Proof. intros.
unfold array_at_.
extensionality lo hi.
apply array_at_ext; intros.
unfold ZnthV. if_tac; auto. rewrite nth_overflow; auto.
simpl; omega.
Qed.

Lemma data_at__array_at_: forall sh t n a p, 
  n >= 0 ->
  legal_alignas_type (Tarray t n a) = true ->
  data_at_ sh (Tarray t n a) p = array_at_ t sh 0 n p.
Proof.
  intros.
  unfold data_at_.
  rewrite <- array_at_ZnthV_nil.
  erewrite data_at_array_at; [| reflexivity | omega | assumption].
  simpl default_val.
  reflexivity.
Qed.

Lemma semax_store_array:
  forall {Espec: OracleKind},
    forall Delta sh n P Q R Rn (e1 e2 : expr)
      (t t1: type) (contents: Z -> reptype t1) lo hi v1 v2,
      t1 = t ->
      type_is_by_value t ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) SEP  (Rn)) |--
        `(array_at t1 sh contents lo hi) v1 ->
      writable_share sh ->
      legal_alignas_type t1 = true ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (Ederef e1 t1)) && 
        local (tc_expr Delta (Ecast e2 t)) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (`(tc_val tint) v2) && 
        local (`(in_range lo hi) (`force_signed_int v2)) && 
        local (`eq (`(eval_binop Oadd (tptr t1) tint) v1 v2) (eval_expr e1)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (Ederef e1 t1) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(array_at t1 sh) 
                      (fun rho => upd contents (force_signed_int (v2 rho)) (valinject t1 (eval_expr (Ecast e2 t) rho)))
                        `lo `hi v1)
                      ))))).
Proof.
  intros.
  eapply semax_pre_post;
   [ | | eapply semax_deref_store_nth].
  + instantiate (1:= (`(array_at t1 sh contents lo) (`force_signed_int v2) v1) ::
      (`(data_at sh t1) (`contents (`force_signed_int v2)) (eval_expr e1)) ::
      (`(array_at t1 sh contents) (`Zsucc (`force_signed_int v2)) `hi v1) :: replace_nth n R emp).
    instantiate (1:= (tc_lvalue Delta (Ederef e1 t1)) :: (tc_expr Delta (Ecast e2 t)) :: (`(tc_val tint) v2) :: (`(in_range lo hi) (`force_signed_int v2)) ::
      (`eq (`(eval_binop Oadd (tptr t1) tint) v1 v2) (eval_expr e1)) :: Q).
    instantiate (1:=P).
    hoist_later_left.
    rewrite insert_local.
    apply later_derives.
    rewrite (add_andp _ _ H5).
    rewrite (add_andp _ _ H6).
    rewrite (replace_nth_nth_error R _ _ H1) at 1.
    change (lifted (LiftEnviron mpred)) with (environ -> mpred).
    rewrite !andp_assoc.
    eapply derives_trans; [eapply andp_derives; [apply replace_nth_SEP', H2 | apply derives_refl] |].
    rewrite (SEP_replace_nth_isolate _ _ _ _ H1) at 1.
    simpl; intro rho.
    normalize.
    repeat rewrite <- sepcon_assoc.
    apply sepcon_derives; [|apply derives_refl].
    rewrite <- H12.
    erewrite split3_array_at at 1; [|exact H11].
    unfold Basics.compose, force_val2.
    rewrite add_ptr_int_unfold by exact H10.
    apply derives_refl.
  + intros; apply andp_left2; apply normal_ret_assert_derives'.
    pose proof nth_error_replace_nth R n _ 
      (`(array_at t1 sh)
                     (fun rho =>
                      upd contents (force_signed_int (v2 rho))
                        (valinject t1 (eval_expr (Ecast e2 t) rho))) 
                     `lo `hi v1) H1.
    rewrite (SEP_nth_isolate _ _ _ H7).
    rewrite replace_nth_replace_nth.
    instantiate (7:= 1%nat); simpl; intros.
    normalize.
    repeat rewrite <- sepcon_assoc.
    apply sepcon_derives; [|apply derives_refl].
    erewrite (split3_array_at (force_signed_int (v2 x)) t1 sh (upd contents (force_signed_int (v2 x))
            (valinject t1
               (force_val1 (sem_cast (typeof e2) t) (eval_expr e2 x)))));
      [|exact H12].
    repeat apply sepcon_derives.
    - erewrite array_at_ext; [apply derives_refl|].
      intros.
      destruct (Z.eq_dec (force_signed_int (v2 x)) i).
      * subst i; omega.
      * rewrite upd_neq; [reflexivity|assumption].
    - instantiate (1:= t).
      rewrite <- H13.
      unfold Basics.compose, force_val2, force_val1.
      rewrite add_ptr_int_unfold. subst t1. 
      simpl.
      rewrite upd_eq.
      apply derives_refl.
      exact H11.
    - erewrite array_at_ext; [apply derives_refl|].
      intros.
      unfold Basics.compose in H15.
      destruct (Z.eq_dec (force_signed_int (v2 x)) i).
      * subst i. omega.
      * rewrite upd_neq; [reflexivity | assumption].
  + exact H.
  + exact H0.
  + reflexivity.
  + unfold_lift. simpl; intros.
    subst t1.
    eapply derives_trans; [| apply data_at_data_at_, H4].
    normalize.
  + exact H3.
  + simpl; intros; normalize.
Qed.

(*
Lemma semax_store_array':
  forall {Espec: OracleKind},
    forall Delta sh n P Q R Rn (e1 e2 : expr)
      (t t1: type) (contents: Z -> reptype t1) lo hi v v1 v2,
      t1 = t ->
      type_is_by_value t ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) SEP  (Rn)) |--
        `(array_at t1 sh contents lo hi) v1 ->
      writable_share sh ->
      legal_alignas_type t1 = true ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (Ederef e1 t1)) && 
        local (tc_expr Delta (Ecast e2 t)) ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (`(in_range lo hi v2)) && 
        local (`(eq (repinject t1 v)) (eval_expr (Ecast e2 t1))) &&
        local (`eq (`(eval_binop Oadd (tptr t1) tint) v1 `(Vint (Int.repr v2))) (eval_expr e1)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (Ederef e1 t1) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(array_at t1 sh (upd contents v2 v) lo hi) v1)))))).
Proof.
  intros.
  eapply semax_pre_post; [ | | eapply semax_store_array].
  + hoist_later_left.
    rewrite insert_local.
    rewrite (add_andp _ _ H6).
    apply later_derives.
    eapply derives_trans; [eapply andp_derives; [| apply derives_refl] |].
    {
      rewrite <- insert_local. apply andp_left2. apply derives_refl.
    }
    rewrite andp_comm.
    rewrite !andp_assoc.
    rewrite !insert_local.
    apply derives_refl.
  + intros; apply andp_left2; apply normal_ret_assert_derives'.
    instantiate (1:= v1).
    instantiate (1:= hi).
    instantiate (1:= lo).
    instantiate (1:= t1).
    instantiate (1:= `(Vint (Int.repr v2))).
    instantiate (1:= contents).
    instantiate (1:= sh).
    instantiate (1:= n).
    erewrite SEP_replace_nth_isolate by exact H1.
    erewrite SEP_replace_nth_isolate by exact H1.
    simpl; intro rho.
    normalize.
    rewrite <- H10.
    rewrite valinject_repinject by (subst t; exact H0).
    rewrite Int.signed_repr by admit. (* should be by omega, we can prove that by reasoning on the range of lo and hi *)
    cancel.
  + reflexivity.
  + subst t; exact H0.
  + exact H1.
  + eapply derives_trans; [| exact H2].
    simpl; intro; normalize.
  + exact H3.
  + subst t; exact H4.
  + subst t; eapply derives_trans; [| exact H5].
    simpl; normalize; intros.
  + simpl; normalize; intros.
    apply andp_right; apply prop_right.
    - simpl. admit. (* same reason; should be omega *)
    - exact H11.
Qed.
*)

Lemma semax_store_array':
  forall {Espec: OracleKind},
    forall Delta sh n P Q R (e1 e2 : expr)
      (t t1: type) (contents: Z -> reptype t1) lo hi v v1 v2,
      t1 = t ->
      type_is_by_value t ->
      nth_error R n = Some (`(array_at t1 sh contents lo hi) v1) ->
      writable_share sh ->
      legal_alignas_type t1 = true ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (Ederef e1 t1)) && 
        local (tc_expr Delta (Ecast e2 t)) ->
      PROPx P (LOCALx Q (SEPx (replace_nth n R (`(array_at_ t1 sh lo hi) v1) ))) |-- 
        local (`(in_range lo hi v2)) && 
        local (`(eq (repinject t1 v)) (eval_expr (Ecast e2 t1))) &&
        local (`eq (`(eval_binop Oadd (tptr t1) tint) v1 `(Vint (Int.repr v2))) (eval_expr e1)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (Ederef e1 t1) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(array_at t1 sh (upd contents v2 v) lo hi) v1)))))).
Proof.
Admitted.

Lemma semax_loadstore_array':
  forall {Espec: OracleKind},
 forall vi lo hi t1 (contents: Z -> reptype t1) v1 v2 (Delta: tycontext) e1 e2 sh P P', 
   writable_share sh ->
   reptype t1 = val -> 
   type_is_by_value t1 ->
   legal_alignas_type t1 = true ->
   typeof e1 = t1 ->
   tc_val t1 v2 ->
   in_range lo hi vi ->
   P |--  rel_lvalue e1  (eval_binop Oadd (tptr t1) tint v1 (Vint (Int.repr vi)) )
           && rel_expr (Ecast e2 t1) v2 
           && (`(array_at t1 sh contents lo hi v1) * P') ->
   @semax Espec Delta (|> P) (Sassign e1 e2) 
          (normal_ret_assert (`(array_at t1 sh (upd contents vi (valinject _ v2)) lo hi v1) * P')).
Proof.
intros until 2. intros BYVAL LAT H1 TCV RANGE H2.
  eapply semax_pre_post; [| | eapply semax_loadstore]; try eassumption.
  apply andp_left2; apply derives_refl.
 intros.
*
 apply andp_left2.
 apply normal_ret_assert_derives'.
 intro rho.
 unfold_lift; simpl.
  rewrite H1.
 match goal with |- ?A |-- _ => set (XX := A) end.
  rewrite (split3_array_at' vi t1 sh (upd contents vi (valinject t1 v2)) lo hi v1 v2); auto.
 2: rewrite upd_eq; apply valinject_JMeq; auto.
 rewrite (sepcon_comm (array_at t1 sh (upd contents vi (valinject t1 v2)) lo vi v1)).
 repeat rewrite sepcon_assoc.
 unfold XX; clear XX.
 apply derives_refl.
*
 rewrite H1.
 repeat rewrite prop_true_andp by auto.
 rewrite <- (andp_dup P).
 eapply derives_trans.
 apply andp_derives. apply H2. apply derives_refl.
(* normalize. *)
 apply andp_right.
 apply andp_right.
 apply andp_left1. apply andp_left1. apply andp_left1. apply derives_refl.
 apply andp_left1. apply andp_left1. apply andp_left2. apply derives_refl.
 intro rho. unfold_lift. simpl.
 apply andp_left1. apply andp_left2.
 rewrite (split3_array_at' vi t1 sh contents lo hi v1 (repinject _ (contents vi))); auto.
 rewrite (sepcon_comm (array_at t1 sh contents lo vi v1)).
 repeat rewrite sepcon_assoc.
 apply sepcon_derives.
 apply derives_refl.
 repeat rewrite <- sepcon_assoc.
 apply sepcon_derives; [ |  apply derives_refl].
 apply sepcon_derives; apply derives_refl'; apply equal_f; apply array_at_ext; intros;
 rewrite upd_neq by omega; auto.
 clear - H0 BYVAL.
 destruct t1; try contradiction.
 destruct i,s; reflexivity.
 destruct s; reflexivity.
 destruct f; reflexivity.
 reflexivity.
Qed.

Lemma semax_loadstore_array:
  forall {Espec: OracleKind},
 forall n vi lo hi t1 (contents: Z -> reptype t1) v1 v2 (Delta: tycontext) e1 ei e2 sh P Q R, 
  (*H0*) reptype t1 = val -> 
  (*H1*) type_is_by_value t1 ->
  (*H2*) legal_alignas_type t1 = true ->
  (*H3*) typeof e1 = tptr t1 ->
  (*H4*) typeof ei = tint ->
  (*H8*) PROPx P (LOCALx Q (SEPx R)) |--  rel_expr e1 v1 && rel_expr ei (Vint (Int.repr vi))
           && rel_expr (Ecast e2 t1) v2 ->
  (*H7*) nth_error R n = Some (`(array_at t1 sh contents lo hi v1)) ->
  (*H *) writable_share sh ->
  (*H5*) tc_val t1 v2 ->
  (*H6*) in_range lo hi vi ->
   @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R))) (Sassign (Ederef (Ebinop Oadd e1 ei (tptr t1)) t1) e2) 
          (normal_ret_assert 
           (PROPx P (LOCALx Q (SEPx 
            (replace_nth n R `(array_at t1 sh (upd contents vi (valinject _ v2)) lo hi v1)))))).
Proof.
intros until R.
intros H0 H1 H2 H3 H4 H8 H7 H H5 H6.
eapply semax_post_flipped'.
apply semax_loadstore_array'; eauto.
apply derives_trans with (!! isptr v1 && PROPx P (LOCALx Q (SEPx R))).
rewrite (SEP_nth_isolate _ _ _ H7).
repeat rewrite <- insert_SEP.
rewrite array_at_isptr. normalize.
normalize.
destruct v1; try contradiction.
instantiate (2:=v1).
simpl eval_binop. rewrite mul_repr.
apply andp_right; auto.
eapply derives_trans; [ apply H8 |].
intro rho. simpl.
repeat apply andp_right.
apply rel_lvalue_deref.
eapply rel_expr_binop.
repeat apply andp_left1. apply derives_refl.
apply andp_left1. apply andp_left2. apply derives_refl.
intro; rewrite H4; simpl. rewrite H3; simpl. 
  unfold Cop.sem_add; simpl. rewrite mul_repr. auto.
 apply andp_left2. auto.
rewrite (SEP_nth_isolate _ _ _ H7).
repeat rewrite <- insert_SEP.
apply derives_refl.
rewrite (SEP_replace_nth_isolate _ _ _ `(array_at t1 sh (upd contents vi (valinject t1 v2)) lo hi v1) H7).
rewrite insert_SEP.
auto.
Qed. 
 
Lemma rel_expr_array_load:
  forall ty sh (contents: Z -> reptype ty) lo hi v1 (i: Z) e1 e2 P  rho,
  typeof e1 = tptr ty ->
  typeof e2 = tint ->
  type_is_by_value ty ->
  P |--  rel_expr e1 v1 rho
        && rel_expr e2 (Vint (Int.repr i)) rho
         && (array_at ty sh contents lo hi v1 * TT)
         &&  !! (lo <= i < hi) 
         &&  !! tc_val ty (repinject _ (contents i)) ->
  P |--  rel_expr
      (Ederef
         (Ebinop Oadd e1 e2 (tptr ty)) ty) (repinject _ (contents i)) rho.
Proof.
intros.
eapply derives_trans; [eassumption | clear H2].
 rewrite array_at_isptr. normalize.
 destruct v1; try contradiction. rename i0 into ofs.
 destruct (access_mode_by_value _ H1) as [ch H1'].
 eapply rel_expr_lvalue_By_value with (ch:=ch); auto.
(* destruct ty; inv H1. try contradiction H1. reflexivity. *)
 apply rel_lvalue_deref.
 eapply rel_expr_binop.
 apply andp_left1. apply andp_left1. apply derives_refl.
 apply andp_left1. apply andp_left2. apply derives_refl.
 intro m. rewrite H, H0. simpl. unfold Cop.sem_add; simpl.
  rewrite mul_repr. reflexivity.
 repeat  apply andp_left2.
  rewrite (split3_array_at i ty sh contents lo hi) by omega.
  rewrite (sepcon_comm (array_at ty sh contents lo i (Vptr b ofs))).
  repeat rewrite sepcon_assoc.
  apply sepcon_derives; auto.
  instantiate (1:=sh).
   simpl typeof.
  unfold add_ptr_int. simpl. rewrite mul_repr.
  rewrite  (by_value_data_at sh ty (contents i) (repinject ty (contents i))); auto.
  apply andp_left2. auto.
  clear - H1.
  destruct ty; try contradiction; reflexivity.
  intro Hx; rewrite Hx in H2; clear Hx.
  apply tc_val_Vundef in H2; auto.
Qed.

Lemma repinject_default_val:
 forall t, repinject t (default_val t) = Vundef.
Proof.
destruct t; reflexivity.
Qed.

(*
Lemma array_at_array_at_:
 forall t sh f lo hi v, 
  array_at t sh f lo hi v |-- array_at_ t sh lo hi v.
Proof.
intros.
unfold array_at_.
assert (RP := sizeof_pos t).
unfold array_at; normalize.
unfold rangespec.
change nat_of_Z with Z.to_nat.
forget (Z.to_nat (hi-lo)) as n.
revert lo; induction n; intros.
apply derives_refl.
simpl.
apply sepcon_derives; auto.
eapply derives_trans; [apply data_at_data_at_ | ].
unfold data_at_.
unfold data_at.
auto.
Qed.
*)
(*Hint Resolve array_at_array_at_ : cancel.  doesn't work *)

Hint Extern 2 (array_at _ _ _ _ _ _ |-- array_at_ _ _ _ _ _) =>
  (apply array_at_array_at_; clear; simpl; congruence) : cancel.

Lemma split_array_at:
  forall (i : Z) (ty : type) (sh : Share.t) (contents : Z -> reptype ty)
    (lo hi : Z) (v : val),
  (lo <= i <= hi)%Z ->
  array_at ty sh contents lo hi v =
  array_at ty sh contents lo i v * array_at ty sh contents i hi v.
Proof.
intros.
  destruct (zlt i hi).
  + rewrite split3_array_at with (lo := lo) (hi := hi) (i := i) by omega.
    rewrite split3_array_at with (lo := i) (hi := hi) (i := i) by omega.
    unfold array_at, rangespec.
    rewrite Zminus_diag. simpl.
    apply pred_ext; normalize.
  + assert (i = hi) by omega. 
    subst.
    unfold array_at, rangespec.
    rewrite Zminus_diag. simpl.
    apply pred_ext; normalize.
Qed.

Lemma split_array_at_:
  forall (i : Z) (ty : type) (sh : Share.t)
    (lo hi : Z) (v : val),
  (lo <= i <= hi)%Z ->
  array_at_ ty sh lo hi v = array_at_ ty sh lo i v * array_at_ ty sh i hi v.
Proof.
intros.
unfold array_at_.
apply split_array_at.
auto.
Qed.

Lemma False_andp:
  forall {A}{NA: NatDed A} (P: A), !! False && P = FF.
Proof. intros. apply pred_ext; normalize. Qed.

Lemma offset_val_array_at:
 forall ofs t sh f lo hi v,
  legal_alignas_type t = true ->
  offset_strict_in_range (sizeof t * ofs) v ->
  array_at t sh (fun i => f (i-ofs)%Z)
               (ofs + lo) (ofs + hi) v =
  array_at t sh f lo hi (offset_val (Int.repr (sizeof t * ofs)) v).
Proof.
  intros.
  unfold array_at, rangespec.
  replace (ofs + hi - (ofs + lo))%Z
    with (hi-lo)%Z by omega.
  forget (nat_of_Z (hi-lo)) as n.
  replace (isptr (offset_val (Int.repr (sizeof t * ofs)) v)) with (isptr v)
    by (apply prop_ext; destruct v; intuition).
  assert (isptr v -> rangespec' (ofs + lo) n
      (fun i : Z => data_at sh t (f (i - ofs)) (add_ptr_int t v i)) =
      rangespec' lo n (fun i : Z =>
      data_at sh t (f i)
        (add_ptr_int t (offset_val (Int.repr (sizeof t * ofs)) v) i))).
  + clear hi.
    revert lo; induction n; simpl; intros; auto.
    replace (ofs+lo-ofs)%Z with lo by omega.
    destruct v; simpl; try tauto.
    f_equal. f_equal.
    unfold add_ptr_int; simpl. unfold sem_add; simpl.
    rewrite Int.add_assoc. f_equal.
    rewrite <- add_repr.
    rewrite <- mul_repr.
    rewrite Int.mul_add_distr_r.
    auto.
    replace (Z.succ (ofs + lo))%Z with (ofs + Z.succ lo)%Z by omega.
    specialize (IHn (Z.succ lo)).
    simpl in IHn. exact (IHn I).
  + unfold offset_in_range, offset_strict_in_range in *.
    destruct v; simpl offset_val in *; auto; apply pred_ext; normalize;
    (rewrite (H1 H5); apply andp_right; [apply prop_right | apply derives_refl]).
    - assert(Int.unsigned (Int.add i (Int.repr (sizeof t * ofs))) = Int.unsigned i + sizeof t * ofs).
      Focus 1. {
        unfold Int.add.
        rewrite !Int.unsigned_repr_eq.
        rewrite Zplus_mod_idemp_r.
        rewrite <- Int.unsigned_repr_eq.
        rewrite Int.unsigned_repr; [reflexivity|].
        unfold Int.max_unsigned.
        omega. } Unfocus.
      unfold align_compatible in *.
      rewrite !H8.
      rewrite <- !Zplus_assoc, <- !Z.mul_add_distr_l.
      repeat split; try omega.
      apply Z.divide_add_r, Z.divide_mul_l; [assumption|].
      apply legal_alignas_sizeof_alignof_compat; assumption.
    - assert(Int.unsigned (Int.add i (Int.repr (sizeof t * ofs))) = Int.unsigned i + sizeof t * ofs).
      Focus 1. {
        unfold Int.add.
        rewrite !Int.unsigned_repr_eq.
        rewrite Zplus_mod_idemp_r.
        rewrite <- Int.unsigned_repr_eq.
        rewrite Int.unsigned_repr; [reflexivity|].
        unfold Int.max_unsigned.
        omega. } Unfocus.
      unfold align_compatible in *.
      rewrite !H8 in *.
      rewrite <- !Zplus_assoc, <- !Z.mul_add_distr_l in *.
      repeat split; try omega.
      rewrite Zplus_comm in H2.
      eapply Z.divide_add_cancel_r; [|exact H2].
      apply Z.divide_mul_l.
      apply legal_alignas_sizeof_alignof_compat; assumption.
Qed.

Lemma array_at_emp:
  forall t sh f lo v, array_at t sh f lo lo v = !!isptr v && !!offset_in_range (sizeof t * lo) v && 
  !!align_compatible t v && emp.
Proof. intros. unfold array_at, rangespec.
replace (lo-lo) with 0 by omega.
simpl.
apply pred_ext; normalize.
Qed.

Lemma pick_prop_from_eq: forall (P: Prop) (Q R: mpred), (P -> Q = R) -> ((!! P) && Q = (!! P) && R).
Proof.
  intros.
  apply pred_ext; normalize.
  rewrite (H H0); apply derives_refl.
  rewrite (H H0); apply derives_refl.
Qed.

Lemma split_offset_array_at: forall (ty : type) (sh : Share.t) (contents : Z -> reptype ty)
         (z lo hi : Z) (v : val),
       z <= lo <= hi ->
       sizeof ty > 0 ->
       legal_alignas_type ty = true ->
       array_at ty sh contents z hi v =
       !! offset_in_range (sizeof ty * z) v &&
       !! offset_in_range (sizeof ty * hi) v &&
       array_at ty sh contents z lo v * 
       array_at ty sh (fun i => contents (i + lo)) 0 (hi - lo) 
       (offset_val (Int.repr (sizeof ty * lo)) v).
Proof.
  intros.
  assert (~ offset_strict_in_range (sizeof ty * lo) v \/
          offset_strict_in_range (sizeof ty * lo) v) by
    (unfold offset_strict_in_range; destruct v; auto; omega).
  destruct H2.
  + rewrite (add_andp (array_at ty sh contents z hi v) (!!offset_in_range (sizeof ty * hi) v)) by 
      (unfold array_at; normalize).
    rewrite (add_andp (array_at ty sh contents z hi v) (!!offset_in_range (sizeof ty * z) v)) by 
      (unfold array_at; normalize).
    rewrite andp_assoc.
    rewrite andp_comm.
    normalize.
    apply pick_prop_from_eq; intros.
    assert (lo = hi).
      assert (offset_in_range (sizeof ty * lo) v).
      apply offset_in_range_mid with (lo := z) (hi := hi); [omega | auto |auto].
      tauto.
      tauto.
      assert ((sizeof ty * lo)%Z <= (sizeof ty * hi)%Z) by (apply Z.mul_le_mono_nonneg_l; omega).
      unfold offset_in_range, offset_strict_in_range in *; destruct v; try tauto.
      apply (Z.mul_cancel_l) with (p := sizeof ty); omega.
    subst.
    replace (hi - hi) with 0 by omega.
    rewrite array_at_emp.
    unfold array_at; apply pred_ext; normalize.
    apply andp_right; [apply prop_right | apply derives_refl].
    unfold offset_in_range, offset_strict_in_range in *; destruct v; try tauto.
    unfold offset_val, Int.add, align_compatible.
    pose proof Int.unsigned_range i.
    rewrite !Int.unsigned_repr_eq.
    rewrite Zplus_mod_idemp_r.
    assert ((Int.unsigned i + sizeof ty * hi) = Int.modulus) by omega.
    rewrite H8.
    rewrite Z_mod_same_full.
    repeat split; auto; try omega.
    apply Z.divide_0_r.
  + rewrite split_array_at with (i := lo) (lo := z) (hi := hi) by omega.
    rewrite <- offset_val_array_at with (lo := 0) (hi := hi - lo) (ofs := lo) by assumption.
    rewrite (add_andp (array_at ty sh contents lo hi v) (!!offset_in_range (sizeof ty * hi) v)) by 
      (unfold array_at; normalize).
    rewrite (add_andp (array_at ty sh contents z lo v) (!!offset_in_range (sizeof ty * z) v)) at 1 by 
      (unfold array_at; normalize).
    normalize.
    f_equal.
    f_equal.
    f_equal; [| omega].
    extensionality.
    f_equal.
    omega.
Qed.

(* move this elsewhere *)
Lemma semax_pre_later:
 forall P' Espec Delta P1 P2 P3 c R,
     (PROPx P1 (LOCALx (tc_environ Delta :: P2) (SEPx P3))) |-- P' ->
     @semax Espec Delta (|> P') c R  -> 
     @semax Espec Delta (|> (PROPx P1 (LOCALx P2 (SEPx P3)))) c R.
Proof.
intros.
eapply semax_pre_simple; try apply H0.
eapply derives_trans; [ | apply later_derives; apply H ].
eapply derives_trans.
2: apply later_derives; rewrite <- insert_local; apply derives_refl.
rewrite later_andp; apply andp_derives; auto; apply now_later.
Qed.

Lemma sizeof_tarray_tuchar:
 forall (n:Z), (n>0)%Z -> (sizeof (tarray tuchar n) =  n)%Z.
Proof. intros.
 unfold sizeof,tarray; cbv beta iota.
  rewrite Z.max_r by omega.
  unfold alignof, tuchar; cbv beta iota.
  repeat  rewrite align_1. rewrite Z.mul_1_l. auto.
Qed.

Lemma memory_block_array_tuchar:
  forall sh n, (n>0)%Z -> memory_block sh (Int.repr n) = array_at_ tuchar sh 0 n.
Proof.
  intros.
  replace (Int.repr n) with (Int.repr (sizeof (tarray tuchar n))) by
   (unfold tarray; simpl; rewrite Z.max_r by omega; destruct n; reflexivity).
  assert (legal_alignas_type (Tarray tuchar n noattr) = true).
    unfold tuchar, legal_alignas_type.
    simpl; destruct (n <=? 0); reflexivity.
  assert (nested_non_volatile_type (Tarray tuchar n noattr) = true).
    unfold tuchar, nested_non_volatile_type.
    simpl; destruct (n <=? 0); reflexivity.
  extensionality. erewrite <- data_at__array_at_; [| omega | eassumption].
  rewrite <- memory_block_data_at_ by assumption.
Opaque sizeof.
  simpl. apply pred_ext; normalize.
  apply andp_right; [apply prop_right | apply derives_refl].
  apply align_1_compatible. reflexivity.
Transparent sizeof.
Qed.

Lemma memory_block_array_tuchar':
 forall sh n p, 
   isptr p ->
   (n>=0)%Z -> 
   memory_block sh (Int.repr n) p = array_at_ tuchar sh 0 n p.
Proof.
  intros.
  destruct p; try contradiction. clear H.
  assert (n=0 \/ n>0)%Z by omega.
  destruct H.
  + subst n.
    rewrite memory_block_zero.
    unfold array_at_, array_at. rewrite prop_true_andp by apply I.
    unfold rangespec;  simpl.
    apply pred_ext; normalize.
    apply andp_right; [apply prop_right | apply derives_refl].
    pose proof Int.unsigned_range i; repeat split; try omega.
    apply Z.divide_1_l.
  + apply equal_f; 
    apply memory_block_array_tuchar; auto.
Qed.

Lemma offset_val_array_at_:
 forall ofs t sh lo hi v,
  legal_alignas_type t = true ->
  offset_strict_in_range (sizeof t * ofs) v ->
  array_at_ t sh (ofs + lo) (ofs + hi) v =
  array_at_ t sh lo hi (offset_val (Int.repr (sizeof t * ofs)) v).
Proof.
intros.
unfold array_at_.
etransitivity; [ | apply offset_val_array_at; try assumption].
f_equal.
Qed.

