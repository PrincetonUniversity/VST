Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.compare_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.loadstore_lemmas.
Require Import Coq.Logic.JMeq.
Local Open Scope logic.

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
 f_equal. f_equal. apply prop_ext; intuition.
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
      Rn |-- `(data_at_ sh t) (eval_expr e1) ->
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

Lemma array_at_array_at_: forall t sh contents lo hi p,
  legal_alignas_type t = true ->
  array_at t sh contents lo hi p |-- array_at_ t sh lo hi p.
Proof.
  intros.
  unfold array_at_, array_at, rangespec.
  normalize.
  forget (nat_of_Z (hi - lo)) as m.
  revert lo; induction m; simpl; intros.
  + apply derives_refl.
  + apply sepcon_derives; [|apply IHm].
    eapply derives_trans; [apply data_at_data_at_, H|].
    unfold data_at_.
    apply derives_refl.
Qed.

Lemma replace_nth_replace_nth: forall {A: Type} R n {Rn Rn': A},
  replace_nth n (replace_nth n R Rn) Rn' = replace_nth n R Rn'.
Proof.
  intros.
  revert R; induction n; destruct R; simpl in *.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + rewrite IHn.
    reflexivity.
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

Lemma size_compatible_array: forall t n a i b ofs ofs',
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
Lemma size_compatible_max: forall t n a p,
  size_compatible (Tarray t n a) p ->
  size_compatible (Tarray t (Z.max 0 n) a) p.
Proof.
  intros.
  destruct p; auto.
  unfold size_compatible in *; simpl in *.
  replace (Z.max 0 (Z.max 0 n)) with (Z.max 0 n); auto.
  apply eq_sym, Z.max_r, Z.le_max_l.
Qed.

Lemma align_compatible_max: forall t n a p,
  align_compatible (Tarray t n a) p ->
  align_compatible (Tarray t (Z.max 0 n) a) p.
Proof.
  intros.
  destruct p; auto.
Qed.
*)

Lemma data_at_array_at: forall sh t n a v v' p, 
  JMeq v v' -> 
  legal_alignas_type (Tarray t n a) = true ->
  data_at sh (Tarray t n a) v p = 
  (!! (size_compatible (Tarray t n a) p)) &&
  array_at t sh (ZnthV t v') 0 n p.
Proof.
  intros.
  unfold array_at, data_at.
  simpl.
  unfold array_at', rangespec.

  apply pred_ext; normalize.
  + erewrite rangespec'_ext; [apply derives_refl|]; intros.
    simpl.
    rewrite andp_comm.
    rewrite <- add_andp; [rewrite H; reflexivity|].
    apply prop_right.
    destruct p; inversion Pp.
    rewrite <- Zminus_0_l_reverse in H3.
    rewrite nat_of_Z_max in H3.
    replace (0 + Z.max n 0) with (Z.max n 0) in H3 by omega.
    replace (Z.max n 0) with n in H3 by (
      destruct (Z.max_spec_le n 0) as [[? HH] | [? ?]]; [
      rewrite HH in H3; omega |
      auto]).
    destruct (add_ptr_int t (Vptr b i0) i) eqn:HH; inversion HH.
    subst b0.
    rewrite H6 in *.
    pose proof size_compatible_array _ _ _ _ _ _ _ H1 H3 HH.
    unfold size_compatible, align_compatible in *.
    rewrite legal_alignas_type_Tarray in H2 by exact H0.
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
      exact H0. omega.
  + admit.
  (* rangespec'_ext has bad specification. i in it should have a upper bound *)
Qed.

Lemma semax_store_array:
  forall {Espec: OracleKind},
    forall Delta sh n P Q R (e1 e2 : expr)
      (t t1: type) (contents: Z -> reptype t1) lo hi v1 v2,
      t1 = t ->
      type_is_by_value t ->
      nth_error R n = Some (`(array_at t1 sh contents lo hi) v1) ->
      writable_share sh ->
      legal_alignas_type t1 = true ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (Ederef e1 t1)) && 
        local (tc_expr Delta (Ecast e2 t)) ->
      PROPx P (LOCALx Q (SEPx (replace_nth n R (`(array_at_ t1 sh lo hi) v1) ))) |-- 
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
    instantiate (1:= (`(tc_val tint) v2) :: (`(in_range lo hi) (`force_signed_int v2)) ::
      (`eq (`(eval_binop Oadd (tptr t1) tint) v1 v2) (eval_expr e1)) :: Q).
    instantiate (1:=P).
    apply andp_left2; apply later_derives.
    rewrite (replace_nth_nth_error R _ _ H1) at 1.
    assert (`(array_at t1 sh contents lo hi) v1 |-- `(array_at_ t1 sh lo hi) v1) by
      (unfold liftx, lift; simpl; intros; apply array_at_array_at_, H3).
    pose proof replace_nth_SEP P Q R n _ _ H6.
    pose proof derives_trans _ _ _ H7 H5; clear H6 H7.
    change (lifted (LiftEnviron mpred)) with (environ -> mpred).
    rewrite (add_andp _ _ H8).
    rewrite (SEP_replace_nth_isolate _ _ _ _ H1) at 1.
    simpl; intros.
    normalize.
    repeat rewrite <- sepcon_assoc.
    apply sepcon_derives; [|apply derives_refl].
    rewrite <- H11.
    erewrite split3_array_at at 1; [|exact H10].
    unfold Basics.compose, force_val2.
    rewrite add_ptr_int_unfold by exact H9.
    auto.
  + intros; apply andp_left2; apply normal_ret_assert_derives'.
    pose proof nth_error_replace_nth R n _ 
      (`(array_at t1 sh)
                     (fun rho =>
                      upd contents (force_signed_int (v2 rho))
                        (valinject t1 (eval_expr (Ecast e2 t) rho))) 
                     `lo `hi v1) H1.
    rewrite (SEP_nth_isolate _ _ _ H6).
    rewrite replace_nth_replace_nth.
    instantiate (7:= 1%nat); simpl; intros.
    normalize.
    repeat rewrite <- sepcon_assoc.
    apply sepcon_derives; [|apply derives_refl].
    erewrite (split3_array_at (force_signed_int (v2 x)) t1 sh (upd contents (force_signed_int (v2 x))
            (valinject t1
               (force_val1 (sem_cast (typeof e2) t) (eval_expr e2 x)))));
      [|exact H9].
    repeat apply sepcon_derives.
    - erewrite array_at_ext; [apply derives_refl|].
      intros.
      destruct (Z.eq_dec (force_signed_int (v2 x)) i).
      * subst i; omega.
      * rewrite upd_neq; [reflexivity|assumption].
    - instantiate (1:= t).
      rewrite <- H10.
      unfold Basics.compose, force_val2, force_val1.
      rewrite add_ptr_int_unfold. subst t1. 
      simpl.
      rewrite upd_eq.
      apply derives_refl.
      exact H8.
    - erewrite array_at_ext; [apply derives_refl|].
      intros.
      unfold Basics.compose in H12.
      destruct (Z.eq_dec (force_signed_int (v2 x)) i).
      * subst i. omega.
      * rewrite upd_neq; [reflexivity|assumption].
  + exact H.
  + exact H0.
  + reflexivity.
  + unfold liftx, lift; simpl; intros.
    subst t1; apply data_at_data_at_, H3.
  + exact H2.
  + apply derives_trans with (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))).
    rewrite (SEP_nth_isolate _ _ _ H1).
    simpl; intros; normalize.
    repeat rewrite <- sepcon_assoc.
    apply sepcon_derives; [|apply derives_refl].
    unfold Basics.compose, force_val2.
    rewrite (split3_array_at (force_signed_int (v2 x)) t1 sh contents lo hi);
      [|exact H9].
    rewrite <- H10.
    unfold Basics.compose, force_val2.
    rewrite add_ptr_int_unfold; [|exact H8].
    apply derives_refl.
    exact H4.
Qed.

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
  intros.
  eapply semax_post'; [|eapply semax_store_array].
  + instantiate (1:= v1).
    instantiate (1:= hi).
    instantiate (1:= lo).
    instantiate (1:= t1).
    instantiate (1:= `(Vint (Int.repr v2))).
    instantiate (1:= contents).
    instantiate (1:= sh).
    instantiate (1:= n).
    match goal with
    | |- (?P |-- ?Q) => erewrite (add_andp P); [|eapply derives_trans; [|exact H5]]
    end.
    - erewrite SEP_replace_nth_isolate by exact H1.
      erewrite SEP_replace_nth_isolate by exact H1.
      simpl; normalize. intros. simpl.
      rewrite <- H10.
      rewrite valinject_repinject by (subst t; exact H0).
      rewrite Int.signed_repr by admit. (* should be by omega, we can prove that by reasoning on the range of lo and hi *)
      cancel.
    - erewrite SEP_replace_nth_isolate by exact H1.
      erewrite SEP_replace_nth_isolate by exact H1.
      simpl; normalize; intros.
      cancel. apply array_at_array_at_.
      exact H3.
  + reflexivity.
  + subst t; exact H0.
  + exact H1.
  + exact H2. 
  + exact H3.
  + subst t; exact H4.
  + eapply derives_trans; [exact H5|].
    simpl; normalize; intros.
    apply andp_right; apply prop_right.
    - simpl. admit. (* same reason; should be omega *)
    - exact H6.
Qed.

(*
Lemma semax_store_array:
forall Espec (Delta: tycontext) n sh t1 (contents: Z -> reptype t1)
              lo hi   
              (v1: environ-> val) P Q R            
             e1  e2 (v2: Z) (v: reptype t1),
    writable_share sh ->
    typeof e1 =  tptr t1 ->
    no_attr_type t1 = true ->
    type_is_by_value t1 -> (*repinject t1 = Some inject -> *)
    nth_error R n = Some (`(array_at t1 sh contents lo hi) v1) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
          local (`eq (`(eval_binop Oadd (tptr t1) tint) v1 `(Vint (Int.repr v2))) (eval_expr e1))
          && !! (in_range lo hi v2)
          && local (tc_expr Delta e1) && local (tc_expr Delta (Ecast e2 t1))
          && local (`(eq (repinject t1 v)) (eval_expr (Ecast e2 t1))) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sassign (Ederef e1 t1) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx (replace_nth n R
                    (`(array_at t1 sh (upd contents v2 v) lo hi) v1)))))).
Proof.
pose (H2:=True).
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
              `(eq (repinject t1 v)) (eval_expr (Ecast e2 t1)) :: 
             Q)
            (SEPx 
             (`(array_at t1 sh contents lo v2) v1 ::
             `(array_at t1 sh contents (Zsucc v2) hi) v1 :: R))))); auto].
* apply later_left2.
  rewrite insert_local.
  rewrite <- (andp_dup (PROPx _ _)).
  eapply derives_trans; [apply andp_derives; [apply derives_refl | apply H5] |  clear H5].
  go_lowerx.
  autorewrite with gather_prop.
  apply derives_extract_prop.
  intros [? [? [? [? ?]]]].
  saturate_local.
  apply andp_right; auto.
  apply prop_right.
  repeat split; auto.
  hnf. simpl. repeat rewrite denote_tc_assert_andp; repeat split; auto.
  rewrite H0; reflexivity. simpl. unfold_lift. rewrite <- H7; simpl.
  destruct (v1 rho); inv H12; apply I.
  rewrite (no_attr_type_nonvol _ H1); reflexivity.
  omega. omega.
  rewrite  (split3_array_at v2).
  cancel.
  unfold_lift. rewrite <- H7; simpl.
  destruct (v1 rho); inv H12. simpl.
  unfold add_ptr_int; simpl.
 rewrite by_value_data_at with (v' := (repinject t1 (contents v2))); [|assumption|admit].
 normalize; apply mapsto_mapsto_.
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
  rewrite upd_eq. 
  simpl.
  rewrite by_value_data_at with (v' := (repinject t1 v)); [|assumption|admit].
  rewrite (data_at_mapsto _ _ H3).
  destruct (eval_expr e1 rho); inv H12.
  destruct (v1 rho); inv H6.
  unfold add_ptr_int. simpl.
  rewrite H10. unfold_lift; simpl. auto.
  apply derives_refl'; apply equal_f; apply array_at_ext; intros.
  rewrite upd_neq by omega. auto. omega.
Qed.
*)

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
replace lo with (i-(i-lo)) in * by omega.
rewrite <- (Z2Nat.id (i-lo)) in * by omega.
forget (Z.to_nat (i-lo)) as n.
clear lo.
unfold array_at.
normalize.
assert (~isptr v \/ isptr v) by (destruct v; simpl; auto).
destruct H0.
apply pred_ext; normalize; contradiction.
repeat rewrite prop_true_andp by auto.
unfold rangespec.
set (f :=fun i0 : Z => data_at sh ty (contents i0) (add_ptr_int ty v i0)).
replace (i - (i - Z.of_nat n)) with (Z.of_nat n) by omega.
replace (hi - (i - Z.of_nat n)) with (Z.of_nat n + (hi-i)) by omega.
rewrite Z2Nat.inj_add by omega.
repeat rewrite Nat2Z.id.
induction n.
*
 change (Z.of_nat 0) with 0 in *.
 rewrite Z.sub_0_r in *. simpl. rewrite emp_sepcon; auto.
*
 unfold plus; fold plus.
unfold rangespec'; fold rangespec'.
 rewrite sepcon_assoc.
 f_equal.
 replace (Z.succ (i - Z.of_nat (S n))) with (i - Z.of_nat n) by (rewrite inj_S; omega).
 apply IHn.
 omega.
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
  array_at t sh (fun i => f (i-ofs)%Z)
               (ofs + lo) (ofs + hi) v =
  array_at t sh f lo hi (offset_val (Int.repr (sizeof t * ofs)) v).
Proof.
 intros.
unfold array_at, rangespec.
 replace (ofs + hi - (ofs + lo))%Z
   with (hi-lo)%Z by omega.
forget (nat_of_Z (hi-lo)) as n.
clear hi.
replace (isptr (offset_val (Int.repr (sizeof t * ofs)) v))
             with (isptr v)
 by (apply prop_ext; destruct v; intuition).
revert lo; induction n; simpl; intros; auto.
replace (ofs+lo-ofs)%Z with lo by omega.
unfold add_ptr_int; simpl. unfold sem_add; simpl.
destruct v; simpl; repeat rewrite False_andp; auto.
f_equal. f_equal.
rewrite Int.add_assoc.  f_equal.
rewrite <- add_repr.
rewrite <- mul_repr.
rewrite Int.mul_add_distr_r.
auto.
replace (Z.succ (ofs + lo))%Z with (ofs + Z.succ lo)%Z by omega.
specialize (IHn (Z.succ lo)).
simpl  in IHn. normalize in IHn.
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

Lemma array_at_ZnthV_nil:
  forall t sh, array_at t sh (ZnthV t nil) = array_at_ t sh.
Proof. intros.
unfold array_at_.
extensionality lo hi.
apply array_at_ext; intros.
unfold ZnthV. if_tac; auto. rewrite nth_overflow; auto.
simpl; omega.
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
 intros. replace (Int.repr n) with (Int.repr (sizeof (tarray tuchar n))).
  admit.
(*
 rewrite memory_block_typed by reflexivity.
 simpl_data_at. rewrite array_at_ZnthV_nil.
  auto.*)
  rewrite sizeof_tarray_tuchar; auto.
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
 subst n. 
 rewrite memory_block_zero.
 unfold array_at_, array_at. rewrite prop_true_andp by apply I.
 unfold rangespec;  simpl. reflexivity.
 apply equal_f; 
  apply memory_block_array_tuchar; auto.
Qed.

Lemma offset_val_array_at_:
 forall ofs t sh lo hi v,
  array_at_ t sh (ofs + lo) (ofs + hi) v =
  array_at_ t sh lo hi (offset_val (Int.repr (sizeof t * ofs)) v).
Proof.
intros.
unfold array_at_.
etransitivity; [ | apply offset_val_array_at].
f_equal.
Qed.

