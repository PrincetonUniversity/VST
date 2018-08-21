Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.

Local Open Scope logic.

Lemma typed_true_nullptr:
 forall v t0 t t',
   typed_true t0 (force_val (sem_cmp Ceq (tptr t) (tptr t') v (Vint Int.zero))) ->
   v=nullval.
Proof.
 intros.
 simpl in H. rewrite !andb_false_r in H. simpl in H.
 unfold typed_true, force_val, sem_cmp_pp, strict_bool_val, nullval in *.
 destruct Archi.ptr64  eqn:Hp;
 destruct t0, v; inv H;
 unfold sem_cmp_pp, strict_bool_val in H1;
 try (clear i; rename i0 into i);
 pose proof (Int.eq_spec i Int.zero);
 destruct (Int.eq i Int.zero); inv H1; auto.
Qed.


Lemma typed_true_nullptr':
  forall  {cs: compspecs} t0  t t' v,
    typed_true t0 (eval_binop Cop.Oeq (tptr t) (tptr t') v nullval) -> v=nullval.
Proof.
 intros.
 simpl in H. unfold sem_binary_operation' in H.
 unfold tptr, typed_true, force_val, sem_cmp, Cop.classify_cmp, sem_cmp_pp, 
   typeconv, remove_attributes, change_attributes, strict_bool_val, nullval, Val.of_bool in *.
   rewrite (proj2 (eqb_type_false (Tpointer t noattr) int_or_ptr_type)) in H
     by (intro Hx; inv Hx).
   rewrite (proj2 (eqb_type_false (Tpointer t' noattr) int_or_ptr_type)) in H
     by (intro Hx; inv Hx).
   simpl in H.
 destruct Archi.ptr64  eqn:Hp;
 destruct t0, v; inv H;
 try solve [revert H1; simple_if_tac; intro H1; inv H1].
 pose proof (Int64.eq_spec i0 Int64.zero);
 destruct (Int64.eq i0 Int64.zero); inv H1; auto.
 pose proof (Int.eq_spec i0 Int.zero);
 destruct (Int.eq i0 Int.zero); inv H1; auto.
Qed.

Lemma typed_true_Oeq_nullval:
 forall  {cs: compspecs}  v t t',
   local (`(typed_true tint) (`(eval_binop Cop.Oeq (tptr t) (tptr t')) v `(nullval))) |--
   local (`(eq nullval) v).
Proof.
intros.
 intro rho; unfold local, lift1; unfold_lift.
 apply prop_derives; intro.
 unfold tptr in H; simpl in H. unfold sem_binary_operation' in H.
 simpl in H. rewrite !andb_false_r in H.
 destruct (v rho); inv H.
 unfold sem_cmp_pp, strict_bool_val, nullval in *.
 destruct Archi.ptr64  eqn:Hp; simpl in H1;
 try solve [inv H1];
 try solve [pose proof (Int64.eq_spec i Int64.zero);
                destruct (Int64.eq i Int64.zero); inv H1; auto];
 try solve [pose proof (Int.eq_spec i Int.zero);
                destruct (Int.eq i Int.zero); inv H1; auto].
Qed.

Definition  binary_operation_to_comparison (op: Cop.binary_operation) :=
 match op with
 | Cop.Oeq => Some (@eq Z)
 | Cop.One => Some Zne
 | Cop.Olt => Some Z.lt
 | Cop.Ole => Some Z.le
 | Cop.Ogt => Some Z.gt
 | Cop.Oge => Some Z.ge
 | _ => None
 end.

(*
Lemma typed_true_binop_int:
  forall op op' e1 e2 Espec  {cs: compspecs} Delta P Q R c Post,
   binary_operation_to_comparison op = Some op' ->
   typeof e1 = tint ->
   typeof e2 = tint ->
   (PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R))) |--  tc_expr Delta e1 ->
   (PROPx P (LOCALx (tc_env Delta :: Q) (SEPx R))) |-- tc_expr Delta e2 ->
  @semax cs Espec Delta (PROPx P (LOCALx
      (`op' (`force_signed_int (eval_expr e1)) (`force_signed_int (eval_expr e2))
          :: Q) (SEPx R))) c Post ->
  @semax cs Espec Delta (PROPx P (LOCALx
      (`(typed_true
          (typeof (Ebinop op e1 e2 tint)))
          (eval_expr (Ebinop op e1 e2 tint)) :: Q) (SEPx R))) c Post.
Proof.
intros.
eapply semax_pre; [clear H4 | apply H4].
eapply derives_trans with
 (tc_expr Delta e1 && (tc_expr Delta e2
   && PROPx P (LOCALx (tc_environ Delta :: `(typed_true (typeof (Ebinop op e1 e2 tint)))(eval_expr (Ebinop op e1 e2 tint)) :: Q) (SEPx R)))).
rewrite <- andp_assoc.
apply andp_right; auto.
do 2 rewrite <- insert_local.
rewrite <- andp_assoc.
rewrite (andp_comm (local _)).
rewrite andp_assoc.
apply andp_left2.
rewrite insert_local.
apply andp_right; auto.
clear H2 H3.
(*do 2 rewrite insert_local.*)
unfold PROPx, LOCALx; intro rho; simpl.
normalize.
autorewrite with norm1 norm2; normalize.
rewrite <- andp_assoc.
apply andp_derives; auto.
eapply derives_trans.
apply andp_derives; apply typecheck_expr_sound; auto.
normalize. split; auto.
rewrite H1,H0 in *.
clear H5 H2 H0 H1.
destruct (eval_expr e1 rho); inv H6.
destruct (eval_expr e2 rho); inv H7.
unfold force_signed_int, force_int.
unfold typed_true, eval_binop in H4.
destruct op; inv H; simpl in H4.
pose proof (Int.eq_spec i i0); destruct (Int.eq i i0); subst; auto.
 contradiction H4; auto.
unfold Zne.
pose proof (Int.eq_spec i i0); destruct (Int.eq i i0); subst; auto.
contradict H.
rewrite <- (Int.repr_signed i).
rewrite <- (Int.repr_signed i0).
f_equal; auto.
unfold Int.lt in H4.
destruct (zlt (Int.signed i) (Int.signed i0)); auto; contradict H4; auto.
unfold Int.lt in H4.
destruct (zlt (Int.signed i0) (Int.signed i)); auto; try omega; contradict H4; auto.
unfold Int.lt in H4.
destruct (zlt (Int.signed i0) (Int.signed i)); auto; try omega; contradict H4; auto.
unfold Int.lt in H4.
destruct (zlt (Int.signed i) (Int.signed i0)); auto; try omega; contradict H4; auto.
Qed.
*)

Definition  binary_operation_to_opp_comparison (op: Cop.binary_operation) :=
 match op with
 | Cop.Oeq => Some Zne
 | Cop.One => Some (@eq Z)
 | Cop.Olt => Some Z.ge
 | Cop.Ole => Some Z.gt
 | Cop.Ogt => Some Z.le
 | Cop.Oge => Some Z.lt
 | _ => None
 end.

(*
Lemma typed_false_binop_int:
  forall op op' e1 e2 Espec  {cs: compspecs} Delta P Q R c Post,
   binary_operation_to_opp_comparison op = Some op' ->
   typeof e1 = tint ->
   typeof e2 = tint ->
   (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))) |-- (tc_expr Delta e1) ->
   (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))) |-- (tc_expr Delta e2) ->
  @semax cs Espec Delta (PROPx P (LOCALx
      (`op' (`force_signed_int (eval_expr e1)) (`force_signed_int (eval_expr e2))
          :: Q) (SEPx R))) c Post ->
  @semax cs Espec Delta (PROPx P (LOCALx
      (`(typed_false
          (typeof (Ebinop op e1 e2 tint)))
          (eval_expr (Ebinop op e1 e2 tint)) :: Q) (SEPx R))) c Post.
Proof.
intros.
eapply semax_pre; [clear H4 | apply H4].
eapply derives_trans with
 ( local (tc_environ Delta) && ((tc_expr Delta e1) && ( (tc_expr Delta e2)
   && PROPx P (LOCALx (tc_environ Delta :: `(typed_false (typeof (Ebinop op e1 e2 tint)))(eval_expr (Ebinop op e1 e2 tint)) :: Q) (SEPx R))))).
apply andp_right.
rewrite <- insert_local. apply andp_left1; auto.
rewrite <- andp_assoc.
apply andp_right; auto.
do 2 rewrite <- insert_local.
rewrite <- andp_assoc.
rewrite (andp_comm (local _)).
rewrite andp_assoc.
apply andp_left2.
rewrite insert_local.
apply andp_right; auto.
clear H2 H3.
unfold PROPx, LOCALx; intro rho; simpl.
unfold local,lift1 at 1.
apply derives_extract_prop; intro TCE.
eapply derives_trans.
apply andp_derives; [ apply typecheck_expr_sound; auto | ].
apply andp_derives; [ apply typecheck_expr_sound; auto | ].
apply derives_refl.
normalize. autorewrite with norm1 norm2; normalize.
apply andp_right; auto. apply prop_right.
split; auto.
clear H6 TCE.
rewrite H0 in *; rewrite H1 in *.
clear H0 H1 H4.
destruct (eval_expr e1 rho); inv H2.
destruct (eval_expr e2 rho); inv H3.
unfold force_signed_int, force_int.
unfold typed_true, eval_binop in H5.
destruct op; inv H; simpl in H5.
pose proof (Int.eq_spec i i0); destruct (Int.eq i i0); inv H5; auto.
intro; apply H.
rewrite <- (Int.repr_signed i).
rewrite <- (Int.repr_signed i0).
f_equal; auto.
pose proof (Int.eq_spec i i0); destruct (Int.eq i i0); inv H5; auto.
unfold Int.lt in H5.
destruct (zlt (Int.signed i) (Int.signed i0)); inv H5; auto.
unfold Int.lt in H5.
destruct (zlt (Int.signed i0) (Int.signed i)); inv H5; omega.
unfold Int.lt in H5.
destruct (zlt (Int.signed i0) (Int.signed i)); inv H5; omega.
unfold Int.lt in H5.
destruct (zlt (Int.signed i) (Int.signed i0)); inv H5; omega.
Qed.
*)

Lemma typed_false_One_nullval:
 forall  {cs: compspecs}  v t t',
   local (`(typed_false tint) (`(eval_binop Cop.One (tptr t) (tptr t')) v `(nullval))) |--
    local (`(eq nullval) v).
Proof.
intros.
 intro rho; unfold local, lift1; unfold_lift.
 apply prop_derives; intro.
 simpl in H. unfold sem_binary_operation' in H.
 simpl in H. rewrite !andb_false_r in H.
 unfold sem_cmp_pp, nullval in *.
 destruct Archi.ptr64 eqn:Hp;
 destruct (v rho); inv H.
 pose proof (Int64.eq_spec i Int64.zero).
 destruct (Int64.eq i Int64.zero); inv H1.
 reflexivity.
 pose proof (Int.eq_spec i Int.zero).
 destruct (Int.eq i Int.zero); inv H1.
 reflexivity.
Qed.

Lemma typed_true_One_nullval:
 forall  {cs: compspecs}  v t t',
   local (`(typed_true tint) (`(eval_binop Cop.One (tptr t) (tptr t')) v `(nullval))) |--
   local (`(ptr_neq nullval) v).
Proof.
intros.
 intro rho; unfold local, lift1; unfold_lift.
 apply prop_derives; intro.
 simpl in H. unfold sem_binary_operation' in H.
 simpl in H. rewrite !andb_false_r in H.
 unfold sem_cmp_pp, ptr_neq, ptr_eq, nullval in *; simpl; intro.
 destruct (v rho); try contradiction.
 simpl in *.
 unfold typed_true, force_val, strict_bool_val in *.
 destruct Archi.ptr64 eqn:?; auto.
 destruct H0 as [? [? ?]].
 first [ pose proof (Int64.eq_spec Int64.zero i)
        | pose proof (Int.eq_spec Int.zero i)];
 rewrite H1 in H3; 
 subst; inv H.
Qed.


Lemma typed_false_Oeq_nullval:
 forall  {cs: compspecs} v t t',
   local (`(typed_false tint) (`(eval_binop Cop.Oeq (tptr t) (tptr t')) v `(nullval))) |--
   local (`(ptr_neq nullval) v).
Proof.
intros. subst.
 unfold_lift; intro rho.  unfold local, lift1; apply prop_derives; intro.
 simpl in H. unfold sem_binary_operation' in H.
 simpl in H. rewrite !andb_false_r in H.
 intro. apply ptr_eq_e in H0. rewrite <- H0 in H.
 inv H.
Qed.

Lemma local_entail_at:
  forall n S T (H: local (locald_denote S) |-- local (locald_denote T))
    P Q R,
    nth_error Q n = Some S ->
    PROPx P (LOCALx Q (SEPx R)) |--
    PROPx P (LOCALx (replace_nth n Q T) (SEPx R)).
Proof.
 intros.
 unfold PROPx, LOCALx; simpl; intro rho;  apply andp_derives; auto.
 apply andp_derives; auto.
 unfold local, lift1.
 specialize (H rho). unfold local,lift1 in H.
 revert Q H0; induction n; destruct Q; simpl; intros; inv H0.
 unfold_lift; repeat rewrite prop_and.
 apply andp_derives; auto.
  unfold_lift; repeat rewrite prop_and.
 apply andp_derives; auto.
Qed.

Lemma local_entail_at_semax_0:
  forall Espec {cs: compspecs}Delta P Q1 Q1' Q R c Post,
   local (locald_denote Q1) |-- local (locald_denote Q1') ->
   @semax cs Espec Delta (PROPx P (LOCALx (Q1'::Q) (SEPx R))) c Post  ->
   @semax cs Espec Delta (PROPx P (LOCALx (Q1::Q) (SEPx R))) c Post.
Proof.
intros.
eapply semax_pre0.
eapply (local_entail_at 0).
apply H. reflexivity.
auto.
Qed.

(*
Ltac simplify_typed_comparison :=
match goal with
| |- semax _ (PROPx _ (LOCALx (`(typed_true _) ?A :: _) _)) _ _ =>
 (eapply typed_true_binop_int;
   [reflexivity | reflexivity | reflexivity
   | try solve [go_lowerx; apply prop_right; auto ]
   | try solve [go_lowerx; apply prop_right; auto ]
   | ])
 ||
  (let a := fresh "a" in set (a:=A); simpl in a; unfold a; clear a;
   eapply local_entail_at_semax_0; [
    first [ apply typed_true_Oeq_nullval
           | apply typed_true_One_nullval
           ]
    |  ])
| |- semax _ (PROPx _ (LOCALx (`(typed_false _) ?A :: _) _)) _ _ =>
 (eapply typed_false_binop_int;
   [reflexivity | reflexivity | reflexivity
   | try solve [go_lowerx; apply prop_right; auto ]
   | try solve [go_lowerx; apply prop_right; auto ]
   | ])
 ||
  let a := fresh "a" in set (a:=A); simpl in a; unfold a; clear a;
   eapply local_entail_at_semax_0; [
    first [ apply typed_false_Oeq_nullval
           | apply typed_false_One_nullval
           ]
    |  ]
| |- _ => idtac
end.
*)

Definition compare_pp op p q :=
   match p with
            | Vptr b z =>
               match q with
               | Vptr b' z' => if eq_block b b'
                              then Vint (if Ptrofs.cmpu op z z' then Int.one else Int.zero)
                              else Vundef
               | _ => Vundef
               end
             | _ => Vundef
   end.

Lemma force_sem_cmp_pp:
  forall op p q,
  isptr p -> isptr q ->
  force_val (sem_cmp_pp op p q) =
   match op with
   | Ceq => Vint (if eq_dec p q then Int.one else Int.zero)
   | Cne => Vint (if eq_dec p q then Int.zero else Int.one)
   | _ => compare_pp op p q
   end.
Proof.
intros.
destruct p; try contradiction.
destruct q; try contradiction.
clear.
unfold sem_cmp_pp, compare_pp, Ptrofs.cmpu, Val.cmplu_bool.
destruct Archi.ptr64 eqn:Hp.
destruct op; simpl; auto.
if_tac. if_tac. inv H0. rewrite Ptrofs.eq_true; reflexivity.
rewrite Ptrofs.eq_false by congruence; reflexivity.
if_tac. congruence. reflexivity.
if_tac. if_tac. inv H0. rewrite Ptrofs.eq_true by auto. reflexivity.
rewrite Ptrofs.eq_false by congruence; reflexivity.
rewrite if_false by congruence. reflexivity.
if_tac; [destruct (Ptrofs.ltu i i0); reflexivity | reflexivity].
if_tac; [destruct (Ptrofs.ltu i0 i); reflexivity | reflexivity].
if_tac; [destruct (Ptrofs.ltu i0 i); reflexivity | reflexivity].
if_tac; [destruct (Ptrofs.ltu i i0); reflexivity | reflexivity].
destruct op; simpl; auto; rewrite Hp.
if_tac. if_tac. inv H0. rewrite Ptrofs.eq_true; reflexivity.
rewrite Ptrofs.eq_false by congruence; reflexivity.
if_tac. congruence. reflexivity.
if_tac. if_tac. inv H0. rewrite Ptrofs.eq_true by auto. reflexivity.
rewrite Ptrofs.eq_false by congruence; reflexivity.
rewrite if_false by congruence. reflexivity.
if_tac; [destruct (Ptrofs.ltu i i0); reflexivity | reflexivity].
if_tac; [destruct (Ptrofs.ltu i0 i); reflexivity | reflexivity].
if_tac; [destruct (Ptrofs.ltu i0 i); reflexivity | reflexivity].
if_tac; [destruct (Ptrofs.ltu i i0); reflexivity | reflexivity].
Qed.

Hint Rewrite force_sem_cmp_pp using (now auto) : norm.
