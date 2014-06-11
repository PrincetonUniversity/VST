Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.canonicalize floyd.forward_lemmas floyd.call_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.loadstore_lemmas.
Require Import floyd.array_lemmas.
Require Import floyd.entailer.
Require Import floyd.globals_lemmas.
Import Cop.

Local Open Scope logic.

Lemma neutral_isCastResultType':  (* move this to veric.expr, to replace neutral_isCastResultType *)
  forall t t' v rho,
   is_neutral_cast t' t = true ->
   denote_tc_assert (isCastResultType t' t t v) rho.
Proof.
intros.
  unfold isCastResultType;
  destruct t',t; inv H; try apply I.
* destruct i,i0; inv H1; simpl; try apply I; if_tac; apply I.
* simpl. if_tac; apply I.
Qed.

Definition denote_local_ptree (P: PTree.t val) rho :=
  forall i v, PTree.get i P = Some v -> eval_id i rho = v.

Fixpoint msubst_eval_expr (P: PTree.t val) (e: expr) : environ -> val :=
 match e with
 | Econst_int i ty => `(Vint i)
 | Econst_long i ty => `(Vlong i)
 | Econst_float f ty => `(Vfloat f)
 | Etempvar id ty => match PTree.get id P with
                                 | Some v => `v
                                 | None => eval_id id 
                                 end
 | Eaddrof a ty => msubst_eval_lvalue P a 
 | Eunop op a ty =>  `(eval_unop op (typeof a)) (msubst_eval_expr P a) 
 | Ebinop op a1 a2 ty =>  
                  `(eval_binop op (typeof a1) (typeof a2)) (msubst_eval_expr P a1) (msubst_eval_expr P a2)
 | Ecast a ty => `(eval_cast (typeof a) ty) (msubst_eval_expr P a)
 | Evar id ty => `(deref_noload ty) (eval_var id ty)
 | Ederef a ty => `(deref_noload ty) (`force_ptr (msubst_eval_expr P a))
 | Efield a i ty => `(deref_noload ty) (`(eval_field (typeof a) i) (msubst_eval_lvalue P a))
 end

 with msubst_eval_lvalue (P: PTree.t val) (e: expr) : environ -> val := 
 match e with 
 | Evar id ty => eval_var id ty
 | Ederef a ty => `force_ptr (msubst_eval_expr P a)
 | Efield a i ty => `(eval_field (typeof a) i) (msubst_eval_lvalue P a)
 | _  => `Vundef
 end.

Lemma msubst_eval_expr_eq:
    forall P e rho, 
   denote_local_ptree P rho ->
   msubst_eval_expr P e rho = eval_expr e rho
with msubst_eval_lvalue_eq: 
    forall P e rho, 
      denote_local_ptree P rho ->
      msubst_eval_lvalue P e rho = eval_lvalue e rho.
Proof.
clear msubst_eval_expr_eq.
induction e; intros; simpl; try auto.
destruct (P ! i) eqn:?; auto.
apply H in Heqo.
unfold_lift; simpl.  auto.
unfold_lift. rewrite <- IHe; auto.
unfold_lift. rewrite <- IHe; auto.
unfold_lift. rewrite <- IHe1, <- IHe2; auto.
unfold_lift. rewrite <- IHe; auto.
unfold_lift. rewrite <- (msubst_eval_lvalue_eq P); auto.

clear msubst_eval_lvalue_eq.
induction e; intros; simpl; try auto.
unfold_lift. rewrite <- (msubst_eval_expr_eq P); auto.
unfold_lift. rewrite <- IHe; auto.
Qed.


Inductive local2ptree0 (j: ident) :
     list (environ -> Prop) -> PTree.t val -> list (environ -> Prop) -> Prop :=
| local2ptree0_nil:
       local2ptree0 j nil (PTree.empty _) nil
| local2ptree0_cons: forall i v Q P Q',
       i <> j ->
       local2ptree0 j Q P Q' ->
       local2ptree0 j (`(eq v) (eval_id i) :: Q) (PTree.set i v P) (`(eq v) (eval_id i):: Q').

Inductive local2ptree (j: ident):
     list (environ -> Prop) -> PTree.t val -> list (environ -> Prop) -> Prop :=
| local2ptree_nil: 
       local2ptree j nil (PTree.empty _) nil
| local2ptree_same: forall v Q P Q',
       local2ptree0 j Q P Q'->
       local2ptree j (`(eq v) (eval_id j) :: Q) (PTree.set j v P) Q'
| local2ptree_other: forall i v Q P Q',
       i <> j ->
       local2ptree j Q P Q' ->
       local2ptree j (`(eq v) (eval_id i) :: Q) (PTree.set i v P) (`(eq v) (eval_id i):: Q').

Lemma ptree_empty_some:
  forall {A i x}, 
    PTree.get i (PTree.empty A) = Some x -> False.
Proof.
intros. rewrite PTree.gempty in H; inv H.
Qed.

Lemma local2ptree_e:
 forall i v Q S Q',
   local2ptree i Q S Q' ->
    S ! i = Some v ->
     (fold_right `and `True Q = fold_right `and `True (`(eq v) (eval_id i) :: Q')) /\
     (forall j v' rho, fold_right `and `True Q rho ->
                            PTree.get j S = Some v' -> eval_id j rho = v') /\
       Forall (closed_wrt_vars (eq i)) Q'.
Proof.
intros.
split3.
*
extensionality rho.
assert (fold_right `and `True Q rho -> v = eval_id i rho). {
revert H0; induction H; simpl; intros.
 + contradiction (ptree_empty_some H0).
 + rewrite PTree.gss in H0; inv H0. destruct H1.
     apply H0.
 + rewrite PTree.gso in H1 by auto. destruct H2.
   auto.
}
revert H0 H1; induction H; simpl; intros.
contradiction (ptree_empty_some H0).
f_equal. rewrite PTree.gss in H0; inv H0.
auto.
clear - H; induction H; auto.
simpl; f_equal; auto.
rewrite PTree.gso in H1 by auto.
unfold_lift. apply prop_ext; intuition.
apply H2; auto.
unfold_lift. split; auto.
spec H3. intro; apply H2. unfold_lift. split; auto.
unfold_lift in H3. simpl in H3.
rewrite H3 in H6. destruct H6; auto.
unfold_lift in H6; simpl in H6; rewrite H6.
split; auto.
*
intros.
clear H0.
revert H1 H2; induction H; simpl; intros.
contradiction (ptree_empty_some H2).
destruct (ident_eq i j).
subst. rewrite PTree.gss in H2. inv H2.
destruct H1.
unfold_lift in H0. auto.
rewrite PTree.gso in H2 by auto.
destruct H1.
 unfold_lift in H1.
clear - n H1 H2 H.
revert n H1 H2; induction H; simpl; intros.
contradiction (ptree_empty_some H2).
destruct H1.
destruct (ident_eq i0 j). subst.
rewrite PTree.gss in H2. inv H2.
unfold_lift in H1; auto.
rewrite PTree.gso in H2 by auto.
apply IHlocal2ptree0; auto.
destruct H1.
destruct (ident_eq i0 j). subst.
rewrite PTree.gss in H2. inv H2. unfold_lift in H1; auto.
rewrite PTree.gso in H2 by auto.
apply IHlocal2ptree; auto.
*
clear H0.
induction H; auto with closed.
induction H; auto with closed.
Qed.
 
Lemma local2ptree_e0:
 forall i Q S Q',
   local2ptree i Q S Q' ->
    S ! i = None ->
     (Q = Q') /\
     (forall j v' rho, fold_right `and `True Q rho ->
                            PTree.get j S = Some v' -> eval_id j rho = v') /\
       Forall (closed_wrt_vars (eq i)) Q'.
Proof.
intros.
split3.
*
revert H0; induction H; simpl; intros; auto.
rewrite PTree.gss in H0; inv H0.
rewrite PTree.gso in H1 by auto. f_equal; auto.
*
intros.
clear H0.
revert H1 H2; induction H; simpl; intros.
contradiction (ptree_empty_some H2).
destruct (ident_eq i j).
subst. rewrite PTree.gss in H2. inv H2.
destruct H1.
unfold_lift in H0. auto.
rewrite PTree.gso in H2 by auto.
destruct H1.
 unfold_lift in H1.
clear - n H1 H2 H.
revert n H1 H2; induction H; simpl; intros.
contradiction (ptree_empty_some H2).
destruct H1.
destruct (ident_eq i0 j). subst.
rewrite PTree.gss in H2. inv H2.
unfold_lift in H1; auto.
rewrite PTree.gso in H2 by auto.
apply IHlocal2ptree0; auto.
destruct H1.
destruct (ident_eq i0 j). subst.
rewrite PTree.gss in H2. inv H2. unfold_lift in H1; auto.
rewrite PTree.gso in H2 by auto.
apply IHlocal2ptree; auto.
*
clear H0.
induction H; auto with closed.
induction H; auto with closed.
Qed.

Lemma msubst_expr:
    forall S i v e rho, 
    S ! i = Some v ->
   msubst_eval_expr S e rho = msubst_eval_expr S e (env_set rho i v)
with msubst_lvalue: 
    forall S i v e rho, 
    S ! i = Some v ->
    msubst_eval_lvalue S e rho = msubst_eval_lvalue S e (env_set rho i v).
Proof.
clear msubst_expr.
induction e; intros; simpl; try auto.
destruct (ident_eq i0 i). subst. rewrite H. reflexivity.
destruct (S ! i0) eqn:?; auto.
unfold eval_id; simpl. rewrite Map.gso; auto.
unfold_lift. rewrite <- IHe; auto.
unfold_lift. rewrite <- IHe; auto.
unfold_lift. rewrite <- IHe1, <- IHe2; auto.
unfold_lift. rewrite <- IHe; auto.
unfold_lift. rewrite <- (msubst_lvalue S); auto.

clear msubst_lvalue.
induction e; intros; simpl; try auto.
unfold_lift. rewrite <- (msubst_expr S); auto.
unfold_lift. rewrite <- IHe; auto.
Qed.

Lemma forward_setx_wow:
  forall S (v: val) Q' Espec Delta P Q R i e,
  Forall (closed_wrt_vars (eq i)) R ->
  local2ptree i Q S Q' ->
  match S ! i with Some _ => True | None => closed_eval_expr i e = true end ->
  msubst_eval_expr S e = `v ->
  (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
          local (tc_expr Delta e) && local (tc_temp_id i (typeof e) Delta e) ) ->
  @semax Espec Delta
             (PROPx P (LOCALx Q (SEPx R)))
             (Sset i e)
             (normal_ret_assert
              (PROPx P (LOCALx (`(eq v) (eval_id i) :: Q') (SEPx R)))).
Proof.
intros.
eapply semax_post; [ | apply forward_setx; auto].
intros.
apply andp_left2.
apply normal_ret_assert_derives'.
apply exp_left; intro old.
clear H3.
apply andp_derives; auto.
apply andp_derives;
 [ | unfold SEPx; rewrite closed_wrt_map_subst; auto].
unfold local,lift1. intro rho; apply prop_derives.
change (`(eq v)) with (`eq `v).
forget (`v) as e'. clear v.
subst e'.
intros [? ?].
destruct (S!i) eqn:H4; [clear H1 | rename H1 into H9].
*
apply (local2ptree_e i v) in H0; auto.
destruct H0 as [? [? ?]].
assert (fold_right `and `True Q (env_set rho i old)). {
 clear - H3.
 induction Q; destruct H3; simpl; split; auto.
}
split.
Focus 2. {
rewrite H0 in H6.
destruct H6.
clear - H5 H7.
induction Q'; auto.
inv H5.
destruct H7; split; auto.
clear - H1 H.
unfold env_set in H.
hnf in H1.
rewrite (H1 rho (Map.set i old (te_of rho))); auto.
intros.
destruct (ident_eq i i0); auto. right.
rewrite Map.gso; auto.
} Unfocus.
unfold_lift.
unfold_lift in H2.
rewrite H2. unfold subst.
assert (old = v).
specialize (H1 i v _ H6 H4).
unfold eval_id, env_set in H1; simpl in H1. rewrite Map.gss in H1.
inv H1. reflexivity.
subst old.
rewrite <- (msubst_eval_expr_eq S e).
Focus 2. {
hnf; intros. destruct (ident_eq i i0). subst. unfold eval_id. simpl. rewrite Map.gss.
simpl; congruence.
unfold eval_id; simpl. rewrite Map.gso by auto.
specialize (H1 _ _ _ H6 H7).
unfold eval_id in H1; simpl in H1; rewrite Map.gso in H1 by auto.
auto.
} Unfocus.
apply msubst_expr; auto.
*
apply (local2ptree_e0 i) in H0; auto.
destruct H0 as [? [? ?]].
subst Q'.
split.
Focus 2. {
clear - H5 H3.
induction Q; auto.
inv H5.
destruct H3; split; auto.
clear - H1 H.
unfold subst, env_set in H.
hnf in H1.
rewrite (H1 rho (Map.set i old (te_of rho))); auto.
intros.
destruct (ident_eq i i0); auto. right.
rewrite Map.gso; auto.
} Unfocus.
unfold_lift.
unfold_lift in H2.
rewrite msubst_eval_expr_eq; auto.
apply closed_eval_expr_e in H9.
rewrite H2.
autorewrite with subst.
auto.
hnf; intros; apply H1; auto.
clear - H3 H5.
induction Q; auto.
inv H5; destruct H3; split; auto.
autorewrite with subst in H; auto.
Qed.

Lemma forward_setx_wow_seq:
  forall S (v: val) Q' Delta' Espec Delta P Q R i e c Post,
  Forall (closed_wrt_vars (eq i)) R ->
  local2ptree i Q S Q' ->
  match S ! i with Some _ => True | None => closed_eval_expr i e = true end ->
  msubst_eval_expr S e = `v ->
  initialized i Delta = Delta' ->
  (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
          local (tc_expr Delta e) && local (tc_temp_id i (typeof e) Delta e) ) ->
  @semax Espec Delta'  (PROPx P (LOCALx (`(eq v) (eval_id i) :: Q') (SEPx R)))
                          c Post ->
  @semax Espec Delta
             (PROPx P (LOCALx Q (SEPx R)))
             (Ssequence (Sset i e) c)
             Post.
Proof.
intros.
eapply semax_seq'.
eapply forward_setx_wow; eassumption.
subst Delta'; simpl; apply H5.
Qed.

Ltac simpl_lift := 
 repeat 
 match goal with
 | |- context [@liftx (Tarrow val (LiftEnviron val)) ?f
                                                         (@liftx (LiftEnviron val) ?v1)] =>
   change (@liftx (Tarrow val (LiftEnviron val)) f
                                                         (@liftx (LiftEnviron val) v1))
   with (`(f v1)); simpl force_val1; simpl eval_unop
 | |- context [@liftx (Tarrow val (Tarrow val (LiftEnviron val))) ?f
                                                         (@liftx (LiftEnviron val) ?v1)
                                                         (@liftx (LiftEnviron val) ?v2)] =>
   change (@liftx (Tarrow val (Tarrow val (LiftEnviron val))) f
                                                         (@liftx (LiftEnviron val) v1)
                                                         (@liftx (LiftEnviron val) v2))
   with (`(f v1 v2)); simpl force_val2; simpl eval_binop
 end.

Lemma refold_andp:  (* MOVE elsewhere? *)
  forall (P Q: environ -> mpred),
     (fun rho: environ => P rho && Q rho) = (P && Q).
Proof. reflexivity. Qed.
Hint Rewrite refold_andp : norm.

Lemma eval_var_env_set:
  forall i t j v (rho: environ), eval_var i t (env_set rho j v) = eval_var i t rho.
Proof. reflexivity. Qed.

Lemma elim_globals_only:
  forall Delta g i t rho,
  tc_environ Delta rho /\ (var_types Delta) ! i = None /\ (glob_types Delta) ! i = Some g ->
  eval_var i t (globals_only rho) = eval_var i t rho.
Proof.
intros. 
destruct H as [H [H8 H0]].
unfold eval_var, globals_only.
simpl. 
destruct H as [_ [? [? ?]]].
destruct (H2 i g H0).
unfold Map.get; rewrite H3; auto.
destruct H3.
congruence.
Qed.

Hint Rewrite eval_var_env_set : norm. (* MOVE elsewhere? *)

Arguments Int.unsigned n : simpl never.

(* Move these elsewhere *)
Arguments Pos.to_nat !x / .

Ltac simpl_stackframe_of := 
  unfold stackframe_of, fn_vars; simpl map; unfold fold_right; rewrite sepcon_emp;
  repeat rewrite var_block_data_at_ by reflexivity;
  repeat rewrite prop_true_andp by (simpl sizeof; computable).

Lemma PROP_LOCAL_SEP_f:
  forall P Q R f, `(PROPx P (LOCALx Q (SEPx R))) f =
     PROPx P (LOCALx (map (fun q : environ -> Prop => `q f) Q)
            (SEPx (map (fun r : environ -> mpred => `r f) R))).
Proof. intros. extensionality rho.
unfold_for_go_lower.
simpl. f_equal. f_equal.
f_equal.
induction Q; simpl; auto. f_equal; auto.
induction R; simpl; auto. f_equal; auto.
Qed.
Hint Rewrite PROP_LOCAL_SEP_f: norm.

Lemma SEP_PROP:
 forall P Q R P' Q' R', 
     PROPx P (LOCALx Q (SEPx (PROPx P' (LOCALx Q' (SEPx R')) :: R))) =
    PROPx (P++P') (LOCALx (Q++Q') (SEPx (R'++R))).
Proof.
intros.
unfold_for_go_lower; extensionality rho.
apply pred_ext; normalize.
rewrite prop_true_andp.
rewrite prop_true_andp; auto.
clear; induction R'; simpl; normalize.
rewrite sepcon_assoc; apply sepcon_derives; auto.
revert H0; induction Q; simpl; intros; auto.
destruct H0; split; auto.
induction P; simpl; auto. destruct H; split; auto.
rewrite prop_true_andp.
rewrite prop_true_andp.
rewrite prop_true_andp.
rewrite prop_true_andp.
induction R'; simpl. normalize.
rewrite sepcon_assoc; apply sepcon_derives; auto.
induction Q; simpl; auto. destruct H0. auto.
induction P; simpl; auto. destruct H; auto.
induction Q; simpl; auto.
destruct H0; split; auto.
induction P; simpl; auto. destruct H; split; auto.
Qed.
Hint Rewrite SEP_PROP: norm.

Lemma simpl_get_result1:
 forall (f: val -> Prop) i, @liftx (Tarrow environ (LiftEnviron Prop)) (@liftx (Tarrow val (LiftEnviron Prop))f retval) (get_result1 i) = `f (eval_id i).
Proof.
intros; extensionality rho.
unfold_lift; unfold retval, get_result1.
f_equal.
Qed.
Hint Rewrite simpl_get_result1: norm.

Hint Rewrite @subst_lift0' : subst.
Hint Rewrite @subst_lift0' : norm.

Definition not_conj_notation (P: Prop) := True.

Ltac not_conj_notation :=
 match goal with 
 | |- not_conj_notation (_ <= _ <= _)%Z => fail 1
 | |- not_conj_notation (_ <= _ < _)%Z => fail 1
 | |- not_conj_notation (_ < _ <= _)%Z => fail 1
 | |- not_conj_notation (_ <= _ <= _)%nat => fail 1
 | |- not_conj_notation (_ <= _ < _)%nat => fail 1
 | |- not_conj_notation (_ < _ <= _)%nat => fail 1
 | |- _ => apply I
 end.

Lemma split_first_PROP:
  forall P Q R S, 
  not_conj_notation (P/\Q) ->
  PROPx ((P/\Q)::R) S = PROPx (P::Q::R) S.
Proof.
intros. unfold PROPx; simpl.
extensionality rho.
apply pred_ext; apply andp_derives; auto;
  apply prop_derives; intuition.
Qed.
Hint Rewrite split_first_PROP using not_conj_notation : norm.

Lemma semax_frame1:
 forall {Espec: OracleKind} Frame Delta Delta1
     P Q c R P1 Q1 R1 P2 Q2 R2,
    semax Delta1 (PROPx P1 (LOCALx Q1 (SEPx R1))) c 
                      (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx R2)))) ->
    Delta1 = Delta ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
    PROPx P1 (LOCALx Q1 (SEPx (R1 ++ Frame))) ->
    closed_wrt_modvars c (SEPx Frame) ->
    semax Delta (PROPx P (LOCALx Q (SEPx R))) c 
                      (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx (R2++Frame))))).
Proof.
intros. subst.
eapply semax_pre.
apply H1.
apply semax_frame_PQR; auto.
Qed.

(* end of "stuff to move elsewhere" *)

Tactic Notation "abbreviate" constr(y) "as"  ident(x)  :=
   (first [ is_var y 
           |  let x' := fresh x in pose (x':= @abbreviate _ y); 
              replace y with x' by reflexivity]).

Tactic Notation "abbreviate" constr(y) ":" constr(t) "as"  ident(x)  :=
   (first [ is_var y 
           |  let x' := fresh x in pose (x':= @abbreviate t y); 
               replace y with x' by reflexivity]).

Ltac unfold_abbrev :=
  repeat match goal with H := @abbreviate _ _ |- _ => 
                        unfold H, abbreviate; clear H 
            end.

Ltac unfold_abbrev_ret :=
  repeat match goal with H := @abbreviate ret_assert _ |- _ => 
                        unfold H, abbreviate; clear H 
            end.

Ltac unfold_abbrev_commands :=
  repeat match goal with H := @abbreviate statement _ |- _ => 
                        unfold H, abbreviate; clear H 
            end.

Ltac clear_abbrevs :=  repeat match goal with H := @abbreviate _ _ |- _ => clear H end.

Arguments var_types !Delta / .

Ltac simplify_Delta_core H := 
 repeat match type of H with _ =  ?A => unfold A in H end;
 cbv delta [abbreviate update_tycon func_tycontext] in H; simpl in H;
 repeat
  (first [
          unfold initialized at 15 in H
        | unfold initialized at 14 in H
        | unfold initialized at 13 in H
        | unfold initialized at 12 in H
        | unfold initialized at 11 in H
        | unfold initialized at 10 in H
        | unfold initialized at 9 in H
        | unfold initialized at 8 in H
        |unfold initialized at 7 in H
        |unfold initialized at 6 in H
        |unfold initialized at 5 in H
        |unfold initialized at 4 in H
        |unfold initialized at 3 in H
        |unfold initialized at 2 in H
        |unfold initialized at 1 in H];
   simpl in H);
 unfold initialized in H;
 simpl in H.

Ltac simplify_Delta_from A :=
 let d := fresh "d" in let H := fresh in 
 remember A as d eqn:H;
 simplify_Delta_core H;
 match type of H with (d = ?A) => apply A end.

Ltac simplify_Delta_at A :=
 match A with
 | (_,_,_,_) => idtac
 | _ => let d := fresh "d" in let H := fresh in 
       remember A as d eqn:H;
       simplify_Delta_core H;
       subst d
 end.

Ltac simplify_Delta := 
 match goal with 
| |- semax ?D _ _ _ =>
            simplify_Delta_at D
| |- PROPx _ (LOCALx (tc_environ ?D :: _) _) |-- _ =>
            simplify_Delta_at D
| |- ?A = _ => unfold A, abbreviate
| |- _ = ?B => unfold B, abbreviate
| |- ?A = ?B =>
     simplify_Delta_at A; simplify_Delta_at B; reflexivity
end.

Ltac abbreviate_semax :=
 match goal with
 | |- semax _ _ _ _ => 
        unfold_abbrev;
        simplify_Delta;
        match goal with |- semax ?D _ ?C ?P => 
            abbreviate D : tycontext as Delta;
            abbreviate P : ret_assert as POSTCONDITION;
            match C with
            | Ssequence ?C1 ?C2 =>
                abbreviate C2 as MORE_COMMANDS;
                match C1 with
                | Swhile _ ?C3 => abbreviate C3 as LOOP_BODY
                | _ => idtac
                end
            | Swhile _ ?C3 => abbreviate C3 as LOOP_BODY
            | _ => idtac
            end
        end
 | |- _ |-- _ => unfold_abbrev_ret
 | |- _ => idtac
 end;
 clear_abbrevs;
 simpl typeof.

Definition query_context Delta id :=
     match ((temp_types Delta) ! id) with 
      | Some _ => (temp_types Delta) ! id =
                  (temp_types Delta) ! id
      | None => 
        match (var_types Delta) ! id with
          | Some _ =>   (var_types Delta) ! id =
                        (var_types Delta) ! id
          | None =>
            match (glob_types Delta) ! id with
              | Some _ => (var_types Delta) ! id =
                          (var_types Delta) ! id
              | None => (temp_types Delta) ! id = None /\
                        (var_types Delta) ! id = None /\
                        (glob_types Delta) ! id = None
            end
        end
    end.


Lemma is_and : forall A B,
A /\ B -> A /\ B.
Proof.
auto.
Qed.

Ltac solve_query_context :=
unfold query_context; simpl; auto.


Ltac query_context Delta id :=
let qu := fresh "QUERY" in
assert (query_context Delta id) as qu by solve_query_context;
hnf in qu;
first [apply is_and in qu |
simpl PTree.get at 2 in qu].

(* BEGIN HORRIBLE1.
  The following lemma is needed because CompCert clightgen
 produces the following AST for function call:
  (Ssequence (Scall (Some id') ... ) (Sset id (Etempvar id' _)))
instead of the more natural
   (Scall id ...)
Our general tactics are powerful enough to reason about the sequence,
one statement at a time, but it is not nice to burden the user with knowing
about id'.  So we handle it all in one gulp.
 
The lemma goes here, because it imports from both forward_lemmas and call_lemmas.

 See also BEGIN HORRIBLE1 , later in this file
*)

Lemma semax_call_id1_x:
 forall Espec Delta P Q R ret ret' id retty retty' bl argsig A x Pre Post
   (GLBL: (var_types Delta) ! id = None),
   (glob_types Delta) ! id = Some (Global_func (mk_funspec (argsig,retty') A Pre Post)) ->
   match retty' with Tvoid => False | Tcomp_ptr _ _ => False | Tarray _ _ _ => False | _ => True end ->
  forall
   (CLOSQ: Forall (closed_wrt_vars (eq ret')) Q)
   (CLOSR: Forall (closed_wrt_vars (eq ret')) R),
   type_is_volatile retty' = false -> 
   (temp_types Delta) ! ret' = Some (retty', false) ->
   is_neutral_cast retty' retty = true ->
   match (temp_types Delta) ! ret with Some (t,_) => eqb_type t retty | None => false end = true ->
  @semax Espec Delta (PROPx P (LOCALx (tc_exprlist Delta (argtypes argsig) bl :: Q) 
                                     (SEPx (`(Pre x) (make_args' (argsig,retty') (eval_exprlist (argtypes argsig) bl)) :: R))))
    (Ssequence (Scall (Some ret')
             (Evar id (Tfunction (type_of_params argsig) retty' cc_default))
             bl)
      (Sset ret (Etempvar ret' retty')))
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (`old)) Q) 
             (SEPx (`(Post x) (get_result1 ret) :: map (subst ret (`old)) R))))).
Proof.
 pose (H1:=True); pose (H2:=True).

 intros. rename H3 into NONVOL.
 eapply semax_seq';
 [assert (H0':    match retty' with Tvoid => False | _ => True end)
  by (clear - H0; destruct retty'; try contradiction; auto);
   apply (semax_call_id1' _ _ P Q R _ _ _ bl _ _ x _ _ GLBL H H0'); auto
 | ].
simpl. rewrite H4; auto.
match goal with |- semax ?D (PROPx ?P ?QR) ?c ?Post =>
   assert ( (fold_right and True P) -> semax D (PROPx nil QR) c Post)
 end.
Focus 2. {
 clear - H3.
 unfold PROPx. 
 unfold PROPx at 1 in H3.
 normalize in H3.
 apply semax_extract_prop. apply H3.
} Unfocus.
 intro.
 apply semax_post_flipped
 with (normal_ret_assert (EX  x0 : val,
PROP  ()
(LOCALx
   (tc_environ
      (initialized ret
         (update_tycon Delta
            (Scall (Some ret') (Evar id (Tfunction (type_of_params argsig) retty' cc_default)) bl)))
    :: `eq (eval_id ret)
         (subst ret (`x0) (eval_expr (Etempvar ret' retty')))
       :: map (subst ret (`x0)) Q)
   (SEPx
      (map (subst ret (`x0)) (`(Post x) (get_result1 ret') :: R)))))).
  make_sequential;
          eapply semax_post_flipped;
          [ apply forward_setx; 
            try solve [intro rho; rewrite andp_unfold; apply andp_right; apply prop_right;
                            repeat split ]
           | intros ?ek ?vl; apply after_set_special1 ].
 apply andp_right.
 intro rho; unfold tc_expr; simpl.
 rewrite NONVOL. simpl.
 replace ( (temp_types (initialized ret' Delta)) ! ret' ) 
     with (Some (retty', true))
   by (unfold initialized;  simpl; rewrite H4;
        unfold temp_types; simpl; rewrite PTree.gss; auto).
 simpl @snd; simpl @fst; cbv iota zeta beta.
 unfold local; apply prop_right.
 simpl.
 clear - H5.
  destruct retty,retty'; simpl; try inv H5; try apply I.
 intro rho; apply prop_right; unfold tc_temp_id; simpl.
 unfold typecheck_temp_id.
 destruct (eq_dec ret' ret).
 subst ret'.
 unfold temp_types. unfold initialized; simpl.
 rewrite H4. simpl. rewrite PTree.gss.
  replace (implicit_deref retty') with retty' by (clear - H0; destruct retty'; try contradiction; reflexivity).
 rewrite H4 in H6. apply eqb_type_true in H6. subst retty'.
 rewrite H5.
 simpl.
 apply neutral_isCastResultType; auto.
 replace (implicit_deref retty') with retty' by (clear - H0; destruct retty'; try contradiction; reflexivity).
 destruct ((temp_types Delta) ! ret) eqn:?; try discriminate.
 destruct p. apply eqb_type_true in H6.
 subst t.
 unfold temp_types, initialized.  rewrite H4. simpl. rewrite PTree.gso by auto.
 rewrite Heqo.
 rewrite denote_tc_assert_andp; split.
 rewrite H5; reflexivity.
 apply neutral_isCastResultType'; auto.
 apply derives_refl.
 intros.
 apply andp_left2. apply normal_ret_assert_derives'.
 apply exp_derives; intro old.
 apply andp_derives.
 apply prop_right; auto.
 go_lowerx.
 apply sepcon_derives; auto.
 rewrite subst_lift1'.
 replace (subst ret (fun _ => old) (get_result1 ret') rho)
   with (get_result1 ret rho); auto.
 destruct (eq_dec ret ret').
 subst.
 unfold get_result1.
 unfold subst. f_equal.
 autorewrite with subst in H8.
 normalize in H8. rewrite H8.
 f_equal. unfold eval_id.  simpl. rewrite Map.gss. reflexivity.
 clear - H6 H8 H7.
 unfold tc_environ in H7.
 unfold env_set. destruct rho; simpl in *; f_equal.
 unfold eval_id in H8; simpl in H8. 
 unfold subst in H8.
 simpl in *. rewrite Map.gss in H8. simpl in H8.
 unfold lift in H8. 
 unfold Map.set. extensionality i. 
 destruct (ident_eq i ret'); auto.  subst i.
 unfold typecheck_environ in H7.
 destruct H7 as [? [_  [_ _]]].
 simpl te_of in H.
 hnf in H.
 specialize (H ret').
 revert H6; case_eq ((temp_types Delta)!ret'); intros; try discriminate.
 destruct p.
 unfold temp_types, initialized in H; simpl in H.
 rewrite H0 in H. unfold temp_types in *. simpl in H. rewrite PTree.gss in H.
 simpl in H. rewrite PTree.gss in H.
 specialize (H true t (eq_refl _)). 
 destruct H as [v [? ?]]. unfold Map.get in H,H8; rewrite H in *.
 f_equal. destruct H1. inv H1.  destruct v; inv H8; inv H1; auto.
  rewrite closed_wrt_subst; auto with closed.
 unfold get_result1.
 f_equal. f_equal.
 rewrite H8.
  rewrite closed_wrt_subst; auto with closed.
Qed.

Lemma semax_call_id1_x_alt:
 forall Espec Delta P Q R ret ret' id (paramty: typelist) (retty retty': type) (bl: list expr)
                  (argsig: list (ident * type)) A (Pre Post: A -> environ -> mpred)
             (witness: A) (Frame: list (LiftEnviron mpred))
   (GLBL: (var_types Delta) ! id = None),
   (glob_types Delta) ! id = Some (Global_func (mk_funspec (argsig,retty') A Pre Post)) ->
   typeof_temp Delta ret = Some retty -> 
   match retty with Tvoid => False | Tcomp_ptr _ _ => False | Tarray _ _ _ => False | _ => True end ->
   paramty = type_of_params argsig ->
   type_is_volatile retty' = false -> 
   (temp_types Delta) ! ret' = Some (retty', false) ->
   is_neutral_cast retty' retty = true ->
   forall (CLOSQ: Forall (closed_wrt_vars (eq ret')) Q),
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
    PROP () LOCAL (tc_exprlist Delta (argtypes argsig) bl) 
                (SEPx (`(Pre witness)  (make_args' (argsig, retty)
                               (eval_exprlist (argtypes argsig) bl)) :: Frame)) ->
  forall
   (CLOSR: Forall (closed_wrt_vars (eq ret')) Frame),
   @semax Espec Delta (PROPx P (LOCALx Q (SEPx R)))
    (Ssequence (Scall (Some ret')
             (Evar id (Tfunction paramty retty' cc_default))
             bl)
      (Sset ret (Etempvar ret' retty')))
    (normal_ret_assert 
       (EX old:val, 
          PROPx P (LOCALx (map (subst ret (`old)) Q) 
             (SEPx (`(Post witness) (get_result1 ret) :: map (subst ret (`old)) Frame))))).
Proof.
intros.
subst paramty.
eapply semax_pre; [ | apply semax_call_id1_x with retty; try eassumption].
rewrite <- (insert_local (tc_exprlist Delta (argtypes argsig) bl)).
apply andp_right.
eapply derives_trans; [apply H6 |].
apply andp_left2; apply andp_left1.
go_lowerx. intros [? _]; apply prop_right; auto.
apply andp_right.
apply andp_left1; auto.
apply andp_right.
rewrite <- insert_local.
apply andp_left2.
apply andp_left2.
 apply andp_left1. auto.
eapply derives_trans; [ apply H6 |].
apply andp_left2; apply andp_left2; auto.
clear - H5; destruct retty,retty'; inv H5; simpl; auto.
clear - H0. unfold typeof_temp in H0.
destruct((temp_types Delta) ! ret); inv H0.
destruct p; inv H1. apply eqb_type_refl.
Qed.

(* END HORRIBLE1 *)


Ltac ignore x := idtac.

(*start tactics for forward_while unfolding *)
Ltac intro_ex_local_derives :=
(match goal with 
   | |- local (_) && exp (fun y => _) |-- _ =>
       rewrite exp_andp2; apply exp_left; let y':=fresh y in intro y'
end).

Ltac unfold_and_function_derives_left :=
(repeat match goal with 
          | |- _ && (exp _) |--  _ => fail 1
          | |- _ && (PROPx _ _) |-- _ => fail 1
          | |- _ && (?X _ _ _ _ _) |--  _ => unfold X
          | |- _ && (?X _ _ _ _) |--  _ => unfold X
          | |- _ && (?X _ _ _) |--  _ => unfold X
          | |- _ && (?X _ _) |--  _ => unfold X
          | |- _ && (?X _) |--  _ => unfold X
          | |- _ && (?X) |--  _ => unfold X
end).

Ltac unfold_and_local_derives :=
try rewrite <- local_lift2_and;
unfold_and_function_derives_left;
repeat intro_ex_local_derives;
try rewrite local_lift2_and;
repeat (try rewrite andp_assoc; rewrite canonicalize.canon9).

Ltac unfold_function_derives_right :=
(repeat match goal with 
          | |- _ |-- (exp _) => fail 1
          | |- _ |-- (PROPx _ _) => fail 1
          | |- _ |-- (?X _ _ _ _ _)  => unfold X
          | |- _ |-- (?X _ _ _ _)  => unfold X
          | |- _ |-- (?X _ _ _)  => unfold X
          | |- _ |-- (?X _ _)  => unfold X
          | |- _ |-- (?X _)  => unfold X
          | |- _ |-- (?X)  => unfold X

end).

Ltac unfold_pre_local_andp :=
(repeat match goal with 
          | |- semax _ ((local _) && exp _) _ _ => fail 1
          | |- semax _ ((local _) && (PROPx _ _)) _ _ => fail 1
          | |- semax _ ((local _) && ?X _ _ _ _ _) _ _ => unfold X at 1
          | |- semax _ ((local _) && ?X _ _ _ _) _ _ => unfold X at 1
          | |- semax _ ((local _) && ?X _ _ _) _ _ => unfold X at 1
          | |- semax _ ((local _) && ?X _ _) _ _ => unfold X at 1
          | |- semax _ ((local _) && ?X _) _ _ => unfold X at 1
          | |- semax _ ((local _) && ?X) _ _ => unfold X at 1
        end).

Ltac intro_ex_local_semax :=
(match goal with 
   | |- semax _ (local (_) && exp (fun y => _)) _ _  =>
       rewrite exp_andp2; apply extract_exists_pre; let y':=fresh y in intro y'
end).

Ltac unfold_and_local_semax :=
unfold_pre_local_andp;
repeat intro_ex_local_semax;
try rewrite canonicalize.canon9.

Lemma quick_typecheck1: 
 forall (P B: environ -> mpred), 
    P |-- B ->
   P |-- local (`True) && B.
Proof.
intros; apply andp_right; auto.
 intro rho; apply TT_right.
Qed.

Lemma quick_typecheck2: 
 forall (P A: environ -> mpred), 
    P |-- A ->
   P |-- A && local (`True).
Proof.
intros; apply andp_right; auto.
 intro rho; apply TT_right.
Qed.

Lemma local_True_right:
 forall (P: environ -> mpred),
   P |-- local (`True).
Proof. intros. intro rho; apply TT_right.
Qed.

Ltac quick_typecheck :=
     first [ apply quick_typecheck1; try apply local_True_right
            | apply quick_typecheck2
            | apply local_True_right
            | idtac ].

Ltac forward_while Inv Postcond :=
  first [ignore (Inv: environ->mpred) 
         | fail 1 "Invariant (first argument to forward_while) must have type (environ->mpred)"];
  first [ignore (Postcond: environ->mpred)
         | fail 1 "Postcondition (second argument to forward_while) must have type (environ->mpred)"];
  apply semax_pre with Inv;
    [  unfold_function_derives_right 
    | (apply semax_seq with Postcond;
       [ first 
          [ apply semax_while' 
          | apply semax_while
          ]; 
          [ compute; auto 
          | unfold_and_local_derives
          | unfold_and_local_derives
          | unfold_and_local_semax
          ] 
       | simpl update_tycon 
       ])
    ]; abbreviate_semax; autorewrite with ret_assert.

Ltac forward_for Inv PreIncr Postcond :=
  first [ignore (Inv: environ->mpred) 
         | fail 1 "Invariant (first argument to forward_for) must have type (environ->mpred)"];
  first [ignore (Postcond: environ->mpred)
         | fail 1 "Postcondition (last argument to forward_for) must have type (environ->mpred)"];
  apply semax_pre with Inv;
    [  unfold_function_derives_right 
    | (apply semax_seq with Postcond;
       [ first 
          [ apply semax_for' with PreIncr
          | apply semax_for with PreIncr
          ]; 
          [ compute; auto 
          | unfold_and_local_derives
          | unfold_and_local_derives
          | unfold_and_local_semax
          | unfold_and_local_semax
          ] 
       | simpl update_tycon 
       ])
    ]; abbreviate_semax; autorewrite with ret_assert.

Ltac forward_if' := 
match goal with 
| |- @semax _ ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                                 (Sifthenelse ?e _ _) _ => 
 (apply semax_ifthenelse_PQR; [ reflexivity | quick_typecheck | | ])
  || fail 2 "semax_ifthenelse_PQR did not match"
end.

Ltac forward_if post :=
first [ignore (post: environ->mpred) 
      | fail 1 "Invariant (first argument to forward_if) must have type (environ->mpred)"];
match goal with
 | |- semax _ _ (Sifthenelse _ _ _) (overridePost post _) =>
       forward_if' 
 | |- semax _ _ (Sifthenelse _ _ _) ?P =>
      apply (semax_post_flipped (overridePost post P)); 
      [ forward_if'
      | try solve [normalize]
      ]
   | |- semax _ _ (Ssequence (Sifthenelse _ _ _) _) _ =>
     apply semax_seq with post;
      [forward_if' | abbreviate_semax; autorewrite with ret_assert]
end.

Ltac normalize :=
 try match goal with |- context[subst] =>  autorewrite with subst typeclass_instances end;
 try match goal with |- context[ret_assert] =>  autorewrite with ret_assert typeclass_instances end;
 match goal with 
 | |- semax _ _ _ _ =>
  floyd.client_lemmas.normalize;
  repeat 
  (first [ simpl_tc_expr
         | simple apply semax_extract_PROP_True; [solve [auto] | ]
         | simple apply semax_extract_PROP; intro
         | extract_prop_from_LOCAL
         | move_from_SEP
         ]; cbv beta; msl.log_normalize.normalize)
  | |- _  => 
    floyd.client_lemmas.normalize
  end.

Lemma eqb_ident_true: forall i, eqb_ident i i = true.
Proof.
intros; apply Pos.eqb_eq. auto.
Qed.

Lemma eqb_ident_false: forall i j, i<>j -> eqb_ident i j = false.
Proof.
intros; destruct (eqb_ident i j) eqn:?; auto.
apply Pos.eqb_eq in Heqb. congruence.
Qed.

Hint Rewrite eqb_ident_true : subst.
Hint Rewrite eqb_ident_false using solve [auto] : subst.

Lemma subst_temp_special:
  forall i e (f: val -> Prop) j,
   i <> j -> subst i e (`f (eval_id j)) = `f (eval_id j).
Proof.
 intros.
 autorewrite with subst; auto.
Qed.
Hint Rewrite subst_temp_special using safe_auto_with_closed: subst.

Ltac do_subst_eval_expr :=
 change (@map (environ->Prop) (environ->Prop))
   with (fun f: (environ->Prop)->(environ->Prop) =>
              fix map l := match l with nil => nil | a::t => f a :: map t end);
 change (@map (environ->mpred) (environ->mpred))
   with (fun f: (environ->mpred)->(environ->mpred) =>
              fix map l := match l with nil => nil | a::t => f a :: map t end);
  cbv beta iota;
  autorewrite with subst; 
  unfold subst_eval_expr, subst_eval_lvalue, sem_cast;
  simpl eqb_ident; cbv iota;
  fold sem_cast; fold eval_expr; fold eval_lvalue;
  simpl typeof.

Lemma forward_setx_aux1:
  forall P (X Y: environ -> Prop),
  (forall rho, X rho) ->
  (forall rho, Y rho) ->
   P |-- local X && local Y.
Proof.
intros; intro rho; rewrite andp_unfold; apply andp_right; apply prop_right; auto.
Qed.

Ltac forward_setx_wow :=
 eapply forward_setx_wow;
 [ solve [auto 50 with closed]
 | solve [repeat constructor; auto with closed]
 | simpl; first [apply I | reflexivity]
 | simpl; simpl_lift; reflexivity
 | quick_typecheck
 ].

Ltac forward_setx_wow_seq :=
eapply forward_setx_wow_seq;
 [ solve [auto 50 with closed]
 | solve [repeat constructor; auto with closed]
 | simpl; first [apply I | reflexivity]
 | simpl; simpl_lift; reflexivity
 | unfold initialized; simpl; reflexivity
 | quick_typecheck
 | abbreviate_semax
 ].


Ltac forward_setx :=
first [forward_setx_wow
       | apply forward_setx_closed_now;
            [solve [auto 50 with closed] | solve [auto 50 with closed] | solve [auto 50 with closed]
            | try apply local_True_right
            | try apply local_True_right
            |  ]
        | apply forward_setx; quick_typecheck
        ].

Ltac hoist_later_in_pre :=
     match goal with |- semax _ ?P _ _ =>
       let P' := strip1_later P in apply semax_pre0 with (|> P'); [solve [auto 50 with derives] | ]
     end.

Ltac intro_old_var' id :=
  match goal with 
  | Name: name id |- _ => 
        let x := fresh Name in
        intro x; do_subst_eval_expr; try clear x
  | |- _ => let x := fresh "x" in 
        intro x; do_subst_eval_expr; try clear x  
  end.

Ltac intro_old_var c :=
  match c with 
  | Sset ?id _ => intro_old_var' id
  | Scall (Some ?id) _ _ => intro_old_var' id
  | Ssequence _ (Sset ?id _) => intro_old_var' id
  | _ => intro x; do_subst_eval_expr; try clear x
  end.

Ltac intro_old_var'' id :=
  match goal with 
  | Name: name id |- _ => 
        let x := fresh Name in
        intro x
  | |- _ => let x := fresh "x" in 
        intro x
  end.

Ltac ensure_normal_ret_assert :=
 match goal with 
 | |- semax _ _ _ (normal_ret_assert _) => idtac
 | |- semax _ _ _ _ => apply sequential
 end.

Lemma sequential': forall Espec Delta Pre c R Post,
  @semax Espec Delta Pre c (normal_ret_assert R) ->
  @semax Espec Delta Pre c (overridePost R Post).
Proof.
intros.
eapply semax_post0; [ | apply H].
unfold normal_ret_assert; intros ek vl rho; simpl; normalize; subst.
unfold overridePost. rewrite if_true by auto.
normalize.
Qed.

Ltac ensure_open_normal_ret_assert :=
 try simple apply sequential';
 match goal with 
 | |- semax _ _ _ (normal_ret_assert ?X) => is_evar X
 end.
Ltac get_global_fun_def Delta f fsig A Pre Post :=
    let VT := fresh "VT" in let GT := fresh "GT" in  
      assert (VT: (var_types Delta) ! f = None) by 
               (reflexivity || fail 1 "Variable " f " is not a function, it is an addressable local variable");
      assert (GT: (glob_types Delta) ! f = Some (Global_func (mk_funspec fsig A Pre Post)))
                    by ((unfold fsig, Pre, Post; try unfold A; simpl; reflexivity) || 
                          fail 1 "Function " f " has no specification in the type context");
     clear VT GT.

Definition This_is_a_warning := tt.

Inductive Warning: unit -> unit -> Prop :=
    ack : forall s s', Warning s s'.
Definition IGNORE_THIS_WARNING_USING_THE_ack_TACTIC_IF_YOU_WISH := tt.

Ltac ack := apply ack.

Ltac all_closed R :=
 match R with 
  | @liftx (LiftEnviron mpred) _ :: ?R' => all_closed R'  
  | @liftx (Tarrow val (LiftEnviron mpred)) _ (eval_var _ _) :: ?R' => all_closed R'
  | nil => idtac
  end.

Definition WARNING__in_your_SEP_clauses_there_is_at_least_one_that_is_not_closed_Use_the_lemma__remember_value__before_moving_forward_through_a_function_call := tt.

Ltac assert_ P :=
  let H := fresh in assert (H: P); [ | clear H].

Ltac warn s := 
   assert_ (Warning s
               IGNORE_THIS_WARNING_USING_THE_ack_TACTIC_IF_YOU_WISH).

Ltac complain_open_sep_terms :=
 match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    first [all_closed R;  assert_ True
            | warn WARNING__in_your_SEP_clauses_there_is_at_least_one_that_is_not_closed_Use_the_lemma__remember_value__before_moving_forward_through_a_function_call
            ]
 end.

Ltac forward_call0_id :=
 complain_open_sep_terms; [auto |
  ensure_open_normal_ret_assert;
  match goal with 
  | |- @semax ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall None (Evar ?f _) ?bl) _ =>
     ensure_open_normal_ret_assert;
      let fsig:=fresh "fsig" in let A := fresh "A" in let Pre := fresh "Pre" in let Post := fresh"Post" in
      evar (fsig: funsig); evar (A: Type); evar (Pre: A -> environ->mpred); evar (Post: A -> environ->mpred);
       get_global_fun_def Delta f fsig A Pre Post;
  let witness := fresh "witness" in let F := fresh "Frame" in
      evar (witness:A); evar (F: list (environ->mpred)); 
      apply semax_pre 
         with (PROPx P (LOCALx (tc_exprlist Delta (snd (split (fst fsig))) bl:: Q)
            (SEPx (`(Pre witness) (make_args' fsig (eval_exprlist (snd (split (fst fsig))) bl)) :: F))));
          [ 
          | unfold F in *; apply (semax_call_id0 Espec Delta P Q F f 
                  bl (fst fsig) (snd fsig) A witness Pre Post (eq_refl _)  (eq_refl _))];
  unfold fsig, A, Pre, Post in *; clear fsig A Pre Post
  end].

Lemma semax_post3: 
  forall R' Espec Delta P c R,
    local (tc_environ (update_tycon Delta c)) && R' |-- R ->
    @semax Espec Delta P c (normal_ret_assert R') ->
    @semax Espec Delta P c (normal_ret_assert R) .
Proof.
 intros. eapply semax_post; [ | apply H0].
 intros. unfold local,lift1, normal_ret_assert.
 intro rho; normalize. eapply derives_trans; [ | apply H].
 simpl; apply andp_right; auto. apply prop_right; auto.
Qed.

Lemma semax_post_flipped3: 
  forall R' Espec Delta P c R,
    @semax Espec Delta P c (normal_ret_assert R') ->
    local (tc_environ (update_tycon Delta c)) && R' |-- R ->
    @semax Espec Delta P c (normal_ret_assert R) .
Proof.
intros; eapply semax_post3; eauto.
Qed.

Ltac forward_call_complain' Delta id :=
  let H1 := fresh in
     assert (H1: (var_types Delta) ! id = None) 
        by (reflexivity || fail 4 "The function-identifier " id " is not a global variable");
     clear H1;
    assert (match (glob_types Delta) ! id with
               | Some (Global_func (mk_funspec _ t _ _)) => Some t
               | _ => None
               end = None);
     simpl; 
     match goal with
     | |- Some ?A = _ => fail 4 "Use forward_call W, where W is a witness of type " A "
"
     | |- None = _ => fail 4 "The function identifier " id " is not a function"
     end.

Ltac forward_call_complain :=
 match goal with 
 | |- semax ?Delta _ (Ssequence (Scall _ (Evar ?id _) _) _) _ =>
       forward_call_complain' Delta id
 | |- semax ?Delta _ (Scall _ (Evar ?id _) _) _ =>
       forward_call_complain' Delta id
  end.

Ltac normalize_postcondition :=
 match goal with 
 | P := _ |- semax _ _ _ ?P =>
     unfold P, abbreviate; clear P; normalize_postcondition
 | |- semax _ _ _ (normal_ret_assert _) => idtac
 | |- _ => apply sequential
  end.

Lemma elim_useless_retval:
 forall Espec Delta P Q (F: val -> Prop) (G: mpred) R c Post,
  @semax Espec Delta (PROPx P (LOCALx Q (SEPx (`G :: R)))) c Post ->
  @semax Espec Delta (PROPx P (LOCALx Q 
    (SEPx 
    (`(fun x : environ => local (`F retval) x && `G x) (make_args nil nil)
      :: R)))) c Post.
Proof.
intros.
eapply semax_pre0; [ | apply H].
apply andp_derives; auto.
apply andp_derives; auto.
apply sepcon_derives; auto.
unfold_lift. unfold local, lift1.
intro rho. apply andp_left2; auto.
Qed.

Definition  DO_THE_after_call_TACTIC_NOW (x: Prop) := x.
Arguments DO_THE_after_call_TACTIC_NOW {x}.

Ltac after_call :=  
  match goal with |- @DO_THE_after_call_TACTIC_NOW _ =>
   unfold DO_THE_after_call_TACTIC_NOW;
   match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (ifvoid ?A ?B ?C :: _)))) _ _ =>
      first [change (ifvoid A B C) with B | change (ifvoid A B C) with C]
   | _ => idtac
   end;
   autorewrite with subst; normalize;
   match goal with 
   | |- forall x:val, _ => intros ?retval0; normalize
   | _ => idtac
   end
  end.

Ltac say_after_call :=
 match goal with |- ?x => 
 change (@DO_THE_after_call_TACTIC_NOW x)
 end.

Lemma focus_make_args:
  forall A Q R R' Frame,
    R = R' ->
    A |-- PROPx nil (LOCALx Q (SEPx (R' :: Frame)))  ->
    A |-- PROPx nil (LOCALx Q (SEPx (R :: Frame))) .
Proof.
intros; subst; auto.
Qed.

Lemma subst_make_args1:
  forall i e j v,
    subst i e (make_args (j::nil) (v::nil)) = make_args (j::nil) (v::nil).
Proof. reflexivity. Qed.
Hint Rewrite subst_make_args1 : norm.
Hint Rewrite subst_make_args1 : subst.

Ltac normalize_make_args :=
 cbv beta iota;
 repeat rewrite subst_make_args1;
 let R' := fresh "R" in evar (R': environ->mpred);
   apply focus_make_args with R';
  [norm_rewrite; unfold R'; reflexivity
  | unfold R'; clear R'].

Ltac forward_call W := 
 let witness := fresh "witness" in
 pose (witness := W);   (* faster this way, for some reason *)
match goal with
| |- semax _ _ (Ssequence (Ssequence (Scall (Some ?i') _ _) 
                                          (Sset ?i (Etempvar ?i' _))) _) _ =>
   let Frame := fresh "Frame" in evar (Frame: list (environ->mpred));
   eapply semax_seq';
    [eapply (semax_call_id1_x_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ witness Frame);
      [reflexivity | reflexivity | reflexivity | apply I | reflexivity | reflexivity 
      | reflexivity | reflexivity | auto 50 with closed | | unfold Frame; clear Frame ]
    | simpl update_tycon; abbreviate_semax; apply extract_exists_pre; 
      intro_old_var' i; autorewrite with subst; unfold Frame; clear Frame;
     say_after_call ]
| |- semax _ _ (Ssequence (Scall (Some ?i') _ _) 
                                          (Sset ?i (Etempvar ?i' _))) _ =>
   normalize_postcondition;
   let Frame := fresh "Frame" in evar (Frame: list (environ->mpred));
   eapply semax_post_flipped3;
    [eapply (semax_call_id1_x_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ witness Frame);
      [reflexivity | reflexivity | reflexivity | apply I | reflexivity | reflexivity 
      | reflexivity | reflexivity | auto 50 with closed | | unfold Frame; clear Frame ]
    | simpl update_tycon; abbreviate_semax; apply extract_exists_pre; 
      intro_old_var' i; autorewrite with subst; unfold Frame; clear Frame;
     say_after_call ]
| |- semax _ _ (Ssequence (Ssequence _ _) _) _ => 
     apply -> seq_assoc; forward_call witness
| |- semax _ _ (Ssequence (Scall None _ _) _) _ =>
  let Frame := fresh "Frame" in evar (Frame: list (environ->mpred));
  eapply semax_seq';
  [eapply (semax_call_id0_alt _ _ _ _ _ _ _ _ _ _ _ witness Frame);
         [reflexivity | reflexivity | reflexivity | normalize_make_args ]
  | cbv beta iota; try simple apply elim_useless_retval;
    simpl update_tycon; abbreviate_semax; unfold Frame; clear Frame;
    say_after_call ]
| |- semax _ _ (Scall None _ _) _ =>
   normalize_postcondition;
  let Frame := fresh "Frame" in evar (Frame: list (environ->mpred));
   eapply semax_post_flipped3;
  [eapply (semax_call_id0_alt _ _ _ _ _ _ _ _ _ _ _ witness Frame);
         [reflexivity | reflexivity | reflexivity | normalize_make_args ]
  | cbv beta iota; try simple apply elim_useless_retval;
    try rewrite exp_andp2;
    try rewrite insert_local; unfold Frame; clear Frame;
    say_after_call ]
| |- semax _ _ (Ssequence (Scall (Some ?i) _ _) _) _ =>
   let Frame := fresh "Frame" in evar (Frame: list (environ->mpred));
   eapply semax_seq';
    [eapply (semax_call_id1_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ witness Frame);
            [reflexivity | reflexivity | apply I 
            | simpl; first [apply I | reflexivity]
            |reflexivity | normalize_make_args ]
    | simpl update_tycon; abbreviate_semax; apply extract_exists_pre; 
      intro_old_var' i; autorewrite with subst; unfold Frame; clear Frame;
     say_after_call ]
| |- semax _ _ (Scall (Some ?i) _ _) _ =>
   normalize_postcondition;
   let Frame := fresh "Frame" in evar (Frame: list (environ->mpred));
   eapply semax_post_flipped3;
    [eapply (semax_call_id1_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ witness Frame);
            [reflexivity | reflexivity | apply I 
            | simpl; first [apply I | reflexivity]
            | reflexivity | normalize_make_args ]
    | try rewrite exp_andp2;
               try (apply exp_left; intro_old_var' i);
               try rewrite insert_local;
               autorewrite with subst; unfold Frame; clear Frame;
               say_after_call ]
 | |- _ => forward_call_complain
end; 
 unfold witness; try clear witness; simpl argtypes.

Ltac check_sequential s :=
 match s with
 | Sskip => idtac
 | Sassign _ _ => idtac
 | Sset _ _ => idtac
 | Scall _ _ _ => idtac
 | Ssequence ?s1 ?s2 => check_sequential s1; check_sequential s2
 | _ => fail
 end.

Ltac sequential := 
 match goal with
 |  |- @semax _ _ _ _ (normal_ret_assert _) => fail 2
 |  |- @semax _ _ _ ?s _ =>  check_sequential s; apply sequential
 end.

Ltac is_canonical P :=
 match P with 
 | PROPx _ (LOCALx _ (SEPx _)) => idtac
 | _ => fail 2 "precondition is not canonical (PROP _ LOCAL _ SEP _)"
 end.

Ltac bool_compute b :=
let H:= fresh in 
  assert (b=true) as H by auto; clear H. 

Ltac tac_if b T F := 
first [bool_compute b;T | F].

Definition ptr_compare e :=
match e with
| (Ebinop cmp e1 e2 ty) =>
   andb (andb (is_comparison cmp) (is_pointer_type (typeof e1))) (is_pointer_type (typeof e2))
| _ => false
end.

Ltac forward_ptr_cmp := 
first [eapply forward_ptr_compare_closed_now;
       [    solve [auto 50 with closed] 
          | solve [auto 50 with closed] 
          | solve [auto 50 with closed] 
          | solve [auto 50 with closed]
          | first [solve [auto] 
                  | (right; go_lower; apply andp_right; 
                                [ | solve [subst;cancel]];
                                apply andp_right; 
                                [ normalize 
                                | solve [subst;cancel]])]
          | reflexivity ]
       | eapply forward_ptr_compare'; try reflexivity; auto].
 
Ltac forward_setx_with_pcmp e :=
tac_if (ptr_compare e) ltac:forward_ptr_cmp ltac:forward_setx.

(* BEGIN new semax_load and semax_store tactics *************************)



Lemma go_lower_lem24:
  forall rho (Q1: environ -> Prop)  Q R PQR,
  (Q1 rho -> LOCALx Q R rho |-- PQR) ->
  LOCALx (Q1::Q) R rho |-- PQR.
Proof.
   unfold LOCALx,local; super_unfold_lift; simpl; intros.
 normalize. 
 eapply derives_trans;  [ | apply (H H0)].
 normalize.
Qed.
Definition force_eq ( x y: val) := force_ptr x = force_ptr y.


Lemma force_force_eq:
  forall v, force_ptr (force_ptr v) = force_ptr v.
Proof. intros. destruct v; reflexivity. Qed.

Lemma force_eq1: forall v w, force_eq v w -> force_eq (force_ptr v) w .
Proof. unfold force_eq; intros; rewrite force_force_eq; auto. Qed.

Lemma force_eq2: forall v w, force_eq v w -> force_eq v (force_ptr w).
Proof. unfold force_eq; intros; rewrite force_force_eq; auto. Qed.

Lemma force_eq0: forall v w, v=w -> force_eq v w.
Proof. intros. subst. reflexivity. Qed.

Ltac force_eq_tac := repeat first [simple apply force_eq1 | simple apply force_eq2];
                                 try apply force_eq0;
                                 first [assumption |  reflexivity].

Ltac quick_load_equality :=
 (intros ?rho; apply prop_right; unfold_lift; force_eq_tac) ||
 (apply go_lower_lem20;
  intros ?rho; 
  simpl derives; repeat (simple apply go_lower_lem24; intro);
  apply prop_right; simpl; unfold_lift; force_eq_tac) ||
  idtac.

Lemma sem_add_ptr_int:
 forall v t i, 
   isptr v -> 
   Cop2.sem_add (tptr t) tint v (Vint (Int.repr i)) = Some (add_ptr_int t v i).
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite sem_add_ptr_int using assumption : norm.

Ltac new_load_tac :=   (* matches:  semax _ _ (Sset _ (Efield _ _ _)) _  *)
 ensure_normal_ret_assert;
 hoist_later_in_pre;
 match goal with   
 | |- semax _ _ (Sset _ (Efield ?e _ _)) _ =>
 match e with
 | Ederef _ _ => 
   (eapply (semax_load_field_40);
   [ solve [auto 50 with closed] | solve [auto 50 with closed]
   | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity 
   | solve [entailer!]
   | try apply I; try assumption; reflexivity
   ]) || fail 1
 | _ =>
   eapply (semax_load_field_38);
   [ solve [auto 50 with closed] | solve [auto 50 with closed]
   | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity 
   | solve [go_lower; apply prop_right; try rewrite <- isptr_force_ptr'; auto]
   | solve [entailer; unfold at_offset; cancel]
   | try apply I; try assumption; reflexivity
   ]
 end
 | |- semax _ _ (Sset _ (Ecast (Efield ?e _ _) _)) _ =>
 match e with
 | Ederef _ _ => 
   (eapply (semax_cast_load_field_40);
   [ solve [auto 50 with closed] | solve [auto 50 with closed]
   | reflexivity | reflexivity | reflexivity | reflexivity  
   | solve [entailer!]
   | try apply I; try assumption; reflexivity
   ]) || fail 1
 | _ =>
   eapply (semax_cast_load_field_38);
   [ solve [auto 50 with closed] | solve [auto 50 with closed]
   | reflexivity | reflexivity | reflexivity | reflexivity 
   | solve [go_lower; apply prop_right; try rewrite <- isptr_force_ptr'; auto]
   | solve [entailer; unfold at_offset; cancel]
   | try apply I; try assumption; reflexivity
   ]
 end
 | |- semax _ _ (Sset _ (Efield _ _ _)) _ =>
  eapply (semax_load_field'');
   [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity 
   | try solve [entailer]
   | solve [entailer; simpl_data_at; unfold at_offset; simpl; cancel]
   | try apply I; try assumption; reflexivity
   ]
 | |- semax _ _ (Sset _ (Ecast (Efield _ _ _) _)) _ =>
  eapply (semax_cast_load_field'');
   [reflexivity | reflexivity | reflexivity | reflexivity 
   | try solve [entailer]
   | solve [entailer; simpl_data_at; unfold at_offset; simpl; cancel]
   | try apply I; try assumption; reflexivity
   ]
 | |- semax _ _ (Sset _ (Ederef (Ebinop Oadd ?e1 ?e2 _) _)) _ =>
    eapply semax_load_array with (lo:=0)(v1:=eval_expr e1)(v2:=eval_expr e2);
      [ reflexivity | reflexivity | ]
 | |- semax _ _ (Sset _ (Ecast (Ederef (Ebinop Oadd ?e1 ?e2 _) _) _)) _ =>
    eapply semax_cast_load_array with (lo:=0)(v1:=eval_expr e1)(v2:=eval_expr e2);
      [ reflexivity | reflexivity | reflexivity | reflexivity 
      | solve [entailer; unfold at_offset; cancel]
      | ]
 | |- _ => eapply semax_load_37';
   [reflexivity | reflexivity
   | entailer;
    try (apply andp_right; [apply prop_right | solve [cancel] ];
           do 2 eexists; split; reflexivity)
    ]
 | |- _ => eapply semax_cast_load_37';
   [reflexivity 
   |entailer;
    try (apply andp_right; [apply prop_right | solve [cancel] ];
           do 2 eexists; split; reflexivity)
    ]
 end.


Definition numbd {A} (n: nat) (x: A) : A := x.

Lemma numbd_eq: forall A n (x: A), numbd n x = x.
Proof. reflexivity. Qed.

Lemma saturate_local_numbd:
 forall n (P Q : mpred), P |-- Q -> numbd n P |-- Q.
Proof. intros. apply H.
Qed.
Hint Resolve saturate_local_numbd: saturate_local.

Fixpoint number_list {A} (k: nat)  (xs: list A): list A :=
 match xs with nil => nil | x::xs' => numbd k x :: number_list (S k) xs' end.

Lemma number_list_eq: forall {A} k (xs: list A), number_list k xs = xs.
Proof.
intros. revert k; induction xs; simpl; auto.
intro; f_equal; auto.
Qed.

Lemma numbd_derives:
 forall n (P Q: mpred), P |-- Q -> numbd n P |-- numbd n Q.
Proof. intros. apply H. Qed.
Lemma numbd_rewrite1:
  forall A B n (f: A->B) (x: A), numbd n f x = numbd n (f x).
Proof. intros. reflexivity. Qed.

Opaque numbd.

Hint Rewrite numbd_rewrite1 : norm.
Hint Resolve numbd_derives : cancel.

Lemma numbd_lift0:
  forall n f,
   numbd n (@liftx (LiftEnviron mpred) f) = 
   (@liftx (LiftEnviron mpred)) (numbd n f).
Proof. reflexivity. Qed.
Lemma numbd_lift1:
  forall A n f v,
   numbd n ((@liftx (Tarrow A (LiftEnviron mpred)) f) v) = 
   (@liftx (Tarrow A (LiftEnviron mpred)) (numbd n f)) v.
Proof. reflexivity. Qed.
Lemma numbd_lift2:
  forall A B n f v1 v2 ,
   numbd n ((@liftx (Tarrow A (Tarrow B (LiftEnviron mpred))) f) v1 v2) = 
   (@liftx (Tarrow A (Tarrow B (LiftEnviron mpred))) (numbd n f)) v1 v2.
Proof. reflexivity. Qed.

Lemma semax_store_aux31:
 forall P Q1 Q R R', 
    PROPx P (LOCALx (Q1::Q) (SEPx R)) |-- fold_right sepcon emp R' ->
    PROPx P (LOCALx (Q1::Q) (SEPx R)) |-- PROPx P (LOCALx Q (SEPx R')).
Proof.
intros. 
apply andp_right. apply andp_left1; auto.
apply andp_right. apply andp_left2; apply andp_left1.
intro rho; unfold local, lift1; unfold_lift; apply prop_derives; intros [? ?]; auto.
apply H.
Qed.

Lemma fast_entail:
  forall n P Q1 Q Rn Rn' R, 
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (Q1::Q) (SEP (Rn))) |-- Rn'  ->
      PROPx P (LOCALx (Q1::Q) (SEPx R)) |-- PROPx P (LOCALx Q (SEPx (replace_nth n R Rn'))).
Proof.
intros.
go_lowerx.
specialize (H0 rho).
unfold PROPx, LOCALx, SEPx, local,lift1 in H0.
unfold_lift in H0. simpl in H0.
repeat  rewrite prop_true_andp in H0 by auto.
clear P H1 Q1 Q H3 H2.
rewrite sepcon_emp in H0.
revert R H H0; induction n; destruct R; simpl; intros; inv H;
 apply sepcon_derives; auto.
Qed.

Lemma local_lifted_reflexivity:
forall A P (x: environ -> A), P |-- local (`eq x x).
Proof. intros. intro rho. apply prop_right. hnf. reflexivity.
Qed.

Ltac new_store_tac := 
ensure_open_normal_ret_assert;
hoist_later_in_pre;
match goal with
| |- @semax ?Esp ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) 
     (Sassign (Ederef (Ebinop Oadd ?e1 ?ei _) ?t) ?e2) _ =>
  let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  let contents := fresh "contents" in evar (contents: Z -> reptype t);
  let lo := fresh "lo" in evar (lo: Z);
  let hi := fresh "hi" in evar (hi: Z);
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (array_at t sh contents lo hi)) (eval_expr e1)) * TT) as _;
  [unfold number_list, n, sh, contents, lo, hi; 
   repeat rewrite numbd_lift0; repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   unfold at_offset; solve [entailer; cancel]
 |  ];
  eapply(@semax_store_array Esp Delta n sh t contents lo hi);
  unfold number_list, n, sh, contents, lo, hi;
  clear n sh contents lo hi;
  [solve [auto] | reflexivity | reflexivity | reflexivity
  | norm_rewrite; try reflexivity;
    fail 4 "Cannot prove 6th premise of semax_store_array"
  | ]
 | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign (Efield ?e ?fld _) _) _ =>
  let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (field_at_ sh (typeof e) fld)) (eval_lvalue e)) * TT) as _;
  [unfold number_list, n, sh; 
   repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   unfold at_offset; solve [entailer; cancel]
 |  ];
(**** 12.8 seconds to here ****)
 apply (semax_pre_later (PROPx P (LOCALx Q 
                (SEPx (replace_nth n R (`(field_at_ sh (typeof e) fld) (eval_lvalue e)))))));
 [ eapply (fast_entail n); [reflexivity | entailer; unfold at_offset; simpl; cancel] | ];
(**** 14.2 seconds to here  *)
 eapply (semax_store_field_nth _ _ n sh); 
   [reflexivity | auto | reflexivity | reflexivity | reflexivity
      | (apply local_lifted_reflexivity || solve [entailer])
      | try solve [entailer]
     ];
  unfold n,sh; clear n sh
 (**** 21.1 seconds to here *****)
  | |- @semax ?Espec ?Delta (|> PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Sassign ?e ?e2) _ =>

 let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (mapsto_ sh (typeof e))) (eval_lvalue e)) * TT) as _;
  [ unfold number_list, n, sh; 
   repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   unfold at_offset; solve [entailer; cancel]
  |  ];
  eapply (@semax_store_nth Espec n Delta P Q R e e2);
    (unfold n,sh; clear n sh);
     [reflexivity | reflexivity |solve [entailer; cancel] | solve [auto] 
     | try solve [entailer!] ]
end.

(* END new semax_load and semax_store tactics *************************)

Ltac semax_logic_and_or :=
first [ eapply semax_logical_or_PQR | eapply semax_logical_and_PQR];
[ auto 50 with closed
| auto 50 with closed
| auto 50 with closed
| auto 50 with closed
| auto | auto | reflexivity
| try solve [intro rho; simpl; repeat apply andp_right; apply prop_right; auto] | ].

Ltac forward0 :=  (* USE FOR DEBUGGING *)
  match goal with 
  | |- @semax _ _ ?PQR (Ssequence ?c1 ?c2) ?PQR' => 
           let Post := fresh "Post" in
              evar (Post : environ->mpred);
              apply semax_seq' with Post;
               [ 
               | unfold exit_tycon, update_tycon, Post; clear Post ]
  end.

Lemma normal_ret_assert_derives'': 
  forall P Q R, P |-- R ->  normal_ret_assert (local Q && P) |-- normal_ret_assert R.
Proof. 
  intros. intros ek vl rho. apply normal_ret_assert_derives. 
 simpl. apply andp_left2. apply H.
Qed.

Lemma drop_tc_environ:
 forall Delta R, local (tc_environ Delta) && R |-- R.
Proof.
intros. apply andp_left2; auto.
Qed.

Ltac forward_return :=
     repeat match goal with |- semax _ _ _ ?D => unfold D, abbreviate; clear D end;
     (eapply semax_pre; [  | apply semax_return ]; 
      entailer_for_return).

Ltac forward_ifthenelse :=
           semax_logic_and_or 
           ||  fail 2 "Use this tactic:  forward_if POST, where POST is the post condition".

Ltac forward_while_complain :=
           fail 2 "Use this tactic:  forward_while INV POST,
    where INV is the loop invariant and POST is the postcondition".

Ltac forward_for_complain := 
           fail 2 "Use this tactic:  forward_for INV PRE_INCR POST,
      where INV is the loop invariant, PRE_INCR is the invariant at the increment,
      and POST is the postcondition".

(* The forward_compound_call tactic is needed because CompCert clightgen
 produces the following AST for function call:
  (Ssequence (Scall (Some id') ... ) (Sset id (Etempvar id' _)))
instead of the more natural
   (Scall id ...)
Our general tactics are powerful enough to reason about the sequence,
one statement at a time, but it is not nice to burden the user with knowing
about id'.  So we handle it all in one gulp.
 See also BEGIN HORRIBLE1 in forward_lemmas.v
*)
Ltac forward_compound_call :=
  complain_open_sep_terms; [auto |
  ensure_open_normal_ret_assert;
   match goal with |-  @semax ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
               (Ssequence (Scall (Some ?id') (Evar ?f _) ?bl)
                       (Sset ?id (Etempvar ?id' _))) _ =>

         let fsig:=fresh "fsig" in let A := fresh "A" in let Pre := fresh "Pre" in let Post := fresh"Post" in
         evar (fsig: funsig); evar (A: Type); evar (Pre: A -> environ->mpred); evar (Post: A -> environ->mpred);
         get_global_fun_def Delta f fsig A Pre Post;
    let x := fresh "witness" in let F := fresh "Frame" in
      evar (x:A); evar (F: list (environ->mpred)); 
      apply semax_pre with (PROPx P
                (LOCALx (tc_exprlist Delta (argtypes (fst fsig)) bl :: Q)
                 (SEPx (`(Pre x)  (make_args' fsig (eval_exprlist (argtypes (fst fsig)) bl)) ::
                            F))));
       [
       | apply (semax_call_id1_x Espec Delta P Q F id id' f 
                   (snd fsig) bl (fst fsig) A x Pre Post 
                      (eq_refl _) (eq_refl _) I) ; 
               [ (solve[ simpl; auto with closed]  || solve [auto with closed]) (* FIXME!*)
               | unfold F (*solve[simpl; auto with closed] PREMATURELY INSTANTIATES FRAME *) 
               | reflexivity | reflexivity | reflexivity | reflexivity ]]
               ;
  unfold fsig, A, Pre, Post in *; clear fsig A Pre Post
end ].

Ltac forward_call1_id :=
 complain_open_sep_terms; [ auto |
 ensure_open_normal_ret_assert;
 match goal with 
  | |- @semax ?Espec ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) (Scall (Some ?id) (Evar ?f _) ?bl) _ =>

      let fsig:=fresh "fsig" in let A := fresh "A" in let Pre := fresh "Pre" in let Post := fresh"Post" in
      evar (fsig: funsig); evar (A: Type); evar (Pre: A -> environ->mpred); evar (Post: A -> environ->mpred);
      get_global_fun_def Delta f fsig A Pre Post;
    let witness := fresh "witness" in let F := fresh "Frame" in
      evar (witness:A); evar (F: list (environ->mpred)); 
      apply semax_pre with (PROPx P
                (LOCALx (tc_exprlist Delta (argtypes (fst fsig)) bl :: Q)
                 (SEPx (`(Pre witness)  (make_args' fsig (eval_exprlist (argtypes (fst fsig)) bl)) ::
                            F))));
       [
       | apply (semax_call_id1 Espec Delta P Q F id f 
                 (snd fsig) bl (fst fsig) A witness Pre Post 
                      (eq_refl _) (eq_refl _) I) ];
  unfold fsig, A, Pre, Post in *; clear fsig A Pre Post
 end].

Ltac forward_skip := apply semax_skip.

Ltac no_loads_expr e as_lvalue enforce :=
 match e with
 | Econst_int _ _ => idtac
 | Econst_float _ _ => idtac
 | Econst_long _ _ => idtac
 | Evar _ _ => match as_lvalue with true => idtac end
 | Etempvar _ _ => idtac
 | Eaddrof ?e1 _ => no_loads_expr e1 true enforce
 | Eunop _ ?e1 _ => no_loads_expr e1 as_lvalue enforce
 | Ebinop _ ?e1 ?e2 _ => no_loads_expr e1 as_lvalue enforce; no_loads_expr e2 as_lvalue enforce
 | Ecast ?e1 _ => no_loads_expr e1 as_lvalue enforce
 | Efield ?e1 _ _ => match as_lvalue with true =>
                              no_loads_expr e1 true enforce
                              end
 | _ => match enforce with false =>
            let r := fresh "The_expression_or_parameter_list_must_not_contain_any_loads_but_the_following_subexpression_is_an_implicit_or_explicit_load_Please_refactor_this_stament_of_your_program" 
           in pose (r:=e) 
            end
end.

Ltac no_loads_exprlist e enforce :=
 match e with
 | ?e1::?er => no_loads_expr e1 false enforce; no_loads_exprlist er enforce
 | nil => idtac
 end.

Ltac forward1 s :=  (* Note: this should match only those commands that
                                     can take a normal_ret_assert *)
  lazymatch s with 
  | Sassign _ _ => new_store_tac
  | Sset _ (Efield ?e _ ?t)  => 
      no_loads_expr e true false;
      first [unify true (match t with Tarray _ _ _ => true | _ => false end);
               forward_setx
              |new_load_tac]
  | Sset _ (Ecast (Efield ?e _ ?t) _) => 
      no_loads_expr e true false;
      first [unify true (match t with Tarray _ _ _ => true | _ => false end);
               forward_setx
              |new_load_tac]
  | Sset _ (Ederef ?e _) => 
         no_loads_expr e true false; new_load_tac
  | Sset _ (Ecast (Ederef ?e _) ?t) => 
         no_loads_expr e true false; 
      first [unify true (match t with Tarray _ _ _ => true | _ => false end);
               forward_setx
              |new_load_tac]
  | Sset _ (Evar _ ?t)  => 
      first [unify true (match t with Tarray _ _ _ => true | _ => false end);
               forward_setx
              |new_load_tac]
  | Sset _ (Ecast (Evar _ _) _) => new_load_tac
  | Sset _ ?e => no_loads_expr e false false; (bool_compute e; forward_ptr_cmp) || forward_setx
  | Sifthenelse ?e _ _ => no_loads_expr e false false; forward_ifthenelse
  | Swhile _ _ => forward_while_complain
  | Sloop (Ssequence (Sifthenelse _ Sskip Sbreak) _) _ => forward_for_complain
  | Ssequence (Scall (Some ?id') (Evar _ _) ?el) (Sset _ (Etempvar ?id' _)) => 
          no_loads_exprlist el false; forward_compound_call
  | Scall (Some _) (Evar _ _) ?el =>  no_loads_exprlist el false; forward_call1_id
  | Scall None (Evar _ _) ?el =>  no_loads_exprlist el false; forward_call0_id
  | Sskip => forward_skip
  end.

Ltac derives_after_forward :=
             first [ simple apply derives_refl 
                     | simple apply drop_tc_environ
                     | simple apply normal_ret_assert_derives'' 
                     | simple apply normal_ret_assert_derives'
                     | idtac].

Ltac forward_break :=
eapply semax_pre; [ | apply semax_break ];
  unfold_abbrev_ret;
  autorewrite with ret_assert.

Ltac forward_with F1 :=
 match goal with 
  | |- semax _ _ (Ssequence (Sset _ ?e) _) _ =>
         no_loads_expr e false true;
         forward_setx_wow_seq
  | |- semax _ _ (Ssequence (Sreturn _) _) _ =>
            apply semax_seq with FF; [ | apply semax_ff];
            forward_return
  | |- semax _ _ (Sreturn _) _ =>  forward_return
  | |- semax _ _ (Ssequence Sbreak _) _ =>
            apply semax_seq with FF; [ | apply semax_ff];
            forward_break
  | |- semax _ _ Sbreak _ => forward_break
  | |- semax _ _ (Ssequence ?c _) _ =>
    let ftac := F1 c in
       ((eapply semax_seq'; 
             [ftac; derives_after_forward
             | unfold replace_nth; cbv beta;
               try (apply extract_exists_pre; intro_old_var c);
               abbreviate_semax
             ]) 
        ||  fail 0)  (* see comment FORWARD_FAILOVER below *)
  | |- semax _ _ (Ssequence (Ssequence _ _) _) _ =>
       apply -> seq_assoc; forward_with F1
  | |- semax _ _ ?c _ =>
     let ftac := F1 c in
      normalize_postcondition;
       eapply semax_post_flipped3;
             [ftac; derives_after_forward
             | try rewrite exp_andp2;
               try (apply exp_left; intro_old_var c);
               try rewrite insert_local
             ] 
end.

(* FORWARD_FAILOVER:
  The first clause of forward_with starts by calling F1, and if it matches,
  then, in principle, no other clause of forward_with should be needed.
  The way to enforce "no other clause" is by writing "fail 1".
  However, there is a small bug in the forward_compound_call tactic:
  if the second assignment has an _implicit_ cast, then the lemma
  semax_call_id1_x  is just a bit too weak to work.   An example
  that demonstrates this is in verif_queue.v, in make_elem at the
  call to mallocN.   Until this lemma
  is generalized, then failover is necessary, so we have "fail 0" instead
  of "fail 1".
*)

Ltac forward := forward_with forward1.

Lemma start_function_aux1:
  forall Espec Delta R1 P Q R c Post,
   @semax Espec Delta (PROPx P (LOCALx Q (SEPx (R1::R)))) c Post ->
   @semax Espec Delta ((PROPx P (LOCALx Q (SEPx R))) * R1) c Post.
Proof.
intros.
rewrite sepcon_comm. rewrite insert_SEP. apply H.
Qed.

Lemma semax_stackframe_emp:
 forall Espec Delta P c R,
 @semax Espec Delta P c R ->
  @semax Espec Delta (P * emp) c (frame_ret_assert R emp) .
Proof. intros. 
            rewrite sepcon_emp;
            rewrite frame_ret_assert_emp;
   auto.
Qed.

Ltac unfold_Delta := 
repeat
match goal with Delta := func_tycontext ?f ?V ?G |- _ =>
  first [unfold f in Delta | unfold V in Delta | unfold G in Delta ]
end;
 match goal with Delta := func_tycontext ?f ?V ?G |- _ =>
     change (func_tycontext f V G) with (@abbreviate _ (func_tycontext f V G)) in Delta;
      unfold func_tycontext, make_tycontext,
     make_tycontext_t, make_tycontext_v, make_tycontext_g,
      fn_temps,fn_params, fn_vars, fn_return in Delta;
     simpl in Delta
 end.

Ltac start_function := 
 match goal with |- semax_body _ _ _ ?spec => try unfold spec end;
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ ?Pre _)) =>
   match Pre with 
   | (fun x => match x with (a,b) => _ end) => intros Espec [a b] 
   | (fun i => _) => intros Espec i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 repeat match goal with |- @semax _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 match goal with |- @semax _ (func_tycontext ?F ?V ?G) _ _ _ => 
   set (Delta := func_tycontext F V G); unfold_Delta
 end;
 try expand_main_pre;
 try match goal with |- context [stackframe_of ?F] => 
            change (stackframe_of F) with (@emp (environ->mpred) _ _);
            rewrite frame_ret_assert_emp;
            try rewrite sepcon_emp;  delete_emp_in_SEP
          end;
 try apply start_function_aux1;
 match goal with
  | |- @semax _ _ (PROPx _ _) _ _ => idtac 
  | _ => canonicalize_pre 
 end;
 repeat (apply semax_extract_PROP; intro);
 abbreviate_semax.

Opaque sepcon.
Opaque emp.
Opaque andp.

Arguments overridePost Q R !ek !vl / _ .
Arguments eq_dec A EqDec / a a' .
Arguments EqDec_exitkind !a !a'.

Ltac debug_store' := 
ensure_normal_ret_assert;
hoist_later_in_pre;
match goal with |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign (Efield ?e ?fld _) _) _ =>
  let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  let H := fresh in 
  assert (H: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (field_at_ sh (typeof e) fld)) (eval_lvalue e)) * TT);
  [unfold number_list;
   repeat rewrite numbd_lift1; repeat rewrite numbd_lift2;
   gather_entail
  |  ]
end.

Ltac debug_store := (forward0; [debug_store' | ]) || debug_store'.
