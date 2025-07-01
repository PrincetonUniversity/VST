Require Import VST.floyd.base2.
Require Export VST.floyd.canon.
Import LiftNotation.
Import compcert.lib.Maps.
Local Open Scope logic.

Lemma SEP_entail:
 forall R' Delta P Q R,
   (fold_right_sepcon R |-- fold_right_sepcon R') ->
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx Q (SEPx R')).
Proof.
intros.
apply andp_left2.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho.
apply H.
Qed.

Ltac refold_right_sepcon R :=
 match R with
 | @sepcon mpred _ _ ?R1 ?R' => let S := refold_right_sepcon R' in constr: (R1 :: S )
 | _ => constr:(R :: nil)
 end.

Lemma SEP_entail':
 forall R' Delta P Q R,
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- ` (fold_right_sepcon R') ->
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx Q (SEPx R')).
Proof.
intros.
apply andp_right.
apply andp_left2; apply andp_left1; auto.
apply andp_right.
do 2 apply andp_left2; apply andp_left1; auto.
eapply derives_trans; [ apply H|].
apply derives_refl.
Qed.

Lemma SEP_entail'_fupd:
 forall R' Delta P Q R,
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- ` (|={Ensembles.Full_set}=> fold_right_sepcon R') ->
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- |={Ensembles.Full_set}=> PROPx P (LOCALx Q (SEPx R')).
Proof.
intros.
eapply derives_trans, corable_andp_fupd, corable_prop.
apply andp_right.
apply andp_left2; apply andp_left1; auto.
eapply derives_trans, local_andp_fupd.
apply andp_right.
do 2 apply andp_left2; apply andp_left1; auto.
eapply derives_trans; [ apply H|].
apply derives_refl.
Qed.

Arguments sem_cmp c !t1 !t2 / v1 v2.

(* The following lines should not be needed, and was not needed
 in Coq 8.3, but in Coq 8.4 they seem to be necessary. *)
Definition ListClassicalSep_environ := @LiftClassicalSep environ.

#[export] Hint Resolve ListClassicalSep_environ : typeclass_instances.

Definition func_ptr' f v := func_ptr f v && emp.

#[export] Hint Resolve func_ptr_isptr: saturate_local.
#[export] Hint Resolve SeparationLogic.func_ptr_valid_pointer: valid_pointer.

Lemma func_ptr'_isptr: forall f v, func_ptr' f v |-- !! isptr v.
Proof.
intros.
unfold func_ptr'.
apply andp_left1. apply func_ptr_isptr.
Qed.
#[export] Hint Resolve func_ptr'_isptr: saturate_local.

Lemma func_ptr'_valid_pointer: forall spec f, func_ptr' spec f |-- valid_pointer f.
Proof. intros. unfold func_ptr'.
apply andp_left1. apply SeparationLogic.func_ptr_valid_pointer. Qed.
#[export] Hint Resolve func_ptr'_valid_pointer : valid_pointer.

Lemma split_func_ptr':
 forall fs p, func_ptr' fs p = func_ptr' fs p * func_ptr' fs p.
Proof.
intros.
unfold func_ptr'.
pose proof (corable_func_ptr fs p).
rewrite  corable_andp_sepcon1 by auto.
rewrite emp_sepcon.
rewrite <- andp_assoc.
f_equal.
apply pred_ext. apply andp_right; auto. apply andp_left2; auto.
Qed.

Lemma approx_func_ptr': forall (A: Type) fsig0 cc P (Q: A -> environ -> mpred) (v: val) (n: nat),
  compcert_rmaps.RML.R.approx (S n) (func_ptr' (NDmk_funspec fsig0 cc A P Q) v) = compcert_rmaps.RML.R.approx (S n) (func_ptr' (NDmk_funspec fsig0 cc A (fun a rho => compcert_rmaps.RML.R.approx n (P a rho)) (fun a rho => compcert_rmaps.RML.R.approx n (Q a rho))) v).
Proof.
  intros.
  unfold func_ptr'.
  rewrite !approx_andp.
  rewrite <- ! (andp_comm (_ _ emp)).
  apply (@f_equal _ _ (andp (compcert_rmaps.RML.R.approx (S n) emp))).
  apply (approx_func_ptr A fsig0 cc P Q).
Qed.

Lemma lift0_unfold: forall {A} (f: A)  rho,  lift0 f rho = f.
Proof. reflexivity. Qed.

Lemma lift0_unfoldC: forall {A} (f: A) (rho: environ),  `f rho = f.
Proof. reflexivity. Qed.

Lemma lift1_unfold: forall {A1 B} (f: A1 -> B) a1 rho,
        lift1 f a1 rho = f (a1 rho).
Proof. reflexivity. Qed.

Lemma lift1_unfoldC: forall {A1 B} (f: A1 -> B) a1 (rho: environ),
        `f a1 rho = f (a1 rho).
Proof. reflexivity. Qed.

Lemma lift2_unfold: forall {A1 A2 B} (f: A1 -> A2 -> B) a1 a2 (rho: environ),
        lift2 f a1 a2 rho = f (a1 rho) (a2 rho).
Proof. reflexivity. Qed.

Lemma lift2_unfoldC: forall {A1 A2 B} (f: A1 -> A2 -> B) a1 a2 (rho: environ),
        `f a1 a2 rho = f (a1 rho) (a2 rho).
Proof. reflexivity. Qed.

Lemma lift3_unfold: forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B) a1 a2 a3 (rho: environ),
        lift3 f a1 a2 a3 rho = f (a1 rho) (a2 rho) (a3 rho).
Proof. reflexivity. Qed.

Lemma lift3_unfoldC: forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B) a1 a2 a3 (rho: environ),
        `f a1 a2 a3 rho = f (a1 rho) (a2 rho) (a3 rho).
Proof. reflexivity. Qed.

Lemma lift4_unfold: forall {A1 A2 A3 A4 B} (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4 (rho: environ),
        lift4 f a1 a2 a3 a4 rho = f (a1 rho) (a2 rho) (a3 rho) (a4 rho).
Proof. reflexivity. Qed.

Lemma lift4_unfoldC: forall {A1 A2 A3 A4 B} (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4 (rho: environ),
        `f a1 a2 a3 a4 rho = f (a1 rho) (a2 rho) (a3 rho) (a4 rho).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @lift0_unfold @lift1_unfold @lift2_unfold @lift3_unfold @lift4_unfold : norm2.
#[export] Hint Rewrite @lift0_unfoldC @lift1_unfoldC @lift2_unfoldC @lift3_unfoldC @lift4_unfoldC : norm2.

Lemma alift0_unfold: forall {A} (f: A)  rho,  alift0 f rho = f.
Proof. reflexivity. Qed.

Lemma alift1_unfold: forall {A1 B} (f: A1 -> B) a1 rho,
        alift1 f a1 rho = f (a1 rho).
Proof. reflexivity. Qed.

Lemma alift2_unfold: forall {A1 A2 B} (f: A1 -> A2 -> B) a1 a2 (rho: argsEnviron),
        alift2 f a1 a2 rho = f (a1 rho) (a2 rho).
Proof. reflexivity. Qed.

Lemma alift3_unfold: forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B) a1 a2 a3 (rho: argsEnviron),
        alift3 f a1 a2 a3 rho = f (a1 rho) (a2 rho) (a3 rho).
Proof. reflexivity. Qed.

Lemma alift4_unfold: forall {A1 A2 A3 A4 B} (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4 (rho: argsEnviron),
        alift4 f a1 a2 a3 a4 rho = f (a1 rho) (a2 rho) (a3 rho) (a4 rho).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @alift0_unfold @alift1_unfold @alift2_unfold @alift3_unfold @alift4_unfold : norm2.

Lemma subst_lift0: forall {A} id v (f: A),
        subst id v (lift0 f) = lift0 f.
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift0': forall {A} id v (f: A),
        subst id v (fun _ => f) = (fun _ => f).
Proof.
intros. extensionality rho; reflexivity.
Qed.

#[export] Hint Rewrite @subst_lift0' : subst.

Lemma subst_lift0C:
  forall {B} id (v: environ -> val) (f: B) ,
          subst id v (`f) = `f.
Proof.
intros. extensionality rho; reflexivity.
Qed.

#[export] Hint Rewrite @subst_lift0 @subst_lift0C : subst.

Lemma subst_lift1:
  forall {A1 B} id v (f: A1 -> B) a,
          subst id v (lift1 f a) = lift1 f (subst id v a).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift1':
  forall {A1 B} id v (f: A1 -> B) a,
          subst id v (fun rho => f (a rho)) = fun rho => f (subst id v a rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift1C:
  forall {A1 B} id (v: environ -> val) (f: A1 -> B) (a: environ -> A1),
          subst id v (`f a)  = `f (subst id v a).
Proof.
intros. extensionality rho; reflexivity.
Qed.

#[export] Hint Rewrite @subst_lift1 @subst_lift1C  : subst.

Lemma subst_lift2:
  forall {A1 A2 B} id v (f: A1 -> A2 -> B) a b,
          subst id v (lift2 f a b) = lift2 f (subst id v a) (subst id v b).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift2':
  forall {A1 A2 B} id v (f: A1 -> A2 -> B) a b,
          subst id v (fun rho => f (a rho) (b rho)) = fun rho => f (subst id v a rho) (subst id v b rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift2C:
  forall {A1 A2 B} id (v: environ -> val) (f: A1 -> A2 -> B) (a: environ -> A1) (b: environ -> A2),
          subst id v (`f a b) = `f (subst id v a) (subst id v b).
Proof.
intros. extensionality rho; reflexivity.
Qed.

#[export] Hint Rewrite @subst_lift2 @subst_lift2C : subst.

Lemma subst_lift3:
  forall {A1 A2 A3 B} id v (f: A1 -> A2 -> A3 -> B) a1 a2 a3,
          subst id v (lift3 f a1 a2 a3) = lift3 f (subst id v a1) (subst id v a2) (subst id v a3).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift3':
  forall {A1 A2 A3 B} id v (f: A1 -> A2 -> A3 -> B) a1 a2 a3,
          subst id v (fun rho => f (a1 rho) (a2 rho) (a3 rho)) =
          fun rho => f (subst id v a1 rho) (subst id v a2 rho) (subst id v a3 rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift3C:
  forall {A1 A2 A3 B} id (v: environ -> val) (f: A1 -> A2 -> A3 -> B)
                  (a1: environ -> A1) (a2: environ -> A2) (a3: environ -> A3),
          subst id v (`f a1 a2 a3) = `f (subst id v a1) (subst id v a2) (subst id v a3).
Proof.
intros. extensionality rho; reflexivity.
Qed.

#[export] Hint Rewrite @subst_lift3 @subst_lift3C : subst.

Lemma subst_lift4:
  forall {A1 A2 A3 A4 B} id v (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4,
          subst id v (lift4 f a1 a2 a3 a4) = lift4 f (subst id v a1) (subst id v a2) (subst id v a3) (subst id v a4).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift4':
  forall {A1 A2 A3 A4 B} id v (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4,
          subst id v (fun rho => f (a1 rho) (a2 rho) (a3 rho) (a4 rho)) =
          fun rho => f (subst id v a1 rho) (subst id v a2 rho) (subst id v a3 rho) (subst id v a4 rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift4C:
  forall {A1 A2 A3 A4 B} id (v: environ -> val) (f: A1 -> A2 -> A3 -> A4 -> B)
                  (a1: environ -> A1) (a2: environ -> A2) (a3: environ -> A3) (a4: environ -> A4),
          subst id v (`f a1 a2 a3 a4) = `f (subst id v a1) (subst id v a2) (subst id v a3) (subst id v a4).
Proof.
intros. extensionality rho; reflexivity.
Qed.

#[export] Hint Rewrite @subst_lift4 @subst_lift4C : subst.


Lemma bool_val_int_eq_e:
  forall i j m, Cop.bool_val (Val.of_bool (Int.eq i j)) type_bool m = Some true ->
    i=j.
Proof.
 intros.
 unfold Cop.bool_val in H.
 destruct Archi.ptr64 eqn:Hp;
 revert H; case_eq (Val.of_bool (Int.eq i j)); simpl; intros; inv H0.
+
 pose proof (Int.eq_spec i j).
 revert H H0; case_eq (Int.eq i j); intros; auto.
 simpl in H0; unfold Vfalse in H0. inv H0. rewrite Int.eq_true in H2. inv H2.
+
 pose proof (Int.eq_spec i j).
 revert H H0; case_eq (Int.eq i j); intros; auto.
 simpl in H0; unfold Vfalse in H0. inv H0. inv H2.
+ unfold Val.of_bool in H.  destruct (Int.eq i j); inv H.
Qed.

Lemma bool_val_notbool_ptr:
    forall v t m,
   match t with Tpointer _ _ => True | _ => False end ->
   (Cop.bool_val (force_val (Cop.sem_notbool v t m)) type_bool m = Some true)
        = (v = nullval).
Proof.
 intros.
 destruct t; try contradiction. clear H.
 unfold Cop.sem_notbool, Cop.bool_val, Val.of_bool, Cop.classify_bool, nullval.
 destruct Archi.ptr64 eqn:Hp; simpl;
 apply prop_ext; split; intros.
-
 destruct v; simpl in H; try solve [inv H].
 destruct (Int64.eq i Int64.zero) eqn:?; inv H.
  apply expr_lemmas.int64_eq_e in Heqb. subst; reflexivity.
 destruct (Memory.Mem.weak_valid_pointer m b (Ptrofs.unsigned i)) eqn:?;
  simpl in H; inv H.
-
  subst v; simpl. reflexivity.
-
 destruct v; simpl in H; try solve [inv H].
 destruct (Int.eq i Int.zero) eqn:?; inv H.
  apply int_eq_e in Heqb. subst; reflexivity.
 destruct (Memory.Mem.weak_valid_pointer m b (Ptrofs.unsigned i)) eqn:?;
  simpl in H; inv H.
-
  subst v; simpl. reflexivity.
Qed.

Definition retval : environ -> val := eval_id ret_temp.

#[export] Hint Rewrite eval_id_same : norm.
#[export] Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : norm.

Lemma simpl_get_result1:
 forall (f: val -> Prop) i, @liftx (Tarrow environ (LiftEnviron Prop)) (@liftx (Tarrow val (LiftEnviron Prop))f retval) (get_result1 i) = `f (eval_id i).
Proof.
intros; extensionality rho.
unfold_lift; unfold retval, get_result1.
f_equal.
Qed.
#[export] Hint Rewrite simpl_get_result1: norm.

Lemma retval_get_result1:
   forall i rho, retval (get_result1 i rho) = (eval_id i rho).
Proof. intros. unfold retval, get_result1. simpl.
 normalize.
Qed.
#[export] Hint Rewrite retval_get_result1 : norm.

Lemma retval_ext_rval:
  forall ge t v, retval (make_ext_rval ge t v) = force_val v.
Proof.
 intros. unfold retval, eval_id; simpl. unfold make_ext_rval; simpl.
destruct t eqn:?H;  destruct v eqn:?H; simpl; auto.
Abort.

Lemma retval_lemma1:
  forall rho v,     retval (env_set rho ret_temp v) = v.
Proof.
 intros. unfold retval.  normalize.
Qed.
#[export] Hint Rewrite retval_lemma1 : norm.

Lemma retval_make_args:
  forall v rho, retval (make_args (ret_temp::nil) (v::nil) rho) = v.
Proof. intros.  unfold retval, eval_id; simpl. try rewrite Map.gss. reflexivity.
Qed.
#[export] Hint Rewrite retval_make_args: norm2.

Lemma andp_makeargs:
   forall (a b: environ -> mpred) d e,
   `(a && b) (make_args d e) = `a (make_args d e) && `b (make_args d e).
Proof. intros. reflexivity. Qed.
#[export] Hint Rewrite andp_makeargs: norm2.

Lemma local_makeargs:
   forall (f: val -> Prop) v,
   `(local (`(f) retval)) (make_args (cons ret_temp nil) (cons v nil))
    = (local (`(f) `(v))).
Proof. intros. reflexivity. Qed.
#[export] Hint Rewrite local_makeargs: norm2.

Lemma simpl_and_get_result1:
  forall (Q R: environ->mpred) i,
    `(Q && R) (get_result1 i) = `Q (get_result1 i) && `R (get_result1 i).
Proof. intros. reflexivity. Qed.
#[export] Hint Rewrite simpl_and_get_result1 : norm2.

Lemma liftx_local_retval:
  forall (P: val -> Prop) i,
   `(local (`P retval)) (get_result1 i) = local (`P (eval_id i)).
Proof. intros. reflexivity. Qed.
#[export] Hint Rewrite liftx_local_retval : norm2.

#[export] Hint Rewrite bool_val_notbool_ptr using apply Logic.I : norm.

Lemma Vint_inj': forall i j,  (Vint i = Vint j) =  (i=j).
Proof. intros; apply prop_ext; split; intro; congruence. Qed.

Lemma overridePost_normal_right:
  forall P Q R,
   (P |-- Q) ->
   P |-- RA_normal (overridePost Q R).
Proof. intros.
  destruct R; simpl; auto.
Qed.

Fixpoint fold_right_and P0 (l: list Prop) : Prop :=
 match l with
 | nil => P0
 | b::r => b  /\ fold_right_and P0 r
 end.

Fixpoint fold_right_and_True (l: list Prop) : Prop :=
 match l with
 | nil => True
 | b :: nil => b
 | b::r => b /\ fold_right_and_True r
 end.

Definition fold_right_PROP_SEP (l1: list Prop) (l2: list mpred) : mpred :=
 match l1 with
 | nil => fold_right_sepcon l2
 | l => !! (fold_right_and_True l) && fold_right_sepcon l2
 end.

Lemma fold_right_PROP_SEP_spec: forall l1 l2,
  fold_right_PROP_SEP l1 l2 = !! (fold_right and True l1) && fold_right_sepcon l2.
Proof.
  intros.
  assert (fold_right_and_True l1 <-> fold_right and True l1).
  {
    destruct l1; [tauto |].
    revert P; induction l1; intros.
    - simpl; tauto.
    - change (P /\ fold_right_and_True (a :: l1) <-> P /\ fold_right and True (a :: l1)).
      specialize (IHl1 a).
      tauto.
  }
  destruct l1.
  + simpl.
    normalize.
  + unfold fold_right_PROP_SEP.
    rewrite H.
    auto.
Qed.

Lemma typed_true_isptr:
 forall t, match t with Tpointer _ _ => True | Tarray _ _ _ => True | Tfunction _ _ _ => True | _ => False end ->
          typed_true t = isptr.
Proof.
intros. extensionality x; apply prop_ext.
unfold typed_true, bool_val, strict_bool_val, isptr.
destruct t; try contradiction;
destruct Archi.ptr64 eqn:Hp;
destruct x; try tauto; intuition (try congruence);
revert H0; simple_if_tac; intro H0; inv H0.
Qed.

#[export] Hint Rewrite typed_true_isptr using apply Logic.I : norm.

Ltac super_unfold_lift_in H :=
   cbv delta [liftx LiftEnviron Tarrow Tend lift_S lift_T
    lift_prod lift_last lifted lift_uncurry_open lift_curry lift lift0
    lift1 lift2 lift3] beta iota in H.

Ltac super_unfold_lift' :=
  cbv delta [liftx LiftEnviron Tarrow Tend lift_S lift_T
    lift_prod lift_last lifted lift_uncurry_open lift_curry lift lift0
    lift1 lift2 lift3] beta iota.

Lemma tc_eval'_id_i:
  forall Delta t i rho,
               tc_environ Delta rho ->
              (temp_types Delta)!i = Some t ->
              tc_val' t (eval_id i rho).
Proof.
intros.
unfold tc_environ in H.
destruct rho.
destruct H as [? _].
destruct (H i t H0) as [v [? ?]].
unfold eval_id. simpl in *. rewrite H1. simpl; auto.
Qed.

Lemma is_int_e:
 forall v i s , is_int i s v -> exists n, v = Vint n /\ is_int i s v.
Proof.
intros.
 destruct i,s,v; try inv H; simpl; eauto.
Qed.

Tactic Notation "name" ident(s) constr(id) :=
    idtac "Warning: the 'name' tactic no loger does anything useful, and will be removed in future versions of VST".

Definition reflect_temps_f (rho: environ) (b: Prop) (i: ident) (t: type) : Prop :=
  tc_val' t (eval_id i rho) /\ b.

Definition reflect_temps (Delta: tycontext) (rho: environ) : Prop :=
    PTree.fold (reflect_temps_f rho) (temp_types Delta) True.

Lemma reflect_temps_valid:
  forall Delta rho,
    tc_environ Delta rho -> reflect_temps Delta rho.
Proof.
intros.
unfold reflect_temps.
rewrite PTree.fold_spec.
remember  (PTree.elements (temp_types Delta)) as el.
assert (forall i v, In (i,v) el -> (temp_types Delta) ! i = Some v).
 intros. subst el. apply PTree.elements_complete; auto.
clear Heqel.
assert (forall b: Prop, b -> fold_left
  (fun (a : Prop) (p : positive * type) =>
   reflect_temps_f rho a (fst p) (snd p)) el b);
  [ | auto].
revert H0; induction el; simpl; intros; auto.
unfold reflect_temps_f at 2.
destruct a as [i t]; simpl; auto.
apply IHel; auto.
split; auto.
eapply tc_eval'_id_i.
eassumption.
apply H0; auto.
Qed.

Definition abbreviate {A:Type} (x:A) := x.
Arguments abbreviate {A} {x}.

Ltac clear_Delta :=
match goal with
| Delta := @abbreviate tycontext ?G |- _ =>
   try match goal with |- context [ret_type Delta] =>
      let x := constr:(ret_type G) in let x := eval hnf in x
       in change (ret_type Delta) with x in *
   end;
   try clear Delta
| _ => idtac
end;
match goal with
 |  DS := @abbreviate (PTree.t funspec) _  |- _ =>
   first [clear DS | clearbody DS]
 | |- _ => idtac
 end.

Ltac clear_Delta_specs :=
 lazymatch goal with
 |  DS := @abbreviate (PTree.t funspec) _  |- _ => clearbody DS
 | |- _ => idtac
 end.

Lemma is_true_negb:
 forall a, is_true (negb a) -> a=false.
Proof.
destruct a; auto; try contradiction.
Qed.

Lemma sem_cast_pointer2':
  forall (v : val) (t1 t2: type),
  match t1 with
  | Tpointer _ _ => is_true (negb (eqb_type t1 int_or_ptr_type))
  | Tint I32 _ _ => if Archi.ptr64 then False else True
  | Tlong _ _ => if Archi.ptr64 then True else False
  | _ => False end ->
  match t2 with
  | Tpointer _ _ => is_true (negb (eqb_type t2 int_or_ptr_type))
  | Tint I32 _ _ => if Archi.ptr64 then False else True
  | Tlong _ _ => if Archi.ptr64 then True else False
  | _ => False end ->
  is_pointer_or_null v -> force_val (sem_cast t1 t2 v) = v.
Proof.
intros.
unfold sem_cast, classify_cast, force_val; simpl.
destruct Archi.ptr64 eqn:Hp;
destruct t1; try contradiction; try destruct i; try contradiction; auto;
destruct t2; try contradiction; try destruct i; try contradiction; auto;
try rewrite (is_true_negb _ H); try rewrite (is_true_negb _ H0);
destruct v; inv H1; auto.
Qed.

#[export] Hint Rewrite sem_cast_pointer2' using (try apply Logic.I; try assumption; reflexivity) : norm.

Lemma sem_cast_pointer2:
  forall v t1 t2 t3 t1' t2',
   t1' = Tpointer t1 noattr ->
   t2' = Tpointer t2 noattr ->
   tc_val (Tpointer t3 noattr) v ->
   force_val (sem_cast t1' t2' v) = v.
Proof.
intros.
subst.
reflexivity.
Qed.

Lemma force_eval_var_int_ptr :
forall  {cs: compspecs}  Delta rho i t,
tc_environ Delta rho ->
tc_lvalue Delta (Evar i t) rho |--
        !! (force_val
            match eval_var i t rho with
            | Vptr _ _ => Some (eval_var i t rho)
            | _ => None
            end = eval_var i t rho).
Proof.
intros.
eapply derives_trans.
apply typecheck_lvalue_sound; auto.
simpl; normalize.
unfold eval_var in *.
destruct (Map.get (ve_of rho) i) as [[? ?] |].
destruct (eqb_type t t0); try discriminate; reflexivity.
destruct (Map.get (ge_of rho) i).
reflexivity.
inv H0.
Qed.

Lemma is_pointer_or_null_force_int_ptr:
   forall v, is_pointer_or_null v -> (force_val
        match v with
        | Vint _ => if Archi.ptr64 then None else Some v
        | Vlong _ => if Archi.ptr64 then Some v else None
        | Vptr _ _ => Some v
        | _ => None
        end) = v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
#[export] Hint Rewrite is_pointer_or_null_force_int_ptr using assumption : norm1.


Lemma is_pointer_force_int_ptr:
   forall v, isptr v -> (force_val
        match v with
        | Vint _ => if Archi.ptr64 then None else Some v
        | Vlong _ => if Archi.ptr64 then Some v else None
        | Vptr _ _ => Some v
        | _ => None
        end) = v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
#[export] Hint Rewrite is_pointer_force_int_ptr using assumption : norm1.


Lemma is_pointer_or_null_match :
   forall v, is_pointer_or_null v ->
        (match v with
        | Vint _ => if Archi.ptr64 then None else Some v
        | Vlong _ => if Archi.ptr64 then Some v else None
        | Vptr _ _ => Some v
        | _ => None
         end) = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
#[export] Hint Rewrite is_pointer_or_null_match using assumption : norm1.

Lemma is_pointer_force_int_ptr2:
   forall v, isptr v ->
        match v with
        | Vint _ => if Archi.ptr64 then None else Some v
        | Vlong _ => if Archi.ptr64 then Some v else None
        | Vptr _ _ => Some v
        | _ => None
         end = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
#[export] Hint Rewrite is_pointer_force_int_ptr2 using assumption : norm1.

Lemma is_pointer_or_null_force_int_ptr2:
   forall v, is_pointer_or_null (force_val
        match v with
        | Vint _ => Some v
        | Vptr _ _ => Some v
        | _ => None
         end) -> (force_val
        match v with
        | Vint _ => Some v
        | Vptr _ _ => Some v
        | _ => None
         end) = v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.

#[export] Hint Rewrite is_pointer_or_null_force_int_ptr2 using assumption : norm1.

Lemma isptr_match : forall w0,
is_pointer_or_null
         match
           match w0 with
          | Vint _ => if Archi.ptr64 then None else Some w0
          | Vlong _ => if Archi.ptr64 then Some w0 else None
          | Vptr _ _ => Some w0
           | _ => None
           end
         with
         | Some v' => v'
         | None => Vundef
         end
= is_pointer_or_null w0.
intros.
unfold is_pointer_or_null.
destruct Archi.ptr64 eqn:Hp;
destruct w0; auto.
Qed.

#[export] Hint Rewrite isptr_match : norm1.

Lemma eval_cast_neutral_tc_val:
   forall v, (exists t, tc_val t v /\ is_pointer_type t = true) ->
       sem_cast_pointer v = Some v.
Proof.
intros.
destruct H as [t [? ?]].
hnf in H.
unfold is_pointer_type in H0.
unfold sem_cast_pointer.
destruct (eqb_type t int_or_ptr_type);
destruct t,v; inv H0; inv H; reflexivity.
Qed.

#[export] Hint Rewrite eval_cast_neutral_tc_val using solve [eauto] : norm.

Lemma eval_cast_neutral_is_pointer_or_null:
   forall v, is_pointer_or_null v -> sem_cast_pointer v = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
#[export] Hint Rewrite eval_cast_neutral_is_pointer_or_null using assumption : norm.

Lemma is_pointer_or_null_eval_cast_neutral:
  forall v, is_pointer_or_null (force_val (sem_cast_pointer v)) = is_pointer_or_null v.
Proof. destruct v; reflexivity. Qed.
#[export] Hint Rewrite is_pointer_or_null_eval_cast_neutral : norm.

Lemma eval_cast_neutral_isptr:
   forall v, isptr v -> sem_cast_pointer v = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
#[export] Hint Rewrite eval_cast_neutral_isptr using assumption : norm.

Arguments ret_type !Delta /.

Arguments Datatypes.id {A} x / .

Lemma raise_sepcon:
 forall A B : environ -> mpred ,
    (fun rho: environ => A rho * B rho) = (A * B).
Proof. reflexivity. Qed.
#[export] Hint Rewrite raise_sepcon : norm1.

Lemma lift1_lift1_retval {A}: forall i (P: val -> A),
lift1 (lift1 P retval) (get_result1 i) = lift1 P (eval_id i).
Proof. intros.  extensionality rho.
  unfold lift1.  f_equal; normalize.
Qed.

Lemma lift_lift_retval:
  forall (i: ident) P,
   @liftx (Tarrow environ (LiftEnviron mpred))
     (@liftx (Tarrow val (LiftEnviron mpred)) P retval) (get_result1 i) = `P (eval_id i).
Proof.
 reflexivity.
Qed.
#[export] Hint Rewrite lift_lift_retval: norm2.

Lemma lift_lift_x:  (* generalizes lift_lift_val *)
  forall t t' P (v: t),
  (@liftx (Tarrow t (LiftEnviron t')) P (@liftx (LiftEnviron t) v)) =
  (@liftx (LiftEnviron t') (P v)).
Proof. reflexivity. Qed.
#[export] Hint Rewrite lift_lift_x : norm2.

Lemma lift0_exp {A}{NA: NatDed A}:
  forall (B: Type) (f: B -> A), lift0 (exp f) = EX x:B, lift0 (f x).
Proof. intros; extensionality rho; unfold lift0. simpl.
f_equal; extensionality b; auto.
Qed.

Lemma lift0C_exp {A}{NA: NatDed A}:
  forall (B: Type) (f: B -> A), `(exp f) = EX x:B, `(f x).
Proof.
intros. unfold_lift. simpl. extensionality rho. f_equal; extensionality x; auto.
Qed.
#[export] Hint Rewrite @lift0_exp : norm2.
#[export] Hint Rewrite @lift0C_exp : norm2.

Lemma lift0_andp {A}{NA: NatDed A}:
 forall P Q,
   lift0 (@andp A NA P Q) = andp (lift0 P) (lift0 Q).
Proof.
intros. extensionality rho. reflexivity.
Qed.

Lemma lift0C_andp {A}{NA: NatDed A}:
 forall P Q: A,
  `(@andp A NA P Q) =
  andp (`P) (`Q).
Proof.
intros. extensionality rho. reflexivity.
Qed.

Lemma lift0_prop {A}{NA: NatDed A}:
 forall P, lift0 (!! P) = !!P.
Proof. intros. extensionality rho; reflexivity. Qed.

Lemma lift0C_prop {A}{NA: NatDed A}:
 forall P, @liftx (LiftEnviron A) (@prop A NA P) =
                  @prop (environ -> A) _ P.
Proof. reflexivity. Qed.

Lemma lift0_sepcon {A}{NA: NatDed A}{SA: SepLog A}:
 forall P Q,
  lift0 (@sepcon A NA SA P Q) = sepcon (lift0 P) (lift0 Q).
Proof.
intros. extensionality rho. reflexivity.
Qed.

Lemma lift0C_sepcon {A}{NA: NatDed A}{SA: SepLog A}:
 forall P Q N2 S2,
  (@liftx (LiftEnviron A) (@sepcon A N2 S2 P Q)) =
  (@sepcon (environ->A) _ _
     (@liftx (LiftEnviron A) P)
     (@liftx (LiftEnviron A) Q)).
Proof. reflexivity. Qed.

Lemma lift0_later {A}{NA: NatDed A}{IA: Indir A}:
  forall P:A,
   lift0 (@later A NA IA P) = later  (lift0 P).
Proof. intros. reflexivity. Qed.

Lemma lift0C_later {A}{NA: NatDed A}{IA: Indir A}:
  forall P:A,
   `(@later A NA IA P) = @later (environ->A) _ _ (`P).
Proof. intros. reflexivity. Qed.

#[export] Hint Rewrite (@lift0C_sepcon mpred _ _) : norm.
#[export] Hint Rewrite (@lift0C_andp mpred _) : norm.
#[export] Hint Rewrite (@lift0C_exp mpred _) : norm.
#[export] Hint Rewrite (@lift0C_later mpred _ _) : norm.
#[export] Hint Rewrite (@lift0C_prop mpred _) : norm.

#[export] Hint Rewrite
    @lift1_lift1_retval
    @lift0_exp
    @lift0_sepcon
    @lift0_prop
    @lift0_later
    : norm2.

Lemma fst_unfold: forall {A B} (x: A) (y: B), fst (x,y) = x.
Proof. reflexivity. Qed.
Lemma snd_unfold: forall {A B} (x: A) (y: B), snd (x,y) = y.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @fst_unfold @snd_unfold : norm.

Lemma eq_True:
   forall (A: Prop), A -> (A=True).
Proof.
intros.
apply prop_ext; intuition.
Qed.

Lemma derives_extract_PROP :
  forall (P1: Prop) A P QR S,
     (P1 -> A && PROPx P QR |-- S) ->
     A && PROPx (P1::P) QR |-- S.
Proof.
unfold PROPx in *.
intros.
rewrite fold_right_cons.
normalize.
eapply derives_trans; [ | apply H; auto].
normalize.
Qed.

Lemma local_andp_prop:  forall P Q, local P && prop Q = prop Q && local P.
Proof. intros. apply andp_comm. Qed.
Lemma local_andp_prop1: forall P Q R, local P && (prop Q && R) = prop Q && (local P && R).
Proof. intros. rewrite andp_comm. rewrite andp_assoc. f_equal. apply andp_comm. Qed.
#[export] Hint Rewrite local_andp_prop local_andp_prop1 : norm2.

Lemma local_sepcon_assoc1:
   forall P Q R, (local P && Q) * R = local P && (Q * R).
Proof.
intros.
extensionality rho; unfold local, lift1; simpl.
apply pred_ext; normalize.
Qed.
Lemma local_sepcon_assoc2:
   forall P Q R, R * (local P && Q) = local P && (R * Q).
Proof.
intros.
extensionality rho; unfold local, lift1; simpl.
apply pred_ext; normalize.
Qed.
#[export] Hint Rewrite local_sepcon_assoc1 local_sepcon_assoc2 : norm2.

Definition do_canon (x y : environ->mpred) := (sepcon x y).

Ltac strip1_later P cP :=
 lazymatch P with
 | do_canon ?L ?R =>
     let cL := (fun L' =>
          let cR := (fun R' => let P' := constr:(do_canon L' R') in cP P')
           in  strip1_later R cR)
      in strip1_later L cL
 | PROPx ?A ?QR =>
           let cQR := (fun QR' => let P' := constr:(PROPx A QR') in cP P')
            in strip1_later QR cQR
 | LOCALx ?Q ?R =>
           let cR := (fun R' => let P' := constr:(LOCALx Q R') in cP P')
            in strip1_later R cR
 | @SEPx environ ?R =>
    let cR := fun R' => (let P' := constr:(@SEPx environ R') in cP P') in
     strip1_later R cR
 | ?L :: ?R =>
      let cL := (fun L' =>
          let cR := (fun R' => let P' := constr:(L'::R') in cP P') in
          strip1_later R cR)
       in strip1_later L cL
 | ?L && ?R =>
      let cL := (fun L' =>
          let cR := (fun R' => let P' := constr:(L'&&R') in cP P') in
          strip1_later R cR)
       in strip1_later L cL
 | sepcon ?L ?R =>
      let cL := (fun L' =>
          let cR := (fun R' => let P' := constr:(sepcon L' R') in cP P') in
          strip1_later R cR)
       in strip1_later L cL
 | |> ?L => cP L
 | _ => cP P
end.

Lemma andp_later_derives {A} {NA: NatDed A}{IA: Indir A}:
  forall P Q P' Q': A, (P |-- |> P') -> (Q |-- |> Q') -> P && Q |-- |> (P' && Q').
Proof.
intros. rewrite later_andp. apply andp_derives; auto. Qed.

Lemma sepcon_later_derives {A} {NA: NatDed A}{SL: SepLog A}{IA: Indir A}{SI: SepIndir A}:
  forall P Q P' Q': A, (P |-- |> P') -> (Q |-- |> Q') -> P * Q |-- |> (P' * Q').
Proof.
intros. rewrite later_sepcon. apply sepcon_derives; auto. Qed.

#[export] Hint Resolve andp_later_derives sepcon_later_derives sepcon_derives
              andp_derives imp_derives now_later derives_refl: derives.

(* Definitions of convertPre and NDmk_funspec' are to support
  compatibility with old-style funspecs (see funspec_old.v) *)
Definition convertPre (f: funsig) A
  (Pre: A -> environ -> mpred)  (w: A) (ae: argsEnviron) : mpred :=
 !! (length (snd ae) = length (fst f)) &&
 Pre w (make_args (map fst (fst f)) (snd ae)
    (mkEnviron (fst ae)   (Map.empty (block*type)) (Map.empty val))).

Definition NDmk_funspec' (f: funsig) (cc: calling_convention)
  (A: Type) (Pre Post: A -> environ -> mpred): funspec :=
  NDmk_funspec (compcert_rmaps.typesig_of_funsig f) cc
  A (convertPre f A Pre) Post.

Declare Scope funspec_scope.
Delimit Scope funspec_scope with funspec.
Global Open Scope funspec_scope.

Notation "'DECLARE' x s" := (x: ident, s: funspec)
   (at level 160, x at level 0, s at level 150, only parsing).

Definition NDsemax_external {Hspec: OracleKind} (ef: external_function)
  (A: Type) (P:A -> argsEnviron -> mpred) (Q: A -> environ -> mpred): Prop :=
  @semax_external Hspec ef (rmaps.ConstType A) (fun _ => P) (fun _ => Q).

Notation "'WITH' x : tx 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default tx (fun x => P%argsassert) (fun x => Q%assert))
            (at level 200, x at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH' x : tx 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default tx (fun x => P%argsassert) (fun x => Q%assert))
            (at level 200, x at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2)
           (fun x => match x with (x1,x2) => P%argsassert end)
           (fun x => match x with (x1,x2) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2)
           (fun x => match x with (x1,x2) => P%argsassert end)
           (fun x => match x with (x1,x2) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3)
           (fun x => match x with (x1,x2,x3) => P%argsassert end)
           (fun x => match x with (x1,x2,x3) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3)
           (fun x => match x with (x1,x2,x3) => P%argsassert end)
           (fun x => match x with (x1,x2,x3) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4)
           (fun x => match x with (x1,x2,x3,x4) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4)
           (fun x => match x with (x1,x2,x3,x4) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5)
           (fun x => match x with (x1,x2,x3,x4,x5) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5)
           (fun x => match x with (x1,x2,x3,x4,x5) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
              x20 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             x20 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 , x21 : t21 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20*t21)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
              x20 at level 0, x21 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 , x21 : t21 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20*t21)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             x20 at level 0, x21 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 , x21 : t21 , x22 : t22 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20*t21*t22)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
              x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
              x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
              x20 at level 0, x21 at level 0, x22 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 , x21 : t21 , x22 : t22 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20*t21*t22)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22) => P%argsassert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             x20 at level 0, x21 at level 0, x22 at level 0,
              P at level 100, Q at level 100) : funspec_scope.

(* Notations for dependent funspecs *)

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) cc_default A
  (fun (ts: list Type) (x: t1*t2) =>
     match x with (x1,x2) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2) =>
     match x with (x1,x2) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2) =>
     match x with (x1,x2) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2) =>
     match x with (x1,x2) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3) =>
     match x with (x1,x2,x3) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3) =>
     match x with (x1,x2,x3) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3) =>
     match x with (x1,x2,x3) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3) =>
     match x with (x1,x2,x3) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4) =>
     match x with (x1,x2,x3,x4) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4) =>
     match x with (x1,x2,x3,x4) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5) =>
     match x with (x1,x2,x3,x4,x5) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5) =>
     match x with (x1,x2,x3,x4,x5) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6) =>
     match x with (x1,x2,x3,x4,x5,x6) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6) =>
     match x with (x1,x2,x3,x4,x5,x6) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7) =>
     match x with (x1,x2,x3,x4,x5,x6,x7) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7) =>
     match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             P at level 100, Q at level 100).

Fixpoint split_as_gv_temps (l: list localdef) : option ((list globals) * (list (ident * val))) :=
  match l with
    nil => Some (nil, nil)
  | temp i v :: l' => match split_as_gv_temps l' with
                        None => None
                      | Some (gvs, temps) => Some (gvs, (i,v)::temps)
                      end
  | lvar i t v :: l' => None
  | gvars g :: l' =>  match split_as_gv_temps l' with
                        None => None
                      | Some (gvs, temps) => Some (g::gvs, temps)
                      end
end.

Definition ImpossibleFunspec :=
   mk_funspec (nil,Tvoid) cc_default (rmaps.ConstType Impossible)
        (fun _ _ => FF) (fun _ _ => FF)
        (args_const_super_non_expansive _ _)
        (const_super_non_expansive _ _).

Notation LAMBDAx gs vals X := (PARAMSx vals (GLOBALSx gs X)) (only parsing).

Lemma prop_true_andp1 {A}{NA: NatDed A} :
  forall (P1 P2: Prop) Q ,
    P1 -> (!! (P1 /\ P2) && Q = !!P2 && Q).
Proof.
intros. f_equal; auto.  f_equal.  apply prop_ext; tauto.
Qed.
#[export] Hint Rewrite prop_true_andp1 using solve [auto 3 with typeclass_instances]: norm1.
#[export] Hint Rewrite prop_true_andp1 using assumption : norm.

Lemma and_assoc': forall A B C: Prop,
  ((A /\ B) /\ C) = (A /\ (B /\ C)).
Proof.
intros. apply prop_ext; apply and_assoc.
Qed.

Ltac splittablex_tac A :=
 match A with
 | _ <= _ < _ => fail 1
 | _ < _ <= _ => fail 1
 | _ <= _ <= _ => fail 1
 | _ < _ < _ => fail 1
 | _ <-> _ => fail 1
 | _ /\ _ => apply Logic.I
 end.

Definition splittablex (A: Prop) := True.

Lemma and_assoc_splittablex {T}{NT: NatDed T}: forall A B C: Prop,
    splittablex (A /\ B) ->
  !! ((A /\ B) /\ C) = !! (A /\ (B /\ C)).
Proof.
intros. rewrite and_assoc'; auto.
Qed.

Lemma and_assoc'' {T}{NT: NatDed T}: forall A B C: Prop,
  !! ((A /\ B) /\ C) = !! (A /\ (B /\ C)).
Proof.
intros. rewrite and_assoc'; auto.
Qed.


#[export] Hint Rewrite and_assoc_splittablex using
    match goal with |- splittablex ?A => splittablex_tac A end : normalize.
#[export] Hint Rewrite and_assoc_splittablex using
    match goal with |- splittablex ?A => splittablex_tac A end : gather_prop.

Ltac hoist_later_left :=
   match goal with
  | |- (?P |-- _) =>
        let cP := (fun P' =>
                   apply derives_trans with (|>P');
                    [ solve [ auto 50 with derives ] | ])
     in strip1_later P cP
  end.

(* Willam proposed that this versions of assert_PROP replace the ones in canon.v. *)
Tactic Notation "assert_PROP" constr(A) :=
  first [eapply (assert_later_PROP' A); [|hoist_later_left; apply derives_refl|] | apply (assert_PROP' A)]; [ | intro ].

Tactic Notation "assert_PROP" constr(A) "by" tactic1(t) :=
  first [eapply (assert_later_PROP' A); [|hoist_later_left; apply derives_refl|] | apply (assert_PROP' A)]; [ now t | intro ].

Tactic Notation "assert_PROP" constr(A) "as" simple_intropattern(H)  :=
  first [eapply (assert_later_PROP' A); [|hoist_later_left; apply derives_refl|] | apply (assert_PROP' A)]; [ | intro H ].

Tactic Notation "assert_PROP" constr(A) "as" simple_intropattern(H) "by" tactic1(t) :=
  first [eapply (assert_later_PROP' A); [|hoist_later_left; apply derives_refl|] | apply (assert_PROP' A)]; [ now t | intro H ].

Lemma semax_later_trivial: forall Espec  {cs: compspecs} Delta P c Q,
  @semax cs Espec Delta (|> P) c Q ->
  @semax cs Espec Delta P c Q.
Proof.
 intros until Q.
 apply semax_pre0.
  apply now_later.
Qed.

Ltac hoist_later_in_pre :=
     match goal with |- semax _ ?P _ _ =>
       match P with
       | context[@later] =>
            let cP := (fun P' => apply semax_pre0 with (|> P'); [solve [auto 50 with derives] | ])
             in strip1_later P cP
       | _ => apply semax_later_trivial
       end
     end.

Ltac simpl_tc_expr :=
    match goal with |- context [tc_expr ?A ?B] =>
        change (tc_expr A B) with (denote_tc_assert (typecheck_expr A B));
     (* These uses of 'simpl' are not too dangerous, for two reasons:
          (1) simpl_tc_expr is not used by any parts of Floyd except explicitly deprecated parts
          (2) the simpl is unlikely to blow up, because the arguments are just
                  clightgen-produced ASTs *)
        simpl typecheck_expr; simpl denote_tc_assert
    end.

Lemma prop_and1 {A}{NA: NatDed A}:
  forall P Q : Prop, P -> !!(P /\ Q) = !!Q.
Proof. intros. f_equal; apply prop_ext; tauto.
Qed.
#[export] Hint Rewrite prop_and1 using solve [auto 3 with typeclass_instances] : norm2.

Lemma subst_make_args':
  forall  {cs: compspecs}  id v (P: environ->mpred) fsig tl el,
  length tl = length el ->
  length (fst fsig) = length el ->
  subst id v (`P (make_args' fsig (eval_exprlist tl el))) =
           (`P (make_args' fsig (subst id v (eval_exprlist tl el)))).
Proof.
intros. unfold_lift. extensionality rho; unfold subst.
f_equal. unfold make_args'.
revert tl el H H0; induction (fst fsig); destruct tl,el; simpl; intros; inv H; inv H0.
reflexivity.
specialize (IHl _ _ H2 H1).
unfold_lift; rewrite IHl. auto.
Qed.
#[export] Hint Rewrite @subst_make_args' using (solve[reflexivity]) : subst.

Lemma map_cons: forall {A B} (f: A -> B) x y,
   map f (x::y) = f x :: map f y.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @map_cons : norm.
#[export] Hint Rewrite @map_cons : subst.

Lemma map_nil: forall {A B} (f: A -> B), map f nil = nil.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @map_nil : norm.
#[export] Hint Rewrite @map_nil : subst.

Definition rlt_ident_eq := ident_eq.  (* for convenience in selectively simplifying *)

Fixpoint remove_localdef_temp (i: ident) (l: list localdef) : list localdef :=
  match l with
  | nil => nil
  | d :: l0 =>
     let rest := remove_localdef_temp i l0 in
     match d with
     | temp j v =>
       if rlt_ident_eq i j
       then rest
       else d :: rest
     | _ => d :: rest
     end
  end.

Lemma subst_stackframe_of:
  forall {cs: compspecs} i v f, subst i v (stackframe_of f) = stackframe_of f.
Proof.
unfold stackframe_of; simpl; intros.
unfold subst.
extensionality rho.
induction (fn_vars f). reflexivity.
simpl map. repeat rewrite fold_right_cons.
f_equal.
apply IHl.
Qed.
#[export] Hint Rewrite @subst_stackframe_of : subst.

Lemma remove_localdef_temp_PROP: forall (i: ident) P Q R,
  EX old: val, subst i `(old) (PROPx P (LOCALx Q (SEPx R))) |--
  PROPx P (LOCALx (remove_localdef_temp i Q) (SEPx R)).
Proof.
  intros.
  apply exp_left; intro old.
  unfold PROPx.
  autorewrite with subst norm.
  apply andp_derives. apply derives_refl.
  unfold LOCALx.
  autorewrite with subst norm.
  apply andp_derives; auto; try apply derives_refl.
  induction Q; simpl fold_right.
  + autorewrite with subst norm; auto.
  + destruct a; [if_tac | ..];
    autorewrite with subst norm.
    - eapply derives_trans; [| exact IHQ].
      rewrite local_lift2_and.
      apply andp_left2; apply derives_refl.
    - rewrite !local_lift2_and.
      apply andp_derives; [| exact IHQ].
      unfold locald_denote.
      autorewrite with subst norm.
      unfold local, lift1; unfold_lift; intros ?.
      apply prop_derives; simpl.
      unfold subst; simpl; intros.
      rewrite eval_id_other in H0 by auto; auto.
    - rewrite !local_lift2_and.
      apply andp_derives; [| exact IHQ].
      unfold local, lift1; unfold_lift; intros rho.
      unfold subst; simpl.
      apply derives_refl.
    - rewrite !local_lift2_and.
      apply andp_derives; [| exact IHQ].
      unfold local, lift1; unfold_lift; intros rho.
      unfold subst; simpl.
      apply derives_refl.
Qed.

Lemma eval_id_denote_tc_initialized: forall Delta i t v,
  (temp_types Delta) ! i = Some t ->
  local (tc_environ Delta) && local (`and (`(eq v) (eval_id i)) `(v <> Vundef)) |-- denote_tc_initialized i t.
Proof.
  intros.
  intros rho.
  unfold local, lift1; unfold_lift; simpl.
  rewrite <- prop_and; apply prop_derives.
  intros [? [? ?]].
  destruct H0 as [? _].
  specialize (H0 _ _ H).
  destruct H0 as [v0 [? ?]].
  unfold eval_id in H1.
  rewrite H0 in *; clear H0; subst v; rename v0 into v.
  simpl in H2.
  specialize (H3 H2).
  eauto.
Qed.

Lemma PQR_denote_tc_initialized: forall Delta i t v P Q R,
  (temp_types Delta) ! i = Some t ->
  local (tc_environ Delta) && PROPx P (LOCALx (temp i v :: Q) R) |-- denote_tc_initialized i t.
Proof.
  intros.
  eapply derives_trans; [| apply eval_id_denote_tc_initialized; eauto].
  apply andp_derives; [apply derives_refl |].
  rewrite <- insert_local'.
  apply andp_left1.
  apply derives_refl.
Qed.

Lemma derives_remove_localdef_PQR: forall P Q R i,
  PROPx P (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx (remove_localdef_temp i Q) (SEPx R)).
Proof.
  intros.
  go_lowerx.
  apply andp_right; auto.
  apply prop_right.
  clear H; rename H0 into H.
  induction Q; simpl in *; auto.
  destruct a; try now (destruct H; simpl in *; split; auto).
  destruct H.
  if_tac; simpl in *; auto.
Qed.

Lemma subst_remove_localdef_PQR: forall P Q R i v,
  subst i v (PROPx P (LOCALx (remove_localdef_temp i Q) (SEPx R))) |-- PROPx P (LOCALx (remove_localdef_temp i Q) (SEPx R)).
Proof.
  intros.
  go_lowerx.
  apply andp_right; auto.
  apply prop_right.
  clear H; rename H0 into H.
  induction Q; simpl in *; auto.
  destruct a; try now (destruct H; simpl in *; split; auto).
  if_tac; simpl in *; auto.
  destruct H; split; auto.
  unfold_lift in H.
  destruct H; subst.
  unfold_lift. rewrite eval_id_other in * by auto.
  auto.
Qed.

Fixpoint iota_formals (i: ident) (tl: list type) :=
 match tl with
 | t::tl' => (i,t) :: iota_formals (i+1)%positive tl'
 | nil => nil
 end.

Ltac make_sequential :=
  match goal with
  | |- @semax _ _ _ _ _ (normal_ret_assert _) => idtac
  | |- _ => apply sequential
  end.

Lemma isptr_force_ptr'' : forall p Q,
    (isptr p -> Q) ->
    (isptr (force_ptr p) -> Q).
Proof.
intros.
apply X.
destruct p; inv H; apply Logic.I.
Qed.

Lemma isptr_offset_val'': forall i p Q,
    (isptr p -> Q) ->
    (isptr (offset_val i p) -> Q).
Proof.
intros.
apply X.
destruct p; inv H; apply Logic.I.
Qed.

Lemma ptr_eq_e': forall v1 v2 B,
   (v1=v2 -> B) ->
   (ptr_eq v1 v2 -> B).
Proof.
intuition. apply X. apply ptr_eq_e; auto.
Qed.

Lemma typed_false_of_bool':
 forall x (P: Prop),
    ((x=false) -> P) ->
    (typed_false tint (bool2val x) -> P).
Proof.
intuition.
apply H, typed_false_of_bool; auto.
Qed.

Lemma typed_true_of_bool':
 forall x (P: Prop),
    ((x=true) -> P) ->
    (typed_true tint (bool2val x) -> P).
Proof.
intuition.
apply H, typed_true_of_bool; auto.
Qed.

Ltac intro_if_new :=
 repeat match goal with
  | |- ?A -> _ => ((assert A by auto; fail 1) || fail 1) || intros _
  | |- (_ <-> _) -> _ =>
         intro
  | |- (?A /\ ?B) -> ?C =>
         apply (@and_ind A B C)
  | |- isptr (force_ptr ?P) -> ?Q =>
         apply (isptr_force_ptr'' P Q)
  | |- isptr (offset_val ?i ?P) -> ?Q =>
         apply (isptr_offset_val'' i P Q)
  | H: is_pointer_or_null ?P |- isptr ?P -> _ =>
         clear H
  | |- ?x = ?y -> _ =>
          let H := fresh in intro H;
                     first [subst x | subst y
                             | is_var x; rewrite H
                             | is_var y; rewrite <- H
                             | solve [discriminate H]
                             | idtac]
  | |- isptr ?x -> _ =>
          let H := fresh "P" x in intro H
  | |- is_pointer_or_null ?x =>
          let H := fresh "PN" x in intro H
  | |- typed_false _ (bool2val _) -> _ =>
          simple apply typed_false_of_bool'
  | |- typed_true _ (bool2val _) -> _ =>
          simple apply typed_true_of_bool'
  | |- ptr_eq _ _ -> _ =>
          apply ptr_eq_e'
  | |- _ -> _ =>
          intro
  end.

Lemma saturate_aux20:
 forall (P Q: mpred) P' Q' ,
    (P |-- !! P') ->
    (Q |-- !! Q') ->
    P * Q |-- !! (P' /\ Q').
Proof.
intros.
eapply derives_trans; [apply sepcon_derives; eassumption | ].
rewrite sepcon_prop_prop.
auto.
Qed.

Lemma saturate_aux21x:
  forall (P Q S: mpred),
   (P |-- S) ->
   (S && P |-- Q) -> P |-- Q.
Proof.
intros. subst.
eapply derives_trans; [ | eassumption].
apply andp_right; auto.
Qed.


Ltac already_saturated :=
(match goal with |- ?P |-- ?Q =>
    let H := fresh in
     assert (H: P |-- Q) by auto with nocore saturate_local;
     cbv beta in H;
     match type of H with _ |-- !! ?Q' =>
     assert (Q') by (repeat simple apply conj; auto);
     fail 3
     end
end || auto with nocore saturate_local)
 || simple apply prop_True_right.

Ltac check_mpreds2 R :=
 lazymatch R with
 | @sepcon mpred _ _ ?a ?b => check_mpreds2 a; check_mpreds2 b
 | _ => match type of R with ?t =>
                          first [constr_eq t mpred
                                 | fail 4 "The conjunct" R "has type" t "but should have type mpred; these two types may be convertible but they are not identical"]
                     end
 | nil => idtac
 end.

Ltac saturate_local :=
 match goal with |- ?R |-- _ => check_mpreds2 R end;
 simple eapply saturate_aux21x;
 [repeat simple apply saturate_aux20;
   (* use already_saturated if want to be fancy,
         otherwise the next lines *)
    auto with nocore saturate_local;
     simple apply prop_True_right
 | simple apply derives_extract_prop;
   match goal with |- _ -> ?A =>
       let P := fresh "P" in set (P := A);
       fancy_intros true;
       subst P
      end
 ].

(*********************************************************)

Lemma prop_right_emp {A} {NA: NatDed A}:
 forall P: Prop, P -> emp |-- !! P.
Proof. intros. normalize.
Qed.

Ltac prop_right_cautious :=
 try solve [simple apply prop_right; auto].

(**********************************************************)
(* testing
Parameter f: nat -> Prop.
Parameter g h : mpred.

Goal ( !! f 1 && ((h && !! f 2) && h ) && (!! f 3 && (g && (!!f 4 && !! f 5) && !! f 6)) |-- FF).

*)

(*****************************************************************)

Ltac subst_any :=
 repeat match goal with
  | H: ?x = ?y |- _ => first [ subst x | subst y ]
 end.

Lemma prop_and_right {A}{NA: NatDed A}:
 forall (U: A) (X Y: Prop),
    X ->
    (U |-- !! Y) ->
    U |-- !! (X /\ Y).
Proof. intros. apply derives_trans with (!!Y); auto.
apply prop_derives; auto.
Qed.

Lemma fold_right_sepcon_subst:
 forall i e R, fold_right sepcon emp (map (subst i e) R) = subst i e (fold_right sepcon emp R).
Proof.
 intros. induction R; auto.
 autorewrite with subst. f_equal; auto.
Qed.

Lemma unsigned_eq_eq: forall i j, Int.unsigned i = Int.unsigned j -> i = j.
Proof.
  intros.
  rewrite <- (Int.repr_unsigned i), <- (Int.repr_unsigned j).
  rewrite H.
  reflexivity.
Qed.

Ltac solve_mod_eq :=
  unfold Int.add, Int.mul;
  repeat rewrite Int.unsigned_repr_eq;
  repeat
  (repeat rewrite Zmod_mod;
  repeat rewrite Zmult_mod_idemp_l;
  repeat rewrite Zmult_mod_idemp_r;
  repeat rewrite Zplus_mod_idemp_l;
  repeat rewrite Zplus_mod_idemp_r).


Lemma prop_false_andp {A}{NA :NatDed A}:
 forall P Q, ~P -> !! P && Q = FF.
Proof.
intros.
apply pred_ext; normalize.
Qed.

Lemma wand_join {A}{NA: NatDed A}{SA: SepLog A}:
  forall x1 x2 y1 y2: A,
    (x1 -* y1) * (x2 -* y2) |-- ((x1 * x2) -* (y1 * y2)).
Proof.
intros.
rewrite <- wand_sepcon_adjoint.
rewrite sepcon_assoc.
rewrite <- (sepcon_assoc _ x1).
rewrite <- (sepcon_comm x1).
rewrite (sepcon_assoc x1).
rewrite <- (sepcon_assoc _ x1).
rewrite <- (sepcon_comm x1).
rewrite <- (sepcon_comm x2).
apply sepcon_derives.
apply modus_ponens_wand.
apply modus_ponens_wand.
Qed.

Lemma wand_sepcon:
 forall {A} {NA: NatDed A}{SA: SepLog A} P Q,
   (P -* Q * P) * P = Q * P.
Proof.
intros.
apply pred_ext.
*
rewrite sepcon_comm.
apply modus_ponens_wand.
*
apply sepcon_derives; auto.
apply -> wand_sepcon_adjoint; auto.
Qed.

Lemma wand_sepcon':
 forall {A} {NA: NatDed A}{SA: SepLog A} P Q,
   P * (P -* Q * P) = P * Q.
Proof.
intros. rewrite (sepcon_comm P Q).
rewrite sepcon_comm; apply wand_sepcon.
Qed.


#[export] Hint Rewrite wand_sepcon wand_sepcon' : norm.



Lemma extract_nth_exists_in_SEP:
  forall n P Q (R: list mpred)
              {A} (S: A -> mpred),
   nth n R emp = (exp S) ->
   PROPx P (LOCALx Q (SEPx R)) =
   exp (fun x => PROPx P (LOCALx Q (SEPx (replace_nth n R (S x))))).
Proof.
intros.
transitivity (PROPx P (LOCALx Q (EX x:A, SEPx (replace_nth n R (S x))))).
*
f_equal. f_equal.
unfold SEPx.
simpl. extensionality rho.
revert R H; induction n; destruct R; intros.
unfold replace_nth, fold_right.
simpl.
unfold nth in H. rewrite H; clear H.
apply pred_ext.
apply exp_left; intro x. apply exp_right with x.
apply exp_right with x.
auto.
apply exp_left; intro x. auto.
unfold replace_nth, nth in *. subst m.
unfold fold_right_sepcon.
fold (fold_right_sepcon R).
normalize.
unfold nth in H. unfold replace_nth.
simpl.
rewrite H.
simpl.
apply pred_ext.
apply exp_left; intro x. apply exp_right with x.
apply exp_right with x.
auto.
apply exp_left; intro x. auto.
unfold nth in H.
fold (nth n R) in H.
simpl.
rewrite (IHn _ H). clear.
normalize.
*
unfold PROPx, LOCALx.
normalize.
Qed.

Ltac extract_exists_in_SEP' PQR :=
 match PQR with
 | PROPx ?P (LOCALx ?Q (SEPx (?R))) =>
   match R with context [(@exp _ _ ?A ?S) :: ?R'] =>
      let n := constr:((length R - Datatypes.S (length R'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      rewrite (@extract_nth_exists_in_SEP n' P Q R A S (eq_refl _));
      unfold replace_nth at 1;
      rewrite ?exp_andp2
   end
 end.

Ltac extract_exists_from_SEP :=
lazymatch goal with
  | |- semax _ ?Pre _ _ =>
    extract_exists_in_SEP' Pre; apply extract_exists_pre
  | |- ENTAIL _, ?Pre |-- ?Post =>
     let P := fresh "POST" in set (P := Post);
    extract_exists_in_SEP' Pre; subst P; apply exp_left
  | |- ?Pre |-- ?Post => (* this case is obsolete, should probably be deleted *)
     let P := fresh "POST" in set (P := Post);
    extract_exists_in_SEP' Pre; subst P; apply exp_left
end.

Ltac move_from_SEP' PQR :=
 match PQR with
 | PROPx ?P (LOCALx ?Q (SEPx (?R))) =>
   match R with context [(prop ?P1 && ?S) :: ?R'] =>
      let n := constr:((length R - Datatypes.S (length R'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      rewrite(@extract_prop_in_SEP n' P1 S P Q R (eq_refl _));
      unfold replace_nth at 1
   end
 end.

Lemma derives_extract_PROP' :
  forall (P1: Prop) P QR S,
     (P1 -> PROPx P QR |-- S) ->
     PROPx (P1::P) QR |-- S.
Proof.
unfold PROPx in *.
intros.
rewrite fold_right_cons.
normalize.
eapply derives_trans; [ | apply H; auto].
normalize.
Qed.



Ltac test_for_Intro_prop R :=
 lazymatch R with
 | nil => fail
 | ?A :: ?B => first [test_for_Intro_prop A | test_for_Intro_prop B]
 | @exp _ _ _  => fail
 | (prop _) => idtac
 | andp ?A ?B => first [test_for_Intro_prop A | test_for_Intro_prop B]
 | sepcon ?A ?B =>  first [test_for_Intro_prop A | test_for_Intro_prop B]
 end.

Ltac Intro_prop' :=
lazymatch goal with
 | |- semax _ ?PQR _ _ =>
     first [ move_from_SEP' PQR;
              simple apply semax_extract_PROP; fancy_intros false
            | flatten_in_SEP PQR
            ]
 | |- ENTAIL _, ?PQR |-- _ =>
     first [ move_from_SEP' PQR;
               simple apply derives_extract_PROP; fancy_intros false
            | flatten_in_SEP PQR
             ]
 | |- ?PQR |-- _ =>  (* this case is obsolete, should probably be deleted *)
     first [ simple apply derives_extract_prop; fancy_intros false
            | move_from_SEP' PQR;
               simple apply derives_extract_PROP; fancy_intros false
            | flatten_in_SEP PQR
             ]
end.

Ltac Intro_prop :=
(*  Intro_prop is written this complicated way to avoid doing
    [autorewrite with gather_prop_core] which is expensive, and
   to avoid [autorewrite with gather_prop] which is even more expensive. *)
lazymatch goal with
 | |- semax _ ?PQR _ _ => tryif is_evar PQR then fail else idtac
 | |- ENTAIL _, ?PQR |-- _ => tryif is_evar PQR then fail else idtac
 | |- ?PQR |-- _ => tryif is_evar PQR then fail else idtac
end;
first
 [ simple apply semax_extract_PROP; fancy_intros false
 | simple apply derives_extract_PROP; fancy_intros false
 |
lazymatch goal with
 | |- ENTAIL _, @exp _ _ _ |-- _ =>  fail
 | |- semax _ (@exp _ _ _) _ _ => fail
 | |- ENTAIL _, PROPx nil (LOCALx _ (SEPx ?R)) |-- _ => test_for_Intro_prop R
 | |- semax _ PROPx nil (LOCALx _ (SEPx ?R)) _ _ => test_for_Intro_prop R
 | |- _ => idtac
 end;
 tryif Intro_prop' then idtac
 else tryif progress autorewrite with gather_prop_core
    then first [Intro_prop' | progress gather_prop; Intro_prop']
    else (progress gather_prop; Intro_prop')
 ].

Ltac Intro'' a :=
  tryif simple apply extract_exists_pre then intro a
  else tryif simple apply exp_left then intro a
  else tryif extract_exists_from_SEP then intro a
  else tryif rewrite exp_andp1 then Intro'' a
  else tryif rewrite exp_andp2 then Intro'' a
  else tryif rewrite exp_sepcon1 then Intro'' a
  else tryif rewrite exp_sepcon2 then Intro'' a
  else fail.

Ltac Intro a :=
  repeat Intro_prop;
  lazymatch goal with
  | |- ?A |-- ?B =>
     let z := fresh "z" in pose (z:=B); change (A|--z); Intro'' a; subst z
  | |- semax _ _ _ _ =>
     Intro'' a
  end.

Tactic Notation "Intro" "?" :=
  lazymatch goal with
  | |- semax _ ?x _ _ =>
    lazymatch x with context [EX ex1 : _, _] =>
      let e1 := fresh ex1 in Intro e1
    end
  | |- context [?Pre |-- _] =>
    lazymatch Pre with context [EX ex1 : _, _] =>
      let e1 := fresh ex1 in Intro e1
    end
  end.

Ltac finish_Intros :=
repeat Intro_prop;
(* Do this next part for backwards compatibility *)
lazymatch goal with
 | |- ?A _ => let x := fresh "x" in set(x:=A);
        gather_prop; subst x
end.

Tactic Notation "Intros" := finish_Intros.

Tactic Notation "Intros" "*" :=
  repeat Intro ?; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0) :=
 Intro x0; finish_Intros.

Tactic Notation "Intros" "?" :=
 Intro ?; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) :=
 Intro x0; Intro x1; finish_Intros.

Tactic Notation "Intros" "?" "?" :=
 Intro ?; Intro ?; finish_Intros.

Tactic Notation "Intros" "?" simple_intropattern(x0) :=
 Intro ?; Intro x0; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0) "?" :=
 Intro x0; Intro ?; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2) :=
 Intro x0; Intro x1; Intro x2; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) :=
 Intro x0; Intro x1; Intro x2; Intro x3; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; Intro x9; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; Intro x9;
 Intro x10; finish_Intros.

Tactic Notation "Intros" simple_intropattern(x0)
 simple_intropattern(x1) simple_intropattern(x2)
 simple_intropattern(x3) simple_intropattern(x4)
 simple_intropattern(x5) simple_intropattern(x6)
 simple_intropattern(x7) simple_intropattern(x8)
 simple_intropattern(x9) simple_intropattern(x10)
 simple_intropattern(x11) :=
 Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
 Intro x5; Intro x6; Intro x7; Intro x8; Intro x9;
 Intro x10; Intro x11; finish_Intros.


Ltac extract_exists_from_SEP_right :=
match goal with
  | |- ?Pre |-- ?Post =>
     let P := fresh "PRE" in set (P := Pre);
    extract_exists_in_SEP' Post; subst P
end.

Ltac Exists'' a :=
  first [apply exp_right with a
         | rewrite exp_andp1; Exists'' a
         | rewrite exp_andp2; Exists'' a
         | rewrite exp_sepcon1; Exists'' a
         | rewrite exp_sepcon2; Exists'' a
         | extract_exists_from_SEP_right; apply exp_right with a
         ].

Ltac Exists' a :=
  match goal with |- ?A |-- ?B =>
     let z := fresh "z" in pose (z:=A); change (z|--B); Exists'' a; subst z
  end.

Tactic Notation "Exists" constr(x0) :=
 Exists' x0.

Tactic Notation "Exists" "?" :=
 lazymatch goal with
 | |- _ |-- ?Post =>
  lazymatch Post with context [EX ex : _, _] => Exists' ex end
 end.

Tactic Notation "Exists" constr(x0) constr(x1) :=
 Exists' x0; Exists' x1.

Tactic Notation "Exists" "?" "?" :=
 do 2 Exists ?.

Tactic Notation "Exists" "?" constr(x0) :=
 Exists ?; Exists' x0.

Tactic Notation "Exists" constr(x0) "?" :=
 Exists' x0; Exists ?.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) :=
 Exists' x0; Exists' x1; Exists' x2.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
 constr(x10) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
 Exists' x10.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
 constr(x10) constr(x11) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
 Exists' x10; Exists' x11.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
 constr(x10) constr(x11) constr(x12) :=
 Exists' x0; Exists' x1; Exists x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
 Exists' x10; Exists' x11; Exists' x12.

(* EExists *)
Ltac my_evar name T cb :=
  let x := fresh name
  in
  evar (x : T);
    let x' := eval unfold x in x
    in
    clear x; cb x'.

Ltac tuple_evar name T cb :=
  lazymatch T with
  | prod ?A ?B => tuple_evar name A
    ltac: (fun xA =>
      tuple_evar name B ltac: (fun xB =>
        cb (xA, xB)))
  | _ => my_evar name T cb
  end; idtac.

Ltac EExists'' :=
  let EExists_core :=
    match goal with [ |- _ |-- EX x:?T, _ ] =>
      tuple_evar x T ltac: (fun x => apply exp_right with x)
    end; idtac
  in
  first [ EExists_core
         | rewrite exp_andp1; EExists''
         | rewrite exp_andp2; EExists''
         | rewrite exp_sepcon1; EExists''
         | rewrite exp_sepcon2; EExists''
         | extract_exists_from_SEP_right; EExists_core
         ].

Ltac EExists' :=
  match goal with |- ?A |-- ?B =>
     let z := fresh "z" in pose (z:=A); change (z|--B); EExists''; unfold z at 1; clear z
  end.

Ltac EExists := EExists'.

Ltac EExists_alt :=
  let T := fresh "T"
  in
  let x := fresh "x"
  in
  evar (T:Type); evar (x:T); subst T; Exists x; subst x.

Tactic Notation "freeze1" uconstr(a) :=
    let x := fresh "x" in set (x:=a);
    let fr := fresh "freeze" in pose (fr := @abbreviate mpred x);
    change (cons x) with (cons fr); subst x.
