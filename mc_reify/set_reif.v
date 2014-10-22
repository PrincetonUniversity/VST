Require Import floyd.proofauto. 
Require Import funcs.
Require Import bool_funcs.
Require Import MirrorCore.Lambda.ExprCore.



Definition appR (e1 : func') e2 := App (@Inj typ func (inr e1)) (e2). 
Definition injR (e1 : func') := @Inj typ func (inr e1).

Fixpoint msubst_eval_expr_reif (T1: PTree.t (ExprCore.expr typ func)) (T2: PTree.t (type * (ExprCore.expr typ func))) (e: Clight.expr) : option (ExprCore.expr typ func) :=
  match e with
  | Econst_int i ty => Some (appR (Value fVfloat) (injR (Const (fint i))))
  | Econst_long i ty => Some (appR (Value fVlong) (injR (Const (fint64 i))))
  | Econst_float f ty => Some (appR (Value fVfloat) (injR (Const (ffloat f))))
  | Econst_single f ty => Some (appR (Value fVsingle) (injR (Const (ffloat32 f))))
  | Etempvar id ty => PTree.get id T1
  | Eaddrof a ty => msubst_eval_lvalue_reif T1 T2 a 
  | Eunop op a ty =>  option_map (appR (Eval_f (feval_unop op (typeof a))))
                                       (msubst_eval_expr_reif T1 T2 a) 
  | Ebinop op a1 a2 ty => match (msubst_eval_expr_reif T1 T2 a1), (msubst_eval_expr_reif T1 T2 a2) with
                            | Some v1, Some v2 => Some 
                                (App (appR (Eval_f (feval_binop op 
                                         (typeof a1) (typeof a2))) v1) v2) 
                            | _, _ => None
                          end
  | Ecast a ty => option_map (appR (Eval_f (feval_cast (typeof a) ty))) (msubst_eval_expr_reif T1 T2 a)
  | Evar id ty => option_map (appR (Eval_f (fderef_noload ty)))
                    match PTree.get id T2 with
                    | Some (ty', v) =>
                      if eqb_type ty ty'
                      then Some v
                      else None
                    | None => None
                    end
  | Ederef a ty => 
      option_map (appR (Eval_f (fderef_noload ty))) 
                 (option_map (appR (Other (fforce_ptr)))
                             (msubst_eval_expr_reif T1 T2 a))
  | Efield a i ty => option_map (appR (Eval_f (fderef_noload ty))) 
                                (option_map (appR (Eval_f (feval_field (typeof a) i))) (msubst_eval_lvalue_reif T1 T2 a))
  end
  with msubst_eval_lvalue_reif (T1: PTree.t (ExprCore.expr typ func)) (T2: PTree.t (type * (ExprCore.expr typ func))) (e: Clight.expr) : option (ExprCore.expr typ func) := 
  match e with 
  | Evar id ty => match PTree.get id T2 with
                  | Some (ty', v) =>
                    if eqb_type ty ty'
                    then Some v
                    else None
                  | None => None
                  end
  | Ederef a ty => option_map (appR (Other fforce_ptr)) (msubst_eval_expr_reif T1 T2 a)
  | Efield a i ty => option_map (appR (Eval_f (feval_field (typeof a) i))) (msubst_eval_lvalue_reif T1 T2 a)
  | _  => Some (injR (Value fVundef))
  end.

Lemma Forall_reverse :
forall A P (l: list A),
Forall P l <->
Forall P (rev l). 
Proof.
intros.
split; intros.
 + rewrite Forall_forall in *.
   intros. destruct l.
      - apply H. auto.
      - simpl in *. apply in_app in H0.
        destruct H0. apply H; auto.
        right. apply in_rev; auto.
        apply H.  left. simpl in H0. intuition.
 + rewrite Forall_forall in *; intros.
   destruct l.
   inversion H0.
   destruct H0.
   subst.
   simpl in *. apply H. apply in_app. right. constructor. auto.
   apply H. simpl. apply in_app. left. apply in_rev in H0. auto.
Qed.

Lemma in_fst :
forall T T2 (p : T) (v: T2) l, 
In (p, v) l -> In p (map fst l).
Proof.
intros.
  + induction l. auto.
      - simpl in *. intuition.
        destruct a. left. simpl. congruence.
Qed.


Lemma elt_eq : forall T l p (v:T) v0 ls, 
(p, v0) :: l = rev (PTree.elements (PTree.set p v ls)) ->
v = v0.
Proof.
intros.
assert (In (p, v) (rev (PTree.elements (PTree.set p v ls)))).
  { rewrite <- in_rev. apply PTree.elements_correct. rewrite PTree.gss. auto. }
assert (X := PTree.elements_keys_norepet (PTree.set p v ls)).
assert (In (p, v0) (rev (PTree.elements (PTree.set p v ls)))).
  { rewrite <- list_norepet_rev in X. rewrite <- map_rev in X. unfold PTree.elt in *. 
    rewrite <- H in *. simpl in *. intuition. }
rewrite <- in_rev in H1. 
  rewrite <- list_norepet_rev in X. rewrite <- map_rev in X. unfold PTree.elt in *.
  rewrite in_rev in H1.  
    rewrite <- H in *. simpl in *. clear - X H0 H1. intuition; try congruence.
    inversion X; subst. intuition. apply in_fst in H. intuition.
    inversion X. subst. intuition. apply in_fst in H. intuition.
Qed.

Definition tempD' := (fun Q i v => `(eq v) (eval_id i) :: Q).
Definition localD' := (fun Q i tv => `(eq (snd tv)) (eval_var i (fst tv)) :: Q).
Definition LocalD_app (T1: PTree.t val) (T2: PTree.t (type * val)) (Q: list (environ -> Prop)) :=
  (PTree.fold tempD' T1 nil) ++ 
 (PTree.fold localD' T2 nil) ++ Q.


Lemma localD_app_eq : forall t2 q, PTree.fold localD' t2 q = PTree.fold localD' t2 nil ++ q.
Proof.
intros.
repeat rewrite PTree.fold_spec.
simpl in *. repeat rewrite <- fold_left_rev_right.
induction (rev (PTree.elements t2)).
  + reflexivity.
  + simpl. rewrite IHl. auto.
Qed.

Lemma tempD_app_eq : forall t2 q, PTree.fold tempD' t2 q = PTree.fold tempD' t2 nil ++ q.
intros.
repeat rewrite PTree.fold_spec.
simpl in *. repeat rewrite <- fold_left_rev_right.
induction (rev (PTree.elements t2)).
  + reflexivity.
  + simpl. rewrite IHl. auto.
Qed.

Lemma LocalD_app_eq : 
forall t1 t2 q,
LocalD t1 t2 q = LocalD_app t1 t2 q.
Proof.
intros.
unfold LocalD, LocalD_app.
simpl in *.
rewrite localD_app_eq.
rewrite tempD_app_eq. auto.
Qed.

Lemma fold_right_conj : 
forall a b rho, 
(fold_right (fun (x0 x1 : environ -> Prop) (x2 : environ) => x0 x2 /\ x1 x2) 
     (`True) (a ++ b) rho) <-> ((fold_right (fun (x0 x1 : environ -> Prop) (x2 : environ) => x0 x2 /\ x1 x2) 
     (`True) a rho /\ fold_right (fun (x0 x1 : environ -> Prop) (x2 : environ) => x0 x2 /\ x1 x2) 
     (`True) b rho)).
Proof.
intros. 
split; intros; induction a; simpl in *; intuition.
Qed.


Lemma semax_set_localD id e v ls vs:
forall Espec Delta R ,
tc_expr_b_norho Delta e= true ->
tc_temp_id_b_norho id (typeof e) Delta e = true ->
msubst_eval_expr_norho ls vs e = Some v ->
@semax Espec Delta (assertD nil (localD ls vs) R)
      (Sset id e)
(normal_ret_assert (assertD nil (localD (PTree.set id v ls) vs) R)).
Proof.
(*intros.
eapply semax_pre_simple; [ | apply forward_setx_closed_now].
unfold assertD. apply andp_left2. apply derives_refl.
Focus 2.
rewrite Forall_forall. intros.
induction R. inversion H2.
simpl in H2. destruct H2. subst. auto with closed.
intuition.
apply andp_right. 
apply andp_right; auto.
intro rho.
apply tc_expr_b_sound with (rho := rho) in H .
unfold local. super_unfold_lift. apply prop_right. auto.
unfold local. intro rho. super_unfold_lift.
apply tc_temp_id_b_sound with (rho := rho) in H0. apply prop_right.
auto.
apply andp_left2. apply derives_refl.
intros. go_lowerx. unfold normal_ret_assert.
normalize. unfold assertD.
autorewrite with subst.
normalize. apply andp_right. apply prop_right. 
Locate forward_setx_closed_now.
eapply derives_trans with (SeparationLogic.subst id `v (assertD [] (localD ls vs) R) rho).

rewrite LocalD_app_eq. 
unfold LocalD_app. repeat rewrite fold_right_conj. 
repeat split. 
repeat rewrite PTree.fold_spec.
repeat rewrite <-  fold_left_rev_right. 
remember (rev (PTree.elements (PTree.set id v ls))).
generalize dependent ls. generalize dependent id. generalize dependent v.
induction l; intros.
  + simpl. auto.
  + simpl. split.
     - destruct a. simpl in *.


 
Check fold_right_app.
rewrite <- fold_right_app.
repeat rewrite fold_right_app.
generalize dependent vs. generalize dependent ls.
induction l0.
  + simpl. induction l; intros.
      - exact I.
      - simpl. split. autorewrite with subst in *. destruct a. simpl. unfold_lift.
        destruct (ident_eq p id). subst id.
        assert (v=v0).
          { apply elt_eq in Heql. subst. reflexivity. } 
        subst. specialize (IHl ls). 

apply PTree_elements_set in H1. destruct H1.
congruence.
rewrite <- list_norepet_rev in X. rewrite <- map_rev in X. unfold PTree.elt in *. 
    rewrite <- H in *. simpl in *. 
    inversion X; subst. 
        
 SearchAbout msubst_eval_expr.
unfold_lift; reflexivity.
unfold_lift; unfold_lift in H4. destruct H4; auto.
remember (PTree.elements ls). induction l.
unfold LocalD. repeat rewrite PTree.fold_spec.
eapply forward_setx_closed_now; auto 50 with closed.
 repeat rewrite <- Heql. simpl.
rewrite <- fold_left_rev_right. 
induction (rev (PTree.elements vs)). simpl. auto.
simpl. rewrite Forall_forall. intros. simpl in H2.
destruct H2. subst. auto with closed.
rewrite Forall_forall in IHl. apply IHl. auto.
admit. (*NOT TRUE. Lifts must be over all of R *)

 SearchAbout Forall.

 rewrite Forall_forall. intros.
rewrite Forall_forall in IHl. apply IHl.


Check PTree.elements_
apply PTree.elements_compete in Heql.
unfold LocalD. simpl.
*)
Admitted.