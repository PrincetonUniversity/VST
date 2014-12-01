Require Import floyd.proofauto. 
Require Import mc_reify.funcs.
Require Import mc_reify.types.
Require Import mc_reify.bool_funcs.
Require Import MirrorCore.Lambda.ExprCore.
Require Import mc_reify.get_set_reif.
Require Import mc_reify.func_defs.


Definition match_reif_option {B: Type} (e: expr typ func) (somef : typ -> expr typ func -> B)
           (nonef : typ -> B) (d : B) := 
match e with 
| (App (Inj (inr (Other (fsome t)))) e) => somef t e
| (Inj (inr (Other (fnone t)))) => nonef t
| _ => d
end.

Check eval_field.
Inductive val_e :=
    Vundef : val_e
  | Vint : int -> val_e
  | Vlong : int64 -> val_e
  | Vfloat : float -> val_e
  | Vsingle : float32 -> val_e
  | Vexpr : expr typ func -> val_e
  | Vunop : Cop.unary_operation -> type ->  val_e -> val_e
  | Vbinop : Cop.binary_operation -> type -> type -> val_e -> val_e -> val_e
  | Veval_cast : type -> type -> val_e -> val_e
  | Vderef_noload : type -> val_e -> val_e
  | Vforce_ptr : val_e -> val_e
  | Veval_field : type -> ident -> val_e -> val_e.

Fixpoint val_e_to_expr (v : val_e) : (expr typ func) :=
match v with
  | Vundef => injR (Value fVundef)
  | Vlong l => (appR (Value fVlong) (injR (Const (fint64 l))))
  | Vint i => (appR (Value fVfloat) (injR (Const (fint i))))
  | Vfloat f => (appR (Value fVfloat) (injR (Const (ffloat f))))
  | Vsingle f => (appR (Value fVsingle) (injR (Const (ffloat32 f))))
  | Vexpr e => e
  | Vunop op ty e => appR (Eval_f (feval_unop op ty)) (val_e_to_expr e)
  | Vbinop op ty1 ty2 e1 e2 => (App (appR (Eval_f (feval_binop op 
                                         ty1 ty2)) (val_e_to_expr e1)) (val_e_to_expr e2))
  | Veval_cast ty1 ty2 v => (appR (Eval_f (feval_cast ty1 ty2))) (val_e_to_expr v) 
  | Vderef_noload t v => (appR (Eval_f (fderef_noload t))) (val_e_to_expr v)
  | Vforce_ptr v => (appR (Other (fforce_ptr))) (val_e_to_expr v)
  | Veval_field t id v => (appR (Eval_f (feval_field t id))) (val_e_to_expr v)
end.

Definition msubst_var id T2 ty :=
match get_reif id T2 with
  | App (Inj (inr (Other (fsome t)))) 
        (App (App (Inj (inr (Data (fpair t1 t2))))
                  (Inj (inr (Const (fCtype ty')))))
             v) =>
    if eqb_type ty ty'
    then Some (Vexpr v)
    else None
  | _ => None
end.


Fixpoint msubst_eval_expr_reif (T1: ExprCore.expr typ func) (T2: ExprCore.expr typ func) (e: Clight.expr) : option (val_e) :=
  match e with
  | Econst_int i ty => Some (Vint i)
  | Econst_long i ty => Some (Vlong i)
  | Econst_float f ty => Some (Vfloat f)
  | Econst_single f ty => Some (Vsingle f)
  | Etempvar id ty => match get_reif id T1 with
                        | (App (Inj (inr (Other (fsome t)))) v) => Some (Vexpr v)
                        | _ => None
                      end
  | Eaddrof a ty => msubst_eval_lvalue_reif T1 T2 a 
  | Eunop op a ty =>  option_map (Vunop op (typeof a)) (msubst_eval_expr_reif T1 T2 a) 
  | Ebinop op a1 a2 ty => match (msubst_eval_expr_reif T1 T2 a1), (msubst_eval_expr_reif T1 T2 a2) with
                            | Some v1, Some v2 => Some (Vbinop op (typeof a1) (typeof a2) v1 v2) 
                            | _, _ => None
                          end
  | Ecast a ty => option_map (Veval_cast (typeof a) ty) (msubst_eval_expr_reif T1 T2 a)
  | Evar id ty => option_map (Vderef_noload ty) (msubst_var id T2 ty)
  | Ederef a ty => option_map (Vderef_noload ty) (option_map Vforce_ptr (msubst_eval_expr_reif T1 T2 a))
  | Efield a i ty => option_map (Vderef_noload ty) (option_map (Veval_field (typeof a) i) (msubst_eval_lvalue_reif T1 T2 a))
  end
with
msubst_eval_lvalue_reif (T1: ExprCore.expr typ func) (T2: ExprCore.expr typ func) (e: Clight.expr) : option val_e := 
  match e with 
  | Evar id ty => (msubst_var id T2 ty)
  | Ederef a ty => option_map Vforce_ptr (msubst_eval_expr_reif T1 T2 a)
  | Efield a i ty => option_map (Veval_field (typeof a) i) (msubst_eval_lvalue_reif T1 T2 a)
  | _  => Some Vundef
  end.
  
Definition rmsubst_eval_expr (T1: (ExprCore.expr typ func)) (T2: ExprCore.expr typ func) (e: Clight.expr) := 
match msubst_eval_expr_reif T1 T2 e with
| Some e => some_reif (val_e_to_expr e) tyval
| None => none_reif tyval
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

Lemma LocalD_to_localD : forall P R t l X,
PROPx (P) (LOCALx (LocalD t l X) (SEPx (R))) |--
PROPx (P) (LOCALx (localD t l) (SEPx (R))).
Proof.
intros. entailer.
apply prop_right.
unfold localD. 
repeat rewrite LocalD_app_eq in *.
unfold LocalD_app in *.
repeat rewrite fold_right_conj in *.
intuition. simpl. apply I.
Qed.


Definition my_set {T} := @PTree.set T.

Lemma semax_set_localD id e (t: PTree.t (type * bool)) (v : PTree.t type) 
      (r : type) (gt : PTree.t type):
forall vl ls vs Espec R gs P,
tc_expr_b_norho (mk_tycontext t v r gt gs) e= true ->
tc_temp_id_b_norho id (typeof e) (mk_tycontext t v r gt gs) e = true ->
msubst_eval_expr_norho ls vs e = Some vl ->
(assertD nil (localD (my_set id vl ls) vs) R) = P -> 
@semax Espec (mk_tycontext t v r gt gs) (assertD nil (localD ls vs) R)
      (Sset id e)
(normal_ret_assert P).
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

