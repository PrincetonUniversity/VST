Require Import floyd.proofauto.
Require Import MirrorShard.Expr.
Require Import functions.
Require Import sep.
Require Import types.
Require Import wrapExpr.
Local Open Scope logic.


Fixpoint flatten_top_conjuncts p : Expr.exprs :=
match p with
| Func 5%nat (a :: b :: nil) => flatten_top_conjuncts a ++ flatten_top_conjuncts b
| _ => p::nil
end.

Definition reflect_and a b := @Func 5%nat (a :: b :: nil).

Fixpoint unflatten_conjuncts l : Expr.expr :=
match l with
| nil => Func (functions.True_f nil) nil
| h::nil => h
| h::t => Func 5%nat (h::(unflatten_conjuncts t)::nil)
end .

Fixpoint unflatten_conjuncts_sep l : Sep.sexpr :=
match l with
| nil => Sep.Inj (Func (functions.True_f nil) nil)
| h::nil => Sep.Inj h
| h::t => Sep.Star (Sep.Inj h) (unflatten_conjuncts_sep t)
end .

Definition lift_and e : Sep.sexpr :=
unflatten_conjuncts_sep (flatten_top_conjuncts e).

Fixpoint lift_ands s : Sep.sexpr :=
match s with
| Sep.Star a b => Sep.Star (lift_ands a) (lift_ands b)
| Sep.Inj e => lift_and e
| _ => s
end.

Definition is_true_e (p: Expr.expr) :=
match p with
| Func f nil  => beq_nat (functions.True_f nil) f
| _ => false
end.


Definition not_true (p: Expr.expr) := negb (is_true_e p).

Definition remove_true l :=
filter not_true l.

Definition remove_trues (e : Expr.expr) :=
unflatten_conjuncts (remove_true (flatten_top_conjuncts e)).

Lemma provable_l : forall t l f uenv ,
nth_error f 5 = Some (functions.and_signature t) ->
Provable f uenv nil (Func 5%nat l) ->
exists a, exists b, l = a::b::nil.
Proof.
intros. unfold Provable in H0. simpl in *; rewrite H in *; simpl in *.
destruct l; simpl in H0; intuition.
destruct l; simpl in H0; intuition.
destruct (exprD f uenv nil e tvProp); intuition.
destruct l. eauto.
destruct (exprD f uenv nil e tvProp); intuition.
destruct (exprD f uenv nil e0 tvProp); intuition.
Qed.

Lemma Provable_reflect_and : forall t a b uenv f,
 nth_error f 5 = Some (functions.and_signature t) -> 
(Provable f uenv nil (reflect_and a b) <-> Provable f uenv nil a /\ Provable f uenv nil b).
Proof.
intros; split; intros; unfold Provable in *;
simpl in *; try rewrite H in *; simpl in *;
destruct (exprD f uenv nil a tvProp); destruct (exprD f uenv nil b tvProp); intuition. 
Qed.

Lemma Provable_f5_and : forall t a b uenv f,
 nth_error f 5 = Some (functions.and_signature t) -> 
(Provable f uenv nil
         (Func 5%nat (a :: b :: nil)) <->  Provable f uenv nil a /\ Provable f uenv nil b).
Proof.
intros. assert (Z := Provable_reflect_and). unfold reflect_and in *. apply Z; auto.
Qed.

Hint Rewrite Provable_reflect_and Provable_f5_and using auto: Provable_and.

Ltac rp := autorewrite with Provable_and in *.

Lemma remove_true_app : forall x x0,
remove_true (x ++ x0) =
remove_true x ++ remove_true x0.
Proof.
intros. unfold remove_true. revert x0.
induction x; intros; auto.
simpl. if_tac. rewrite <- app_comm_cons. f_equal. auto.
auto.
Qed.

Lemma provable_unflatten_cons : forall t l a f uenv,
                                  nth_error f 5 = Some (functions.and_signature t) ->
                                  nth_error f (functions.True_f nil) = Some (functions.True_signature t) ->
                                  (Provable f uenv nil (unflatten_conjuncts (a :: l)) <->
                                  Provable f uenv nil a /\ Provable f uenv nil (unflatten_conjuncts l)).
Proof.
intros; split; intros;
induction l; auto. simpl. unfold Provable in *; simpl in *; rewrite H0; auto; clear H0.
intuition.
simpl; auto.
simpl in H1; rp; intuition.
intuition.
simpl; rp; intuition.
Qed.

Hint Rewrite provable_unflatten_cons: Provable_and.

Lemma unflatten_conjuncts_app :
forall t l1 l2 f uenv, 
nth_error f 5%nat = Some (functions.and_signature t) -> 
nth_error f (functions.True_f nil) = Some (functions.True_signature t) ->
(Provable f uenv nil
(Func 5%nat 
((unflatten_conjuncts l1) :: ((unflatten_conjuncts) l2) :: nil)) <->
Provable f uenv nil
(unflatten_conjuncts (l1 ++ l2))).
Proof.
intros; split; intros.
  + generalize dependent l2. induction l1; intros. 
      - simpl. simpl in H1. 
        unfold Provable in *; simpl in *; try rewrite H in *; try rewrite H0 in *; clear H0;
        simpl in *. 
        destruct (exprD f uenv nil (unflatten_conjuncts l2) tvProp);
          intuition.
      - rewrite <- app_comm_cons. rp; intuition.
        apply IHl1. rp; auto.
  + induction l1; auto.
      - rp; intuition. simpl. unfold Provable; simpl; simpl in H0; rewrite H0; simpl; auto.
      - rewrite <- app_comm_cons in *.
        rp. intuition. auto. auto.
        auto. auto.
Qed.

Lemma provable_l_remove : forall t l f uenv,
nth_error f 5 = Some (functions.and_signature t) ->
Provable f uenv nil (remove_trues (Func 5%nat l)) ->
exists a, exists b, l = a::b::nil.
Proof.
intros. unfold Provable in H0.
destruct l; simpl in *; try rewrite H in *; intuition.
destruct l; simpl in *; try rewrite H in *; intuition.
simpl in *.
destruct (exprD f uenv nil e tvProp); intuition.
destruct l; eauto.
simpl in H0. rewrite H in H0. simpl in H0.
destruct (exprD f uenv nil e tvProp); intuition.
destruct (exprD f uenv nil e0 tvProp); intuition.
Qed.

Lemma func_True : forall t f uenv,  
nth_error f (functions.True_f nil) = Some (functions.True_signature t) ->
Provable f uenv nil (Func (functions.True_f nil) nil) = True.
Proof.
intros.
unfold Provable.
simpl in *;  rewrite H; simpl; auto.
Qed.

Hint Rewrite func_True: Provable_and.


Lemma Provable_remove_trues : forall t e uenv f,
nth_error f 5 = Some (functions.and_signature t) ->
nth_error f (functions.True_f nil) = Some (functions.True_signature t) ->
(Provable f uenv nil e <-> Provable f uenv nil (remove_trues e)). 
Proof.
intros; split; induction e; intros; auto.
(* + unfold remove_trues. unfold flatten_top_conjuncts.
   unfold remove_true. unfold filter. simpl. unfold not_true. 
   destruct (is_true_e (Const t0)). simpl. unfold Provable; simpl; auto.
   apply H0.*)
 + do 5 (destruct f0; [ unfold remove_trues; try destruct l; auto | ]). 
   destruct f0.
   assert (L := provable_l _ _ _ _ H H2).
   destruct L. destruct H3. subst.
   unfold remove_trues. simpl.
   rewrite remove_true_app.
   rewrite <-unflatten_conjuncts_app.
   rp. destruct H2. 
   rewrite Forall_forall in H1. unfold remove_trues in H1.
   intuition.
   auto. auto.
   (* TODO make this not depend on the length of functions *)
   do 44 (destruct f0; [ unfold remove_trues; try destruct l; auto | auto ]).
   unfold Provable; simpl. auto.
   destruct l; auto.
 + do 5 (destruct f0; [ unfold remove_trues; try destruct l; auto | ]). 
   destruct f0.
   assert (L := provable_l_remove _ _ _ _ H H2).
   destruct L. destruct H3. subst.
   unfold remove_trues in H2. simpl in H2.
   rewrite remove_true_app in H2. rewrite <- unflatten_conjuncts_app in H2.
   rp. rewrite Forall_forall in H1. 
   intuition.
   auto. auto.
   
   do 44 (destruct f0; [ unfold remove_trues; try destruct l; auto | auto ]).
   unfold remove_trues in *. simpl in H2. destruct l; auto.
Qed.

Lemma unflatten_conjuncts_sep_app : forall t f p uenv l1 l2,
nth_error f (functions.True_f nil) = Some (functions.True_signature t) ->
Sep.sexprD f p uenv nil 
(Sep.Star (unflatten_conjuncts_sep l1) (unflatten_conjuncts_sep l2)) =
Sep.sexprD f p uenv nil
         (unflatten_conjuncts_sep
            (l1 ++ l2)).
Proof.
intros. apply pred_ext.
induction l1. simpl (unflatten_conjuncts_sep nil).
Opaque functions.True_f.
simpl. rewrite H. simpl. 
unfold VericSepLogic.star. unfold VericSepLogic.inj.
 entailer. 
simpl in *. remember (l1 ++ l2).
destruct l. simpl. destruct l1; inv Heql.
simpl. destruct (exprD f uenv nil a tvProp).
unfold VericSepLogic.star. unfold VericSepLogic.inj.
entailer. destruct l2; inv H0; simpl; entailer.
simpl in *. rewrite H in *. simpl in *.
unfold VericSepLogic.inj in *. 
unfold VericSepLogic.star in *.
unfold VericSepLogic_Kernel.emp in *.
entailer!.
unfold VericSepLogic.inj in *. 
unfold VericSepLogic.star in *.
unfold VericSepLogic_Kernel.emp in *. unfold SepExpr.BadInj.
entailer!. simpl.
destruct l1. simpl. destruct (exprD f uenv nil a tvProp).
simpl in IHl1. rewrite H in *. simpl in *.
unfold VericSepLogic.inj in *. 
unfold VericSepLogic.star in *.
unfold VericSepLogic_Kernel.emp in *.
entailer. 
unfold VericSepLogic.inj in *. 
unfold VericSepLogic.star in *.
unfold VericSepLogic_Kernel.emp in *.
entailer.
inv Heql. simpl.
destruct ( exprD f uenv nil a tvProp).
simpl in IHl1. entailer!.
unfold VericSepLogic.star in *.
cancel.
apply IHl1.
simpl in *. entailer. unfold SepExpr.BadInj. entailer!.
unfold VericSepLogic.star in *.
cancel.
apply IHl1.

induction l1; auto.
  + simpl. rewrite H.
    simpl. unfold VericSepLogic.inj. entailer!. 
  + simpl in *.
    remember (l1 ++ l2). destruct (l). 
      - simpl in *.
        rewrite H in *. simpl in *.
        destruct l1; inv Heql. simpl.
        destruct (exprD f uenv nil a tvProp); [ | unfold SepExpr.BadInj, VericSepLogic.inj; entailer].
        unfold VericSepLogic.inj in *. 
        unfold VericSepLogic.star in *.
        unfold VericSepLogic_Kernel.emp in *.
        entailer. simpl in IHl1. rewrite H in *. simpl in IHl1.
        unfold VericSepLogic.inj in *. 
        unfold VericSepLogic.star in *.
        unfold VericSepLogic_Kernel.emp in *.
        entailer. 
        autorewrite with norm in IHl1. auto.
        apply Cveric.
      - simpl in *.
        destruct l1; inv Heql.
          * simpl. destruct (exprD f uenv nil a tvProp); 
                   [ | unfold SepExpr.BadInj, VericSepLogic.inj; entailer].
            simpl in *. rewrite H in *. simpl in *. destruct l. simpl in *.
            destruct (exprD f uenv nil e tvProp);
                     [ | unfold SepExpr.BadInj, VericSepLogic.inj; entailer].
            unfold VericSepLogic.inj in *. 
            unfold VericSepLogic.star in *.
            unfold VericSepLogic_Kernel.emp in *.
            entailer. autorewrite with norm in IHl1; [ | apply Cveric].
            auto.
            simpl in *.
            destruct (exprD f uenv nil e tvProp); 
                   [ | unfold SepExpr.BadInj, VericSepLogic.inj; entailer].
            unfold VericSepLogic.inj in *. 
            unfold VericSepLogic.star in *.
            unfold VericSepLogic_Kernel.emp in *.
            entailer.
            unfold VericSepLogic.inj in *. 
            unfold VericSepLogic.star in *.
            unfold VericSepLogic_Kernel.emp in *.
            cancel.
            autorewrite with norm in *. auto.
            apply Cveric.
            unfold VericSepLogic.star in *.
            entailer.
            (* apply Cveric. *)
          * simpl in *.
            unfold VericSepLogic.inj in *. 
            unfold VericSepLogic.star in *.
            unfold VericSepLogic_Kernel.emp in *.
            destruct (exprD f uenv nil a tvProp); entailer.
Qed.

Lemma Provable_lift_and : forall t e uenv f p,
nth_error f 5 = Some (functions.and_signature t) ->
nth_error f (functions.True_f nil) = Some (functions.True_signature t) ->
Sep.sexprD f p uenv nil (Sep.Inj e) = Sep.sexprD f p uenv nil (lift_and e).
Proof.
intros. apply pred_ext.
  + simpl. 
    induction e; auto.
    do 6 (destruct f0; auto).
    simpl. simpl in H. rewrite H. simpl.
    destruct l; simpl. 
      - unfold SepExpr.BadInj.
        unfold VericSepLogic.inj. apply derives_extract_prop.
        contradiction.
      - destruct l. simpl. rewrite H. simpl.
        destruct (exprD f uenv nil e tvProp). auto.
        auto.
        destruct l. 
          * rewrite Forall_forall in *.
            assert (Ee := (H1 e)). simpl in Ee. intuition. clear H2 H5.
            assert (Ee0 := (H1 e0)). simpl in Ee0. intuition. clear H2 H6.
            destruct (exprD f uenv nil e tvProp).
            simpl.
            destruct (exprD f uenv nil e0 tvProp). 
            unfold VericSepLogic.inj in *. unfold VericSepLogic_Kernel.emp in *.
            unfold lift_and. simpl.
            rewrite <- unflatten_conjuncts_sep_app.
            simpl. entailer. autorewrite with norm in *.
            eapply derives_trans.
            instantiate (1:= emp * emp). cancel.
            unfold VericSepLogic.star. 
            apply sepcon_derives; auto. auto.

            unfold SepExpr.BadInj. simpl. unfold VericSepLogic.inj.  entailer!.
            unfold SepExpr.BadInj. simpl. unfold VericSepLogic.inj. entailer!.
          * simpl in *. rewrite H in *. simpl in *. cancel.
  + induction e; auto.

do 6 (destruct f0; auto).
simpl. simpl in H. rewrite H. simpl.
destruct l; simpl. rewrite H. simpl.
unfold SepExpr.BadInj. entailer.
destruct l. simpl. rewrite H. simpl.
destruct (exprD f uenv nil e tvProp). auto.
auto.
destruct l. 
rewrite Forall_forall in *.
assert (Ee := (H1 e)). simpl in Ee. intuition. clear H2 H5.
assert (Ee0 := (H1 e0)). simpl in Ee0. intuition. clear H2 H6.
unfold lift_and. simpl.
rewrite <- unflatten_conjuncts_sep_app.
simpl. unfold VericSepLogic.star.
destruct (exprD f uenv nil e tvProp).
simpl.
destruct (exprD f uenv nil e0 tvProp). 
unfold VericSepLogic.inj in *. unfold VericSepLogic_Kernel.emp in *.
simpl. 
unfold VericSepLogic.star. 
eapply derives_trans.
Focus 2.
instantiate (1:= ((!!t0 && emp) * (!!t1 && emp))). entailer!. 
apply sepcon_derives; auto. 

unfold SepExpr.BadInj in *. unfold VericSepLogic.inj in *.
eapply derives_trans. 
apply sepcon_derives. apply H4. apply H3.
entailer!.

unfold SepExpr.BadInj.
eapply derives_trans.
apply sepcon_derives; eassumption.
unfold VericSepLogic.inj, SepExpr.BadInj.
destruct (exprD f uenv nil e0 tvProp); entailer!. 
auto.

simpl in *. rewrite H in *. simpl in *.
cancel.

Qed.

Lemma lift_ands_eq : forall t f p s uenv,
nth_error f 5 = Some (functions.and_signature t) ->
nth_error f (functions.True_f nil) = Some (functions.True_signature t) ->
Sep.sexprD f p uenv nil s =
Sep.sexprD f p uenv nil (lift_ands s).
Proof.
intros.
apply pred_ext.
+ induction s; auto.
    - simpl. rewrite <- Provable_lift_and; auto.
    - simpl. unfold VericSepLogic.star. apply sepcon_derives; auto.
+ induction s; auto.
    - simpl. rewrite <- Provable_lift_and; auto.
    - simpl. unfold VericSepLogic.star. apply sepcon_derives; auto.
Qed.  
  
Lemma goal_lift_and :
forall t f preds uenv a l r,
nth_error f 5 = Some (functions.and_signature t) ->
nth_error f (functions.True_f nil) = Some (functions.True_signature t) ->
(goalD (functions.all_types_r t) f preds uenv nil (a, (l,r)) <-> 
goalD (functions.all_types_r t) f preds uenv nil (a, ((lift_ands l), (lift_ands r)))).
intuition.
 + induction a. 
     - simpl in *. 
       repeat rewrite <- lift_ands_eq; auto.
     - simpl. intros. simpl in *. destruct a0; intuition.
 + induction a.
     - simpl in *. do 2 rewrite <- lift_ands_eq in *; auto.
     - simpl in *. destruct a0; intuition.
Qed.

Lemma goal_lift_and' :
forall t f preds uenv a l r newl newr n,
nth_error f 5 = Some (functions.and_signature t) ->
nth_error f (functions.True_f nil) = Some (functions.True_signature t) ->
lift_ands l = newl -> lift_ands r = newr ->
n = nil ->
(goalD (functions.all_types_r t) f preds uenv n (a, (l,r)) <-> 
goalD (functions.all_types_r t) f preds uenv nil (a, (newl, newr))).
intros. rewrite <- H1. rewrite <- H2. rewrite H3. apply goal_lift_and; auto.
Qed.

Ltac e_vm_compute_left :=
match goal with 
| |- ?X = Some _ => match eval vm_compute in X with 
                   | Some ?Y => exact (@eq_refl _ (Some Y) (*<: (Some Y) = (Some Y)*))
                   end
| |- ?X = _ => let comp := eval vm_compute in X in exact (@eq_refl _ X)
end.

Ltac lift_and_goal :=
erewrite goal_lift_and';
[ | auto | auto | e_vm_compute_left |  e_vm_compute_left | auto ]. 