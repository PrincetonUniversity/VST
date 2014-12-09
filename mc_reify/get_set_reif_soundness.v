Require Import  Coq.Numbers.BinNums.
Require Import compcert.lib.Maps.
Require Import mc_reify.func_defs.
Require Import mc_reify.get_set_reif.
Require Import mc_reify.app_lemmas.

Section tbled.

Parameter tbl : SymEnv.functions RType_typ.

Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.


Let Expr_expr_fs := Expr_expr_fs tbl.
Existing Instance Expr_expr_fs.

Let Expr_ok_fs := Expr_ok_fs tbl.
Existing Instance Expr_ok_fs.

Existing Instance MA.

Definition reflect tus tvs e (ty : typ)
 := @exprD _ _ _ Expr_expr_fs tus tvs e ty.


Lemma as_tree_l : forall e t l o r,
as_tree e = Some (inl (t, l, o, r)) ->
e = (App (App (App (Inj (inr (Data (fnode t)))) l) o) r).
intros.
unfold as_tree in H.
repeat
match goal with 
| [ H : match ?x with _ => _  end = _ |- _ ] => destruct x; simpl in H; try congruence end. 
inversion H. subst. clear H.
auto.
Admitted. (*WHATEVER*)

Lemma as_tree_r : forall e t,
as_tree e = Some (inr t) ->
e = (Inj (inr (Data (fleaf t)))).
intros.
unfold as_tree in H.
repeat
match goal with 
| [ H : match ?x with _ => _  end = _ |- _ ] => destruct x; simpl in H; try congruence end. 
inversion H. subst. auto.
Admitted.

Lemma set_reif_eta : forall i v m ty,
  set_reif i v m ty=
match (as_tree m) with
  | Some (inl (t,l,o,r)) (* Node l o r *)=>
    match i with 
      | xH => node l (some_reif v t) r t
      | xO ii => node (set_reif ii v l ty) o r t
      | xI ii => node l o (set_reif ii v r ty) t
    end
  | Some (inr t) => 
    match i with
      | xH => node (leaf t) (some_reif v t) (leaf t) t
      | xO ii => node (set_reif ii v (leaf t) ty) (none_reif t) (leaf t) t
      | xI ii => node (leaf t) (none_reif t) (set_reif ii v (leaf t) ty) t
    end
  | _ => (App (App (Inj (inr (Data (fset ty i)))) v) m)
end.
destruct i; reflexivity.
Qed.

Ltac destruct_as_tree :=
repeat
match goal with
| [ H : as_tree _ = Some (inl (_ , _ , _, _)) |- _ ] => fail 1
| [ H : as_tree _ = Some (inr _) |- _ ] => fail 1
| [ H : as_tree _ = Some (inl (?p, _, _)) |- _ ] => destruct p
| [ H : as_tree _ = Some (inl (?p, _)) |- _ ] => destruct p
| [ H : as_tree _ = Some (inl ?p) |- _ ] => destruct p
| [ H : as_tree _ = Some ?p |- _ ] => destruct p
end.

Lemma set_reif_eq2 :
forall typ i vr tr,
reflect nil nil (App (App (Inj (inr (Data (fset typ i)))) vr) tr) (typtree typ) =
reflect nil nil (set_reif i vr tr typ) (typtree typ).
Proof.
intros. 
unfold reflect. unfold exprD. cbv [split_env]. simpl.
induction i. simpl.
match goal with 
[ |-  match ?d with _ => _ end = match ?x with _ => _ end ] => 
destruct d eqn:?, x eqn:?
end; auto.
f_equal.
destruct (as_tree tr) eqn:?; destruct_as_tree; auto.
erewrite exprD'_App_L_rw in Heqo. Focus 3.
erewrite exprD'_App_L_rw; eauto. simpl. unfold typeof_func_opt. reflexivity.
simpl. unfold exprD'. unfold funcAs. simpl.
Focus 2. simpl.

Admitted.



Lemma set_reif_eq :
forall typ i v vr t tr tbl pt, 
Some v = reflect tbl nil nil vr typ ->
Some t = reflect tbl nil nil tr (typtree typ) ->
reflect tbl nil nil (set_reif i vr tr) (typtree typ) = Some pt ->
PTree.set i v t = pt.
intros. induction i; simpl in *.
  + destruct (as_tree tr) eqn : atr;  destruct_as_tree. 
     - unfold reflect in *. 

Require MirrorCore.syms.SymSum.

Existing Instance SymSum.RSymOk_sum.
Instance RSym_env : RSym SymEnv.func := SymEnv.RSym_func fs.

Lemma ptree_node : forall e0 e1 e2 typ t0 p,
exprD nil nil (node e1 e0 e2 t0) (typtree typ) =
       Some p ->
t0 = typ.
intros.
assert (typeof_expr nil nil (node e1 e0 e2 t0) = Some (typtree typ)).
unfold exprD in H.  simpl in H.
destruct (exprD' nil nil (typtree typ) (node e1 e0 e2 t0)) eqn:?; simpl in H; try congruence.
eapply ExprTac.exprD_typeof_Some; auto with typeclass_instances.
admit. 
apply Heqo.
unfold node in H0. Check AppN.apps.
 change (App (App (App (Inj (inr (Data (fnode t0)))) e1) e0) e2) 
with (AppN.apps (Inj (inr (Data (fnode t0)))) (e1 :: e0 :: e2 :: nil)) in H0.
erewrite AppN.type_of_applys_typeof in H0. 
simpl in H0.
unfold node in *.
simpl in *. unfold AppN.apps in *. simpl in *.
SearchAbout typeof_expr.
rewrite Heqo.
reflexivity.
simpl in H.
repeat apply SymSum.RSymOk_sum. 
apply RSym_sum_OK.
Check @ExprTac.exprD_typeof_Some.
pose (ExprTac.exprD_typeof_Some). eapply e; auto with typeclass_instances.

apply (@ExprTac.exprD_typeof_Some (expr typ func) _ _ _ _ _ _ _) in H; auto with typeclass_instances.
simpl.
SearchAbout exprD'. 
unfold exprD in H. simpl in H.
destruct (exprD' nil nil (typtree typ) (node e1 e0 e2 t0)) eqn:?; intros; try congruence. 
eapply ExprTac.exprD_typeof_eq; eauto with typeclass_instances.
apply Heqo.
SearchAbout exprD'. Locate later. Check @seplog.later.
Print fstatement.
 unfold node in H. simpl in H.
unfold exprD in H. sc

       unfold exprD, split_env, ExprI.exprD' in H1. simpl in H1. unfold exprD' in H1. destruct t0; compute in H1.
Locate exprD'.
Admitted.

Lemma set_reif_eq2 :
forall typ i vr tr tbl,
reflect tbl nil nil (App (App (Inj (inr (Data (fset typ i)))) vr) tr) (typtree typ) =
reflect tbl nil nil (set_reif i vr tr) (typtree typ).
Proof.
Admitted.

Lemma get_reif_eq :
forall typ i  t tr tbl , 
Some t = reflect tbl nil nil tr (typtree typ) ->
Some (PTree.get i t) = reflect tbl nil nil (get_reif i tr) (tyoption typ).
Admitted.

Lemma get_reif_eq2 :
forall typ i tr tbl,
reflect tbl nil nil (App (Inj (inr (Data (fget typ i)))) tr) (tyoption typ) =
reflect tbl nil nil (get_reif i tr) (tyoption typ).
Proof.
Admitted.